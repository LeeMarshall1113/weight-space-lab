"""PREREG_BRIDGE: train tiny ReLU nets on popcount mod 3 (6 bits), quantize, exact rational
eval + rational weight-space IBP.

    python bridge/train.py dev            # seeds 0-3, w in {8,12,16}, arms ORD/STR/RND
Writes bridge/nets/<arm>_w<w>_s<seed>.json (quantized weights as integers over 256) and
results/bridge_dev.jsonl.
"""
import argparse
import itertools
import json
import time
from fractions import Fraction as F
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "results"
NETS = HERE / "nets"
Q = 256
TAUS = (F(1, 1000), F(1, 300), F(1, 100), F(1, 30))

X = np.array(list(itertools.product([0, 1], repeat=6)), dtype=np.float64)
Y = np.where(X.sum(1) % 3 == 0, 1.0, -1.0)


def train(arm, w, seed, steps=4000, qat=500, idx=None):
    import torch
    torch.set_num_threads(2)
    torch.manual_seed(seed)
    net = torch.nn.Sequential(torch.nn.Linear(6, w), torch.nn.ReLU(), torch.nn.Linear(w, w), torch.nn.ReLU(),
                              torch.nn.Linear(w, 1)).double()
    if arm == "RND":
        return net
    x = torch.tensor(X if idx is None else X[idx])
    y = torch.tensor(Y if idx is None else Y[idx])
    if arm == "ORD":
        opt = torch.optim.Adam(net.parameters(), lr=1e-2)
        for _ in range(steps):
            z = net(x).squeeze(1)
            loss = torch.nn.functional.binary_cross_entropy_with_logits(z, (y > 0).double())
            opt.zero_grad(); loss.backward(); opt.step()
        return net
    opt = torch.optim.AdamW(net.parameters(), lr=1e-2, weight_decay=1e-3)
    params = list(net.parameters())

    def fwd_q():
        h = x
        lin = [m for m in net if isinstance(m, torch.nn.Linear)]
        for k, m in enumerate(lin):
            Wq = m.weight + (torch.round(m.weight * Q) / Q - m.weight).detach()
            bq = m.bias + (torch.round(m.bias * Q) / Q - m.bias).detach()
            h = h @ Wq.T + bq
            if k < len(lin) - 1:
                h = torch.relu(h)
        return h.squeeze(1)

    for it in range(steps + qat):
        z = net(x).squeeze(1) if it < steps else fwd_q()
        loss = torch.clamp(1 - y * z, min=0).mean()
        opt.zero_grad(); loss.backward(); opt.step()
    del params
    return net


def quantize(net):
    """-> list of (W, b) with integer numerators over Q."""
    import torch
    layers = []
    for m in net:
        if isinstance(m, torch.nn.Linear):
            W = np.rint(m.weight.detach().numpy() * Q).astype(int).tolist()
            b = np.rint(m.bias.detach().numpy() * Q).astype(int).tolist()
            layers.append((W, b))
    return layers


def exact_logits(layers):
    out = []
    for x in X.astype(int).tolist():
        h = [F(v) for v in x]
        for k, (W, b) in enumerate(layers):
            h = [sum(F(wij, Q) * hj for wij, hj in zip(row, h)) + F(bi, Q) for row, bi in zip(W, b)]
            if k < len(layers) - 1:
                h = [max(v, F(0)) for v in h]
        out.append(h[0])
    return out


def ibp_margins(layers, tau):
    """Lower bound on y*z over the closed weight ball of radius tau, per input (exact rationals)."""
    res = []
    for x, y in zip(X.astype(int).tolist(), Y):
        lo = [F(v) for v in x]
        hi = list(lo)
        for k, (W, b) in enumerate(layers):
            nlo, nhi = [], []
            for row, bi in zip(W, b):
                L = F(bi, Q) - tau
                U = F(bi, Q) + tau
                for wij, l, u in zip(row, lo, hi):
                    a, c = F(wij, Q) - tau, F(wij, Q) + tau
                    cs = (a * l, a * u, c * l, c * u)
                    L += min(cs)
                    U += max(cs)
                nlo.append(L)
                nhi.append(U)
            if k < len(layers) - 1:
                nlo = [max(v, F(0)) for v in nlo]
                nhi = [max(v, F(0)) for v in nhi]
            lo, hi = nlo, nhi
        res.append(lo[0] if y > 0 else -hi[0])
    return res


def max_tau(layers, lo=F(0), hi=F(1, 4), iters=24):
    if min(ibp_margins(layers, F(0))) <= 0:
        return F(0)
    for _ in range(iters):
        mid = (lo + hi) / 2
        if min(ibp_margins(layers, mid)) > 0:
            lo = mid
        else:
            hi = mid
    return lo


def one(arm, w, seed, idx=None):
    t0 = time.time()
    net = train(arm, w, seed, idx=idx)
    import torch
    with torch.no_grad():
        zf = net(torch.tensor(X)).squeeze(1).numpy()
    layers = quantize(net)
    zq = exact_logits(layers)
    yq = np.array([1.0 if v > 0 else -1.0 for v in zq])
    own = arm == "RND"  # RND is certified against its own sign function (B3)
    target = yq if own else Y
    ok_q = int((yq == Y).sum())
    margins = [float(v * t) for v, t in zip(zq, target)]
    cert = {}
    if own or ok_q == 64:
        global Y_SAVE
        Ysave = Y.copy()
        Y[:] = target
        try:
            for tau in TAUS:
                cert[str(tau)] = min(ibp_margins(layers, tau)) > 0
            mt = max_tau(layers)
        finally:
            Y[:] = Ysave
    else:
        mt = None
    rec = {"arm": arm, "w": w, "seed": seed, "split": None if idx is None else "48/16",
           "float_acc": int((np.sign(zf) == Y).sum()), "quant_acc": ok_q,
           "min_margin_q": min(margins), "cert": cert, "max_tau": None if mt is None else float(mt),
           "sec": round(time.time() - t0, 1)}
    NETS.mkdir(exist_ok=True)
    if idx is None:
        (NETS / f"{arm}_w{w}_s{seed}.json").write_text(json.dumps({"q": Q, "layers": layers, "rec": rec}))
    return rec


def falsify(layers, tau, n_rand=10000, seed=0):
    """C3: search the closed tau-ball for a sign violation on any of the 64 inputs (float64).
    Uniform, sign-corner and gradient-sign (PGD) perturbations. Returns the worst y*z found."""
    import torch
    torch.manual_seed(seed)
    W = [torch.tensor(np.array(Wl, dtype=np.float64) / Q) for Wl, _ in layers]
    B = [torch.tensor(np.array(bl, dtype=np.float64) / Q) for _, bl in layers]
    x, y = torch.tensor(X), torch.tensor(Y)

    def margins(dW, dB):  # dW: list of [k, out, in]
        h = x.unsqueeze(0).expand(dW[0].shape[0], -1, -1)
        for i, (w, b, d, e) in enumerate(zip(W, B, dW, dB)):
            h = h @ (w + d).transpose(1, 2) + (b + e).unsqueeze(1)
            if i < len(W) - 1:
                h = torch.relu(h)
        return (h.squeeze(-1) * y).min(1).values

    worst = float("inf")
    t = float(tau)
    for kind in ("uniform", "corner"):
        for _ in range(n_rand // 2000):
            k = 1000
            if kind == "uniform":
                dW = [(torch.rand(k, *w.shape, dtype=torch.float64) * 2 - 1) * t for w in W]
                dB = [(torch.rand(k, *b.shape, dtype=torch.float64) * 2 - 1) * t for b in B]
            else:
                dW = [torch.sign(torch.rand(k, *w.shape, dtype=torch.float64) - 0.5) * t for w in W]
                dB = [torch.sign(torch.rand(k, *b.shape, dtype=torch.float64) - 0.5) * t for b in B]
            worst = min(worst, margins(dW, dB).min().item())
    for j in range(64):  # PGD per input, sign steps, projected to the ball
        dW = [torch.zeros(1, *w.shape, dtype=torch.float64, requires_grad=True) for w in W]
        dB = [torch.zeros(1, *b.shape, dtype=torch.float64, requires_grad=True) for b in B]
        for _ in range(50):
            h = x[j:j + 1].unsqueeze(0)
            for i, (w, b, d, e) in enumerate(zip(W, B, dW, dB)):
                h = h @ (w + d).transpose(1, 2) + (b + e).unsqueeze(1)
                if i < len(W) - 1:
                    h = torch.relu(h)
            m = (h.squeeze() * y[j])
            g = torch.autograd.grad(m, dW + dB)
            with torch.no_grad():
                for v, gv in zip(dW + dB, g):
                    v -= t / 10 * torch.sign(gv)
                    v.clamp_(-t, t)
        with torch.no_grad():
            worst = min(worst, margins([d.detach() for d in dW], [e.detach() for e in dB]).min().item())
    return worst


def test(a):
    """Blind test seeds 100-107, w = 16 (A2). One run; not inspected before scoring."""
    OUT.mkdir(exist_ok=True)
    with open(OUT / "bridge_test.jsonl", "w") as f:
        for arm in ("ORD", "STR", "RND"):
            for s in range(100, 108):
                r = one(arm, 16, s)
                d = json.loads((NETS / f"{arm}_w16_s{s}.json").read_text())
                if r["quant_acc"] == 64 or arm == "RND":
                    if arm == "RND":
                        Ysave = Y.copy()
                        zq = exact_logits(d["layers"])
                        Y[:] = np.array([1.0 if v > 0 else -1.0 for v in zq])
                    try:
                        r["falsifier_worst_margin"] = falsify(d["layers"], F(1, 1000))
                    finally:
                        if arm == "RND":
                            Y[:] = Ysave
                f.write(json.dumps(r) + "\n"); f.flush()
                print(arm, s, r["quant_acc"], r["cert"], r["max_tau"], r.get("falsifier_worst_margin"), flush=True)


def dev(a):
    OUT.mkdir(exist_ok=True)
    with open(OUT / "bridge_dev.jsonl", "w") as f:
        for w in (8, 12, 16):
            for arm in ("ORD", "STR", "RND"):
                for s in range(4):
                    r = one(arm, w, s)
                    f.write(json.dumps(r) + "\n"); f.flush()
                    print(arm, w, s, r["float_acc"], r["quant_acc"], r["cert"], r["max_tau"], r["sec"], flush=True)
        # diagnostic 48/16 split, ORD only (not an outcome)
        rng = np.random.default_rng(48)
        idx = np.sort(rng.permutation(64)[:48])
        for w in (8, 12, 16):
            for s in range(4):
                net_rec = one("ORD", w, s, idx=idx)
                f.write(json.dumps(net_rec) + "\n"); f.flush()


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["dev", "test"])
    a = ap.parse_args()
    {"dev": dev, "test": test}[a.cmd](a)
