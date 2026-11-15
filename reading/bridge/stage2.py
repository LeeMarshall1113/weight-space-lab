"""PREREG_BRIDGE stage 2 (A1, A4).

    python bridge/stage2.py s2a            # tightness gap on the 16 stage-1 test nets (CPU)
    python bridge/stage2.py s2b            # retrain ORD test seeds, save float weights (exact dyadics)
    python bridge/stage2.py s2c_dev --n 8  # width choice for n bits (dev seeds 0-3)
    python bridge/stage2.py s2c_test --n 8 --w 16
"""
import argparse
import itertools
import json
import sys
import time
from fractions import Fraction as F
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import train as T  # noqa: E402

OUT = T.OUT


def set_task(n):
    T.X = np.array(list(itertools.product([0, 1], repeat=n)), dtype=np.float64)
    T.Y = np.where(T.X.sum(1) % 3 == 0, 1.0, -1.0)


# ---------- S2a ----------
def witness(layers, tau, seed=0):
    """Frozen C3 search, returning the worst perturbation found (float64) and its input."""
    import torch
    torch.manual_seed(seed)
    Q = T.Q
    W = [torch.tensor(np.array(Wl, dtype=np.float64) / Q) for Wl, _ in layers]
    B = [torch.tensor(np.array(bl, dtype=np.float64) / Q) for _, bl in layers]
    x, y = torch.tensor(T.X), torch.tensor(T.Y)
    t = float(tau)

    def fwd(dW, dB, xs):
        h = xs.unsqueeze(0).expand(dW[0].shape[0], -1, -1)
        for i, (w, b, d, e) in enumerate(zip(W, B, dW, dB)):
            h = h @ (w + d).transpose(1, 2) + (b + e).unsqueeze(1)
            if i < len(W) - 1:
                h = torch.relu(h)
        return h.squeeze(-1)

    best = (float("inf"), None, None, None)
    for kind in ("uniform", "corner"):
        for _ in range(5):
            k = 1000
            if kind == "uniform":
                dW = [(torch.rand(k, *w.shape, dtype=torch.float64) * 2 - 1) * t for w in W]
                dB = [(torch.rand(k, *b.shape, dtype=torch.float64) * 2 - 1) * t for b in B]
            else:
                dW = [torch.sign(torch.rand(k, *w.shape, dtype=torch.float64) - 0.5) * t for w in W]
                dB = [torch.sign(torch.rand(k, *b.shape, dtype=torch.float64) - 0.5) * t for b in B]
            m = fwd(dW, dB, x) * y
            v, idx = m.min(1).values.min(0)
            if v.item() < best[0]:
                i = int(idx)
                best = (v.item(), [d[i] for d in dW], [e[i] for e in dB], int(m[i].argmin()))
    for j in range(len(T.X)):
        dW = [torch.zeros(1, *w.shape, dtype=torch.float64, requires_grad=True) for w in W]
        dB = [torch.zeros(1, *b.shape, dtype=torch.float64, requires_grad=True) for b in B]
        for _ in range(50):
            m = (fwd(dW, dB, x[j:j + 1]) * y[j]).sum()
            g = torch.autograd.grad(m, dW + dB)
            with torch.no_grad():
                for v, gv in zip(dW + dB, g):
                    v -= t / 10 * torch.sign(gv)
                    v.clamp_(-t, t)
        with torch.no_grad():
            v = (fwd(dW, dB, x[j:j + 1]) * y[j]).item()
        if v < best[0]:
            best = (v, [d.detach()[0] for d in dW], [e.detach()[0] for e in dB], j)
    return best


def exact_margin(layers, dW, dB, j):
    Q = T.Q
    h = [F(int(v)) for v in T.X[j]]
    for k, ((Wl, bl), d, e) in enumerate(zip(layers, dW, dB)):
        d, e = d.numpy(), e.numpy()
        h = [sum((F(wij, Q) + F(float(d[r, c]))) * hc for c, (wij, hc) in enumerate(zip(row, h)))
             + F(bl[r], Q) + F(float(e[r])) for r, row in enumerate(Wl)]
        if k < len(layers) - 1:
            h = [max(v, F(0)) for v in h]
    return h[0] * int(T.Y[j])


def s2a(a):
    set_task(6)
    rows = [json.loads(l) for l in open(OUT / "bridge_test.jsonl")]
    with open(OUT / "bridge_s2a.jsonl", "w") as f:
        for r in rows:
            if r["arm"] == "RND":
                continue
            d = json.loads((T.NETS / f"{r['arm']}_w16_s{r['seed']}.json").read_text())
            L = d["layers"]
            lo, hi = r["max_tau"], 0.25
            v, dW, dB, j = witness(L, hi)
            if not (v <= 0 and exact_margin(L, dW, dB, j) <= 0):
                rec = {**{k: r[k] for k in ("arm", "seed", "max_tau")}, "break_tau": None, "note": "no break at 1/4"}
            else:
                for _ in range(20):
                    mid = (lo + hi) / 2
                    v, dW, dB, j = witness(L, mid)
                    if v <= 0 and exact_margin(L, dW, dB, j) <= 0:
                        hi = mid
                    else:
                        lo = mid
                rec = {**{k: r[k] for k in ("arm", "seed", "max_tau")}, "break_tau": hi,
                       "ratio": hi / r["max_tau"]}
            f.write(json.dumps(rec) + "\n"); f.flush()
            print(rec, flush=True)


# ---------- S2b ----------
def s2b(a):
    set_task(6)
    import torch
    out = []
    for s in range(100, 108):
        net = T.train("ORD", 16, s)
        q = T.quantize(net)
        ref = json.loads((T.NETS / f"ORD_w16_s{s}.json").read_text())["layers"]
        same = json.dumps(q) == json.dumps(ref)
        fr = []
        for m in net:
            if isinstance(m, torch.nn.Linear):
                W = [[F(float(v)) for v in row] for row in m.weight.detach().numpy()]
                b = [F(float(v)) for v in m.bias.detach().numpy()]
                fr.append(([[[v.numerator, v.denominator] for v in row] for row in W],
                           [[v.numerator, v.denominator] for v in b]))
        (T.NETS / f"ORDF_w16_s{s}.json").write_text(json.dumps({"frac": fr, "quant_matches_stage1": same}))
        out.append({"seed": s, "quant_matches_stage1": same})
        print(s, "quant matches stage 1:", same, flush=True)
    (OUT / "bridge_s2b_retrain.json").write_text(json.dumps(out))


# ---------- S2c ----------
def train_n(n, w, seed):
    import torch
    torch.set_num_threads(2)
    torch.manual_seed(seed)
    net = torch.nn.Sequential(torch.nn.Linear(n, w), torch.nn.ReLU(), torch.nn.Linear(w, w), torch.nn.ReLU(),
                              torch.nn.Linear(w, 1)).double()
    x, y = torch.tensor(T.X), torch.tensor(T.Y)
    opt = torch.optim.Adam(net.parameters(), lr=1e-2)
    for _ in range(4000):
        z = net(x).squeeze(1)
        loss = torch.nn.functional.binary_cross_entropy_with_logits(z, (y > 0).double())
        opt.zero_grad(); loss.backward(); opt.step()
    return net


def one_n(n, w, seed, test=False):
    t0 = time.time()
    net = train_n(n, w, seed)
    L = T.quantize(net)
    zq = T.exact_logits(L)
    acc = int(sum((v > 0) == (y > 0) for v, y in zip(zq, T.Y)))
    rec = {"n": n, "w": w, "seed": seed, "quant_acc": acc, "N": len(T.X)}
    if acc == len(T.X):
        rec["cert_1e-3"] = min(T.ibp_margins(L, F(1, 1000))) > 0
        rec["max_tau"] = float(T.max_tau(L, iters=16))
        if test:
            rec["falsifier_worst_margin"] = T.falsify(L, F(1, 1000))
    rec["sec"] = round(time.time() - t0, 1)
    (T.NETS / f"N{n}_w{w}_s{seed}.json").write_text(json.dumps({"q": T.Q, "layers": L, "rec": rec}))
    return rec


def s2c_dev(a):
    set_task(a.n)
    with open(OUT / f"bridge_s2c_dev_n{a.n}.jsonl", "w") as f:
        for w in (16, 24, 32):
            ok = 0
            for s in range(4):
                r = one_n(a.n, w, s)
                ok += r["quant_acc"] == r["N"]
                f.write(json.dumps(r) + "\n"); f.flush()
                print(r, flush=True)
            if ok >= 3:
                print("CHOSEN w", w, flush=True)
                break


def s2c_test(a):
    set_task(a.n)
    with open(OUT / f"bridge_s2c_test_n{a.n}.jsonl", "w") as f:
        for s in range(100, 108):
            r = one_n(a.n, a.w, s, test=True)
            f.write(json.dumps(r) + "\n"); f.flush()
            print(r, flush=True)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["s2a", "s2b", "s2c_dev", "s2c_test"])
    ap.add_argument("--n", type=int, default=8)
    ap.add_argument("--w", type=int, default=16)
    a = ap.parse_args()
    {"s2a": s2a, "s2b": s2b, "s2c_dev": s2c_dev, "s2c_test": s2c_test}[a.cmd](a)
