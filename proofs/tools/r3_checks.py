"""Rung-3 lane checks on one exported net (PREREG_R3.md, "Checks the lane runs" and
"The comparison with verified code"). numpy, CPU, float64 unless stated.

    python tools/r3_checks.py <casedir> [--quick]     -> <casedir>/r3_checks.json

Needs <casedir>/net.json (exact export), case.json (tau, delta) and the pool spec.
Fixed here before any run:
  inside ball : 4,000 uniform + 4,000 sign-corner + 2,000 adversarial perturbations,
                each batch at 2,000 box points (random + the box corners).
  adversarial : sign-gradient ascent on the worst point's deviation, 30 steps of r/8,
                projected to the ball of radius r.
  outside     : the same search (100 starts) at r = s*tau, s = 2, 4, ..., 4096.
  float32     : forward pass in float32 at 10,000 float32 box points against the exact spec.
  fine-tune   : full-batch Adam, lr 1e-4, 2,000 steps, weights clipped to the ball each step.
"""
import itertools, json, os, sys
from fractions import Fraction as F
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import specpool as SP
import train_twin as TT

HERE = SP.HERE


def load(casedir):
    meta = json.load(open(os.path.join(casedir, "case.json"), encoding="utf-8"))
    j = json.load(open(os.path.join(casedir, "net.json")))
    layers = j["hidden"] + [j["out"]]
    Wq = [[[F(v) for v in r] for r in L["W"]] for L in layers]
    bq = [[F(v) for v in L["b"]] for L in layers]
    pool = {s["id"]: s for s in json.load(open(os.path.join(HERE, "pool", "rung1_pool.json")))}
    s = pool[meta["id"]]
    return meta, Wq, bq, SP.from_json(s["expr"]), [tuple(b) for b in s["box"]]


def points(box, n, g):
    lo, hi = np.array([b[0] for b in box], float), np.array([b[1] for b in box], float)
    X = g.uniform(lo, hi, (n, len(box)))
    C = np.array(list(itertools.product(*[(b[0], b[1]) for b in box])), float)
    X[:len(C)] = C
    return X


def fwd(Ws, bs, X):
    """Batched: Ws[l] (K, out, in), bs[l] (K, out), X (N, n). Returns y (K, N) and caches."""
    h = np.broadcast_to(X, (Ws[0].shape[0],) + X.shape)
    hs, zs = [h], []
    for i, (W, b) in enumerate(zip(Ws, bs)):
        z = np.einsum("kij,knj->kni", W, h) + b[:, None, :]
        zs.append(z)
        h = np.maximum(z, 0) if i < len(Ws) - 1 else z
        hs.append(h)
    return h[:, :, 0], hs, zs


def grads(Ws, hs, zs, gy):
    """gy (K, N) = dL/dy. Returns dL/dW, dL/db per layer."""
    d = gy[:, :, None]
    gW, gb = [None] * len(Ws), [None] * len(Ws)
    for i in range(len(Ws) - 1, -1, -1):
        gW[i] = np.einsum("kni,knj->kij", d, hs[i])
        gb[i] = d.sum(1)
        if i:
            d = np.einsum("kni,kij->knj", d, Ws[i]) * (zs[i - 1] > 0)
    return gW, gb


def worst_dev(W0, b0, dWs, dbs, X, S):
    y, _, _ = fwd([w + d for w, d in zip(W0, dWs)], [b + d for b, d in zip(b0, dbs)], X)
    return np.max(np.abs(y - S), axis=1)       # (K,)


def adversarial(W0, b0, r, X, S, K, g, steps=30):
    dWs = [r * g.choice([-1.0, 1.0], (K,) + w.shape[1:]) for w in W0]
    dbs = [r * g.choice([-1.0, 1.0], (K,) + b.shape[1:]) for b in b0]
    best = np.zeros(K)
    for _ in range(steps):
        Ws = [w + d for w, d in zip(W0, dWs)]; bs = [b + d for b, d in zip(b0, dbs)]
        y, hs, zs = fwd(Ws, bs, X)
        dev = y - S
        best = np.maximum(best, np.max(np.abs(dev), axis=1))
        idx = np.argmax(np.abs(dev), axis=1)
        gy = np.zeros_like(dev)
        gy[np.arange(K), idx] = np.sign(dev[np.arange(K), idx])
        gW, gb = grads(Ws, hs, zs, gy)
        dWs = [np.clip(d + (r / 8) * np.sign(gr), -r, r) for d, gr in zip(dWs, gW)]
        dbs = [np.clip(d + (r / 8) * np.sign(gr), -r, r) for d, gr in zip(dbs, gb)]
    return max(float(best.max()), float(worst_dev(W0, b0, dWs, dbs, X, S).max()))


def finetune(Wf, bf, e, box, tau, delta, seed, clip=True, steps=2000, lr=1e-4):
    g = np.random.default_rng(1000 + seed)
    lo, hi = np.array([b[0] for b in box], float), np.array([b[1] for b in box], float)
    c = g.normal(size=len(box))
    c *= (delta / 4) / np.sum(np.abs(c) * (hi - lo) / 2)      # max |g| over the box = delta/4
    shift = lambda X: (X - (lo + hi) / 2) @ c
    Xtr = g.uniform(lo, hi, (2000, len(box))); Xte = g.uniform(lo, hi, (5000, len(box)))
    ytr = TT.spec_np(e, Xtr) + shift(Xtr) + g.normal(0, delta / 4, 2000)
    yte = TT.spec_np(e, Xte) + shift(Xte)
    W = [w[None].copy() for w in Wf]; b = [x[None].copy() for x in bf]
    mse = lambda W_, b_: float(np.mean((fwd(W_, b_, Xte)[0][0] - yte) ** 2))
    out = {"mse_written_net": mse(W, b), "mse_spec_program": float(np.mean((TT.spec_np(e, Xte) - yte) ** 2))}
    P = W + b
    m = [np.zeros_like(p) for p in P]; v = [np.zeros_like(p) for p in P]
    base = [p.copy() for p in P]
    for t in range(1, steps + 1):
        y, hs, zs = fwd(P[:len(W)], P[len(W):], Xtr)
        gW, gb = grads(P[:len(W)], hs, zs, 2 * (y - ytr[None]) / len(ytr))
        for k, gr in enumerate(gW + gb):
            m[k] = 0.9 * m[k] + 0.1 * gr; v[k] = 0.999 * v[k] + 0.001 * gr * gr
            P[k] = P[k] - lr * (m[k] / (1 - 0.9 ** t)) / (np.sqrt(v[k] / (1 - 0.999 ** t)) + 1e-8)
            if clip:
                P[k] = np.clip(P[k], base[k] - tau, base[k] + tau)
    out["mse_finetuned"] = mse(P[:len(W)], P[len(W):])
    out["max_weight_move"] = float(max(np.max(np.abs(p - q)) for p, q in zip(P, base)))
    Xc = points(box, 20000, g)
    out["max_dev_from_spec"] = float(np.max(np.abs(fwd(P[:len(W)], P[len(W):], Xc)[0][0] - TT.spec_np(e, Xc))))
    return out


def main(casedir, quick=False):
    meta, Wq, bq, e, box = load(casedir)
    tau, delta = float(F(meta["tau"])), float(F(meta["delta"]))
    Wf = [np.array(W, float).reshape(len(b), -1) for W, b in zip(Wq, bq)]
    bf = [np.array(b, float) for b in bq]
    W0 = [w[None] for w in Wf]; b0 = [b[None] for b in bf]
    g = np.random.default_rng(31)
    res = {"id": meta["id"], "tau": tau, "delta": delta, "hidden_widths": [len(b) for b in bq[:-1]],
           "max_abs_weight": float(max(np.max(np.abs(w)) for w in Wf))}
    X = points(box, 20000, g)
    res["written_net_max_dev"] = float(np.max(np.abs(fwd(W0, b0, X)[0][0] - TT.spec_np(e, X))))
    # 1. inside the ball
    scale = 10 if quick else 1
    worst = {"uniform": 0.0, "sign": 0.0, "adversarial": 0.0}
    for kind, total in (("uniform", 4000 // scale), ("sign", 4000 // scale), ("adversarial", 2000 // scale)):
        for _ in range(total // 100):
            X = points(box, 2000, g); S = TT.spec_np(e, X)[None]
            if kind == "adversarial":
                d = adversarial(W0, b0, tau, X, S, 100, g)
            else:
                draw = (lambda sh: g.uniform(-tau, tau, sh)) if kind == "uniform" else (lambda sh: tau * g.choice([-1.0, 1.0], sh))
                d = float(worst_dev(W0, b0, [draw((100,) + w.shape[1:]) for w in W0],
                                    [draw((100,) + b.shape[1:]) for b in b0], X, S).max())
            worst[kind] = max(worst[kind], d)
    res["inside_ball_max_dev"] = worst
    res["inside_ball_ok"] = bool(max(worst.values()) <= delta)
    # 2. outside the ball
    res["outside"] = {}
    res["smallest_violating_multiple"] = None
    for k in range(1, 13):
        s = 2 ** k
        X = points(box, 2000, g); S = TT.spec_np(e, X)[None]
        d = adversarial(W0, b0, s * tau, X, S, 100, g)
        res["outside"][str(s)] = d
        if d > delta and res["smallest_violating_multiple"] is None:
            res["smallest_violating_multiple"] = s
            break
    # 3. float32
    X32 = points(box, 10000, g).astype(np.float32)
    y32, _, _ = fwd([w.astype(np.float32) for w in W0], [b.astype(np.float32) for b in b0], X32)
    assert y32.dtype == np.float32
    exact = np.array([float(SP.ev(e, [F(float(v)) for v in x])) for x in X32[:2000 if quick else 10000]])
    res["float32_max_dev_from_spec"] = float(np.max(np.abs(y32[0][:len(exact)].astype(float) - exact)))
    # 4. fine-tune inside the ball, and unconstrained for reference
    res["finetune"] = {}
    for seed in (0, 1, 2):
        a = finetune(Wf, bf, e, box, tau, delta, seed, clip=True)
        u = finetune(Wf, bf, e, box, tau, delta, seed, clip=False)
        a["inside_ball"] = bool(a["max_weight_move"] <= tau * (1 + 1e-9))
        a["within_delta"] = bool(a["max_dev_from_spec"] <= delta)
        a["gain_vs_program"] = 1 - a["mse_finetuned"] / a["mse_spec_program"]
        a["unconstrained"] = {"mse_finetuned": u["mse_finetuned"], "max_weight_move": u["max_weight_move"],
                              "max_dev_from_spec": u["max_dev_from_spec"], "leaves_delta": bool(u["max_dev_from_spec"] > delta)}
        res["finetune"][str(seed)] = a
    res["finetune_median_gain"] = float(np.median([res["finetune"][s]["gain_vs_program"] for s in "012"]))
    json.dump(res, open(os.path.join(casedir, "r3_checks.json"), "w"), indent=1)
    print(meta["id"], "widths", res["hidden_widths"], "written dev %.4f" % res["written_net_max_dev"],
          "| inside max %.4f (delta %.3f) ok=%s" % (max(worst.values()), delta, res["inside_ball_ok"]),
          "| breaks at s=%s" % res["smallest_violating_multiple"],
          "| f32 %.2e" % res["float32_max_dev_from_spec"],
          "| fine-tune gain %.1f%%" % (100 * res["finetune_median_gain"]), flush=True)
    return res


if __name__ == "__main__":
    main(os.path.abspath(sys.argv[1]), "--quick" in sys.argv)
