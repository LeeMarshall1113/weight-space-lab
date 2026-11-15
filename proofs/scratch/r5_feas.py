"""Lane feasibility check for rung 5 (not a result): rung-4 style carry construction with
SOFTMAX attention (max-subtracted, left-to-right sums) in numpy float32. Nothing proved."""
import sys, os
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tools"))
import r4net as R, r4pool as P

def soft_attend(h, X, Q, chunk=4_000_000):
    n, D = X.shape; dt = X.dtype
    rows = [r for r in range(D) if np.any(h["A"][r] != 0)]
    vrows = [r for r in range(D) if np.any(h["V"][r] != 0)]
    AX = {r: R.rdot(h["A"][r], X) for r in rows}; VX = {r: R.rdot(h["V"][r], X) for r in vrows}
    out = np.zeros((len(Q), D), dtype=dt); step = max(1, chunk // n); j = np.arange(n)
    for s in range(0, len(Q), step):
        q = Q[s:s + step]
        sc = np.zeros((len(q), n), dtype=dt)
        for r in rows: sc = sc + X[q, r][:, None] * AX[r][None, :]
        ok = (j[None, :] <= q[:, None]) if h["mask"] == "causal" else (j[None, :] < q[:, None]) if h["mask"] == "strict" else np.ones((len(q), n), bool)
        m = np.where(ok, sc, -np.inf).max(axis=1, keepdims=True)
        with np.errstate(invalid="ignore", under="ignore"):
            e = np.where(ok, np.exp((sc - m).astype(dt)), dt.type(0)).astype(dt)
        Zs = np.cumsum(e, axis=1, dtype=dt)[:, -1]
        for r in vrows:
            tot = np.cumsum((e * VX[r][None, :]).astype(dt), axis=1, dtype=dt)[:, -1]
            with np.errstate(invalid="ignore", divide="ignore"):
                out[s:s + step, r] = np.where(Zs > 0, (tot / Zs).astype(dt), dt.type(0))
    return out
R.attend = soft_attend

def carry_net(c, g):
    V, m = c["V"], c["m"]; D = 9
    emb = [[0] * 6] + [[c["dg"][t], (c["dg"][t] + 1) % m, 1 if c["cls"][t] == 2 else 0, 1 if c["cls"][t] == 1 else 0, 0, 0] for t in range(V)]
    Z = lambda r, cc: [[0.0] * cc for _ in range(r)]
    A = Z(D, D); A[6][7] = g; A[8][2] = -2 * g
    Vm = Z(D, D); Vm[4][3] = 1; K = m
    W1 = Z(2, D); W1[0][0] = 1; W1[0][4] = -K; W1[1][1] = 1; W1[1][4] = K
    W2 = Z(D, 2); W2[5][0] = 1; W2[5][1] = 1
    outW = [0] * D; outW[5] = 1
    return {"embed": emb, "blocks": [{"heads": [{"A": A, "V": Vm, "mask": "strict"}], "W1": W1, "b1": [0, -K], "W2": W2, "b2": [0] * D}], "outW": outW, "outB": 0}

pool = P.make_pool(); rng = np.random.default_rng(3)
cases = [c for c in pool if c["family"] == "carry"][-3:]
for g in (4, 8, 16, 32):
    for c in cases[:2]:
        net = carry_net(c, g); res = {}
        for n, dt in ((300, np.float64), (2000, np.float32), (65534, np.float32)):
            for mult in (0, 1, 4):
                wd = 0.0
                for trial in range(3):
                    w = rng.integers(1, c["V"] + 1, n)
                    if trial == 1:
                        w[2:] = [t + 1 for t in range(c["V"]) if c["cls"][t] == 2][0]
                    q = None if n <= 2000 else np.unique(np.concatenate([np.arange(1, 40), np.arange(n - 40, n + 1), rng.integers(1, n + 1, 120)]))
                    p = R.random_pert(net, mult / 200, rng, "sign") if mult else None
                    y = R.run(net, w, p, dt, q)
                    tg = np.array(P.target(c, list(w)), dtype=float)
                    tg = tg if q is None else tg[q - 1]
                    wd = max(wd, float(np.max(np.abs(y - tg))))
                res["%d/%s/%dtau" % (n, np.dtype(dt).name[-2:], mult)] = round(wd, 4)
        print("gamma", g, c["id"], res, flush=True)
