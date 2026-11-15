"""Rung-6a feasibility probe (not a result, nothing proved): a hand-built GATED network for
the carry task under ADDITIVE noise on every weight, zeros included.

Architecture tried (writeup/NOTE_open_problems.md, section 2):
  * state = token embedding only (width 7), NO position coordinates;
  * one head: a key j is a candidate for query i iff j < i and its gate neuron
    relu(wg . x_j + bg) is exactly 0; score = -m (i - j) + x_i^T A x_j with A written as 0;
    hard attention (ties averaged) or softmax; value V x_j added to the query's state;
  * a two-unit ReLU MLP and a linear read-out, as in the rung-4 carry construction.
Every weight (embedding, gate neuron, slope m, A, V, MLP, read-out), written zeros
included, is moved by +delta or -delta (sign corners). Deviation = |output - target|.

    python scratch/r6_probe.py      -> results/r6-probe.json
"""
import json, os, sys, time
import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tools"))
import r4pool as P

HERE = P.HERE


def build(c):
    V, m = c["V"], c["m"]
    # columns: dA, dB, prop, gen, c (carry slot), o (output slot), one
    E = np.zeros((V + 1, 7))
    E[0] = [0, 0, 0, 0, 0, 0, 1]
    for t in range(V):
        E[t + 1] = [c["dg"][t], (c["dg"][t] + 1) % m, 1 if c["cls"][t] == 2 else 0, 1 if c["cls"][t] == 1 else 0, 0, 0, 1]
    wg = np.zeros(7); wg[2] = 1.0; bg = -0.5                 # gate neuron: > 0 exactly on propagate keys
    A = np.zeros((7, 7)); slope = 4.0
    Vm = np.zeros((7, 7)); Vm[4, 3] = 1.0                    # copy gen into the carry slot
    K = float(m)
    W1 = np.zeros((2, 7)); W1[0, 0] = 1; W1[0, 4] = -K; W1[1, 1] = 1; W1[1, 4] = K
    b1 = np.array([0.0, -K])
    W2 = np.zeros((7, 2)); W2[5, 0] = 1; W2[5, 1] = 1
    outW = np.zeros(7); outW[5] = 1
    return {"E": E, "wg": wg, "bg": np.array(bg), "A": A, "slope": np.array(slope), "V": Vm, "W1": W1, "b1": b1, "W2": W2, "outW": outW, "outB": np.array(0.0)}


def perturb(N, delta, rng):
    return {k: v + delta * rng.choice([-1.0, 1.0], np.shape(v)) for k, v in N.items()}


def run(N, w, q, dtype=np.float64, soft=False):
    dt = np.dtype(dtype)
    M = {k: np.asarray(v, dtype=dt) for k, v in N.items()}
    toks = np.concatenate([[0], w]); n = len(toks)
    X = M["E"][toks]                                          # (n, 7)
    gate = np.maximum(X @ M["wg"] + M["bg"], 0)               # exactly 0 on wanted keys
    cand = gate == 0
    j = np.arange(n)
    Y = X[q].copy()
    AX = X @ M["A"].T                                         # row j: A x_j
    VX = X @ M["V"].T
    for a in range(0, len(q), 256):
        qq = q[a:a + 256]
        sc = -M["slope"] * (qq[:, None] - j[None, :]).astype(dt) + X[qq] @ AX.T
        ok = (j[None, :] < qq[:, None]) & cand[None, :]
        scm = np.where(ok, sc, -np.inf)
        mx = scm.max(axis=1, keepdims=True)
        if soft:
            with np.errstate(under="ignore", invalid="ignore"):
                e = np.where(ok, np.exp(np.where(ok, sc - mx, 0)), 0).astype(dt)
        else:
            e = (ok & (scm == mx)).astype(dt)
        Z = e.sum(axis=1, keepdims=True)
        Y[a:a + 256] += np.where(Z > 0, (e @ VX) / np.where(Z > 0, Z, 1), 0)
    H = np.maximum(Y @ M["W1"].T + M["b1"], 0)
    Y = Y + H @ M["W2"].T
    return (Y @ M["outW"] + M["outB"]).astype(np.float64)


if __name__ == "__main__":
    pool = P.make_pool()
    cases = [c for c in pool if c["family"] == "carry" and c["id"] in ("c37", "c38", "c39")]
    rng = np.random.default_rng(6)
    rows = []
    t0 = time.time()
    for c in cases:
        N = build(c)
        for soft in (False, True):
            for delta in (0.0, 1e-3, 4e-3, 1.6e-2):
                for n in (20, 1000, 20000, 65534):
                    worst = 0.0
                    for trial in range(1 if delta == 0 else 20):
                        w = rng.integers(1, c["V"] + 1, n)
                        if trial % 3 == 1:                    # long propagate run after one generate token
                            w[1:] = [t + 1 for t in range(c["V"]) if c["cls"][t] == 2][0]
                        if trial % 3 == 2:                    # alternate two different non-propagate tokens
                            nz = [t + 1 for t in range(c["V"]) if c["cls"][t] != 2]
                            w = np.array([nz[k % len(nz)] for k in range(n)])
                        q = np.arange(1, n + 1) if n <= 1000 else np.unique(np.concatenate([np.arange(1, 60), np.arange(n - 60, n + 1), rng.integers(1, n + 1, 200)]))
                        Np = perturb(N, delta, rng) if delta else N
                        y = run(Np, w, q, np.float32 if n > 1000 else np.float64, soft)
                        tg = np.array(P.target(c, [int(t) for t in w]), dtype=float)[q - 1]
                        worst = max(worst, float(np.max(np.abs(y - tg))))
                    rows.append({"id": c["id"], "attention": "softmax" if soft else "hard", "delta": delta, "length": n,
                                 "dtype": "float32" if n > 1000 else "float64", "worst_dev": worst})
                    print(c["id"], "soft" if soft else "hard", "delta %.4f" % delta, "n %6d" % n, "worst dev %.4f" % worst, flush=True)
    json.dump(rows, open(os.path.join(HERE, "results", "r6-probe.json"), "w"), indent=1)
    print("done in %.0f s" % (time.time() - t0))
