"""Numeric evaluator for the rung-6a gated transformer of Lane4/AGate.lean (numpy).

Follows the stated order: stored weight = round(w + d) (ADDITIVE perturbation), every
product and sum rounded to `dtype`, sums left to right, gate = relu(g'.x + gb') and a key
is a candidate iff the mask allows it and its gate is exactly 0, score = round(round(m' *
(j - i)) + x_i . (A' x_j)), max-subtracted softmax over the candidates, an empty candidate
list gives 0. No position features in the state.

A net is a dict:
  {"embed": M, "blocks": [{"heads": [{"A": M, "V": M, "mask": "all|causal|strict", "m": q,
                                      "g": v, "gb": q}], "W1": M, "b1": v, "W2": M, "b2": v}],
   "outW": v, "outB": q}
A perturbation has the same layout and holds the additive offsets d (missing = 0).
Unlike the rung-4/5 evaluators, zero weights are NOT skipped: a perturbed zero is not zero.
"""
import numpy as np


def _a(M, shape=None):
    a = np.array(M, dtype=np.float64)
    return a.reshape(shape) if shape is not None else a


def stored(net, pert, dtype):
    def sw(w, d, shape=None):
        w = _a(w, shape)
        return (w if d is None else w + np.array(d, dtype=np.float64).reshape(w.shape)).astype(dtype)
    p = pert or {}
    D = len(net["embed"][0])
    out = {"embed": sw(net["embed"], p.get("embed")), "outW": sw(net["outW"], p.get("outW")),
           "outB": sw(net["outB"], p.get("outB")), "blocks": []}
    for b, B in enumerate(net["blocks"]):
        pb = p.get("blocks", [{}] * len(net["blocks"]))[b]
        H = len(B["b1"])
        blk = {"heads": [], "W1": sw(B["W1"], pb.get("W1"), (H, D)), "b1": sw(B["b1"], pb.get("b1")),
               "W2": sw(B["W2"], pb.get("W2"), (D, H)), "b2": sw(B["b2"], pb.get("b2"))}
        for k, h in enumerate(B["heads"]):
            ph = pb.get("heads", [{}] * len(B["heads"]))[k]
            blk["heads"].append({"A": sw(h["A"], ph.get("A")), "V": sw(h["V"], ph.get("V")), "mask": h["mask"],
                                 "m": sw(h["m"], ph.get("m")), "g": sw(h["g"], ph.get("g")), "gb": sw(h["gb"], ph.get("gb"))})
        out["blocks"].append(blk)
    return out


def rdot(row, X):
    """Rounded left-to-right dot product of a stored row with each row of X (all terms)."""
    acc = np.zeros(X.shape[0], dtype=X.dtype)
    for k in range(len(row)):
        acc = acc + row[k] * X[:, k]
    return acc


def rmat(M, X):
    return np.stack([rdot(M[r], X) for r in range(M.shape[0])], axis=1) if M.shape[0] else np.zeros((X.shape[0], 0), X.dtype)


def attend(h, X, Q, chunk=3_000_000):
    n, D = X.shape
    dt = X.dtype
    gate = np.maximum(rdot(h["g"], X) + h["gb"], dt.type(0))
    cand = gate == 0
    AX = rmat(h["A"], X)                       # row j: A' x_j
    VX = rmat(h["V"], X)
    out = np.zeros((len(Q), D), dtype=dt)
    step = max(1, chunk // n)
    j = np.arange(n)
    for s in range(0, len(Q), step):
        q = Q[s:s + step]
        content = np.zeros((len(q), n), dtype=dt)
        for r in range(D):                     # pdot: left to right over the query's entries
            content = content + X[q, r][:, None] * AX[:, r][None, :]
        bias = (h["m"] * (j[None, :] - q[:, None]).astype(dt)).astype(dt)
        sc = (bias + content).astype(dt)
        ok = cand[None, :] & ((j[None, :] <= q[:, None]) if h["mask"] == "causal" else
                              (j[None, :] < q[:, None]) if h["mask"] == "strict" else np.ones((len(q), n), bool))
        m = np.where(ok, sc, -np.inf).max(axis=1, keepdims=True)
        m = np.where(np.isfinite(m), m, 0).astype(dt)
        with np.errstate(under="ignore"):
            e = np.where(ok, np.exp(np.where(ok, (sc - m).astype(dt), dt.type(0))), dt.type(0)).astype(dt)
        Z = np.cumsum(e, axis=1, dtype=dt)[:, -1]
        for r in range(D):
            with np.errstate(under="ignore"):
                num = np.cumsum((e * VX[:, r][None, :]).astype(dt), axis=1, dtype=dt)[:, -1]
            with np.errstate(invalid="ignore", divide="ignore"):
                out[s:s + step, r] = np.where(Z > 0, (num / Z).astype(dt), dt.type(0))
    return out


def run(net, w, pert=None, dtype=np.float32, queries=None):
    dt = np.dtype(dtype)
    S = stored(net, pert, dt)
    toks = np.concatenate([[0], np.asarray(w, dtype=np.int64)])
    n = len(toks)
    X = S["embed"][toks]
    Qfinal = np.arange(1, n) if queries is None else np.asarray(queries, dtype=np.int64)
    nb = len(S["blocks"])
    Q = np.arange(n)
    for b, B in enumerate(S["blocks"]):
        if b == nb - 1:
            Q = Qfinal
        Y = X[Q].copy()
        for h in B["heads"]:
            Y = Y + attend(h, X, Q)
        hid = np.maximum(rmat(B["W1"], Y) + B["b1"][None, :], dt.type(0))
        Y = Y + (rmat(B["W2"], hid) + B["b2"][None, :])
        X = Y
    if nb == 0:
        X = X[Qfinal]
    return (rdot(S["outW"], X) + S["outB"]).astype(np.float64)


def random_pert(net, delta, rng, kind="sign"):
    draw = (lambda shape: rng.uniform(-delta, delta, shape)) if kind == "uniform" else \
        (lambda shape: delta * rng.choice([-1.0, 1.0], shape))
    D = len(net["embed"][0])
    p = {"embed": draw(np.shape(net["embed"])), "outW": draw((D,)), "outB": draw(()), "blocks": []}
    for B in net["blocks"]:
        H = len(B["b1"])
        p["blocks"].append({"W1": draw((H, D)), "b1": draw((H,)), "W2": draw((D, H)), "b2": draw((D,)),
                            "heads": [{"A": draw((D, D)), "V": draw((D, D)), "m": draw(()), "g": draw((D,)), "gb": draw(())}
                                      for _ in B["heads"]]})
    return p


EXAMPLE_NET = {  # the worked example (runs/r6-kit/kX): output the previous token
    "embed": [[0, 0, 1], [1, 0, 1], [2, 0, 1]],
    "blocks": [{"heads": [{"A": [[0] * 3] * 3, "V": [[0, 0, 0], [1, 0, 0], [0, 0, 0]], "mask": "strict",
                           "m": 24, "g": [0, 0, 0], "gb": -1}],
                "W1": [], "b1": [], "W2": [[], [], []], "b2": [0, 0, 0]}],
    "outW": [0, 1, 0], "outB": 0}

if __name__ == "__main__":
    for n in (50, 5000, 65534):
        rw = np.random.default_rng(1)
        w = rw.integers(1, 3, n)
        q = None if n <= 5000 else np.concatenate([np.arange(1, 200), rw.integers(1, n + 1, 300), [n]])
        tgt = np.concatenate([[0], w])[(np.arange(1, n + 1) if q is None else q) - 1]
        for mult in (0, 1, 64, 128):
            p = random_pert(EXAMPLE_NET, mult / 1000, np.random.default_rng(mult), "sign") if mult else None
            y = run(EXAMPLE_NET, w, p, np.float32, q)
            print("example net  n=%6d  additive %3d/1000  max dev %.4f" % (n, mult, np.max(np.abs(y - tgt))), flush=True)
