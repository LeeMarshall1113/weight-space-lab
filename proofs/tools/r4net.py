"""Numeric evaluator for the rung-4 transformer of Lane4/RSeq.lean (numpy).

Follows the Lean definition operation by operation: every product, sum and quotient is
rounded to `dtype` (float32 = the modelled rounding with u = 2^-24, barring overflow and
underflow; float64 stands in for exact arithmetic), sums run left to right, stored weights
are round(w * (1 + d)), position features are [1, fl i, fl n].

Steps whose weight is exactly 0 are skipped: in the model they add an exact 0 to a value
that is already rounded, which changes nothing.

A net is a dict:
  {"embed": [[..],..], "blocks": [{"heads": [{"A": M, "V": M, "mask": "all|causal|strict"}],
                                   "W1": M, "b1": v, "W2": M, "b2": v}], "outW": v, "outB": q}
A perturbation is a dict with the same layout holding the relative offsets d (missing = 0).
"""
import numpy as np


def _arr(M, shape=None):
    a = np.array(M, dtype=np.float64)
    return a.reshape(shape) if shape is not None else a


def stored(net, pert, dtype):
    """Stored weights round(w * (1 + d)) as dtype arrays, same layout as the net."""
    def sw(w, d):
        w = np.array(w, dtype=np.float64)
        if d is None:
            return w.astype(dtype)
        return (w * (1.0 + np.array(d, dtype=np.float64).reshape(w.shape))).astype(dtype)
    p = pert or {}
    D = len(net["embed"][0]) + 3
    out = {"embed": sw(net["embed"], p.get("embed")), "outW": sw(net["outW"], p.get("outW")),
           "outB": sw(net["outB"], p.get("outB")), "blocks": []}
    for b, B in enumerate(net["blocks"]):
        pb = p.get("blocks", [{}] * len(net["blocks"]))[b]
        H = len(B["b1"])
        blk = {"heads": [], "W1": sw(_arr(B["W1"], (H, D)), pb.get("W1")), "b1": sw(B["b1"], pb.get("b1")),
               "W2": sw(_arr(B["W2"], (D, H)), pb.get("W2")), "b2": sw(B["b2"], pb.get("b2"))}
        for k, h in enumerate(B["heads"]):
            ph = pb.get("heads", [{}] * len(B["heads"]))[k]
            blk["heads"].append({"A": sw(h["A"], ph.get("A")), "V": sw(h["V"], ph.get("V")), "mask": h["mask"]})
        out["blocks"].append(blk)
    return out


def rdot(row, X):
    """Rounded left-to-right dot product of a stored weight row with each row of X."""
    acc = np.zeros(X.shape[0], dtype=X.dtype)
    for k in np.nonzero(row)[0]:
        acc = acc + row[k] * X[:, k]
    return acc


def rmat(M, X):
    return np.stack([rdot(M[r], X) for r in range(M.shape[0])], axis=1)


def attend(h, X, Q, chunk=4_000_000):
    """Head output at query positions Q (array of indices) given the full state X."""
    n, D = X.shape
    dt = X.dtype
    rows = [r for r in range(D) if np.any(h["A"][r] != 0)]
    vrows = [r for r in range(D) if np.any(h["V"][r] != 0)]
    AX = {r: rdot(h["A"][r], X) for r in rows}         # only the rows that can be non-zero
    VX = {r: rdot(h["V"][r], X) for r in vrows}
    out = np.zeros((len(Q), D), dtype=dt)
    step = max(1, chunk // n)
    j = np.arange(n)
    for s in range(0, len(Q), step):
        q = Q[s:s + step]
        sc = np.zeros((len(q), n), dtype=dt)
        for r in rows:
            sc = sc + X[q, r][:, None] * AX[r][None, :]
        if h["mask"] == "causal":
            ok = j[None, :] <= q[:, None]
        elif h["mask"] == "strict":
            ok = j[None, :] < q[:, None]
        else:
            ok = np.ones((len(q), n), dtype=bool)
        scm = np.where(ok, sc, -np.inf)
        sel = ok & (scm == scm.max(axis=1, keepdims=True))
        cnt = sel.sum(axis=1)
        for r in vrows:
            vals = np.where(sel, VX[r][None, :], dt.type(0))
            tot = np.cumsum(vals, axis=1, dtype=dt)[:, -1]
            with np.errstate(invalid="ignore", divide="ignore"):
                avg = (tot / cnt.astype(dt)).astype(dt)
            out[s:s + step, r] = np.where(cnt > 0, avg, dt.type(0))
    return out


def run(net, w, pert=None, dtype=np.float64, queries=None):
    """Outputs at the query positions (default: positions 1..len(w)). Returns a float64 array."""
    dt = np.dtype(dtype)
    S = stored(net, pert, dt)
    toks = np.concatenate([[0], np.asarray(w, dtype=np.int64)])
    n = len(toks)
    pos = np.stack([np.ones(n, dtype=dt), np.arange(n).astype(dt), np.full(n, n).astype(dt)], axis=1)
    X = np.concatenate([S["embed"][toks], pos], axis=1)
    Qfinal = np.arange(1, n) if queries is None else np.asarray(queries, dtype=np.int64)
    nb = len(S["blocks"])
    Q = np.arange(n)
    for b, B in enumerate(S["blocks"]):
        if b == nb - 1:
            Q = Qfinal
        Y = X[Q].copy()
        for h in B["heads"]:
            Y = Y + attend(h, X, Q)
        if len(B["b1"]):
            hid = np.maximum(rmat(B["W1"], Y) + B["b1"][None, :], dt.type(0))
            Y = Y + (rmat(B["W2"], hid) + B["b2"][None, :])
        else:
            Y = Y + np.broadcast_to(B["b2"][None, :], Y.shape)
        X = Y
    if nb == 0:
        X = X[Qfinal]
    return (rdot(S["outW"], X) + S["outB"]).astype(np.float64)


def random_pert(net, tau, rng, kind="uniform"):
    """A relative perturbation with every |d| <= tau (uniform or sign corners)."""
    def draw(shape):
        return rng.uniform(-tau, tau, shape) if kind == "uniform" else tau * rng.choice([-1.0, 1.0], shape)
    D = len(net["embed"][0]) + 3
    p = {"embed": draw(np.shape(net["embed"])), "outW": draw((D,)), "outB": draw(()), "blocks": []}
    for B in net["blocks"]:
        H = len(B["b1"])
        p["blocks"].append({"W1": draw((H, D)), "b1": draw((H,)), "W2": draw((D, H)), "b2": draw((D,)),
                            "heads": [{"A": draw((D, D)), "V": draw((D, D))} for _ in B["heads"]]})
    return p


EXAMPLE_NET = {  # the worked example: output the previous token
    "embed": [[0, 0], [1, 0], [2, 0]],
    "blocks": [{"heads": [{"A": [[0] * 5, [0] * 5, [0, 0, 0, 1, 0], [0] * 5, [0] * 5],
                           "V": [[0] * 5, [1, 0, 0, 0, 0], [0] * 5, [0] * 5, [0] * 5], "mask": "strict"}],
                "W1": [], "b1": [], "W2": [[]] * 5, "b2": [0] * 5}],
    "outW": [0, 1, 0, 0, 0], "outB": 0}


if __name__ == "__main__":
    rng = np.random.default_rng(0)
    for n, dt in ((50, np.float64), (5000, np.float32), (65534, np.float32)):
        w = rng.integers(1, 3, n)
        q = None if n <= 5000 else np.concatenate([np.arange(1, 200), rng.integers(1, n + 1, 300), [n]])
        for tau in (0.0, 1 / 200):
            p = random_pert(EXAMPLE_NET, tau, rng, "sign") if tau else None
            y = run(EXAMPLE_NET, w, p, dt, q)
            tgt = np.concatenate([[0], w])[(np.arange(1, n + 1) if q is None else q) - 1]
            print("example net  n=%6d  %s  tau=%.4f  max dev %.3e" % (n, np.dtype(dt).name, tau, np.max(np.abs(y - tgt))))
