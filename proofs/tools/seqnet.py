"""Exact (Fraction) reference evaluator for the rung-2 transformer of Lane4/Seq.lean.

A net is a dict:
  {"embed": [[..],..], "blocks": [{"heads": [{"A": M, "V": M, "mask": "all|causal|strict"}],
                                   "W1": M, "b1": v, "W2": M, "b2": v}], "outW": v, "outB": q}
Token 0 is BOS and is prepended here, as in the Lean definition.
"""
from fractions import Fraction as F


def qdot(a, b):
    return sum((u * v for u, v in zip(a, b)), F(0))


def matvec(M, x):
    return [qdot(r, x) for r in M]


def vadd(a, b):
    return [u + v for u, v in zip(a, b)]


def pos(i, n):
    i, n = F(i), F(n)
    return [F(1), i, i * i, 1 / (i + 1), F(-1) ** int(i), n, 1 / n, i / n]


def cand(mask, n, i):
    return list(range(n)) if mask == "all" else list(range(i + 1)) if mask == "causal" else list(range(i))


def attn(h, n, x, i):
    c = cand(h["mask"], n, i)
    sc = {j: qdot(x[i], matvec(h["A"], x[j])) for j in c}
    S = [j for j in c if all(sc[k] <= sc[j] for k in c)]
    out = []
    for r in range(len(h["V"])):
        out.append(sum((qdot(h["V"][r], x[j]) for j in S), F(0)) / len(S) if S else F(0))
    return out


def run(net, w):
    toks = [0] + list(w)
    n = len(toks)
    x = [[F(v) for v in net["embed"][t]] + pos(i, n) for i, t in enumerate(toks)]
    for B in net["blocks"]:
        new = []
        for i in range(n):
            y = x[i]
            for h in B["heads"]:
                y = vadd(y, attn(h, n, x, i))
            hid = [max(qdot(r, y) + c, F(0)) for r, c in zip(B["W1"], B["b1"])]
            new.append(vadd(y, [qdot(r, hid) + c for r, c in zip(B["W2"], B["b2"])]))
        x = new
    return [qdot(net["outW"], xi) + F(net["outB"]) for xi in x]


def zeros(r, c):
    return [[F(0)] * c for _ in range(r)]


def shape_ok(net, ntok):
    de = len(net["embed"][0])
    d = de + 8
    ok = d <= 24 and len(net["embed"]) == ntok + 1 and all(len(r) == de for r in net["embed"])
    ok = ok and len(net["blocks"]) <= 4 and len(net["outW"]) == d
    for B in net["blocks"]:
        hd = len(B["b1"])
        ok = ok and len(B["heads"]) <= 4 and hd <= 32
        ok = ok and len(B["W1"]) == hd and all(len(r) == d for r in B["W1"])
        ok = ok and len(B["W2"]) == d and all(len(r) == hd for r in B["W2"]) and len(B["b2"]) == d
        for h in B["heads"]:
            ok = ok and all(len(M) == d and all(len(r) == d for r in M) for M in (h["A"], h["V"]))
    return ok
