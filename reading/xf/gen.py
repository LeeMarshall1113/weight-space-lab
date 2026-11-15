"""Random RASP program pool for the transformer stage (PREREG_XF.md).

Every program is built from a small set of templates whose outputs are always defined
(no categorical Aggregate over disagreeing values), with random lookup tables and
comparisons, so there is no famous task to guess. `random_program(seed)` returns
(program SOp, source string, info). The source string uses only xf.rasp / tracr.rasp names
and is what the true program "is"; it is never shown to the doctor.
"""
from __future__ import annotations

import itertools

import numpy as np

from xf import rasp as R

CMPS = ["EQ", "LT", "LEQ", "GT", "GEQ", "NEQ"]


def _table(rng, keys, n_out):
    vals = rng.integers(0, n_out, size=len(keys))
    if len(set(vals.tolist())) == 1:  # avoid constant tables
        vals[0] = (vals[0] + 1) % n_out
    return {k: int(v) for k, v in zip(keys, vals)}


def _src_table(t):
    return "{" + ", ".join(f"{k!r}: {v}" for k, v in t.items()) + "}"


def random_program(seed: int, vocab_size: int | None = None):
    rng = np.random.default_rng(seed)
    V = int(vocab_size or rng.integers(3, 6))
    vocab = [chr(ord("a") + i) for i in range(V)]
    template = rng.choice(["count", "count_combine", "permute", "count_cmp"])
    lines = []

    def operand(name):
        """tokens, indices, or a Map(table) of tokens."""
        kind = rng.choice(["tokens", "indices", "map"], p=[0.4, 0.25, 0.35])
        if kind == "tokens":
            return R.tokens, "tokens"
        if kind == "indices":
            return R.indices, "indices"
        t = _table(rng, vocab, int(rng.integers(2, 4)))
        lines.append(f"{name} = Map(lambda x: {_src_table(t)}[x], tokens)")
        return R.Map(lambda x, t=t: t[x], R.tokens), name

    def same_kind(a_src, b_src):
        # Select needs comparable operands: tokens are str, indices and Maps are int
        return (a_src == "tokens") == (b_src == "tokens")

    if template in ("count", "count_combine", "count_cmp"):
        while True:
            k, ks = operand("k")
            q, qs = operand("q")
            if same_kind(ks, qs):
                break
            lines.clear()
        cmp = CMPS[int(rng.integers(len(CMPS)))]
        lines.append(f"w = SelectorWidth(Select({ks}, {qs}, Comparison.{cmp}))")
        w = R.SelectorWidth(R.Select(k, q, getattr(R.Comparison, cmp)))
        if template == "count":
            m = int(rng.integers(2, 4))
            lines.append(f"out = Map(lambda x: x % {m}, w)")
            out = R.Map(lambda x, m=m: x % m, w)
        elif template == "count_cmp":
            th = int(rng.integers(1, 4))
            lines.append(f"out = Map(lambda x: 1 if x >= {th} else 0, w)")
            out = R.Map(lambda x, th=th: 1 if x >= th else 0, w)
        else:
            t2 = _table(rng, vocab, 2)
            lines.append(f"g = Map(lambda x: {_src_table(t2)}[x], tokens)")
            g = R.Map(lambda x, t2=t2: t2[x], R.tokens)
            m = int(rng.integers(2, 4))
            lines.append(f"out = SequenceMap(lambda x, y: (x + y) % {m}, w, g)")
            out = R.SequenceMap(lambda x, y, m=m: (x + y) % m, w, g)
    else:  # permute: out[i] = f(token[pi(i)]) for a random index map pi, default for no match
        fam = rng.choice(["rev", "shl", "shr"])
        lines.append("n = SelectorWidth(Select(tokens, tokens, Comparison.TRUE))")
        n = R.SelectorWidth(R.Select(R.tokens, R.tokens, R.Comparison.TRUE))
        if fam == "rev":
            lines.append("src = SequenceMap(lambda i, n: n - i - 1, indices, n)")
            src = R.SequenceMap(lambda i, n: n - i - 1, R.indices, n)
        elif fam == "shl":
            lines.append("src = SequenceMap(lambda i, n: i + 1, indices, n)")
            src = R.SequenceMap(lambda i, n: i + 1, R.indices, n)
        else:
            lines.append("src = SequenceMap(lambda i, n: i - 1, indices, n)")
            src = R.SequenceMap(lambda i, n: i - 1, R.indices, n)
        t = _table(rng, vocab, int(rng.integers(2, V + 1)))
        lines.append(f"val = Map(lambda x: {_src_table(t)}[x], tokens)")
        val = R.Map(lambda x, t=t: t[x], R.tokens)
        dflt = int(rng.integers(0, 3))
        lines.append(f"out = Aggregate(Select(indices, src, Comparison.EQ), val, default={dflt})")
        out = R.Aggregate(R.Select(R.indices, src, R.Comparison.EQ), val, default=dflt)
    return out, "\n".join(lines), {"seed": seed, "vocab": vocab, "template": str(template)}


def sample_inputs(rng, vocab, n, lo=4, hi=8):
    lens = rng.integers(lo, hi + 1, size=n)
    return [[vocab[i] for i in rng.integers(0, len(vocab), size=L)] for L in lens]


def acceptable(prog, vocab, seed=0) -> tuple[bool, dict]:
    """Reject programs whose output is constant, a function of length alone, a function
    of position alone, or a function of the same-position token alone."""
    rng = np.random.default_rng(seed)
    xs = sample_inputs(rng, vocab, 400)
    ys = [R.evaluate(prog, x) for x in xs]
    flat = [v for y in ys for v in y]
    if any(v is None for v in flat) or len(set(flat)) < 2:
        return False, {"why": "constant or undefined"}
    def det(key):
        seen = {}
        for x, y in zip(xs, ys):
            for i, v in enumerate(y):
                k = key(x, i)
                if seen.setdefault(k, v) != v:
                    return False
        return True
    for name, key in [("length", lambda x, i: len(x)), ("position", lambda x, i: (i, len(x))),
                      ("token", lambda x, i: x[i])]:
        if det(key):
            return False, {"why": f"function of {name} only"}
    vals = sorted(set(flat))
    return True, {"out_values": vals}


def draw(n, seed):
    """n acceptable programs from a seeded stream of the pool."""
    rng = np.random.default_rng(seed)
    out = []
    for s in itertools.count():
        ps = int(rng.integers(0, 10**6))
        prog, src, info = random_program(ps)
        ok, extra = acceptable(prog, info["vocab"])
        if ok:
            out.append((prog, src, {**info, **extra}))
            if len(out) == n:
                return out
