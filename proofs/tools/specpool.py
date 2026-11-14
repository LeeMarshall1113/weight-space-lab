"""Lane 4 spec pool: random piecewise-linear specs (rung 1) and random 4-bit
boolean functions (rung 0). Stdlib only, exact rational arithmetic.

    python tools/specpool.py pool      # write pool/rung1_pool.json, pool/rung0_pool.json
    python tools/specpool.py draw      # write pool/draw.json (dev, test, reserve ids) + hashes

Expressions are nested tuples:
    ("aff", {i: c}, c0)          sum_i c*x_i + c0
    ("max", a, b) ("min", a, b) ("abs", a) ("relu", a)
    ("clamp", a, lo, hi)         min(max(a, lo), hi)
    ("med3", a, b, c)            median of three
    ("lin", c1, a, c2, b)        c1*a + c2*b
"""
import hashlib, json, os, random, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
POOL_SEED, DRAW_SEED = 20261111, 4042
N_POOL, N_DEV, N_TEST = 300, 4, 20
COEFS = [F(-2), F(-1), F(-1, 2), F(1, 2), F(1), F(2), F(3)]
CONSTS = [F(k, 2) for k in range(-6, 7)]
OPS = ["max", "min", "abs", "relu", "clamp", "med3", "lin"]
ARITY = {"max": 2, "min": 2, "abs": 1, "relu": 1, "clamp": 1, "med3": 3, "lin": 2}


def gen(rng, n_in, budget):
    if budget == 0:
        k = rng.choice([1, 1, 2]) if n_in > 1 else 1
        idx = rng.sample(range(n_in), min(k, n_in))
        return ("aff", {i: rng.choice(COEFS) for i in sorted(idx)}, rng.choice(CONSTS))
    op = rng.choice(OPS)
    if op == "lin":
        rest = budget  # "lin" is free: it only combines
        if budget < 2:
            op = rng.choice(["max", "min", "abs", "relu", "clamp"])
    if op != "lin":
        rest = budget - 1
    ar = ARITY[op]
    parts = [0] * ar
    for _ in range(rest):
        parts[rng.randrange(ar)] += 1
    if op == "lin":
        if 0 in parts:  # both sides must carry a nonlinearity
            parts = [1, rest - 1]
        kids = [gen(rng, n_in, p) for p in parts]
        return ("lin", rng.choice(COEFS), kids[0], rng.choice(COEFS), kids[1])
    kids = [gen(rng, n_in, p) for p in parts]
    if op == "clamp":
        lo, hi = sorted(rng.sample(CONSTS, 2))
        return ("clamp", kids[0], lo, hi)
    return (op,) + tuple(kids)


def ev(e, x, trace=None):
    """Exact evaluation. `trace` collects (node id, branch) pairs."""
    t = e[0]
    if t == "aff":
        return sum(c * x[i] for i, c in e[1].items()) + e[2]
    if t == "lin":
        return e[1] * ev(e[2], x, trace) + e[3] * ev(e[4], x, trace)
    if t == "clamp":
        a = ev(e[1], x, trace)
        b = 0 if a < e[2] else (2 if a > e[3] else 1)
        if trace is not None:
            trace.add((id(e), b))
        return min(max(a, e[2]), e[3])
    vals = [ev(k, x, trace) for k in e[1:]]
    if t == "max":
        b, r = int(vals[0] >= vals[1]), max(vals)
    elif t == "min":
        b, r = int(vals[0] <= vals[1]), min(vals)
    elif t == "abs":
        b, r = int(vals[0] >= 0), abs(vals[0])
    elif t == "relu":
        b, r = int(vals[0] >= 0), max(vals[0], F(0))
    elif t == "med3":
        s = sorted(range(3), key=lambda i: vals[i])
        b, r = s[1], vals[s[1]]
    if trace is not None:
        trace.add((id(e), b))
    return r


def nodes(e):
    if e[0] == "aff":
        return []
    kids = [k for k in e[1:] if isinstance(k, tuple)]
    return [e] + [n for k in kids for n in nodes(k)]


def n_branches(e):
    return {"clamp": 3, "med3": 3}.get(e[0], 2)


def live(e, box, rng, n=3000):
    """Every nonlinear node takes every one of its branches on at least 2% of the box."""
    counts = {}
    for _ in range(n):
        x = [F(rng.randint(lo * 64, hi * 64), 64) for lo, hi in box]
        tr = set()
        ev(e, x, tr)
        for k in tr:
            counts[k] = counts.get(k, 0) + 1
    for nd in nodes(e):
        if nd[0] == "lin":
            continue
        for b in range(n_branches(nd)):
            if counts.get((id(nd), b), 0) < 0.02 * n:
                return False
    return True


def q(c):
    c = F(c)
    return str(c.numerator) if c.denominator == 1 else "%d/%d" % (c.numerator, c.denominator)


def qp(c):  # parenthesised when negative or a fraction
    s = q(c)
    return "(%s)" % s if ("-" in s or "/" in s) else s


def text(e):
    """Same string is valid maths text and a valid Lean term over ℝ (with max/min/|.|)."""
    t = e[0]
    if t == "aff":
        parts = []
        for i, c in e[1].items():
            parts.append("x%d" % i if c == 1 else "%s * x%d" % (qp(c), i))
        if e[2] != 0 or not parts:
            parts.append(qp(e[2]))
        return " + ".join(parts)
    if t == "lin":
        return "%s * (%s) + %s * (%s)" % (qp(e[1]), text(e[2]), qp(e[3]), text(e[4]))
    if t == "max" or t == "min":
        return "%s (%s) (%s)" % (t, text(e[1]), text(e[2]))
    if t == "abs":
        return "|%s|" % text(e[1])
    if t == "relu":
        return "max (%s) 0" % text(e[1])
    if t == "clamp":
        return "min (max (%s) %s) %s" % (text(e[1]), qp(e[2]), qp(e[3]))
    if t == "med3":
        a, b, c = (text(k) for k in e[1:])
        return "max (min (%s) (%s)) (min (max (%s) (%s)) (%s))" % (a, b, a, b, c)


def to_json(e):
    if e[0] == "aff":
        return ["aff", {str(i): q(c) for i, c in e[1].items()}, q(e[2])]
    return [e[0]] + [to_json(k) if isinstance(k, tuple) else q(k) for k in e[1:]]


def from_json(j):
    if j[0] == "aff":
        return ("aff", {int(i): F(c) for i, c in j[1].items()}, F(j[2]))
    return (j[0],) + tuple(from_json(k) if isinstance(k, list) else F(k) for k in j[1:])


def make_pool():
    rng = random.Random(POOL_SEED)
    pool, seen = [], set()
    while len(pool) < N_POOL:
        n_in = rng.choice([1, 2, 2, 2, 2, 2, 3, 3, 3, 3])
        budget = rng.choice([2, 3, 3, 4])
        e = gen(rng, n_in, budget)
        used = set()
        stack = [e]
        while stack:
            k = stack.pop()
            if k[0] == "aff":
                used |= set(k[1])
            else:
                stack += [c for c in k[1:] if isinstance(c, tuple)]
        if used != set(range(n_in)):
            continue
        box = []
        for _ in range(n_in):
            box.append((rng.choice([-8, -4, -2, -1]), rng.choice([1, 2, 4, 8])))
        n_ops = len([n for n in nodes(e) if n[0] != "lin"])
        if n_ops != budget or not live(e, box, rng):
            continue
        s = text(e)
        if s in seen:
            continue
        seen.add(s)
        pool.append({"id": "p%03d" % len(pool), "n_in": n_in, "n_ops": n_ops, "box": box,
                     "expr": to_json(e), "text": s})
    return pool


def make_rung0_pool():
    rng = random.Random(POOL_SEED + 1)
    pool = []
    while len(pool) < 50:
        tt = [rng.random() < 0.5 for _ in range(16)]
        dep = sum(any(tt[i] != tt[i ^ (1 << b)] for i in range(16)) for b in range(4))
        if dep < 4 or sum(tt) in (0, 16):
            continue
        pool.append({"id": "b%02d" % len(pool), "truth_table": [int(v) for v in tt]})
    return pool


def sha(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True).encode()).hexdigest()


if __name__ == "__main__":
    os.makedirs(os.path.join(HERE, "pool"), exist_ok=True)
    p1 = os.path.join(HERE, "pool", "rung1_pool.json")
    p0 = os.path.join(HERE, "pool", "rung0_pool.json")
    if sys.argv[1] == "pool":
        pool, pool0 = make_pool(), make_rung0_pool()
        json.dump(pool, open(p1, "w"), indent=0)
        json.dump(pool0, open(p0, "w"), indent=0)
        print("rung1 pool: %d specs, sha256 %s" % (len(pool), sha(pool)))
        print("rung0 pool: %d specs, sha256 %s" % (len(pool0), sha(pool0)))
        from collections import Counter
        print("n_in:", sorted(Counter(s["n_in"] for s in pool).items()),
              "n_ops:", sorted(Counter(s["n_ops"] for s in pool).items()))
    elif sys.argv[1] == "draw":
        pool, pool0 = json.load(open(p1)), json.load(open(p0))
        rng = random.Random(DRAW_SEED)
        ids = [s["id"] for s in pool]
        rng.shuffle(ids)
        ids0 = [s["id"] for s in pool0]
        rng.shuffle(ids0)
        draw = {"pool_seed": POOL_SEED, "draw_seed": DRAW_SEED,
                "rung1_dev": ids[:N_DEV], "rung1_test": ids[N_DEV:N_DEV + N_TEST],
                "rung1_reserve": ids[N_DEV + N_TEST:N_DEV + N_TEST + 10],
                "rung0": ids0[:3], "pool_sha256": sha(pool), "pool0_sha256": sha(pool0)}
        json.dump(draw, open(os.path.join(HERE, "pool", "draw.json"), "w"), indent=1)
        print("draw written; test-set sha256", sha(draw["rung1_test"]))
        print("dev ids:", draw["rung1_dev"], "(test ids are in pool/draw.json; do not read the specs before the prompt freeze)")
