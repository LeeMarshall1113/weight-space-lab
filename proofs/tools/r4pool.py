"""Rung-4 case pool (PREREG_R4.md). Stdlib only.

    python tools/r4pool.py pool   # pool/rung4_pool.json
    python tools/r4pool.py draw   # pool/draw4.json (dev, test, reserve ids); prints dev only

Four families of per-position tasks. Tokens are 1..V; the target at position i is a small
natural number. All four can be solved by unique hard attention to the nearest or the
first position of a kind, which is why a weight ball that does not shrink with length is
possible for them (NOVELTY.md, rung-4 section). Counting tasks are deliberately absent.

    carry   V in 3..5, modulus m in 2..3, each token is generate / kill / propagate
            (each class non-empty) and has a digit dg in 0..m-1 (not constant).
            target_i = (dg(tok_i) + carry into i) mod m
    last    V in 3..5, a non-empty proper subset of marked tokens with values in 1..3
            (not all equal). target_i = value of the last marked token at or before i, else 0
    first   V in 3..5, marked tokens carry a bit a (both bits occur), every token has a
            bit c (not constant). target_i = (a(first marked token at or before i, 0 if
            none) + c(tok_i)) mod 2
    induct  V in 2..3, a table h : token -> 0..2 (not constant).
            target_i = h(token right after the most recent earlier occurrence of tok_i),
            0 if tok_i has not occurred before
"""
import hashlib, itertools, json, os, random, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
POOL_SEED, DRAW_SEED, CAP = 20261114, 4045, 40
N_DEV, N_TEST, N_RESERVE = 1, 3, 2
FAMILIES = ("carry", "last", "first", "induct")
# settings the lane used for its own numeric feasibility check before the prereg
# (scratch/r4_feas.py); kept out of the draw
FEASIBILITY_IDS = {"c34", "c35", "c36", "c37", "c38", "c39", "i24", "i25", "i26", "i27", "i28", "i29"}


def all_cases():
    fam = {f: [] for f in FAMILIES}
    for V in (3, 4, 5):
        for m in (2, 3):
            for cls in itertools.product((0, 1, 2), repeat=V):      # 0 kill, 1 generate, 2 propagate
                if set(cls) != {0, 1, 2}:
                    continue
                for dg in itertools.product(range(m), repeat=V):
                    if len(set(dg)) > 1:
                        fam["carry"].append({"V": V, "m": m, "cls": list(cls), "dg": list(dg)})
        for val in itertools.product((0, 1, 2, 3), repeat=V):       # 0 = unmarked
            marked = [v for v in val if v]
            if 0 in val and len(set(marked)) > 1:
                fam["last"].append({"V": V, "val": list(val)})
        for code in itertools.product((0, 1, 2), repeat=V):         # 0 unmarked, 1 a=0, 2 a=1
            if set(code) != {0, 1, 2}:
                continue
            for c in itertools.product((0, 1), repeat=V):
                if len(set(c)) > 1:
                    fam["first"].append({"V": V, "code": list(code), "c": list(c)})
    for V in (2, 3):
        for h in itertools.product((0, 1, 2), repeat=V):
            if len(set(h)) > 1:
                fam["induct"].append({"V": V, "h": list(h)})
    return fam


def make_pool():
    rng = random.Random(POOL_SEED)
    pool = []
    for name in FAMILIES:
        cases = all_cases()[name]
        rng.shuffle(cases)
        for k, c in enumerate(cases[:CAP]):
            pool.append(dict(c, family=name, id="%s%02d" % (name[0], k)))
    return pool


def sha(o):
    return hashlib.sha256(json.dumps(o, sort_keys=True).encode()).hexdigest()


# ---------- reference semantics (used by the lane checks and the smoke test) ----------

def target(c, w):
    """Targets at positions 1..len(w) for token list w (tokens 1..V)."""
    fam, out = c["family"], []
    if fam == "carry":
        carry = 0
        for t in w:
            out.append((c["dg"][t - 1] + carry) % c["m"])
            k = c["cls"][t - 1]
            carry = carry if k == 2 else k
    elif fam == "last":
        s = 0
        for t in w:
            s = c["val"][t - 1] or s
            out.append(s)
    elif fam == "first":
        s = 0
        for t in w:
            s = s or c["code"][t - 1]
            out.append(((1 if s == 2 else 0) + c["c"][t - 1]) % 2)
    else:
        for i, t in enumerate(w):
            v = 0
            for j in range(i - 1, -1, -1):
                if w[j] == t:
                    v = c["h"][w[j + 1] - 1]
                    break
            out.append(v)
    return out


if __name__ == "__main__":
    os.makedirs(os.path.join(HERE, "pool"), exist_ok=True)
    pp = os.path.join(HERE, "pool", "rung4_pool.json")
    if sys.argv[1] == "pool":
        pool = make_pool()
        json.dump(pool, open(pp, "w"), indent=0)
        from collections import Counter
        print("rung4 pool: %d cases %s (of %s possible) sha256 %s" % (
            len(pool), dict(Counter(c["family"] for c in pool)),
            {k: len(v) for k, v in all_cases().items()}, sha(pool)))
    elif sys.argv[1] == "draw":
        pool = json.load(open(pp))
        rng = random.Random(DRAW_SEED)
        by = {}
        for c in pool:
            if c["id"] not in FEASIBILITY_IDS:
                by.setdefault(c["family"], []).append(c["id"])
        dev, test, reserve = [], [], []
        for name in FAMILIES:
            ids = by[name]
            rng.shuffle(ids)
            dev += ids[:N_DEV]
            test += ids[N_DEV:N_DEV + N_TEST]
            reserve += ids[N_DEV + N_TEST:N_DEV + N_TEST + N_RESERVE]
        draw = {"pool_seed": POOL_SEED, "draw_seed": DRAW_SEED, "rung4_dev": dev, "rung4_test": test,
                "rung4_reserve": reserve, "pool_sha256": sha(pool)}
        json.dump(draw, open(os.path.join(HERE, "pool", "draw4.json"), "w"), indent=1)
        print("draw written; test-set sha256", sha(test), "| %d dev, %d test, %d reserve" % (len(dev), len(test), len(reserve)))
        print("dev ids:", dev, "(test ids are in pool/draw4.json; do not read them before the prompt freeze)")
