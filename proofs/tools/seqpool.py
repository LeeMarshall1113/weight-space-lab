"""Rung-2 case pool (PREREG_R2.md). Stdlib only.

    python tools/seqpool.py pool   # pool/rung2_pool.json
    python tools/seqpool.py draw   # pool/draw2.json (dev, test, reserve ids); prints dev only

Families and parameters:
    parity  V in 2..4, S a non-empty proper subset of 1..V, target in {0,1}
    dyck    V in 2..4, a weight in {+1,-1,0} per token, at least one +1 and one -1
    sort    V in 2..4
    add     base b in 2..3 (tokens 1..b*b; token = 1 + a*b + c)
"""
import hashlib, itertools, json, os, random, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
POOL_SEED, DRAW_SEED, CAP = 20261113, 4043, 30
N_TEST = {"parity": 3, "dyck": 3, "sort": 2, "add": 2}
N_RESERVE = 2


def all_cases():
    fam = {"parity": [], "dyck": [], "sort": [], "add": []}
    for V in (2, 3, 4):
        toks = list(range(1, V + 1))
        for k in range(1, V):
            for S in itertools.combinations(toks, k):
                for target in (0, 1):
                    fam["parity"].append({"V": V, "S": list(S), "target": target})
        for wt in itertools.product((1, -1, 0), repeat=V):
            if 1 in wt and -1 in wt:
                fam["dyck"].append({"V": V, "wt": list(wt)})
        fam["sort"].append({"V": V})
    for b in (2, 3):
        fam["add"].append({"V": b * b, "base": b})
    return fam


def make_pool():
    rng = random.Random(POOL_SEED)
    pool = []
    for name, cases in all_cases().items():
        rng.shuffle(cases)
        for k, c in enumerate(cases[:CAP]):
            pool.append(dict(c, family=name, id="%s%02d" % (name[0], k)))
    return pool


def sha(o):
    return hashlib.sha256(json.dumps(o, sort_keys=True).encode()).hexdigest()


if __name__ == "__main__":
    os.makedirs(os.path.join(HERE, "pool"), exist_ok=True)
    pp = os.path.join(HERE, "pool", "rung2_pool.json")
    if sys.argv[1] == "pool":
        pool = make_pool()
        json.dump(pool, open(pp, "w"), indent=0)
        from collections import Counter
        print("rung2 pool: %d cases %s sha256 %s" % (len(pool), dict(Counter(c["family"] for c in pool)), sha(pool)))
    elif sys.argv[1] == "draw":
        pool = json.load(open(pp))
        rng = random.Random(DRAW_SEED)
        by = {}
        for c in pool:
            by.setdefault(c["family"], []).append(c["id"])
        for ids in by.values():
            rng.shuffle(ids)
        dev_fams = ["dyck", "parity"]   # the only families with spare settings (amendment 1)
        dev, test, reserve = [], [], []
        for name in sorted(by):
            ids = by[name]
            if name in dev_fams and len(ids) > N_TEST[name]:
                dev.append(ids.pop(0))
            test += ids[:N_TEST[name]]
            reserve += ids[N_TEST[name]:N_TEST[name] + N_RESERVE]
        draw = {"pool_seed": POOL_SEED, "draw_seed": DRAW_SEED, "rung2_dev": dev, "rung2_test": test,
                "rung2_reserve": reserve, "pool_sha256": sha(pool)}
        json.dump(draw, open(os.path.join(HERE, "pool", "draw2.json"), "w"), indent=1)
        print("draw written; test-set sha256", sha(test), "| %d test, %d reserve" % (len(test), len(reserve)))
        print("dev ids:", dev, "(test ids are in pool/draw2.json; do not read them before the prompt freeze)")
