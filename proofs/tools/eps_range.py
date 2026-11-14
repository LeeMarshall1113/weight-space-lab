"""Post-hoc (not pre-registered): each test twin's eps as a fraction of its spec's
output range over the box. The range is SAMPLED: exact rational evaluation at the box
corners plus 20,000 random points on the 1/64 grid, so it is a lower bound on the true
range and the fraction is an upper bound.

    python tools/eps_range.py        -> results/twin-eps-range.json + table
"""
import itertools, json, os, random, sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import specpool as SP

HERE = SP.HERE
pool = {s["id"]: s for s in json.load(open(os.path.join(HERE, "pool", "rung1_pool.json")))}
draw = json.load(open(os.path.join(HERE, "pool", "draw.json")))
twins = json.load(open(os.path.join(HERE, "results", "twins-test.json")))
res = {r["id"]: r for r in json.load(open(os.path.join(HERE, "results", "rung1-test.json")))
       if r["arm"] == "twin"}
out = []
for sid in draw["rung1_test"]:
    s = pool[sid]
    e = SP.from_json(s["expr"])
    box = [tuple(b) for b in s["box"]]
    rng = random.Random(777)
    pts = [[F(v) for v in c] for c in itertools.product(*box)]
    pts += [[F(rng.randint(lo * 64, hi * 64), 64) for lo, hi in box] for _ in range(20000)]
    vals = [SP.ev(e, x) for x in pts]
    span = max(vals) - min(vals)
    eps = F(twins[sid]["eps"])
    r = res.get(sid, {})
    out.append({"id": sid, "eps": float(eps), "range_sampled": float(span),
                "eps_over_range": round(float(eps / span), 4),
                "submissions": r.get("submissions", 0), "pass": bool(r.get("pass"))})
json.dump(out, open(os.path.join(HERE, "results", "twin-eps-range.json"), "w"), indent=1)
print("id     eps      range    eps/range  subs  pass")
for o in sorted(out, key=lambda o: o["eps_over_range"]):
    print("%-5s %8.2f %8.2f %9.1f%%  %4d  %s" % (o["id"], o["eps"], o["range_sampled"],
          100 * o["eps_over_range"], o["submissions"], o["pass"]))
tight = [o for o in out if o["eps_over_range"] < 0.10]
print("eps under 10%% of range: %d twins, %d attempted, %d pass" % (
    len(tight), sum(o["submissions"] > 0 for o in tight), sum(o["pass"] for o in tight)))
