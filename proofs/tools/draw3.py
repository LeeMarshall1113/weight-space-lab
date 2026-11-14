"""Rung-3 draw (PREREG_R3.md): seed 4044, from the rung-1 pool specs not drawn at rung 1.

    python tools/draw3.py      -> pool/draw3.json (dev 2, test 12, reserve 6); prints dev only
"""
import json, os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import specpool as SP

HERE = SP.HERE
pool = json.load(open(os.path.join(HERE, "pool", "rung1_pool.json")))
d1 = json.load(open(os.path.join(HERE, "pool", "draw.json")))
used = set(d1["rung1_dev"]) | set(d1["rung1_test"]) | set(d1["rung1_reserve"])
ids = [s["id"] for s in pool if s["id"] not in used]
rng = random.Random(4044)
rng.shuffle(ids)
draw = {"draw_seed": 4044, "excluded": len(used), "rung3_dev": ids[:2], "rung3_test": ids[2:14],
        "rung3_reserve": ids[14:20]}
json.dump(draw, open(os.path.join(HERE, "pool", "draw3.json"), "w"), indent=1)
print("draw3 written from %d unused specs; test-set sha256 %s" % (len(ids), SP.sha(draw["rung3_test"])))
print("dev ids:", draw["rung3_dev"], "(test ids are in pool/draw3.json; do not read the specs before the freeze)")
