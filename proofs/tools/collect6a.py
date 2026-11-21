"""Rung-6a results from attempt logs and numeric checks (never from doctor reports).

    python tools/collect6a.py   -> results/rung6a-test.json + printed tables
"""
import glob, json, os, statistics as st
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
root = os.path.join(HERE, "runs", "rung6a-test")
FAM = {"c": "carry", "l": "last", "f": "first", "i": "induct"}
# doctor cost per net case (tokens in thousands, minutes), from the harness's completion notices
COST = {"c19": (416, 28), "c01": (291, 16), "c08": (335, 21), "l16": (173, 6), "l15": (226, 9), "l27": (202, 7),
        "f22": (366, 40), "f12": (342, 35), "f37": (347, 36), "i17": (397, 42), "i18": (613, 49), "i16": (440, 48)}
rows = []
for arm in ("net", "prog"):
    for d in sorted(glob.glob(os.path.join(root, arm, "*"))):
        cid = os.path.basename(d)
        r = {"id": cid, "family": FAM[cid[0]], "arm": arm, "submissions": 0, "pass": False, "lean_secs": 0.0,
             "native_decide_attempts": 0, "banned_rejections": 0, "timeouts": 0, "mem_kills": 0}
        for p in sorted(glob.glob(os.path.join(d, "attempts", "*.json"))):
            a = json.load(open(p, encoding="utf-8"))
            if a.get("pending"):
                continue
            r["submissions"] += 1
            r["lean_secs"] += a.get("secs", 0) or 0
            r["native_decide_attempts"] += bool(a.get("native_decide_attempted"))
            r["banned_rejections"] += str(a.get("reason", "")).startswith("banned")
            r["timeouts"] += bool(a.get("timed_out")); r["mem_kills"] += bool(a.get("mem_killed"))
            if a.get("pass") and not r["pass"]:
                r["pass"] = True
                r["pass_at"] = a["attempt"]
                r["axioms"] = sorted(a.get("axioms") or [])
                r["proof_lines"] = sum(1 for _ in open(p[:-5] + ".lean", encoding="utf-8"))
                r["uses_per_coordinate_lemma"] = any(k in open(p[:-5] + ".lean", encoding="utf-8").read()
                                                     for k in ("ardot_near_w", "CloseL", "wErr"))
        if arm == "net" and cid in COST:
            r["doctor_ktokens"], r["doctor_minutes"] = COST[cid]
        ck = os.path.join(d, "r6a_checks.json")
        if os.path.exists(ck):
            r["checks"] = json.load(open(ck))
            nj = json.load(open(os.path.join(d, "net.json")))
            from fractions import Fraction as F
            big = 0
            def walk(x):
                global big
                if isinstance(x, list):
                    for y in x: walk(y)
                elif isinstance(x, (str, int, float)) and not isinstance(x, bool):
                    try: big = max(big, abs(F(str(x))))
                    except Exception: pass
            walk(nj["embed"]); walk(nj["outW"])
            for B in nj["blocks"]:
                for k in ("W1", "b1", "W2", "b2"): walk(B[k])
                for h in B["heads"]:
                    for k in ("A", "V", "g", "gb", "m"): walk(h[k])
            r["largest_written_weight"] = float(big)
        rows.append(r)
json.dump(rows, open(os.path.join(HERE, "results", "rung6a-test.json"), "w"), indent=1)

for arm in ("net", "prog"):
    R = [r for r in rows if r["arm"] == arm]
    ok = [r for r in R if r["pass"]]
    fam = {f: "%d/%d" % (sum(r["pass"] for r in R if r["family"] == f), sum(1 for r in R if r["family"] == f)) for f in FAM.values()}
    print("%s: %d/%d %s | pass_at %d..%d (median %s) | lines %d..%d (median %s) | native_decide %d | std axioms %s" % (
        arm, len(ok), len(R), fam, min(r["pass_at"] for r in ok), max(r["pass_at"] for r in ok), st.median(r["pass_at"] for r in ok),
        min(r["proof_lines"] for r in ok), max(r["proof_lines"] for r in ok), st.median(r["proof_lines"] for r in ok),
        sum(r["native_decide_attempts"] for r in R),
        all(r["axioms"] in ([], ["Classical.choice", "Quot.sound", "propext"]) for r in ok)))
net = [r for r in rows if r["arm"] == "net"]
print("net uses per-coordinate lemma:", sorted(r["id"] for r in net if r.get("uses_per_coordinate_lemma")))
print("net doctor ktokens total %d, minutes total %d" % (sum(r.get("doctor_ktokens", 0) for r in net), sum(r.get("doctor_minutes", 0) for r in net)))
print("| id | family | blocks | heads | width | largest written weight | inside ball, worst | breaks at | float32 to 65,534 tokens, worst | relative 1/200, worst | additive 1/1000 breaks at 100 / 1,000 (of 50) |")
print("|---|---|---|---|---|---|---|---|---|---|---|")
for r in net:
    c = r.get("checks")
    if not c:
        continue
    row = c.get("additive_1_1000_breaks_of_50", {})
    print("| %s | %s | %d | %s | %d | %g | %.3f | %s | %.3f | %.3f | %s / %s |" % (
        r["id"], r["family"], c["blocks"], ", ".join(map(str, c["heads"])), c["width"], r["largest_written_weight"],
        max(c["inside_ball_max_dev"].values()),
        ("%dδ" % c["smallest_violating_multiple"]) if c["smallest_violating_multiple"] else "not up to 64δ",
        max(c["float32_max_dev"].values()), c["relative_1_200_max_dev"], row.get("100"), row.get("1000")))
