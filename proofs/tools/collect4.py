"""Rung-4 results from attempt logs and lane checks (never from doctor reports).

    python tools/collect4.py [dev|test]   -> results/rung4-<split>.json + printed table
"""
import glob, json, os, statistics as st, sys
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
split = sys.argv[1] if len(sys.argv) > 1 else "test"
root = os.path.join(HERE, "runs", "rung4-" + split)
FAM = {"c": "carry", "l": "last", "f": "first", "i": "induct"}
rows = []
for arm in ("net", "net-rerun", "prog", "net-fable"):
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
                r["pass_at_submission"] = r["submissions"]
                r["axioms"] = a.get("axioms")
                r["solution_lines"] = len(open(p[:-5] + ".lean", encoding="utf-8").read().splitlines())
        r["lean_secs"] = round(r["lean_secs"], 1)
        ck = os.path.join(d, "r4_checks.json")
        if os.path.exists(ck):
            c = json.load(open(ck))
            f = c["float32"]
            r.update(blocks=c["blocks"], heads=c["heads"], width=c["width"], mlp_hidden=c["mlp_hidden"],
                     written_exact_max_dev=c["written_exact_max_dev"],
                     inside_ball_max_dev=max(c["inside_ball_max_dev"].values()), inside_ball_ok=c["inside_ball_ok"],
                     smallest_violating_multiple=c["smallest_violating_multiple"],
                     float32_in_range_max_dev=max(max(v["written"], v["perturbed_at_tau"] or 0)
                                                  for v in f.values() if v["in_theorem_range"]),
                     float32_ok_in_range=c["float32_ok_in_range"],
                     float32_beyond={n: v["written"] for n, v in f.items() if not v["in_theorem_range"]})
        rows.append(r)
os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
json.dump(rows, open(os.path.join(HERE, "results", "rung4-%s.json" % split), "w"), indent=1)
for arm in ("net", "net-rerun", "prog", "net-fable"):
    rs = [r for r in rows if r["arm"] == arm]   # a case with 0 submissions (crashed doctor) counts as a fail
    if not rs:
        continue
    subs = sorted(r["submissions"] for r in rs)
    fam = {f: "%d/%d" % (sum(r["pass"] for r in rs if r["family"] == f), sum(r["family"] == f for r in rs))
           for f in FAM.values() if any(r["family"] == f for r in rs)}
    print("%s: %d/%d pass %s | subs %s median %s | lean s median %s | lines %s | nd %d banned %d timeouts %d memkills %d" % (
        arm, sum(r["pass"] for r in rs), len(rs), fam, subs, st.median(subs), st.median(r["lean_secs"] for r in rs),
        sorted(r.get("solution_lines", 0) for r in rs), sum(r["native_decide_attempts"] for r in rs),
        sum(r["banned_rejections"] for r in rs), sum(r["timeouts"] for r in rs), sum(r["mem_kills"] for r in rs)))
print("id   arm        fam     blk heads width  exact    in-ball  breaks@  f32 in range  f32 beyond")
for r in rows:
    if "blocks" in r:
        print("%-4s %-10s %-7s %d   %-5s %-5d  %.1e  %.3f    %-7s  %.3g        %s" % (
            r["id"], r["arm"], r["family"], r["blocks"], r["heads"], r["width"], r["written_exact_max_dev"],
            r["inside_ball_max_dev"], r["smallest_violating_multiple"], r["float32_in_range_max_dev"],
            {k: round(v, 3) for k, v in r["float32_beyond"].items()}))
