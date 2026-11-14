"""Re-check every case folder under runs/ that has a Solution.lean, one after another.

    python tools/recheck_all.py [--only rung2-test,rung3-test,rung4-test] [--ids c14,i09] [--out results/recheck.json]

Prints one line per case (PASS/FAIL, seconds, peak working set, axioms) and writes the rows
as JSON. Cases are compared with the recorded verdict in their attempts/ folder.
"""
import argparse, glob, json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check as C
sys.stdout.reconfigure(encoding="utf-8", errors="replace")
ap = argparse.ArgumentParser()
ap.add_argument("--only", default="rung2-test,rung3-test,rung4-test")
ap.add_argument("--ids", default="")
ap.add_argument("--arms", default="net,prog")
ap.add_argument("--out", default=os.path.join(C.HERE, "results", "recheck.json"))
ap.add_argument("--timeout", type=int, default=600)
a = ap.parse_args()
ids = set(filter(None, a.ids.split(",")))
rows, t0 = [], time.time()
for rung in a.only.split(","):
    for arm in a.arms.split(","):
        for d in sorted(glob.glob(os.path.join(C.HERE, "runs", rung, arm, "*"))):
            if not os.path.exists(os.path.join(d, "Solution.lean")):
                continue
            if ids and os.path.basename(d) not in ids:
                continue
            r = C.check(d, a.timeout)
            row = {"rung": rung, "arm": arm, "id": os.path.basename(d), "pass": r["pass"], "reason": r.get("reason"),
                   "secs": r.get("secs"), "peak_rss_gb": r.get("peak_rss_gb"), "axioms": r.get("axioms"),
                   "native_decide_attempted": r.get("native_decide_attempted")}
            rows.append(row)
            print("%-5s %s/%s/%s  %ss  rss=%sGB  %s" % ("PASS" if r["pass"] else "FAIL", rung, arm, row["id"],
                  row["secs"], row["peak_rss_gb"], row["reason"] if not r["pass"] else ",".join(r.get("axioms") or [])), flush=True)
            json.dump(rows, open(a.out, "w", encoding="utf-8"), indent=1)
print("total wall seconds: %.0f; passed %d of %d" % (time.time() - t0, sum(r["pass"] for r in rows), len(rows)))
