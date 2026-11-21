"""One-line verdict of a rung-6a case from its attempt records (never from a doctor's report).

    python tools/r6a_verdict.py runs/rung6a-test/net/c19 [...]
"""
import glob, json, os, sys

for d in sys.argv[1:]:
    recs = [json.load(open(p, encoding="utf-8")) for p in sorted(glob.glob(os.path.join(d, "attempts", "*.json")))]
    sol = os.path.join(d, "Solution.lean")
    lines = sum(1 for _ in open(sol, encoding="utf-8")) if os.path.exists(sol) else 0
    nd = sum(1 for r in recs if r.get("native_decide_attempted"))
    ok = [r for r in recs if r.get("pass")]
    if ok:
        r = ok[0]
        std = sorted(r.get("axioms") or []) == ["Classical.choice", "Quot.sound", "propext"] or not r.get("axioms")
        print("%s PASS at %d of %d submissions; %s; axioms %s; native_decide attempts %d; %d lines; %s" % (
            os.path.basename(d), r["attempt"], len(recs), r.get("reason"), "standard" if std else r.get("axioms"), nd, lines, r.get("time")))
    else:
        print("%s FAIL; %d submissions; reasons %s; native_decide attempts %d; %d lines; last %s" % (
            os.path.basename(d), len(recs), sorted(set(r.get("reason") for r in recs)), nd, lines, recs[-1].get("time") if recs else None))
