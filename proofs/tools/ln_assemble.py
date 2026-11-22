"""Turn a proved rung 9-LN15 kit case into a framework module (after tools/r8_assemble.py).
usage: python tools/ln_assemble.py <case id> <module name> <import1,import2,...>
Lane4/<module>.lean = imports + Solution.lean, with namespace Lane4.Case renamed to Lane4.<module>.
Only for cases whose attempts show a kernel-checked PASS (checked here)."""
import json, os, sys, glob
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
cid, mod, imps = sys.argv[1], sys.argv[2], sys.argv[3].split(",")
d = os.path.join(HERE, "runs", "r9ln15-kit", cid)
recs = [json.load(open(p, encoding="utf-8")) for p in sorted(glob.glob(os.path.join(d, "attempts", "*.json")))]
ok = [r for r in recs if r.get("pass") and r.get("reason") == "kernel-checked"]
assert ok, "case not passed"
sol = open(os.path.join(d, "attempts", "%02d.lean" % ok[0]["attempt"]), encoding="utf-8").read()
assert sol == open(os.path.join(d, "Solution.lean"), encoding="utf-8").read(), "Solution.lean differs from the passing attempt"
head = "/-\nLane 4, rung 9-LN15 kit module, assembled by tools/ln_assemble.py from kit case " + cid + "\n(runs/r9ln15-kit/" + cid + \
       "): statements by the study team (Lane4/LNDefs.lean), proofs checked by tools/check.py.\n-/\n"
txt = head + "".join("import Lane4.%s\n" % i for i in imps) + "\n" + sol.replace("Lane4.Case", "Lane4." + mod) + "\n"
open(os.path.join(HERE, "Lane4", mod + ".lean"), "w", encoding="utf-8", newline="\n").write(txt)
print("wrote Lane4/%s.lean" % mod, len(txt.splitlines()), "lines")
