"""Turn a proved rung-7 kit case into a framework module.
usage: python tools/r7_assemble.py <case id> <module name> <import1,import2,...>
Lane4/<module>.lean = imports + Spec.lean + Solution.lean, with namespace Lane4.Case renamed to
Lane4.<module>. Only for cases whose attempts show a kernel-checked PASS (checked here)."""
import json, os, sys, glob
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
cid, mod, imps = sys.argv[1], sys.argv[2], sys.argv[3].split(",")
d = os.path.join(HERE, "runs", "r7-kit", cid)
att = sorted(glob.glob(os.path.join(d, "attempts", "*.json")))
last = json.load(open(att[-1], encoding="utf-8"))
assert last["pass"] and last["reason"] == "kernel-checked", "case not passed"
rd = lambda n: open(os.path.join(d, n), encoding="utf-8").read()
body = rd("Spec.lean") + chr(10) + chr(10) + rd("Solution.lean") + chr(10)
body = body.replace("Lane4.Case", "Lane4." + mod)
head = "/-" + chr(10) + "the proofs study, rung 7 kit module, assembled by tools/r7_assemble.py from kit case " + cid + chr(10) + \
       "(runs/r7-kit/" + cid + "): statements by the study team, proofs by a Sonnet doctor, checked by tools/check.py." + chr(10) + "-/" + chr(10)
txt = head + "".join("import Lane4.%s" % i + chr(10) for i in imps) + chr(10) + body
open(os.path.join(HERE, "Lane4", mod + ".lean"), "w", encoding="utf-8", newline=chr(10)).write(txt)
print("wrote Lane4/%s.lean" % mod, len(txt.splitlines()), "lines")
