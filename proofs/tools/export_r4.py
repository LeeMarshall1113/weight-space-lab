"""Rung 4: export each passing doctor net as exact JSON by evaluating it in Lean.

    python tools/export_nets.py runs/rung4-test        (RUN UNDER A LEASE: one lean.exe at a time)

Writes runs/.../net/<id>/net.json. Uses the passing attempt's Solution text.
"""
import glob, json, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check as C

EXPORT = open(os.path.join(C.HERE, "Lane4", "Export4.lean.txt"), encoding="utf-8").read()

root = os.path.abspath(sys.argv[1])
C.ensure_basic(name="RSeq")
for d in sorted(glob.glob(os.path.join(root, "net", "*"))):
    passed = [p for p in sorted(glob.glob(os.path.join(d, "attempts", "*.json")))
              if json.load(open(p, encoding="utf-8")).get("pass")]
    if not passed or os.path.exists(os.path.join(d, "net.json")):
        continue
    sol = open(passed[0][:-5] + ".lean", encoding="utf-8").read()
    full = "import Lane4.RSeq\n\n" + open(os.path.join(d, "Spec.lean"), encoding="utf-8").read() + "\n\n" + sol + "\n\n" + EXPORT
    path = os.path.join(d, "_Export.lean")
    open(path, "w", encoding="utf-8", newline="\n").write(full)
    r = C.run_lean([path], 600, d)
    m = re.search(r"NETJSON (\{.*\})", r["out"])
    if not m:
        print(os.path.basename(d), "EXPORT FAILED", r["out"][-600:])
        continue
    net = json.loads(m.group(1))
    json.dump(net, open(os.path.join(d, "net.json"), "w"))
    print(os.path.basename(d), "exported: blocks", len(net["blocks"]), "heads",
          [len(b["heads"]) for b in net["blocks"]], "width", len(net["outW"]), "secs", r["secs"], flush=True)
