"""Rung 3: export each passing net (arm net: `net`; arm twin: `twin`) as exact JSON via Lean.

    python tools/export_r3.py runs/rung3-test [arm]      (RUN UNDER A LEASE: one lean.exe at a time)

Writes runs/.../<arm>/<id>/net.json from the passing attempt's Solution text.
"""
import glob, json, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check as C

root = os.path.abspath(sys.argv[1])
arm = sys.argv[2] if len(sys.argv) > 2 else "net"
EXPORT = open(os.path.join(C.HERE, "Lane4", "ExportNet.lean.txt"), encoding="utf-8").read().replace(
    "NETNAME", "net" if arm == "net" else "twin")
C.ensure_basic(name="Robust")
for d in sorted(glob.glob(os.path.join(root, arm, "*"))):
    passed = [p for p in sorted(glob.glob(os.path.join(d, "attempts", "*.json")))
              if json.load(open(p, encoding="utf-8")).get("pass")]
    if not passed or os.path.exists(os.path.join(d, "net.json")):
        continue
    sol = open(passed[0][:-5] + ".lean", encoding="utf-8").read()
    full = "import Lane4.Robust\n\n" + open(os.path.join(d, "Spec.lean"), encoding="utf-8").read() + "\n\n" + sol + "\n\n" + EXPORT
    path = os.path.join(d, "_Export.lean")
    open(path, "w", encoding="utf-8", newline="\n").write(full)
    r = C.run_lean([path], 600, d)
    m = re.search(r"NETJSON (\{.*\})", r["out"])
    if not m:
        print(os.path.basename(d), "EXPORT FAILED", r["out"][-600:])
        continue
    net = json.loads(m.group(1))
    json.dump(net, open(os.path.join(d, "net.json"), "w"))
    print(os.path.basename(d), "exported: hidden widths", [len(L["b"]) for L in net["hidden"]], "secs", r["secs"], flush=True)
