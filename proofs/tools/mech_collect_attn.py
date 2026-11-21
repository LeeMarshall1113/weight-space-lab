"""Mechanism row (a): collect per-network attention results into results/mech-attn.json (reads logs only)."""
import glob, json, os, re
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STD = "depends on axioms: [propext, Classical.choice, Quot.sound]"
rows = []
for mf in sorted(glob.glob(os.path.join(HERE, "runs", "mech", "*", "attn_meta.json"))):
    m = json.load(open(mf)); d = os.path.dirname(mf)
    s = open(os.path.join(d, "attn.log"), encoding="utf-8", errors="replace").read()
    rc = re.search(r"^rc (\S+) secs (\S+) rss (\S+) commit (\S+)", s, re.M)
    names = re.findall(r"'Lane4\.(?:Net|Case)\.(\w+)' depends on axioms", s)
    rows.append(dict(tag=m["tag"], window_L=m["window_L"], eps_bound=m["eps_bound"], theorems=names,
                     attn_theorems_ok=all(n in names for n in ("head_tail8", "attn_window8", "attn_window", "attn_eps0", "attn_eps1")),
                     standard_axioms_only=all(STD in ln for ln in s.splitlines() if "'Lane4.Net." in ln or "'Lane4.Case." in ln),
                     sorry=s.count("sorryAx"), errors=len(re.findall(r"error", s)), rc=int(rc.group(1)), secs=float(rc.group(2)),
                     peak_commit_gb=float(rc.group(4)), within_limits="WITHIN_LIMITS True" in s,
                     native_decide=open(os.path.join(d, "Attn.lean"), encoding="utf-8").read().count("native_decide")))
json.dump(rows, open(os.path.join(HERE, "results", "mech-attn.json"), "w"), indent=1)
fr = [r for r in rows if r["tag"].startswith("fresh")]
from collections import Counter
print("fresh:", len(fr), "| attention theorems", sum(r["attn_theorems_ok"] for r in fr), "| standard axioms only", sum(r["standard_axioms_only"] for r in fr),
      "| sorry", sum(r["sorry"] for r in fr), "| errors", sum(r["errors"] for r in fr), "| within limits", sum(r["within_limits"] for r in fr),
      "| native_decide", sum(r["native_decide"] for r in fr), "| max secs", max(r["secs"] for r in fr), "max GB", max(r["peak_commit_gb"] for r in fr),
      "| windows", Counter(tuple(r["window_L"]) for r in fr))
