"""Mechanism rows: collect per-network results into results/mech-rows.json (reads meta.json and lean.log only)."""
import glob, json, os, re
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STD = "depends on axioms: [propext, Classical.choice, Quot.sound]"
rows = []
for mf in sorted(glob.glob(os.path.join(HERE, "runs", "mech", "*", "meta.json"))):
    m = json.load(open(mf)); d = os.path.dirname(mf)
    lf = os.path.join(d, "lean.log")
    r = dict(tag=m["tag"], dir=m["dir"], net=m["net"], seed=m["seed"], extract_ok=m["extract_ok"], extract_reason=m["extract_reason"],
             window=m.get("window"), program_states=m.get("program_states"), program_rows=m.get("program_rows"),
             cert_states=m.get("cert_states"), cert_rows=m.get("cert_rows"), mirror_ok=m.get("mirror_ok"), mirror_reason=m.get("mirror_reason"),
             is_task_A=m.get("is_task_A"), five_state_program=m.get("five_state_program"), program=m.get("program"))
    if os.path.exists(lf):
        s = open(lf, encoding="utf-8", errors="replace").read()
        rc = re.search(r"^rc (\S+) secs (\S+) rss (\S+) commit (\S+)", s, re.M)
        names = re.findall(r"'Lane4\.Net\.(\w+)' depends on axioms", s)
        r.update(kernel="accept" if "accept" in names else ("reject" if "reject" in names else "none"), theorems=names,
                 standard_axioms_only=all(STD in ln for ln in s.splitlines() if "'Lane4.Net." in ln), sorry=s.count("sorryAx"),
                 errors=len(re.findall(r"error", s)), secs=float(rc.group(2)) if rc else None, peak_commit_gb=float(rc.group(4)) if rc else None,
                 within_limits="WITHIN_LIMITS True" in s, native_decide=open(os.path.join(d, "Net.lean"), encoding="utf-8").read().count("native_decide"))
    rows.append(r)
json.dump(rows, open(os.path.join(HERE, "results", "mech-rows.json"), "w"), indent=1)
for r in rows:
    print("%-22s extract %-5s | program %s states %s rows | certificate %s rows | kernel %-6s | theorems %s | task A %s | %s s %s GB" % (
        r["tag"], r["extract_ok"], r["program_states"], r["program_rows"], r["cert_rows"], r.get("kernel", "-"),
        len(r.get("theorems", [])), r["is_task_A"], r.get("secs"), r.get("peak_commit_gb")))
fr = [r for r in rows if r["tag"].startswith("fresh") and r["seed"] != 153]
print("fresh accepted networks:", len(fr), "| extraction ok", sum(r["extract_ok"] for r in fr), "| kernel accept", sum(r.get("kernel") == "accept" for r in fr),
      "| all 7 theorems standard axioms", sum(len(r.get("theorems", [])) == 7 and r["standard_axioms_only"] and r["sorry"] == 0 for r in fr),
      "| prog_is_task", sum("prog_is_task" in r.get("theorems", []) for r in fr), "| 5-state program", sum(bool(r["five_state_program"]) for r in fr),
      "| within limits", sum(bool(r.get("within_limits")) for r in fr), "| native_decide", sum(r.get("native_decide", 0) for r in fr),
      "| max secs", max(r["secs"] for r in fr), "max GB", max(r["peak_commit_gb"] for r in fr))
