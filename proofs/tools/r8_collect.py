"""Rung 8: collect every per-network kernel result into results/rung8-kernel.json (reads logs only; runs nothing).

    python tools/r8_collect.py

One row per job of scratch/r8jobs/*.txt: mirror decision and reason (logs/r8-gen-<tag>.log), kernel decision,
theorems with standard axioms, time, peak commit, within limits (runs/r8-nets/<tag>/lean.log), native_decide count.
"""
import json, os, re

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STD = "depends on axioms: [propext, Classical.choice, Quot.sound]"
rows = []
for name in ("bar", "A-rest", "B-ok", "ctl1-6", "ctl7", "ctl8"):
    for ln in open(os.path.join(HERE, "scratch", "r8jobs", name + ".txt")):
        p = ln.strip().split("|")
        if len(p) < 2 or not p[0]: continue
        tag = p[1]
        g = open(os.path.join(HERE, "logs", "r8-gen-%s.log" % tag), encoding="utf-8", errors="replace").read()
        m = re.search(r"mirror: (\w+) \| (.*)", g)
        s = open(os.path.join(HERE, "runs", "r8-nets", tag, "lean.log"), encoding="utf-8", errors="replace").read()
        src = open(os.path.join(HERE, "runs", "r8-nets", tag, "Net.lean"), encoding="utf-8", errors="replace").read()
        rc = re.search(r"^rc (\S+) secs (\S+) rss (\S+) commit (\S+) timed_out (\w+) mem_killed (\w+)", s, re.M)
        names = re.findall(r"'Lane4\.Net\.(\w+)' depends on axioms", s)
        kernel = "accept" if "accept" in names else ("reject" if "reject" in names else "none")
        within = re.search(r"WITHIN_LIMITS (\w+)", s)
        rows.append(dict(list=name, tag=tag, run_dir=p[0], args=p[2] if len(p) > 2 else "",
                         mirror=m.group(1) if m else None, mirror_detail=m.group(2).strip() if m else None,
                         kernel=kernel, theorems=names, standard_axioms_only=s.count(STD) == s.count("depends on axioms") and len(names) > 0,
                         rc=int(rc.group(1)) if rc else None, secs=float(rc.group(2)) if rc else None,
                         peak_commit_gb=float(rc.group(4)) if rc else None,
                         within_limits=(within.group(1) == "True") if within else None,
                         errors=len(re.findall(r"error", s)), sorry=len(re.findall(r"sorry", s)),
                         native_decide=src.count("native_decide")))
json.dump(rows, open(os.path.join(HERE, "results", "rung8-kernel.json"), "w"), indent=1)
for name in ("bar", "A-rest", "B-ok", "ctl1-6", "ctl7", "ctl8"):
    rr = [r for r in rows if r["list"] == name]
    print("%-7s files %2d | kernel accept %2d reject %2d none %d | kernel==mirror %2d | standard axioms %2d | within limits %2d | rc!=0 %d | errors %d sorry %d native_decide %d | max secs %.1f max commit %.2f" % (
        name, len(rr), sum(r["kernel"] == "accept" for r in rr), sum(r["kernel"] == "reject" for r in rr), sum(r["kernel"] == "none" for r in rr),
        sum(r["kernel"] == r["mirror"] for r in rr), sum(r["standard_axioms_only"] for r in rr), sum(bool(r["within_limits"]) for r in rr),
        sum(r["rc"] != 0 for r in rr), sum(r["errors"] for r in rr), sum(r["sorry"] for r in rr), sum(r["native_decide"] for r in rr),
        max(r["secs"] for r in rr), max(r["peak_commit_gb"] for r in rr)))
acc = [r for r in rows if r["kernel"] == "accept"]
print("accepted files with all four theorems:", sum(set(r["theorems"]) >= {"accept", "skeleton_ok", "trained_exact_all_lengths", "trained_binary32"} for r in acc), "of", len(acc))
