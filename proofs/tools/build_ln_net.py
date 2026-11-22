"""Rung 9-LN15: compile the files of one network (tools/make_r9ln15_net.py) in order, each as a module
build/R9LN15/<tag>/<X>.olean, under the limits of the registration: 900 s and 6 GB peak commit PER FILE, at most
four files per network (rule KK).

    python tools/build_ln_net.py <tag> [<tag> ...] 

Writes runs/r9ln15-nets/<tag>/kernel.json: per file rc, seconds, peak commit, within limits; the kernel's decision
(accept / reject, from which theorems were checked) and whether it equals the mirror's; the axioms printed."""
import json, os, re, subprocess, sys, time
sys.stdout.reconfigure(encoding="utf-8", errors="replace")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check as C
C.MEM_KILL_GB = 6.0


C.ensure_basic(900, "LNAll")
for tag in sys.argv[1:]:
    d = os.path.join(C.HERE, "runs", "r9ln15-nets", tag)
    meta = json.load(open(os.path.join(d, "meta.json")))
    od = os.path.join(C.BUILD, "R9LN15", tag)
    os.makedirs(od, exist_ok=True)
    res, out_all, ok = [], "", True
    for name in meta["files"]:
        if not ok: break
        r = C.run_lean([os.path.join(d, name + ".lean"), "-o", os.path.join(od, name + ".olean")], 900, C.HERE)
        within = (r["rc"] == 0 and not r["timed_out"] and not r["mem_killed"] and r["secs"] <= 900 and (r["peak_commit_gb"] or 0) <= 6.0)
        res.append(dict(file=name, rc=r["rc"], secs=r["secs"], commit=r["peak_commit_gb"], timed_out=r["timed_out"], mem_killed=r["mem_killed"], within=within))
        open(os.path.join(d, name + ".log"), "w", encoding="utf-8").write(r["out"])
        out_all += r["out"]; ok = within
        print(tag, name, "rc", r["rc"], "secs", r["secs"], "commit", r["peak_commit_gb"], "within", within, flush=True)
    ax = re.findall(r"'Lane4\.LNNetFile\.(\w+)' depends on axioms: \[([^\]]*)\]", out_all)
    std = all(sorted(a.strip() for a in s.split(",")) == ["Classical.choice", "Quot.sound", "propext"] for _, s in ax)
    names = [n for n, _ in ax]
    kernel = None
    if ok and "accept" in names: kernel = "accept"
    if ok and "reject" in names: kernel = "reject"
    k = dict(tag=tag, files=res, n_files=len(res), all_within=ok, four_file_rule=bool(ok and len(meta["files"]) <= 4), kernel=kernel,
             mirror="accept" if meta["mirror_ok"] else "reject", agree=(kernel == ("accept" if meta["mirror_ok"] else "reject")),
             theorems=names, axioms_standard=bool(ax) and std, total_secs=round(sum(x["secs"] for x in res), 1),
             max_commit=max([x["commit"] or 0 for x in res] + [0]))
    json.dump(k, open(os.path.join(d, "kernel.json"), "w"), indent=1)
    print("RESULT", tag, "kernel", kernel, "| mirror", k["mirror"], "| agree", k["agree"], "| files", len(res), "| secs", k["total_secs"],
          "| max commit", k["max_commit"], "| theorems", ",".join(names), "| axioms standard", k["axioms_standard"], flush=True)
