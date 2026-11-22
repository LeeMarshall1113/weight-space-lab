"""Re-check the rung 9-LN15 (LayerNorm) material, one Lean process at a time.

    python tools/recheck_ln15.py [--set frameworks,kits,nets] [--match REGEX] [--out results/recheck-ln15.json]

Sets (default: all):
  frameworks  build Lane4/LNAll (which builds the 20 LN* modules and everything under them, in dependency order)
  kits        runs/r9ln15-kit/*: the ten framework lemmas proved by agents (or by text-substitution ports), through tools/check.py
  nets        runs/r9ln15-nets/<tag>/: the per-network files. f* = fresh seeds 400 to 419, t* = tuning networks, c_* = controls.
              Each network's files are compiled in order as modules R9LN15.<tag>.<File>, under the limits of
              PREREG_R9LN15.md (900 s and 6 GB peak commit per file).
--match filters kit folders and net tags by regex.

A network passes when every file compiles (rc 0, no error, no `sorry`, within the limits), every `#print axioms`
line is within propext, Classical.choice, Quot.sound, the kernel's decision (accept if the file set proves `accept`,
reject if it proves `reject`) equals the decision recorded in the folder's kernel.json, and an accepted network proves
all five theorems accept, skeleton_ok, binary32, trained_exact_all_lengths, trained_binary32 (a tuning network or
control that is a rejection proves `reject`). Plan for about 5 GB of memory per Lean job and about three hours for
the whole set.
"""
import argparse, glob, json, os, re, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check as C
sys.stdout.reconfigure(encoding="utf-8", errors="replace")
ap = argparse.ArgumentParser()
ap.add_argument("--set", default="frameworks,kits,nets")
ap.add_argument("--match", default="")
ap.add_argument("--limit", type=int, default=900, help="seconds allowed per network file (900 is the registered limit)")
ap.add_argument("--out", default=os.path.join(C.HERE, "results", "recheck-ln15.json"))
a = ap.parse_args()
sets = a.set.split(",")
rows, t0 = [], time.time()
posix = lambda p: os.path.relpath(p, C.HERE).replace("\\", "/")
save = lambda: json.dump(rows, open(a.out, "w", encoding="utf-8"), indent=1)
ALLOWED = C.ALLOWED_AXIOMS
C.MEM_KILL_GB = 6.0
FIVE = {"accept", "skeleton_ok", "binary32", "trained_exact_all_lengths", "trained_binary32"}

if "frameworks" in sets:
    t = time.time()
    C.ensure_basic(1800, "LNAll")
    rows.append({"kind": "framework", "unit": "Lane4/LNAll.lean (and the 20 LN modules and all modules they import)", "pass": True, "secs": round(time.time() - t, 1)})
    print("PASS framework LNAll", flush=True); save()

if "kits" in sets:
    for cj in sorted(glob.glob(os.path.join(C.HERE, "runs", "r9ln15-kit", "*", "case.json"))):
        d = os.path.dirname(cj)
        if a.match and not re.search(a.match, posix(d)): continue
        r = C.check(d, 900)
        rows.append({"kind": "case", "unit": posix(d), "pass": r["pass"], "reason": r.get("reason"), "secs": r.get("secs"),
                     "peak_rss_gb": r.get("peak_rss_gb"), "axioms": r.get("axioms")})
        print("%-5s %s %ss %s" % ("PASS" if r["pass"] else "FAIL", posix(d), r.get("secs"), r.get("reason") if not r["pass"] else ",".join(r.get("axioms") or [])), flush=True)
        save()

if "nets" in sets:
    for d in sorted(glob.glob(os.path.join(C.HERE, "runs", "r9ln15-nets", "*"))):
        tag = os.path.basename(d)
        if a.match and not re.search(a.match, tag): continue
        if not os.path.exists(os.path.join(d, "kernel.json")): continue   # f406, t114: no Lean file was generated (rejected by the mirror / not run)
        meta = json.load(open(os.path.join(d, "meta.json")))
        rec = json.load(open(os.path.join(d, "kernel.json")))
        od = os.path.join(C.BUILD, "R9LN15", tag)
        os.makedirs(od, exist_ok=True)
        files, out_all, ok = [], "", True
        for name in meta["files"]:
            if not ok: break
            r = C.run_lean([os.path.join(d, name + ".lean"), "-o", os.path.join(od, name + ".olean")], a.limit, C.HERE)
            within = (r["rc"] == 0 and not r["timed_out"] and not r["mem_killed"] and r["secs"] <= a.limit
                      and (r["peak_commit_gb"] or 0) <= 6.0 and not re.search(r": error", r["out"]) and "sorry" not in r["out"])
            files.append({"file": name, "rc": r["rc"], "secs": r["secs"], "commit": r["peak_commit_gb"], "within": within})
            out_all += r["out"]; ok = within
        ax = re.findall(r"'Lane4\.LNNetFile\.(\w+)' depends on axioms: \[([^\]]*)\]", out_all)
        std = all({x.strip() for x in s.split(",")} <= ALLOWED for _, s in ax)
        names = [n for n, _ in ax]
        kernel = ("accept" if "accept" in names else "reject" if "reject" in names else None) if ok else None
        need = FIVE if kernel == "accept" else ({"reject"} if kernel == "reject" else set())
        good = ok and std and kernel is not None and kernel == rec.get("kernel") and need <= set(names) and len(meta["files"]) <= 4
        rows.append({"kind": "net", "unit": "runs/r9ln15-nets/" + tag, "pass": good, "verdict": kernel, "recorded_verdict": rec.get("kernel"),
                     "mirror": rec.get("mirror"), "files": files, "total_secs": round(sum(f["secs"] for f in files), 1),
                     "limit_secs": a.limit, "max_commit": max([f["commit"] or 0 for f in files] + [0]), "theorems": names, "axioms_standard": bool(ax) and std,
                     "recorded_total_secs": rec.get("total_secs"), "tail": "" if good else out_all[-300:]})
        print("PASS" if good else "FAIL", tag, kernel, "files", len(files), "secs", rows[-1]["total_secs"], "commit", rows[-1]["max_commit"], flush=True)
        save()

# token audit over the new Lean files
audit = {"native_decide": 0, "ofReduceBool": 0, "sorry": 0, "axiom": 0}
audit_attempts = dict(audit)
nfiles = 0
for pat in ("Lane4/LN*.lean", "runs/r9ln15-kit/**/*.lean", "runs/r9ln15-nets/**/*.lean"):
    for f in glob.glob(os.path.join(C.HERE, pat), recursive=True):
        if os.path.basename(f) == "_Full.lean": continue
        tgt = audit_attempts if "attempts" in f.replace("\\", "/").split("/") else audit
        nfiles += 1
        code = C.strip_comments(open(f, encoding="utf-8", errors="replace").read())
        for k in tgt:
            tgt[k] += len(re.findall(r"(?<![\w.])%s(?![\w])" % k, code))
rows.append({"kind": "audit", "files": nfiles, "token_counts": audit, "token_counts_attempts": audit_attempts})
save()
n = [r for r in rows if r["kind"] != "audit"]
print("total wall seconds: %.0f; passed %d of %d; failed: %s; audit %s attempts %s files %d"
      % (time.time() - t0, sum(r["pass"] for r in n), len(n), [r["unit"] for r in n if not r["pass"]], audit, audit_attempts, nfiles))
