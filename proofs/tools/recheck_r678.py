"""Re-check the rung 6a, 7 and 8 material, one Lean process at a time.

    python tools/recheck_r678.py [--set frameworks,kits,r6a,nets-r7,nets-r8] [--match REGEX] [--out results/recheck-r678.json]

Sets (default: all):
  frameworks  build Lane4/R8All (which builds AGate*, R7* and R8* in dependency order)
  kits        runs/r6-kit, runs/r7-kit, runs/r8-kit: framework lemmas proved by agents, through tools/check.py
  r6a         runs/rung6a-dev and runs/rung6a-test: gated-transformer cases (net and control arms), through tools/check.py
  nets-r7     runs/r7-nets/*/Net.lean: per-network files of rung 7
  nets-r8     runs/r8-nets/*/Net.lean: per-network files and controls of rung 8
  nets-mech   runs/mech/*/Net.lean: the mechanism row (b) files (19 fresh seeds, 2 tuning-set networks, the swapped-embedding control), plus Lane4/MechBisim
  attn        runs/mech/*/Attn.lean: the mechanism row (a) files (statements about where each head looks; no accept/reject verdict, they must compile with the standard axioms)
  kit-mech    runs/mech-kit/*: the kit case for row (a), through tools/check.py
--match filters case folders and net tags by regex.

A per-network file passes when Lean exits 0 with no error and no `sorry`, every `#print axioms` line is within
propext, Classical.choice, Quot.sound, and it proves either `accept` (and its companions) or `reject`; the row
records which and compares it with the verdict recorded in the folder's `lean.log`. Net files are run under the limits of PREREG_R8 Amendment 1 (900 s and 6 GB commit): a file that
does not finish is recorded as a failure, not as a rejection. Plan for about 5 GB of memory per Lean job and
several hours for the whole set; `--set` and `--match` cut it down.
"""
import argparse, glob, json, os, re, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check as C
sys.stdout.reconfigure(encoding="utf-8", errors="replace")
ap = argparse.ArgumentParser()
ap.add_argument("--set", default="frameworks,kits,r6a,nets-r7,nets-r8,nets-mech")
ap.add_argument("--match", default="")
ap.add_argument("--out", default=os.path.join(C.HERE, "results", "recheck-r678.json"))
ap.add_argument("--timeout", type=int, default=900)
a = ap.parse_args()
sets = a.set.split(",")
rows, t0 = [], time.time()
posix = lambda p: os.path.relpath(p, C.HERE).replace("\\", "/")
save = lambda: json.dump(rows, open(a.out, "w", encoding="utf-8"), indent=1)
ALLOWED = C.ALLOWED_AXIOMS
C.MEM_KILL_GB = 6.0

if "frameworks" in sets:
    t = time.time()
    C.ensure_basic(name="R8All")
    C.ensure_basic(name="MechBisim")
    rows.append({"kind": "framework", "unit": "Lane4/R8All.lean and Lane4/MechBisim.lean (and all modules they import)", "pass": True, "secs": round(time.time() - t, 1)})
    print("PASS framework R8All", flush=True); save()

def cases(*dirs):
    out = []
    for d in dirs:
        out += sorted(glob.glob(os.path.join(C.HERE, "runs", d, "**", "case.json"), recursive=True))
    return out

todo = []
if "kits" in sets: todo += cases("r6-kit", "r7-kit", "r8-kit")
if "r6a" in sets: todo += cases("rung6a-dev", "rung6a-test")
if "kit-mech" in sets: todo += cases("mech-kit")
for cj in todo:
    d = os.path.dirname(cj)
    if not os.path.exists(os.path.join(d, "Solution.lean")): continue
    if a.match and not re.search(a.match, posix(d)): continue
    r = C.check(d, a.timeout)
    rows.append({"kind": "case", "unit": posix(d), "pass": r["pass"], "reason": r.get("reason"), "secs": r.get("secs"),
                 "peak_rss_gb": r.get("peak_rss_gb"), "axioms": r.get("axioms")})
    print("%-5s %s %ss %s" % ("PASS" if r["pass"] else "FAIL", posix(d), r.get("secs"), r.get("reason") if not r["pass"] else ",".join(r.get("axioms") or [])), flush=True)
    save()

nets = []
if "nets-r7" in sets: nets += sorted(glob.glob(os.path.join(C.HERE, "runs", "r7-nets", "*", "Net.lean")))
if "nets-r8" in sets: nets += sorted(glob.glob(os.path.join(C.HERE, "runs", "r8-nets", "*", "Net.lean")))
if "nets-mech" in sets: nets += sorted(glob.glob(os.path.join(C.HERE, "runs", "mech", "*", "Net.lean")))
if "attn" in sets: nets += sorted(glob.glob(os.path.join(C.HERE, "runs", "mech", "*", "Attn.lean")))
for f in nets:
    if a.match and not re.search(a.match, posix(os.path.dirname(f))): continue
    text = open(f, encoding="utf-8").read()
    mod = re.search(r"^import Lane4\.(\w+)", text, flags=re.M).group(1)
    C.ensure_basic(name=mod)
    r = C.run_lean([f], a.timeout, C.HERE)
    out = r["out"]
    ax = set()
    for lst in re.findall(r"depends on axioms: \[(.*?)\]", out, flags=re.S):
        ax |= {x.strip() for x in lst.replace("\n", " ").split(",") if x.strip()}
    kind = "reject" if re.search(r"Net\.reject'", out) else ("accept" if re.search(r"Net\.accept'", out) else "unknown")
    is_attn = os.path.basename(f) == "Attn.lean"
    if is_attn and not re.search(r"Net\.attn_window'", out): kind = "unknown"   # an Attn file must also prove attn_window (it contains the row (b) theorems too)
    rec = os.path.join(os.path.dirname(f), "attn.log" if is_attn else "lean.log")
    recorded = None
    if os.path.exists(rec):
        rt = open(rec, encoding="utf-8", errors="replace").read()
        recorded = "reject" if re.search(r"Net\.reject'", rt) else ("accept" if re.search(r"Net\.accept'", rt) else None)
    ok = r["rc"] == 0 and not r["timed_out"] and not r["mem_killed"] and not re.search(r": error", out) \
        and "sorry" not in out and ax <= ALLOWED and kind != "unknown" and (recorded is None or recorded == kind) and (r.get("peak_commit_gb") or 0) <= 6.0
    rows.append({"kind": "net", "unit": posix(f), "pass": ok, "verdict": kind, "recorded_verdict": recorded, "secs": r["secs"], "peak_rss_gb": r["peak_rss_gb"],
                 "peak_commit_gb": r.get("peak_commit_gb"), "axioms": sorted(ax), "tail": out[-300:] if not ok else ""})
    print("PASS" if ok else "FAIL", posix(f), kind, r["secs"], "commit=%s" % r.get("peak_commit_gb"), flush=True)
    save()

# token audit over the new Lean files (final files and every recorded attempt counted separately)
audit = {"native_decide": 0, "ofReduceBool": 0, "sorry": 0, "axiom": 0}
audit_attempts = dict(audit)
nfiles = 0
for pat in ("Lane4/AGate*.lean", "Lane4/R7*.lean", "Lane4/R8*.lean", "runs/r6-kit/**/*.lean", "runs/rung6a-*/**/*.lean", "runs/r7-*/**/*.lean", "runs/r8-*/**/*.lean", "runs/mech/**/*.lean", "Lane4/MechBisim.lean"):
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
