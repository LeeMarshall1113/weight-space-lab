"""Re-check every Lean file in this folder, one Lean process at a time.

    python tools/recheck_release.py [--out results/recheck-release.json] [--skip-cases]

Covers (in this order):
  1. framework modules   Lane4/*.lean, built in dependency order (Collision, TokenBlind,
                         Conjectures are compiled as well; they are statements, not proofs)
  2. every case folder   runs/**/case.json that has a Solution.lean, through tools/check.py
                         (banned tokens, kernel check, axioms within the standard three)
  3. standalone files    runs/r6b/*/_Corollary.lean, runs/r6c/{members,final,example}/*.lean
                         (they import Lane4.Seq), compiled and their `#print axioms` read
Also counts `native_decide` / `ofReduceBool` / `sorry` / `axiom` tokens in every Lean file
under runs/ and Lane4/ (comments stripped). Writes one JSON row per unit and a summary.
"""
import argparse, glob, json, os, re, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check as C
sys.stdout.reconfigure(encoding="utf-8", errors="replace")
ap = argparse.ArgumentParser()
ap.add_argument("--out", default=os.path.join(C.HERE, "results", "recheck-release.json"))
ap.add_argument("--timeout", type=int, default=900)
ap.add_argument("--skip-cases", action="store_true")
ap.add_argument("--match", default="", help="regex: only check cases whose folder path matches (frameworks and standalone files always run)")
a = ap.parse_args()
rows, t0 = [], time.time()
posix = lambda p: os.path.relpath(p, C.HERE).replace("\\", "/")
save = lambda: json.dump(rows, open(a.out, "w", encoding="utf-8"), indent=1)
ALLOWED = C.ALLOWED_AXIOMS
# kept on purpose and expected to FAIL against the current framework: kA, kC were checked against an
# earlier framework version (superseded by kA2, kC2); kColl and rung5-dev/net/i13 are recorded failed attempts
EXPECTED_FAIL = {"runs/r5-kit/kA", "runs/r5-kit/kC", "runs/r6b/kColl", "runs/rung5-dev/net/i13"}

# 1. frameworks
mods = ["Basic", "Seq", "Robust", "RSeq", "RSoft", "RSoftKit", "Bin32", "RSoftAll", "QRSeq"]
for m in mods:
    t = time.time()
    C.ensure_basic(name=m)
    rows.append({"kind": "framework", "unit": "Lane4/%s.lean" % m, "pass": True, "secs": round(time.time() - t, 1)})
    print("PASS framework", m, flush=True)
for name, extra in [("Collision", ""), ("TokenBlind", "import Lane4.Seq\n"), ("Conjectures", "")]:
    src = os.path.join(C.HERE, "Lane4", name + ".lean")
    text = open(src, encoding="utf-8").read()
    if name == "TokenBlind":     # statements; used after the text of Collision.lean
        text = "import Lane4.Seq\n" + open(os.path.join(C.HERE, "Lane4", "Collision.lean"), encoding="utf-8").read().replace("import Lane4.Seq\n", "") + "\n" + text
    tmp = os.path.join(C.HERE, "build", "_" + name + ".lean")
    os.makedirs(os.path.dirname(tmp), exist_ok=True)
    open(tmp, "w", encoding="utf-8", newline="\n").write(text)
    r = C.run_lean([tmp], a.timeout, C.HERE)
    ok = r["rc"] == 0 and not r["timed_out"] and not r["mem_killed"] and not re.search(r": error", r["out"])
    rows.append({"kind": "framework", "unit": "Lane4/%s.lean" % name, "pass": ok, "secs": r["secs"],
                 "peak_rss_gb": r["peak_rss_gb"], "sorry_warning": "sorry" in r["out"]})
    print("PASS" if ok else "FAIL", "framework", name, flush=True)
    save()

# 2. cases
if not a.skip_cases:
    for cj in sorted(glob.glob(os.path.join(C.HERE, "runs", "**", "case.json"), recursive=True)):
        d = os.path.dirname(cj)
        if not os.path.exists(os.path.join(d, "Solution.lean")):
            continue
        if a.match and not re.search(a.match, posix(d)):
            continue
        r = C.check(d, a.timeout)
        row = {"kind": "case", "unit": posix(d), "pass": r["pass"], "reason": r.get("reason"), "secs": r.get("secs"),
               "peak_rss_gb": r.get("peak_rss_gb"), "axioms": r.get("axioms"),
               "native_decide_attempted": r.get("native_decide_attempted")}
        rows.append(row)
        print("%-5s %s %ss rss=%s %s" % ("PASS" if r["pass"] else "FAIL", row["unit"], row["secs"], row["peak_rss_gb"],
              row["reason"] if not r["pass"] else ",".join(r.get("axioms") or [])), flush=True)
        save()

# 3. standalone files
stand = sorted(glob.glob(os.path.join(C.HERE, "runs", "r6b", "*", "_Corollary.lean"))) + \
    [os.path.join(C.HERE, "runs", "r6c", "members", "Members.lean"),
     os.path.join(C.HERE, "runs", "r6c", "final", "R6C.lean"),
     os.path.join(C.HERE, "runs", "r6c", "example", "Example.lean")]
for f in stand:
    r = C.run_lean([f], a.timeout, os.path.dirname(f))
    out = r["out"]
    ax = set()
    for lst in re.findall(r"depends on axioms: \[(.*?)\]", out, flags=re.S):
        ax |= {x.strip() for x in lst.replace("\n", " ").split(",") if x.strip()}
    ok = r["rc"] == 0 and not r["timed_out"] and not r["mem_killed"] and not re.search(r": error", out) \
        and "sorry" not in out and ax <= ALLOWED
    rows.append({"kind": "standalone", "unit": posix(f), "pass": ok, "secs": r["secs"], "peak_rss_gb": r["peak_rss_gb"],
                 "axioms": sorted(ax), "n_axiom_reports": len(re.findall(r"depends on axioms|does not depend", out))})
    print("PASS" if ok else "FAIL", posix(f), r["secs"], sorted(ax), flush=True)
    save()

# token audit
strip = C.strip_comments
audit = {"native_decide": 0, "ofReduceBool": 0, "sorry": 0, "axiom": 0}   # submitted/final files
audit_attempts = {"native_decide": 0, "ofReduceBool": 0, "sorry": 0, "axiom": 0}   # every recorded attempt
nfiles = 0
for pat in ("Lane4/*.lean", "runs/**/*.lean"):
    for f in glob.glob(os.path.join(C.HERE, pat), recursive=True):
        if os.path.basename(f) == "_Full.lean":
            continue
        tgt = audit_attempts if "attempts" in f.replace("\\", "/").split("/") else audit
        nfiles += 1
        code = strip(open(f, encoding="utf-8", errors="replace").read())
        for k in tgt:
            tgt[k] += len(re.findall(r"(?<![\w.])%s(?![\w])" % k, code))
rows.append({"kind": "audit", "files": nfiles, "token_counts": audit, "token_counts_attempts": audit_attempts})
save()
n = [r for r in rows if r["kind"] != "audit"]
unexpected = [r["unit"] for r in n if (not r["pass"]) != (r["unit"] in EXPECTED_FAIL) and r["unit"] in EXPECTED_FAIL or (not r["pass"] and r["unit"] not in EXPECTED_FAIL)]
print("total wall seconds: %.0f; passed %d of %d; expected-fail cases that failed: %s; unexpected: %s; audit %s"
      % (time.time() - t0, sum(r["pass"] for r in n), len(n), sorted(r["unit"] for r in n if r["unit"] in EXPECTED_FAIL and not r["pass"]), unexpected, audit))
