"""Re-check the bridge Lean files: the interval-bound-propagation framework and the per-net certificates.

    python reading/bridge/recheck_bridge.py [--set stage1,float,n8,region] [--out results/recheck-bridge.json]

Needs the setup of proofs/README.md (LANE4_LEAN, LANE4_MATHLIB_PROJECT); builds
proofs/build/Lane4/Robust.olean first if missing. Compiles Bridge/IBP.lean and Bridge/Region.lean
into bridge/lean/build, then each selected net file, one Lean process at a time.

Sets (default: stage1, float, n8):
  stage1  ORD_w16_s100..107 and STR_w16_s100..107   (n = 6, kernel-checked at tau = 1/1000, about 1 minute each)
  float   ORDF_w16_s100..107                         (n = 6, exact dyadic float64 weights, about 1.5 minutes each)
  n8      N8_w24_s100                                 (n = 8, about 8 minutes; the other seven are not re-run by default)
  rnn     RNNC_* nine test certificates of unit 4 (trained RNNs, all lengths; builds Bridge/RNN and Bridge/RNNClust first;
          NOT in the default; about 12 s each, about 4 GB of commit)
  rnnpipe RNNC_L3_ORD_d4_s2, the pipeline-check net (outside dev and test)
  region  R_MAJ10_w32_s104_maj                        (n = 10 majority, region certificate; NOT in the default: it did not finish
                                                       within a 1,500 s time limit in the release re-check)
Not re-run: N10_w32_s100 (hit a 900 s stop; recorded), the other R_MAJ10 files and the n = 12 columns (CPU only).
A file passes when Lean exits 0 with no error, no `sorry`, and every `#print axioms` line within
propext, Classical.choice, Quot.sound.
"""
import argparse, json, os, re, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))          # repository root
sys.path.insert(0, os.path.join(ROOT, "proofs", "tools"))
import check as C
sys.stdout.reconfigure(encoding="utf-8", errors="replace")
ap = argparse.ArgumentParser()
ap.add_argument("--set", default="stage1,float,n8")
ap.add_argument("--out", default=os.path.join(ROOT, "proofs", "results", "recheck-bridge.json"))
ap.add_argument("--timeout", type=int, default=1500)
a = ap.parse_args()
C.MEM_KILL_GB = 6.0
BUILD = os.path.join(HERE, "lean", "build")
LEAN = os.path.join(HERE, "lean")
_lp = C.lean_path
C.lean_path = lambda: os.pathsep.join([BUILD, _lp()])
C.ensure_basic(name="Robust")
rows, t0 = [], time.time()


def run(src, olean=None):
    args = [src] + (["-o", olean] if olean else [])
    if olean:
        os.makedirs(os.path.dirname(olean), exist_ok=True)
    r = C.run_lean(args, a.timeout, LEAN)
    out = r["out"]
    ax = set()
    for lst in re.findall(r"depends on axioms: \[(.*?)\]", out, flags=re.S):
        ax |= {x.strip() for x in lst.replace("\n", " ").split(",") if x.strip()}
    ok = r["rc"] == 0 and not r["timed_out"] and not r["mem_killed"] and not re.search(r": error", out) \
        and "sorry" not in out and ax <= C.ALLOWED_AXIOMS
    return {"unit": os.path.relpath(src, ROOT).replace("\\", "/"), "pass": ok, "secs": r["secs"],
            "peak_rss_gb": r["peak_rss_gb"], "axioms": sorted(ax),
            "n_axiom_reports": len(re.findall(r"depends on axioms|does not depend", out)),
            "tail": out[-300:] if not ok else ""}


fw = ["IBP", "Region"] + (["RNN", "RNNClust"] if re.search(r"rnn", a.set) else [])
for name in fw:
    row = run(os.path.join(LEAN, "Bridge", name + ".lean"), os.path.join(BUILD, "Bridge", name + ".olean"))
    rows.append(row); print("PASS" if row["pass"] else "FAIL", row["unit"], row["secs"], flush=True)
sets = {
    "stage1": ["ORD_w16_s%d" % s for s in range(100, 108)] + ["STR_w16_s%d" % s for s in range(100, 108)],
    "float": ["ORDF_w16_s%d" % s for s in range(100, 108)],
    "n8": ["N8_w24_s100"],
    "rnn": ["RNNC_" + x for x in ["L1_ORD_d8_s100", "L1_ORD_d8_s106", "L1_ORD_d8_s107", "L1_SAT_d8_s106", "L3_ORD_d8_s100",
                                  "L3_SAT_d8_s103", "L3_SAT_d8_s104", "L3_SAT_d8_s105", "L3_SAT_d8_s107"]],
    "rnnpipe": ["RNNC_L3_ORD_d4_s2"],
    "region": ["R_MAJ10_w32_s104_maj"],
}
for s in a.set.split(","):
    for n in sets[s]:
        row = run(os.path.join(LEAN, "Bridge", "Nets", n + ".lean"))
        rows.append(row)
        print("PASS" if row["pass"] else "FAIL", row["unit"], row["secs"], "rss=%s" % row["peak_rss_gb"], row["axioms"], flush=True)
        json.dump(rows, open(a.out, "w", encoding="utf-8"), indent=1)
json.dump(rows, open(a.out, "w", encoding="utf-8"), indent=1)
print("total wall seconds: %.0f; passed %d of %d" % (time.time() - t0, sum(r["pass"] for r in rows), len(rows)))
