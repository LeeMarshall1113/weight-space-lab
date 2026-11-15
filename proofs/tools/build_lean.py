"""Compile one framework or scratch Lean file with the guarded runner (600 s, 4.5 GB).

    python tools/build_lean.py Lane4/Seq.lean [build/Lane4/Seq.olean]

Budget about 4.5 GB and run one at a time.
"""
import os, sys
sys.stdout.reconfigure(encoding="utf-8", errors="replace")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check as C

src = os.path.abspath(sys.argv[1])
C.ensure_basic()
args = [src]
if len(sys.argv) > 2:
    out = os.path.abspath(sys.argv[2])
    os.makedirs(os.path.dirname(out), exist_ok=True)
    args += ["-o", out]
r = C.run_lean(args, 600, C.HERE)
print("rc", r["rc"], "secs", r["secs"], "rss", r["peak_rss_gb"], "commit", r["peak_commit_gb"],
      "timed_out", r["timed_out"], "mem_killed", r["mem_killed"])
print(r["out"][:8000])
if r["rc"] != 0 and len(sys.argv) > 2 and os.path.exists(sys.argv[2]):
    os.remove(sys.argv[2])
