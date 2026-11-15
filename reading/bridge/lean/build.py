"""Compile one bridge Lean file against the proofs study's built framework (read-only) + Mathlib.

    python bridge/lean/build.py Bridge/IBP.lean [build/Bridge/IBP.olean]     (paths relative to bridge/lean)
Budget several GB of RAM. Reuses the proofs study's guarded runner (tools/check.py) with a 7 GB kill.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
L4 = os.path.abspath(os.path.join(HERE, "..", "..", "..", "proofs", "tools"))
sys.path.insert(0, L4)
sys.stdout.reconfigure(encoding="utf-8", errors="replace")
import check as C  # noqa: E402  (the proofs study, read-only)

BUILD = os.path.join(HERE, "build")
_lp = C.lean_path
C.lean_path = lambda: os.pathsep.join([BUILD, _lp()])
C.MEM_KILL_GB = 7.0

src = sys.argv[1]
args = [src]
if len(sys.argv) > 2:
    out = os.path.join(HERE, sys.argv[2])
    os.makedirs(os.path.dirname(out), exist_ok=True)
    args += ["-o", out]
timeout = int(os.environ.get("BRIDGE_LEAN_TIMEOUT", "1800"))
r = C.run_lean(args, timeout, HERE)
print("rc", r["rc"], "secs", r["secs"], "rss", r["peak_rss_gb"], "commit", r["peak_commit_gb"],
      "timed_out", r["timed_out"], "mem_killed", r["mem_killed"])
print(r["out"][:12000])
sys.exit(r["rc"] or 0)
