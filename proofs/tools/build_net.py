"""Compile one per-network Lean file under the limits of PREREG_R8 Amendment 1: 900 s, 6 GB peak commit.

    python tools/build_net.py <Net.lean>          RUN UNDER A 5 GB MEMORY RESERVATION (tools/lean_lease5.sh)

The runner stops the job at 900 s (and at 6 GB working set as a safety stop); peak commit is measured and the
last line says whether the job stayed within both limits. A job outside them is "not checked within limits".
"""
import os, sys
sys.stdout.reconfigure(encoding="utf-8", errors="replace")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check as C

C.MEM_KILL_GB = 6.0
src = os.path.abspath(sys.argv[1])
C.ensure_basic()
r = C.run_lean([src], 900, C.HERE)
within = (r["rc"] == 0 and not r["timed_out"] and not r["mem_killed"] and r["secs"] <= 900 and (r["peak_commit_gb"] or 0) <= 6.0)
print("rc", r["rc"], "secs", r["secs"], "rss", r["peak_rss_gb"], "commit", r["peak_commit_gb"],
      "timed_out", r["timed_out"], "mem_killed", r["mem_killed"])
print(r["out"][:8000])
print("WITHIN_LIMITS", within)
