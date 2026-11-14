"""Run tools/r3_checks.py on every exported net of an arm that has no r3_checks.json yet.

    python tools/r3_checks_all.py runs/rung3-test [arm]
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "2"); os.environ.setdefault("OPENBLAS_NUM_THREADS", "2")
import glob, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r3_checks as R
root = os.path.abspath(sys.argv[1]); arm = sys.argv[2] if len(sys.argv) > 2 else "net"
for d in sorted(glob.glob(os.path.join(root, arm, "*"))):
    if os.path.exists(os.path.join(d, "net.json")) and not os.path.exists(os.path.join(d, "r3_checks.json")):
        R.main(d)
