"""Rung 3, POST HOC (not pre-registered): how much of the fine-tune target would a program
with three or four tunable constants capture? Same data as tools/r3_checks.py seeds 0-2:
least-squares fit of an affine correction (spec + a.x + c) on the noisy training points,
scored on the same held-out points. Writes results/r3-posthoc-affine.json.
"""
import glob, json, os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r3_checks as R, train_twin as TT
from fractions import Fraction as F
rows = {}
for d in sorted(glob.glob(os.path.join(R.HERE, "runs", "rung3-test", "net", "*"))):
    meta, Wq, bq, e, box = R.load(d)
    delta = float(F(meta["delta"])); gains = []
    for seed in (0, 1, 2):
        g = np.random.default_rng(1000 + seed)
        lo, hi = np.array([b[0] for b in box], float), np.array([b[1] for b in box], float)
        c = g.normal(size=len(box)); c *= (delta / 4) / np.sum(np.abs(c) * (hi - lo) / 2)
        shift = lambda X: (X - (lo + hi) / 2) @ c
        Xtr = g.uniform(lo, hi, (2000, len(box))); Xte = g.uniform(lo, hi, (5000, len(box)))
        ytr = TT.spec_np(e, Xtr) + shift(Xtr) + g.normal(0, delta / 4, 2000)
        yte = TT.spec_np(e, Xte) + shift(Xte)
        A = np.c_[Xtr, np.ones(len(Xtr))]
        coef = np.linalg.lstsq(A, ytr - TT.spec_np(e, Xtr), rcond=None)[0]
        pred = TT.spec_np(e, Xte) + np.c_[Xte, np.ones(len(Xte))] @ coef
        gains.append(1 - float(np.mean((pred - yte) ** 2)) / float(np.mean((TT.spec_np(e, Xte) - yte) ** 2)))
    rows[meta["id"]] = gains
    print(meta["id"], [round(x, 3) for x in gains])
json.dump(rows, open(os.path.join(R.HERE, "results", "r3-posthoc-affine.json"), "w"), indent=1)
