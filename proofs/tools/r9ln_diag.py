"""Rung 9-LN K2 diagnostics (tuning networks only): where does the prototype's radius come from?"""
import json, os, sys
from fractions import Fraction as F
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(HERE, "tools"))
import r9ln_proto as L, r9_proto as P9
AF, RND = P9.AF, P9.RND
for seed in [int(x) for x in sys.argv[1:]]:
    net = json.load(open(os.path.join(HERE, "runs", "r9ln-tune", "A", "n1", "s%03d" % seed, "W14.json")))
    Q = lambda m: [[F(v) for v in r] for r in m]
    E = Q(net["embed"]); d = len(E[0]); delta = F(1, 2 ** 14); e0 = delta + RND
    LN = {n: ([F(v) for v in net["ln"][n]["g"]], [F(v) for v in net["ln"][n]["b"]]) for n in ("ln1", "ln2", "lnf")}
    print("seed", seed)
    for n in ("ln1", "ln2", "lnf"):
        print("  ", n, "gain", [round(float(g), 2) for g in LN[n][0]], "bias", [round(float(b), 2) for b in LN[n][1]])
    for t in range(len(E)):
        m = sum(E[t]) / d; var = sum((x - m) ** 2 for x in E[t]) / d
        try:
            hs, v = L.ln_af([AF(E[t][r], None, e0) for r in range(d)], *LN["ln1"], delta, "LN1")
            rad = max(float(a.dev()) for a in hs)
        except P9.Reject as ex:
            rad = str(ex)
        print("   token %d: embedding variance %.2e  sigma %.4f  nonzero %d  | LN1 output radius max %s" % (t, float(var), float(var + L.EPS) ** 0.5, sum(x != 0 for x in E[t]), rad))
