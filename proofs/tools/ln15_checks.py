"""Rung 9-LN15 numericchecks on accepted networks (searches, not proofs; PREREG_R9LN15.md):
trained network in float32 and float64 on inputs up to 65,534 tokens; skeleton W14 under sampled perturbations
inside the 2^-15 ball (uniform and sign corners, LayerNorm gains and biases included); the smallest multiple of
the radius at which a sampled perturbation breaks the 1/4 bound; the numeric interval test against the mirror.
    python tools/ln15_checks.py <dir of seeds> <seed> ...   -> results/rung9ln15-lanechecks.json (appends by seed)"""
import json, os, sys
from fractions import Fraction as F
import numpy as np
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(HERE, "tools"))
import r9ln as N, r9ln15_cert as C, r9ln_proto as L3, r4_checks as C4, r5_checks as C5
C5.memory_guard(2.5)
RAD = F(1, 2 ** 15)
outp = os.path.join(HERE, "results", "rung9ln15-lanechecks.json")
res = json.load(open(outp)) if os.path.exists(outp) else {}
base = sys.argv[1]
for seed in [int(x) for x in sys.argv[2:]]:
    d = os.path.join(HERE, base, "A", "n1", "s%03d" % seed)
    Tq, Wq = json.load(open(os.path.join(d, "T.json"))), json.load(open(os.path.join(d, "W14.json")))
    T, W = N.fmap(Tq, lambda v: float(F(v))), N.fmap(Wq, lambda v: float(F(v)))
    dev = lambda net, w, pert, dt, q: float(np.max(np.abs(N.run(net, w, pert, dt, q) - np.array(N.target(w), dtype=np.float64)[q - 1])))
    rng = np.random.default_rng(1000 + seed)
    gen = lambda n: C4.gen_input(N.C, n, rng)
    r = {"seed": seed}
    for name, dt in (("T_f32", np.float32), ("T_f64", np.float64)):
        worst = 0.0
        for n in (6, 40, 300, 2000, 2000, 16000, 65534):
            w = gen(n); worst = max(worst, dev(T, w, None, dt, C4.queries(n, rng, cap=2000)))
        r[name + "_dev_to_65534"] = worst
    inside = 0.0
    for kind in ("uniform", "sign"):
        for _ in range(30):
            w = gen(int(rng.choice([6, 40, 300, 2000])))
            inside = max(inside, dev(W, w, N.random_pert(W, float(RAD), rng, kind), np.float64, C4.queries(len(w), rng)))
    r["W14_inside_ball_dev"] = inside
    r["breaks_at_multiple"] = None
    for mult in (2, 4, 8, 16, 32, 64, 128, 256, 512):
        bad = 0.0
        for _ in range(10):
            w = gen(int(rng.choice([40, 300])))
            bad = max(bad, dev(W, w, N.random_pert(W, float(RAD) * mult, rng, "sign"), np.float64, C4.queries(len(w), rng)))
        if bad > 0.25: r["breaks_at_multiple"] = mult; break
    table = {}
    ok, why, info = C.check(Wq, RAD, table)
    r["mirror_ok"] = bool(ok)
    if ok: r["interval_test"] = L3.interval_test(Wq, RAD, seed, table)
    res[str(seed)] = r
    json.dump(res, open(outp, "w"), indent=1)
    print(r, flush=True)
