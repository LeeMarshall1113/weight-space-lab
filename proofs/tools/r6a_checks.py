"""Rung-6a numeric checks on exported gated nets (PREREG_R6A.md, "Checks the study team runs"). numpy, CPU.

    python tools/r6a_checks.py runs/rung6a-test [--quick]   -> <case>/r6a_checks.json per net
    python tools/r6a_checks.py selftest                      -> two-block shape test at 65,534 tokens
    RUN UNDER reservation wrapper (hard cap); the script also exits itself above 2.5 GB of commit.

Fixed before any run (delta = the case's additive radius, tolerance 1/4):
  inside   : 40 uniform + 40 sign-corner ADDITIVE perturbations of every weight at delta,
             float64, lengths 6, 40, 300, 2000, the four input patterns of rung 4.
  outside  : 30 sign-corner perturbations at s*delta for s = 2, 4, ..., 64 (lengths up to 20,000).
  binary32 : numpy float32 in the stated order, written weights and 5 sign-corner perturbations
             at delta, at 1,000 / 16,000 / 65,534 tokens. The perturbation draws are the SAME
             at every length (seeded by trial), so the columns are comparable.
  relative : the same nets under the rung-4 RELATIVE ball of 1/200 (40 sign corners, zeros fixed).
  2x2 row  : additive 1/1000 on every weight at lengths 100 and 1,000, per length (50 corners).
A PyTorch module is not built here: rung 5 showed numpy and torch `exp` differ in the last
bit, so a torch pass would be a numeric comparison only; it is left out and said so.
"""
import glob, json, os, sys, time
from fractions import Fraction as F
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r6net as R, r4pool as P, r4_checks as C4, r5_checks as C5

HERE = P.HERE
TOL = 0.25


def load_net(path):
    j = json.load(open(path))
    q = lambda v: float(F(v))
    M = lambda m: [[q(v) for v in r] for r in m]
    return {"embed": M(j["embed"]), "outW": [q(v) for v in j["outW"]], "outB": q(j["outB"]),
            "blocks": [{"heads": [{"A": M(h["A"]), "V": M(h["V"]), "mask": h["mask"], "m": q(h["m"]),
                                   "g": [q(v) for v in h["g"]], "gb": q(h["gb"])} for h in B["heads"]],
                        "W1": M(B["W1"]), "b1": [q(v) for v in B["b1"]], "W2": M(B["W2"]),
                        "b2": [q(v) for v in B["b2"]]} for B in j["blocks"]]}


def rel_pert(net, tau, rng):
    """Additive offsets equal to a RELATIVE sign-corner perturbation (zeros stay zero)."""
    s = lambda a: tau * rng.choice([-1.0, 1.0], np.shape(a)) * np.array(a, dtype=float)
    D = len(net["embed"][0])
    p = {"embed": s(net["embed"]), "outW": s(net["outW"]), "outB": s(net["outB"]), "blocks": []}
    for B in net["blocks"]:
        H = len(B["b1"])
        p["blocks"].append({"W1": s(np.array(B["W1"], float).reshape(H, D)), "b1": s(B["b1"]),
                            "W2": s(np.array(B["W2"], float).reshape(D, H)), "b2": s(B["b2"]),
                            "heads": [{"A": s(h["A"]), "V": s(h["V"]), "m": s(h["m"]), "g": s(h["g"]), "gb": s(h["gb"])}
                                      for h in B["heads"]]})
    return p


def dev(net, target, w, pert, dtype, q):
    y = R.run(net, w, pert, dtype, q)
    tgt = np.array(target([int(t) for t in w]), dtype=np.float64)[q - 1]
    return float(np.max(np.abs(y - tgt)))


def check(net, c, target, delta, quick=False):
    rng = np.random.default_rng(61)
    k = 5 if quick else 1
    res = {"delta": delta, "blocks": len(net["blocks"]), "heads": [len(B["heads"]) for B in net["blocks"]],
           "width": len(net["outW"]), "mlp_hidden": [len(B["b1"]) for B in net["blocks"]]}
    gen = lambda n: C4.gen_input(c, n, rng)
    res["written_exact_max_dev"] = max(dev(net, target, w, None, np.float64, C4.queries(len(w), rng))
                                       for w in (gen(n) for n in (6, 40, 300, 2000)))
    inside = {}
    for kind in ("uniform", "sign"):
        worst = 0.0
        for t in range(40 // k):
            w = gen(int(rng.choice([6, 40, 300, 2000])))
            worst = max(worst, dev(net, target, w, R.random_pert(net, delta, rng, kind), np.float64, C4.queries(len(w), rng)))
        inside[kind] = worst
    res["inside_ball_max_dev"] = inside
    res["inside_ball_ok"] = bool(max(inside.values()) <= TOL)
    res["outside"], res["smallest_violating_multiple"] = {}, None
    for s in (2, 4, 8, 16, 32, 64):
        worst = 0.0
        for t in range(30 // k):
            w = gen(int(rng.choice([6, 40, 300, 2000, 20000])))
            worst = max(worst, dev(net, target, w, R.random_pert(net, s * delta, rng, "sign"), np.float64, C4.queries(len(w), rng)))
            if worst > TOL:
                break
        res["outside"][str(s)] = worst
        if worst > TOL:
            res["smallest_violating_multiple"] = s
            break
    f32 = {}
    for n in (1000, 16000, 65534):
        w = gen(n)
        q = C4.queries(n, rng, cap=1000)
        worst = dev(net, target, w, None, np.float32, q)
        for t in range(5 // k or 1):
            worst = max(worst, dev(net, target, w, R.random_pert(net, delta, np.random.default_rng(900 + t), "sign"), np.float32, q))
        f32[str(n)] = worst
    res["float32_max_dev"] = f32
    res["float32_ok_in_range"] = bool(max(f32.values()) <= TOL)
    worst = 0.0
    for t in range(40 // k):
        w = gen(int(rng.choice([6, 40, 300, 2000])))
        worst = max(worst, dev(net, target, w, rel_pert(net, 1 / 200, rng), np.float64, C4.queries(len(w), rng)))
    res["relative_1_200_max_dev"] = worst
    row = {}
    for n in (100, 1000):
        ws = [gen(n) for _ in range(2)]
        hits = 0
        for t in range(50 // k):
            p = R.random_pert(net, 1e-3, np.random.default_rng(500 + t), "sign")
            hits += any(dev(net, target, w, p, np.float64, np.arange(1, n + 1)) >= 0.5 for w in ws)
        row[str(n)] = hits
    res["additive_1_1000_breaks_of_%d" % (50 // k)] = row
    return res


if __name__ == "__main__":
    C5.memory_guard(2.5)
    if sys.argv[1] == "selftest":
        # a two-block, three-head net of width 8 with random small weights: shape and memory only
        rng = np.random.default_rng(0)
        D, H = 8, 4
        mk = lambda *s: (rng.integers(-2, 3, s) / 2).tolist()
        head = lambda: {"A": mk(D, D), "V": mk(D, D), "mask": "causal", "m": 24, "g": mk(D), "gb": -1}
        net = {"embed": mk(4, D), "outW": mk(D), "outB": 0,
               "blocks": [{"heads": [head()], "W1": mk(H, D), "b1": mk(H), "W2": mk(D, H), "b2": mk(D)},
                          {"heads": [head(), head()], "W1": mk(H, D), "b1": mk(H), "W2": mk(D, H), "b2": mk(D)}]}
        t0 = time.time()
        w = rng.integers(1, 4, 65534)
        y = R.run(net, w, R.random_pert(net, 1e-3, rng), np.float32, C4.queries(65534, rng, cap=1000))
        print("selftest: two blocks at 65,534 tokens, %d outputs, finite %s, %.0f s" % (len(y), bool(np.all(np.isfinite(y))), time.time() - t0))
        sys.exit(0)
    root = os.path.abspath(sys.argv[1])
    pool = {c["id"]: c for c in json.load(open(os.path.join(HERE, "pool", "rung4_pool.json")))}
    t0 = time.time()
    for d in sorted(glob.glob(os.path.join(root, "net*", "*"))):
        if os.path.exists(os.path.join(d, "net.json")) and not os.path.exists(os.path.join(d, "r6a_checks.json")):
            cid = os.path.basename(d)
            c = pool[cid]
            delta = float(F(json.load(open(os.path.join(d, "case.json")))["delta"]))
            res = check(load_net(os.path.join(d, "net.json")), c, lambda w, c=c: P.target(c, w), delta, "--quick" in sys.argv)
            res.update(id=cid, family=c["family"])
            json.dump(res, open(os.path.join(d, "r6a_checks.json"), "w"), indent=1)
            print(cid, c["family"], "blocks", res["blocks"], "| inside %.3f ok=%s" % (max(res["inside_ball_max_dev"].values()), res["inside_ball_ok"]),
                  "| breaks at %s delta" % res["smallest_violating_multiple"], "| f32 %.3f" % max(res["float32_max_dev"].values()),
                  "| relative 1/200 %.3f" % res["relative_1_200_max_dev"], flush=True)
    print("done in %.0f s" % (time.time() - t0))
