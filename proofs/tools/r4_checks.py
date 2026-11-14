"""Rung-4 lane checks on exported nets (PREREG_R4.md, "Checks the lane runs"). numpy, CPU.

    python tools/r4_checks.py runs/rung4-test [--quick]     -> <case>/r4_checks.json per net
    (RUN UNDER A LEASE: tools/r4_checks_lease.sh)

Needs <case>/net.json (exact export) and the pool setting. Fixed here before any run:
  inside   : 60 uniform + 60 sign-corner relative perturbations at tau, float64, each on a
             fresh input (lengths 6, 40, 300, 2000; random, biased, constant-tail patterns).
  outside  : 40 sign-corner perturbations at s*tau for s = 2, 4, ..., 64, lengths up to
             20,000 (300 query positions when the length is over 2,000).
  float32  : forward pass in float32, written weights (no perturbation) and 5 sign-corner
             perturbations at tau, at 1,000 / 16,000 / 65,534 tokens; then beyond the
             theorem at 200,000 and 2,000,000 tokens (one-block nets only).
A deviation is |output - target|; the tolerance is 1/4.
"""
import glob, json, os, sys, time
from fractions import Fraction as F
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r4net as R, r4pool as P

HERE = P.HERE
TOL = 0.25


def load_net(path):
    j = json.load(open(path))
    q = lambda v: float(F(v))
    M = lambda m: [[q(v) for v in r] for r in m]
    return {"embed": M(j["embed"]), "outW": [q(v) for v in j["outW"]], "outB": q(j["outB"]),
            "blocks": [{"heads": [{"A": M(h["A"]), "V": M(h["V"]), "mask": h["mask"]} for h in B["heads"]],
                        "W1": M(B["W1"]), "b1": [q(v) for v in B["b1"]], "W2": M(B["W2"]),
                        "b2": [q(v) for v in B["b2"]]} for B in j["blocks"]]}


def gen_input(c, n, rng):
    V = c["V"]
    kind = rng.integers(0, 4)
    w = rng.integers(1, V + 1, n)
    if kind == 1:                                   # one token dominates
        t = rng.integers(1, V + 1)
        w = np.where(rng.random(n) < 0.9, t, w)
    elif kind == 2:                                 # random head, constant tail
        k = int(rng.integers(1, min(n, 6) + 1))
        w[k:] = rng.integers(1, V + 1)
    elif kind == 3:                                 # constant with one late change
        w[:] = rng.integers(1, V + 1)
        w[int(rng.integers(0, n))] = rng.integers(1, V + 1)
    return w


def queries(n, rng, cap=2000):
    if n <= cap:
        return np.arange(1, n + 1)
    return np.unique(np.concatenate([np.arange(1, 51), np.arange(n - 49, n + 1), rng.integers(1, n + 1, 200)]))


def dev(net, c, w, pert, dtype, q):
    y = R.run(net, w, pert, dtype, q)
    tgt = np.array(P.target(c, [int(t) for t in w]), dtype=np.float64)[q - 1]
    return float(np.max(np.abs(y - tgt)))


def check(casedir, c, quick=False):
    net = load_net(os.path.join(casedir, "net.json"))
    tau = float(F(json.load(open(os.path.join(casedir, "case.json")))["tau"]))
    rng = np.random.default_rng(41)
    k = 6 if quick else 1
    res = {"id": c["id"], "family": c["family"], "tau": tau, "blocks": len(net["blocks"]),
           "heads": [len(B["heads"]) for B in net["blocks"]], "width": len(net["outW"]),
           "mlp_hidden": [len(B["b1"]) for B in net["blocks"]]}
    res["written_exact_max_dev"] = max(dev(net, c, w, None, np.float64, queries(len(w), rng))
                                       for w in (gen_input(c, n, rng) for n in (6, 40, 300, 2000)))
    inside = {}
    for kind in ("uniform", "sign"):
        worst = 0.0
        for t in range(60 // k):
            w = gen_input(c, int(rng.choice([6, 40, 300, 2000])), rng)
            worst = max(worst, dev(net, c, w, R.random_pert(net, tau, rng, kind), np.float64, queries(len(w), rng)))
        inside[kind] = worst
    res["inside_ball_max_dev"] = inside
    res["inside_ball_ok"] = bool(max(inside.values()) <= TOL)
    res["outside"], res["smallest_violating_multiple"] = {}, None
    for s in (2, 4, 8, 16, 32, 64):
        worst = 0.0
        for t in range(40 // k):
            w = gen_input(c, int(rng.choice([6, 40, 300, 2000, 20000])), rng)
            worst = max(worst, dev(net, c, w, R.random_pert(net, s * tau, rng, "sign"), np.float64, queries(len(w), rng)))
            if worst > TOL:
                break
        res["outside"][str(s)] = worst
        if worst > TOL:
            res["smallest_violating_multiple"] = s
            break
    f32 = {}
    lengths = [1000, 16000, 65534] + ([200000, 2000000] if len(net["blocks"]) == 1 and not quick else [])
    for n in lengths:
        w = gen_input(c, n, rng)
        q = queries(n, rng, cap=1000)
        d0 = dev(net, c, w, None, np.float32, q)
        dp = max(dev(net, c, w, R.random_pert(net, tau, rng, "sign"), np.float32, q) for _ in range(5 // k or 1)) \
            if n <= 65534 else None
        f32[str(n)] = {"written": d0, "perturbed_at_tau": dp, "in_theorem_range": n <= 65534}
    res["float32"] = f32
    res["float32_ok_in_range"] = bool(all(max(v["written"], v["perturbed_at_tau"] or 0) <= TOL
                                          for v in f32.values() if v["in_theorem_range"]))
    json.dump(res, open(os.path.join(casedir, "r4_checks.json"), "w"), indent=1)
    print(c["id"], c["family"], "blocks", res["blocks"], "width", res["width"],
          "| exact %.3g" % res["written_exact_max_dev"],
          "| inside %.3f ok=%s" % (max(inside.values()), res["inside_ball_ok"]),
          "| breaks at %s tau" % res["smallest_violating_multiple"],
          "| f32 " + " ".join("%s:%.3g" % (n, max(v["written"], v["perturbed_at_tau"] or 0)) for n, v in f32.items()),
          flush=True)
    return res


if __name__ == "__main__":
    root = os.path.abspath(sys.argv[1])
    pool = {c["id"]: c for c in json.load(open(os.path.join(HERE, "pool", "rung4_pool.json")))}
    t0 = time.time()
    for d in sorted(glob.glob(os.path.join(root, "net", "*"))):
        if os.path.exists(os.path.join(d, "net.json")) and not os.path.exists(os.path.join(d, "r4_checks.json")):
            check(d, pool[os.path.basename(d)], "--quick" in sys.argv)
    print("done in %.0f s" % (time.time() - t0))
