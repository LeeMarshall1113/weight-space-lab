"""Rung-7 numeric checks on the networks the checker accepted (PREREG_R7.md Amendment 2, point 4). numpy, CPU.

    python tools/r7_checks.py            -> results/rung7-lane-checks.json
    RUN UNDER reservation wrapper; the script also exits itself above 2.5 GB of commit.

Fixed before the run (2026-11-20), for every network with kernel == "accept" in results/rung7-kernel.json:
  trained T, no perturbation, float64, unrounded order of operations as numpy gives it:
      lengths 6, 40, 300, 2000 (all positions up to 300, sampled above), then 16,000 and 65,534 tokens
      (1,000 sampled positions each), the input patterns of rung 4 (C4.gen_input).
  trained T, no perturbation, float32 in the stated order: 1,000 / 16,000 / 65,534 tokens.
  skeleton W under the rung-6a numeric checks unchanged (tools/r6a_checks.check, delta 1/1000):
      inside the ball (40 uniform + 40 sign corners), outside at 2, 4, ..., 64 times the radius,
      float32 with perturbations, relative ball, additive row.
These are searches over inputs and random draws, not proofs. "Exact rational" evaluation of the network
does not exist: the softmax uses exp. float64 is the study team's stand-in for exact arithmetic, as in rung 6a.
"""
import json, os, sys, time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r6net as R, r4pool as P, r4_checks as C4, r5_checks as C5, r6a_checks as C6, r7

HERE = P.HERE

if __name__ == "__main__":
    C5.memory_guard(2.5)
    rows = [r for r in json.load(open(os.path.join(HERE, "results", "rung7-kernel.json"))) if r["kernel"] == "accept"]
    out_path = os.path.join(HERE, "results", "rung7-lane-checks.json")
    out = json.load(open(out_path)) if os.path.exists(out_path) else {}
    for r in rows:
        tag = r["tag"]
        if tag in out:
            continue
        t0 = time.time()
        c = r7.task(r["task"])
        target = lambda w: r7.target(c, w)
        d = os.path.join(HERE, "runs", "r7-stage0", r["task"], "u5", "s%d" % r["seed"])
        T, W = C6.load_net(os.path.join(d, "T.json")), C6.load_net(os.path.join(d, "W.json"))
        rng = np.random.default_rng(7000 + r["seed"])
        gen = lambda n: C4.gen_input(c, n, rng)
        res = {"seed": r["seed"]}
        f64 = {}
        for n in (6, 40, 300, 2000, 16000, 65534):
            worst = 0.0
            for _ in range(10 if n <= 300 else (3 if n == 2000 else 1)):
                w = gen(n)
                q = np.arange(1, n + 1) if n <= 300 else C4.queries(n, rng, cap=1000)
                worst = max(worst, C6.dev(T, target, w, None, np.float64, q))
            f64[str(n)] = worst
        res["T_float64_max_dev"] = f64
        f32 = {}
        for n in (1000, 16000, 65534):
            w = gen(n)
            f32[str(n)] = C6.dev(T, target, w, None, np.float32, C4.queries(n, rng, cap=1000))
        res["T_float32_max_dev"] = f32
        res["W_r6a_checks"] = C6.check(W, c, target, 1e-3)
        res["secs"] = round(time.time() - t0, 1)
        out[tag] = res
        json.dump(out, open(out_path, "w"), indent=1)
        print(tag, "| T f64", " ".join("%s:%.4f" % kv for kv in f64.items()), "| T f32", " ".join("%s:%.4f" % kv for kv in f32.items()),
              "| W inside %.4f" % max(res["W_r6a_checks"]["inside_ball_max_dev"].values()),
              "| breaks", res["W_r6a_checks"]["smallest_violating_multiple"], "| %.0f s" % res["secs"], flush=True)
