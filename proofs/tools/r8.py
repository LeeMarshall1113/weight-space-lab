"""Rung 8: the screen at the rung-8 ball, and the fresh-seed sweep (PREREG_R8.md). RUN UNDER reservation wrapper.

    python tools/r8.py screen8 <dir with T.json and the frozen rung-7 screen.json>   -> W14.json, screen8.json
    python tools/r8.py sweep <task A|B> <recipe> <seed0> <seed1> [--out runs/r8-fresh]
        per seed: tools/r7.py train (frozen), tools/r7.py screen (frozen rung-7 screen), then screen8
    python tools/r8.py old <task> <recipe> <seed0> <seed1>
        screen8 only, on networks already under runs/r7-stage0 (tuning set; nothing is trained)

The training script and the rung-7 screen (tools/r7.py) are frozen and are not edited; this file calls them.

Screen 8 (pass = s1 and s3'):
  s1   exactly the frozen screen's s1, read from its screen.json: the network as trained, float32 in the stated
       order, worst |output - target| <= 1/4 on inputs up to 65,534 tokens.
  s3'  the skeleton W14 (every weight of T rounded to the nearest multiple of 2^-14) under 20 uniform and 20
       sign-corner additive perturbations of every weight at radius 2^-14, float64, lengths 6 to 2,000: worst
       deviation <= 0.10. This is the frozen s3 with the skeleton step and the radius of the rung-8 statement
       in place of 1/1024 and 1/1000; the threshold 0.10 and the sampling plan are unchanged.
  recorded, not part of the pass: the multiple of 2^-14 at which W14 breaks; non-zero weights of W14.
"""
import json, os, sys, time
from fractions import Fraction as F
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r7, r6net as R, r4_checks as C4, r5_checks as C5

HERE = r7.HERE
G = 14


def screen8(d):
    tj = json.load(open(os.path.join(d, "train.json")))
    old = json.load(open(os.path.join(d, "screen.json")))
    c = r7.task(tj["task"])
    s = F(1, 2 ** G)
    Tq = json.load(open(os.path.join(d, "T.json")))
    Wq = r7.fmap(Tq, lambda v: "%d/%d" % (round(F(v) / s) * s).as_integer_ratio())
    json.dump(Wq, open(os.path.join(d, "W14.json"), "w"))
    W = r7.fmap(Wq, lambda v: float(F(v)))
    for B in W["blocks"]:
        B["W1"] = np.array(B["W1"], float).reshape(r7.H, r7.D).tolist()
    a, b = r7.flat(Tq), r7.flat(Wq)
    res = {"task": tj["task"], "recipe": tj["recipe"], "seed": tj["seed"], "grid": "2^-%d" % G, "radius": "2^-%d" % G,
           "delta_T": float(max(abs(x - y) for x, y in zip(a, b))), "nonzero_W14": sum(1 for y in b if y != 0),
           "weights": len(b), "max_abs_W14": float(max(abs(y) for y in b)),
           "s1_ok": bool(old.get("s1_ok", False)),
           "T_f32_dev": old.get("T_f32_dev_to_65534", old.get("T_f32_dev_to_300")),
           "rung7_screen_pass": bool(old.get("pass", False))}
    if not res["s1_ok"]:
        res["pass"] = False
        json.dump(res, open(os.path.join(d, "screen8.json"), "w"), indent=1)
        return res
    rng = np.random.default_rng(72)
    tg = lambda w: r7.target(c, w)
    gen = lambda n: C4.gen_input(c, n, rng)

    def dev(w, pert, q):
        y = R.run(W, w, pert, np.float64, q)
        return float(np.max(np.abs(y - np.array(tg(w), dtype=np.float64)[q - 1])))
    rad = 2.0 ** -G
    inside = {}
    for kind in ("uniform", "sign"):
        wi = 0.0
        for _ in range(20):
            w = gen(int(rng.choice([6, 40, 300, 2000])))
            wi = max(wi, dev(w, R.random_pert(W, rad, rng, kind), C4.queries(len(w), rng)))
        inside[kind] = wi
    res["W14_inside_ball_dev"] = inside
    res["s3_ok"] = bool(max(inside.values()) <= 0.10)
    res["W14_breaks_at_multiple"] = None
    for mult in (2, 4, 8, 16, 32, 64, 128, 256):
        wi = 0.0
        for _ in range(10):
            w = gen(int(rng.choice([6, 40, 300, 2000])))
            wi = max(wi, dev(w, R.random_pert(W, mult * rad, rng, "sign"), C4.queries(len(w), rng)))
            if wi > r7.TOL: break
        if wi > r7.TOL:
            res["W14_breaks_at_multiple"] = mult
            break
    res["pass"] = bool(res["s1_ok"] and res["s3_ok"])
    json.dump(res, open(os.path.join(d, "screen8.json"), "w"), indent=1)
    return res


def line(d, t0):
    r = json.load(open(os.path.join(d, "screen8.json")))
    print("%s %s s%d | T f32 dev %.3f | s1 %s | W14 inside 2^-14 ball %s | breaks at x%s | rung-7 screen %s | SCREEN 8 PASS %s | %.0f s" % (
        r["task"], r["recipe"], r["seed"], r["T_f32_dev"], r["s1_ok"],
        ("%.3f" % max(r["W14_inside_ball_dev"].values())) if "W14_inside_ball_dev" in r else "-",
        r.get("W14_breaks_at_multiple"), r["rung7_screen_pass"], r["pass"], time.time() - t0), flush=True)


if __name__ == "__main__":
    C5.memory_guard(2.5)
    a = sys.argv
    if a[1] == "screen8":
        print(json.dumps(screen8(os.path.abspath(a[2]))))
    elif a[1] == "old":
        for seed in range(int(a[4]), int(a[5]) + 1):
            t0 = time.time()
            d = os.path.join(HERE, "runs", "r7-stage0", a[2], a[3], "s%d" % seed)
            screen8(d); line(d, t0)
    elif a[1] == "sweep":
        assert int(a[4]) >= 140, "fresh seeds start at 140"
        out = os.path.join(HERE, a[a.index("--out") + 1] if "--out" in a else "runs/r8-fresh")
        for seed in range(int(a[4]), int(a[5]) + 1):
            t0 = time.time()
            d = os.path.join(out, a[2], a[3], "s%03d" % seed)
            if not os.path.exists(os.path.join(d, "T.json")):
                r7.train(a[2], a[3], seed, out)
            if not os.path.exists(os.path.join(d, "screen.json")):
                r7.screen(d)
            if not os.path.exists(os.path.join(d, "screen8.json")):
                screen8(d)
            line(d, t0)
