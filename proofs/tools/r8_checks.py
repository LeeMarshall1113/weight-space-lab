"""Rung 8 numeric checks on every kernel-accepted network (PREREG_R8.md, "Numeric checks on every accepted network"),
plus the two mirror-only items of the registration. numpy, CPU. RUN UNDER reservation wrapper. Searches, not proofs.
Written 2026-11-21 AFTER the checker freeze and after the A count was read; it calls the frozen mirror
(tools/r8_cert.py) and the earlier lane-check helpers unchanged and edits no frozen file.

    python tools/r8_checks.py lane     -> results/rung8-lane-checks.json   (resumable by tag)
    python tools/r8_checks.py extra    -> results/rung8-extra.json

lane, for every job in scratch/r8jobs/{bar,A-rest,B-ok}.txt whose lean.log shows theorem accept:
  trained T, no perturbation, float64: lengths 6, 40, 300, 2000 (all positions to 300, sampled above), 16,000 and
      65,534 tokens (1,000 sampled positions); float32 in the stated order: 1,000 / 16,000 / 65,534 tokens.
      (the plan of tools/r7_checks.py)
  the skeleton of the job (W14.json, or W.json for the 1/1000 jobs) under tools/r6a_checks.check at the job's
      radius: inside the ball (uniform and sign-corner draws), outside at 2, 4, ... times the radius (break multiple).
  numeric interval test, the plan of tools/r8_k1.py sound_test with the frozen mirror's table in place of the
      prototype's: forward passes (float64 short inputs with sampled perturbations inside the ball, float32 at
      2,000 and 65,534 tokens) must land inside the mirror's interval for the abstract case of each position.
extra:
  control 8, mirror only: the task-failing B u5 networks of seeds 100 to 139 other than the first five by seed,
      W14 at 2^-14 and W.json at 1/1000, each must be rejected.
  the rung-7 checker's mirror (tools/r7_cert.py) on the fresh B u5 networks that pass the frozen rung-7 screen.
"""
import json, os, sys, time
from fractions import Fraction as F
import numpy as np

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(HERE, "tools"))
import r8_cert as C, r7_cert as RC, r7, r6net as R, r4_checks as C4, r5_checks as C5, r6a_checks as C6


def jobs():
    out = []
    for name in ("bar", "A-rest", "B-ok"):
        for ln in open(os.path.join(HERE, "scratch", "r8jobs", name + ".txt")):
            p = ln.rstrip("\n").split("|")
            if len(p) < 2 or not p[0]: continue
            extra = p[2].split() if len(p) > 2 else []
            netf = extra[extra.index("--net") + 1] if "--net" in extra else "W14.json"
            rad = F(extra[extra.index("--radius") + 1]) if "--radius" in extra else F(1, 2 ** 14)
            out.append((p[1], os.path.join(HERE, p[0]), netf, rad))
    return out


def accepted(tag):
    f = os.path.join(HERE, "runs", "r8-nets", tag, "lean.log")
    if not os.path.exists(f): return None
    s = open(f).read()
    if "'Lane4.Net.accept' depends on axioms" in s: return True
    if "'Lane4.Net.reject' depends on axioms" in s: return False
    return None


def interval_test(Wq, task, rad, seed):
    table = {}
    ok, why, info = C.check(Wq, task, rad, table)
    if not ok: return {"mirror": "reject", "reason": why}
    heads = table.pop("__heads__"); table.pop("__states__", None)
    tmp = os.path.join(HERE, "scratch", "_r8_tmp.json")
    json.dump(Wq, open(tmp, "w")); net = C6.load_net(tmp)
    rng = np.random.default_rng(8000 + seed)
    res = {"mirror": "accept", "positions": 0, "violations": 0, "smallest_slack": 1e9}
    plan = [(int(rng.choice([3, 8, 30, 200])), np.float64, k % 3) for k in range(45)] + [(2000, np.float32, 0), (2000, np.float32, 1), (65534, np.float32, 0)]
    for n, dt, pk in plan:
        w = rng.integers(1, 6, n)
        pert = None if pk == 0 else R.random_pert(net, float(rad), rng, "sign" if pk == 1 else "uniform")
        q = np.arange(1, n + 1) if n <= 200 else np.sort(rng.choice(np.arange(1, n + 1), 500, replace=False))
        y = R.run(net, w, pert, dt, q)
        toks = [0] + [int(t) for t in w]
        for yi, i in zip(y, q):
            i = int(i); t = toks[i]; sel = []
            for hd in heads:
                prev, j = [], i - 1
                while j >= 0 and len(prev) < hd["L"]:
                    if hd["cand"][toks[j]]: prev.append(toks[j])
                    j -= 1
                sel.append((((t,) if (hd["mask"] == "causal" and hd["cand"][t]) else ()) + tuple(prev)))
            o = table[(t, tuple(sel))][2]
            slack = min(float(yi) - float(o.lo()), float(o.hi()) - float(yi))
            res["positions"] += 1; res["violations"] += int(slack < 0)
            res["smallest_slack"] = min(res["smallest_slack"], slack)
    return res


def lane():
    out_path = os.path.join(HERE, "results", "rung8-lane-checks.json")
    out = json.load(open(out_path)) if os.path.exists(out_path) else {}
    for tag, d, netf, rad in jobs():
        if tag in out or accepted(tag) is not True: continue
        t0 = time.time()
        tj = json.load(open(os.path.join(d, "train.json")))
        c = r7.task(tj["task"])
        target = lambda w: r7.target(c, w)
        T, W = C6.load_net(os.path.join(d, "T.json")), C6.load_net(os.path.join(d, netf))
        rng = np.random.default_rng(8800 + tj["seed"])
        gen = lambda n: C4.gen_input(c, n, rng)
        res = {"task": tj["task"], "seed": tj["seed"], "skeleton": netf, "radius": str(rad)}
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
        res["skeleton_r6a_checks"] = C6.check(W, c, target, float(rad))
        res["interval_test"] = interval_test(json.load(open(os.path.join(d, netf))), tj["task"], rad, tj["seed"])
        res["secs"] = round(time.time() - t0, 1)
        out[tag] = res
        json.dump(out, open(out_path, "w"), indent=1)
        it = res["interval_test"]
        print(tag, "| T f64 max %.4f" % max(f64.values()), "| T f32 max %.4f" % max(f32.values()),
              "| skeleton inside %.4f" % max(res["skeleton_r6a_checks"]["inside_ball_max_dev"].values()),
              "| breaks", res["skeleton_r6a_checks"]["smallest_violating_multiple"],
              "| intervals: %s positions, %s violations, slack %.5f" % (it.get("positions"), it.get("violations"), it.get("smallest_slack", -1)),
              "| %.0f s" % res["secs"], flush=True)


def extra():
    out = {"control8_mirror_only": [], "rung7_checker_fresh_B": []}
    bad = []
    for s in range(100, 140):
        d = os.path.join(HERE, "runs", "r7-stage0", "B", "u5", "s%d" % s)
        if not json.load(open(os.path.join(d, "screen.json"))).get("s1_ok", False): bad.append((s, d))
    print("task-failing B u5 networks, seeds 100-139:", len(bad), [s for s, _ in bad], flush=True)
    for s, d in bad[5:]:
        for netf, rad in (("W14.json", F(1, 2 ** 14)), ("W.json", F(1, 1000))):
            ok, why, info = C.check(json.load(open(os.path.join(d, netf))), "B", rad)
            out["control8_mirror_only"].append(dict(seed=s, skeleton=netf, radius=str(rad), ok=ok, reason=why))
            print("control 8 (mirror only) B u5 s%d %s radius %s ->" % (s, netf, rad), "ACCEPT (BAD)" if ok else "reject", "|", why[:120], flush=True)
    for s in range(140, 160):
        d = os.path.join(HERE, "runs", "r8-fresh", "B", "u5", "s%03d" % s)
        if not json.load(open(os.path.join(d, "screen.json"))).get("pass"): continue
        ok = RC.check(json.load(open(os.path.join(d, "W.json"))), "B", verbose=False)
        out["rung7_checker_fresh_B"].append(dict(seed=s, ok=bool(ok[0]), reason=str(ok[1])[:200] if len(ok) > 1 else ""))
        print("rung-7 checker (mirror) fresh B u5 s%d W.json radius 1/1000 ->" % s, "accept" if ok[0] else "reject", flush=True)
    json.dump(out, open(os.path.join(HERE, "results", "rung8-extra.json"), "w"), indent=1)


if __name__ == "__main__":
    C5.memory_guard(2.5)
    {"lane": lane, "extra": extra}[sys.argv[1]]()
