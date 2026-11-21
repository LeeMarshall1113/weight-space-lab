"""Rung 8, kill rule K1 read (SCOPE_R8.md): the frozen prototype tools/r8_proto.py on the 18 screened A u3
networks and the 15 screened B u5 networks. No Lean, no doctor, no fresh seed. RUN UNDER reservation wrapper.

    python tools/r8_k1.py  -> results/rung8-k1.json, printed table

Design value: skeleton = trained weights rounded to multiples of 2^-14, ball radius 2^-14 ("g = 14").
Also reported: g = 10, 11, 12, 13, 16 (sensitivity), and the rung-7 skeleton W.json with radius 1/1000.
Controls on A u3 seed 110 at g = 14: wrong task, two embedding rows swapped, read-out negated, radius
times 16 and times 64, and every A u3 test-seed network that FAILED the screen.
Numeric soundness test (not a proof): float64 forward passes on short inputs with sampled perturbations
inside the ball, and float32 forward passes at 2,000 and 65,534 tokens, must land inside the prototype's
interval for the abstract case of each sampled position.
"""
import copy, json, os, sys, time
from fractions import Fraction as F
import numpy as np

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(HERE, "tools"))
import r8_proto as P, r7_cert as RC, r6net as R, r6a_checks as C6, r5_checks as C5

G0 = 14


def snap(net, g):
    q = lambda v: str(F(round(F(v) * 2 ** g), 2 ** g))
    def walk(x):
        if isinstance(x, list): return [walk(y) for y in x]
        if isinstance(x, dict): return {k: (v if k == "mask" else walk(v)) for k, v in x.items()}
        return q(x)
    return walk(net)


def screened(task, rec, lo, hi):
    scr = [json.load(open(os.path.join(HERE, "runs", "r7-stage0", task, rec, "s%d" % s, "screen.json"))) for s in range(lo, hi + 1)]
    order = sorted(scr, key=lambda j: (j["seed"] >= 120, j["nonzero_W"], j["seed"]))
    return [j["seed"] for j in order if j.get("pass")], [j["seed"] for j in order if not j.get("pass")]


def load(task, rec, seed, name):
    return json.load(open(os.path.join(HERE, "runs", "r7-stage0", task, rec, "s%d" % seed, name)))


def sound_test(Wn, task, g, seed):
    table = {}
    ok, why, info = P.check(Wn, task, F(1, 2 ** g), table)
    if not ok: return None
    heads = table.pop("__heads__")
    tmp = os.path.join(HERE, "scratch", "_r8_tmp.json")
    json.dump(Wn, open(tmp, "w")); net = C6.load_net(tmp)
    rng = np.random.default_rng(8000 + seed)
    res = {"positions": 0, "violations": 0, "smallest_slack": 1e9}
    plan = [(int(rng.choice([3, 8, 30, 200])), np.float64, k % 3) for k in range(45)] + [(2000, np.float32, 0), (2000, np.float32, 1), (65534, np.float32, 0)]
    for n, dt, pk in plan:
        w = rng.integers(1, 6, n)
        pert = None if pk == 0 else R.random_pert(net, 2.0 ** -g, rng, "sign" if pk == 1 else "uniform")
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
            res["positions"] += 1; res["violations"] += slack < 0
            res["smallest_slack"] = min(res["smallest_slack"], slack)
    return res


if __name__ == "__main__":
    C5.memory_guard(2.5)
    t0 = time.time()
    out = {"design_g": G0, "nets": {}, "controls": [], "sound_test": {}}
    for task, rec, lo, hi in (("A", "u3", 100, 119), ("B", "u5", 100, 139)):
        ok_seeds, bad_seeds = screened(task, rec, lo, hi)
        rows = []
        for s in ok_seeds:
            T = load(task, rec, s, "T.json")
            row = {"seed": s, "by_g": {}}
            for g in (10, 11, 12, 13, 14, 16):
                ok, why, info = P.check(snap(T, g), task, F(1, 2 ** g))
                row["by_g"][str(g)] = dict(ok=ok, reason=why, **info)
            ok, why, info = P.check(load(task, rec, s, "W.json"), task, RC.DELTA)
            row["rung7_skeleton_radius_1_1000"] = dict(ok=ok, reason=why, **info)
            row["rung7_checker"] = RC.check(load(task, rec, s, "W.json"), task, verbose=False)[0]
            d = row["by_g"][str(G0)]
            row["ok"], row["reason"] = d["ok"], d["reason"]
            rows.append(row)
            print(task, rec, s, "| g=14:", "ACCEPT %.3f" % d["worst"] if d["ok"] else "reject", "| window", d.get("window"), "spread", d.get("spread"),
                  "mixed rows", d.get("mixed_rows"), "| accepted at g:", [g for g in (10, 11, 12, 13, 14, 16) if row["by_g"][str(g)]["ok"]],
                  "| 1/1000 ball:", "accept" if row["rung7_skeleton_radius_1_1000"]["ok"] else "reject", "| rung-7 checker:", "accept" if row["rung7_checker"] else "reject",
                  "" if d["ok"] else "| " + d["reason"][:120], flush=True)
        out["nets"]["%s/%s" % (task, rec)] = rows
        print(task, rec, "ACCEPTED at g=14:", sum(r["ok"] for r in rows), "of", len(rows), flush=True)
        if task == "A":
            T = load("A", "u3", 110, "T.json"); Wn = snap(T, G0)
            ctl = [("wrong task (B automaton)", P.check(Wn, "B", F(1, 2 ** G0)))]
            w2 = copy.deepcopy(Wn); w2["embed"][1], w2["embed"][2] = w2["embed"][2], w2["embed"][1]
            ctl.append(("embedding rows 1 and 2 swapped", P.check(w2, "A", F(1, 2 ** G0))))
            w3 = copy.deepcopy(Wn); w3["outW"] = [str(-F(v)) for v in w3["outW"]]
            ctl.append(("read-out negated", P.check(w3, "A", F(1, 2 ** G0))))
            ctl.append(("radius x16", P.check(Wn, "A", F(16, 2 ** G0))))
            ctl.append(("radius x64", P.check(Wn, "A", F(64, 2 ** G0))))
            for s in bad_seeds:
                ctl.append(("A u3 seed %d (failed the screen)" % s, P.check(snap(load("A", "u3", s, "T.json"), G0), "A", F(1, 2 ** G0))))
            for name, (ok, why, info) in ctl:
                out["controls"].append(dict(control=name, ok=ok, reason=why))
                print("control:", name, "->", "ACCEPT (BAD)" if ok else "reject", "|", why[:110], flush=True)
        for s in ok_seeds:
            r = sound_test(snap(load(task, rec, s, "T.json"), G0), task, G0, s)
            if r: out["sound_test"]["%s-%d" % (task, s)] = r
        st = [v for k, v in out["sound_test"].items() if k.startswith(task)]
        print(task, "numeric soundness test:", len(st), "networks,", sum(v["positions"] for v in st), "positions,", sum(v["violations"] for v in st),
              "violations, smallest slack %.5f" % min([v["smallest_slack"] for v in st] + [9]), flush=True)
    out["secs"] = round(time.time() - t0, 1)
    json.dump(out, open(os.path.join(HERE, "results", "rung8-k1.json"), "w"), indent=1)
    print("done in %.0f s" % out["secs"])
