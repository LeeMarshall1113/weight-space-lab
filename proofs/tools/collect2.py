"""Rung-2 results from attempt logs (and net.json exports, if present).

    python tools/collect2.py [runs/rung2-test]   -> results/rung2-test.json + table

Per case and arm: submissions, pass, Lean seconds, solution lines, native_decide attempts,
banned rejections, timeouts, memory kills. For exported nets: blocks, heads, state width,
an exact re-test against the task on random inputs (independent of the proof), and the
float32 gap on random inputs of length up to 100.
"""
import glob, json, os, random, statistics as st, sys
from fractions import Fraction as F
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import seqnet as SN
import train_seq_twin as T

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
root = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "runs", "rung2-test"))
pool = {c["id"]: c for c in json.load(open(os.path.join(HERE, "pool", "rung2_pool.json")))}


def q(s):
    return F(s)


def load_net(path):
    j = json.load(open(path))
    M = lambda m: [[q(x) for x in r] for r in m]
    return {"embed": M(j["embed"]), "outW": [q(x) for x in j["outW"]], "outB": q(j["outB"]),
            "blocks": [{"heads": [{"A": M(h["A"]), "V": M(h["V"]), "mask": h["mask"]} for h in b["heads"]],
                        "W1": M(b["W1"]), "b1": [q(x) for x in b["b1"]], "W2": M(b["W2"]),
                        "b2": [q(x) for x in b["b2"]]} for b in j["blocks"]]}


def correct(c, w, out):
    y = T.target(c, w)
    if c["family"] in ("parity", "dyck"):
        return (out[-1] > 0) == (y > 0)
    return all(o == t for o, t in zip(out[1:], y))


def float_params(net):
    P = {"E": np.array(net["embed"], np.float32), "outW": np.array(net["outW"], np.float32),
         "outB": np.array([net["outB"]], np.float32)}
    shape = {"de": len(net["embed"][0]), "heads": [], "mlp": [], "masks": []}
    for k, b in enumerate(net["blocks"]):
        shape["heads"].append(len(b["heads"])); shape["mlp"].append(len(b["b1"]))
        shape["masks"].append([h["mask"] for h in b["heads"]])
        for h, hd in enumerate(b["heads"]):
            P["A%d_%d" % (k, h)] = np.array(hd["A"], np.float32)
            P["V%d_%d" % (k, h)] = np.array(hd["V"], np.float32)
        P["W1_%d" % k] = np.array(b["W1"], np.float32).reshape(len(b["b1"]), -1)
        P["b1_%d" % k] = np.array(b["b1"], np.float32)
        P["W2_%d" % k] = np.array(b["W2"], np.float32).reshape(-1, len(b["b1"]))
        P["b2_%d" % k] = np.array(b["b2"], np.float32)
    return P, shape


rows = []
for arm in ("net", "prog"):
    for d in sorted(glob.glob(os.path.join(root, arm, "*"))):
        cid = os.path.basename(d)
        c = pool[cid]
        r = {"id": cid, "arm": arm, "family": c["family"], "submissions": 0, "pass": False, "lean_secs": 0.0,
             "native_decide_attempts": 0, "banned_rejections": 0, "timeouts": 0, "mem_kills": 0}
        for p in sorted(glob.glob(os.path.join(d, "attempts", "*.json"))):
            a = json.load(open(p, encoding="utf-8"))
            if a.get("pending"):
                continue
            r["submissions"] += 1
            r["lean_secs"] += a.get("secs", 0) or 0
            r["native_decide_attempts"] += bool(a.get("native_decide_attempted"))
            r["banned_rejections"] += str(a.get("reason", "")).startswith("banned")
            r["timeouts"] += bool(a.get("timed_out"))
            r["mem_kills"] += bool(a.get("mem_killed"))
            if a.get("pass") and not r["pass"]:
                r["pass"] = True
                r["solution_lines"] = len(open(p[:-5] + ".lean", encoding="utf-8").read().splitlines())
        r["lean_secs"] = round(r["lean_secs"], 1)
        nj = os.path.join(d, "net.json")
        if arm == "net" and os.path.exists(nj):
            net = load_net(nj)
            r.update(blocks=len(net["blocks"]), heads=sum(len(b["heads"]) for b in net["blocks"]),
                     width=len(net["outW"]), shape_ok=SN.shape_ok(net, c["V"]))
            rng = random.Random(99)
            bad = 0
            lens = [1, 2, 3, 4, 5, 6, 7, 8, 12, 20, 30]
            for k in range(110):
                w = [rng.randint(1, c["V"]) for _ in range(lens[k % len(lens)])]
                if c["family"] == "dyck" and k % 2:
                    w = T.sample(c, len(w), np.random.default_rng(k))
                bad += not correct(c, w, SN.run(net, w))
            r["exact_retest_wrong_of_110"] = bad
            P, shape = float_params(net)
            pf64 = T.posfeat
            T.posfeat = lambda n: pf64(n).astype(np.float32)   # make the whole pass float32
            nrng = np.random.default_rng(7)
            wrong, worst = 0, 0.0
            for k in range(1000):
                L = int(nrng.integers(1, 101))
                w = T.sample(c, L, nrng)
                out = T.forward(P, shape, np.array([[0] + w]), hard=True)[0][0]
                assert out.dtype == np.float32
                y = T.target(c, w)
                if c["family"] in ("parity", "dyck"):
                    wrong += (out[-1] > 0) != (y > 0)
                else:
                    wrong += bool(np.any(np.abs(out[1:] - np.array(y)) >= 0.5))
                    worst = max(worst, float(np.max(np.abs(out[1:] - np.array(y)))))
            T.posfeat = pf64
            r["float32_wrong_of_1000"] = int(wrong)
            r["float32_max_dev_seq"] = worst
        rows.append(r)

os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
json.dump(rows, open(os.path.join(HERE, "results", os.path.basename(root) + ".json"), "w"), indent=1)
for arm in ("net", "prog"):
    rs = [r for r in rows if r["arm"] == arm]
    done = [r for r in rs if r["submissions"]]
    if not done:
        continue
    subs = sorted(r["submissions"] for r in done)
    print("%s: %d/%d pass | submissions %s median %s | lean s median %s | native_decide %d, banned %d, timeouts %d, mem kills %d" % (
        arm, sum(r["pass"] for r in rs), len(rs), subs, st.median(subs), st.median(r["lean_secs"] for r in done),
        sum(r["native_decide_attempts"] for r in done), sum(r["banned_rejections"] for r in done),
        sum(r["timeouts"] for r in done), sum(r["mem_kills"] for r in done)))
    for r in rs:
        print("   ", {k: v for k, v in r.items() if k != "arm"})
