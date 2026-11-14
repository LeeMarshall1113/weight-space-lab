"""Collect per-case results from attempt logs.

    python tools/collect.py runs/rung0 [runs/rung1-test ...]

Writes results/<rung>.json and prints a table. For passing nets it also parses
the weights and measures the float32 gap on 10,000 random box points (PREREG).
"""
import glob, json, os, random, re, sys
from fractions import Fraction as F
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import specpool as SP

HERE = SP.HERE


def strip(s):
    s = re.sub(r"/-.*?-/", " ", s, flags=re.S)
    return re.sub(r"--.*", " ", s)


def parse_net(src, name="net"):
    """All `W := [...], b := [...]` layer literals in file order (hidden layers first, output
    last). Doctors often name layers in separate defs, so this is a heuristic: the caller
    cross-checks it by exact evaluation against the spec (exact_mismatches_10k must be 0)."""
    s = strip(src)
    layers = re.findall(r"W\s*:=\s*(\[(?:[^\[\]]|\[[^\[\]]*\])*\])\s*,\s*b\s*:=\s*(\[[^\[\]]*\])", s)
    if not layers:
        return None
    q = lambda t: F("".join(t.replace("(", "").replace(")", "").split()))
    net = []
    try:
        for W, b in layers:
            rows = re.findall(r"\[([^\[\]]*)\]", W[1:-1])
            net.append(([[q(t) for t in r.split(",") if t.strip()] for r in rows],
                        [q(t) for t in b[1:-1].split(",") if t.strip()]))
    except Exception:
        return None
    return net if len(net[-1][1]) == 1 else None


def eval_exact(net, x):
    h = x
    for i, (W, b) in enumerate(net):
        h = [sum(w * a for w, a in zip(row, h)) + c for row, c in zip(W, b)]
        if i < len(net) - 1:
            h = [max(a, F(0)) for a in h]
    return h[0]


def float_gap(net, e, box, n=10000, seed=7):
    rng = random.Random(seed)
    Ws = [(np.array([[float(v) for v in r] for r in W], np.float32), np.array([float(v) for v in b], np.float32)) for W, b in net]
    worst, exact_bad = 0.0, 0
    for _ in range(n):
        # random float32 inputs (not dyadic grid points), taken as exact rationals for the spec
        x = [F(float(np.float32(rng.uniform(lo, hi)))) for lo, hi in box]
        want = SP.ev(e, x)
        if eval_exact(net, x) != want:
            exact_bad += 1
        h = np.array([float(v) for v in x], np.float32)
        for i, (W, b) in enumerate(Ws):
            h = W @ h + b
            if i < len(Ws) - 1:
                h = np.maximum(h, np.float32(0))
        worst = max(worst, abs(float(h[0]) - float(want)))
    return worst, exact_bad


def case_result(d, pool):
    meta = json.load(open(os.path.join(d, "case.json"), encoding="utf-8"))
    atts = [json.load(open(p, encoding="utf-8")) for p in sorted(glob.glob(os.path.join(d, "attempts", "*.json")))]
    r = {"id": meta["id"], "arm": meta["arm"], "submissions": len(atts), "pass": any(a.get("pass") for a in atts),
         "lean_secs": round(sum(a.get("secs", 0) or 0 for a in atts), 1),
         "native_decide_attempts": sum(bool(a.get("native_decide_attempted")) for a in atts),
         "banned_rejections": sum(str(a.get("reason", "")).startswith("banned") for a in atts),
         "timeouts": sum(bool(a.get("timed_out")) for a in atts),
         "max_peak_commit_gb": max([a.get("peak_commit_gb") or 0 for a in atts] or [0])}
    if "eps" in meta:
        r["eps"] = meta["eps"]
    if r["pass"]:
        k = [i for i, a in enumerate(atts) if a.get("pass")][0]
        src = open(sorted(glob.glob(os.path.join(d, "attempts", "*.lean")))[k], encoding="utf-8").read()
        r["pass_at"] = k + 1
        r["solution_lines"] = len([l for l in strip(src).splitlines() if l.strip()])
        if meta["arm"] == "net":
            net = parse_net(src)
            if net is None:
                r["net_parse"] = "not a plain literal"
            else:
                r["hidden_layers"] = len(net) - 1
                r["hidden_units"] = sum(len(b) for _, b in net[:-1])
                r["nonzero_weights"] = sum(v != 0 for W, b in net for row in W for v in row) + sum(v != 0 for _, b in net for v in b)
                if meta.get("rung") == 1 and meta["id"] in pool:
                    s = pool[meta["id"]]
                    gap, bad = float_gap(net, SP.from_json(s["expr"]), [tuple(b) for b in s["box"]])
                    r["float32_max_dev"] = gap
                    r["exact_mismatches_10k"] = bad
    return r


if __name__ == "__main__":
    pool = {s["id"]: s for s in json.load(open(os.path.join(HERE, "pool", "rung1_pool.json")))}
    for root in sys.argv[1:]:
        rows = [case_result(os.path.dirname(p), pool) for p in sorted(glob.glob(os.path.join(root, "*", "*", "case.json")))]
        out = os.path.join(HERE, "results", os.path.basename(os.path.normpath(root)) + ".json")
        os.makedirs(os.path.dirname(out), exist_ok=True)
        json.dump(rows, open(out, "w"), indent=1)
        for arm in sorted({r["arm"] for r in rows}):
            a = [r for r in rows if r["arm"] == arm]
            subs = sorted(r["submissions"] for r in a)
            print("%s %s: %d/%d pass, median submissions %s, native_decide attempts %d" % (
                root, arm, sum(r["pass"] for r in a), len(a), subs[len(subs) // 2] if subs else "-",
                sum(r["native_decide_attempts"] for r in a)))
            for r in a:
                print("   ", {k: v for k, v in r.items() if k != "arm"})
