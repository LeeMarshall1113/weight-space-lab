"""Rung-3 design calibration (not a result): how much can the rung-1 doctor nets move
when every weight and bias is perturbed by at most tau?

    python tools/r3_calibrate.py

For each rung-1 test net: a sound interval bound on the output change (layer by layer),
the largest change seen with random sign perturbations, and both as a fraction of the
spec's sampled output range.
"""
import glob, json, os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.argv = [sys.argv[0]]
import importlib.util
spec = importlib.util.spec_from_file_location("collect_mod", os.path.join(os.path.dirname(os.path.abspath(__file__)), "collect.py"))
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
src = open(os.path.join(HERE, "tools", "collect.py"), encoding="utf-8").read().split("def case_result")[0]
ns = {"__file__": os.path.join(HERE, "tools", "collect.py"), "__name__": "collect_head"}
exec(compile(src, "collect_head", "exec"), ns)
parse_net = ns["parse_net"]

pool = {s["id"]: s for s in json.load(open(os.path.join(HERE, "pool", "rung1_pool.json")))}
rng_info = {r["id"]: r for r in json.load(open(os.path.join(HERE, "results", "twin-eps-range.json")))}
TAUS = (1e-4, 1e-3, 1e-2)
rows = []
for d in sorted(glob.glob(os.path.join(HERE, "runs", "rung1-test", "net", "*"))):
    sid = os.path.basename(d)
    passed = [p for p in sorted(glob.glob(os.path.join(d, "attempts", "*.json"))) if json.load(open(p, encoding="utf-8")).get("pass")]
    net = parse_net(open(passed[0][:-5] + ".lean", encoding="utf-8").read())
    Ws = [np.array(W, float).reshape(len(b), -1) for W, b in net]
    bs = [np.array(b, float) for W, b in net]
    box = pool[sid]["box"]
    lo, hi = np.array([b[0] for b in box], float), np.array([b[1] for b in box], float)
    # sound bound on |h| per layer by interval arithmetic
    l, u = lo, hi
    Bs = [np.maximum(np.abs(l), np.abs(u))]
    for i, (W, b) in enumerate(zip(Ws, bs)):
        Wp, Wn = np.maximum(W, 0), np.minimum(W, 0)
        l2, u2 = Wp @ l + Wn @ u + b, Wp @ u + Wn @ l + b
        if i < len(Ws) - 1:
            l2, u2 = np.maximum(l2, 0), np.maximum(u2, 0)
        l, u = l2, u2
        Bs.append(np.maximum(np.abs(l), np.abs(u)))
    r = {"id": sid, "layers": len(Ws) - 1, "units": int(sum(len(b) for b in bs[:-1])), "range": rng_info[sid]["range_sampled"]}
    g = np.random.default_rng(0)
    X = g.uniform(lo, hi, (400, len(box)))
    def fwd(Ws_, bs_):
        h = X
        for i, (W, b) in enumerate(zip(Ws_, bs_)):
            h = h @ W.T + b
            if i < len(Ws_) - 1:
                h = np.maximum(h, 0)
        return h[:, 0]
    base = fwd(Ws, bs)
    for tau in TAUS:
        e = np.zeros(len(box))
        for i, W in enumerate(Ws):
            e = np.abs(W) @ e + tau * (np.sum(Bs[i] + e) + 1.0)
        worst = 0.0
        for _ in range(300):
            Wp_ = [W + tau * g.choice([-1.0, 1.0], W.shape) for W in Ws]
            bp_ = [b + tau * g.choice([-1.0, 1.0], b.shape) for b in bs]
            worst = max(worst, float(np.max(np.abs(fwd(Wp_, bp_) - base))))
        r["bound_%g" % tau] = float(e[0]); r["seen_%g" % tau] = worst
    rows.append(r)
print("id    L  units  range | tau=1e-4: bound seen | tau=1e-3: bound seen (bound/range) | tau=1e-2: bound seen")
for r in sorted(rows, key=lambda r: r["bound_0.001"] / r["range"]):
    print("%-5s %d  %3d  %6.2f | %7.4f %7.4f | %7.3f %7.3f (%5.1f%%) | %7.2f %7.2f" % (
        r["id"], r["layers"], r["units"], r["range"], r["bound_0.0001"], r["seen_0.0001"],
        r["bound_0.001"], r["seen_0.001"], 100 * r["bound_0.001"] / r["range"], r["bound_0.01"], r["seen_0.01"]))
json.dump(rows, open(os.path.join(HERE, "results", "r3-calibration.json"), "w"), indent=1)
