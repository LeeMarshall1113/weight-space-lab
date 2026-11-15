"""The 2x2 of writeup/NOTE_2x2_prestated.md: rung-2 and rung-4 proved transformers under
absolute (zeros included) and relative (zeros fixed) weight perturbations. Float64.

    python tools/r3_2x2.py      -> results/r3-2x2.json
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "2"); os.environ.setdefault("OPENBLAS_NUM_THREADS", "2")
import copy, glob, json, sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import train_seq_twin as T
import collect2_lib as CL
import r4net as R4, r4pool as P4, r4_checks as C4

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ABS, REL = 1e-3, 1 / 200
LENS, LONG = [2, 3, 5, 8, 13, 20], [100, 1000]
OUT = os.path.join(HERE, "results", "r3-2x2.json")


def screens(entries, get, put, wrong_short, wrong_long, kind, rng):
    """entries: list of handles; get/put read and write one entry of the live parameters."""
    size = ABS if kind == "abs" else REL
    move = (lambda b, s: b + s * size) if kind == "abs" else (lambda b, s: b * (1 + s * size))
    live = [e for e in entries if kind == "abs" or get(e) != 0]
    single, example = 0, None
    for e in live:
        b = get(e)
        for s in (1.0, -1.0):
            put(e, move(b, s))
            bad = wrong_short()
            put(e, b)
            if bad:
                single += 1
                example = example or (str(e), s)
                break
    base = [get(e) for e in live]

    def corners(n, wrong):
        hits = 0
        for _ in range(n):
            for e, b in zip(live, base):
                put(e, move(b, rng.choice([-1.0, 1.0])))
            hits += bool(wrong())
        for e, b in zip(live, base):
            put(e, b)
        return hits
    return {"entries_moved": len(live), "single_entry_breaks": single, "single_example": example,
            "all_entries_short_breaks_of_200": corners(200, wrong_short),
            "all_entries_long_breaks_of_50": corners(50, wrong_long)}


rows = []
# ------------------------------------------------------------------ rung-2 networks
pool2 = {c["id"]: c for c in json.load(open(os.path.join(HERE, "pool", "rung2_pool.json")))}
for d in sorted(glob.glob(os.path.join(HERE, "runs", "rung2-test", "net", "*"))):
    cid = os.path.basename(d); c = pool2[cid]
    net = CL.load_net(os.path.join(d, "net.json"))
    P32, shape = CL.float_params(net)
    Pm = {k: np.array(v, dtype=float) for k, v in P32.items()}
    rng = np.random.default_rng(5)

    def mk(lengths, per):
        out = []
        for L in lengths:
            ws = [T.sample(c, L, rng) for _ in range(per)]
            out.append((np.array([[0] + w for w in ws]), np.array([T.target(c, w) for w in ws])))
        return out
    short, long_ = mk(LENS, 8), mk(LONG, 2)

    def wrong(batches):
        for toks, ys in batches:
            out = T.forward(Pm, shape, toks, hard=True)[0]
            if c["family"] in ("parity", "dyck"):
                if np.any((out[:, -1] > 0) != (ys > 0)):
                    return True
            elif np.any(np.abs(out[:, 1:] - ys) >= 0.5):
                return True
        return False
    r = {"set": "rung2", "id": cid, "family": c["family"],
         "clean_ok_short": not wrong(short), "clean_ok_long": not wrong(long_)}
    entries = [(k, idx) for k in sorted(Pm) for idx in np.ndindex(Pm[k].shape)]
    t0 = time.time()
    for kind in ("abs", "rel"):
        r[kind] = screens(entries, lambda e: float(Pm[e[0]][e[1]]), lambda e, v: Pm[e[0]].__setitem__(e[1], v),
                          lambda: wrong(short), lambda: wrong(long_), kind, np.random.default_rng(11))
    r["secs"] = round(time.time() - t0, 1)
    rows.append(r); json.dump(rows, open(OUT, "w"), indent=1)
    print("rung2", cid, c["family"], "clean", r["clean_ok_short"], r["clean_ok_long"], "| ABS", r["abs"], "| REL", r["rel"], flush=True)

# ------------------------------------------------------------------ rung-4 networks
pool4 = {c["id"]: c for c in json.load(open(os.path.join(HERE, "pool", "rung4_pool.json")))}
for d in sorted(glob.glob(os.path.join(HERE, "runs", "rung4-test", "net", "*"))):
    if not os.path.exists(os.path.join(d, "net.json")):
        continue
    cid = os.path.basename(d); c = pool4[cid]
    net = C4.load_net(os.path.join(d, "net.json"))
    net = {"embed": np.array(net["embed"], float), "outW": np.array(net["outW"], float), "outB": np.array(net["outB"], float),
           "blocks": [{"heads": [{"A": np.array(h["A"], float), "V": np.array(h["V"], float), "mask": h["mask"]} for h in B["heads"]],
                       "W1": np.array(B["W1"], float).reshape(len(B["b1"]), len(net["outW"])), "b1": np.array(B["b1"], float),
                       "W2": np.array(B["W2"], float).reshape(len(net["outW"]), len(B["b1"])), "b2": np.array(B["b2"], float)}
                      for B in net["blocks"]]}
    rng = np.random.default_rng(5)
    mk = lambda lengths, per: [rng.integers(1, c["V"] + 1, L) for L in lengths for _ in range(per)]
    short, long_ = mk(LENS, 8), mk(LONG, 2)
    tol = [0.5]

    def wrong(ws):
        for w in ws:
            y = R4.run(net, w, None, np.float64)
            if np.any(np.abs(y - np.array(P4.target(c, [int(t) for t in w]), float)) >= tol[0]):
                return True
        return False
    arrs = [("E", net["embed"]), ("outW", net["outW"])] + \
        [(n_ + str(b) + "_" + str(k), h[n_]) for b, B in enumerate(net["blocks"]) for k, h in enumerate(B["heads"]) for n_ in ("A", "V")] + \
        [(n_ + str(b), B[n_]) for b, B in enumerate(net["blocks"]) for n_ in ("W1", "b1", "W2", "b2")]
    amap = dict(arrs)
    entries = [(k, idx) for k, a in arrs for idx in np.ndindex(a.shape)]
    r = {"set": "rung4", "id": cid, "family": c["family"], "clean_ok_short": not wrong(short), "clean_ok_long": not wrong(long_)}
    t0 = time.time()
    for kind in ("abs", "rel"):
        for name, t in (("", 0.5), ("_tol_quarter", 0.25 + 1e-12)):
            tol[0] = t
            r[kind + name] = screens(entries, lambda e: float(amap[e[0]][e[1]]), lambda e, v: amap[e[0]].__setitem__(e[1], v),
                                     lambda: wrong(short), lambda: wrong(long_), kind, np.random.default_rng(11))
    r["secs"] = round(time.time() - t0, 1)
    rows.append(r); json.dump(rows, open(OUT, "w"), indent=1)
    print("rung4", cid, c["family"], "clean", r["clean_ok_short"], r["clean_ok_long"], "| ABS", r["abs"], "| REL", r["rel"], flush=True)
print("done")
