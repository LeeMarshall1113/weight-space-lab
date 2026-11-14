"""Rung-3 Part B1 (PREREG_R3.md): do the proved rung-2 transformers survive a single-weight
perturbation of size <= tau = 1/1000 at lengths <= 20?

    python tools/r3_transformers.py        -> results/r3-transformers.json

Screen in float64 (hard attention): every weight entry, both signs, at size tau; the
entries that break are re-tried at tau/10, tau/100, tau/1000. One witness per net at tau
and one at the smallest breaking size are confirmed with the exact rational evaluator.
"Wrong": classification = wrong sign at the last position; sequence = some output is at
least 1/2 away from the target (exact equality cannot survive any perturbation, so the
lenient rounding rule is used). Inputs: 8 per length at lengths 2, 3, 5, 8, 13, 20.
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "2"); os.environ.setdefault("OPENBLAS_NUM_THREADS", "2")
import glob, json, sys, time
from fractions import Fraction as F
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import seqnet as SN
import train_seq_twin as T
import collect2_lib as CL

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
pool = {c["id"]: c for c in json.load(open(os.path.join(HERE, "pool", "rung2_pool.json")))}
TAU = 1e-3
LENS = [2, 3, 5, 8, 13, 20]


def wrong_float(c, P, shape, batches):
    for toks, ys in batches:
        out = T.forward(P, shape, toks, hard=True)[0]
        if c["family"] in ("parity", "dyck"):
            if np.any((out[:, -1] > 0) != (ys > 0)):
                return True
        elif np.any(np.abs(out[:, 1:] - ys) >= 0.5):
            return True
    return False


def wrong_exact(c, net, w):
    out = SN.run(net, w)
    y = T.target(c, w)
    if c["family"] in ("parity", "dyck"):
        return (out[-1] > 0) != (y > 0)
    return any(abs(o - t) >= F(1, 2) for o, t in zip(out[1:], y))


def exact_entry(net, key, idx):
    """Return (container, index) in the exact net for float param `key` at flat index idx."""
    if key == "E":
        M = net["embed"]; return M[idx[0]], idx[1]
    if key == "outW":
        return net["outW"], idx[0]
    if key == "outB":
        return None, None
    name, k = key.rsplit("_", 1) if key[0] in "Wb" else (key, None)
    if key[0] in "AV":
        kk, h = key[1:].split("_")
        M = net["blocks"][int(kk)]["heads"][int(h)][key[0]]; return M[idx[0]], idx[1]
    B = net["blocks"][int(k)]
    if name in ("W1", "W2"):
        return B[name][idx[0]], idx[1]
    return B[name], idx[0]


rows = []
for d in sorted(glob.glob(os.path.join(HERE, "runs", "rung2-test", "net", "*"))):
    cid = os.path.basename(d); c = pool[cid]
    net = CL.load_net(os.path.join(d, "net.json"))
    P32, shape = CL.float_params(net)
    P = {k: np.array(v, dtype=float) for k, v in P32.items()}
    for k in list(P):          # float64 straight from the exact values, not through float32
        pass
    rng = np.random.default_rng(5)
    batches, words = [], []
    for L in LENS:
        ws = [T.sample(c, L, rng) for _ in range(8)]
        words += ws
        ys = np.array([T.target(c, w) for w in ws])
        batches.append((np.array([[0] + w for w in ws]), ys))
    assert not wrong_float(c, P, shape, batches), cid
    t0 = time.time()
    total, breaking = 0, []
    for key in sorted(P):
        it = np.nditer(P[key], flags=["multi_index"])
        for _ in it:
            idx = it.multi_index; total += 1
            base = P[key][idx]
            for sgn in (1.0, -1.0):
                P[key][idx] = base + sgn * TAU
                bad = wrong_float(c, P, shape, batches)
                P[key][idx] = base
                if bad:
                    breaking.append((key, idx, sgn)); break
    groups = {}
    for key, idx, sgn in breaking:
        g = "attention score (A)" if key[0] == "A" else "attention value (V)" if key[0] == "V" else "embedding" if key == "E" else "MLP" if key[0] in "Wb" else "read-out"
        groups[g] = groups.get(g, 0) + 1
    # smaller sizes on the breaking entries
    smallest, wit_small = TAU, None
    for scale in (0.1, 0.01, 0.001):
        found = None
        for key, idx, sgn in breaking:
            base = P[key][idx]
            for s2 in (sgn, -sgn):
                P[key][idx] = base + s2 * TAU * scale
                bad = wrong_float(c, P, shape, batches)
                P[key][idx] = base
                if bad:
                    found = (key, idx, s2); break
            if found:
                break
        if not found:
            break
        smallest, wit_small = TAU * scale, found

    def confirm(wit, size):
        if wit is None or wit[0] == "outB":
            return None
        cont, j = exact_entry(net, wit[0], wit[1])
        old = cont[j]
        cont[j] = old + F(int(wit[2])) * F(size).limit_denominator(10 ** 9)
        hit = next((w for w in words if wrong_exact(c, net, w)), None)
        cont[j] = old
        return {"param": wit[0], "index": list(map(int, wit[1])), "sign": int(wit[2]), "size": size,
                "exact_confirmed": hit is not None, "input": hit}
    r = {"id": cid, "family": c["family"], "weights": total, "single_weight_breaks_at_tau": len(breaking),
         "by_group": groups, "smallest_breaking_size_tried": smallest if breaking else None,
         "witness_tau": confirm(breaking[0], TAU) if breaking else None,
         "witness_smallest": confirm(wit_small, smallest) if wit_small else None, "secs": round(time.time() - t0, 1)}
    rows.append(r)
    json.dump(rows, open(os.path.join(HERE, "results", "r3-transformers.json"), "w"), indent=1)
    print(cid, c["family"], "weights", total, "break at tau:", len(breaking), groups, "| smallest size", r["smallest_breaking_size_tried"],
          "| exact:", (r["witness_tau"] or {}).get("exact_confirmed"), (r["witness_smallest"] or {}).get("exact_confirmed"), "| %ss" % r["secs"], flush=True)
print("nets with at least one breaking single-weight perturbation of size tau: %d / %d" % (sum(1 for r in rows if r["single_weight_breaks_at_tau"]), len(rows)))
