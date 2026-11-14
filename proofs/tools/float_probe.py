"""Post hoc (not pre-registered): where does a float32 forward pass of the proved rung-2
nets start to give wrong answers? 20 random inputs per length, lengths 300..4000.

    python tools/float_probe.py     -> results/rung2-float-probe.json
"""
import json, os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import train_seq_twin as T
import collect2_lib as CL

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
pool = {c["id"]: c for c in json.load(open(os.path.join(HERE, "pool", "rung2_pool.json")))}
draw = json.load(open(os.path.join(HERE, "pool", "draw2.json")))
pf64 = T.posfeat
out = {}
for cid in draw["rung2_test"]:
    c = pool[cid]
    net = CL.load_net(os.path.join(HERE, "runs", "rung2-test", "net", cid, "net.json"))
    P, shape = CL.float_params(net)
    res = {}
    for L in (300, 1000, 2000, 4000):
        rng = np.random.default_rng(L)
        wrong = {"float32": 0, "float64": 0}
        for _ in range(20):
            w = T.sample(c, L, rng)
            y = T.target(c, w)
            for name, dt in (("float32", np.float32), ("float64", np.float64)):
                T.posfeat = lambda n, dt=dt: pf64(n).astype(dt)
                Pd = {k: v.astype(dt) for k, v in P.items()}
                o = T.forward(Pd, shape, np.array([[0] + w]), hard=True)[0][0]
                if c["family"] in ("parity", "dyck"):
                    wrong[name] += int((o[-1] > 0) != (y > 0))
                else:
                    wrong[name] += int(np.any(np.abs(o[1:] - np.array(y)) >= 0.5))
        res[L] = wrong
    T.posfeat = pf64
    out[cid] = res
    print(cid, c["family"], res, flush=True)
json.dump(out, open(os.path.join(HERE, "results", "rung2-float-probe.json"), "w"), indent=1)
