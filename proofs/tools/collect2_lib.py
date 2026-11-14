"""Helpers shared by collect2.py and float_probe.py."""
import json
from fractions import Fraction as F
import numpy as np
import train_seq_twin as T


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


