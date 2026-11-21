"""Rung 8 controls 2 to 4 (PREREG_R8.md, Controls): altered copies of a skeleton, written as JSON for
tools/make_r8_net.py --net <absolute path>.

    python tools/r8_ctl.py <run dir> [--net W14.json]   -> runs/r8-ctl/<task>-<recipe>-s<seed>/{swap12,negout,bias_half}.json

swap12: embedding rows 1 and 2 swapped; negout: read-out weights negated; bias_half: read-out bias + 1/2.
Exact rationals; no numerics beyond that.
"""
import copy, json, os, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
d = os.path.abspath(sys.argv[1])
netf = sys.argv[sys.argv.index("--net") + 1] if "--net" in sys.argv else "W14.json"
tj = json.load(open(os.path.join(d, "train.json")))
W = json.load(open(os.path.join(d, netf)))
out = os.path.join(HERE, "runs", "r8-ctl", "%s-%s-s%d" % (tj["task"], tj["recipe"], tj["seed"]))
os.makedirs(out, exist_ok=True)


def fmt(x, like):
    return str(x) if isinstance(like, str) else float(x)


a = copy.deepcopy(W); a["embed"][1], a["embed"][2] = a["embed"][2], a["embed"][1]
b = copy.deepcopy(W); b["outW"] = [fmt(-F(v), v) for v in W["outW"]]
c = copy.deepcopy(W); c["outB"] = fmt(F(W["outB"]) + F(1, 2), W["outB"])
for name, net in (("swap12", a), ("negout", b), ("bias_half", c)):
    json.dump(net, open(os.path.join(out, name + ".json"), "w"))
    print("wrote", os.path.relpath(os.path.join(out, name + ".json"), HERE).replace(os.sep, "/"))
