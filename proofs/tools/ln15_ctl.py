"""Rung 9-LN15 controls (PREREG_R9LN15.md): altered copies of one tuning network's skeleton W14.
    python tools/ln15_ctl.py <seed>      -> runs/r9ln15-ctl/<name>/{W14.json,train.json}
Text work only. Each control is then given to tools/make_r9ln15_net.py (--no-trained) and must be rejected."""
import copy, json, os, sys
from fractions import Fraction as F
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
seed = int(sys.argv[1])
src = os.path.join(HERE, "runs", "r9ln-tune", "A", "n1", "s%03d" % seed)
W = json.load(open(os.path.join(src, "W14.json"))); tj = json.load(open(os.path.join(src, "train.json")))
fr = lambda v: "%d/%d" % F(v).as_integer_ratio()
neg = lambda v: fr(-F(v))
V = {}
a = copy.deepcopy(W); a["embed"][1], a["embed"][2] = a["embed"][2], a["embed"][1]; V["swap12"] = a
a = copy.deepcopy(W); a["outW"] = [neg(v) for v in a["outW"]]; a["outB"] = neg(a["outB"]); V["negout"] = a
a = copy.deepcopy(W); a["outB"] = fr(F(a["outB"]) + F(1, 2)); V["bias_half"] = a
a = copy.deepcopy(W); a["ln"]["ln2"]["g"] = [neg(v) for v in a["ln"]["ln2"]["g"]]; V["ln2neg"] = a
V["rad16"] = copy.deepcopy(W); V["rad64"] = copy.deepcopy(W)
for name, net in V.items():
    d = os.path.join(HERE, "runs", "r9ln15-ctl", name)
    os.makedirs(d, exist_ok=True)
    json.dump(net, open(os.path.join(d, "W14.json"), "w")); json.dump(tj, open(os.path.join(d, "train.json"), "w"))
    print("wrote", name)
