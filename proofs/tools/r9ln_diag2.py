"""Rung 9-LN K2 diagnostics 2 (tuning networks only): radius at each stage of one case."""
import json, os, sys
from fractions import Fraction as F
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(HERE, "tools"))
import r9ln_proto as L, r9_proto as P9
AF, RND, dot_af, relu_af = P9.AF, P9.RND, P9.dot_af, P9.relu_af
mx = lambda xs: max(float(a.dev()) for a in xs)
mr = lambda xs: max(float(a.r) for a in xs)
mg = lambda xs: max(float(a.mag()) for a in xs)
for seed in [int(x) for x in sys.argv[1:]]:
    net = json.load(open(os.path.join(HERE, "runs", "r9ln-tune", "A", "n1", "s%03d" % seed, "W14.json")))
    Q = lambda m: [[F(v) for v in r] for r in m]
    E = Q(net["embed"]); d = len(E[0]); ntok = len(E); delta = F(1, 2 ** 14); e0 = delta + RND; sw = e0
    P1 = P9.parse_block(net["blocks"][0], d)
    LN = {n: ([F(v) for v in net["ln"][n]["g"]], [F(v) for v in net["ln"][n]["b"]]) for n in ("ln1", "ln2", "lnf")}
    oW, oB = [F(v) for v in net["outW"]], F(net["outB"])
    res = lambda t: [AF(E[t][r], None, e0) for r in range(d)]
    boxes = {}
    for t in range(ntok):
        hs, _ = L.ln_af(res(t), *LN["ln1"], delta, "LN1")
        boxes[t] = ([a.c for a in hs], [a.dev() for a in hs])
    heads = [P9.head_tables(1, k, h, boxes, list(range(1, ntok)), delta, d) for k, h in enumerate(P1["heads"])]
    t = 1; sel = ((0,), (1, 0))
    y = res(t)
    print("seed %d | case token 1 keys %s | residual x: dev %.5f mag %.3f" % (seed, sel, mx(y), mg(y)))
    for hd, keys in zip(heads, sel):
        ho, desc = P9.head_out(hd, t, keys, delta, d)
        print("   head %d: output dev %.5f (radius part %.5f) mag %.3f | weights of other keys <= %s | VE err max %.5f | soft %.5f | tail %.2e" % (
            hd["k"], mx(ho), mr(ho), mg(ho), ["%.2e" % a for a in desc], max(float(e) for k in keys for _, e in hd["VE"][k]), max(float(s) for s in hd["soft"]), float(hd["tail"])))
        y = [a.add(b_) for a, b_ in zip(y, ho)]
    print("   y (before LN2): dev %.5f mag %.3f" % (mx(y), mg(y)))
    y2, v2 = L.ln_af(y, *LN["ln2"], delta, "LN2")
    print("   LN2: variance in [%.5f, %.5f] (sigma %.4f) | output dev %.5f mag %.3f" % (v2[0], v2[1], v2[0] ** 0.5, mx(y2), mg(y2)))
    hid, cross = [], 0
    for hh in range(P1["H"]):
        p = dot_af(P1["W1"][hh], y2, delta); p.c += P1["b1"][hh]; p.r += sw + RND
        cross += int(p.lo() < 0 < p.hi())
        hid.append(relu_af(p, None))
    print("   hidden: dev %.5f | units straddling zero %d of %d | pre-activations nearest zero %s" % (mx(hid), cross, P1["H"], sorted(round(float(abs(h_.c)), 3) for h_ in hid)[:4]))
    z = []
    for r in range(d):
        c2 = dot_af(P1["W2"][r], hid, delta); c2.c += P1["b2"][r]; c2.r += sw + RND
        z.append(y[r].add(c2))
    print("   z (before LNf): dev %.5f mag %.3f" % (mx(z), mg(z)))
    zf, vf = L.ln_af(z, *LN["lnf"], delta, "LNf")
    print("   LNf: variance in [%.5f, %.5f] (sigma %.4f) | output dev %.5f" % (vf[0], vf[1], vf[0] ** 0.5, mx(zf)))
    o = dot_af(oW, zf, delta); o.c += oB
    print("   read-out: %.4f +- %.4f | |oW| sum %.2f" % (float(o.c), float(o.dev()), float(sum(abs(v) for v in oW))))
