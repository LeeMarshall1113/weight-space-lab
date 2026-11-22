"""Rung 9-LN, K2 prototype, DESIGN 4 = the third and last registered design change (PREREG_R9LN.md):
symbolic tracking of the weight ball. Exact dyadic rationals with outward rounding into the radius.

Every perturbed weight that enters the value path gets its own symbol in [-1, 1] with coefficient delta:
embedding entries, LayerNorm gains and biases, V, W1, b1, W2, b2, oW, oB. Linear operations act exactly on
the symbols, so the final deviation is delta times the 1-norm of the exact first-order sensitivity, plus
remainders. Nonlinear steps:
  weight * value     a*x + delta*eps*x.c exactly; delta * dev(x) to the radius;
  LayerNorm          centring exact; variance linearised around the centre (remainder: products of deviations);
                     1/sqrt linearised with a second-order remainder bound; product of two forms with the
                     product of their deviations as remainder;
  ReLU               exact when the sign is decided, else the rung-8 relaxation;
  attention          scores, windows, weight intervals from boxes as in design 3 (the A matrices are not
                     symbolised); values are forms, combined with the weight symbols.
Rounding charges relative to magnitude, as in design 3. Coefficients are snapped to the 2^-GRID grid with the
difference added to the radius.

    python tools/r9ln_proto4.py tune <recipe> <seed0> <seed1> [--radius r] [--itest] The frozen files are not edited.
"""
import json, math, os, sys, time
from fractions import Fraction as F
import numpy as np

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(HERE, "tools"))
import r9_proto as P9, r7_cert as RC, r9ln_proto as L3

Reject, up, dn, exp_iv = P9.Reject, P9.up, P9.dn, P9.exp_iv
TOL, SMALL, EPS, URel, T0 = P9.TOL, P9.SMALL, L3.EPS, L3.URel, L3.T0
GRID = 56
G2 = 2 ** GRID


def snapq(v):
    q = F(round(v * G2), G2)
    return q, abs(v - q)


class A4:
    """centre + sum coeff * symbol + [-r, r]"""
    __slots__ = ("c", "t", "r")

    def __init__(self, c=F(0), t=None, r=F(0)):
        self.c, self.t, self.r = F(c), (t if t is not None else {}), F(r)

    def copy(self): return A4(self.c, dict(self.t), self.r)

    def add(self, o):
        t = dict(self.t)
        for k, v in o.t.items(): t[k] = t.get(k, 0) + v
        return A4(self.c + o.c, t, self.r + o.r)

    def scale(self, a):
        return A4(self.c * a, {k: v * a for k, v in self.t.items()}, self.r * abs(a))

    def lin(self): return sum(abs(v) for v in self.t.values())
    def dev(self): return self.lin() + self.r
    def lo(self): return self.c - self.dev()
    def hi(self): return self.c + self.dev()
    def mag(self): return abs(self.c) + self.dev()

    def snap(self):
        e = F(0)
        self.c, d = snapq(self.c); e += d
        for k in list(self.t):
            self.t[k], d = snapq(self.t[k]); e += d
            if self.t[k] == 0: del self.t[k]
        self.r = F(-((-(self.r + e) * G2).__floor__()), G2)
        return self


def wdot(names, row, xs, delta):
    """stored row (weights a_i with symbols names[i], radius delta) applied to forms xs"""
    out = A4()
    for nm, a, x in zip(names, row, xs):
        out = out.add(x.scale(a))
        if delta: out.t[nm] = out.t.get(nm, 0) + delta * x.c
    mags = [x.mag() for x in xs]
    out.r += delta * sum(x.dev() for x in xs) + (len(row) + 2) * URel * 2 * sum((abs(a) + delta) * m for a, m in zip(row, mags)) + T0
    return out.snap()


def wbias(o, name, b, delta):
    o.c += b
    if delta: o.t[name] = o.t.get(name, 0) + delta
    o.r += URel * o.mag() + T0
    return o


def mul(a, b):
    """product of two forms; remainder: product of the deviations"""
    out = a.scale(b.c)
    out.r = abs(b.c) * a.r
    for k, v in b.t.items(): out.t[k] = out.t.get(k, 0) + a.c * v
    out.r += abs(a.c) * b.r + a.dev() * b.dev()
    return out


def ln4(xs, lname, g, b, delta, where):
    d = len(xs)
    mx = max(x.mag() for x in xs)
    mean = A4()
    for x in xs: mean = mean.add(x)
    mean = mean.scale(F(1, d)); mean.r += d * URel * mx + T0
    cs = []
    for x in xs:
        c = x.add(mean.scale(-1)); c.r += URel * (x.mag() + mean.mag()) + T0
        cs.append(c.snap())
    # variance, linearised around the centres
    v = A4(sum(c.c * c.c for c in cs) / d + EPS)
    for c in cs:
        for k, t_ in c.t.items(): v.t[k] = v.t.get(k, 0) + 2 * c.c * t_ / d
        v.r += 2 * abs(c.c) * c.r / d + c.dev() * c.dev() / d
    v.r += (d + 3) * URel * (abs(v.c) + v.dev()) + T0
    v.snap()
    dv = v.dev()
    vmin = v.c - dv
    if vmin <= 0: raise Reject(f"{where}: variance not bounded away from zero")
    a_, b_ = L3.sqrt_iv(v.c, v.c)
    g0 = 2 / (a_ + b_)                                   # about v0^(-1/2)
    eg = (b_ - a_) / (a_ * a_) + URel * g0              # its error, and the rounding of sqrt and of the division
    smin, _ = L3.sqrt_iv(vmin, vmin)
    k1 = g0 * g0 * g0 / 2                                 # about |d/dv v^(-1/2)| at v0
    rinv = A4(g0, {k: -k1 * t_ for k, t_ in v.t.items()},
              k1 * v.r + eg + 4 * k1 * (eg / g0) * dv + F(3, 8) * dv * dv / (smin ** 5))
    rinv.snap()
    out = []
    for k, c in enumerate(cs):
        o = mul(c, rinv); o.r += URel * o.mag() + T0
        if o.mag() > SMALL: raise Reject(f"{where}: normalised value fails the magnitude guard")
        o2 = o.scale(g[k])
        if delta: o2.t[(lname, "g", k)] = o2.t.get((lname, "g", k), 0) + delta * o.c
        o2.r += delta * o.dev() + URel * o2.mag() + T0
        out.append(wbias(o2, (lname, "b", k), b[k], delta).snap())
    return out, float(vmin)


def relu4(p):
    lo, hi = p.lo(), p.hi()
    if lo >= 0: return p
    if hi <= 0: return A4()
    lam = dn(hi / (hi - lo), 20)
    mu = max(-lam * lo, (1 - lam) * hi) / 2
    q = p.scale(lam); q.c += mu; q.r += mu
    return q


def head_out4(hd, VA, q, keys, delta, d):
    """tools/r9_proto.py head_out with values as forms VA[token][coord]."""
    if not keys: return [A4() for _ in range(d)], []
    full = len(keys) >= hd["L"] + (1 if hd["mask"] == "causal" else 0)
    nom = [-hd["m"] * rank + hd["S"][q, keys[rank]][0] for rank in range(len(keys))]
    ref = 0
    for i in range(1, len(keys)):
        if nom[i] > nom[ref]: ref = i
    if hd["S"][q, keys[0]][1] + hd["S"][q, keys[ref]][1] + hd["sigma"] + delta * ref > 1:
        raise Reject(f"head {hd['k']}: score radii too large for the reference key")
    c1, r1 = hd["S"][q, keys[ref]]
    w, idx = [], []
    for rank in range(len(keys)):
        if rank == ref: continue
        ck, rk = hd["S"][q, keys[rank]]
        dist = rank - ref
        hi_e = -hd["m"] * dist + delta * abs(dist) + (ck - c1) + rk + r1 + hd["sigma"]
        lo_e = -hd["m"] * dist - delta * abs(dist) + (ck - c1) - rk - r1 - hd["sigma"]
        if hi_e > 6: raise Reject(f"head {hd['k']}: a key outscores the reference by more than e^6")
        w.append([exp_iv(lo_e)[0], exp_iv(hi_e)[1]]); idx.append(rank)
    tl = (hd["tail"] * 3) if full else F(0)
    outs = [VA[keys[ref]][r].copy() for r in range(d)]
    desc = []
    for j, (rlo, rhi) in enumerate(w):
        others_lo = sum(x[0] for i, x in enumerate(w) if i != j)
        others_hi = sum(x[1] for i, x in enumerate(w) if i != j)
        ahi = up(rhi / (1 + rhi + others_lo))
        alo = dn(rlo / (1 + rlo + others_hi + tl))
        mid, rad = (ahi + alo) / 2, (ahi - alo) / 2
        desc.append(float(ahi))
        sym = ("a", hd["k"], j)
        for r in range(d):
            diff = VA[keys[idx[j]]][r].add(VA[keys[ref]][r].scale(-1))
            term = diff.scale(mid)
            term.t[sym] = term.t.get(sym, 0) + rad * diff.c
            term.r += rad * diff.dev()
            outs[r] = outs[r].add(term)
    for r in range(d):
        outs[r].r += 2 * tl * hd["Bv"][r] + hd["soft"][r] + P9.TINY
        outs[r].snap()
    return outs, desc


def check(net, delta, table=None):
    info = {}
    try:
        Q = lambda m: [[F(v) for v in r] for r in m]
        E = Q(net["embed"]); ntok = len(E); d = len(E[0])
        if len(net["blocks"]) != 1: raise Reject("not one block")
        P1 = P9.parse_block(net["blocks"][0], d)
        if [h["mask"] for h in P1["heads"]] != ["strict", "causal"]: raise Reject("heads are not (strict, causal)")
        oW, oB = [F(v) for v in net["outW"]], F(net["outB"])
        LN = {n: ([F(v) for v in net["ln"][n]["g"]], [F(v) for v in net["ln"][n]["b"]]) for n in ("ln1", "ln2", "lnf")}
        if delta < 0 or delta > F(1, 2): raise Reject("radius out of range")
        res = lambda t: [A4(E[t][r], ({("E", t, r): delta} if delta else {}), URel * (abs(E[t][r]) + delta) + T0) for r in range(d)]
        Hs, boxes = {}, {}
        for t in range(ntok):
            Hs[t], _ = ln4(res(t), "ln1", *LN["ln1"], delta, f"LN1 token {t}")
            boxes[t] = ([a.c for a in Hs[t]], [a.dev() for a in Hs[t]])
        info["ln1_radius_max"] = float(max(max(r) for _, r in boxes.values()))
        heads = [L3.head_tables2(k, h, boxes, list(range(1, ntok)), delta, d) for k, h in enumerate(P1["heads"])]
        info["window"] = [hd["L"] for hd in heads]
        VA = [{t: [wdot([("V", k, r, i) for i in range(d)], h["V"][r], Hs[t], delta) for r in range(d)] for t in range(ntok)}
              for k, h in enumerate(P1["heads"])]
        s0, step, outp = RC.task_dfa("A")
        init = (s0, tuple((0,) for _ in heads))
        seen, todo, cache, worst, ncase = {init: 0}, [init], {}, F(0), 0
        while todo:
            s, wins = todo.pop()
            for t in range(1, ntok):
                sel = tuple((((t,) + wn) if hd["mask"] == "causal" else wn) for hd, wn in zip(heads, wins))
                key = (t, sel)
                if key not in cache:
                    y = res(t)
                    for hd, keys in zip(heads, sel):
                        ho, desc = head_out4(hd, VA[hd["k"]], t, keys, delta, d)
                        y = [a.add(b_) for a, b_ in zip(y, ho)]
                        for a in y: a.r += URel * a.mag() + T0
                        if any(a.mag() > SMALL for a in y): raise Reject("residual stream fails the magnitude guard")
                    y2, _ = ln4(y, "ln2", *LN["ln2"], delta, "LN2")
                    hid = []
                    for hh in range(P1["H"]):
                        p = wbias(wdot([("W1", hh, i) for i in range(d)], P1["W1"][hh], y2, delta), ("b1", hh), P1["b1"][hh], delta)
                        hid.append(relu4(p))
                    z = []
                    for r in range(d):
                        c2 = wbias(wdot([("W2", r, i) for i in range(P1["H"])], P1["W2"][r], hid, delta), ("b2", r), P1["b2"][r], delta)
                        zz = y[r].add(c2); zz.r += URel * zz.mag() + T0
                        z.append(zz.snap())
                    zf, _ = ln4(z, "lnf", *LN["lnf"], delta, "LNf")
                    o = wbias(wdot([("oW", i) for i in range(d)], oW, zf, delta), ("oB",), oB, delta)
                    cache[key] = (o, float(o.lin()), float(o.r))
                o = cache[key][0]
                tg = outp(s, t); ncase += 1
                bound = abs(o.c - tg) + o.dev()
                worst = max(worst, bound)
                if bound > TOL:
                    info["worst"] = float(bound)
                    raise Reject(f"case token {t}, keys {sel}, task state {s}: output {float(o.c):.4f} +- {float(o.dev()):.4f} "
                                 f"(symbols {float(o.lin()):.4f}, radius {float(o.r):.4f}) against target {tg}")
                nxt = (step(s, t), tuple(((t,) + wn)[:hd["L"]] for hd, wn in zip(heads, wins)))
                if nxt not in seen: seen[nxt] = len(seen); todo.append(nxt)
        info.update(worst=float(worst), states=len(seen), table_rows=len(cache), cases=ncase,
                    symbols=max(len(v[0].t) for v in cache.values()),
                    worst_symbol_part=max(v[1] for v in cache.values()), worst_radius_part=max(v[2] for v in cache.values()))
        if table is not None: table.update(cache={k: (v[0], False) for k, v in cache.items()}, heads=heads, init=init)
        return True, "ok", info
    except Reject as e:
        return False, str(e), info


if __name__ == "__main__":
    import r5_checks as C5
    C5.memory_guard(2.5)
    a = sys.argv
    RAD = F(a[a.index("--radius") + 1]) if "--radius" in a else F(1, 2 ** 14)
    rows = []
    for seed in range(int(a[3]), int(a[4]) + 1):
        dd = os.path.join(HERE, "runs", "r9ln-tune", "A", a[2], "s%03d" % seed)
        sj = json.load(open(os.path.join(dd, "screen.json")))
        row = dict(seed=seed, s1_ok=sj["s1_ok"], screen=sj["pass"])
        if sj["pass"]:
            t0 = time.time(); table = {}
            Wq = json.load(open(os.path.join(dd, "W14.json")))
            ok, why, info = check(Wq, RAD, table)
            row.update(ok=ok, reason=why, secs=round(time.time() - t0, 1), **info)
            if ok and "--itest" in a:
                row["interval_test"] = L3.interval_test(Wq, RAD, seed, table)
        rows.append(row)
        print("A-LN %s s%03d | screen %s |" % (a[2], seed, sj["pass"]),
              ("-" if not sj["pass"] else ("ACCEPT worst %.3f (symbols %.3f radius %.3f) rows %d, %d symbols" % (row["worst"], row["worst_symbol_part"], row["worst_radius_part"], row["table_rows"], row["symbols"]) if row["ok"] else "reject: " + row["reason"][:170])),
              "| %s s |" % row.get("secs"), row.get("interval_test", ""), flush=True)
        json.dump(rows, open(os.path.join(HERE, "results", "rung9ln-proto4-%s-r%s.json" % (a[2], str(RAD).replace("/", "_"))), "w"), indent=1)
    sc = [r for r in rows if r["screen"]]
    print("screened %d of %d | prototype (design 4) accepts %d | interval-test violations %d" % (
        len(sc), len(rows), sum(bool(r.get("ok")) for r in sc), sum(r.get("interval_test", {}).get("violations", 0) for r in sc)))
