"""Rung 8 certificate checker: Python mirror, in exact rationals, of the Lean checker Lane4/R8Cert.lean
(PREREG_R8.md, Route step 1). The frozen K1 prototype is tools/r8_proto.py; this file is the design the kernel
evaluates. Differences from the prototype are listed in the study's private log (not included) entry that introduces this file.

Design (options in OPT so that variants can be compared on the tuning set BEFORE the checker freeze):
  forms     affine form = centre + sum of coefficient * symbol + radius. Symbols are ONLY the attention weights
            of the non-reference window keys (per head, in window order); every other error goes to the radius
            (OPT["fold"] = True restores the prototype's extra symbols, for comparison only).
  relu      slope lam = hi / (hi - lo) rounded DOWN to a multiple of 2^-LAMBITS; any lam in [0, 1] is sound with
            offset mu = max(-lam * lo, (1 - lam) * hi) / 2 and radius mu.
  refguard  in a head whose candidate set is every token, the reference key is the one with the highest nominal
            score, and the tail of older keys is bounded relative to the NEWEST key; the factor 3 between the two
            needs r_newest + r_ref + sigma <= 1, which is now CHECKED (the prototype assumed it).
  charges   SIG_DENSE (P1) and SOFT_DEN (P2) are parameters; one softmax-arithmetic charge for all heads.

usage: python tools/r8_cert.py <run dir> [--net W14.json] [--radius 1/16384] [--quiet]
"""
import json, os, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(HERE, "tools"))
import r7_cert as RC

RND, TINY, TOL, SMALL = RC.RND, RC.TINY, RC.TOL, RC.SMALL
TAILEXP, LMAX = 16, 3
GB = 70                      # outward rounding grid 2^-70 for exponentials and attention weights
OPT = dict(fold=False, lambits=20, sig_dense=F(1, 2 ** 8), soft_den=2 ** 13, soft_den_gated=2 ** 13)   # chosen 2026-11-20, pass 1


def up(x, b=GB): return F(-((-x.numerator * 2 ** b) // x.denominator), 2 ** b)
def dn(x, b=GB): return F((x.numerator * 2 ** b) // x.denominator, 2 ** b)


def exp_iv(x):
    """Rational enclosure (lo, hi) of exp(x) for rational x <= 6: 14 Taylor terms at x / 64, six squarings."""
    if x < -60: return F(0), F(1, 2 ** 80)
    assert x <= 6
    y = x / 64
    s = F(0); term = F(1)
    for k in range(14):
        s += term
        term = term * y / (k + 1)
    rem = abs(term) * 3
    lo, hi = dn(s - rem), up(s + rem)
    for _ in range(6):
        lo, hi = dn(lo * lo), up(hi * hi)
    return max(lo, F(0)), hi


class AF:
    __slots__ = ("c", "t", "r")

    def __init__(self, c=F(0), t=None, r=F(0)):
        self.c, self.t, self.r = F(c), dict(t or {}), F(r)

    def add(self, o):
        t = dict(self.t)
        for k, v in o.t.items(): t[k] = t.get(k, 0) + v
        return AF(self.c + o.c, t, self.r + o.r)

    def scale(self, a):
        return AF(self.c * a, {k: v * a for k, v in self.t.items()}, self.r * abs(a))

    def dev(self): return sum(abs(v) for v in self.t.values()) + self.r
    def lo(self): return self.c - self.dev()
    def hi(self): return self.c + self.dev()
    def mag(self): return abs(self.c) + self.dev()

    def fold(self, name):
        if not OPT["fold"] or self.r == 0: return self
        t = dict(self.t); t[name] = t.get(name, 0) + self.r
        return AF(self.c, t, 0)


def dot_af(row, xs, delta):
    out = AF()
    for a, x in zip(row, xs): out = out.add(x.scale(a))
    mags = [x.mag() for x in xs]
    Wm, Xm = max([abs(a) for a in row] + [0]), max(mags + [0])
    out.r += delta * sum(mags) + len(row) * (Wm + 1) * (Xm + 1) / 2 ** 16 + F(1, 2 ** 100)
    return out


def relu_af(p, name):
    lo, hi = p.lo(), p.hi()
    if lo >= 0: return p
    if hi <= 0: return AF()
    lam = dn(hi / (hi - lo), OPT["lambits"])
    mu = max(-lam * lo, (1 - lam) * hi) / 2
    q = p.scale(lam); q.c += mu
    if OPT["fold"]: q.t[name] = mu
    else: q.r += mu
    return q


def check(net, tname, delta, table=None):
    Q = lambda m: [[F(v) for v in r] for r in m]
    E = Q(net["embed"]); ntok = len(E); d = len(E[0])
    if len(net["blocks"]) != 1: return False, "more than one block", {}
    B = net["blocks"][0]
    H = len(B["b1"])
    W1 = [F(v) for r in B["W1"] for v in (r if isinstance(r, list) else [r])]
    W1 = [W1[i * d:(i + 1) * d] for i in range(H)]
    W2, b1, b2 = Q(B["W2"]), [F(v) for v in B["b1"]], [F(v) for v in B["b2"]]
    oW, oB = [F(v) for v in net["outW"]], F(net["outB"])
    allw = [v for r in E for v in r] + [v for r in W1 for v in r] + [v for r in W2 for v in r] + b1 + b2 + oW + [oB]
    for h in B["heads"]:
        allw += [F(v) for r in h["A"] for v in r] + [F(v) for r in h["V"] for v in r] + [F(v) for v in h["g"]] + [F(h["gb"])]
    fails = []          # head-level failures: the certificate is still built (the kernel then proves check8 = false)
    if max(abs(v) for v in allw) > SMALL: fails.append("a written weight is larger than 15")
    if delta < 0 or delta > F(1, 2): fails.append("radius out of range")
    e0 = delta + RND; xe = [e0] * d; sw = delta + RND
    heads = []
    for k, h in enumerate(B["heads"]):
        if h["mask"] not in ("strict", "causal"): fails.append(f"head {k}: mask not supported")
        A, V, g, gb, m = Q(h["A"]), Q(h["V"]), [F(v) for v in h["g"]], F(h["gb"]), F(h["m"])
        if m < 1 or m > 1024: fails.append(f"head {k}: slope out of range")
        cand = []
        for t in range(ntok):
            c, e = RC.dot_w(g, E[t], xe, delta); c += gb; e += sw + RND
            if abs(c) + e > SMALL: fails.append(f"head {k}: gate of token {t} fails the magnitude guard")
            if c + e < 0: cand.append(True)
            elif c - e > 0: cand.append(False)
            else: fails.append(f"head {k}: gate of token {t} not decided"); cand.append(c < 0)
        cs = [t for t in range(ntok) if cand[t]]
        AE = [[RC.dot_w(r, E[t], xe, delta) for r in A] for t in range(ntok)]
        S, Sfull = {}, [[None] * ntok for _ in range(ntok)]
        for q in range(ntok):
            Xq = max(abs(v) for v in E[q])
            for t in range(ntok):
                Y = max(abs(c) for c, _ in AE[t]); e2 = max(e for _, e in AE[t])
                cen = sum(E[q][i] * AE[t][i][0] for i in range(d))
                err = d * (e0 * (Y + e2) + Xq * e2) + d * (Xq + e0 + 1) * (Y + e2 + 1) / 2 ** 16 + F(1, 2 ** 100)
                Sfull[q][t] = (cen, err)
                if q >= 1 and cand[t]:
                    if (Xq + e0 + 1) * (Y + e2 + 1) > 2 ** 20 or abs(cen) + err > 1024:
                        fails.append(f"head {k}: content score of query {q}, key {t} fails the range guard")
                    S[q, t] = (cen, err)
        spread = max([S[q, b][0] - S[q, a][0] + S[q, a][1] + S[q, b][1] for q in range(1, ntok) for a in cs for b in cs] + [F(0)])
        sigma = (m + 2) / 32 + (m + 2) / 128 + F(1, 2 ** 11)
        L = next((l for l in range(1, LMAX + 1) if (m - delta) * l - spread - sigma >= TAILEXP), None)
        if L is None:
            fails.append(f"head {k}: content score spread {float(spread):.2f} too large for a window of {LMAX} at slope {float(m):g}"); L = LMAX
        VE = [[RC.dot_w(r, E[t], xe, delta) for r in V] for t in range(ntok)]
        Bv = [max([abs(VE[t][r][0]) + VE[t][r][1] for t in cs] + [0]) for r in range(d)]
        if max(Bv + [0]) > 2 ** 20: fails.append(f"head {k}: value bound too large")
        tail = F(1) if fails else up(exp_iv(-((m - delta) * L - spread - sigma))[1] * F(101, 100))
        dense = all(cand)
        sig_win = OPT["sig_dense"] if dense else sigma
        den = OPT["soft_den"] if dense else OPT["soft_den_gated"]
        soft = [b / den for b in Bv]
        heads.append(dict(k=k, mask=h["mask"], cand=cand, m=m, S=S, VE=VE, Bv=Bv, L=L, sigma=sig_win, tail=tail,
                          dense=dense, spread=spread, soft=soft, Sfull=Sfull))
    s0, step, outp = RC.task_dfa(tname)
    init = (s0, tuple((0,) if hd["cand"][0] else () for hd in heads))
    mkcert = lambda states: dict(heads=[dict(cands=hd["cand"], L=hd["L"], spread=hd["spread"], S=hd["Sfull"], VE=hd["VE"], Bv=hd["Bv"])
                                        for hd in heads], states=list(states))
    if fails: return False, fails[0], dict(cert=mkcert([init]))

    def head_out(hd, q, keys):
        if not keys: return [AF() for _ in range(d)], []
        full = len(keys) >= hd["L"] + (1 if hd["mask"] == "causal" and hd["cand"][q] else 0)
        nom = [-hd["m"] * rank + hd["S"][q, keys[rank]][0] for rank in range(len(keys))]
        ref = 0
        if hd["dense"]:
            for i in range(1, len(keys)):
                if nom[i] > nom[ref]: ref = i                      # first index of the maximum
            if hd["S"][q, keys[0]][1] + hd["S"][q, keys[ref]][1] + hd["sigma"] + delta * ref > 1:
                return None, "score radii too large for the reference key"
        c1, r1 = hd["S"][q, keys[ref]]
        w, idx = [], []
        for rank in range(len(keys)):
            if rank == ref: continue
            ck, rk = hd["S"][q, keys[rank]]
            dist = rank - ref
            hi_e = -hd["m"] * dist + delta * abs(dist) + (ck - c1) + rk + r1 + hd["sigma"]
            lo_e = -hd["m"] * dist - delta * abs(dist) + (ck - c1) - rk - r1 - hd["sigma"]
            if hi_e > 6: return None, "a key outscores the reference by more than e^6"
            rhi = exp_iv(hi_e)[1]
            rlo = exp_iv(lo_e)[0] if hd["dense"] else F(0)
            w.append([rlo, rhi]); idx.append(rank)
        tl = (hd["tail"] * 3) if full else F(0)
        outs = [AF(hd["VE"][keys[ref]][r][0]) for r in range(d)]
        desc = []
        for j, (rlo, rhi) in enumerate(w):
            others_lo = sum(x[0] for i, x in enumerate(w) if i != j)
            others_hi = sum(x[1] for i, x in enumerate(w) if i != j)
            ahi = up(rhi / (1 + rhi + others_lo))
            alo = dn(rlo / (1 + rlo + others_hi + tl))
            mid, rad = (ahi + alo) / 2, (ahi - alo) / 2
            desc.append((float(alo), float(ahi)))
            sym = ("a", hd["k"], j)
            for r in range(d):
                diff = hd["VE"][keys[idx[j]]][r][0] - hd["VE"][keys[ref]][r][0]
                outs[r] = outs[r].add(AF(mid * diff, {sym: rad * diff}))
        for r in range(d):
            outs[r].r += max(hd["VE"][t][r][1] for t in keys) + 2 * tl * hd["Bv"][r] + hd["soft"][r] + TINY
        return outs, desc

    cache, worst, ncase = {}, F(0), 0
    seen, todo = {init: 0}, [init]          # insertion-ordered: the certificate lists states in this order
    mixed = 0
    while todo:
        s, wins = todo.pop()
        for t in range(1, ntok):
            sel = tuple((((t,) if (hd["mask"] == "causal" and hd["cand"][t]) else ()) + wn) for hd, wn in zip(heads, wins))
            key = (t, sel)
            if key not in cache:
                y = [AF(E[t][r], None, e0) for r in range(d)]
                ok, why, mx, o = True, "", False, None
                for hd, keys in zip(heads, sel):
                    ho, desc = head_out(hd, t, keys)
                    if ho is None: ok, why = False, f"head {hd['k']}: {desc}"; break
                    mx = mx or any(a[1] > F(1, 100) for a in desc)
                    y = [a.add(b) for a, b in zip(y, ho)]
                    for a in y: a.r += RND
                    if any(a.mag() > SMALL for a in y): ok, why = False, "residual stream fails the magnitude guard"; break
                if ok:
                    y = [a.fold(("ey", r)) for r, a in enumerate(y)]
                    hid = []
                    for hh in range(H):
                        p = dot_af(W1[hh], y, delta); p.c += b1[hh]; p.r += sw + RND
                        if p.mag() > SMALL: ok, why = False, "hidden unit fails the magnitude guard"; break
                        hid.append(relu_af(p.fold(("eh", hh)), ("rl", hh)))
                if ok:
                    z = []
                    for r in range(d):
                        c2 = dot_af(W2[r], hid, delta); c2.c += b2[r]; c2.r += sw + RND
                        if c2.mag() > SMALL: ok, why = False, "MLP output fails the magnitude guard"; break
                        zz = y[r].add(c2); zz.r += RND
                        if zz.mag() > SMALL: ok, why = False, "block output fails the magnitude guard"; break
                        z.append(zz.fold(("ez", r)))
                if ok:
                    o = dot_af(oW, z, delta); o.c += oB; o.r += sw + RND
                    if o.mag() > SMALL: ok, why = False, "read-out fails the magnitude guard"
                cache[key] = (ok, why, o if ok else None, mx)
                mixed += mx
            ok, why, o, mx = cache[key]
            if not ok:
                return False, f"case token {t}, keys {sel}: {why}", dict(cert=mkcert(seen))
            tg = outp(s, t); ncase += 1
            bound = abs(o.c - tg) + o.dev()
            worst = max(worst, bound)
            if bound > TOL:
                return False, (f"case token {t}, keys {sel}, task state {s}: output {float(o.c):.4f} +- {float(o.dev()):.4f} "
                               f"against target {tg}" + (" (mixed attention)" if mx else "")), dict(worst=float(bound), cert=mkcert(seen))
            nxt = (step(s, t), tuple((((t,) + wn) if hd["cand"][t] else wn)[:hd["L"]] for hd, wn in zip(heads, wins)))
            if nxt not in seen: seen[nxt] = len(seen); todo.append(nxt)
    if table is not None: table.update(cache); table["__heads__"] = heads; table["__states__"] = list(seen)
    return True, "ok", dict(worst=float(worst), states=len(seen), table_rows=len(cache), cases=ncase,
                            window=[hd["L"] for hd in heads], spread=[round(float(hd["spread"]), 2) for hd in heads],
                            dense=[hd["dense"] for hd in heads], mixed_rows=mixed, cert=mkcert(seen))


if __name__ == "__main__":
    dd = sys.argv[1]
    f = sys.argv[sys.argv.index("--net") + 1] if "--net" in sys.argv else "W14.json"
    rad = F(sys.argv[sys.argv.index("--radius") + 1]) if "--radius" in sys.argv else F(1, 2 ** 14)
    tname = json.load(open(os.path.join(dd, "train.json")))["task"]
    ok, why, info = check(json.load(open(os.path.join(dd, f))), tname, rad)
    info.pop("cert", None)
    print(json.dumps(dict(dir=dd, net=f, radius=str(rad), ok=ok, reason=why, **info)))
