"""Rung 9-LN15 (PREREG_R9LN15.md): Python MIRROR of the Lean checker `Lane4.LNC.checkLN` (Lane4/LNCert.lean).
Integer arithmetic only after the heads: every quantity is an integer in units of 2^-56, with floor / ceiling
division exactly as the Lean text. A mirror, not a proof.

Shape of the check (reference for its decisions: tools/r9ln_proto4r.py mode 8):
  LN1          per token, on the embedding row with one symbol per embedding entry; gives a box per token.
  heads        rung 8's head check on those boxes with the score and value tables on relative rounding charges
               (headOKLN); windows, tails and headAF are rung 8's.
  head output  rational form -> integers; its whole radius becomes one fresh symbol per (head, coordinate).
  LN2, W1, ReLU, W2, LNf, read-out   forms with NS symbol slots:
               [ embedding (d) | attention (3 per head) | head output (d per head) | LN2 (d) | W1 (H) | W2 (d) ]

    python tools/r9ln15_cert.py tune <recipe> <seed0> <seed1> [--radius r] [--itest]
"""
import json, os, sys, time
from fractions import Fraction as F
from math import isqrt

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(HERE, "tools"))
import r9_proto as P9, r7_cert as RC

Reject = P9.Reject
SCB = 56
SC = 2 ** SCB
UB = 22                      # relative rounding charge 2^-22 (four binary32 roundings)
EPSI = SC // 100000          # LayerNorm epsilon 10^-5, rounded down; one unit of radius pays for it
TOL4 = SC // 4
SMALLI = 15 * SC


def cdiv(a, b): return -((-a) // b)
def chg(m): return m // 2 ** UB + 1
def toI(q):
    q = F(q) * SC
    if q.denominator != 1: raise Reject("a written weight or the radius is not on the 2^-56 grid")
    return q.numerator


class FF:
    __slots__ = ("c", "t", "r")
    def __init__(self, c, t, r): self.c, self.t, self.r = c, t, r
    def lin(self): return sum(abs(v) for v in self.t)
    def dev(self): return self.lin() + self.r
    def mag(self): return abs(self.c) + self.dev()


def addF(a, b): return FF(a.c + b.c, [x + y for x, y in zip(a.t, b.t)], a.r + b.r)
def subF(a, b): return FF(a.c - b.c, [x - y for x, y in zip(a.t, b.t)], a.r + b.r)
def zeroF(ns): return FF(0, [0] * ns, 0)
def bump(a, slot, v):
    """v >= 0 to the symbol slot, or to the radius when slot is None"""
    if slot is None: a.r += v
    else: a.t[slot] += v
    return a


def lnF(xs, gI, bI, dI, slot0, where):
    """LayerNorm of forms. slot0: first of len(xs) symbol slots for gain and bias, or None for the radius."""
    n, ns = len(xs), len(xs[0].t)
    mx = max(x.mag() for x in xs)
    s = xs[0]
    for x in xs[1:]: s = addF(s, x)
    mean = FF(s.c // n, [v // n for v in s.t], cdiv(s.r, n) + (ns + 1) + n * chg(mx))
    cs = []
    for x in xs:
        c = subF(x, mean); c.r += chg(x.mag() + mean.mag())
        cs.append(c)
    v = FF(sum(c.c * c.c for c in cs) // (n * SC) + EPSI,
           [sum(2 * c.c * c.t[i] for c in cs) // (n * SC) for i in range(ns)],
           cdiv(sum(2 * abs(c.c) * c.r + c.dev() ** 2 for c in cs), n * SC) + (ns + 3))
    v.r += (n + 3) * chg(v.mag())
    dv = v.dev()
    vmin = v.c - dv
    if vmin <= 0: raise Reject(f"{where}: variance not bounded away from zero")
    a = isqrt(v.c * SC); b_ = isqrt(vmin * SC)                  # Lean: found by Newton steps, then verified
    if b_ < 1: raise Reject(f"{where}: variance too small")
    glo, ghi = SC * SC // (a + 1), cdiv(SC * SC, a)
    g0 = (glo + ghi) // 2
    eg = ghi - glo + 1 + chg(cdiv(SC * SC, b_))
    if 8 * eg > g0: raise Reject(f"{where}: reciprocal square root too coarse")
    k1 = g0 ** 3 // (2 * SC * SC) + 1
    rinv = FF(g0, [(-k1 * t) // SC for t in v.t],
              cdiv(k1 * v.r, SC) + eg + cdiv(4 * k1 * eg * dv, g0 * SC) + cdiv(dv, SC) + cdiv(3 * dv * dv * SC ** 4, 8 * b_ ** 5) + (ns + 2))
    dr = rinv.dev()
    out = []
    for k, c in enumerate(cs):
        o = FF(c.c * g0 // SC, [(g0 * x + c.c * y) // SC for x, y in zip(c.t, rinv.t)],
               cdiv(g0 * c.r + abs(c.c) * rinv.r + c.dev() * dr, SC) + (ns + 1))
        o.r += chg(o.mag())
        if o.mag() > SMALLI: raise Reject(f"{where}: normalised value fails the magnitude guard")
        o2 = FF(gI[k] * o.c // SC, [gI[k] * x // SC for x in o.t], cdiv(abs(gI[k]) * o.r, SC) + (ns + 1) + cdiv(dI * o.dev(), SC))
        if slot0 is not None: assert not any(o2.t[slot0:])        # Lean: freeOpt guard
        bump(o2, None if slot0 is None else slot0 + k, cdiv(dI * (abs(o.c) + SC), SC))
        o2.r += chg(o2.mag()) + chg(abs(bI[k]) + dI)
        o2.c += bI[k]
        o2.r += chg(o2.mag())
        if o2.mag() > SMALLI: raise Reject(f"{where}: output fails the magnitude guard")
        out.append(o2)
    return out


def dotF(slot, wI, xs, bI, dI, slot0=None):
    """stored row . forms + stored bias; the ball on row and bias as one symbol (slot) or radius (None)"""
    ns, n = len(xs[0].t), len(wI)
    o = FF(sum(w * x.c for w, x in zip(wI, xs)) // SC,
           [sum(w * x.t[i] for w, x in zip(wI, xs)) // SC for i in range(ns)],
           cdiv(sum(abs(w) * x.r for w, x in zip(wI, xs)), SC) + (ns + 1))
    o.r += cdiv(dI * sum(x.dev() for x in xs), SC) + cdiv((n + 2) * 2 * sum((abs(w) + dI) * x.mag() for w, x in zip(wI, xs)), SC * 2 ** UB) + 1 + chg(abs(bI) + dI)
    if slot0 is not None: assert not any(o.t[slot0:])            # Lean: freeOpt guard
    o.c += bI
    bump(o, slot, cdiv(dI * (sum(abs(x.c) for x in xs) + SC), SC))
    o.r += chg(o.mag())
    if o.mag() > SMALLI: raise Reject("a row output fails the magnitude guard")
    return o


def reluF(p):
    lo, hi = p.c - p.dev(), p.c + p.dev()
    if lo >= 0: return p
    if hi <= 0: return zeroF(len(p.t))
    lam = hi * 2 ** 20 // (hi - lo)
    mu = cdiv(max(-lam * lo, (2 ** 20 - lam) * hi), 2 ** 21)
    return FF(lam * p.c // 2 ** 20 + mu, [lam * x // 2 ** 20 for x in p.t], cdiv(lam * p.r, 2 ** 20) + (len(p.t) + 1) + mu)


def dot_rel(row, xc, xe, delta):
    """value table entry: rational centre and error of a stored row applied to a box (relative rounding charge)"""
    c = sum(a * x for a, x in zip(row, xc))
    tot = sum((abs(a) + delta) * (abs(x) + e) for a, x, e in zip(row, xc, xe))
    werr = sum(abs(a) * e + delta * (abs(x) + e) for a, x, e in zip(row, xc, xe))
    return c, werr + (len(row) + 2) * tot / 2 ** (UB - 1) + F(1, 2 ** 60)


def head_tablesR(k, h, boxes, ntok, delta, d):
    """The tables of Lane4.LNC.headOKLN, formula for formula: score and value tables with relative charges."""
    if any(v != 0 for v in h["g"]) or h["gb"] != -1: raise Reject(f"head {k}: gated head")
    m = h["m"]
    if m < 1 or m > 1024: raise Reject(f"head {k}: slope out of range")
    AE = {c: [dot_rel(r, bc, br, delta) for r in h["A"]] for c, (bc, br) in boxes.items()}
    S = {}
    for q in boxes:
        qc, qr = boxes[q]
        X, e1 = max(abs(v) for v in qc), max(qr)
        for c in boxes:
            Y = max(abs(x) for x, _ in AE[c]); e2 = max(e for _, e in AE[c])
            cen = sum(qc[i] * AE[c][i][0] for i in range(d))
            tot = sum((abs(qc[i]) + qr[i]) * (abs(AE[c][i][0]) + AE[c][i][1]) for i in range(d))
            err = sum(qr[i] * (abs(AE[c][i][0]) + AE[c][i][1]) + abs(qc[i]) * AE[c][i][1] for i in range(d)) \
                + (d + 2) * tot / 2 ** (UB - 1) + F(1, 2 ** 60)
            if q >= 1 and ((X + e1 + 1) * (Y + e2 + 1) > 2 ** 20 or abs(cen) + err > 1024):
                raise Reject(f"head {k}: content score of query {q}, key {c} fails the range guard")
            S[q, c] = (cen, err)
    cs = list(boxes)
    spread = max([S[q, b][0] - S[q, a][0] + S[q, a][1] + S[q, b][1] for q in range(1, ntok) for a in cs for b in cs] + [F(0)])
    sigma = (m + 2) / 32 + (m + 2) / 128 + F(1, 2 ** 11)
    L = next((l for l in range(1, P9.LMAX + 1) if (m - delta) * l - spread - sigma >= P9.TAILEXP), None)
    if L is None: raise Reject(f"head {k}: content score spread {float(spread):.2f} too large for a window of {P9.LMAX}")
    VE = {c: [dot_rel(r, bc, br, delta) for r in h["V"]] for c, (bc, br) in boxes.items()}
    Bv = [max([abs(VE[c][r][0]) + VE[c][r][1] for c in cs] + [F(0)]) for r in range(d)]
    if max(Bv) > 2 ** 20: raise Reject(f"head {k}: value bound too large")
    tail = P9.up(P9.exp_iv(-((m - delta) * L - spread - sigma))[1] * F(101, 100))
    return dict(b=0, k=k, mask=h["mask"], m=m, S=S, VE=VE, Bv=Bv, L=L, sigma=P9.OPT["sig_dense"], tail=tail, spread=spread,
                soft=[b / P9.OPT["soft_den"] for b in Bv])


def check(net, delta, table=None, task="A"):
    info = {}
    try:
        Q = lambda m: [[F(v) for v in r] for r in m]
        E = Q(net["embed"]); ntok = len(E); d = len(E[0])
        if len(net["blocks"]) != 1: raise Reject("not one block")
        P1 = P9.parse_block(net["blocks"][0], d)
        nh, H = len(P1["heads"]), P1["H"]
        if [h["mask"] for h in P1["heads"]] != ["strict", "causal"]: raise Reject("heads are not (strict, causal)")
        if delta < 0 or delta > F(1, 2): raise Reject("radius out of range")
        I = lambda l: [toI(v) for v in l]
        dI = toI(delta)
        EI = [I(r) for r in E]
        LN = {n: (I(net["ln"][n]["g"]), I(net["ln"][n]["b"])) for n in ("ln1", "ln2", "lnf")}
        W1I, b1I, W2I, b2I = [I(r) for r in P1["W1"]], I(P1["b1"]), [I(r) for r in P1["W2"]], I(P1["b2"])
        oWI, oBI = I([F(v) for v in net["outW"]]), toI(F(net["outB"]))
        allw = [v for r in EI for v in r] + oWI + [oBI] + [v for r in W1I for v in r] + [v for r in W2I for v in r] + b1I + b2I
        for g, b in LN.values(): allw += g + b
        if max(abs(v) for v in allw) > SMALLI: raise Reject("a written weight is larger than 15")
        aB = d; hB = aB + 3 * nh; lB = hB + nh * d; wB = lB + d; vB = wB + H; NS = vB + d
        info["slots"] = NS

        def res(t):
            out = []
            for r in range(d):
                f = FF(EI[t][r], [0] * NS, chg(abs(EI[t][r]) + dI)); f.t[r] = dI
                out.append(f)
            return out
        boxes = {}
        for t in range(ntok):
            hs = lnF(res(t), *LN["ln1"], dI, None, f"LN1 token {t}")
            boxes[t] = ([F(a.c, SC) for a in hs], [F(a.dev(), SC) for a in hs])
        heads = [head_tablesR(k, h, boxes, ntok, delta, d) for k, h in enumerate(P1["heads"])]
        info["window"] = [hd["L"] for hd in heads]
        s0, step, outp = RC.task_dfa(task)
        init = (s0, tuple((0,) for _ in heads))
        seen, todo, cache, worst, ncase = {init: 0}, [init], {}, 0, 0
        tk = range(ntok)
        cur = [None]
        mkcert = lambda fail=None: dict(fail=fail,
            heads=[dict(cands=[True] * ntok, L=hd["L"], spread=hd["spread"], S=[[hd["S"][q, t] for t in tk] for q in tk],
                        VE=[hd["VE"][t] for t in tk], Bv=hd["Bv"]) for hd in heads],
            boxes=[list(zip(*boxes[t])) for t in tk],
            W=dict(E=EI, g1=LN["ln1"][0], b1=LN["ln1"][1], g2=LN["ln2"][0], b2=LN["ln2"][1], gf=LN["lnf"][0], bf=LN["lnf"][1],
                   W1=W1I, c1=b1I, W2=W2I, c2=b2I, oW=oWI, oB=oBI),
            states=[(s_, [list(wn) for wn in wins_]) for (s_, wins_) in seen], d=d, NS=NS)
        info["mk"], info["cur"] = mkcert, cur      # Lean files need the certificate also when a case fails
        while todo:
            s, wins = todo.pop()
            for t in range(1, ntok):
                cur[0] = (seen[(s, wins)], t)
                sel = tuple((((t,) + wn) if hd["mask"] == "causal" else wn) for hd, wn in zip(heads, wins))
                key = (t, sel)
                if key not in cache:
                    y = res(t)
                    for hd, keys in zip(heads, sel):
                        k = hd["k"]
                        if len(keys) > 4: raise Reject("more than four keys in a window")
                        ho8, _ = P9.head_out(hd, t, keys, delta, d)
                        for r in range(d):
                            a8 = ho8[r]
                            f = FF((a8.c * SC).__floor__(), [0] * NS, 0)
                            n8 = 0
                            for (_, _, _, j), cf in a8.t.items():
                                f.t[aB + 3 * k + j] = (cf * SC).__floor__(); n8 += 1
                            f.t[hB + k * d + r] = -((-(a8.r * SC)).__floor__()) + 1 + n8
                            y[r] = addF(y[r], f); y[r].r += chg(y[r].mag())
                            if y[r].mag() > SMALLI: raise Reject("residual stream fails the magnitude guard")
                    assert not any(v for a in y for v in a.t[lB:])   # Lean: y.all (zeroFrom lB)
                    y2 = lnF(y, *LN["ln2"], dI, lB, "LN2")
                    hid = [reluF(dotF(wB + hh, W1I[hh], y2, b1I[hh], dI, wB)) for hh in range(H)]
                    if any(a.mag() > SMALLI for a in hid): raise Reject("a hidden unit after the ReLU fails the magnitude guard")
                    z = []
                    for r in range(d):
                        zz = addF(y[r], dotF(vB + r, W2I[r], hid, b2I[r], dI, vB)); zz.r += chg(zz.mag())
                        if zz.mag() > SMALLI: raise Reject("residual stream after the MLP fails the magnitude guard")
                        z.append(zz)
                    zf = lnF(z, *LN["lnf"], dI, None, "LNf")
                    cache[key] = dotF(None, oWI, zf, oBI, dI)
                o = cache[key]
                tg = outp(s, t); ncase += 1
                bound = abs(o.c - tg * SC) + o.dev()
                worst = max(worst, bound)
                if bound > TOL4:
                    info["worst"] = bound / SC
                    raise Reject(f"case token {t}, keys {sel}, task state {s}: output {o.c / SC:.4f} +- {o.dev() / SC:.4f} "
                                 f"(symbols {o.lin() / SC:.4f}, radius {o.r / SC:.4f}) against target {tg}")
                nxt = (step(s, t), tuple(((t,) + wn)[:hd["L"]] for hd, wn in zip(heads, wins)))
                if nxt not in seen: seen[nxt] = len(seen); todo.append(nxt)
        info.update(worst=worst / SC, states=len(seen), table_rows=len(cache), cases=ncase)
        info.pop("cur"); info["cert"] = info.pop("mk")()
        if table is not None:
            class V:
                def __init__(s_, o): s_.c, s_._d = F(o.c, SC), F(o.dev(), SC)
                def dev(s_): return s_._d
                def lo(s_): return s_.c - s_._d
                def hi(s_): return s_.c + s_._d
            table.update(cache={k: (V(v), False) for k, v in cache.items()}, heads=heads, init=init)
        return True, "ok", info
    except Reject as e:
        if "mk" in info: info["cert"] = info.pop("mk")(info.pop("cur")[0])
        return False, str(e), info


if __name__ == "__main__":
    import r5_checks as C5, r9ln_proto as L3
    C5.memory_guard(2.5)
    a = sys.argv
    RAD = F(a[a.index("--radius") + 1]) if "--radius" in a else F(1, 2 ** 15)
    rows = []
    for seed in range(int(a[3]), int(a[4]) + 1):
        dd = os.path.join(HERE, "runs", "r9ln-tune", "A", a[2], "s%03d" % seed)
        sj = json.load(open(os.path.join(dd, "screen.json")))
        row = dict(seed=seed, s1_ok=sj["s1_ok"], screen=sj["pass"])
        if sj["pass"]:
            t0 = time.time(); table = {}
            Wq = json.load(open(os.path.join(dd, "W14.json")))
            ok, why, info = check(Wq, RAD, table)
            info.pop("cert", None)
            row.update(ok=ok, reason=why, secs=round(time.time() - t0, 1), **info)
            if ok and "--itest" in a:
                row["interval_test"] = L3.interval_test(Wq, RAD, seed, table)
        rows.append(row)
        print("A-LN %s s%03d | screen %s |" % (a[2], seed, sj["pass"]),
              ("-" if not sj["pass"] else ("ACCEPT worst %.3f rows %d" % (row["worst"], row["table_rows"]) if row["ok"] else "reject: " + row["reason"][:150])),
              "| %s s |" % row.get("secs"), row.get("interval_test", ""), flush=True)
        json.dump(rows, open(os.path.join(HERE, "results", "rung9ln15-mirror-%s-r%s.json" % (a[2], str(RAD).replace("/", "_"))), "w"), indent=1)
    sc = [r for r in rows if r["screen"]]
    print("mirror radius %s | screened %d | accepts %d %s | interval-test violations %d" % (
        RAD, len(sc), sum(bool(r.get("ok")) for r in sc), [r["seed"] for r in sc if r.get("ok")],
        sum(r.get("interval_test", {}).get("violations", 0) for r in sc)))
