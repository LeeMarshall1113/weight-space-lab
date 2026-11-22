"""Rung 9-LN, K2 prototype (PREREG_R9LN.md): exact-rational certificate check for the one-block network with
three LayerNorms (tools/r9ln.py). A prototype, not a proved checker. It keeps the rung-8 mirror's arithmetic
(tools/r8_cert.py through tools/r9_proto.py: affine forms, head tables over boxes, window states) and adds the
LayerNorm enclosure registered in PREREG_R9LN.md:

  centring     exact on the affine forms (linear), one rounding charge per operation;
  variance     interval from the centred forms' ranges: sum of min / max squares over D, plus eps;
  1/sigma      rational square-root enclosure (integer square root on a 2^-SQB grid), reciprocal interval
               [r_lo, r_hi]; each centred form is scaled by the midpoint and charged (r_hi - r_lo)/2 * magnitude;
  gain, bias   stored weights in the delta-ball: scale by the gain, charge delta * magnitude, add the bias.
LN1 is applied to the embedding boxes per token before the head tables (keys, values and query scores read it).

    python tools/r9ln_proto.py tune <recipe> <seed0> <seed1> [--itest]    -> results/rung9ln-proto-<recipe>.json
"""
import json, math, os, sys, time
from fractions import Fraction as F
import numpy as np

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(HERE, "tools"))
import r9_proto as P9, r7_cert as RC

AF, dot_af, relu_af, up, dn = P9.AF, P9.dot_af, P9.relu_af, P9.up, P9.dn
RND, TINY, TOL, SMALL = P9.RND, P9.TINY, P9.TOL, P9.SMALL
EPS = F(1, 100000)
SQB = 40
OPTL = dict(var="interval")


def sqrt_iv(lo, hi):
    """Rational enclosure of sqrt on [lo, hi], 0 <= lo <= hi, on the 2^-SQB grid."""
    a = math.isqrt((lo.numerator << (2 * SQB)) // lo.denominator)
    b = math.isqrt(-((-hi.numerator << (2 * SQB)) // hi.denominator)) + 1
    return F(a, 2 ** SQB), F(b, 2 ** SQB)


URel = F(1, 2 ** 22)          # a few binary32 roundings, RELATIVE to the magnitude (the Rnd model is relative)
T0 = F(1, 2 ** 60)


def ln_af(xs, g, b, delta, where):
    """LayerNorm of a list of affine forms; returns a list of affine forms. Design 2 (2026-11-21): rounding is
    charged relative to magnitudes, as the rounding model states it, not as the absolute 2^-20 of design 1."""
    d = len(xs)
    mx = max(x.mag() for x in xs)
    mean = AF()
    for x in xs: mean = mean.add(x)
    mean = mean.scale(F(1, d)); mean.r += d * URel * mx + T0
    cs = []
    for x in xs:
        c = x.add(mean.scale(-1)); c.r += URel * (x.mag() + mean.mag()) + T0
        if c.mag() > SMALL: raise P9.Reject(f"{where}: centred value fails the magnitude guard")
        cs.append(c)
    slo = shi = F(0)
    for c in cs:
        lo, hi = c.lo(), c.hi()
        slo += F(0) if lo <= 0 <= hi else min(lo * lo, hi * hi)
        shi += max(lo * lo, hi * hi)
    vraw = shi / d + EPS
    charge = (d + 3) * URel * vraw + T0                # squares, their sum, the division and + eps, each relative
    vlo, vhi = slo / d + EPS - charge, vraw + charge
    if vlo <= 0: raise P9.Reject(f"{where}: variance not bounded away from zero")
    s_lo, _ = sqrt_iv(vlo, vlo); _, s_hi = sqrt_iv(vhi, vhi)
    s_lo = s_lo * (1 - URel); s_hi = s_hi * (1 + URel)   # rounding of the square root
    r_lo, r_hi = 1 / s_hi, 1 / s_lo
    r0, rho = (r_lo + r_hi) / 2, (r_hi - r_lo) / 2
    out = []
    for k, c in enumerate(cs):
        o = c.scale(r0); o.r += rho * c.mag(); o.r += URel * o.mag() + T0
        if o.mag() > SMALL: raise P9.Reject(f"{where}: normalised value fails the magnitude guard")
        m = o.mag()
        o = o.scale(g[k]); o.r += delta * m + URel * o.mag() + T0
        o.c += b[k]; o.r += delta; o.r += URel * o.mag() + T0
        if o.mag() > SMALL: raise P9.Reject(f"{where}: LayerNorm output fails the magnitude guard")
        out.append(o)
    return out, (float(vlo), float(vhi))


def dot_w2(row, xc, xe, delta):
    """Stored-weight row applied to a vector known to (xc, xe). Design 3: the rounding of a d-term binary32 dot
    product is charged as (d + 2) * 2^-23 * sum |a||x| (the standard relative bound), not rung 8's 2^-16 constant."""
    c = sum(a * x for a, x in zip(row, xc))
    tot = sum((abs(a) + delta) * (abs(x) + e) for a, x, e in zip(row, xc, xe))
    werr = sum(abs(a) * e + delta * (abs(x) + e) for a, x, e in zip(row, xc, xe))
    return c, werr + (len(row) + 2) * URel * 2 * tot + T0


def dot_af2(row, xs, delta):
    out = AF()
    for a_, x in zip(row, xs): out = out.add(x.scale(a_))
    mags = [x.mag() for x in xs]
    out.r += delta * sum(mags) + (len(row) + 2) * URel * 2 * sum((abs(a_) + delta) * m for a_, m in zip(row, mags)) + T0
    return out


def head_tables2(k, h, boxes, qclasses, delta, d):
    """tools/r9_proto.py head_tables with the tightened dot products (design 3)."""
    m = h["m"]
    if m < 1 or m > 1024: raise P9.Reject(f"head {k}: slope out of range")
    AE = {c: [dot_w2(r, bc, br, delta) for r in h["A"]] for c, (bc, br) in boxes.items()}
    S = {}
    for q in boxes:
        qc, qr = boxes[q]
        for c in boxes:
            cen = sum(qc[i] * AE[c][i][0] for i in range(d))
            tot = sum((abs(qc[i]) + qr[i]) * (abs(AE[c][i][0]) + AE[c][i][1]) for i in range(d))
            err = sum(qr[i] * (abs(AE[c][i][0]) + AE[c][i][1]) + abs(qc[i]) * AE[c][i][1] for i in range(d)) + (d + 2) * URel * 2 * tot + T0
            if abs(cen) + err > 1024: raise P9.Reject(f"head {k}: content score of query {q}, key {c} fails the range guard")
            S[q, c] = (cen, err)
    cs = list(boxes)
    spread = max([S[q, b][0] - S[q, a][0] + S[q, a][1] + S[q, b][1] for q in qclasses for a in cs for b in cs] + [F(0)])
    sigma = (m + 2) / 32 + (m + 2) / 128 + F(1, 2 ** 11)
    L_ = next((l for l in range(1, P9.LMAX + 1) if (m - delta) * l - spread - sigma >= P9.TAILEXP), None)
    if L_ is None:
        raise P9.Reject(f"head {k}: content score spread {float(spread):.2f} too large for a window of {P9.LMAX} at slope {float(m):g}")
    VE = {c: [dot_w2(r, bc, br, delta) for r in h["V"]] for c, (bc, br) in boxes.items()}
    Bv = [max(abs(VE[c][r][0]) + VE[c][r][1] for c in cs) for r in range(d)]
    tail = up(P9.exp_iv(-((m - delta) * L_ - spread - sigma))[1] * F(101, 100))
    return dict(b=1, k=k, mask=h["mask"], m=m, S=S, VE=VE, Bv=Bv, L=L_, sigma=P9.OPT["sig_dense"], tail=tail,
                spread=spread, soft=[b / P9.OPT["soft_den"] for b in Bv])


def check(net, delta, table=None):
    info = {}
    try:
        Q = lambda m: [[F(v) for v in r] for r in m]
        E = Q(net["embed"]); ntok = len(E); d = len(E[0])
        if len(net["blocks"]) != 1: raise P9.Reject("not one block")
        P1 = P9.parse_block(net["blocks"][0], d)
        if [h["mask"] for h in P1["heads"]] != ["strict", "causal"]: raise P9.Reject("heads are not (strict, causal)")
        oW, oB = [F(v) for v in net["outW"]], F(net["outB"])
        LN = {n: ([F(v) for v in net["ln"][n]["g"]], [F(v) for v in net["ln"][n]["b"]]) for n in ("ln1", "ln2", "lnf")}
        allw = [v for r in E for v in r] + oW + [oB] + [v for r in P1["W1"] for v in r] + [v for r in P1["W2"] for v in r] + P1["b1"] + P1["b2"]
        for h in P1["heads"]: allw += [v for r in h["A"] for v in r] + [v for r in h["V"] for v in r]
        for g, b in LN.values(): allw += g + b
        if max(abs(v) for v in allw) > SMALL: raise P9.Reject("a written weight is larger than 15")
        if delta < 0 or delta > F(1, 2): raise P9.Reject("radius out of range")
        sw = delta + URel * 16 + T0
        res = lambda t: [AF(E[t][r], None, delta + URel * (abs(E[t][r]) + delta) + T0) for r in range(d)]
        # LN1 on every token's embedding: boxes for keys, values and query scores
        boxes = {}
        for t in range(ntok):
            hs, _ = ln_af(res(t), *LN["ln1"], delta, f"LN1 token {t}")
            boxes[t] = ([a.c for a in hs], [a.dev() for a in hs])
        info["ln1_radius_max"] = float(max(max(r) for _, r in boxes.values()))
        heads = [head_tables2(k, h, boxes, list(range(1, ntok)), delta, d) for k, h in enumerate(P1["heads"])]
        info["window"] = [hd["L"] for hd in heads]; info["spread"] = [round(float(hd["spread"]), 2) for hd in heads]
        s0, step, outp = RC.task_dfa("A")
        init = (s0, tuple((0,) for _ in heads))
        seen, todo, cache, worst, ncase, mixed, vmin = {init: 0}, [init], {}, F(0), 0, 0, 1e9
        while todo:
            s, wins = todo.pop()
            for t in range(1, ntok):
                sel = tuple((((t,) + wn) if hd["mask"] == "causal" else wn) for hd, wn in zip(heads, wins))
                key = (t, sel)
                if key not in cache:
                    y = res(t); mx = False
                    for hd, keys in zip(heads, sel):
                        ho, desc = P9.head_out(hd, t, keys, delta, d)
                        mx = mx or any(a > 0.01 for a in desc)
                        y = [a.add(b_) for a, b_ in zip(y, ho)]
                        for a in y: a.r += URel * a.mag() + T0
                        if any(a.mag() > SMALL for a in y): raise P9.Reject("residual stream fails the magnitude guard")
                    y2, v2 = ln_af(y, *LN["ln2"], delta, "LN2")
                    hid = []
                    for hh in range(P1["H"]):
                        p = dot_af2(P1["W1"][hh], y2, delta); p.c += P1["b1"][hh]; p.r += sw
                        if p.mag() > SMALL: raise P9.Reject("hidden unit fails the magnitude guard")
                        hid.append(relu_af(p, None))
                    z = []
                    for r in range(d):
                        c2 = dot_af2(P1["W2"][r], hid, delta); c2.c += P1["b2"][r]; c2.r += sw
                        if c2.mag() > SMALL: raise P9.Reject("MLP output fails the magnitude guard")
                        zz = y[r].add(c2); zz.r += URel * zz.mag() + T0
                        if zz.mag() > SMALL: raise P9.Reject("block output fails the magnitude guard")
                        z.append(zz)
                    zf, vf = ln_af(z, *LN["lnf"], delta, "LNf")
                    o = dot_af2(oW, zf, delta); o.c += oB; o.r += sw
                    if o.mag() > SMALL: raise P9.Reject("read-out fails the magnitude guard")
                    cache[key] = (o, mx); mixed += mx; vmin = min(vmin, v2[0], vf[0])
                o, mx = cache[key]
                tg = outp(s, t); ncase += 1
                bound = abs(o.c - tg) + o.dev()
                worst = max(worst, bound)
                if bound > TOL:
                    info["worst"] = float(bound)
                    raise P9.Reject(f"case token {t}, keys {sel}, task state {s}: output {float(o.c):.4f} +- {float(o.dev()):.4f} "
                                    f"against target {tg}" + (" (mixed attention)" if mx else ""))
                nxt = (step(s, t), tuple(((t,) + wn)[:hd["L"]] for hd, wn in zip(heads, wins)))
                if nxt not in seen: seen[nxt] = len(seen); todo.append(nxt)
        info.update(worst=float(worst), states=len(seen), table_rows=len(cache), cases=ncase, mixed_rows=mixed, variance_min=vmin)
        if table is not None: table.update(cache=cache, heads=heads, init=init)
        return True, "ok", info
    except P9.Reject as e:
        return False, str(e), info


def interval_test(Wq, delta, seed, table):
    import r9ln
    net = r9ln.fmap(Wq, lambda v: float(F(v)))
    heads, cache = table["heads"], table["cache"]
    rng = np.random.default_rng(9500 + seed)
    res = {"positions": 0, "violations": 0, "smallest_slack": 1e9}
    plan = [(int(rng.choice([3, 8, 30, 200])), np.float64, k % 3) for k in range(45)] + \
           [(2000, np.float32, 0), (2000, np.float32, 1), (65534, np.float32, 0)]
    for n, dt, pk in plan:
        w = rng.integers(1, 6, n)
        pert = None if pk == 0 else r9ln.random_pert(net, float(delta), rng, "sign" if pk == 1 else "uniform")
        q = np.arange(1, n + 1) if n <= 200 else np.sort(rng.choice(np.arange(1, n + 1), 500, replace=False))
        y = dict(zip([int(i) for i in q], r9ln.run(net, w, pert, dt, q)))
        wins = table["init"][1]
        for i in range(1, n + 1):
            t = int(w[i - 1])
            sel = tuple((((t,) + wn) if hd["mask"] == "causal" else wn) for hd, wn in zip(heads, wins))
            if i in y:
                o = cache[t, sel][0]
                slack = min(float(y[i]) - float(o.lo()), float(o.hi()) - float(y[i]))
                res["positions"] += 1; res["violations"] += int(slack < 0)
                res["smallest_slack"] = min(res["smallest_slack"], slack)
            wins = tuple(((t,) + wn)[:hd["L"]] for hd, wn in zip(heads, wins))
    return res


if __name__ == "__main__":
    import r5_checks as C5
    C5.memory_guard(2.5)
    a = sys.argv
    rows = []
    RAD = F(a[a.index("--radius") + 1]) if "--radius" in a else F(1, 2 ** 14)   # diagnostic only; the statement is 2^-14
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
                row["interval_test"] = interval_test(Wq, RAD, seed, table)
        rows.append(row)
        print("A-LN %s s%03d | screen %s |" % (a[2], seed, sj["pass"]),
              ("-" if not sj["pass"] else ("ACCEPT worst %.3f rows %d" % (row["worst"], row["table_rows"]) if row["ok"] else "reject: " + row["reason"][:140])),
              "|", {k: row[k] for k in ("window", "spread", "ln1_radius_max", "variance_min") if k in row}, "|", row.get("interval_test", ""), flush=True)
        json.dump(rows, open(os.path.join(HERE, "results", "rung9ln-proto-%s%s.json" % (a[2], "" if "--radius" not in a else "-r" + a[a.index("--radius") + 1].replace("/", "_"))), "w"), indent=1)
    sc = [r for r in rows if r["screen"]]
    print("screened %d of %d | prototype accepts %d | interval-test violations %d" % (
        len(sc), len(rows), sum(bool(r.get("ok")) for r in sc), sum(r.get("interval_test", {}).get("violations", 0) for r in sc)))
