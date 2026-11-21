"""Rung 8 prototype checker (SCOPE_R8.md candidate (a), with (b) folded in). Exact rationals; exp by rational
enclosures. NOT a proof and not yet backed by any Lean statement: it computes what a sound checker of this
design would accept, so that kill rule K1 can be read before any Lean or doctor work.

Differences from the rung-7 checker (tools/r7_cert.py):
  window    per head, the abstract state keeps the last L candidate tokens (newest first), L in 1..3 read from
            the network: the smallest L for which keys older than the window carry softmax weight < e^-16.
  mixture   the head output is the newest key's value plus, for each older key in the window, its attention
            weight times the value difference. Weights are bounded from score intervals (ratio to the newest
            key); no fixed gap is required. Heads whose candidate set is every token have exactly known
            spacing; gated heads only a minimum spacing (older keys may be anywhere further back).
  affine    values are affine forms: centre + sum of coefficient * symbol (each symbol in [-1, 1]) + radius.
            Symbols: one per older-key attention weight per head, one per residual coordinate error, one per
            hidden unit error and per ReLU relaxation. ReLU on a unit whose range straddles 0 uses the
            standard zonotope relaxation.
  kept      rounding charges (RND, the dot-product rounding term), magnitude guards at 15, tolerance 1/4; for
            GATED heads the proved rung-7 charges: softmax arithmetic B/100 + 2^-90 and score-difference slack
            (m+2)/32 + (m+2)/128 + 2^-11.
  new, NOT yet proved (proof obligations of rung 8, marked P1 and P2 in the code): for heads whose candidate
            set is every token, the score-difference slack is 2^-10 and the softmax-arithmetic charge is
            B/2^16, because the competing keys are within L + 1 positions of the query.
  ball      the perturbation radius is a parameter. The rung-7 skeleton (multiples of 1/1024, radius 1/1000)
            is one choice; a finer skeleton (multiples of 2^-g, radius 2^-g) gives the same headline for the
            network as trained with a smaller robustness ball.

usage: python tools/r8_proto.py <run dir> [--quiet]         one network
       python tools/r8_proto.py --k1                        the K1 read -> results/rung8-k1.json
"""
import json, os, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(HERE, "tools"))
import r7_cert as RC

DELTA, RND, TINY, TOL, SMALL = RC.DELTA, RC.RND, RC.TINY, RC.TOL, RC.SMALL
TAILEXP = 16                 # keys older than the window are below e^-16 relative to the newest key
LMAX = 3
G = 2 ** 70                  # outward rounding grid for exponentials and weights


def up(x): return F(-((-x.numerator * G) // x.denominator), G)
def dn(x): return F((x.numerator * G) // x.denominator, G)


def exp_iv(x):
    """Rational enclosure (lo, hi) of exp(x) for rational x <= 6."""
    if x < -60: return F(0), F(1, 2 ** 80)
    assert x <= 6
    y = x / 64
    lo = hi = F(0); term = F(1)
    for k in range(14):
        lo += term; hi += term
        term = term * y / (k + 1)
    rem = abs(term) * 3                      # |y| < 1: remainder <= |y|^14/14! * e^|y|
    lo, hi = dn(lo - rem), up(hi + rem)
    for _ in range(6):
        lo, hi = dn(lo * lo), up(hi * hi)
    return max(lo, F(0)), hi


class AF:
    """affine form: c + sum_k t[k] * eps_k + [-r, r], eps_k in [-1, 1]"""
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
        """move the radius into a fresh symbol (so later linear maps track it with its sign)"""
        if self.r == 0: return self
        t = dict(self.t); t[name] = t.get(name, 0) + self.r
        return AF(self.c, t, 0)


def dot_af(row, xs, delta):
    """stored-weight row applied to affine forms: affine part exact, perturbation and rounding into the radius"""
    out = AF()
    for a, x in zip(row, xs): out = out.add(x.scale(a))
    mags = [x.mag() for x in xs]
    Wm, Xm = max([abs(a) for a in row] + [0]), max(mags + [0])
    out.r += delta * sum(mags) + len(row) * (Wm + 1) * (Xm + 1) / 2 ** 16 + F(1, 2 ** 100)
    return out


def check(net, tname, delta=DELTA, table=None):
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
    if max(abs(v) for v in allw) > SMALL: return False, "a written weight is larger than 15", {}
    e0 = delta + RND; xe = [e0] * d; sw = delta + RND
    heads = []
    for k, h in enumerate(B["heads"]):
        if h["mask"] not in ("strict", "causal"): return False, f"head {k}: mask not supported", {}
        A, V, g, gb, m = Q(h["A"]), Q(h["V"]), [F(v) for v in h["g"]], F(h["gb"]), F(h["m"])
        if m < 1 or m > 1024: return False, f"head {k}: slope out of range", {}
        cand = []
        for t in range(ntok):
            c, e = RC.dot_w(g, E[t], xe, delta); c += gb; e += sw + RND
            if abs(c) + e > SMALL: return False, f"head {k}: gate of token {t} fails the magnitude guard", {}
            if c + e < 0: cand.append(True)
            elif c - e > 0: cand.append(False)
            else: return False, f"head {k}: gate of token {t} not decided", {}
        cs = [t for t in range(ntok) if cand[t]]
        AE = [[RC.dot_w(r, E[t], xe, delta) for r in A] for t in range(ntok)]
        S = {}
        for q in range(1, ntok):
            Xq = max(abs(v) for v in E[q])
            for t in cs:
                Y = max(abs(c) for c, _ in AE[t]); e2 = max(e for _, e in AE[t])
                cen = sum(E[q][i] * AE[t][i][0] for i in range(d))
                err = d * (e0 * (Y + e2) + Xq * e2) + d * (Xq + e0 + 1) * (Y + e2 + 1) / 2 ** 16 + F(1, 2 ** 100)
                if (Xq + e0 + 1) * (Y + e2 + 1) > 2 ** 20 or abs(cen) + err > 1024:
                    return False, f"head {k}: content score of query {q}, key {t} fails the range guard", {}
                S[q, t] = (cen, err)
        spread = max([S[q, b][0] - S[q, a][0] + S[q, a][1] + S[q, b][1] for q in range(1, ntok) for a in cs for b in cs] + [F(0)])
        sigma = (m + 2) / 32 + (m + 2) / 128 + F(1, 2 ** 11)
        L = next((l for l in range(1, LMAX + 1) if (m - delta) * l - spread - sigma >= TAILEXP), None)
        if L is None:
            return False, f"head {k}: content score spread {float(spread):.2f} too large for a window of {LMAX} at slope {float(m):g}", {}
        VE = [[RC.dot_w(r, E[t], xe, delta) for r in V] for t in range(ntok)]
        Bv = [max([abs(VE[t][r][0]) + VE[t][r][1] for t in cs] + [0]) for r in range(d)]
        if max(Bv + [0]) > 2 ** 20: return False, f"head {k}: value bound too large", {}
        tail = exp_iv(-((m - delta) * L - spread - sigma))[1] * F(101, 100)      # geometric sum of older keys
        dense = all(cand)
        # A dense head (every token a candidate) has its window keys at known distances 0..L+1 from the query,
        # so their position biases are at most (m + 1) * (L + 2) in size and one rounding of bias or score
        # costs at most 2^-24 * ((m + 1) * (L + 2) + 1024) + eta: far below 2^-11. PROOF OBLIGATION P1.
        sig_win = F(1, 2 ** 10) if dense else sigma
        # Softmax arithmetic in a dense head: the rounded sums run oldest key first, weights grow geometrically
        # toward the newest keys, so the accumulated rounding is a few units of u times the value bound, not
        # u * n. Charged here as B / 2^16. PROOF OBLIGATION P2. Gated heads keep the proved B / 100.
        soft = [b / 2 ** 16 for b in Bv] if dense else [b / 100 for b in Bv]
        heads.append(dict(k=k, mask=h["mask"], cand=cand, m=m, S=S, VE=VE, Bv=Bv, L=L, sigma=sig_win, tail=tail,
                          dense=dense, spread=spread, soft=soft))
    s0, step, outp = RC.task_dfa(tname)

    def head_out(hd, q, keys):
        """affine forms of the head output for query token q and key tokens `keys` (newest first; for a dense
        head at consecutive positions). Returns (list of AF, description of the weights)."""
        if not keys: return [AF() for _ in range(d)], []
        full = len(keys) >= hd["L"] + (1 if hd["mask"] == "causal" and hd["cand"][q] else 0)
        # reference key: the newest one; in a dense head (known spacing) the one with the highest nominal score
        nom = [-hd["m"] * rank + hd["S"][q, keys[rank]][0] for rank in range(len(keys))]
        ref = max(range(len(keys)), key=lambda i: nom[i]) if hd["dense"] else 0
        c1, r1 = hd["S"][q, keys[ref]]
        w, idx = [], []
        for rank in range(len(keys)):
            if rank == ref: continue
            ck, rk = hd["S"][q, keys[rank]]
            dist = rank - ref                             # positions behind the reference (minimum if gated)
            hi_e = -hd["m"] * dist + delta * abs(dist) + (ck - c1) + rk + r1 + hd["sigma"]
            lo_e = -hd["m"] * dist - delta * abs(dist) + (ck - c1) - rk - r1 - hd["sigma"]
            if hi_e > 6: return None, f"a key outscores the reference by more than e^6"
            rhi = exp_iv(hi_e)[1]
            rlo = exp_iv(lo_e)[0] if hd["dense"] else F(0)
            w.append([rlo, rhi]); idx.append(rank)
        tl = (hd["tail"] * 3) if full else F(0)          # older keys, relative to the reference (factor 3: radii)
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
    init = (s0, tuple((0,) if hd["cand"][0] else () for hd in heads))
    seen, todo = {init}, [init]
    mixed = 0
    while todo:
        s, wins = todo.pop()
        for t in range(1, ntok):
            sel = tuple((((t,) if (hd["mask"] == "causal" and hd["cand"][t]) else ()) + wn) for hd, wn in zip(heads, wins))
            key = (t, sel)
            if key not in cache:
                y = [AF(E[t][r], None, e0) for r in range(d)]
                ok, why, mx = True, "", False
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
                        p = p.fold(("eh", hh))
                        lo, hi = p.lo(), p.hi()
                        if lo >= 0: hid.append(p)
                        elif hi <= 0: hid.append(AF())
                        else:
                            lam = hi / (hi - lo); mu = -lam * lo / 2
                            q2 = p.scale(lam); q2.c += mu; q2.t[("rl", hh)] = mu
                            hid.append(q2)
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
                return False, f"case token {t}, keys {sel}: {why}", {}
            tg = outp(s, t); ncase += 1
            bound = abs(o.c - tg) + o.dev()
            worst = max(worst, bound)
            if bound > TOL:
                return False, (f"case token {t}, keys {sel}, task state {s}: output {float(o.c):.4f} +- {float(o.dev()):.4f} "
                               f"against target {tg}" + (" (mixed attention)" if mx else "")), dict(worst=float(bound))
            nxt = (step(s, t), tuple((((t,) + wn) if hd["cand"][t] else wn)[:hd["L"]] for hd, wn in zip(heads, wins)))
            if nxt not in seen: seen.add(nxt); todo.append(nxt)
    if table is not None: table.update(cache); table["__heads__"] = heads
    return True, "ok", dict(worst=float(worst), states=len(seen), table_rows=len(cache), cases=ncase,
                            window=[hd["L"] for hd in heads], spread=[round(float(hd["spread"]), 2) for hd in heads],
                            dense=[hd["dense"] for hd in heads], mixed_rows=mixed)


if __name__ == "__main__":
    if sys.argv[1] == "--k1":
        res = {}
        for task, rec, lo, hi in (("A", "u3", 100, 119), ("B", "u5", 100, 139)):
            rows = []
            scr = [json.load(open(os.path.join(HERE, "runs", "r7-stage0", task, rec, "s%d" % s, "screen.json"))) for s in range(lo, hi + 1)]
            for j in sorted(scr, key=lambda j: (j["seed"] >= 120, j["nonzero_W"], j["seed"])):
                if not j.get("pass"): continue
                dd = os.path.join(HERE, "runs", "r7-stage0", task, rec, "s%d" % j["seed"])
                ok, why, info = check(json.load(open(os.path.join(dd, "W.json"))), task)
                r7ok = RC.check(json.load(open(os.path.join(dd, "W.json"))), task, verbose=False)[0]
                rows.append(dict(seed=j["seed"], ok=ok, r7_ok=r7ok, reason=why, **info))
                print(task, rec, j["seed"], "ACCEPT" if ok else "reject", "| rung 7:", "accept" if r7ok else "reject", "|", why[:150],
                      "|", {k: v for k, v in info.items() if k in ("worst", "window", "spread", "mixed_rows", "states")}, flush=True)
            res["%s/%s" % (task, rec)] = rows
            print(task, rec, "accepted", sum(r["ok"] for r in rows), "of", len(rows), flush=True)
        json.dump(res, open(os.path.join(HERE, "results", "rung8-k1.json"), "w"), indent=1)
    else:
        dd = sys.argv[1]
        tname = json.load(open(os.path.join(dd, "train.json")))["task"]
        ok, why, info = check(json.load(open(os.path.join(dd, "W.json"))), tname)
        print(json.dumps(dict(dir=dd, ok=ok, reason=why, **info)))
