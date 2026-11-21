"""Rung 7 certificate checker, Python prototype in exact rationals (PREREG_R7.md Amendment 2).

Mirrors the Lean evaluator to be proved sound: per-token intervals (centre, radius) pushed through the one-block
gated architecture with the kit's own error terms (asw_near, ardot_near_w, pdot_near, bias_gap, soft_near), then a
closed set of abstract cases (task state, token picked by each head) checked against the task's automaton.
The certificate is computed from the network alone: candidate token sets and the closed case set.

usage: python tools/r7_cert.py <run dir> [--net W.json] [--radius-mult k] [--quiet]
"""
import json, sys, os
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

DELTA = F(1, 1000)
RND = F(1, 2 ** 20)          # one rounding of a quantity of size <= 16 (u <= 2^-24)
TINY = F(1, 2 ** 90)
TOL = F(1, 4)
SMALL = 15                   # magnitude guard (Amendment 3): every rounded quantity is at most 15, so RND covers its rounding
GAP = 12                     # score gap per position the softmax lemma needs (kit lemma to be proved: SavgNear12)


def task_dfa(name):
    """(initial state, step(state, token), out(state, token)); tokens 1..5."""
    if name == "A":
        return 0, (lambda s, t: t - 1), (lambda s, t: ((t - 1) + s) % 5)
    cls, dg = [0, 1, 2, 0, 0], [2, 0, 2, 2, 0]      # pool case c01
    return 0, (lambda s, t: s if cls[t - 1] == 2 else cls[t - 1]), (lambda s, t: (dg[t - 1] + s) % 3)


def dot_w(row, xc, xe, delta):
    """ardot_near_w: centre and error of a stored-weight row applied to a vector known to (xc, xe)."""
    c = sum(a * x for a, x in zip(row, xc))
    Xs = [abs(x) for x in xc]
    werr = sum(abs(a) * e + delta * (X + e) for a, e, X in zip(row, xe, Xs))
    Wm, Xm, em = max([abs(a) for a in row] + [0]), max(Xs + [0]), max(xe + [0])
    return c, werr + len(row) * (Wm + 1) * (Xm + em + 1) / 2 ** 16 + F(1, 2 ** 100)


def check(net, tname, delta=DELTA, verbose=True):
    """Returns (ok, reason, info)."""
    Q = lambda m: [[F(v) for v in r] for r in m]
    E = Q(net["embed"]); ntok = len(E); d = len(E[0])
    if len(net["blocks"]) != 1: return False, "more than one block", {}
    B = net["blocks"][0]
    W1 = [F(v) for r in B["W1"] for v in (r if isinstance(r, list) else [r])]
    H = len(B["b1"]); W1 = [W1[i * d:(i + 1) * d] for i in range(H)]
    W2, b1, b2 = Q(B["W2"]), [F(v) for v in B["b1"]], [F(v) for v in B["b2"]]
    oW, oB = [F(v) for v in net["outW"]], F(net["outB"])
    allw = [v for r in E for v in r] + [v for r in W1 for v in r] + [v for r in W2 for v in r] + b1 + b2 + oW + [oB]
    for h in B["heads"]:
        allw += [F(v) for r in h["A"] for v in r] + [F(v) for r in h["V"] for v in r] + [F(v) for v in h["g"]] + [F(h["gb"])]
    if max(abs(v) for v in allw) > SMALL: return False, "a written weight is larger than 15 (magnitude guard)", {}
    e0 = delta + RND                                   # stored embedding entry (asw_near)
    xe = [e0] * d
    sw = delta + RND                                   # a stored bias
    heads = []
    for k, h in enumerate(B["heads"]):
        if h["mask"] not in ("strict", "causal"): return False, f"head {k}: mask {h['mask']} not supported", {}
        A, V, g, gb, m = Q(h["A"]), Q(h["V"]), [F(v) for v in h["g"]], F(h["gb"]), F(h["m"])
        cand = []
        for t in range(ntok):
            c, e = dot_w(g, E[t], xe, delta); c += gb; e += sw + RND
            if abs(c) + e > SMALL: return False, f"head {k}: gate of token {t} fails the magnitude guard", {}
            if c + e < 0: cand.append(True)
            elif c - e > 0: cand.append(False)
            else: return False, f"head {k}: gate of token {t} not decided (pre {float(c):.4f}, slack {float(e):.4f})", {}
        # content score bounds: pdot(x_q, armat(A, x_t)) by pdot_near with uniform bounds
        AE = [[dot_w(r, E[t], xe, delta) for r in A] for t in range(ntok)]
        X = max(abs(v) for row in E for v in row)
        S = [[None] * ntok for _ in range(ntok)]
        for q in range(ntok):
            for t in range(ntok):
                Y = max(abs(c) for c, _ in AE[t]); e2 = max(e for _, e in AE[t])
                cen = sum(E[q][i] * AE[t][i][0] for i in range(d))
                err = d * (e0 * (Y + e2) + X * e2) + d * (X + e0 + 1) * (Y + e2 + 1) / 2 ** 16 + F(1, 2 ** 100)
                S[q][t] = (cen, err)
                Xq, e1q = max(abs(v) for v in E[q]), e0
                S[q][t] = (cen, d * (e1q * (Y + e2) + Xq * e2) + d * (Xq + e1q + 1) * (Y + e2 + 1) / 2 ** 16 + F(1, 2 ** 100),
                           (Xq + e1q + 1) * (Y + e2 + 1) <= 2 ** 20)
        need = m - delta - GAP - 3 * (m + 2) / 64      # slope left after the gap and rounding (bias_gap)
        cs = [t for t in range(ntok) if cand[t]]
        for q in range(1, ntok):
            for a in cs:
                if not S[q][a][2] or abs(S[q][a][0]) + S[q][a][1] > 1024:
                    return False, f"head {k}: content score of query token {q}, key {a} fails the range guard", {}
        for q in range(1, ntok):
            for a in cs:
                for b in cs:
                    if S[q][b][0] - S[q][a][0] + S[q][a][1] + S[q][b][1] > need:
                        return False, (f"head {k}: content score spread {float(S[q][b][0] - S[q][a][0]):.3f} for query token {q} "
                                       f"(keys {a},{b}) leaves no gap of {GAP} per position (allowed {float(need):.3f})"), {}
        if m < 1 or m > 1024: return False, f"head {k}: slope out of range", {}
        VE = [[dot_w(r, E[t], xe, delta) for r in V] for t in range(ntok)]
        Bv = [max([abs(VE[t][r][0]) + VE[t][r][1] for t in cs] + [0]) for r in range(d)]
        if max(Bv + [0]) > 2 ** 20: return False, f"head {k}: value bound too large", {}
        heads.append(dict(mask=h["mask"], cand=cand, VE=VE, Bv=Bv))
    s0, step, outp = task_dfa(tname)
    # closed set of abstract states before reading the next token: (task state, strict pick of each head)
    init = (s0, tuple(0 if hd["cand"][0] else None for hd in heads))
    seen, todo, worst, ncase, ndot = {init}, [init], F(0), 0, 0
    cache = {}
    while todo:
        s, picks = todo.pop()
        for t in range(1, ntok):
            sel = tuple(t if (hd["mask"] == "causal" and hd["cand"][t]) else p for hd, p in zip(heads, picks))
            key = (t, sel)
            if key not in cache:
                yc, ye = list(E[t]), list(xe)
                guard = True
                for hd, p in zip(heads, sel):
                    for r in range(d):
                        if p is None: hc, he = F(0), F(0)
                        else: hc, he = hd["VE"][p][r][0], hd["VE"][p][r][1] + hd["Bv"][r] / 100 + TINY
                        yc[r] += hc; ye[r] += he + RND
                    guard = guard and all(abs(c_) + e_ <= SMALL for c_, e_ in zip(yc, ye))
                hc, he = [], []
                for r in range(H):
                    c, e = dot_w(W1[r], yc, ye, delta); c += b1[r]; e += sw + RND
                    guard = guard and abs(c) + e <= SMALL
                    lo, hi = max(c - e, 0), max(c + e, 0)
                    hc.append((lo + hi) / 2); he.append((hi - lo) / 2)
                zc, ze = [], []
                for r in range(d):
                    c, e = dot_w(W2[r], hc, he, delta); c += b2[r]; e += sw + RND
                    guard = guard and abs(c) + e <= SMALL
                    zc.append(yc[r] + c); ze.append(ye[r] + e + RND)
                    guard = guard and abs(zc[-1]) + ze[-1] <= SMALL
                c, e = dot_w(oW, zc, ze, delta); c += oB; e += sw + RND
                guard = guard and abs(c) + e <= SMALL
                cache[key] = (c, e, guard); ndot += H + d + 1
            c, e, guard = cache[key]
            if not guard:
                return False, f"case token {t}, picks {sel}: a rounded quantity fails the magnitude guard (15)", {}
            tg = outp(s, t); ncase += 1
            bound = abs(c - tg) + e
            worst = max(worst, bound)
            if bound > TOL:
                return False, (f"case token {t}, picks {sel}, task state {s}: output {float(c):.4f} +- {float(e):.4f} "
                               f"against target {tg}"), dict(worst=float(bound))
            nxt = (step(s, t), tuple(t if hd["cand"][t] else p for hd, p in zip(heads, picks)))
            if nxt not in seen: seen.add(nxt); todo.append(nxt)
    info = dict(worst=float(worst), states=len(seen), table_rows=len(cache), cases=ncase,
                cands=[[t for t in range(ntok) if hd["cand"][t]] for hd in heads])
    return True, "ok", info


if __name__ == "__main__":
    d = sys.argv[1]
    f = "W.json"
    if "--net" in sys.argv: f = sys.argv[sys.argv.index("--net") + 1]
    mult = F(sys.argv[sys.argv.index("--radius-mult") + 1]) if "--radius-mult" in sys.argv else 1
    tname = json.load(open(os.path.join(d, "train.json")))["task"]
    ok, why, info = check(json.load(open(os.path.join(d, f))), tname, DELTA * mult)
    print(json.dumps(dict(dir=d, ok=ok, reason=why, **info)))
