"""Sanity check for PREREG_R6.md BEFORE any proof (exact rationals, pure Python, small).

For the three proved rung-2 parity networks p05, p10, p29:
 (1) closed form: with the block-1 value weight scaled by (1+d), the output at the last
     position is  c * avg_{j in argmax}(-1)^j,  argmax over j < n of  a*z*j - b*j^2/n,
     z = (1+d)*k/n.  Checked against the exact evaluator tools/seqnet.py at length 30
     and (collision pair only) at length 100.
 (2) the collision pair of the statement at tau = 1/(2L-1): inputs of length L with
     k = L-1 and k+1 = L counted tokens, d1 = (1 - tau*L)/(L-1), d2 = -tau: equal outputs.
 (3) the smallest value-weight-only radius with a break at length L (closed form, scan
     over k and both signs of d at the extreme corner and at every tie point).
 (4) the same with EVERY nonzero weight on the count path moved (factor rho up to
     (1+t)^3/(1-t)): smallest radius with a break, for comparison with the 2x2 v2 rows
     (relative 1/200: no break found at lengths <= 20, breaks found at 100 and 1,000).
"""
import copy, json, os, sys
from fractions import Fraction as F
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tools"))
import seqnet as S, collect2_lib as CL

HERE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
NETS = {"p05": ([1, 3, 4], 2, 0), "p10": ([1, 2], 3, 0), "p29": ([2, 3], 1, 1)}   # counted tokens, other token, wanted parity


def consts(net):
    h1, h2 = net["blocks"][0]["heads"][0], net["blocks"][1]["heads"][0]
    return h2["A"][1][4], -h2["A"][9][5], net["outW"][2] * h2["V"][2][7]


def closed_brute(net, n, z):
    a, b, c = consts(net)
    sc = [a * z * j - b * F(j * j, n) for j in range(n)]
    m = max(sc)
    sel = [j for j in range(n) if sc[j] == m]
    return c * sum(F(-1) ** j for j in sel) / len(sel)


def closed(net, n, z):
    """Same value without the scan: the score is a concave parabola in j with vertex x."""
    a, b, c = consts(net)
    x = a * z * n / (2 * b)
    lo = x.numerator // x.denominator
    cands = [j for j in (lo - 1, lo, lo + 1, lo + 2, 0, n - 1) if 0 <= j < n]
    sc = {j: a * z * j - b * F(j * j, n) for j in cands}
    m = max(sc.values())
    sel = [j for j in sc if sc[j] == m]
    return c * sum(F(-1) ** j for j in sel) / len(sel)


def scaled(net, d):
    N = copy.deepcopy(net)
    N["blocks"][0]["heads"][0]["V"][1][0] *= (1 + d)
    return N


def good(k, par):
    return k % 2 == par


def wrong(out, k, par):
    return (out > 0) != good(k, par)


res = {}
for name, (cnt, other, par) in NETS.items():
    net = CL.load_net(os.path.join(HERE, "runs", "rung2-test", "net", name, "net.json"))
    a, b, c = consts(net)
    r = {"a": str(a), "b": str(b), "c": str(c)}
    # (1) closed form against the exact evaluator, length 30, several k and d
    ok = True
    for k in (0, 1, 7, 29, 30):
        for d in (F(0), F(1, 200), F(-1, 200), F(1, 14), F(1, 58)):
            w = [cnt[i % len(cnt)] for i in range(k)] + [other] * (30 - k)
            w = w[::-1] if k % 3 == 0 else w
            ok &= S.run(scaled(net, d), w)[-1] == closed(net, 31, (1 + d) * F(k, 31)) == closed_brute(net, 31, (1 + d) * F(k, 31))
    r["closed_form_matches_evaluator_len30"] = ok
    for L in (20, 100, 1000):
        n = L + 1
        tau = F(1, 2 * L - 1)
        d1, d2 = (1 - tau * L) / (L - 1), -tau
        assert abs(d1) <= tau
        o1 = closed(net, n, (1 + d1) * F(L - 1, n))
        o2 = closed(net, n, (1 + d2) * F(L, n))
        row = {"collision_equal_outputs": o1 == o2, "collision_out": str(o1),
               "one_is_wrong": wrong(o1, L - 1, par) or wrong(o2, L, par)}
        if L == 100:
            w1 = [cnt[0]] * (L - 1) + [other]
            w2 = [cnt[0]] * L
            e1, e2 = S.run(scaled(net, d1), w1)[-1], S.run(scaled(net, d2), w2)[-1]
            row["evaluator_agrees"] = (e1 == o1 and e2 == o2)
        # (3),(4): smallest radius t such that some k <= L and some factor rho in [lo(t), hi(t)] breaks.
        # Output depends on rho*k only; a break needs rho*k >= k + 1/2 or <= k - 1/2 (tie or wrong peak)
        # when the correct answer at k is "positive", or a strict move past the tie otherwise.
        def breaks(t, hi, lo):
            for k in range(1, L + 1):
                for rho in (hi(t), lo(t)):
                    if wrong(closed(net, n, rho * F(k, n)), k, par):
                        return True
            return False
        def smallest(hi, lo):
            lo_t, hi_t = F(0), F(1, 2)
            for _ in range(40):
                mid = (lo_t + hi_t) / 2
                if breaks(mid, hi, lo):
                    hi_t = mid
                else:
                    lo_t = mid
            return hi_t
        t1 = smallest(lambda t: 1 + t, lambda t: 1 - t)
        t4 = smallest(lambda t: (1 + t) ** 3 / (1 - t), lambda t: (1 - t) ** 3 / (1 + t))
        row["value_weight_only_break_radius_times_L"] = float(t1 * L)
        row["count_path_all_weights_break_radius_times_L"] = float(t4 * L)
        row["statement_radius_times_L"] = float(tau * L)
        row["statement_radius"] = "1/%d" % (2 * L - 1)
        row["break_at_rel_1_200_value_weight_only"] = breaks(F(1, 200), lambda t: 1 + t, lambda t: 1 - t)
        row["break_at_rel_1_200_count_path"] = breaks(F(1, 200), lambda t: (1 + t) ** 3 / (1 - t), lambda t: (1 - t) ** 3 / (1 + t))
        r["L=%d" % L] = row
    res[name] = r
    print(name, json.dumps(r, indent=1), flush=True)
json.dump(res, open(os.path.join(HERE, "results", "r6-collision-sanity.json"), "w"), indent=1)
