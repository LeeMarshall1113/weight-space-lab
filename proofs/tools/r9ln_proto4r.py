"""Rung 9-LN feasibility step after K2: design 4 with FEWER SYMBOLS. Python only, tuning networks only.
The registered rung stays stopped at K2; this file is not part of it and registers nothing.

A group of symbols may be replaced by ONE fresh symbol whose coefficient is the sum of the absolute coefficients
(sound always: the fresh symbol is a new quantity in [-1, 1] used by this one form). It loses nothing when the
group reaches the output only through this form; otherwise it gives up the correlation.

  mode 1  merges that lose nothing: W1 row + b1 -> one symbol per hidden unit; W2 row + b2 -> one per coordinate;
          LN2 gain + bias -> one per coordinate; LNf gain and bias, oW, oB -> straight to the radius.
  mode 2  mode 1, and each head value VA[head][token][coord] gets one symbol (absorbing V, LN1 gain/bias and the
          key's embedding symbols; gives up their correlation across coordinates and with the query's residual);
          after the attention mix, one symbol per (head, coord).
  mode 3  mode 2, and LN2 gain/bias and the attention-weight symbols go to the radius.
  mode 4  mode 3, and the W1 symbols go to the radius.
  mode 5  mode 2 after the heads, but the HEADS ARE RUNG 8's, unchanged (tools/r9_proto.py head_tables and head_out,
          the mirror of headOK8 / headAF with their absolute rounding charges), applied to the LN1 boxes: value
          deviations go to the radius. If this holds, Lane4.R8KG.head_sound8 is reused without a new proof.
  mode 6  as mode 5 with design 3's relative charges in the head tables (isolates which part matters).
  mode 7  mode 5, then the whole RADIUS of each head-output coordinate becomes one fresh symbol (the same
          enclosure of that coordinate; later steps keep its sign). head_sound8 still reused unchanged.
  mode 8  mode 6 with the same radius-to-symbol step.
  mode 9  mode 7 with rung 8's score tables kept and only the VALUE tables on relative charges.

    python tools/r9ln_proto4r.py tune <recipe> <seed0> <seed1> --mode m [--radius r] [--itest]
"""
import json, os, sys, time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(HERE, "tools"))
import r9_proto as P9, r7_cert as RC, r9ln_proto as L3, r9ln_proto4 as P4

Reject, A4, mul, relu4 = P9.Reject, P4.A4, P4.mul, P4.relu4
TOL, SMALL, EPS, URel, T0 = P4.TOL, P4.SMALL, P4.EPS, P4.URel, P4.T0
MODE = 1


def bump(o, name, v):
    """add v >= 0 to symbol name, or to the radius when name is None"""
    if v == 0: return
    if name is None: o.r += v
    else: o.t[name] = o.t.get(name, 0) + v


def merge(o, pred, name):
    s = F(0)
    for k in [k for k in o.t if pred(k)]:
        s += abs(o.t.pop(k))
    bump(o, name, s)
    return o


def wdot1(name, row, xs, bias, delta):
    """row . xs + bias; the ball on the row and the bias as ONE symbol `name` (or the radius)"""
    out = A4()
    for a, x in zip(row, xs): out = out.add(x.scale(a))
    mags = [x.mag() for x in xs]
    out.r += delta * sum(x.dev() for x in xs) + (len(row) + 2) * URel * 2 * sum((abs(a) + delta) * m for a, m in zip(row, mags)) + T0
    out.snap()
    out.c += bias
    bump(out, name, delta * (sum(abs(x.c) for x in xs) + 1))
    out.r += URel * out.mag() + T0
    return out.snap()


def ln4r(xs, lname, g, b, delta, where, gb):
    """tools/r9ln_proto4.py ln4; gb = 'sep' (as there), 'sym' (one symbol per coordinate), 'rad' (radius)"""
    if gb == "sep": return P4.ln4(xs, lname, g, b, delta, where)
    outs, vmin = P4.ln4(xs, lname, g, b, delta, where)
    for k, o in enumerate(outs):
        merge(o, lambda n, k=k: n in ((lname, "g", k), (lname, "b", k)), (lname, k) if gb == "sym" else None)
    return outs, vmin


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
            Hs[t], _ = P4.ln4(res(t), "ln1", *LN["ln1"], delta, f"LN1 token {t}")
            boxes[t] = ([a.c for a in Hs[t]], [a.dev() for a in Hs[t]])
        M2 = 2 if MODE >= 5 else MODE
        if MODE in (5, 7): heads = [P9.head_tables(0, k, h, boxes, list(range(1, ntok)), delta, d) for k, h in enumerate(P1["heads"])]
        else: heads = [L3.head_tables2(k, h, boxes, list(range(1, ntok)), delta, d) for k, h in enumerate(P1["heads"])]
        if MODE == 9:
            heads = [P9.head_tables(0, k, h, boxes, list(range(1, ntok)), delta, d) for k, h in enumerate(P1["heads"])]
            for k, h in enumerate(P1["heads"]):
                t2 = L3.head_tables2(k, h, boxes, list(range(1, ntok)), delta, d)
                heads[k].update(VE=t2["VE"], Bv=t2["Bv"], soft=t2["soft"])
        info["window"] = [hd["L"] for hd in heads]
        VA = []
        for k, h in enumerate(P1["heads"] if MODE < 5 else []):
            va = {}
            for t in range(ntok):
                va[t] = [P4.wdot([("V", k, r, i) for i in range(d)], h["V"][r], Hs[t], delta) for r in range(d)]
                if MODE >= 2:
                    for r in range(d): merge(va[t][r], lambda n: True, ("VA", k, t, r) if delta else None)
            VA.append(va)
        s0, step, outp = RC.task_dfa("A")
        init = (s0, tuple((0,) for _ in heads))
        seen, todo, cache, worst, ncase = {init: 0}, [init], {}, F(0), 0
        gb2 = "sym" if M2 <= 2 else "rad"
        w1name = (lambda hh: ("W1", hh)) if M2 <= 3 else (lambda hh: None)
        nsym = 0
        while todo:
            s, wins = todo.pop()
            for t in range(1, ntok):
                sel = tuple((((t,) + wn) if hd["mask"] == "causal" else wn) for hd, wn in zip(heads, wins))
                key = (t, sel)
                if key not in cache:
                    y = res(t)
                    for hd, keys in zip(heads, sel):
                        if MODE >= 5:
                            ho8, desc = P9.head_out(hd, t, keys, delta, d)
                            ho = [A4(a.c, dict(a.t), a.r).snap() for a in ho8]
                            if MODE >= 7:
                                for r in range(d):
                                    if ho[r].r: ho[r].t[("HO", hd["k"], r)] = ho[r].r; ho[r].r = F(0)
                        else:
                            ho, desc = P4.head_out4(hd, VA[hd["k"]], t, keys, delta, d)
                        for r in range(d):
                            if MODE >= 5: break
                            if MODE >= 2: merge(ho[r], lambda n: n[0] == "VA", ("HO", hd["k"], r))
                            if MODE >= 3: merge(ho[r], lambda n: n[0] == "a", None)
                        y = [a.add(b_) for a, b_ in zip(y, ho)]
                        for a in y: a.r += URel * a.mag() + T0
                        if any(a.mag() > SMALL for a in y): raise Reject("residual stream fails the magnitude guard")
                    y2, _ = ln4r(y, "ln2", *LN["ln2"], delta, "LN2", gb2)
                    hid = [relu4(wdot1(w1name(hh), P1["W1"][hh], y2, P1["b1"][hh], delta)) for hh in range(P1["H"])]
                    z = []
                    for r in range(d):
                        zz = y[r].add(wdot1(("W2", r), P1["W2"][r], hid, P1["b2"][r], delta)); zz.r += URel * zz.mag() + T0
                        z.append(zz.snap())
                    zf, _ = ln4r(z, "lnf", *LN["lnf"], delta, "LNf", "rad")
                    o = wdot1(None, oW, zf, oB, delta)
                    nsym = max(nsym, max(len(a.t) for a in z), max(len(a.t) for a in y2))
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
        info.update(worst=float(worst), states=len(seen), table_rows=len(cache), cases=ncase, symbols=nsym)
        if table is not None: table.update(cache={k: (v[0], False) for k, v in cache.items()}, heads=heads, init=init)
        return True, "ok", info
    except Reject as e:
        return False, str(e), info


if __name__ == "__main__":
    import r5_checks as C5
    C5.memory_guard(2.5)
    a = sys.argv
    RAD = F(a[a.index("--radius") + 1]) if "--radius" in a else F(1, 2 ** 15)
    MODE = int(a[a.index("--mode") + 1])
    rows = []
    for seed in range(int(a[3]), int(a[4]) + 1):
        dd = os.path.join(HERE, "runs", "r9ln-tune", "A", a[2], "s%03d" % seed)
        sj = json.load(open(os.path.join(dd, "screen.json")))
        row = dict(seed=seed, s1_ok=sj["s1_ok"], screen=sj["pass"], mode=MODE)
        if sj["pass"]:
            t0 = time.time(); table = {}
            Wq = json.load(open(os.path.join(dd, "W14.json")))
            ok, why, info = check(Wq, RAD, table)
            row.update(ok=ok, reason=why, secs=round(time.time() - t0, 1), **info)
            if ok and "--itest" in a:
                row["interval_test"] = L3.interval_test(Wq, RAD, seed, table)
        rows.append(row)
        print("A-LN %s s%03d mode %d | screen %s |" % (a[2], seed, MODE, sj["pass"]),
              ("-" if not sj["pass"] else ("ACCEPT worst %.3f rows %d, %d symbols" % (row["worst"], row["table_rows"], row["symbols"]) if row["ok"] else "reject: " + row["reason"][:150])),
              "| %s s |" % row.get("secs"), row.get("interval_test", ""), flush=True)
        json.dump(rows, open(os.path.join(HERE, "results", "rung9ln-proto4r-m%d-%s-r%s.json" % (MODE, a[2], str(RAD).replace("/", "_"))), "w"), indent=1)
    sc = [r for r in rows if r["screen"]]
    acc = [r for r in sc if r.get("ok")]
    print("mode %d radius %s | screened %d | accepts %d | symbols max %s median %s | interval-test violations %d" % (
        MODE, RAD, len(sc), len(acc), max([r["symbols"] for r in acc] or [0]),
        sorted(r["symbols"] for r in acc)[len(acc) // 2] if acc else "-", sum(r.get("interval_test", {}).get("violations", 0) for r in sc)))
