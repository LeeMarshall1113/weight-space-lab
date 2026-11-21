"""Mechanism row (b), PREREG_MECH.md: read a finite-state program off a one-block UNGATED network's weights.
The finder is NOT given the task: it imports no task definition. RUN UNDER reservation wrapper.

    python tools/mech_extract.py <W14.json> [--radius 1/16384]      -> prints the program as JSON
    from mech_extract import extract                                 (used by tools/make_mech_net.py)

Rule (PREREG_MECH.md): enumerate the reachable window states as the rung-8 checker does; for each state and next
token the read-out enclosure (centre c, deviation d) gives the integer n nearest to c, and the extraction FAILS
if |c - n| + d > 1/4 for any row; the Mealy machine on window states is minimised by partition refinement and
its states numbered in order of first visit from the initial state.

The enclosure arithmetic is that of the rung-8 mirror for dense heads, taken from tools/r9_proto.py (block one
with tokens as classes). It only PROPOSES a program: the frozen rung-8 checker, in the kernel, decides whether
the network is within 1/4 of that program.
"""
import json, os, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(HERE, "tools"))
import r9_proto as P9

AF, dot_af, RND, TOL, SMALL = P9.AF, P9.dot_af, P9.RND, P9.TOL, P9.SMALL


def extract(net, delta):
    """Returns (ok, reason, program, info). program = dict(ntok, init, step, out) with step[s][t-1], out[s][t-1]."""
    info = {}
    try:
        Q = lambda m: [[F(v) for v in r] for r in m]
        E = Q(net["embed"]); ntok = len(E); d = len(E[0])
        if len(net["blocks"]) != 1: raise P9.Reject("not one block")
        P1 = P9.parse_block(net["blocks"][0], d)
        oW, oB = [F(v) for v in net["outW"]], F(net["outB"])
        e0 = delta + RND; sw = delta + RND
        boxes = {t: (E[t], [e0] * d) for t in range(ntok)}
        heads = [P9.head_tables(1, k, h, boxes, list(range(1, ntok)), delta, d) for k, h in enumerate(P1["heads"])]
        info["window"] = [hd["L"] for hd in heads]
        init = tuple((0,) for _ in heads)
        order, todo, rows = {init: 0}, [init], {}
        k = 0
        while k < len(todo):                      # breadth-first, tokens ascending: a fixed visiting order
            wins = todo[k]; k += 1
            for t in range(1, ntok):
                sel = tuple((((t,) + wn) if hd["mask"] == "causal" else wn) for hd, wn in zip(heads, wins))
                z, _ = P9.block_case(1, P1, heads, [AF(E[t][r], None, e0) for r in range(d)], t, sel, delta, d)
                o = dot_af(oW, z, delta); o.c += oB; o.r += sw + RND
                n = round(o.c)
                if abs(o.c - n) + o.dev() > TOL:
                    raise P9.Reject(f"row windows {wins}, token {t}: read-out {float(o.c):.4f} +- {float(o.dev()):.4f} is not within 1/4 of an integer")
                if n < 0: raise P9.Reject(f"row windows {wins}, token {t}: nearest integer {n} is negative")
                nxt = tuple(((t,) + wn)[:hd["L"]] for hd, wn in zip(heads, wins))
                if nxt not in order: order[nxt] = len(order); todo.append(nxt)
                rows[wins, t] = (int(n), nxt)
        info["window_states"] = len(order); info["window_rows"] = len(rows)
        # partition refinement on the Mealy machine
        toks = list(range(1, ntok))
        part = {w: tuple(rows[w, t][0] for t in toks) for w in order}
        while True:
            new = {w: (part[w], tuple(part[rows[w, t][1]] for t in toks)) for w in order}
            if len(set(new.values())) == len(set(part.values())): break
            part = new
        ids = {}
        q, queue, seen = 0, [init], {init}
        while q < len(queue):                     # number classes in order of first visit from the initial state
            w = queue[q]; q += 1
            if part[w] not in ids: ids[part[w]] = len(ids)
            for t in toks:
                nx = rows[w, t][1]
                if nx not in seen: seen.add(nx); queue.append(nx)
        ns = len(ids)
        step, out = [[None] * len(toks) for _ in range(ns)], [[None] * len(toks) for _ in range(ns)]
        for w in order:
            s = ids[part[w]]
            for j, t in enumerate(toks):
                n, nx = rows[w, t]
                assert out[s][j] in (None, n) and step[s][j] in (None, ids[part[nx]])
                out[s][j], step[s][j] = n, ids[part[nx]]
        prog = dict(ntok=ntok - 1, init=ids[part[init]], step=step, out=out)
        info["program_states"] = ns; info["program_rows"] = ns * len(toks)
        return True, "ok", prog, info
    except P9.Reject as e:
        return False, str(e), None, info


def run_prog(prog, w):
    s, ys = prog["init"], []
    for t in w:
        ys.append(prog["out"][s][t - 1]); s = prog["step"][s][t - 1]
    return ys


if __name__ == "__main__":
    import r5_checks as C5
    C5.memory_guard(2.5)
    rad = F(sys.argv[sys.argv.index("--radius") + 1]) if "--radius" in sys.argv else F(1, 2 ** 14)
    for f in [x for x in sys.argv[1:] if x.endswith(".json")]:
        ok, why, prog, info = extract(json.load(open(f)), rad)
        print(json.dumps(dict(net=f, ok=ok, reason=why, program=prog, **info)), flush=True)
