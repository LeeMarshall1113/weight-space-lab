"""Rung 8, design passes of the mirror tools/r8_cert.py on the TUNING SET (PREREG_R8.md, Route: changes before the
checker freeze are logged with the tuning-set count). RUN UNDER reservation wrapper. No fresh seed is read: seeds < 140 only.

    python tools/r8_variants.py <tag> <variant> [<variant> ...]     -> results/rung8-variants-<tag>.json
variants are python dict literals merged into r8_cert.OPT, e.g.  "dict(fold=True)"
Sets: A u3 seeds 100-119 that pass screen 8 (W14, radius 2^-14); B u5 seeds 100-139 that pass screen 8 (W14,
2^-14); B u5 seeds 100-139 that pass the frozen rung-7 screen (W.json, radius 1/1000).
"""
import json, os, sys, time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(HERE, "tools"))
import r8_cert as C, r5_checks as C5

BASE = dict(C.OPT)


def nets():
    out = []
    for task, rec, lo, hi in (("A", "u3", 100, 119), ("B", "u5", 100, 139)):
        for s in range(lo, hi + 1):
            assert s < 140
            d = os.path.join(HERE, "runs", "r7-stage0", task, rec, "s%d" % s)
            s8 = json.load(open(os.path.join(d, "screen8.json")))
            s7 = json.load(open(os.path.join(d, "screen.json")))
            if s8["pass"]: out.append((task + "@2^-14", s, d, "W14.json", F(1, 2 ** 14), task))
            if task == "B" and s7.get("pass"): out.append(("B@1/1000", s, d, "W.json", F(1, 1000), task))
    return out


if __name__ == "__main__":
    C5.memory_guard(2.5)
    tag, res = sys.argv[1], {}
    for vs in sys.argv[2:]:
        C.OPT.clear(); C.OPT.update(BASE); C.OPT.update(eval(vs, {"F": F, "dict": dict}))
        t0 = time.time(); rows = []
        for setname, s, d, f, rad, task in nets():
            t1 = time.time()
            ok, why, info = C.check(json.load(open(os.path.join(d, f))), task, rad)
            info.pop("cert", None)
            rows.append(dict(set=setname, seed=s, ok=ok, reason=why, secs=round(time.time() - t1, 1), **info))
        res[vs] = rows
        for setname in ("A@2^-14", "B@2^-14", "B@1/1000"):
            rr = [r for r in rows if r["set"] == setname]
            acc = [r for r in rr if r["ok"]]
            print("%-60s %-9s accepted %2d of %2d | worst bound %s | most table rows %s | rejected: %s" % (
                vs, setname, len(acc), len(rr), ("%.3f" % max(r["worst"] for r in acc)) if acc else "-",
                max([r["table_rows"] for r in acc] + [0]), [(r["seed"], r["reason"][:60]) for r in rr if not r["ok"]]), flush=True)
        print("   %.0f s" % (time.time() - t0), flush=True)
    json.dump(res, open(os.path.join(HERE, "results", "rung8-variants-%s.json" % tag), "w"), indent=1)
