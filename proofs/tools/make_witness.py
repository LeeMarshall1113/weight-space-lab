"""Exact-rational Lean witnesses for break cells of the 2x2 (writeup/NOTE_2x2_results.md).

    python tools/make_witness.py r2rel <id>     # rung-2 net, relative perturbation within 1/200, zeros fixed

Searches (exact Fractions) for the shortest input on which a perturbed copy of a proved
rung-2 network is at least 1/2 from the target, and writes a case folder
runs/witness/r2rel_<id>/ that the ordinary checker can check:
  Spec.lean     the case's original Spec + closeness predicate
  Solution.lean the case's passing Solution (defines `net`, proves `net_ok`) + the perturbed
                net as a literal + three theorems proved by kernel evaluation
  Final.lean    the original theorem and the witness theorems
"""
import glob, itertools, json, os, sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import seqnet as SN, collect2_lib as CL, train_seq_twin as T

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

CLOSE = '''
/-- `b` is within a relative 1/200 of `a` (so `b = 0` when `a = 0`). -/
def qClose (a b : ℚ) : Bool := decide (|b - a| ≤ |a| / 200)
def vClose (a b : List ℚ) : Bool := a.length == b.length && (List.zipWith qClose a b).all id
def mClose (A B : List (List ℚ)) : Bool := A.length == B.length && (List.zipWith vClose A B).all id
def hClose (h g : Head) : Bool := mClose h.A g.A && mClose h.V g.V && decide (h.mask = g.mask)
def bClose (B C : Block) : Bool :=
  B.heads.length == C.heads.length && (List.zipWith hClose B.heads C.heads).all id &&
  mClose B.W1 C.W1 && vClose B.b1 C.b1 && mClose B.W2 C.W2 && vClose B.b2 C.b2
/-- Every weight of `N'` is within a relative 1/200 of the corresponding weight of `N`,
and every weight written as 0 is still 0. -/
def netClose (N N' : TNet) : Bool :=
  mClose N.embed N'.embed && N.blocks.length == N'.blocks.length &&
  (List.zipWith bClose N.blocks N'.blocks).all id && vClose N.outW N'.outW && qClose N.outB N'.outB
'''


def q(v):
    v = F(v)
    return ("(%d : ℚ)" % v.numerator if v.denominator == 1 else "(%d / %d : ℚ)" % (v.numerator, v.denominator)) if v < 0 or v.denominator != 1 else str(v.numerator)


vec = lambda r: "[" + ", ".join(q(v) for v in r) + "]"
mat = lambda M: "[" + ", ".join(vec(r) for r in M) + "]"


def lean_net(net, name):
    bl = []
    for B in net["blocks"]:
        hs = ", ".join("{ A := %s, V := %s, mask := Mask.%s }" % (mat(h["A"]), mat(h["V"]), h["mask"]) for h in B["heads"])
        bl.append("{ heads := [%s], W1 := %s, b1 := %s, W2 := %s, b2 := %s }" % (hs, mat(B["W1"]), vec(B["b1"]), mat(B["W2"]), vec(B["b2"])))
    return "def %s : TNet :=\n  { embed := %s,\n    blocks := [%s],\n    outW := %s,\n    outB := %s }\n" % (
        name, mat(net["embed"]), ",\n      ".join(bl), vec(net["outW"]), q(net["outB"]))


def entries(net):
    for i, r in enumerate(net["embed"]):
        for j in range(len(r)):
            yield ("E", r, j, "embed[%d][%d]" % (i, j))
    for b, B in enumerate(net["blocks"]):
        for k, h in enumerate(B["heads"]):
            for nm in ("A", "V"):
                for i, r in enumerate(h[nm]):
                    for j in range(len(r)):
                        yield (nm, r, j, "block %d head %d %s[%d][%d]" % (b, k, nm, i, j))
        for nm in ("W1", "W2"):
            for i, r in enumerate(B[nm]):
                for j in range(len(r)):
                    yield (nm, r, j, "block %d %s[%d][%d]" % (b, nm, i, j))
        for nm in ("b1", "b2"):
            for j in range(len(B[nm])):
                yield (nm, B[nm], j, "block %d %s[%d]" % (b, nm, j))
    for j in range(len(net["outW"])):
        yield ("outW", net["outW"], j, "outW[%d]" % j)


def r2rel(cid, maxlen=8):
    pool = {c["id"]: c for c in json.load(open(os.path.join(HERE, "pool", "rung2_pool.json")))}
    c = pool[cid]
    d = os.path.join(HERE, "runs", "rung2-test", "net", cid)
    net = CL.load_net(os.path.join(d, "net.json"))
    V = len(net["embed"]) - 1
    best = None
    for L in range(1, maxlen + 1):
        words = list(itertools.product(range(1, V + 1), repeat=L))
        for kind, cont, j, label in entries(net):
            if cont[j] == 0:
                continue
            old = cont[j]
            for sgn in (1, -1):
                cont[j] = old * (1 + F(sgn, 200))
                for w in words:
                    out = SN.run(net, list(w)); y = T.target(c, list(w))
                    for i in range(1, L + 1):
                        if abs(out[i] - y[i - 1]) >= F(1, 2):
                            best = (label, sgn, list(w), i, int(y[i - 1]), out[i]); break
                    if best: break
                if best: break
            if best:
                pert = {"embed": [list(r) for r in net["embed"]], "outW": list(net["outW"]), "outB": net["outB"],
                        "blocks": [{"heads": [{"A": [list(r) for r in h["A"]], "V": [list(r) for r in h["V"]], "mask": h["mask"]} for h in B["heads"]],
                                    "W1": [list(r) for r in B["W1"]], "b1": list(B["b1"]), "W2": [list(r) for r in B["W2"]], "b2": list(B["b2"])} for B in net["blocks"]]}
                cont[j] = old
                break
            cont[j] = old
        if best:
            break
    if not best:
        raise SystemExit("no single-entry relative witness up to length %d" % maxlen)
    label, sgn, w, i, t, o = best
    print(cid, "witness:", label, "times (1 %s 1/200); input" % ("+" if sgn > 0 else "-"), w, "position", i, "target", t, "output", o, "=", float(o))
    out = os.path.join(HERE, "runs", "witness", "r2rel_" + cid)
    os.makedirs(out, exist_ok=True)
    rd = lambda n: open(os.path.join(d, n), encoding="utf-8").read()
    spec = rd("Spec.lean")
    assert spec.rstrip().endswith("end Lane4.Case")
    spec = spec.rstrip()[:-len("end Lane4.Case")] + CLOSE + "\nend Lane4.Case\n"
    passing = [p for p in sorted(glob.glob(os.path.join(d, "attempts", "*.json"))) if json.load(open(p, encoding="utf-8")).get("pass")][0]
    sol = open(passing[:-5] + ".lean", encoding="utf-8").read()
    wl = "[" + ", ".join(map(str, w)) + "]"
    add = "\nnamespace Lane4.Case\nopen Lane4.Seq\n\n/-- `net` with one weight changed: %s multiplied by (1 %s 1/200). -/\n" % (label, "+" if sgn > 0 else "-") + lean_net(pert, "netP") + '''
/-- The changed network is inside the relative ball of radius 1/200 around `net`, zeros fixed. -/
theorem witness_close : netClose net netP = true := by decide +kernel

/-- On the input `%s`, the correct output at position %d is %d ... -/
theorem witness_target : IsRank %s %d %d := by unfold IsRank; decide

/-- ... and the changed network's output there is at least 1/2 away from it. -/
theorem witness_off : |netP.out %s %d - (%d : ℚ)| ≥ 1 / 2 := by decide +kernel

end Lane4.Case
''' % (wl, i, t, wl, i, t, wl, i, t)
    fin = rd("Final.lean").rstrip() + '''

namespace Lane4Final
theorem witness : Lane4.Case.netClose Lane4.Case.net Lane4.Case.netP = true ∧
    Lane4.Case.IsRank %s %d %d ∧ |Lane4.Case.netP.out %s %d - (%d : ℚ)| ≥ 1 / 2 :=
  ⟨Lane4.Case.witness_close, Lane4.Case.witness_target, Lane4.Case.witness_off⟩
end Lane4Final
#print axioms Lane4Final.witness
''' % (wl, i, t, wl, i, t)
    for n, txt in (("Spec.lean", spec), ("Solution.lean", sol + add), ("Final.lean", fin)):
        open(os.path.join(out, n), "w", encoding="utf-8", newline="\n").write(txt)
    meta = json.load(open(os.path.join(d, "case.json")))
    meta.update(id="r2rel_" + cid, final_theorems=meta.get("final_theorems", ["Lane4Final.final"]) + ["Lane4Final.witness"], max_attempts=6,
                witness={"entry": label, "sign": sgn, "input": w, "position": i, "target": t, "output": str(o)})
    json.dump(meta, open(os.path.join(out, "case.json"), "w"), indent=1)
    print("wrote", out)


if __name__ == "__main__" and sys.argv[1] == "r2rel":
    r2rel(sys.argv[2])


def r2long(cid):
    """Addition networks (one block): shortest long-carry input on which a relative sign-corner
    perturbation of ALL non-zero weights within 1/200 gives an output at least 1/2 off."""
    import numpy as np
    pool = {c["id"]: c for c in json.load(open(os.path.join(HERE, "pool", "rung2_pool.json")))}
    c = pool[cid]; b = c["base"]
    d = os.path.join(HERE, "runs", "rung2-test", "net", cid)
    net = CL.load_net(os.path.join(d, "net.json"))
    P32, shape = CL.float_params(net)
    P0 = {k: np.array(v, dtype=float) for k, v in P32.items()}
    gen = b * b                       # token with digits (b-1, b-1): generates a carry
    prop = b                          # token with digits (0, b-1): propagates a carry
    found = None
    for L in list(range(4, 40, 2)) + list(range(40, 400, 10)):
        w = [gen] + [prop] * (L - 1)
        y = T.target(c, w)
        toks = np.array([[0] + w])
        for seed in range(40):
            rng = np.random.default_rng(seed)
            signs = {k: rng.choice([-1.0, 1.0], P0[k].shape) for k in P0}
            Pm = {k: P0[k] * (1 + signs[k] / 200) for k in P0}
            out = T.forward(Pm, shape, toks, hard=True)[0][0]
            bad = [i for i in range(1, L + 1) if abs(out[i] - y[i - 1]) >= 0.5]
            if bad:
                found = (L, seed, w, bad[0], signs); break
        if found:
            break
    if not found:
        raise SystemExit("no break found")
    L, seed, w, i, signs = found
    # exact perturbed net: same signs applied to the exact rationals
    it = {}
    def sg(key, idx):
        return int(signs[key][idx])
    pert = {"embed": [[v * (1 + F(sg("E", (r, j)), 200)) for j, v in enumerate(row)] for r, row in enumerate(net["embed"])],
            "outW": [v * (1 + F(sg("outW", (j,)), 200)) for j, v in enumerate(net["outW"])],
            "outB": net["outB"] * (1 + F(int(signs["outB"].reshape(-1)[0]), 200)) if "outB" in signs else net["outB"], "blocks": []}
    for k, B in enumerate(net["blocks"]):
        pert["blocks"].append({
            "heads": [{"A": [[v * (1 + F(sg("A%d_%d" % (k, h), (r, j)), 200)) for j, v in enumerate(row)] for r, row in enumerate(H["A"])],
                       "V": [[v * (1 + F(sg("V%d_%d" % (k, h), (r, j)), 200)) for j, v in enumerate(row)] for r, row in enumerate(H["V"])],
                       "mask": H["mask"]} for h, H in enumerate(B["heads"])],
            "W1": [[v * (1 + F(sg("W1_%d" % k, (r, j)), 200)) for j, v in enumerate(row)] for r, row in enumerate(B["W1"])],
            "b1": [v * (1 + F(sg("b1_%d" % k, (j,)), 200)) for j, v in enumerate(B["b1"])],
            "W2": [[v * (1 + F(sg("W2_%d" % k, (r, j)), 200)) for j, v in enumerate(row)] for r, row in enumerate(B["W2"])],
            "b2": [v * (1 + F(sg("b2_%d" % k, (j,)), 200)) for j, v in enumerate(B["b2"])]})
    out = SN.run(pert, w); y = T.target(c, w)
    bad = [j for j in range(1, L + 1) if abs(out[j] - y[j - 1]) >= F(1, 2)]
    print(cid, "float break at length", L, "seed", seed, "position", i, "| exact break positions:", bad[:5])
    if not bad:
        raise SystemExit("exact evaluation does not confirm")
    i = bad[0]; t = int(y[i - 1]); o = out[i]
    print("exact output", float(o), "target", t)
    outd = os.path.join(HERE, "runs", "witness", "r2long_" + cid)
    os.makedirs(outd, exist_ok=True)
    rd = lambda n: open(os.path.join(d, n), encoding="utf-8").read()
    spec = rd("Spec.lean").rstrip()[:-len("end Lane4.Case")] + CLOSE + "\nend Lane4.Case\n"
    passing = [p for p in sorted(glob.glob(os.path.join(d, "attempts", "*.json"))) if json.load(open(p, encoding="utf-8")).get("pass")][0]
    sol = open(passing[:-5] + ".lean", encoding="utf-8").read()
    wl = "(%d :: List.replicate %d %d)" % (gen, L - 1, prop)
    add = "\nnamespace Lane4.Case\nopen Lane4.Seq\n\n/-- `net` with every non-zero weight multiplied by (1 + 1/200) or (1 - 1/200). -/\n" + lean_net(pert, "netP") + '''
/-- The changed network is inside the relative ball of radius 1/200 around `net`, zeros fixed. -/
theorem witness_close : netClose net netP = true := by decide +kernel

/-- The input: one carry-generating token followed by %d carry-propagating tokens
(length %d). The correct output at position %d is %d ... -/
theorem witness_target : digit %s %d = %d := by decide +kernel

/-- ... and the changed network's output there is at least 1/2 away from it. -/
theorem witness_off : |netP.out %s %d - (%d : ℚ)| ≥ 1 / 2 := by decide +kernel

end Lane4.Case
''' % (L - 1, L, i, t, wl, i, t, wl, i, t)
    fin = rd("Final.lean").rstrip() + '''

namespace Lane4Final
theorem witness : Lane4.Case.netClose Lane4.Case.net Lane4.Case.netP = true ∧
    Lane4.Case.digit %s %d = %d ∧ |Lane4.Case.netP.out %s %d - (%d : ℚ)| ≥ 1 / 2 :=
  ⟨Lane4.Case.witness_close, Lane4.Case.witness_target, Lane4.Case.witness_off⟩
end Lane4Final
#print axioms Lane4Final.witness
''' % (wl, i, t, wl, i, t)
    for n, txt in (("Spec.lean", spec), ("Solution.lean", sol + add), ("Final.lean", fin)):
        open(os.path.join(outd, n), "w", encoding="utf-8", newline="\n").write(txt)
    meta = json.load(open(os.path.join(d, "case.json")))
    meta.update(id="r2long_" + cid, final_theorems=meta.get("final_theorems", ["Lane4Final.final"]) + ["Lane4Final.witness"], max_attempts=6,
                witness={"all_nonzero_entries": "sign corner, numpy seed %d" % seed, "input": "one generate token then %d propagate tokens" % (L - 1),
                         "length": L, "position": i, "target": t, "output": str(o)})
    json.dump(meta, open(os.path.join(outd, "case.json"), "w"), indent=1)
    print("wrote", outd)


if __name__ == "__main__" and sys.argv[1] == "r2long":
    r2long(sys.argv[2])
