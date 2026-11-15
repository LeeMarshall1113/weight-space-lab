"""Exact Lean witness that a proved rung-4 network is wrong under an ADDITIVE 1/1000 on every
weight (zeros included), in exact arithmetic (writeup/NOTE_2x2_results.md, cell R4 x ABS).

    python tools/make_witness_r4.py <case-id>      -> runs/witness/r4abs_<id>/

Search in float64 (short inputs, sign-corner perturbations), exact confirmation with
Fractions, then a case folder for the ordinary checker (import Lane4.QRSeq).
"""
import glob, json, os, sys
from fractions import Fraction as F
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r4net as R4, r4pool as P4
from make_witness import lean_net

HERE = P4.HERE


def qeval(net, w, i):
    """Exact mirror of Lane4.QR.qout (hard attention, ties averaged, left-to-right sums)."""
    toks = [0] + list(w); n = len(toks)
    x = [list(net["embed"][t]) + [F(1), F(j), F(n)] for j, t in enumerate(toks)]
    dot = lambda a, b: sum((u * v for u, v in zip(a, b)), F(0))
    for B in net["blocks"]:
        new = []
        for q in range(n):
            y = list(x[q])
            for h in B["heads"]:
                c = list(range(n)) if h["mask"] == "all" else list(range(q + 1)) if h["mask"] == "causal" else list(range(q))
                sc = {j: dot(x[q], [dot(r, x[j]) for r in h["A"]]) for j in c}
                S = [j for j in c if all(sc[k] <= sc[j] for k in c)]
                att = [(sum((dot(r, x[j]) for j in S), F(0)) / len(S) if S else F(0)) for r in h["V"]]
                y = [a + b for a, b in zip(y, att)]
            hid = [max(dot(r, y) + cc, F(0)) for r, cc in zip(B["W1"], B["b1"])]
            new.append([a + dot(r, hid) + cc for a, r, cc in zip(y, B["W2"], B["b2"])])
        x = new
    return dot(net["outW"], x[i]) + net["outB"]


def main(cid):
    c = {x["id"]: x for x in json.load(open(os.path.join(HERE, "pool", "rung4_pool.json")))}[cid]
    d = os.path.join(HERE, "runs", "rung4-test", "net", cid)
    j = json.load(open(os.path.join(d, "net.json")))
    Q = lambda M: [[F(v) for v in r] for r in M]
    D = len(j["outW"])
    net = {"embed": Q(j["embed"]), "outW": [F(v) for v in j["outW"]], "outB": F(j["outB"]),
           "blocks": [{"heads": [{"A": Q(h["A"]), "V": Q(h["V"]), "mask": h["mask"]} for h in B["heads"]],
                       "W1": Q(B["W1"]), "b1": [F(v) for v in B["b1"]],
                       "W2": Q(B["W2"]) if B["b1"] else [[] for _ in range(D)], "b2": [F(v) for v in B["b2"]]} for B in j["blocks"]]}

    def perturbed(rng):
        s = lambda: F(int(rng.choice([-1, 1])), 1000)
        return {"embed": [[v + s() for v in r] for r in net["embed"]], "outW": [v + s() for v in net["outW"]], "outB": net["outB"] + s(),
                "blocks": [{"heads": [{"A": [[v + s() for v in r] for r in h["A"]], "V": [[v + s() for v in r] for r in h["V"]], "mask": h["mask"]} for h in B["heads"]],
                            "W1": [[v + s() for v in r] for r in B["W1"]], "b1": [v + s() for v in B["b1"]],
                            "W2": [[v + s() for v in r] for r in B["W2"]], "b2": [v + s() for v in B["b2"]]} for B in net["blocks"]]}
    tof = lambda N: {"embed": [[float(v) for v in r] for r in N["embed"]], "outW": [float(v) for v in N["outW"]], "outB": float(N["outB"]),
                     "blocks": [{"heads": [{"A": [[float(v) for v in r] for r in h["A"]], "V": [[float(v) for v in r] for r in h["V"]], "mask": h["mask"]} for h in B["heads"]],
                                 "W1": [[float(v) for v in r] for r in B["W1"]], "b1": [float(v) for v in B["b1"]],
                                 "W2": [[float(v) for v in r] for r in B["W2"]], "b2": [float(v) for v in B["b2"]]} for B in N["blocks"]]}
    found = None
    for L in range(2, 41):
        for seed in range(60):
            rng = np.random.default_rng(1000 * L + seed)
            Np = perturbed(rng)
            w = [int(t) for t in rng.integers(1, c["V"] + 1, L)]
            y = R4.run(tof(Np), np.array(w), None, np.float64)
            tg = P4.target(c, w)
            bad = [i for i in range(1, L + 1) if abs(y[i - 1] - tg[i - 1]) > 0.26]
            if bad:
                o = qeval(Np, w, bad[0])
                if abs(o - tg[bad[0] - 1]) > F(1, 4):
                    found = (L, seed, Np, w, bad[0], tg[bad[0] - 1], o); break
        if found:
            break
    if not found:
        raise SystemExit("no additive witness up to length 40")
    L, seed, Np, w, i, t, o = found
    assert abs(qeval(net, w, i) - t) == 0, "unperturbed net should be exact"
    print(cid, "additive witness: length", L, "seed", seed, "input", w, "position", i, "target", t, "output", float(o))
    out = os.path.join(HERE, "runs", "witness", "r4abs_" + cid)
    os.makedirs(out, exist_ok=True)
    rd = lambda n: open(os.path.join(d, n), encoding="utf-8").read()
    spec = rd("Spec.lean").rstrip()[:-len("end Lane4.Case")] + '''
/-- `b` is within an absolute 1/1000 of `a`. -/
def qNear (a b : ℚ) : Bool := decide (|b - a| ≤ 1 / 1000)
def vNear (a b : List ℚ) : Bool := a.length == b.length && (List.zipWith qNear a b).all id
def mNear (A B : List (List ℚ)) : Bool := A.length == B.length && (List.zipWith vNear A B).all id
def hNear (h g : Head) : Bool := mNear h.A g.A && mNear h.V g.V && decide (h.mask = g.mask)
def bNear (B C : Block) : Bool :=
  B.heads.length == C.heads.length && (List.zipWith hNear B.heads C.heads).all id &&
  mNear B.W1 C.W1 && vNear B.b1 C.b1 && mNear B.W2 C.W2 && vNear B.b2 C.b2
/-- Every weight of `N'` is within an absolute 1/1000 of the corresponding weight of `N`. -/
def netNear (N N' : TNet) : Bool :=
  mNear N.embed N'.embed && N.blocks.length == N'.blocks.length &&
  (List.zipWith bNear N.blocks N'.blocks).all id && vNear N.outW N'.outW && qNear N.outB N'.outB

end Lane4.Case
'''
    passing = [p for p in sorted(glob.glob(os.path.join(d, "attempts", "*.json"))) if json.load(open(p, encoding="utf-8")).get("pass")][0]
    sol = open(passing[:-5] + ".lean", encoding="utf-8").read()
    wl = "[" + ", ".join(map(str, w)) + "]"
    add = "\nnamespace Lane4.Case\nopen Lane4.RSeq\nopen Lane4.Seq (Mask cand tokAt)\n\n/-- `net` with every weight (zeros included) moved by +1/1000 or -1/1000. -/\n" + lean_net(Np, "netP") + '''
/-- The changed network is within an absolute 1/1000 of `net`, entry by entry. -/
theorem witness_near : netNear net netP = true := by decide +kernel

/-- On the input `%s` the target at position %d is %d ... -/
theorem witness_target : target %s %d = %d := by decide +kernel

/-- ... the rational mirror of the changed network is more than 1/4 away from it ... -/
theorem witness_q : |Lane4.QR.qout netP %s %d - (%d : ℚ)| > 1 / 4 := by decide +kernel

/-- ... and so is the changed network itself, in exact arithmetic with no further
perturbation (`fl = id`, zero relative perturbation). -/
theorem witness_off :
    |netP.out (fun x => x) Lane4.QR.pert0 %s %d - (%d : ℝ)| > 1 / 4 := by
  rw [Lane4.QR.q_bridge netP %s %d]
  have h2 := Rat.cast_lt (K := ℝ) |>.mpr witness_q
  push_cast at h2
  exact h2

end Lane4.Case
''' % (wl, i, t, wl, i, t, wl, i, t, wl, i, t, wl, i)
    fin = rd("Final.lean").rstrip() + '''

namespace Lane4Final
theorem witness : Lane4.Case.netNear Lane4.Case.net Lane4.Case.netP = true ∧
    Lane4.Case.target %s %d = %d ∧
    |Lane4.RSeq.TNet.out Lane4.Case.netP (fun x => x) Lane4.QR.pert0 %s %d - (%d : ℝ)| > 1 / 4 :=
  ⟨Lane4.Case.witness_near, Lane4.Case.witness_target, Lane4.Case.witness_off⟩
end Lane4Final
#print axioms Lane4Final.witness
''' % (wl, i, t, wl, i, t)
    for n, txt in (("Spec.lean", spec), ("Solution.lean", sol + add), ("Final.lean", fin)):
        open(os.path.join(out, n), "w", encoding="utf-8", newline="\n").write(txt)
    meta = json.load(open(os.path.join(d, "case.json")))
    meta.update({"id": "r4abs_" + cid, "import": "QRSeq", "final_theorems": meta["final_theorems"] + ["Lane4Final.witness"], "max_attempts": 6,
                 "witness": {"all_entries": "additive sign corner 1/1000, numpy seed %d" % (1000 * L + seed), "input": w, "position": i, "target": t, "output": str(o)}})
    json.dump(meta, open(os.path.join(out, "case.json"), "w"), indent=1)
    print("wrote", out)


if __name__ == "__main__":
    main(sys.argv[1])
