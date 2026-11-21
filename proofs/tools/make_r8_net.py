"""Rung 8: the per-network Lean file (PREREG_R8.md).

    python tools/make_r8_net.py <run dir> [--net W14.json] [--radius 1/16384] [--tag name] [--task-as A|B]
                                [--pieces-only] [--chunk n]
        -> runs/r8-nets/<tag>/Net.lean  (and Net_<k>.lean parts when --chunk splits the state lemmas)

If the mirror (tools/r8_cert.py) accepts, the file proves, with `decide +kernel` for every closed Boolean and no
proof search: `accept : check8 δ net task cert = true` (split into pieces, reassembled by check8_of), and, unless
--pieces-only, the theorems skeleton_ok, exact_all_lengths, binary32, trained_exact_all_lengths, trained_binary32
from Lane4.R8K.sound8. If the mirror rejects, the file proves `check8 ... = false` (theorem `reject`).
No doctor, no per-network proof. RUN UNDER reservation wrapper (the mirror is exact-rational work).
"""
import json, os, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(HERE, "tools"))
import r8_cert as C8
import make_r7_ka as KA
import make_r7_cases as MC
import make_r7_net as M7
import r7

q = KA.q
nl = "\n"


def arg(name, default=None):
    return sys.argv[sys.argv.index(name) + 1] if name in sys.argv else default


def iv(p): return "(%s, %s)" % (q(p[0]), q(p[1]))
def ivs(row): return "[" + ", ".join(iv(p) for p in row) + "]"
def ivm(M): return "[" + ("," + nl + "      ").join(ivs(r) for r in M) + "]"


STATEMENT = """def Statement (N : ANet) : Prop :=
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Rnd u η M fl → ExpM u η ex →
  0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  ∀ p : APert, p.Within (%(RAD)s) →
  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) →
  u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 → η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100 →
  2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M →
  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → |N.out fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4
"""

# The automaton's target equals the registered target. For B this is definitional; for A (the automaton's state is
# the previous digit) it needs the two position hypotheses; proof by the study team, the same text for every A network.
TEQ = {
    "B": """theorem target_eq (w : List ℕ) (i : ℕ) (_h1 : 1 ≤ i) (_h2 : i ≤ w.length) :
    task.target w i = target w i := rfl""",
    "A": """theorem fold_last (w : List ℕ) (k : ℕ) (hk : k < w.length) :
    (w.take (k + 1)).foldl (fun _ t => t - 1) 0 = w.getD k 0 - 1 := by
  rw [List.take_succ_eq_append_getElem hk, List.foldl_append]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem target_eq (w : List ℕ) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    task.target w i = target w i := by
  by_cases h : 2 ≤ i
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
    have e := fold_last w k (by omega)
    show ((w.getD (k + 2 - 1) 0 - 1) + (w.take (k + 2 - 1)).foldl (fun _ t => t - 1) 0) % 5
      = ((w.getD (k + 2 - 1) 0 - 1) + (if 2 ≤ k + 2 then w.getD (k + 2 - 2) 0 - 1 else 0)) % 5
    rw [if_pos h,show k + 2 - 1 = k + 1 from rfl, show k + 2 - 2 = k from rfl, e]
  · have hi : i = 1 := by omega
    subst hi
    show ((w.getD (1 - 1) 0 - 1) + (w.take (1 - 1)).foldl (fun _ t => t - 1) 0) % 5
      = ((w.getD (1 - 1) 0 - 1) + (if 2 ≤ 1 then w.getD (1 - 2) 0 - 1 else 0)) % 5
    simp""",
}

TAIL = """
%(TEQ)s

theorem rad_cast : (((%(RAD)s : ℚ)) : ℝ) = %(RAD)s := by norm_num

/-- The registered statement for the skeleton `net`: every network within the additive ball of
radius %(RAD)s, every length the rounding model covers. -/
theorem skeleton_ok : Statement net := by
  have s := Lane4.R8K.sound8
  unfold Lane4.Cert8.Sound8 at s
  intro u η M fl ex hr he hu0 hu hη0 hη p hp w hw h1 h2 h3 i hi1 hi2
  have hp' : p.Within (((%(RAD)s : ℚ)) : ℝ) := by rw [rad_cast]; exact hp
  have h := s (%(RAD)s) net task cert accept u η M fl ex hr he hu0 hu hη0 hη p hp' w hw h1 h2 h3 i hi1 hi2
  rw [target_eq w i hi1 hi2] at h
  exact h

theorem exact_all_lengths (p : APert) (hp : p.Within (%(RAD)s)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    |ANet.out net (fun x => x) Real.exp p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 :=
  skeleton_ok 0 0 (2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2) (fun x => x) Real.exp
    (rnd_id (by positivity)) expM_real le_rfl (by positivity) le_rfl (by positivity)
    p hp w hw (by simp) (by simp) le_rfl i h1 h2

theorem binary32 (rn fl ex : ℝ → ℝ) (hrn : IsRN rn) (hfl : ∀ x, |x| ≤ maxF → fl x = rn x)
    (hex : ExpM (1 / 2 ^ 24) (1 / 2 ^ 149) ex) (p : APert) (hp : p.Within (%(RAD)s))
    (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hlen : w.length + 1 ≤ 65536)
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    |ANet.out net fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 :=
  skeleton_ok (1 / 2 ^ 24) (1 / 2 ^ 149) maxF fl ex (bin32_rnd' hrn hfl) hex (by positivity) le_rfl
    (by positivity) le_rfl p hp w hw (side_u hlen) (side_eta hlen) (range_ok hlen) i h1 h2

/-! The network exactly as trained. -/

theorem same : Lane4.R7KT.sameShape net trained = true := by decide +kernel
theorem near : Lane4.R7KT.nearNet (%(RAD)s) net trained = true := by decide +kernel

theorem trained_in_ball : (Lane4.R7KT.diffP net trained).Within (%(RAD)s) := by
  have d := Lane4.R7KT.diff_within
  unfold Lane4.R7KT.DiffWithin at d
  have h := d net trained (%(RAD)s) (by norm_num) same near
  rwa [rad_cast] at h

theorem shift (fl ex : ℝ → ℝ) (w : List ℕ) (i : ℕ) :
    ANet.out net fl ex (Lane4.R7KT.diffP net trained) w i
      = ANet.out trained fl ex Lane4.R7KT.zeroP w i := by
  have o := Lane4.R7KT.out_shift
  unfold Lane4.R7KT.OutShift at o
  exact o net trained same fl ex w i

/-- THE HEADLINE: the network AS TRAINED (float32 weights, no rounding of weights, no
perturbation), exact real arithmetic, every input length. -/
theorem trained_exact_all_lengths (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ)
    (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    |ANet.out trained (fun x => x) Real.exp Lane4.R7KT.zeroP w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  rw [← shift]
  exact exact_all_lengths _ trained_in_ball w hw i h1 h2

/-- The network AS TRAINED, binary32 arithmetic, at most 65,535 input tokens. -/
theorem trained_binary32 (rn fl ex : ℝ → ℝ) (hrn : IsRN rn) (hfl : ∀ x, |x| ≤ maxF → fl x = rn x)
    (hex : ExpM (1 / 2 ^ 24) (1 / 2 ^ 149) ex)
    (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hlen : w.length + 1 ≤ 65536)
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    |ANet.out trained fl ex Lane4.R7KT.zeroP w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  rw [← shift]
  exact binary32 rn fl ex hrn hfl hex _ trained_in_ball w hw hlen i h1 h2
"""


def main():
    d = os.path.abspath(sys.argv[1])
    tj = json.load(open(os.path.join(d, "train.json")))
    tname, recipe, seed = tj["task"], tj["recipe"], tj["seed"]
    netf = arg("--net", "W14.json")
    delta = F(arg("--radius", "1/16384"))
    task_as = arg("--task-as", tname)
    pieces_only = "--pieces-only" in sys.argv
    W = json.load(open(netf if os.path.isabs(netf) else os.path.join(d, netf)))
    T = json.load(open(os.path.join(d, "T.json")))
    tag = arg("--tag", "%s-%s-s%d" % (tname, recipe, seed))
    ok, why, info = C8.check(W, task_as, delta)
    cert = info["cert"]
    dq = q(delta)
    L = ["import Lane4.R8Glue" if pieces_only or not ok else "import Lane4.R8All", "", "/-",
         "the proofs study, rung 8, per-network file. Generated by tools/make_r8_net.py; no hand edits.",
         "network: %s (%s), task automaton %s, radius %s" % (os.path.relpath(d, HERE).replace(os.sep, "/"), os.path.basename(netf), task_as, dq),
         "mirror (tools/r8_cert.py): %s (%s)" % ("accept" if ok else "reject", why), "-/", "",
         "namespace Lane4.Case", "open Lane4.RSeq (Vec)", "open Lane4.RSoft Lane4.AGate", "open Lane4.Seq (Mask cand tokAt)", ""]
    defs, _ = MC.task_parts(r7.task(tname))
    L += defs + ["", STATEMENT % dict(RAD=dq), KA.lean_net("net", W), KA.lean_net("trained", T), "end Lane4.Case", "",
                 "namespace Lane4.Net", "open Lane4.Case Lane4.Cert Lane4.Cert8 Lane4.AGate Lane4.RSoft Lane4.Bin32",
                 "open Lane4.Seq (Mask cand tokAt)", "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", ""]
    L.append(M7.TASKDEF[tname] if task_as == tname else M7.TASKDEF_PLAIN[task_as])
    b = lambda x: "true" if x else "false"
    nh, ns = len(cert["heads"]), len(cert["states"])
    for k, hc in enumerate(cert["heads"]):
        L.append("def hc%d : HCert :=" % k + nl + "  { cands := [%s], L := %d, spread := %s," % (", ".join(b(x) for x in hc["cands"]), hc["L"], q(hc["spread"]))
                 + nl + "    S := %s," % ivm(hc["S"]) + nl + "    VE := %s," % ivm(hc["VE"]) + nl + "    Bv := %s }" % KA.L(hc["Bv"]))
    for k, (s, wins) in enumerate(cert["states"]):
        L.append("def s%d : ℕ × List (List ℕ) := (%d, [%s])" % (k, s, ", ".join("[" + ", ".join(str(t) for t in wn) + "]" for wn in wins)))
    L.append("def cert : Cert8 :=" + nl + "  { heads := [%s]," % ", ".join("hc%d" % k for k in range(nh)) + nl
             + "    states := [%s] }" % ", ".join("s%d" % k for k in range(ns)))
    L.append("abbrev E : List (List IV) := net.embed.map (embIV (%s))" % dq)
    L.append("")
    if not ok:
        L += ["/-- THE CHECKER REJECTS (kernel evaluation). -/",
              "theorem reject : check8 (%s) net task cert = false := by decide +kernel" % dq,
              "", "end Lane4.Net", "#print axioms Lane4.Net.reject", ""]
    else:
        st = lambda k: "(List.range task.ntok).all (fun k => caseOK8 (%s) net netB0 task cert s%d (k + 1))" % (dq, k)
        L.append("theorem rd0 : decide ((0 : ℚ) ≤ %s) = true := by decide +kernel" % dq)
        L.append("theorem rd1 : decide ((%s : ℚ) ≤ 1 / 2) = true := by decide +kernel" % dq)
        L.append("theorem shape : net.shapeOK task.ntok = true := by decide +kernel")
        L.append("theorem wts : weightsOK net netB0 = true := by decide +kernel")
        L.append("theorem len : (cert.heads.length == netB0.heads.length) = true := by decide +kernel")
        L.append("theorem stl : cert.states.all (fun st => st.2.length == netB0.heads.length) = true := by decide +kernel")
        L.append("theorem ini : cert.states.contains (task.init, cert.heads.map (fun hc => if hc.cands.getD 0 false = true then [0] else [])) = true := by decide +kernel")
        for k in range(nh):
            L.append("theorem hd%d : headOK8 (%s) E netH%d hc%d = true := by decide +kernel" % (k, dq, k, k))
        per_case = "--per-case" in sys.argv   # one lemma per case: measured WORSE (K2, 2026-11-20); kept for the record
        for k in range(ns):
            if not per_case:                 # the registered form (PREREG_R8 Amendment 1): one lemma per state
                L.append("theorem st%d : %s = true := by decide +kernel" % (k, st(k)))
                continue
            for t in range(1, 6):
                L.append("theorem c%d_%d : caseOK8 (%s) net netB0 task cert s%d %d = true := by decide +kernel" % (k, t, dq, k, t))
            L.append("theorem st%d : %s = true :=" % (k, st(k)))
            L.append("  range5_all _ c%d_1 c%d_2 c%d_3 c%d_4 c%d_5" % (k, k, k, k, k))

        def nest(lemma, nil, names):
            t = nil
            for x in reversed(names):
                t = "%s _ _ _ _ _ %s (%s)" % (lemma, x, t) if lemma == "heads_cons" else "%s _ _ _ %s (%s)" % (lemma, x, t)
            return t
        L.append("")
        L.append("/-- THE CHECKER ACCEPTS: every conjunct evaluated by the kernel above, put together by `check8_of`. -/")
        L.append("theorem accept : check8 (%s) net task cert = true :=" % dq)
        L.append("  check8_of (%s) net task cert netB0 rfl rd0 rd1 shape wts len" % dq)
        L.append("    (%s) stl ini" % nest("heads_cons", "heads_nil _", ["hd%d" % k for k in range(nh)]))
        L.append("    (%s)" % nest("all_cons_of", "all_nil_of _", ["st%d" % k for k in range(ns)]))
        if not pieces_only:
            assert task_as == tname
            L.append(TAIL % dict(RAD=dq, TEQ=TEQ[tname]))
        L += ["", "end Lane4.Net", "#print axioms Lane4.Net.accept"]
        if not pieces_only:
            L += ["#print axioms Lane4.Net.skeleton_ok", "#print axioms Lane4.Net.trained_exact_all_lengths",
                  "#print axioms Lane4.Net.trained_binary32"]
        L.append("")
    out = os.path.join(HERE, "runs", "r8-nets", tag)
    os.makedirs(out, exist_ok=True)
    open(os.path.join(out, "Net.lean"), "w", encoding="utf-8", newline=nl).write(nl.join(L))
    info.pop("cert", None)
    json.dump(dict(tag=tag, dir=os.path.relpath(d, HERE).replace(os.sep, "/"), net=os.path.basename(netf), task=tname, recipe=recipe,
                   seed=seed, task_as=task_as, radius=str(delta), mirror_ok=bool(ok), mirror_reason=why, states=ns,
                   info=info), open(os.path.join(out, "meta.json"), "w"), indent=1)
    print(tag, "mirror:", "accept" if ok else "reject", "|", why, "| states", ns, "| table rows", info.get("table_rows"))


if __name__ == "__main__":
    main()
