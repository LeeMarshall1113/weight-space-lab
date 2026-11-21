"""Rung 7: the per-network Lean file (PREREG_R7.md Amendment 2 point 1, Amendment 3 checker).

    python tools/make_r7_net.py <task A|B> <recipe> <seed> [--radius-mult k] [--tag name] [--net file.json]
                                [--task-as A|B] [--cands-from <run dir>:<head>]
        -> runs/r7-nets/<tag>/Net.lean

If the frozen prototype (tools/r7_cert.py) accepts, the file proves, with `decide +kernel` for every
closed Boolean and no proof search:
  accept            check (1/1000) net task cert = true           (split into pieces, reassembled)
  skeleton_ok       the registered Statement for the skeleton W   (from Lane4.R7K5.sound)
  exact_all_lengths, binary32                                     (rung-6a corollaries, for W)
  trained_exact_all_lengths, trained_binary32                     (transfer to the trained T)
If the prototype rejects, the file proves `check ... = false` (one theorem, `reject`).
The options build the negative controls of Amendment 2 point 4. No doctor, no per-network proof.
"""
import json, os, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(HERE, "tools"))
import r7_cert as RC
import make_r7_ka as KA
import make_r7_cases as MC
import r7

STATEMENT = """def Statement (N : ANet) : Prop :=
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Rnd u η M fl → ExpM u η ex →
  0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  ∀ p : APert, p.Within (1 / 1000) →
  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) →
  u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 → η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100 →
  2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M →
  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → |N.out fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4
"""

TASKDEF = {
    "B": "def task : Task :=\n  { ntok := 5, init := 0,\n    step := fun c t => if cls t = 2 then c else cls t,\n"
         "    out := fun s t => (dg t + s) % 3 }\n",
    "A": "def task : Task :=\n  { ntok := 5, init := 0,\n    step := fun _ t => t - 1,\n    out := fun s t => ((t - 1) + s) % 5 }\n",
}
# the automaton of the OTHER task, with its own letters (for the wrong-task control)
TASKDEF_PLAIN = {
    "B": "def task : Task :=\n  { ntok := 5, init := 0,\n"
         "    step := fun s t => if [0, 1, 2, 0, 0].getD (t - 1) 0 = 2 then s else [0, 1, 2, 0, 0].getD (t - 1) 0,\n"
         "    out := fun s t => ([2, 0, 2, 2, 0].getD (t - 1) 0 + s) % 3 }\n",
    "A": TASKDEF["A"],
}

ACCEPT_TAIL = """
/-- THE CHECKER ACCEPTS: every conjunct evaluated by the kernel above, put together by
`check_of` (Lane4/R7Glue.lean) without further evaluation. -/
theorem accept : check (1 / 1000) net task cert = true :=
  check_of (1 / 1000) net task cert netB0 rfl shape wts len
    (%(HEADPF)s) stl ini
    (%(STATEPF)s)

theorem target_eq (w : List ℕ) (i : ℕ) : task.target w i = target w i := rfl

/-- The registered statement for the skeleton `net` (the trained weights rounded to multiples of
1/1024): every network within the additive 1/1000 ball, every length the rounding model covers. -/
theorem skeleton_ok : Statement net := by
  have s := Lane4.R7K5.sound
  unfold Lane4.Cert.Sound at s
  intro u η M fl ex hr he hu0 hu hη0 hη p hp w hw h1 h2 h3 i hi1 hi2
  have h := s net task cert accept u η M fl ex hr he hu0 hu hη0 hη p hp w hw h1 h2 h3 i hi1 hi2
  rw [target_eq] at h
  exact h

theorem exact_all_lengths (p : APert) (hp : p.Within (1 / 1000)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    |ANet.out net (fun x => x) Real.exp p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 :=
  skeleton_ok 0 0 (2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2) (fun x => x) Real.exp
    (rnd_id (by positivity)) expM_real le_rfl (by positivity) le_rfl (by positivity)
    p hp w hw (by simp) (by simp) le_rfl i h1 h2

theorem binary32 (rn fl ex : ℝ → ℝ) (hrn : IsRN rn) (hfl : ∀ x, |x| ≤ maxF → fl x = rn x)
    (hex : ExpM (1 / 2 ^ 24) (1 / 2 ^ 149) ex) (p : APert) (hp : p.Within (1 / 1000))
    (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hlen : w.length + 1 ≤ 65536)
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    |ANet.out net fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 :=
  skeleton_ok (1 / 2 ^ 24) (1 / 2 ^ 149) maxF fl ex (bin32_rnd' hrn hfl) hex (by positivity) le_rfl
    (by positivity) le_rfl p hp w hw (side_u hlen) (side_eta hlen) (range_ok hlen) i h1 h2

/-! The network exactly as trained. -/

theorem same : Lane4.R7KT.sameShape net trained = true := by decide +kernel
theorem near : Lane4.R7KT.nearNet (1 / 1000) net trained = true := by decide +kernel

theorem trained_in_ball : (Lane4.R7KT.diffP net trained).Within (1 / 1000) := by
  have d := Lane4.R7KT.diff_within
  unfold Lane4.R7KT.DiffWithin at d
  have h := d net trained (1 / 1000) (by norm_num) same near
  have e : (((1 / 1000 : ℚ)) : ℝ) = 1 / 1000 := by norm_num
  rwa [e] at h

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

end Lane4.Net
#print axioms Lane4.Net.accept
#print axioms Lane4.Net.skeleton_ok
#print axioms Lane4.Net.trained_exact_all_lengths
#print axioms Lane4.Net.trained_binary32
"""


def arg(name, default=None):
    return sys.argv[sys.argv.index(name) + 1] if name in sys.argv else default


def main():
    tname, recipe, seed = sys.argv[1], sys.argv[2], int(sys.argv[3])
    mult = F(arg("--radius-mult", "1"))
    task_as = arg("--task-as", tname)
    d = os.path.join(HERE, "runs", "r7-stage0", tname, recipe, "s%d" % seed)
    W = json.load(open(os.path.join(d, arg("--net", "W.json")) if not os.path.isabs(arg("--net", "W.json")) else arg("--net")))
    T = json.load(open(os.path.join(d, "T.json")))
    tag = arg("--tag", "%s-%s-s%d" % (tname, recipe, seed))
    delta = RC.DELTA * mult
    ok, why, cands, states = KA.certificate(W, task_as) if mult == 1 else (None, None, None, None)
    if mult != 1:
        ok, why, _ = RC.check(W, task_as, delta, verbose=False)
        _, _, cands, states = KA.certificate(W, task_as)
    cf = arg("--cands-from")
    if cf:      # wrong-certificate control: one head's candidate set replaced by another network's
        src, hk = cf.rsplit(":", 1)
        _, _, c2, _ = KA.certificate(json.load(open(os.path.join(HERE, src, "W.json"))), task_as)
        cands = [c2[int(hk)] for _ in cands]
        s0, step, _ = RC.task_dfa(task_as)
        ntok = len(W["embed"])
        init = (s0, tuple(0 if c[0] else None for c in cands))
        states, todo = [init], [init]
        while todo:
            s, picks = todo.pop()
            for t in range(1, ntok):
                nxt = (step(s, t), tuple(t if c[t] else p for c, p in zip(cands, picks)))
                if nxt not in states:
                    states.append(nxt); todo.append(nxt)
        ok, why = False, "wrong certificate (control): candidate sets of another network's head"
    dq = KA.q(delta)
    nl = "\n"
    L = ["import Lane4.R7Glue", "", "/-", "the proofs study, rung 7, per-network file. Generated by tools/make_r7_net.py; no hand edits.",
         "network: runs/r7-stage0/%s/%s/s%d (%s), task automaton %s, radius %s" % (tname, recipe, seed, arg("--net", "W.json"), task_as, dq),
         "prototype (tools/r7_cert.py): %s (%s)" % ("accept" if ok else "reject", why), "-/", "",
         "namespace Lane4.Case", "open Lane4.RSeq (Vec)", "open Lane4.RSoft Lane4.AGate", "open Lane4.Seq (Mask cand tokAt)", ""]
    defs, _ = MC.task_parts(r7.task(tname))
    L += defs + ["", STATEMENT, KA.lean_net("net", W), KA.lean_net("trained", T), "end Lane4.Case", "",
                 "namespace Lane4.Net", "open Lane4.Case Lane4.Cert Lane4.AGate Lane4.RSoft Lane4.Bin32",
                 "open Lane4.Seq (Mask cand tokAt)", "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", ""]
    L.append(TASKDEF[tname] if task_as == tname else TASKDEF_PLAIN[task_as])
    b = lambda x: "true" if x else "false"
    o = lambda p: "none" if p is None else "some %d" % p
    for k, c in enumerate(cands):
        L.append("def cd%d : List Bool := [%s]" % (k, ", ".join(b(x) for x in c)))
    for k, (s, pk) in enumerate(states):
        L.append("def s%d : ℕ × List (Option ℕ) := (%d, [%s])" % (k, s, ", ".join(o(p) for p in pk)))
    L.append("def cert : Cert :=" + nl + "  { cands := [%s]," % ", ".join("cd%d" % k for k in range(len(cands))) + nl
             + "    states := [%s] }" % ", ".join("s%d" % k for k in range(len(states))))
    L.append("abbrev E : List (List IV) := net.embed.map (embIV (%s))" % dq)
    L.append("")
    if not ok:
        L += ["/-- THE CHECKER REJECTS (kernel evaluation). -/",
              "theorem reject : check (%s) net task cert = false := by decide +kernel" % dq,
              "", "end Lane4.Net", "#print axioms Lane4.Net.reject", ""]
    else:
        hd = lambda k: "headOK (1 / 1000) E netH%d cd%d" % (k, k)
        st = lambda k: "(List.range task.ntok).all (fun k => caseOK (1 / 1000) net netB0 task cert E s%d (k + 1))" % k
        L.append("theorem shape : net.shapeOK task.ntok = true := by decide +kernel")
        L.append("theorem wts : weightsOK net netB0 = true := by decide +kernel")
        L.append("theorem len : (cert.cands.length == netB0.heads.length) = true := by decide +kernel")
        L.append("theorem stl : cert.states.all (fun st => st.2.length == netB0.heads.length) = true := by decide +kernel")
        L.append("theorem ini : cert.states.contains (task.init, cert.cands.map (fun cd => if cd.getD 0 false = true then some 0 else none)) = true := by decide +kernel")
        for k in range(len(cands)):
            L.append("theorem hd%d : %s = true := by decide +kernel" % (k, hd(k)))
        for k in range(len(states)):
            L.append("theorem st%d : %s = true := by decide +kernel" % (k, st(k)))
        def nest(lemma, nil, names):
            t = nil
            for x in reversed(names):
                t = "%s _ _ _ _ _ %s (%s)" % (lemma, x, t) if lemma == "heads_cons" else "%s _ _ _ %s (%s)" % (lemma, x, t)
            return t
        nh, ns = len(cands), len(states)
        L.append(ACCEPT_TAIL % dict(HEADPF=nest("heads_cons", "heads_nil _", ["hd%d" % k for k in range(nh)]),
                                    STATEPF=nest("all_cons_of", "all_nil_of _", ["st%d" % k for k in range(ns)])))
    out = os.path.join(HERE, "runs", "r7-nets", tag)
    os.makedirs(out, exist_ok=True)
    open(os.path.join(out, "Net.lean"), "w", encoding="utf-8", newline=nl).write(nl.join(L))
    json.dump(dict(tag=tag, task=tname, recipe=recipe, seed=seed, task_as=task_as, radius=str(delta), prototype_ok=bool(ok),
                   prototype_reason=why, states=len(states), cands=cands), open(os.path.join(out, "meta.json"), "w"), indent=1)
    print(tag, "prototype:", "accept" if ok else "reject", "|", why)


if __name__ == "__main__":
    main()
