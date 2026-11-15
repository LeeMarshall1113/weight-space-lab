set_option linter.unusedVariables false
set_option linter.style.longLine false
namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

def z7 : List ℚ := [0, 0, 0, 0, 0, 0, 0]

def hd : Head :=
  { A := [z7, z7, z7, z7, [0, 0, 0, 0, 0, -20, 0], [40, 0, 0, 0, 0, 0, 0], z7],
    V := [z7, z7, z7, [0, 1, 0, 0, 0, 0, 0], z7, z7, z7],
    mask := Mask.causal }

def blk : Block :=
  { heads := [hd], W1 := [[0, 0, 1, 1, 0, 0, 0]], b1 := [-1],
    W2 := [[0], [0], [0], [-2], [0], [0], [0]], b2 := z7 }

def net : TNet :=
  { embed := [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [1, 1, 0, 0], [1, 1, 0, 0]],
    blocks := [blk],
    outW := [0, 0, 1, 1, 0, 0, 0],
    outB := 0 }

noncomputable def mv (fl : ℝ → ℝ) (p : Pert) (t : ℕ) : ℝ :=
  if t = 1 ∨ t = 4 ∨ t = 5 then sw fl 1 (p.E t 0) else 0
noncomputable def av (fl : ℝ → ℝ) (p : Pert) (t : ℕ) : ℝ :=
  if t = 4 ∨ t = 5 then sw fl 1 (p.E t 1) else 0
noncomputable def cv (fl : ℝ → ℝ) (p : Pert) (t : ℕ) : ℝ :=
  if t = 2 then sw fl 1 (p.E t 2) else 0

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [mv fl p (tokAt w j), av fl p (tokAt w j), cv fl p (tokAt w j), 0]
      ++ pos fl j (w.length + 1) := by
  have h6 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4
      ∨ tokAt w j = 5 := by
    have := tok_le w hw j
    omega
  rcases h6 with h | h | h | h | h | h <;>
    simp [TNet.init, net, swRow, h, mv, av, cv, sw_zero hr]

theorem zrow_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ) (a b c d e f g : ℝ) :
    rdot fl z7 [a, b, c, d, e, f, g] dV 0 0 = 0 := by
  simp [z7, rdot, sw_zero hr, hr.zero]

theorem val_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ) (a b c d e f g : ℝ)
    (hI : fl (fl (sw fl 1 (dV 1) * b)) = fl (sw fl 1 (dV 1) * b)) :
    rdot fl [0, 1, 0, 0, 0, 0, 0] [a, b, c, d, e, f, g] dV 0 0 = fl (sw fl 1 (dV 1) * b) := by
  simp [rdot, sw_zero hr, hr.zero, hI]

theorem score_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (a b c d e f g mk ak ck dk ek fk gk : ℝ)
    (hI1 : fl (fl (sw fl (-20) (dA 4 5) * fk)) = fl (sw fl (-20) (dA 4 5) * fk))
    (hI2 : fl (fl (sw fl 40 (dA 5 0) * mk)) = fl (sw fl 40 (dA 5 0) * mk))
    (hI3 : fl (fl (fl (sw fl (-20) (dA 4 5) * fk) + fl (f * fl (sw fl 40 (dA 5 0) * mk))))
      = fl (fl (sw fl (-20) (dA 4 5) * fk) + fl (f * fl (sw fl 40 (dA 5 0) * mk)))) :
    hd.score fl dA [a, b, c, d, e, f, g] [mk, ak, ck, dk, ek, fk, gk]
      = fl (fl (sw fl (-20) (dA 4 5) * fk) + fl (f * fl (sw fl 40 (dA 5 0) * mk))) := by
  simp [Head.score, hd, z7, pdot, rmat, rdot, sw_zero hr, hr.zero, hI1, hI2, hI3]

theorem attn_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) :
    sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, 0, savg fl ex (cand Mask.causal (w.length + 1) i)
              (hscore hd fl (p.A 0 0) (net.init fl p w) i)
              (fun j => rdot fl [0, 1, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 3) 0 0),
         0, 0, 0] := by
  have hV : hd.V = [z7, z7, z7, [0, 1, 0, 0, 0, 0, 0], z7, z7, z7] := rfl
  have hm : hd.mask = Mask.causal := rfl
  have hz : ∀ d : ℕ → ℝ,
      savg fl ex (cand Mask.causal (w.length + 1) i)
        (hscore hd fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl z7 (net.init fl p w j) d 0 0) = 0 := by
    intro d
    apply soft_zeros hr
    intro k _
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact zrow_eq hr d _ _ _ _ _ _ _
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz]

theorem net_ok : Statement net := by
  skip

end Lane4.Case
