namespace Lane4Final
open Lane4.RSeq Lane4.RSoft Lane4.Bin32

theorem shape : TNet.shapeOK Lane4.Case.net 3 = true := by decide

/-- The pre-registered statement. -/
theorem final : Lane4.Case.Statement Lane4.Case.net := Lane4.Case.net_ok

/-- Corollary 1: exact real arithmetic and the real exponential, EVERY input length. -/
theorem exact_all_lengths (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    |sout Lane4.Case.net (fun x => x) Real.exp p w i - ((Lane4.Case.target w i : ℕ) : ℝ)|
      ≤ 1 / 4 :=
  final 0 0 (2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2) (fun x => x) Real.exp
    (rnd_id (by positivity)) expM_real le_rfl (by positivity) le_rfl (by positivity)
    p hp w hw (by simp) (by simp) le_rfl i h1 h2

/-- Corollary 2: binary32 arithmetic (any round-to-nearest, subnormals included, nothing
assumed beyond the largest finite number), a float exponential within the stated error,
at most 65,535 input tokens. -/
theorem binary32 (rn fl ex : ℝ → ℝ) (hrn : IsRN rn) (hfl : ∀ x, |x| ≤ maxF → fl x = rn x)
    (hex : ExpM (1 / 2 ^ 24) (1 / 2 ^ 149) ex) (p : Pert) (hp : p.Within (1 / 200))
    (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (hlen : w.length + 1 ≤ 65536)
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    |sout Lane4.Case.net fl ex p w i - ((Lane4.Case.target w i : ℕ) : ℝ)| ≤ 1 / 4 :=
  final (1 / 2 ^ 24) (1 / 2 ^ 149) maxF fl ex (bin32_rnd' hrn hfl) hex (by positivity) le_rfl
    (by positivity) le_rfl p hp w hw (side_u hlen) (side_eta hlen) (range_ok hlen) i h1 h2

end Lane4Final
#print axioms Lane4Final.final
#print axioms Lane4Final.shape
#print axioms Lane4Final.exact_all_lengths
#print axioms Lane4Final.binary32
