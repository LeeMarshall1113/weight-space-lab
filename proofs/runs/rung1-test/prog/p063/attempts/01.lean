namespace Lane4.Case

def mx (a b : ℝ) : ℝ := if a ≤ b then b else a

def ab (m : ℝ) : ℝ := if m ≤ 0 then -m else m

noncomputable def prog (x0 x1 : ℝ) : ℝ :=
  ab (mx (3 * x0 + 3 * x1 + 1) ((1/2) * x0 + (-1/2)))

-- PROOF
theorem key (a b : ℝ) : ab (mx a b) = |max a b| := by
  unfold ab mx
  by_cases h : a ≤ b
  · rw [if_pos h, max_eq_right h]
    by_cases h2 : b ≤ 0
    · rw [if_pos h2, abs_of_nonpos h2]
    · rw [if_neg h2, abs_of_nonneg (by linarith [not_le.mp h2])]
  · have h' : b ≤ a := by linarith [not_le.mp h]
    rw [if_neg h, max_eq_left h']
    by_cases h2 : a ≤ 0
    · rw [if_pos h2, abs_of_nonpos h2]
    · rw [if_neg h2, abs_of_nonneg (by linarith [not_le.mp h2])]

theorem prog_correct : StatementProg prog := by
  intro x0 x1 _ _ _ _
  unfold prog spec
  exact key _ _
end Lane4.Case
