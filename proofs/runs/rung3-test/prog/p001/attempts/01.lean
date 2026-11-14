namespace Lane4.Case
noncomputable def prog (x0 x1 : ℝ) : ℝ :=
  if x0 + (-3) ≤ (1/2) * x1 + 2 then
    (if 0 ≤ x0 + (-3) then x0 + (-3) else -(x0 + (-3)))
  else
    (if 0 ≤ (1/2) * x1 + 2 then (1/2) * x1 + 2 else -((1/2) * x1 + 2))
-- PROOF
theorem prog_correct : StatementProg prog := by
  intro x0 x1 _ _ _ _
  unfold prog spec
  by_cases h : x0 + (-3) ≤ (1/2) * x1 + 2
  · rw [if_pos h, min_eq_left h]
    by_cases h2 : 0 ≤ x0 + (-3)
    · rw [if_pos h2, abs_of_nonneg h2]
    · rw [if_neg h2, abs_of_neg (not_le.mp h2)]
  · rw [if_neg h, min_eq_right (le_of_lt (not_le.mp h))]
    by_cases h2 : 0 ≤ (1/2) * x1 + 2
    · rw [if_pos h2, abs_of_nonneg h2]
    · rw [if_neg h2, abs_of_neg (not_le.mp h2)]
end Lane4.Case
