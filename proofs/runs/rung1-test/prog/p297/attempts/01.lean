namespace Lane4.Case
noncomputable def prog (x0 : ℝ) : ℝ :=
  if x0 ≤ -3/8 then
    (if -2/3 ≤ x0 then 3 * x0 + 2 else -(3 * x0 + 2))
  else
    (if x0 ≤ 1/2 then -x0 + 1/2 else x0 - 1/2)
-- PROOF
theorem prog_correct : StatementProg prog := by
  intro x0 _ _
  unfold prog spec
  by_cases h1 : x0 ≤ -3/8
  · rw [if_pos h1, min_eq_left (by linarith)]
    by_cases h2 : -2/3 ≤ x0
    · rw [if_pos h2, abs_of_nonneg (by linarith)]
    · rw [if_neg h2, abs_of_nonpos (by linarith)]
  · rw [if_neg h1, min_eq_right (by linarith)]
    by_cases h2 : x0 ≤ 1/2
    · rw [if_pos h2, abs_of_nonneg (by linarith)]
    · rw [if_neg h2, abs_of_nonpos (by linarith)]
      ring
end Lane4.Case
