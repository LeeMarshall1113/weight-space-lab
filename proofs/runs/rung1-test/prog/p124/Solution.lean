namespace Lane4.Case

noncomputable def prog (x0 x1 : ℝ) : ℝ :=
  if (-2) * x0 + 1 ≤ 0 then
    (if 0 ≤ x0 + 3 * x1 then x0 + 3 * x1 else 0)
  else
    (if (-2) * x0 + 1 ≤ x0 + 3 * x1 then x0 + 3 * x1 else (-2) * x0 + 1)

-- PROOF
theorem prog_correct : StatementProg prog := by
  intro x0 x1 _ _ _ _
  unfold prog spec
  by_cases h1 : (-2) * x0 + 1 ≤ 0
  · by_cases h2 : 0 ≤ x0 + 3 * x1
    · rw [if_pos h1, if_pos h2, max_eq_right h1, max_eq_right h2]
    · have h3 : x0 + 3 * x1 ≤ 0 := by linarith
      rw [if_pos h1, if_neg h2, max_eq_right h1, max_eq_left h3]
  · have h0 : 0 ≤ (-2) * x0 + 1 := by linarith
    by_cases h2 : (-2) * x0 + 1 ≤ x0 + 3 * x1
    · rw [if_neg h1, if_pos h2, max_eq_left h0, max_eq_right h2]
    · have h3 : x0 + 3 * x1 ≤ (-2) * x0 + 1 := by linarith
      rw [if_neg h1, if_neg h2, max_eq_left h0, max_eq_left h3]

end Lane4.Case
