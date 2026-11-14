namespace Lane4.Case

noncomputable def lo (a b : ℝ) : ℝ := if a ≤ b then a else b
noncomputable def hi (a b : ℝ) : ℝ := if a ≤ b then b else a

noncomputable def prog (x0 x1 x2 : ℝ) : ℝ :=
  hi (lo (lo (3 * x1) ((-2) * x2 + (-1/2))) (x0 + (3/2)))
     (lo (hi (lo (3 * x1) ((-2) * x2 + (-1/2))) (x0 + (3/2))) ((-1/2) * x0 + (-5/2)))
-- PROOF
theorem lo_eq (a b : ℝ) : lo a b = min a b := by
  unfold lo; rw [min_def]

theorem hi_eq (a b : ℝ) : hi a b = max a b := by
  unfold hi; rw [max_def]
theorem prog_correct : StatementProg prog := by
  intro x0 x1 x2 _ _ _ _ _ _
  unfold prog spec
  simp only [lo_eq, hi_eq]

end Lane4.Case
