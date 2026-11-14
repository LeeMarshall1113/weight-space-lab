namespace Lane4.Case

noncomputable def prog (x0 x1 x2 : ℝ) : ℝ :=
  (-1) * (if x1 + x2 + 3 ≤ (1/2) * x0 + 1 then (1/2) * x0 + 1 else x1 + x2 + 3)
    + (1/2) * (if (-2) * x0 + (-1/2) * x2 + 1 ≤ 0 then 0 else (-2) * x0 + (-1/2) * x2 + 1)

-- PROOF
theorem prog_correct : StatementProg prog := by
  intro x0 x1 x2 _ _ _ _ _ _
  unfold prog spec
  simp only [max_def]

end Lane4.Case
