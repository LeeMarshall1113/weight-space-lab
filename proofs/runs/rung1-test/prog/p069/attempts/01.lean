namespace Lane4.Case
noncomputable def prog (x0 x1 x2 : ℝ) : ℝ :=
  if (-2) * x2 + 2 ≤ (-2) * x0 + (1/2) * x2 + (1/2) then
    (if (-2) * x0 + (1/2) * x2 + (1/2) ≤ (-2) * x1 + (-1/2) * x2 + (-3/2) then
      (-2) * x0 + (1/2) * x2 + (1/2) else (-2) * x1 + (-1/2) * x2 + (-3/2))
  else
    (if (-2) * x2 + 2 ≤ (-2) * x1 + (-1/2) * x2 + (-3/2) then
      (-2) * x2 + 2 else (-2) * x1 + (-1/2) * x2 + (-3/2))
-- PROOF
theorem prog_correct : StatementProg prog := by
  intro x0 x1 x2 _ _ _ _ _ _
  unfold prog spec
  simp only [max_def, min_def]
  split_ifs <;> linarith
end Lane4.Case
