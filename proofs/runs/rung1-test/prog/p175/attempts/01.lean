namespace Lane4.Case
noncomputable def prog (x0 : ℝ) : ℝ :=
  if (-1/2) * x0 + 2 ≤ 2 * x0 + (5/2) then
    (if 2 * x0 + (5/2) ≤ 3 * x0 + (1/2) then 2 * x0 + (5/2) else 3 * x0 + (1/2))
  else
    (if (-1/2) * x0 + 2 ≤ 3 * x0 + (1/2) then (-1/2) * x0 + 2 else 3 * x0 + (1/2))
-- PROOF
theorem prog_correct : StatementProg prog := by
  intro x0 _ _
  unfold prog spec
  rw [max_def, min_def]
  split_ifs <;> linarith
end Lane4.Case
