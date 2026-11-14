namespace Lane4.Case

noncomputable def m1 (x0 x1 : ℝ) : ℝ :=
  if x0 + (-1) * x1 + (1/2) ≤ 2 * x1 + (-3) then 2 * x1 + (-3) else x0 + (-1) * x1 + (1/2)

noncomputable def m2 (x0 x1 : ℝ) : ℝ :=
  if m1 x0 x1 ≤ 3 * x1 + 2 then m1 x0 x1 else 3 * x1 + 2

noncomputable def prog (x0 x1 : ℝ) : ℝ :=
  if m2 x0 x1 ≤ (-1/2) * x1 + 1 then (-1/2) * x1 + 1 else m2 x0 x1
-- PROOF
theorem prog_correct : StatementProg prog := by
  intro x0 x1 _ _ _ _
  unfold prog m2 m1 spec
  simp only [max_def, min_def]
  all_goals (split_ifs)
  all_goals (first | done | linarith)
end Lane4.Case
