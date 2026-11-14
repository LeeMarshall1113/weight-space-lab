namespace Lane4.Case

noncomputable def prog (x0 x1 : ℝ) : ℝ :=
  if (-1) * x0 + 3 * x1 + 2 ≤ (-1) * x1 + (-3/2) then
    (if (-2) * (if 3 ≤ x0 then (1/2) * x0 + (-3/2) else 0) + (-2) * (if 0 ≤ (-1) * x1 + (-3/2) then (-1) * x1 + (-3/2) else -((-1) * x1 + (-3/2))) ≤ (-1) * x0 + (1/2) then
      (-2) * (if 3 ≤ x0 then (1/2) * x0 + (-3/2) else 0) + (-2) * (if 0 ≤ (-1) * x1 + (-3/2) then (-1) * x1 + (-3/2) else -((-1) * x1 + (-3/2)))
    else (-1) * x0 + (1/2))
  else if (-1) * x0 + 3 * x1 + 2 ≤ (-1/2) * x1 + (3/2) then
    (if (-2) * (if 3 ≤ x0 then (1/2) * x0 + (-3/2) else 0) + (-2) * (if 0 ≤ (-1) * x0 + 3 * x1 + 2 then (-1) * x0 + 3 * x1 + 2 else -((-1) * x0 + 3 * x1 + 2)) ≤ (-1) * x0 + (1/2) then
      (-2) * (if 3 ≤ x0 then (1/2) * x0 + (-3/2) else 0) + (-2) * (if 0 ≤ (-1) * x0 + 3 * x1 + 2 then (-1) * x0 + 3 * x1 + 2 else -((-1) * x0 + 3 * x1 + 2))
    else (-1) * x0 + (1/2))
  else
    (if (-2) * (if 3 ≤ x0 then (1/2) * x0 + (-3/2) else 0) + (-2) * (if 0 ≤ (-1/2) * x1 + (3/2) then (-1/2) * x1 + (3/2) else -((-1/2) * x1 + (3/2))) ≤ (-1) * x0 + (1/2) then
      (-2) * (if 3 ≤ x0 then (1/2) * x0 + (-3/2) else 0) + (-2) * (if 0 ≤ (-1/2) * x1 + (3/2) then (-1/2) * x1 + (3/2) else -((-1/2) * x1 + (3/2)))
    else (-1) * x0 + (1/2))
-- PROOF
theorem prog_correct : StatementProg prog := by
  intro x0 x1 h1 h2 h3 h4
  have e1 : min ((-1) * x1 + (-3/2)) ((-1/2) * x1 + (3/2)) = (-1) * x1 + (-3/2) :=
    min_eq_left (by linarith)
  have e2 : max ((-1) * x1 + (-3/2)) ((-1/2) * x1 + (3/2)) = (-1/2) * x1 + (3/2) :=
    max_eq_right (by linarith)
  unfold spec prog
  rw [e1, e2]
  simp only [max_def, min_def, abs_eq_max_neg]
  split_ifs <;> linarith

end Lane4.Case
