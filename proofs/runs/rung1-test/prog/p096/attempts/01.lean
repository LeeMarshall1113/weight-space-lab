namespace Lane4.Case

noncomputable def prog (x0 x1 : ℝ) : ℝ :=
  if 0 ≤ 2 * x0 + (-1) * x1 + (-1/2) then
    (if 2 * x0 + (-1) * x1 + (-1/2) ≤
      (-1/2) * (if (-2) * x0 + 2 * x1 + (-1/2) ≤ (-1) * x1 then (-2) * x0 + 2 * x1 + (-1/2) else (-1) * x1)
        + 1 * (if (if 1 ≤ 2 * x0 + (-2) * x1 + (3/2) then 2 * x0 + (-2) * x1 + (3/2) else 1) ≤ 5/2
               then (if 1 ≤ 2 * x0 + (-2) * x1 + (3/2) then 2 * x0 + (-2) * x1 + (3/2) else 1) else 5/2)
     then 2 * x0 + (-1) * x1 + (-1/2)
     else (-1/2) * (if (-2) * x0 + 2 * x1 + (-1/2) ≤ (-1) * x1 then (-2) * x0 + 2 * x1 + (-1/2) else (-1) * x1)
        + 1 * (if (if 1 ≤ 2 * x0 + (-2) * x1 + (3/2) then 2 * x0 + (-2) * x1 + (3/2) else 1) ≤ 5/2
               then (if 1 ≤ 2 * x0 + (-2) * x1 + (3/2) then 2 * x0 + (-2) * x1 + (3/2) else 1) else 5/2))
  else
    (if -(2 * x0 + (-1) * x1 + (-1/2)) ≤
      (-1/2) * (if (-2) * x0 + 2 * x1 + (-1/2) ≤ (-1) * x1 then (-2) * x0 + 2 * x1 + (-1/2) else (-1) * x1)
        + 1 * (if (if 1 ≤ 2 * x0 + (-2) * x1 + (3/2) then 2 * x0 + (-2) * x1 + (3/2) else 1) ≤ 5/2
               then (if 1 ≤ 2 * x0 + (-2) * x1 + (3/2) then 2 * x0 + (-2) * x1 + (3/2) else 1) else 5/2)
     then -(2 * x0 + (-1) * x1 + (-1/2))
     else (-1/2) * (if (-2) * x0 + 2 * x1 + (-1/2) ≤ (-1) * x1 then (-2) * x0 + 2 * x1 + (-1/2) else (-1) * x1)
        + 1 * (if (if 1 ≤ 2 * x0 + (-2) * x1 + (3/2) then 2 * x0 + (-2) * x1 + (3/2) else 1) ≤ 5/2
               then (if 1 ≤ 2 * x0 + (-2) * x1 + (3/2) then 2 * x0 + (-2) * x1 + (3/2) else 1) else 5/2))

-- PROOF
theorem prog_correct : StatementProg prog := by
  intro x0 x1 _ _ _ _
  unfold prog spec
  simp only [max_def, min_def, abs_eq_max_neg]
  split_ifs <;> linarith

end Lane4.Case
