namespace Lane4.Case

noncomputable def mx (a b : ℝ) : ℝ := if a ≤ b then b else a
noncomputable def mn (a b : ℝ) : ℝ := if a ≤ b then a else b

noncomputable def prog (x0 : ℝ) : ℝ :=
  mx (mn ((-1) * x0 + 2) (mx (mn ((-1) * x0) (x0 + (-5/2))) (mn (mx ((-1) * x0) (x0 + (-5/2))) ((1/2) * x0 + (1/2))))) (mn (mx ((-1) * x0 + 2) (mx (mn ((-1) * x0) (x0 + (-5/2))) (mn (mx ((-1) * x0) (x0 + (-5/2))) ((1/2) * x0 + (1/2))))) ((-2) * x0 + (-3/2)))

-- PROOF
theorem mx_eq (a b : ℝ) : mx a b = max a b := by
  unfold mx
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (not_le.mp h).le).symm

theorem mn_eq (a b : ℝ) : mn a b = min a b := by
  unfold mn
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (not_le.mp h).le).symm

theorem prog_correct : StatementProg prog := by
  intro x0 _ _
  unfold prog spec
  simp only [mx_eq, mn_eq]

end Lane4.Case
