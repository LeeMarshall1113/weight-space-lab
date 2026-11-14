namespace Lane4.Case

noncomputable def mn (a b : ℝ) : ℝ := if a ≤ b then a else b
noncomputable def mx (a b : ℝ) : ℝ := if a ≤ b then b else a

noncomputable def prog (x0 x1 : ℝ) : ℝ :=
  mn ((1/2) * x0 + (1/2) * x1 + 1) (mx (mn (3 * x0 + (3/2)) ((-2) * x1 + (3/2))) (mx (mn (x1 + (-3/2)) (2 * x1 + (-5/2))) (mn (mx (x1 + (-3/2)) (2 * x1 + (-5/2))) ((-2) * x0 + 3 * x1))))
-- PROOF
theorem mn_eq (a b : ℝ) : mn a b = min a b := by
  unfold mn
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_lt (not_le.mp h))).symm

theorem mx_eq (a b : ℝ) : mx a b = max a b := by
  unfold mx
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_lt (not_le.mp h))).symm

theorem prog_correct : StatementProg prog := by
  intro x0 x1 _ _ _ _
  unfold prog spec
  simp only [mn_eq, mx_eq]

end Lane4.Case
