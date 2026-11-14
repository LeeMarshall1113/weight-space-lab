namespace Lane4.Case

noncomputable def mx (a b : ℝ) : ℝ := if a ≤ b then b else a
noncomputable def mn (a b : ℝ) : ℝ := if a ≤ b then a else b
noncomputable def ab (a : ℝ) : ℝ := if 0 ≤ a then a else -a

noncomputable def prog (x0 x1 x2 : ℝ) : ℝ :=
  mx (mn (mx (x0 + (-1) * x2 + (-5/2)) 0) (2 * x1 + (-5/2)))
    (mn (mx (mx (x0 + (-1) * x2 + (-5/2)) 0) (2 * x1 + (-5/2)))
      (ab (x0 + (-1/2) * x1 + 1)))
-- PROOF
theorem mx_eq (a b : ℝ) : mx a b = max a b := by
  unfold mx
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_lt (not_le.mp h))).symm

theorem mn_eq (a b : ℝ) : mn a b = min a b := by
  unfold mn
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_lt (not_le.mp h))).symm

theorem ab_eq (a : ℝ) : ab a = |a| := by
  unfold ab
  split_ifs with h
  · exact (abs_of_nonneg h).symm
  · exact (abs_of_neg (not_le.mp h)).symm

theorem prog_correct : StatementProg prog := by
  intro x0 x1 x2 _ _ _ _ _ _
  unfold prog spec
  simp only [mx_eq, mn_eq, ab_eq]

end Lane4.Case
