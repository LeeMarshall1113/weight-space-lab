namespace Lane4.Case

noncomputable def hi (a b : ℝ) : ℝ := if a ≤ b then b else a
noncomputable def lo (a b : ℝ) : ℝ := if a ≤ b then a else b
noncomputable def ab (a : ℝ): ℝ := if 0 ≤ a then a else -a

noncomputable def prog (x0 x1 x2 : ℝ) : ℝ :=
  hi (lo (lo ((1/2) * x2 + (1/2)) ((1/2) * x0 + (-1) * x2 + 1)) (ab (hi ((1/2) * x0 + 2 * x1 + (-1)) ((-1/2) * x2 + (-5/2))))) (lo (hi (lo ((1/2) * x2 + (1/2)) ((1/2) * x0 + (-1) * x2 + 1)) (ab (hi ((1/2) * x0 + 2 * x1 + (-1)) ((-1/2) * x2 + (-5/2))))) ((-1) * x2 + (-1/2)))

-- PROOF
theorem hi_eq (a b : ℝ) : hi a b = max a b := by
  unfold hi
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_lt (not_le.mp h))).symm

theorem lo_eq (a b : ℝ) : lo a b = min a b := by
  unfold lo
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
  simp only [hi_eq, lo_eq, ab_eq]

end Lane4.Case
