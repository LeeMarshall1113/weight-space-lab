namespace Lane4.Case

noncomputable def lo (a b : ℝ) : ℝ := if a ≤ b then a else b
noncomputable def hi (a b : ℝ) : ℝ := if a ≤ b then b else a
noncomputable def ab (a : ℝ) : ℝ := if 0 ≤ a then a else -a

noncomputable def prog (x0 x1 : ℝ) : ℝ :=
  lo (ab (2 * x0 + (-1) * x1 + (-1/2)))
    ((-1/2) * (lo ((-2) * x0 + 2 * x1 + (-1/2)) ((-1) * x1))
      + 1 * (lo (hi (2 * x0 + (-2) * x1 + (3/2)) 1) (5/2)))

-- PROOF
theorem lo_eq (a b : ℝ) : lo a b = min a b := by
  unfold lo
  rcases le_total a b with h | h
  · rw [if_pos h, min_eq_left h]
  · by_cases h' : a ≤ b
    · rw [if_pos h', min_eq_left h']
    · rw [if_neg h', min_eq_right h]

theorem hi_eq (a b : ℝ) : hi a b = max a b := by
  unfold hi
  rcases le_total a b with h | h
  · rw [if_pos h, max_eq_right h]
  · by_cases h' : a ≤ b
    · rw [if_pos h', max_eq_right h']
    · rw [if_neg h', max_eq_left h]

theorem ab_eq (a : ℝ) : ab a = |a| := by
  unfold ab
  by_cases h : 0 ≤ a
  · rw [if_pos h, abs_of_nonneg h]
  · rw [if_neg h, abs_of_neg (not_le.mp h)]

theorem prog_correct : StatementProg prog := by
  intro x0 x1 _ _ _ _
  unfold prog spec
  simp only [lo_eq, hi_eq, ab_eq]

end Lane4.Case
