namespace Lane4.Case

noncomputable def bmx (a b : ℝ) : ℝ := if a ≤ b then b else a
noncomputable def bmn (a b : ℝ) : ℝ := if a ≤ b then a else b

noncomputable def prog (x0 x1 : ℝ) : ℝ :=
  bmn (bmx (bmn (bmx ((-1) * x1 + (3/2)) (-3)) 1) (x0 + (-2) * x1 + (-5/2))) (x0 + (-3))

-- PROOF
theorem bmx_eq (a b : ℝ) : bmx a b = max a b := by
  unfold bmx
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_lt (not_le.mp h))).symm

theorem bmn_eq (a b : ℝ) : bmn a b = min a b := by
  unfold bmn
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_lt (not_le.mp h))).symm

theorem prog_correct : StatementProg prog := by
  intro x0 x1 _ _ _ _
  simp only [prog, spec, bmx_eq, bmn_eq]

end Lane4.Case
