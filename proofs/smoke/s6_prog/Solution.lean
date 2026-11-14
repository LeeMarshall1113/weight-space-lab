namespace Lane4.Case
noncomputable def prog (x0 x1 : ℝ) : ℝ := if x0 ≤ x1 then x1 else x0
-- PROOF
theorem prog_correct : StatementProg prog := by
  intro x0 x1 _ _ _ _
  unfold prog spec
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_lt (not_le.mp h))).symm
end Lane4.Case
