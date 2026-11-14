namespace Lane4.Case
def mn (a b : ℝ) : ℝ := if a ≤ b then a else b
def mx (a b : ℝ) : ℝ := if a ≤ b then b else a
noncomputable def prog (x0 x1 : ℝ) : ℝ :=
  mn (mx (mn ((-1) * x0 + 1) ((-1) * x0 + (1/2))) (mn (mx ((-1) * x0 + 1) ((-1) * x0 + (1/2))) (2 * x0 + (5/2)))) ((1/2) * x1 + (-2))
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
