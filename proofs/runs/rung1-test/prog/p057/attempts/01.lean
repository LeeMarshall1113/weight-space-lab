namespace Lane4.Case

def mx (a b : ℝ) : ℝ := if a ≤ b then b else a
def mn (a b : ℝ) : ℝ := if a ≤ b then a else b

noncomputable def prog (x0 x1 : ℝ) : ℝ :=
  (-1) * (mx (mx ((-1) * x0 + (1/2)) 0) (mn (mx ((-2) * x1 + (5/2)) (-3/2)) (3/2))) + (1/2) * (mn (mx (3 * x1 + 1) (-3/2)) (-1/2))

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

theorem prog_correct : StatementProg prog := by
  intro x0 x1 _ _ _ _
  unfold prog spec
  simp only [mx_eq, mn_eq]

end Lane4.Case
