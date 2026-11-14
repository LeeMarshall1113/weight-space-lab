namespace Lane4.Case

def mxx (a b : ℝ) : ℝ := if a ≤ b then b else a
def mnn (a b : ℝ) : ℝ := if a ≤ b then a else b

noncomputable def prog (x0 x1 : ℝ) : ℝ :=
  mxx (mnn (2 * x1 + (-5/2)) ((-1) * x0 + (-2) * x1 + (-1/2))) (mnn (mxx (2 * x1 + (-5/2)) ((-1) * x0 + (-2) * x1 + (-1/2))) (mxx (mnn ((-1) * x1 + (-1)) ((1/2) * x0 + (1/2) * x1 + 1)) (mnn (mxx ((-1) * x1 + (-1)) ((1/2) * x0 + (1/2) * x1 + 1)) ((-1/2) * x0 + (-3)))))

-- PROOF
theorem mxx_eq (a b : ℝ) : mxx a b = max a b := by
  unfold mxx
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_lt (not_le.mp h))).symm

theorem mnn_eq (a b : ℝ) : mnn a b = min a b := by
  unfold mnn
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_lt (not_le.mp h))).symm

theorem prog_correct : StatementProg prog := by
  intro x0 x1 _ _ _ _
  unfold prog spec
  simp only [mxx_eq, mnn_eq]

end Lane4.Case
