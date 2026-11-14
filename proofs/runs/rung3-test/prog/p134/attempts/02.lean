namespace Lane4.Case

noncomputable def pmx (a b : ℝ) : ℝ := if a ≤ b then b else a
noncomputable def pmn (a b : ℝ) : ℝ := if a ≤ b then a else b
noncomputable def pab (a : ℝ) : ℝ := if 0 ≤ a then a else -a

noncomputable def prog (x0 x1 : ℝ) : ℝ :=
  pab (pmn (pmx (x0 + (5/2)) ((-1) * x0 + (-1/2))) (2 * x1 + 3))
-- PROOF
lemma pmx_eq (a b : ℝ) : pmx a b = max a b := by
  unfold pmx
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (not_le.mp h).le).symm

lemma pmn_eq (a b : ℝ) : pmn a b = min a b := by
  unfold pmn
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (not_le.mp h).le).symm

lemma pab_eq (a : ℝ) : pab a = |a| := by
  unfold pab
  split_ifs with h
  · exact (abs_of_nonneg h).symm
  · exact (abs_of_neg (not_le.mp h)).symm

theorem prog_correct : StatementProg prog := by
  intro x0 x1 _ _ _ _
  unfold prog spec
  rw [pab_eq, pmn_eq, pmx_eq]

end Lane4.Case
