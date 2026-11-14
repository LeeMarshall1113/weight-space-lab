namespace Lane4.Case

noncomputable def absf (t : ℝ) : ℝ := if 0 ≤ t then t else -t

noncomputable def med (a b c : ℝ) : ℝ :=
  if a ≤ b then
    (if b ≤ c then b else if a ≤ c then c else a)
  else
    (if a ≤ c then a else if b ≤ c then c else b)

noncomputable def prog (x0 x1 x2 : ℝ) : ℝ :=
  med (absf (3 * x1 + 1)) (x0 + (1/2) * x2 + 2) (3 * x1 + (1/2))

-- PROOF

theorem absf_eq (t : ℝ) : absf t = |t| := by
  unfold absf
  split_ifs with h
  · exact (abs_of_nonneg h).symm
  · exact (abs_of_neg (not_le.mp h)).symm

theorem med_eq (a b c : ℝ) : med a b c = max (min a b) (min (max a b) c) := by
  unfold med
  simp only [max_def, min_def]
  split_ifs <;> first | rfl | (exfalso; linarith) | linarith

theorem prog_correct : StatementProg prog := by
  intro x0 x1 x2 _ _ _ _ _ _
  unfold prog spec
  rw [med_eq, absf_eq]

end Lane4.Case
