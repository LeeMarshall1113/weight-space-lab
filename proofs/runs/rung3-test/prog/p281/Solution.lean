namespace Lane4.Case

noncomputable def hA (x0 : ℝ) : ℝ := if 3 ≤ x0 then (1/2) * x0 + (-3/2) else 0

noncomputable def hAbs (m : ℝ) : ℝ := if 0 ≤ m then m else -m

noncomputable def hM (x0 x1 : ℝ) : ℝ :=
  if (-1) * x0 + 3 * x1 + 2 ≤ (-1) * x1 + (-3/2) then (-1) * x1 + (-3/2)
  else if (-1) * x0 + 3 * x1 + 2 ≤ (-1/2) * x1 + (3/2) then (-1) * x0 + 3 * x1 + 2
  else (-1/2) * x1 + (3/2)

noncomputable def hFin (s x0 : ℝ) : ℝ := if s ≤ (-1) * x0 + (1/2) then s else (-1) * x0 + (1/2)

noncomputable def prog (x0 x1 : ℝ) : ℝ :=
  hFin ((-2) * hA x0 + (-2) * hAbs (hM x0 x1)) x0
-- PROOF
lemma hA_eq (x0 : ℝ) : hA x0 = max ((1/2) * x0 + (-3/2)) 0 := by
  unfold hA
  split_ifs with h
  · exact (max_eq_left (by linarith)).symm
  · exact (max_eq_right (by linarith)).symm

lemma hAbs_eq (m : ℝ) : hAbs m = |m| := by
  unfold hAbs
  split_ifs with h
  · exact (abs_of_nonneg h).symm
  · exact (abs_of_neg (not_le.mp h)).symm

lemma hFin_eq (s x0 : ℝ) : hFin s x0 = min s ((-1) * x0 + (1/2)) := by
  unfold hFin
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_lt (not_le.mp h))).symm

lemma hM_eq (x0 x1 : ℝ) (h3 : (-4) ≤ x1) (h4 : x1 ≤ 1) :
    hM x0 x1 = max (min ((-1) * x1 + (-3/2)) ((-1/2) * x1 + (3/2)))
      (min (max ((-1) * x1 + (-3/2)) ((-1/2) * x1 + (3/2))) ((-1) * x0 + 3 * x1 + 2)) := by
  have e1 : min ((-1) * x1 + (-3/2)) ((-1/2) * x1 + (3/2)) = (-1) * x1 + (-3/2) :=
    min_eq_left (by linarith)
  have e2 : max ((-1) * x1 + (-3/2)) ((-1/2) * x1 + (3/2)) = (-1/2) * x1 + (3/2) :=
    max_eq_right (by linarith)
  rw [e1, e2]
  unfold hM
  split_ifs with h h'
  · rw [min_eq_right (by linarith)]
    exact (max_eq_left (by linarith)).symm
  · rw [min_eq_right (by linarith)]
    exact (max_eq_right (by linarith)).symm
  · rw [min_eq_left (by linarith)]
    exact (max_eq_right (by linarith)).symm

theorem prog_correct : StatementProg prog := by
  intro x0 x1 h1 h2 h3 h4
  unfold prog spec
  rw [hFin_eq, hA_eq, hAbs_eq, hM_eq x0 x1 h3 h4]

end Lane4.Case
