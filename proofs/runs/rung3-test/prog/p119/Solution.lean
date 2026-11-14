namespace Lane4.Case

noncomputable def A (x : ℝ) : ℝ := if -x - 1 ≤ x + 1 then x + 1 else -x - 1

noncomputable def M (x : ℝ) : ℝ := if -2 * x ≤ -x / 2 - 1 then -2 * x else -x / 2 - 1

noncomputable def B (x : ℝ) : ℝ := if -2 * x - 3 / 2 ≤ M x then M x else -2 * x - 3 / 2

noncomputable def prog (x0 : ℝ) : ℝ := if A x0 ≤ B x0 then B x0 else A x0

-- PROOF
theorem A_eq (x : ℝ) : A x = |(-1) * x + (-1)| := by
  unfold A
  rcases le_total (-x - 1) (x + 1) with h | h
  · rw [if_pos h, abs_of_nonpos (by linarith)]; ring_nf
  · rcases eq_or_lt_of_le h with h' | h'
    · rw [if_pos (by linarith), abs_of_nonpos (by linarith)]; ring_nf
    · rw [if_neg (by linarith), abs_of_nonneg (by linarith)]; ring_nf

theorem M_eq (x : ℝ) : M x = min (-2 * x) ((-1/2) * x + (-1)) := by
  unfold M
  rcases le_total (-2 * x) (-x / 2 - 1) with h | h
  · rw [if_pos h, min_eq_left (by linarith)]
  · rcases eq_or_lt_of_le h with h' | h'
    · rw [if_pos (by linarith), min_eq_left (by linarith)]
    · rw [if_neg (by linarith), min_eq_right (by linarith)]; ring

theorem B_eq (x : ℝ) : B x = max (-2 * x + -3 / 2) (M x) := by
  unfold B
  rcases le_total (-2 * x - 3 / 2) (M x) with h | h
  · rw [if_pos h, max_eq_right (by linarith)]
  · rcases eq_or_lt_of_le h with h' | h'
    · rw [if_pos (by linarith), max_eq_right (by linarith)]
    · rw [if_neg (by linarith), max_eq_left (by linarith)]; ring

theorem prog_correct : StatementProg prog := by
  intro x _ _
  have h1 : min (-2 * x) (-2 * x + -3 / 2) = -2 * x + -3 / 2 := min_eq_right (by linarith)
  have h2 : max (-2 * x) (-2 * x + -3 / 2) = -2 * x := max_eq_left (by linarith)
  have h3 : spec x = max (A x) (max (-2 * x + -3 / 2) (M x)) := by
    unfold spec
    rw [h1, h2, A_eq, M_eq]
  have h4 : prog x = max (A x) (B x) := by
    unfold prog
    rcases le_total (A x) (B x) with h | h
    · rw [if_pos h, max_eq_right h]
    · rcases eq_or_lt_of_le h with h' | h'
      · rw [if_pos (by linarith), max_eq_right (by linarith)]
      · rw [if_neg (by linarith), max_eq_left (by linarith)]
  rw [h4, h3, B_eq]

end Lane4.Case
