namespace Lane4.Case

noncomputable def A (x : ℝ) : ℝ := if -x - 1 ≤ x + 1 then x + 1 else -x - 1

noncomputable def M (x : ℝ) : ℝ := if -2 * x ≤ -x / 2 - 1 then -2 * x else -x / 2 - 1

noncomputable def B (x : ℝ) : ℝ := if -2 * x - 3 / 2 ≤ M x then M x else -2 * x - 3 / 2

noncomputable def prog (x0 : ℝ) : ℝ := if A x0 ≤ B x0 then B x0 else A x0

-- PROOF
theorem prog_correct : StatementProg prog := by
  intro x _ _
  have h1 : min (-2 * x) (-2 * x + -3 / 2) = -2 * x + -3 / 2 := min_eq_right (by linarith)
  have h2 : max (-2 * x) (-2 * x + -3 / 2) = -2 * x := max_eq_left (by linarith)
  unfold prog spec A B M
  rw [h1, h2]
  simp only [abs_eq_max_neg, max_def, min_def]
  split_ifs <;> linarith

end Lane4.Case
