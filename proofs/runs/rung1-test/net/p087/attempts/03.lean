namespace Lane4.Case
open Lane4
def net : Net :=
  { hidden :=
    [ { W := [[0, 3, 2], [0, 3, 0], [1, 0, 0], [-1/2, 0, 0]], b := [1/2, 20, 43/2, 35/2] },
      { W := [[1, -1, 1, 0], [-1, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], b := [0, 0, 0, 0] },
      { W := [[-1, -1, 0, 1], [-1, 0, 1, 0], [0, 0, 0, 1]], b := [0, 0, 0] },
      { W := [[-1, -1, 1], [0, 1, 0]], b := [0, 0] } ],
    out := { W := [[1, 1]], b := [-20] } }

theorem relu_cases' (a r : ℝ) (h : relu a = r) : (r = a ∧ 0 ≤ a) ∨ (r = 0 ∧ a ≤ 0) := by
  rcases le_total 0 a with h' | h'
  · left; exact ⟨by rw [← h, relu_of_nonneg h'], h'⟩
  · right; exact ⟨by rw [← h, relu_of_nonpos h'], h'⟩

theorem relu_rr (a : ℝ) : relu (relu a) = relu a := max_eq_left (le_max_right a 0)

theorem net_correct : Statement net := by
  intro x0 x1 x2 h1 h2 h3 h4 h5 h6
  simp only [net, Net.eval, Layer.apply, dot, spec, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true]
  push_cast
  simp only [zero_mul, one_mul, neg_one_mul, zero_add, add_zero,
    relu_of_nonneg (show (0:ℝ) ≤ 3 * x1 + 20 by linarith),
    relu_of_nonneg (show (0:ℝ) ≤ x0 + 43 / 2 by linarith),
    relu_of_nonneg (show (0:ℝ) ≤ -1 / 2 * x0 + 35 / 2 by linarith), relu_rr]
  generalize hg : relu (3 * x1 + 2 * x2 + 1 / 2) = g
  generalize hk1 : relu (g + (-(3 * x1 + 20) + (x0 + 43 / 2))) = k1
  have hg' := relu_cases' _ _ hg
  have hk1' := relu_cases' _ _ hk1
  have hk2 : relu (-g + (3 * x1 + 20)) = -g + (3 * x1 + 20) :=
    relu_of_nonneg (by rcases hg' with ⟨a, b⟩ | ⟨a, b⟩ <;> linarith)
  rw [hk2]
  generalize hj3 : relu (-k1 + (x0 + 43 / 2)) = j3
  have hj3e : j3 = -k1 + (x0 + 43 / 2) := by
    rw [← hj3]
    exact relu_of_nonneg (by
      rcases hg' with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases hk1' with ⟨c, d⟩ | ⟨c, d⟩ <;> linarith)
  generalize hj1 : relu (-k1 + (-(-g + (3 * x1 + 20)) + (-1 / 2 * x0 + 35 / 2))) = j1
  generalize ht : relu (-j1 + (-j3 + (-1 / 2 * x0 + 35 / 2))) = t
  have hj1' := relu_cases' _ _ hj1
  have ht' := relu_cases' _ _ ht
  have Fm : min (3 * x1) (-2 * x2 + -1 / 2) = 3 * x1 - g := by
    rcases hg' with ⟨a, b⟩ | ⟨a, b⟩
    · rw [min_eq_right (by linarith)]; linarith
    · rw [min_eq_left (by linarith)]; linarith
  have Fp : min (3 * x1 - g) (x0 + 3 / 2) = x0 + 3 / 2 - k1 := by
    rcases hk1' with ⟨a, b⟩ | ⟨a, b⟩
    · rw [min_eq_left (by linarith)]; linarith
    · rw [min_eq_right (by linarith)]; linarith
  have Fq : max (3 * x1 - g) (x0 + 3 / 2) = 3 * x1 - g + k1 := by
    rcases hk1' with ⟨a, b⟩ | ⟨a, b⟩
    · rw [max_eq_right (by linarith)]; linarith
    · rw [max_eq_left (by linarith)]; linarith
  have Fr : min (3 * x1 - g + k1) (-1 / 2 * x0 + -5 / 2) = -1 / 2 * x0 + -5 / 2 - j1 := by
    rcases hj1' with ⟨a, b⟩ | ⟨a, b⟩
    · rw [min_eq_left (by linarith)]; linarith
    · rw [min_eq_right (by linarith)]; linarith
  rw [Fm, Fp, Fq, Fr]
  rcases ht' with ⟨a, b⟩ | ⟨a, b⟩
  · rw [max_eq_right (by linarith)]; linarith
  · rw [max_eq_left (by linarith)]; linarith
end Lane4.Case
