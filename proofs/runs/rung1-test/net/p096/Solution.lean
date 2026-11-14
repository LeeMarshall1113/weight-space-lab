namespace Lane4.Case
open Lane4

def net : Net :=
  { hidden :=
      [{ W := [[2, -1], [-2, 1], [-2, 2], [2, -2], [-2, 3], [2, -2], [2, -2]],
         b := [-1/2, 1/2, -1/2, 1/2, -1/2, 1/2, -1] },
       { W := [[1, 1, 0, 0, 0, 0, 0], [1, 1, 1/2, -1/2, -1/2, -1, 1]],
         b := [0, -1] }],
    out := { W := [[1, -1]], b := [0] } }

theorem net_correct : Statement net := by
  intro x0 x1 _ _ _ _
  have e1 := relu_add_relu_neg (2 * x0 + (-1) * x1 + (-1/2))
  have e2 := relu_sub_relu_neg ((-2) * x0 + 2 * x1 + (-1/2))
  have e3 := sub_relu_sub ((-2) * x0 + 2 * x1 + (-1/2)) ((-1) * x1)
  have e4 : relu (2 * x0 + (-2) * x1 + (3/2) - 1) - relu (2 * x0 + (-2) * x1 + (3/2) - 5/2)
      = min (max (2 * x0 + (-2) * x1 + (3/2)) 1) (5/2) - 1 := by
    unfold relu
    rcases le_total (2 * x0 + (-2) * x1 + (3/2)) 1 with h | h
    · rw [max_eq_right (by linarith : 2 * x0 + (-2) * x1 + (3/2) - 1 ≤ 0),
        max_eq_right (by linarith : 2 * x0 + (-2) * x1 + (3/2) - 5/2 ≤ 0),
        max_eq_right h, min_eq_left (by norm_num)]; ring
    · rw [max_eq_left h, max_eq_left (by linarith : (0:ℝ) ≤ 2 * x0 + (-2) * x1 + (3/2) - 1)]
      rcases le_total (2 * x0 + (-2) * x1 + (3/2)) (5/2) with h' | h'
      · rw [max_eq_right (by linarith : 2 * x0 + (-2) * x1 + (3/2) - 5/2 ≤ 0), min_eq_left h']; ring
      · rw [max_eq_left (by linarith : (0:ℝ) ≤ 2 * x0 + (-2) * x1 + (3/2) - 5/2), min_eq_right h']; ring
  have key : net.eval [x0, x1] =
      [relu (relu (2 * x0 + (-1) * x1 + (-1/2)) + relu (-(2 * x0 + (-1) * x1 + (-1/2))))
       - relu (relu (2 * x0 + (-1) * x1 + (-1/2)) + relu (-(2 * x0 + (-1) * x1 + (-1/2)))
         + 1/2 * relu ((-2) * x0 + 2 * x1 + (-1/2)) - 1/2 * relu (-((-2) * x0 + 2 * x1 + (-1/2)))
         - 1/2 * relu ((-2) * x0 + 2 * x1 + (-1/2) - (-1) * x1)
         - relu (2 * x0 + (-2) * x1 + (3/2) - 1) + relu (2 * x0 + (-2) * x1 + (3/2) - 5/2) - 1)] := by
    simp only [net, Net.eval, Layer.apply, dot, List.foldl, List.map, List.zipWith,
      List.sum_cons, List.sum_nil]
    push_cast
    ring_nf
  rw [key]
  simp only [spec, List.cons.injEq, and_true]
  rw [e1, relu_of_nonneg (abs_nonneg _)]
  have e5 : |2 * x0 + (-1) * x1 + (-1/2)| + 1/2 * relu ((-2) * x0 + 2 * x1 + (-1/2))
      - 1/2 * relu (-((-2) * x0 + 2 * x1 + (-1/2)))
      - 1/2 * relu ((-2) * x0 + 2 * x1 + (-1/2) - (-1) * x1)
      - relu (2 * x0 + (-2) * x1 + (3/2) - 1) + relu (2 * x0 + (-2) * x1 + (3/2) - 5/2) - 1
      = |2 * x0 + (-1) * x1 + (-1/2)| - ((-1/2) * (min ((-2) * x0 + 2 * x1 + (-1/2)) ((-1) * x1)) + 1 * (min (max (2 * x0 + (-2) * x1 + (3/2)) 1) (5/2))) := by
    linarith
  rw [e5]
  exact sub_relu_sub _ _
end Lane4.Case
