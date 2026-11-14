namespace Lane4.Case
open Lane4
def net : Net :=
  { hidden := [
      { W := [[0, 3, 0], [0, -3, 0], [1, 0, 1/2], [0, 3, 0]], b := [1, -1, 5, 13/2] },
      { W := [[1, 1, 0, 0], [1, 1, -1, 0], [-1, -1, 1, 0], [0, 0, 0, 1]], b := [0, 3, -3, 0] },
      { W := [[1, 0, 1, -1], [1, -1, 0, 0], [1, 0, 1, 0]], b := [6, 3, 0] },
      { W := [[-1, -1, 1], [0, 1, 0]], b := [3, 0] }],
    out := { W := [[1, 1]], b := [-3] } }
theorem net_correct : Statement net := by
  intro x0 x1 x2 h0 h1 h2 h3 h4 h5
  simp only [net, Net.eval, Layer.apply, dot, spec, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true]
  push_cast
  have hP : relu (0 * x0 + (3 * x1 + (0 * x2 + 0)) + 1) = relu (3 * x1 + 1) := by
    congr 1; ring
  have hQ : relu (0 * x0 + (-3 * x1 + (0 * x2 + 0)) + -1) = relu (-(3 * x1 + 1)) := by
    congr 1; ring
  have hB : relu (1 * x0 + (0 * x1 + (1 / 2 * x2 + 0)) + 5) = x0 + 1 / 2 * x2 + 5 := by
    rw [relu_of_nonneg (by linarith)]; ring
  have hC : relu (0 * x0 + (3 * x1 + (0 * x2 + 0)) + 13 / 2) = 3 * x1 + 13 / 2 := by
    rw [relu_of_nonneg (by linarith)]; ring
  rw [hP, hQ, hB, hC]
  have e1 := relu_sub_relu_neg (3 * x1 + 1)
  have e2 := relu_add_relu_neg (3 * x1 + 1)
  have n1 : 0 ≤ relu (3 * x1 + 1) := le_max_right _ _
  have n2 : 0 ≤ relu (-(3 * x1 + 1)) := le_max_right _ _
  rw [← e2]
  generalize relu (3 * x1 + 1) = P at *
  generalize relu (-(3 * x1 + 1)) = Q at *
  simp only [relu]
  simp only [max_def, min_def]
  split_ifs <;> linarith
end Lane4.Case
