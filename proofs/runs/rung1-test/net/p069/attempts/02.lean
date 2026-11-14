namespace Lane4.Case
open Lane4

def net : Net :=
  { hidden :=
      [{ W := [[-2, 0, 1/2], [2, 0, -1/2], [2, 0, -5/2], [0, -2, -1/2], [0, 2, 1/2]],
         b := [1/2, -1/2, 3/2, -3/2, 3/2] },
       { W := [[1, -1, 1, 0, 0], [-1, 1, -1, 0, 0], [1, -1, 1, -1, 1]],
         b := [0, 0, 0] }],
    out := { W := [[1, -1, -1]], b := [0] } }

theorem net_correct : Statement net := by
  intro x0 x1 x2 _ _ _ _ _ _
  have e1 := relu_sub_relu_neg ((-2) * x0 + (1/2) * x2 + (1/2))
  have e2 := add_relu_sub ((-2) * x0 + (1/2) * x2 + (1/2)) ((-2) * x2 + 2)
  have e3 := relu_sub_relu_neg ((-2) * x1 + (-1/2) * x2 + (-3/2))
  have hm : (relu ((-2) * x0 + (1/2) * x2 + (1/2)) - relu (-((-2) * x0 + (1/2) * x2 + (1/2)))
      + relu ((-2) * x2 + 2 - ((-2) * x0 + (1/2) * x2 + (1/2))))
      = max ((-2) * x0 + (1/2) * x2 + (1/2)) ((-2) * x2 + 2) := by
    rw [← e2]; linarith
  have e4 := relu_sub_relu_neg (max ((-2) * x0 + (1/2) * x2 + (1/2)) ((-2) * x2 + 2))
  have e5 := sub_relu_sub (max ((-2) * x0 + (1/2) * x2 + (1/2)) ((-2) * x2 + 2))
    ((-2) * x1 + (-1/2) * x2 + (-3/2))
  have k1 : relu (-2 * x0 + (0 * x1 + (1 / 2 * x2 + 0)) + 1 / 2)
      = relu ((-2) * x0 + (1/2) * x2 + (1/2)) := by congr 1; ring
  have k2 : relu (2 * x0 + (0 * x1 + (-1 / 2 * x2 + 0)) + -1 / 2)
      = relu (-((-2) * x0 + (1/2) * x2 + (1/2))) := by congr 1; ring
  have k3 : relu (2 * x0 + (0 * x1 + (-5 / 2 * x2 + 0)) + 3 / 2)
      = relu ((-2) * x2 + 2 - ((-2) * x0 + (1/2) * x2 + (1/2))) := by congr 1; ring
  have k4 : relu (0 * x0 + (-2 * x1 + (-1 / 2 * x2 + 0)) + -3 / 2)
      = relu ((-2) * x1 + (-1/2) * x2 + (-3/2)) := by congr 1; ring
  have k5 : relu (0 * x0 + (2 * x1 + (1 / 2 * x2 + 0)) + 3 / 2)
      = relu (-((-2) * x1 + (-1/2) * x2 + (-3/2))) := by congr 1; ring
  have A : ∀ P Q R S T : ℝ,
      relu (1 * P + (-1 * Q + (1 * R + (0 * S + (0 * T + 0)))) + 0) = relu (P - Q + R) := by
    intros; congr 1; ring
  have B : ∀ P Q R S T : ℝ,
      relu (-1 * P + (1 * Q + (-1 * R + (0 * S + (0 * T + 0)))) + 0) = relu (-(P - Q + R)) := by
    intros; congr 1; ring
  have C : ∀ P Q R S T : ℝ,
      relu (1 * P + (-1 * Q + (1 * R + (-1 * S + (1 * T + 0)))) + 0)
        = relu ((P - Q + R) - (S - T)) := by
    intros; congr 1; ring
  simp only [net, Net.eval, Layer.apply, dot, spec, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true]
  push_cast
  rw [k1, k2, k3, k4, k5, A, B, C, hm, e3]
  linarith
end Lane4.Case
