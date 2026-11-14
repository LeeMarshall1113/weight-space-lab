namespace Lane4.Case
open Lane4
def net : Net :=
  { hidden := [{ W := [[0, 1], [-1, 1], [-1, 2], [1, -2], [-1, -5/2], [1, 5/2]],
                 b := [1, 3/2, 5/2, -5/2, -7/2, 7/2] },
               { W := [[1,0,0,0,0,0], [0,1,0,0,0,0], [0,0,1,0,0,0], [0,0,0,1,0,0],
                       [0,1,0,0,1,-1]],
                 b := [0, 0, 0, 0, 0] }],
    out := { W := [[1, -1/2, 1/2, -1/2, 1/2]], b := [0] } }

theorem net_correct : Statement net := by
  intro x0 x1 _ _ _ _
  have rr : ∀ a : ℝ, relu (relu a) = relu a := fun a => relu_of_nonneg (le_max_right a 0)
  have hA := relu_sub_relu_neg ((-1) * x0 + 2 * x1 + (5/2))
  have hq := relu_sub_relu_neg ((-1) * x0 + (-5/2) * x1 + (-7/2))
  have hm := sub_relu_sub ((-1) * x0 + 2 * x1 + (5/2)) (x1 + 1)
  have e1 : ((-1) * x0 + 2 * x1 + (5/2)) - (x1 + 1) = (-1) * x0 + 1 * x1 + 3/2 := by ring
  rw [e1] at hm
  have hs := add_relu_sub (min ((-1) * x0 + 2 * x1 + (5/2)) (x1 + 1))
    ((-2) * x0 + (-1/2) * x1 + (-1))
  rw [← hm] at hs
  have e2 : (-2) * x0 + (-1/2) * x1 + (-1) - ((-1) * x0 + 2 * x1 + (5/2) - relu ((-1) * x0 + 1 * x1 + 3/2))
      = ((-1) * x0 + (-5/2) * x1 + (-7/2) + relu ((-1) * x0 + 1 * x1 + 3/2)) - 0 := by ring
  have e3 : (-1) * x0 + (-5/2) * x1 + (-7/2) + relu ((-1) * x0 + 1 * x1 + 3/2)
      = relu ((-1) * x0 + (-5/2) * x1 + (-7/2)) - relu (-((-1) * x0 + (-5/2) * x1 + (-7/2)))
        + relu ((-1) * x0 + 1 * x1 + 3/2) := by linarith
  rw [e2, e3] at hs
  simp only [net, Net.eval, Layer.apply, dot, spec, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true, rr]
  try push_cast
  try simp only [rr]
  ring_nf at hA hq hs hm ⊢
  unfold relu at hA hq hs hm ⊢
  simp only [max_assoc, max_self]
  rw [← hm]
  linarith
end Lane4.Case
