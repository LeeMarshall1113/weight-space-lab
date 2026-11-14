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
  have hc : (relu ((-2) * x1 + (-1/2) * x2 + (-3/2)) - relu (-((-2) * x1 + (-1/2) * x2 + (-3/2))))
      = (-2) * x1 + (-1/2) * x2 + (-3/2) := e3
  set m := max ((-2) * x0 + (1/2) * x2 + (1/2)) ((-2) * x2 + 2) with hmdef
  set c := (-2) * x1 + (-1/2) * x2 + (-3/2) with hcdef
  have e4 := relu_sub_relu_neg m
  have e5 := sub_relu_sub m c
  simp only [net, Net.eval, Layer.apply, dot, spec, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true]
  push_cast
  done
