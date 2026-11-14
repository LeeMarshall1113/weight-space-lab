namespace Lane4.Case
open Lane4
def net : Net :=
  { hidden :=
    [ { W := [[0, 3, 2], [0, 3, 0], [1, 0, 0], [-1/2, 0, 0]], b := [1/2, 20, 43/2, 35/2] },
      { W := [[1, -1, 1, 0], [-1, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], b := [0, 0, 0, 0] },
      { W := [[-1, -1, 0, 1], [-1, 0, 1, 0], [0, 0, 0, 1]], b := [0, 0, 0] },
      { W := [[-1, -1, 1], [0, 1, 0]], b := [0, 0] } ],
    out := { W := [[1, 1]], b := [-20] } }
theorem net_correct : Statement net := by
  intro x0 x1 x2 h1 h2 h3 h4 h5 h6
  simp only [net, Net.eval, Layer.apply, dot, spec, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true]
  push_cast
  simp only [zero_mul, one_mul, neg_mul, zero_add, add_zero, mul_zero]
  done
end Lane4.Case
