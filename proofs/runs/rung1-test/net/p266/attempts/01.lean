namespace Lane4.Case
open Lane4
def net : Net :=
  { hidden :=
    [ { W := [[-2, 0, 1/2], [2, 0, -1/2], [0, 0, -1/2], [0, 0, 1/2], [-2, 0, 1], [3, -1, 0], [-1, 0, 0], [1, 0, 0]],
        b := [-3/2, 3/2, -1, 1, -1/2, 5, -3, 3] },
      { W := [[1, -1, 0, 0, -1, 0, 0, 0], [-1, 1, 0, 0, 1, 0, 0, 0],
              [0, 0, 1, -1, 1, 0, 0, 0], [0, 0, -1, 1, -1, 0, 0, 0],
              [0, 0, 1, -1, 1, -1, -1, 1]],
        b := [0, 0, 0, 0, 0] },
      { W := [[-1, 1, 1, -1, -1], [1, 0, 0, 0, 0], [0, 1, 0, 0, 0]],
        b := [0, 0, 0] },
      { W := [[1, 1, -1]], b := [0] } ],
    out := { W := [[1]], b := [0] } }
theorem net_correct : Statement net := by
  intro x0 x1 x2 _ _ _ _ _ _
  simp only [net, Net.eval, Layer.apply, dot, spec, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true]
  push_cast
  done
end Lane4.Case
