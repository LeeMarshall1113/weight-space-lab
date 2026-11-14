namespace Lane4.Case
open Lane4

def net : Net :=
  { hidden := [{ W := [[-1, 0], [0, -2], [0, 3]], b := [1/2, 4, 5/2] },
               { W := [[1, 0, 0], [0, -1, 0], [0, 0, -1]], b := [0, 3, 1] },
               { W := [[1, 0, 0], [-1, -1, 0], [0, 0, 1]], b := [0, 3/2, 0] }],
    out := { W := [[-1, -1, -1/2]], b := [-1/4] } }

theorem net_correct : Statement net := by
  intro x0 x1 _ _ _ _
  simp only [net, Net.eval, Layer.apply, dot, spec, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true]
  push_cast
  simp only [relu, max_def, min_def]
  split_ifs <;> first | (exfalso; linarith) | linarith
end Lane4.Case
