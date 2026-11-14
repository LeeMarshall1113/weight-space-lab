namespace Lane4.Case
open Lane4
def net : Net :=
  { hidden := [{ W := [[-2, 0], [1, 3], [-1, -3]], b := [1, 0, 0] },
               { W := [[-1, 1, -1], [1, 0, 0]], b := [0, 0] }],
    out := { W := [[1, 1]], b := [0] } }
theorem net_correct : Statement net := by
  intro x0 x1 _ _ _ _
  simp only [net, Net.eval, Layer.apply, dot, spec, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true, relu]
  push_cast
  simp only [max_def]
  split_ifs <;> linarith
end Lane4.Case
