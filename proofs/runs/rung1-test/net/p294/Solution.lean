namespace Lane4.Case
open Lane4
def net : Net :=
  { hidden := [{ W := [[1], [1], [1], [1], [-1]], b := [5/2, 1, 0, -1, 0] }],
    out := { W := [[-1, 5/2, -5/2, 3/2, 1]], b := [5/2] } }
set_option maxHeartbeats 0 in
theorem net_correct : Statement net := by
  intro x0 _ _
  simp only [net, Net.eval, Layer.apply, dot, spec, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true, relu]
  push_cast
  simp only [max_def, min_def]
  split_ifs <;> linarith
end Lane4.Case
