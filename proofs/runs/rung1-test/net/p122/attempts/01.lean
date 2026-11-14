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
  done
end Lane4.Case
