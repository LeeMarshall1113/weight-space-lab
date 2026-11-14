namespace Lane4.Case
open Lane4
def net : Net :=
  { hidden := [{ W := [[1], [1], [1], [1], [-1]], b := [5/2, 1, 0, -1, 0] }],
    out := { W := [[-1, 5/2, -5/2, 3/2, 1]], b := [5/2] } }
theorem net_correct : Statement net := by
  intro x0 _ _
  simp only [net, Net.eval, Layer.apply, dot, spec, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true, relu]
  push_cast
  rcases le_total x0 (-5/2) with h1 | h1
  · simp (disch := linarith) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right]
    linarith
  rcases le_total x0 (-1) with h2 | h2
  · simp (disch := linarith) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right]
    linarith
  rcases le_total x0 (-2/5) with h3 | h3
  · simp (disch := linarith) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right]
    linarith
  rcases le_total x0 0 with h4 | h4
  · simp (disch := linarith) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right]
    linarith
  rcases le_total x0 1 with h5 | h5
  · simp (disch := linarith) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right]
    linarith
  · simp (disch := linarith) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right]
    linarith
end Lane4.Case
