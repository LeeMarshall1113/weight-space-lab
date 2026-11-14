namespace Lane4.Case
open Lane4
def net : Net :=
  { hidden := [{ W := [[1], [1], [1], [1], [-1]], b := [5/2, 1, 0, -1, 0] }],
    out := { W := [[-1, 5/2, -5/2, 3/2, 1]], b := [5/2] } }
theorem net_correct : Statement net := by
  intro x0 _ _
  have mxl : ∀ a b : ℝ, b ≤ a → max a b = a := fun a b h => max_eq_left h
  have mxr : ∀ a b : ℝ, a ≤ b → max a b = b := fun a b h => max_eq_right h
  have mnl : ∀ a b : ℝ, a ≤ b → min a b = a := fun a b h => min_eq_left h
  have mnr : ∀ a b : ℝ, b ≤ a → min a b = b := fun a b h => min_eq_right h
  simp only [net, Net.eval, Layer.apply, dot, spec, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true, relu]
  push_cast
  rcases le_total x0 (-5/2) with h1 | h1
  · trace_state
    simp (disch := linarith) only [mxl, mxr, mnl, mnr]
    linarith
  rcases le_total x0 (-1) with h2 | h2
  · simp (disch := linarith) only [mxl, mxr, mnl, mnr]
    linarith
  rcases le_total x0 (-2/5) with h3 | h3
  · simp (disch := linarith) only [mxl, mxr, mnl, mnr]
    linarith
  rcases le_total x0 0 with h4 | h4
  · simp (disch := linarith) only [mxl, mxr, mnl, mnr]
    linarith
  rcases le_total x0 1 with h5 | h5
  · simp (disch := linarith) only [mxl, mxr, mnl, mnr]
    linarith
  · simp (disch := linarith) only [mxl, mxr, mnl, mnr]
    linarith
end Lane4.Case
