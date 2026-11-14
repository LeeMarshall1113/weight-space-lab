namespace Lane4.Case
open Lane4
def net : Net :=
  { hidden := [{ W := [[1, 0], [-1, 0], [-1, 1]], b := [0, 0, 0] }],
    out := { W := [[1, -1, 1]], b := [0] } }
theorem net_correct : Statement net := by
  intro x0 x1 _ _ _ _
  have h1 := relu_sub_relu_neg x0
  have h2 := add_relu_sub x0 x1
  simp only [net, Net.eval, Layer.apply, dot, spec, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true]
  push_cast
  ring_nf
  ring_nf at h1 h2
  linarith
end Lane4.Case
