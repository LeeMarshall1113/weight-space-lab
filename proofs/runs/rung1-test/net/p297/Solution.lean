namespace Lane4.Case
open Lane4
def net : Net :=
  { hidden := [{ W := [[3], [-3], [4]], b := [2, -2, 3/2] },
               { W := [[1, -1, -1], [-1, 1, 1]], b := [0, 0] }],
    out := { W := [[1, 1]], b := [0] } }
theorem net_correct : Statement net := by
  intro x0 _ _
  have h1 := relu_sub_relu_neg (3 * x0 + 2)
  have h2 := sub_relu_sub (3 * x0 + 2) ((-1) * x0 + (1/2))
  have h3 := relu_add_relu_neg (relu (3 * x0 + 2) - relu (-(3 * x0 + 2)) - relu (4 * x0 + 3/2))
  have e1 : relu (-3 * x0 - 2) = relu (-(3 * x0 + 2)) := by congr 1; ring
  have e2 : relu (3 * x0 + 2 - ((-1) * x0 + (1/2))) = relu (4 * x0 + 3/2) := by congr 1; ring
  rw [e2] at h2
  have hm : relu (3 * x0 + 2) - relu (-(3 * x0 + 2)) - relu (4 * x0 + 3/2)
      = min (3 * x0 + 2) ((-1) * x0 + (1/2)) := by linarith
  rw [hm] at h3
  have e3 : relu (-(relu (3 * x0 + 2) - relu (-(3 * x0 + 2)) - relu (4 * x0 + 3/2)))
      = relu (-(min (3 * x0 + 2) ((-1) * x0 + (1/2)))) := by rw [hm]
  simp only [net, Net.eval, Layer.apply, dot, spec, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true]
  push_cast
  have e4 : relu (-3 * x0 + -2) = relu (-(3 * x0 + 2)) := by congr 1; ring
  have e5 : relu (4 * x0 + 3/2) = relu (4 * x0 + 3/2) := rfl
  ring_nf at *
  have hm' : -relu (2 + x0 * 3) + relu (-2 - x0 * 3) + relu (3 / 2 + x0 * 4)
      = -min (2 + x0 * 3) (1 / 2 - x0) := by linarith
  rw [hm, hm']
  linarith
end Lane4.Case
