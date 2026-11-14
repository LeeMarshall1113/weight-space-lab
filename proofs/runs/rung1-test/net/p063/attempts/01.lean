namespace Lane4.Case
open Lane4

def net : Net :=
  { hidden := [{ W := [[5/2, 3], [1/2, 0], [-1/2, 0]], b := [3/2, -1/2, 1/2] },
               { W := [[1, 1, -1], [-1, -1, 1]], b := [0, 0] }],
    out := { W := [[1, 1]], b := [0] } }

theorem net_correct : Statement net := by
  intro x0 x1 _ _ _ _
  have h1 := relu_sub_relu_neg ((1/2:ℝ) * x0 + (-1/2))
  have h2 := add_relu_sub ((1/2:ℝ) * x0 + (-1/2)) (3 * x0 + 3 * x1 + 1)
  have hm : relu (5/2 * x0 + 3 * x1 + 3/2 : ℝ) + relu (1/2 * x0 + 0 * x1 + -1/2 : ℝ)
      - relu (-1/2 * x0 + 0 * x1 + 1/2 : ℝ) = max (3 * x0 + 3 * x1 + 1) ((1/2:ℝ) * x0 + (-1/2)) := by
    rw [max_comm, ← h2]
    have e1 : (3 * x0 + 3 * x1 + 1 - ((1/2:ℝ) * x0 + (-1/2))) = 5/2 * x0 + 3 * x1 + 3/2 := by ring
    have e2 : (1/2 * x0 + 0 * x1 + -1/2 : ℝ) = (1/2:ℝ) * x0 + (-1/2) := by ring
    have e3 : (-1/2 * x0 + 0 * x1 + 1/2 : ℝ) = -((1/2:ℝ) * x0 + (-1/2)) := by ring
    rw [e1, e2, e3]
    linarith
  have h3 := relu_add_relu_neg (max (3 * x0 + 3 * x1 + 1) ((1/2:ℝ) * x0 + (-1/2)))
  simp only [net, Net.eval, Layer.apply, dot, spec, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true]
  push_cast
  rw [← hm] at h3
  have k1 : ∀ m : ℝ, relu (1 * (relu (5/2 * x0 + 3 * x1 + 3/2 : ℝ)) + 1 * relu (1/2 * x0 + 0 * x1 + -1/2 : ℝ)
      + -1 * relu (-1/2 * x0 + 0 * x1 + 1/2 : ℝ) + 0) = relu (relu (5/2 * x0 + 3 * x1 + 3/2 : ℝ) + relu (1/2 * x0 + 0 * x1 + -1/2 : ℝ)
      - relu (-1/2 * x0 + 0 * x1 + 1/2 : ℝ)) := by intro m; ring_nf
  ring_nf at h3 ⊢
  linarith
end Lane4.Case
