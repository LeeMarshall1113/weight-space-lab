namespace Lane4.Case
open Lane4
def net : Net :=
  { hidden := [{ W := [[5/2], [1], [-1]], b := [1/2, 0, 0] },
               { W := [[1, -7/2, 7/2], [1, -1/2, 1/2], [-1, 1/2, -1/2]], b := [3/2, 2, -2] }],
    out := { W := [[-1, 1, -1]], b := [0] } }
theorem net_correct : Statement net := by
  intro x _ _
  have hx := relu_sub_relu_neg x
  have h1 := add_relu_sub ((-1/2 : ℝ) * x + 2) (2 * x + 5/2)
  have h2 := sub_relu_sub (max ((-1/2 : ℝ) * x + 2) (2 * x + 5/2)) (3 * x + 1/2)
  simp only [net, Net.eval, Layer.apply, dot, spec, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true]
  push_cast
  simp only [one_mul, add_zero, neg_one_mul, mul_zero]
  have eu : (2 * x + 5/2) - ((-1/2 : ℝ) * x + 2) = 5/2 * x + 1/2 := by ring
  rw [eu] at h1
  generalize hu : relu (5/2 * x + 1/2) = u at *
  generalize hp : relu x = p at *
  generalize hn : relu (-x) = n at *
  have hxx : p - n = x := hx
  have hm := relu_sub_relu_neg ((-1/2 : ℝ) * x + 2 + u)
  have eA : u + -(7/2) * p + 7/2 * n + 3/2
      = max ((-1/2 : ℝ) * x + 2) (2 * x + 5/2) - (3 * x + 1/2) := by
    rw [← h1, ← hxx]; ring
  have eB : u + -(1/2) * p + 1/2 * n + 2 = (-1/2 : ℝ) * x + 2 + u := by
    rw [← hxx]; ring
  have eC : -u + 1/2 * p + -(1/2) * n + -2 = -((-1/2 : ℝ) * x + 2 + u) := by
    rw [← hxx]; ring
  rw [eA, eB, eC]
  rw [← h1] at h2
  rw [← h1] at hm
  linarith
end Lane4.Case
