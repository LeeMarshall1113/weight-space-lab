namespace Lane4.Case
open Lane4

def net : Net :=
  { hidden :=
      [ { W := [[3, 1], [1, 0], [0, 1]], b := [-2, 4, 2] },
        { W := [[1, -4, 0], [1, 0, 0], [0, 1, 0], [0, 0, 1]], b := [19, 0, 0, 0] },
        { W := [[-1, 2, -3, -1], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], b := [16, 0, 0, 0] },
        { W := [[-1, 1, -2, -1], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]],
          b := [23/2, 0, 0, 0, 0] },
        { W := [[-1, -1, 1, 0, -1], [1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0],
                [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
          b := [1/2, 0, 0, 0, 0, 0] } ],
    out := { W := [[1, 1, 1, -1, 2, 1]], b := [-23/2] } }

theorem chain (a c d e R S Q V W : ℝ) (hR : R = relu (a - c)) (hS : S = relu (c + R - d))
    (hQ : Q = relu ((c + R - S) - (a - R))) (hV : V = relu (-(a - R + Q)))
    (hW : W = relu (e - (a - R + Q + V))) :
    max (max (max (min a c) (min (max a c) d)) 0) e = a - R + Q + V + W := by
  have hmin : min a c = a - R := by rw [hR]; exact (sub_relu_sub a c).symm
  have hmax : max a c = c + R := by rw [hR, max_comm]; exact (add_relu_sub c a).symm
  have hmin2 : min (c + R) d = c + R - S := by rw [hS]; exact (sub_relu_sub (c + R) d).symm
  have hmed : max (a - R) (c + R - S) = a - R + Q := by
    rw [hQ]; exact (add_relu_sub (a - R) (c + R - S)).symm
  have h0 : max (a - R + Q) 0 = a - R + Q + V := by
    have := add_relu_sub (a - R + Q) 0
    rw [zero_sub] at this
    rw [hV]; exact this.symm
  have hf : max (a - R + Q + V) e = a - R + Q + V + W := by
    rw [hW]; exact (add_relu_sub (a - R + Q + V) e).symm
  rw [hmin, hmax, hmin2, hmed, h0, hf]

theorem hrr (y : ℝ) : relu (relu y) = relu y := relu_of_nonneg (le_max_right _ _)

theorem net_correct : Statement net := by
  intro x0 x1 h0 h1 h2 h3
  have ch := chain (2 * x0 + x1 + (-3/2)) ((-1) * x0 + (1/2)) (3 * x0 + (-5/2)) (2 * x0 + (-3))
    _ _ _ _ _ rfl rfl rfl rfl rfl
  have hx0 : relu (x0 + 4) = x0 + 4 := relu_of_nonneg (by linarith)
  have hx1 : relu (x1 + 2) = x1 + 2 := relu_of_nonneg (by linarith)
  simp only [net, Net.eval, Layer.apply, dot, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true]
  unfold spec
  rw [ch]
  push_cast
  try ring_nf
  ring_nf at hx0 hx1 ch
  try simp only [hrr, hx0, hx1]
  try ring_nf
  try simp only [hrr, hx0, hx1]
  try ring_nf
  try simp only [hrr, hx0, hx1]
  try ring_nf
  try simp only [hrr, hx0, hx1]
  try ring_nf
  try simp only [hrr, hx0, hx1]
  try ring_nf
  try linarith

end Lane4.Case
