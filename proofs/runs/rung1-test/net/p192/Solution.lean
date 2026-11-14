namespace Lane4.Case
open Lane4

def L1 : Layer := { W := [[-1, 0], [1, 0], [4, 2], [-4, -2], [-2, 0]], b := [0, 0, 1/2, -1/2, -3] }
def L2 : Layer := { W := [[1, -1, 1, 0, -1], [1, -1, 0, -1, 0], [-1, 1, 0, 1, 0], [1, -1, 1, 0, 0], [-1, 1, -1, 0, 0]], b := [0, 0, 0, 0, 0] }
def L3 : Layer := { W := [[-1, -1, 1, 1, -1], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0]], b := [0, 0, 0] }
def L4 : Layer := { W := [[1, 1, -1]], b := [5/2] }
def L5 : Layer := { W := [[1], [1]], b := [0, -1/2] }
def Lout : Layer := { W := [[1, -1]], b := [-5/2] }

def net : Net := { hidden := [L1, L2, L3, L4, L5], out := Lout }

theorem l4s1 (x0 x1 : ℝ) : (L1.apply [x0, x1]).map relu =
    [relu (-x0), relu x0, relu (4*x0+2*x1+1/2), relu (-(4*x0+2*x1+1/2)), relu (-2*x0-3)] := by
  simp only [L1, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil]
  push_cast
  ring_nf

theorem l4s2 (y1 y2 y3 y4 y5 : ℝ) : (L2.apply [y1, y2, y3, y4, y5]).map relu =
    [relu (y1 - y2 + y3 - y5), relu (y1 - y2 - y4), relu (-(y1 - y2 - y4)),
     relu (y1 - y2 + y3), relu (-(y1 - y2 + y3))] := by
  simp only [L2, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil]
  push_cast
  ring_nf

theorem l4s3 (z1 z2 z3 z4 z5 : ℝ) : (L3.apply [z1, z2, z3, z4, z5]).map relu =
    [relu (z4 - z5 - z1 - z2 + z3), relu z2, relu z3] := by
  simp only [L3, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil]
  push_cast
  ring_nf

theorem l4s4 (w1 w2 w3 : ℝ) : (L4.apply [w1, w2, w3]).map relu =
    [relu (w1 + w2 - w3 + 5/2)] := by
  simp only [L4, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil]
  push_cast
  ring_nf

theorem l4s5 (u : ℝ) : (L5.apply [u]).map relu = [relu u, relu (u - 1/2)] := by
  simp only [L5, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil]
  push_cast
  ring_nf

theorem net_correct : Statement net := by
  intro x0 x1 _ _ _ _
  simp only [net, Net.eval, List.foldl]
  rw [l4s1]
  generalize hy1 : relu (-x0) = y1
  generalize hy2 : relu x0 = y2
  generalize hy3 : relu (4*x0+2*x1+1/2) = y3
  generalize hy4 : relu (-(4*x0+2*x1+1/2)) = y4
  generalize hy5 : relu (-2*x0-3) = y5
  have F1 : y1 - y2 + y3 = max ((-1) * x0) (3 * x0 + 2 * x1 + (1/2)) := by
    rw [← hy1, ← hy2, ← hy3]; simp only [relu, max_def]; split_ifs <;> linarith
  have F2 : y1 - y2 - y4 = min ((-1) * x0) (3 * x0 + 2 * x1 + (1/2)) := by
    rw [← hy1, ← hy2, ← hy4]; simp only [relu, max_def, min_def]; split_ifs <;> linarith
  have F3 : y5 = max ((-2) * x0 + (-3)) 0 := by
    rw [← hy5]; simp only [relu, max_def]; split_ifs <;> linarith
  rw [l4s2]
  generalize hz1 : relu (y1 - y2 + y3 - y5) = z1
  generalize hz2 : relu (y1 - y2 - y4) = z2
  generalize hz3 : relu (-(y1 - y2 - y4)) = z3
  generalize hz4 : relu (y1 - y2 + y3) = z4
  generalize hz5 : relu (-(y1 - y2 + y3)) = z5
  have G1 : z4 - z5 - z1 = min (max ((-1) * x0) (3 * x0 + 2 * x1 + (1/2))) (max ((-2) * x0 + (-3)) 0) := by
    rw [← F1, ← F3, ← hz1, ← hz4, ← hz5]
    simp only [relu, max_def, min_def]; split_ifs <;> linarith
  have G2 : z2 - z3 = min ((-1) * x0) (3 * x0 + 2 * x1 + (1/2)) := by
    rw [← F2, ← hz2, ← hz3]; simp only [relu, max_def]; split_ifs <;> linarith
  have N2 : 0 ≤ z2 := by rw [← hz2]; unfold relu; exact le_max_right _ _
  have N3 : 0 ≤ z3 := by rw [← hz3]; unfold relu; exact le_max_right _ _
  rw [l4s3]
  generalize hw1 : relu (z4 - z5 - z1 - z2 + z3) = w1
  generalize hw2 : relu z2 = w2
  generalize hw3 : relu z3 = w3
  have e2 : w2 = z2 := by rw [← hw2]; exact relu_of_nonneg N2
  have e3 : w3 = z3 := by rw [← hw3]; exact relu_of_nonneg N3
  have H1 : w2 - w3 + w1 = max (min ((-1) * x0) (3 * x0 + 2 * x1 + (1/2))) (min (max ((-1) * x0) (3 * x0 + 2 * x1 + (1/2))) (max ((-2) * x0 + (-3)) 0)) := by
    have h := add_relu_sub (min ((-1) * x0) (3 * x0 + 2 * x1 + (1/2))) (min (max ((-1) * x0) (3 * x0 + 2 * x1 + (1/2))) (max ((-2) * x0 + (-3)) 0))
    have h2 : z4 - z5 - z1 - z2 + z3 = min (max ((-1) * x0) (3 * x0 + 2 * x1 + (1/2))) (max ((-2) * x0 + (-3)) 0) - min ((-1) * x0) (3 * x0 + 2 * x1 + (1/2)) := by
      linarith [G1, G2]
    rw [e2, e3, ← hw1, h2]
    linarith
  rw [l4s4]
  generalize hu : relu (w1 + w2 - w3 + 5/2) = u
  rw [l4s5]
  generalize hv1 : relu u = v1
  generalize hv2 : relu (u - 1/2) = v2
  have FIN' : v1 - v2 - 5/2 = min (max (w2 - w3 + w1) (-5/2)) (-2) := by
    rw [← hv1, ← hv2, ← hu]; simp only [relu, max_def, min_def]; split_ifs <;> linarith
  have FIN2 : v1 - v2 - 5/2 = spec x0 x1 := by
    unfold spec
    rw [H1] at FIN'
    first | exact FIN' | linarith
  simp only [Lout, Layer.apply, dot, List.zipWith, List.sum_cons, List.sum_nil,
    List.cons.injEq, and_true]
  push_cast
  linarith [FIN2]

end Lane4.Case
