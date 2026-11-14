namespace Lane4.Case
open Lane4

theorem P_aux (a a' : ℝ) (h : a' = -a) : relu a - relu a' = a := by
  subst h; exact relu_sub_relu_neg a

theorem R_aux (a a' : ℝ) (h : a' = -a) : relu a + relu a' = |a| := by
  subst h; exact relu_add_relu_neg a

theorem Q_aux (a b c : ℝ) (h : c = a - b) : a - relu c = min a b := by
  subst h; exact sub_relu_sub a b

theorem Q'_aux (a b c : ℝ) (h : c = b - a) : a + relu c = max a b := by
  subst h; exact add_relu_sub a b

def L1 : Layer :=
  { W := [[-1, 1], [0, -1], [0, 1], [0, -2], [0, 2], [-2, 1], [2, -1]],
    b := [-1/2, -3, 3, 1/2, -1/2, 1/2, -1/2] }
def L2 : Layer :=
  { W := [[-1, 1, -1, -1, 1, 0, 0], [1, -1, 1, 1, -1, 0, 0], [-1, 1, -1, 0, 0, 0, 0],
          [1, -1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, -1], [0, 0, 0, 0, 0, -1, 1]],
    b := [0, 0, 0, 0, 0, 0] }
def L3 : Layer :=
  { W := [[0, 1, 1, -1, -1, 1], [-1, 0, 1, -1, 0, 0], [1, 0, -1, 1, 0, 0],
          [0, 1, 1, -1, 0, 0], [0, -1, -1, 1, 0, 0]],
    b := [0, 0, 0, 0, 0] }
def L4 : Layer :=
  { W := [[-1, -1, 1, 1, -1], [0, 1, -1, 0, 0], [0, -1, 1, 0, 0]],
    b := [0, 0, 0] }
def L5 : Layer :=
  { W := [[1, 1, -1], [-1, -1, 1]], b := [0, 0] }

def net : Net :=
  { hidden := [L1, L2, L3, L4, L5], out := { W := [[1, 1]], b := [0] } }

theorem e1 (x0 x1 : ℝ) : ∃ u1 u2 u3 u4 u5 u6 u7 : ℝ,
    (L1.apply [x0, x1]).map relu = [u1, u2, u3, u4, u5, u6, u7] ∧
    u2 - u3 - u1 = min ((-1) * x1 + (-3)) (x0 + (-2) * x1 + (-5/2)) ∧
    u4 - u5 = (-2) * x1 + (1/2) ∧
    u6 - u7 = (-2) * x0 + x1 + (1/2) := by
  have E : (L1.apply [x0, x1]).map relu =
      [relu (-x0 + x1 + (-1/2)), relu ((-1) * x1 + (-3)), relu (x1 + 3),
       relu ((-2) * x1 + (1/2)), relu (2 * x1 + (-1/2)),
       relu ((-2) * x0 + x1 + (1/2)), relu (2 * x0 - x1 + (-1/2))] := by
    simp only [L1, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil]
    push_cast
    ring_nf
  refine ⟨_, _, _, _, _, _, _, E, ?_, ?_, ?_⟩
  · have h1 := P_aux ((-1) * x1 + (-3)) (x1 + 3) (by ring)
    have h2 := Q_aux ((-1) * x1 + (-3)) (x0 + (-2) * x1 + (-5/2)) (-x0 + x1 + (-1/2)) (by ring)
    linarith
  · exact P_aux _ _ (by ring)
  · exact P_aux _ _ (by ring)

theorem e2 (u1 u2 u3 u4 u5 u6 u7 m1 C D : ℝ) (hm : m1 = u2 - u3 - u1) (hC : C = u4 - u5)
    (hD : D = u6 - u7) : ∃ v1 v2 v3 v4 v5 v6 : ℝ,
    (L2.apply [u1, u2, u3, u4, u5, u6, u7]).map relu = [v1, v2, v3, v4, v5, v6] ∧
    v3 - v4 - v1 = min m1 C ∧ v3 - v4 + v2 = max m1 C ∧ v5 - v6 = D := by
  have E : (L2.apply [u1, u2, u3, u4, u5, u6, u7]).map relu =
      [relu (-u1 + u2 - u3 - u4 + u5), relu (u1 - u2 + u3 + u4 - u5),
       relu (-u1 + u2 - u3), relu (u1 - u2 + u3), relu (u6 - u7), relu (-u6 + u7)] := by
    simp only [L2, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil]
    push_cast
    ring_nf
  refine ⟨_, _, _, _, _, _, E, ?_, ?_, ?_⟩
  · have h1 := P_aux (-u1 + u2 - u3) (u1 - u2 + u3) (by ring)
    have h2 := Q_aux m1 C (-u1 + u2 - u3 - u4 + u5) (by rw [hm, hC]; ring)
    have h3 : -u1 + u2 - u3 = m1 := by rw [hm]; ring
    linarith
  · have h1 := P_aux (-u1 + u2 - u3) (u1 - u2 + u3) (by ring)
    have h2 := Q'_aux m1 C (u1 - u2 + u3 + u4 - u5) (by rw [hm, hC]; ring)
    have h3 : -u1 + u2 - u3 = m1 := by rw [hm]; ring
    linarith
  · have h1 := P_aux (u6 - u7) (-u6 + u7) (by ring)
    rw [hD]; exact h1

theorem e3 (v1 v2 v3 v4 v5 v6 m2 M D : ℝ) (hm : m2 = v3 - v4 - v1) (hM : M = v3 - v4 + v2)
    (hD : D = v5 - v6) : ∃ w1 w2 w3 w4 w5 : ℝ,
    (L3.apply [v1, v2, v3, v4, v5, v6]).map relu = [w1, w2, w3, w4, w5] ∧
    w2 - w3 = m2 ∧ w4 - w5 - w1 = min M D := by
  have E : (L3.apply [v1, v2, v3, v4, v5, v6]).map relu =
      [relu (v2 + v3 - v4 - v5 + v6), relu (-v1 + v3 - v4), relu (v1 - v3 + v4),
       relu (v2 + v3 - v4), relu (-v2 - v3 + v4)] := by
    simp only [L3, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil]
    push_cast
    ring_nf
  refine ⟨_, _, _, _, _, E, ?_, ?_⟩
  · have h1 := P_aux (-v1 + v3 - v4) (v1 - v3 + v4) (by ring)
    rw [hm]
    linarith
  · have h1 := P_aux (v2 + v3 - v4) (-v2 - v3 + v4) (by ring)
    have h2 := Q_aux M D (v2 + v3 - v4 - v5 + v6) (by rw [hM, hD]; ring)
    have h3 : v2 + v3 - v4 = M := by rw [hM]; ring
    linarith

theorem e4 (w1 w2 w3 w4 w5 m2 m3 : ℝ) (hm : m2 = w2 - w3) (hM : m3 = w4 - w5 - w1) :
    ∃ z1 y1 y2 : ℝ,
    (L4.apply [w1, w2, w3, w4, w5]).map relu = [z1, y1, y2] ∧
    y1 - y2 + z1 = max m2 m3 := by
  have E : (L4.apply [w1, w2, w3, w4, w5]).map relu =
      [relu (-w1 - w2 + w3 + w4 - w5), relu (w2 - w3), relu (-w2 + w3)] := by
    simp only [L4, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil]
    push_cast
    ring_nf
  refine ⟨_, _, _, E, ?_⟩
  have h1 := P_aux (w2 - w3) (-w2 + w3) (by ring)
  have h2 := Q'_aux m2 m3 (-w1 - w2 + w3 + w4 - w5) (by rw [hm, hM]; ring)
  linarith

theorem e5 (z1 y1 y2 r : ℝ) (hr : r = y1 - y2 + z1) : ∃ t1 t2 : ℝ,
    (L5.apply [z1, y1, y2]).map relu = [t1, t2] ∧ t1 + t2 = |r| := by
  have E : (L5.apply [z1, y1, y2]).map relu =
      [relu (z1 + y1 - y2), relu (-z1 - y1 + y2)] := by
    simp only [L5, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil]
    push_cast
    ring_nf
  refine ⟨_, _, E, ?_⟩
  exact R_aux _ _ (by ring) |>.trans (by rw [hr]; congr 1; ring)

theorem net_correct : Statement net := by
  intro x0 x1 _ _ _ _
  obtain ⟨u1, u2, u3, u4, u5, u6, u7, E1, g1, g2, g3⟩ := e1 x0 x1
  obtain ⟨v1, v2, v3, v4, v5, v6, E2, f1, f2, f3⟩ :=
    e2 u1 u2 u3 u4 u5 u6 u7 _ _ _ g1.symm g2.symm g3.symm
  obtain ⟨w1, w2, w3, w4, w5, E3, k1, k2⟩ := e3 v1 v2 v3 v4 v5 v6 _ _ _ f1.symm f2.symm f3.symm
  obtain ⟨z1, y1, y2, E4, j1⟩ := e4 w1 w2 w3 w4 w5 _ _ k1.symm k2.symm
  obtain ⟨t1, t2, E5, i1⟩ := e5 z1 y1 y2 _ j1.symm
  simp only [net, Net.eval, List.foldl, E1, E2, E3, E4, E5]
  simp only [Layer.apply, dot, spec, List.zipWith, List.map, List.sum_cons, List.sum_nil,
    List.cons.injEq, and_true]
  push_cast
  rw [← i1]
  ring
end Lane4.Case
