namespace Lane4.Case
open Lane4

def L1 : Layer :=
  { W := [[-1/2, -1, 1/2], [-1/2, -2, 0], [1/2, 2, 0], [1, 1/2, 0], [-1, -1/2, 0],
          [0, 0, -1], [1, 0, 0], [-1, 0, 0]],
    b := [2, 3/2, -3/2, -3, 3, 2, 0, 0] }

def L2 : Layer :=
  { W := [[-1, 1, -1, -1, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0],
          [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0],
          [0, 0, 0, 0, 0, 0, 0, 1]],
    b := [0, 0, 0, 0, -7/2, 0, 0] }

def L3 : Layer :=
  { W := [[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
          [0, 0, 0, 1, -1, 1, -1], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]],
    b := [0, 0, 0, 0, 0, 0] }

def Lout : Layer := { W := [[2, 2, -2, 2, -2, 2]], b := [-6] }

def net : Net := { hidden := [L1, L2, L3], out := Lout }

theorem l1 (x0 x1 x2 : ℝ) : (L1.apply [x0, x1, x2]).map relu =
    [relu (((-1/2) * x0 + (-2) * x1 + (3/2)) - ((-1) * x1 + (-1/2) * x2 + (-1/2))),
     relu ((-1/2) * x0 + (-2) * x1 + (3/2)),
     relu (-((-1/2) * x0 + (-2) * x1 + (3/2))),
     relu (x0 + (1/2) * x1 + (-3)),
     relu (-(x0 + (1/2) * x1 + (-3))),
     relu ((-1) * x2 + (-1) - (-3)),
     relu x0,
     relu (-x0)] := by
  simp only [L1, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil,
    List.cons.injEq]
  push_cast
  repeat' apply And.intro
  all_goals first | trivial | (congr 1; ring1) | rfl

theorem l2 (p1 p2 p3 p4 p5 p6 p7 p8 : ℝ) : (L2.apply [p1, p2, p3, p4, p5, p6, p7, p8]).map relu =
    [relu (p2 - p3 - p1 - p4 + p5), relu p4, relu p5, relu p6, relu (p6 - 7/2), relu p7,
     relu p8] := by
  simp only [L2, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil,
    List.cons.injEq]
  push_cast
  repeat' apply And.intro
  all_goals first | trivial | (congr 1; ring1) | rfl

theorem l3 (v1 v2 v3 v4 v5 v6 v7 : ℝ) : (L3.apply [v1, v2, v3, v4, v5, v6, v7]).map relu =
    [relu v1, relu v2, relu v3, relu (v4 - v5 + v6 - v7), relu v6, relu v7] := by
  simp only [L3, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil,
    List.cons.injEq]
  push_cast
  repeat' apply And.intro
  all_goals first | trivial | (congr 1; ring1) | rfl

theorem core (x0 x1 x2 p1 p2 p3 p4 p5 p6 p7 p8 v1 v2 v3 v4 v5 v6 v7 w1 w2 w3 w4 w5 w6 : ℝ)
    (hp1 : p1 = relu (((-1/2) * x0 + (-2) * x1 + (3/2)) - ((-1) * x1 + (-1/2) * x2 + (-1/2))))
    (hp2 : p2 = relu ((-1/2) * x0 + (-2) * x1 + (3/2)))
    (hp3 : p3 = relu (-((-1/2) * x0 + (-2) * x1 + (3/2))))
    (hp4 : p4 = relu (x0 + (1/2) * x1 + (-3)))
    (hp5 : p5 = relu (-(x0 + (1/2) * x1 + (-3))))
    (hp6 : p6 = relu ((-1) * x2 + (-1) - (-3)))
    (hp7 : p7 = relu x0)
    (hp8 : p8 = relu (-x0))
    (hv1 : v1 = relu (p2 - p3 - p1 - p4 + p5))
    (hv2 : v2 = relu p4)
    (hv3 : v3 = relu p5)
    (hv4 : v4 = relu p6)
    (hv5 : v5 = relu (p6 - 7/2))
    (hv6 : v6 = relu p7)
    (hv7 : v7 = relu p8)
    (hw1 : w1 = relu v1)
    (hw2 : w2 = relu v2)
    (hw3 : w3 = relu v3)
    (hw4 : w4 = relu (v4 - v5 + v6 - v7))
    (hw5 : w5 = relu v6)
    (hw6 : w6 = relu v7) :
    net.out.apply [w1, w2, w3, w4, w5, w6] = [spec x0 x1 x2] := by
  have lout : net.out.apply [w1, w2, w3, w4, w5, w6] =
      [2 * w1 + 2 * w2 - 2 * w3 + 2 * w4 - 2 * w5 + 2 * w6 - 6] := by
    simp only [net, Lout, Layer.apply, dot, List.zipWith, List.sum_cons, List.sum_nil,
      List.cons.injEq, and_true]
    push_cast
    ring
  have nn : ∀ y : ℝ, 0 ≤ relu y := fun y => le_max_right _ _
  have nv : ∀ y z : ℝ, z = relu y → 0 ≤ z := by
    intro y z h
    rw [h]
    exact nn y
  have F1 := relu_sub_relu_neg ((-1/2) * x0 + (-2) * x1 + (3/2))
  have F2 := relu_sub_relu_neg (x0 + (1/2) * x1 + (-3))
  have F3 := sub_relu_sub ((-1/2) * x0 + (-2) * x1 + (3/2))
    ((-1) * x1 + (-1/2) * x2 + (-1/2))
  have F4 := add_relu_sub (x0 + (1/2) * x1 + (-3))
    (min ((-1/2) * x0 + (-2) * x1 + (3/2)) ((-1) * x1 + (-1/2) * x2 + (-1/2)))
  have F8 := relu_sub_relu_neg x0
  have hv1' : v1 = relu (min ((-1/2) * x0 + (-2) * x1 + (3/2))
      ((-1) * x1 + (-1/2) * x2 + (-1/2)) - (x0 + (1/2) * x1 + (-3))) := by
    have h : p2 - p3 - p1 - p4 + p5 = min ((-1/2) * x0 + (-2) * x1 + (3/2))
      ((-1) * x1 + (-1/2) * x2 + (-1/2)) - (x0 + (1/2) * x1 + (-3)) := by linarith
    rw [hv1, h]
  have e1 : w1 = v1 := by rw [hw1]; exact relu_of_nonneg (nv _ _ hv1)
  have e2 : w2 = v2 := by rw [hw2]; exact relu_of_nonneg (nv _ _ hv2)
  have e3 : w3 = v3 := by rw [hw3]; exact relu_of_nonneg (nv _ _ hv3)
  have e5 : w5 = v6 := by rw [hw5]; exact relu_of_nonneg (nv _ _ hv6)
  have e6 : w6 = v7 := by rw [hw6]; exact relu_of_nonneg (nv _ _ hv7)
  have g2 : v2 = p4 := by rw [hv2]; exact relu_of_nonneg (nv _ _ hp4)
  have g3 : v3 = p5 := by rw [hv3]; exact relu_of_nonneg (nv _ _ hp5)
  have g4 : v4 = p6 := by rw [hv4]; exact relu_of_nonneg (nv _ _ hp6)
  have g6 : v6 = p7 := by rw [hv6]; exact relu_of_nonneg (nv _ _ hp7)
  have g7 : v7 = p8 := by rw [hv7]; exact relu_of_nonneg (nv _ _ hp8)
  have F5 : max ((-1) * x2 + (-1)) (-3) = -3 + p6 := by
    rw [max_comm, hp6]
    exact (add_relu_sub _ _).symm
  have F6 : min (-3 + p6) (1/2) = (-3 + p6) - v5 := by
    have h := sub_relu_sub (-3 + p6) (1/2)
    have h2 : (-3 + p6) - 1/2 = p6 - 7/2 := by ring
    rw [h2, ← hv5] at h
    linarith
  have harg : v4 - v5 + v6 - v7 = min (max ((-1) * x2 + (-1)) (-3)) (1/2)
      - ((-1) * x0 + (-3)) := by
    rw [F5, F6]
    linarith
  have F7 := add_relu_sub ((-1) * x0 + (-3)) (min (max ((-1) * x2 + (-1)) (-3)) (1/2))
  have hw4' : w4 = relu (min (max ((-1) * x2 + (-1)) (-3)) (1/2) - ((-1) * x0 + (-3))) := by
    rw [hw4, harg]
  rw [lout]
  simp only [List.cons.injEq, and_true, spec]
  linarith

theorem net_correct : Statement net := by
  intro x0 x1 x2 _ _ _ _ _ _
  show net.out.apply ((L3.apply ((L2.apply ((L1.apply [x0, x1, x2]).map relu)).map relu)).map
    relu) = [spec x0 x1 x2]
  rw [l1, l2, l3]
  exact core x0 x1 x2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

end Lane4.Case
