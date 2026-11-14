namespace Lane4.Case
open Lane4
def l1 : Layer := { W := [[0, 3, 0], [0, -3, 0], [1, 0, 1/2], [0, 3, 0]], b := [1, -1, 5, 13/2] }
def l2 : Layer := { W := [[1, 1, 0, 0], [1, 1, -1, 0], [-1, -1, 1, 0], [0, 0, 0, 1]], b := [0, 3, -3, 0] }
def l3 : Layer := { W := [[1, 0, 1, -1], [1, -1, 0, 0], [1, 0, 1, 0]], b := [6, 3, 0] }
def l4 : Layer := { W := [[-1, -1, 1], [0, 1, 0]], b := [3, 0] }
def lo : Layer := { W := [[1, 1]], b := [-3] }
def net : Net := { hidden := [l1, l2, l3, l4], out := lo }
theorem net_correct : Statement net := by
  intro x0 x1 x2 h0 h1 h2 h3 h4 h5
  obtain ⟨P, hP⟩ : ∃ P, P = relu (3 * x1 + 1) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = relu (-(3 * x1 + 1)) := ⟨_, rfl⟩
  have e1 := relu_sub_relu_neg (3 * x1 + 1)
  have e2 := relu_add_relu_neg (3 * x1 + 1)
  rw [← hP, ← hQ] at e1 e2
  have n1 : 0 ≤ P := by rw [hP]; exact le_max_right _ _
  have n2 : 0 ≤ Q := by rw [hQ]; exact le_max_right _ _
  have L1 : (l1.apply [x0, x1, x2]).map relu
      = [P, Q, x0 + 1/2 * x2 + 5, 3 * x1 + 13/2] := by
    simp only [l1, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil,
      List.cons.injEq, and_true]
    push_cast
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hP]; congr 1; ring
    · rw [hQ]; congr 1; ring
    · refine (relu_of_nonneg ?_).trans ?_
      · linarith
      · ring
    · refine (relu_of_nonneg ?_).trans ?_
      · linarith
      · ring
  obtain ⟨R1, hR1⟩ : ∃ R, R = relu (P + Q - (x0 + 1/2 * x2 + 2)) := ⟨_, rfl⟩
  obtain ⟨R2, hR2⟩ : ∃ R, R = relu ((x0 + 1/2 * x2 + 2) - (P + Q)) := ⟨_, rfl⟩
  have m1 := sub_relu_sub (P + Q) (x0 + 1/2 * x2 + 2)
  have m2 := add_relu_sub (P + Q) (x0 + 1/2 * x2 + 2)
  rw [← hR1] at m1
  rw [← hR2] at m2
  have r1n : 0 ≤ R1 := by rw [hR1]; exact le_max_right _ _
  have r2n : 0 ≤ R2 := by rw [hR2]; exact le_max_right _ _
  have L2 : (l2.apply [P, Q, x0 + 1/2 * x2 + 5, 3 * x1 + 13/2]).map relu
      = [P + Q, R1, R2, 3 * x1 + 13/2] := by
    simp only [l2, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil,
      List.cons.injEq, and_true]
    push_cast
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine (relu_of_nonneg ?_).trans ?_
      · linarith
      · ring
    · rw [hR1]; congr 1; ring
    · rw [hR2]; congr 1; ring
    · refine (relu_of_nonneg ?_).trans ?_
      · linarith
      · ring
  obtain ⟨S, hS⟩ : ∃ S, S = relu ((P + Q + R2) - (3 * x1 + 1/2)) := ⟨_, rfl⟩
  have m3 := sub_relu_sub (P + Q + R2) (3 * x1 + 1/2)
  rw [← hS] at m3
  have mmin : -3 ≤ min (P + Q) (x0 + 1/2 * x2 + 2) :=
    le_min (by linarith) (by linarith)
  have L3 : (l3.apply [P + Q, R1, R2, 3 * x1 + 13/2]).map relu
      = [S, P + Q - R1 + 3, P + Q + R2] := by
    simp only [l3, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil,
      List.cons.injEq, and_true]
    push_cast
    refine ⟨?_, ?_, ?_⟩
    · rw [hS]; congr 1; ring
    · refine (relu_of_nonneg ?_).trans ?_
      · linarith
      · ring
    · refine (relu_of_nonneg ?_).trans ?_
      · linarith
      · ring
  obtain ⟨D, hD⟩ : ∃ D, D = relu ((P + Q + R2 - S) - (P + Q - R1)) := ⟨_, rfl⟩
  have L4 : (l4.apply [S, P + Q - R1 + 3, P + Q + R2]).map relu
      = [D, P + Q - R1 + 3] := by
    simp only [l4, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil,
      List.cons.injEq, and_true]
    push_cast
    refine ⟨?_, ?_⟩
    · rw [hD]; congr 1; ring
    · refine (relu_of_nonneg ?_).trans ?_
      · linarith
      · ring
  have key := add_relu_sub (P + Q - R1) (P + Q + R2 - S)
  rw [← hD] at key
  have hX : P + Q - R1 = min (P + Q) (x0 + 1/2 * x2 + 2) := m1
  have hM : P + Q + R2 = max (P + Q) (x0 + 1/2 * x2 + 2) := m2
  have hY : P + Q + R2 - S = min (max (P + Q) (x0 + 1/2 * x2 + 2)) (3 * x1 + 1/2) := by
    rw [← hM]; exact m3
  have hmax : max (P + Q - R1) (P + Q + R2 - S)
      = max (min (P + Q) (x0 + 1/2 * x2 + 2))
          (min (max (P + Q) (x0 + 1/2 * x2 + 2)) (3 * x1 + 1/2)) := by
    rw [← hX, ← hY]
  simp only [net, Net.eval, List.foldl, L1, L2, L3, L4]
  simp only [lo, Layer.apply, dot, spec, List.zipWith, List.sum_cons, List.sum_nil,
    List.cons.injEq, and_true]
  push_cast
  rw [← e2]
  linarith
end Lane4.Case
