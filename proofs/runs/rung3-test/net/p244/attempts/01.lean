namespace Lane4.Case
open Lane4

def net : Net :=
  { hidden := [{ W := [[1], [1], [1], [1], [1]], b := [1, 4/5, 1/3, -5/4, -9/4] }],
    out := { W := [[-2, 5/2, -3/2, 2, -2]], b := [1/2] } }

theorem exact_eq (x : ℝ) (l : -1 ≤ x) (u : x ≤ 4) :
    spec x = 1/2 - 2 * relu (x + 1) + 5/2 * relu (x + 4/5) - 3/2 * relu (x + 1/3)
      + 2 * relu (x + (-5/4)) - 2 * relu (x + (-9/4)) := by
  rcases le_total x (-4/5) with h1 | h1 <;> rcases le_total x (-1/3) with h2 | h2 <;>
  rcases le_total x (5/4) with h3 | h3 <;> rcases le_total x (9/4) with h4 | h4 <;>
  (simp (disch := linarith) only [spec, relu_of_nonneg, relu_of_nonpos, max_eq_left,
      max_eq_right, min_eq_left, min_eq_right] <;> linarith)

theorem pre {a c x b : ℝ} (ha : |a| ≤ 1/1000) (hc : |c| ≤ 1/1000) (hx : |x| ≤ 4) :
    |((1 + a) * x + (b + c)) - (x + b)| ≤ 1/200 := by
  have h : ((1 + a) * x + (b + c)) - (x + b) = a * x + c := by ring
  rw [h]
  have := pert_abs_mul ha hx
  exact le_trans (abs_add_le _ _) (by linarith)

theorem key {R0 R1 R2 R3 R4 o0 o1 o2 o3 o4 oc x : ℝ}
    (r0 : |R0 - relu (x + 1)| ≤ 1/200) (r1 : |R1 - relu (x + 4/5)| ≤ 1/200)
    (r2 : |R2 - relu (x + 1/3)| ≤ 1/200) (r3 : |R3 - relu (x + (-5/4))| ≤ 1/200)
    (r4 : |R4 - relu (x + (-9/4))| ≤ 1/200)
    (h0 : |o0| ≤ 1/1000) (h1 : |o1| ≤ 1/1000) (h2 : |o2| ≤ 1/1000)
    (h3 : |o3| ≤ 1/1000) (h4 : |o4| ≤ 1/1000) (hc : |oc| ≤ 1/1000)
    (l : -1 ≤ x) (u : x ≤ 4) :
    |(-2 + o0) * R0 + (5/2 + o1) * R1 + (-3/2 + o2) * R2 + (2 + o3) * R3
      + (-2 + o4) * R4 + (1/2 + oc) - spec x| ≤ 1/5 := by
  have E := exact_eq x l u
  have s0 : relu (x + 1) ≤ 5 := relu_le_of_le (by linarith) (by norm_num)
  have s1 : relu (x + 4/5) ≤ 5 := relu_le_of_le (by linarith) (by norm_num)
  have s2 : relu (x + 1/3) ≤ 5 := relu_le_of_le (by linarith) (by norm_num)
  have s3 : relu (x + (-5/4)) ≤ 5 := relu_le_of_le (by linarith) (by norm_num)
  have s4 : relu (x + (-9/4)) ≤ 5 := relu_le_of_le (by linarith) (by norm_num)
  have n0 := relu_nonneg' (x + 1)
  have n1 := relu_nonneg' (x + 4/5)
  have n2 := relu_nonneg' (x + 1/3)
  have n3 := relu_nonneg' (x + (-5/4))
  have n4 := relu_nonneg' (x + (-9/4))
  have a0 := abs_le.mp r0
  have a1 := abs_le.mp r1
  have a2 := abs_le.mp r2
  have a3 := abs_le.mp r3
  have a4 := abs_le.mp r4
  have q0 := abs_le.mp (pert_abs_mul h0 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R0| ≤ 6))
  have q1 := abs_le.mp (pert_abs_mul h1 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R1| ≤ 6))
  have q2 := abs_le.mp (pert_abs_mul h2 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R2| ≤ 6))
  have q3 := abs_le.mp (pert_abs_mul h3 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R3| ≤ 6))
  have q4 := abs_le.mp (pert_abs_mul h4 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R4| ≤ 6))
  have qc := abs_le.mp hc
  have h : (-2 + o0) * R0 + (5/2 + o1) * R1 + (-3/2 + o2) * R2 + (2 + o3) * R3
      + (-2 + o4) * R4 + (1/2 + oc) - spec x
      = -2 * (R0 - relu (x + 1)) + 5/2 * (R1 - relu (x + 4/5))
        - 3/2 * (R2 - relu (x + 1/3)) + 2 * (R3 - relu (x + (-5/4)))
        - 2 * (R4 - relu (x + (-9/4)))
        + o0 * R0 + o1 * R1 + o2 * R2 + o3 * R3 + o4 * R4 + oc := by
    rw [E]; ring
  rw [h, abs_le]
  constructor <;> linarith [a0.1, a0.2, a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2,
    q0.1, q0.2, q1.1, q1.2, q2.1, q2.2, q3.1, q3.2, q4.1, q4.2, qc.1, qc.2]

theorem net_robust : StatementRobust net := by
  intro dW db hW x0 l u
  obtain ⟨hw, hb⟩ := hW
  have bx : |x0| ≤ 4 := abs_le.mpr ⟨by linarith, u⟩
  refine ⟨(-2 + dW 1 0 0) * relu ((1 + dW 0 0 0) * x0 + (1 + db 0 0))
      + (5/2 + dW 1 0 1) * relu ((1 + dW 0 1 0) * x0 + (4/5 + db 0 1))
      + (-3/2 + dW 1 0 2) * relu ((1 + dW 0 2 0) * x0 + (1/3 + db 0 2))
      + (2 + dW 1 0 3) * relu ((1 + dW 0 3 0) * x0 + (-5/4 + db 0 3))
      + (-2 + dW 1 0 4) * relu ((1 + dW 0 4 0) * x0 + (-9/4 + db 0 4))
      + (1/2 + db 1 0), ?_, ?_⟩
  · simp [net, Net.evalP, hiddenP, rowsP, dotP]
    try ring_nf
  · exact key (relu_pert (pre (hw 0 0 0) (hb 0 0) bx)) (relu_pert (pre (hw 0 1 0) (hb 0 1) bx))
      (relu_pert (pre (hw 0 2 0) (hb 0 2) bx)) (relu_pert (pre (hw 0 3 0) (hb 0 3) bx))
      (relu_pert (pre (hw 0 4 0) (hb 0 4) bx))
      (hw 1 0 0) (hw 1 0 1) (hw 1 0 2) (hw 1 0 3) (hw 1 0 4) (hb 1 0) l u
end Lane4.Case
