namespace Lane4.Case
open Lane4
def net : Net :=
  { hidden := [{ W := [[-3], [1], [-1]], b := [-5/2, 1, -1] }],
    out := { W := [[1, 1, -1]], b := [0] } }

theorem spec_eq (x : ℝ) :
    spec x = relu (-3 * x - 5/2) + relu (x + 1) - relu (-x - 1) := by
  have hs : spec x = max (-2 * x - 3/2) (x + 1) := by
    unfold spec
    simp only [max_def, min_def, abs_eq_max_neg]
    split_ifs <;> linarith
  rw [hs]
  unfold relu
  rcases le_total x (-1) with h | h
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ -3 * x - 5/2), max_eq_right (by linarith : x + 1 ≤ 0),
      max_eq_left (by linarith : (0:ℝ) ≤ -x - 1), max_eq_left (by linarith : x + 1 ≤ -2 * x - 3/2)]
    ring
  rcases le_total x (-5/6) with h' | h'
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ -3 * x - 5/2), max_eq_left (by linarith : (0:ℝ) ≤ x + 1),
      max_eq_right (by linarith : -x - 1 ≤ 0), max_eq_left (by linarith : x + 1 ≤ -2 * x - 3/2)]
    ring
  · rw [max_eq_right (by linarith : -3 * x - 5/2 ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ x + 1),
      max_eq_right (by linarith : -x - 1 ≤ 0), max_eq_right (by linarith : -2 * x - 3/2 ≤ x + 1)]
    ring

theorem key {a0 c0 a1 c1 a2 c2 o0 o1 o2 oc x : ℝ}
    (h0 : |a0| ≤ 1/1000) (hc0 : |c0| ≤ 1/1000)
    (h1 : |a1| ≤ 1/1000) (hc1 : |c1| ≤ 1/1000)
    (h2 : |a2| ≤ 1/1000) (hc2 : |c2| ≤ 1/1000)
    (ho0 : |o0| ≤ 1/1000) (ho1 : |o1| ≤ 1/1000) (ho2 : |o2| ≤ 1/1000) (hoc : |oc| ≤ 1/1000)
    (l : -8 ≤ x) (u : x ≤ 2) :
    |(1 + o0) * relu ((-3 + a0) * x + (-5/2 + c0))
      + (1 + o1) * relu ((1 + a1) * x + (1 + c1))
      + (-1 + o2) * relu ((-1 + a2) * x + (-1 + c2)) + oc - spec x| ≤ 18/25 := by
  have bx : |x| ≤ 8 := abs_le.mpr ⟨l, by linarith⟩
  have e0 : |((-3 + a0) * x + (-5/2 + c0)) - (-3 * x - 5/2)| ≤ 9/1000 := by
    have h : ((-3 + a0) * x + (-5/2 + c0)) - (-3 * x - 5/2) = a0 * x + c0 := by ring
    rw [h]
    have := pert_abs_mul h0 bx
    exact le_trans (abs_add_le _ _) (by linarith)
  have e1 : |((1 + a1) * x + (1 + c1)) - (x + 1)| ≤ 9/1000 := by
    have h : ((1 + a1) * x + (1 + c1)) - (x + 1) = a1 * x + c1 := by ring
    rw [h]
    have := pert_abs_mul h1 bx
    exact le_trans (abs_add_le _ _) (by linarith)
  have e2 : |((-1 + a2) * x + (-1 + c2)) - (-x - 1)| ≤ 9/1000 := by
    have h : ((-1 + a2) * x + (-1 + c2)) - (-x - 1) = a2 * x + c2 := by ring
    rw [h]
    have := pert_abs_mul h2 bx
    exact le_trans (abs_add_le _ _) (by linarith)
  have r0 := abs_le.mp (relu_pert e0)
  have r1 := abs_le.mp (relu_pert e1)
  have r2 := abs_le.mp (relu_pert e2)
  have id := spec_eq x
  have s0 : relu (-3 * x - 5/2) ≤ 22 := relu_le_of_le (by linarith) (by norm_num)
  have s1 : relu (x + 1) ≤ 3 := relu_le_of_le (by linarith) (by norm_num)
  have s2 : relu (-x - 1) ≤ 7 := relu_le_of_le (by linarith) (by norm_num)
  have n0 := relu_nonneg' ((-3 + a0) * x + (-5/2 + c0))
  have n1 := relu_nonneg' ((1 + a1) * x + (1 + c1))
  have n2 := relu_nonneg' ((-1 + a2) * x + (-1 + c2))
  have m0 := relu_nonneg' (-3 * x - 5/2)
  have m1 := relu_nonneg' (x + 1)
  have m2 := relu_nonneg' (-x - 1)
  generalize relu ((-3 + a0) * x + (-5/2 + c0)) = R0 at *
  generalize relu ((1 + a1) * x + (1 + c1)) = R1 at *
  generalize relu ((-1 + a2) * x + (-1 + c2)) = R2 at *
  generalize relu (-3 * x - 5/2) = S0 at *
  generalize relu (x + 1) = S1 at *
  generalize relu (-x - 1) = S2 at *
  have q0 := abs_le.mp (pert_abs_mul ho0 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R0| ≤ 23))
  have q1 := abs_le.mp (pert_abs_mul ho1 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R1| ≤ 4))
  have q2 := abs_le.mp (pert_abs_mul ho2 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R2| ≤ 8))
  have qc := abs_le.mp hoc
  have h : (1 + o0) * R0 + (1 + o1) * R1 + (-1 + o2) * R2 + oc - spec x
      = (R0 - S0) + (R1 - S1) - (R2 - S2) + o0 * R0 + o1 * R1 + o2 * R2 + oc := by
    rw [id]; ring
  rw [h, abs_le]
  constructor <;> linarith [r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, q0.1, q0.2, q1.1, q1.2, q2.1, q2.2, qc.1, qc.2]

theorem net_robust : StatementRobust net := by
  intro dW db hW x l u
  obtain ⟨hw, hb⟩ := hW
  refine ⟨(1 + dW 1 0 0) * relu ((-3 + dW 0 0 0) * x + (-5/2 + db 0 0))
        + (1 + dW 1 0 1) * relu ((1 + dW 0 1 0) * x + (1 + db 0 1))
        + (-1 + dW 1 0 2) * relu ((-1 + dW 0 2 0) * x + (-1 + db 0 2)) + db 1 0, ?_, ?_⟩
  · simp [net, Net.evalP, hiddenP, rowsP, dotP]
    try ring_nf
  · exact key (hw 0 0 0) (hb 0 0) (hw 0 1 0) (hb 0 1) (hw 0 2 0) (hb 0 2)
      (hw 1 0 0) (hw 1 0 1) (hw 1 0 2) (hb 1 0) l u
end Lane4.Case
