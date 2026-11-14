namespace Lane4.Case
open Lane4
def net : Net :=
  { hidden := [{ W := [[0, 1, 1], [0, -1, -1], [1/2, -1, -1], [-2, 0, -1/2]], b := [3, -3, -2, 1] }],
    out := { W := [[-1, 1, -1, 1/2]], b := [0] } }

theorem key {a00 a01 a02 c0 a10 a11 a12 c1 a20 a21 a22 c2 a30 a31 a32 c3 o0 o1 o2 o3 oc x0 x1 x2 : ℝ}
    (h00 : |a00| ≤ 1/1000) (h01 : |a01| ≤ 1/1000) (h02 : |a02| ≤ 1/1000) (hc0 : |c0| ≤ 1/1000)
    (h10 : |a10| ≤ 1/1000) (h11 : |a11| ≤ 1/1000) (h12 : |a12| ≤ 1/1000) (hc1 : |c1| ≤ 1/1000)
    (h20 : |a20| ≤ 1/1000) (h21 : |a21| ≤ 1/1000) (h22 : |a22| ≤ 1/1000) (hc2 : |c2| ≤ 1/1000)
    (h30 : |a30| ≤ 1/1000) (h31 : |a31| ≤ 1/1000) (h32 : |a32| ≤ 1/1000) (hc3 : |c3| ≤ 1/1000)
    (ho0 : |o0| ≤ 1/1000) (ho1 : |o1| ≤ 1/1000) (ho2 : |o2| ≤ 1/1000) (ho3 : |o3| ≤ 1/1000)
    (hoc : |oc| ≤ 1/1000)
    (l0 : -2 ≤ x0) (u0 : x0 ≤ 4) (l1 : -2 ≤ x1) (u1 : x1 ≤ 4) (l2 : -2 ≤ x2) (u2 : x2 ≤ 1) :
    |(-1 + o0) * relu (a00 * x0 + (1 + a01) * x1 + (1 + a02) * x2 + (3 + c0))
      + (1 + o1) * relu (a10 * x0 + (-1 + a11) * x1 + (-1 + a12) * x2 + (-3 + c1))
      + (-1 + o2) * relu ((1/2 + a20) * x0 + (-1 + a21) * x1 + (-1 + a22) * x2 + (-2 + c2))
      + (1/2 + o3) * relu ((-2 + a30) * x0 + a31 * x1 + (-1/2 + a32) * x2 + (1 + c3)) + oc
      - ((-1) * (max (x1 + x2 + 3) ((1/2) * x0 + 1))
         + (1/2) * (max ((-2) * x0 + (-1/2) * x2 + 1) 0))| ≤ 11/20 := by
  have bx0 : |x0| ≤ 4 := abs_le.mpr ⟨by linarith, u0⟩
  have bx1 : |x1| ≤ 4 := abs_le.mpr ⟨by linarith, u1⟩
  have bx2 : |x2| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have p00 := abs_le.mp (pert_abs_mul h00 bx0)
  have p01 := abs_le.mp (pert_abs_mul h01 bx1)
  have p02 := abs_le.mp (pert_abs_mul h02 bx2)
  have p10 := abs_le.mp (pert_abs_mul h10 bx0)
  have p11 := abs_le.mp (pert_abs_mul h11 bx1)
  have p12 := abs_le.mp (pert_abs_mul h12 bx2)
  have p20 := abs_le.mp (pert_abs_mul h20 bx0)
  have p21 := abs_le.mp (pert_abs_mul h21 bx1)
  have p22 := abs_le.mp (pert_abs_mul h22 bx2)
  have p30 := abs_le.mp (pert_abs_mul h30 bx0)
  have p31 := abs_le.mp (pert_abs_mul h31 bx1)
  have p32 := abs_le.mp (pert_abs_mul h32 bx2)
  have k0 := abs_le.mp hc0
  have k1 := abs_le.mp hc1
  have k2 := abs_le.mp hc2
  have k3 := abs_le.mp hc3
  have e0 : |(a00 * x0 + (1 + a01) * x1 + (1 + a02) * x2 + (3 + c0)) - (x1 + x2 + 3)| ≤ 1/50 :=
    abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have e1 : |(a10 * x0 + (-1 + a11) * x1 + (-1 + a12) * x2 + (-3 + c1)) - (-(x1 + x2 + 3))| ≤ 1/50 :=
    abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have e2 : |((1/2 + a20) * x0 + (-1 + a21) * x1 + (-1 + a22) * x2 + (-2 + c2))
      - ((1/2) * x0 + 1 - (x1 + x2 + 3))| ≤ 1/50 :=
    abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have e3 : |((-2 + a30) * x0 + a31 * x1 + (-1/2 + a32) * x2 + (1 + c3))
      - ((-2) * x0 + (-1/2) * x2 + 1)| ≤ 1/50 :=
    abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have r0 := abs_le.mp (relu_pert e0)
  have r1 := abs_le.mp (relu_pert e1)
  have r2 := abs_le.mp (relu_pert e2)
  have r3 := abs_le.mp (relu_pert e3)
  have id1 := relu_sub_relu_neg (x1 + x2 + 3)
  have id2 := add_relu_sub (x1 + x2 + 3) ((1/2) * x0 + 1)
  have id3 : relu ((-2) * x0 + (-1/2) * x2 + 1) = max ((-2) * x0 + (-1/2) * x2 + 1) 0 := rfl
  have s0 : relu (x1 + x2 + 3) ≤ 8 := relu_le_of_le (by linarith) (by norm_num)
  have s1 : relu (-(x1 + x2 + 3)) ≤ 1 := relu_le_of_le (by linarith) (by norm_num)
  have s2 : relu ((1/2) * x0 + 1 - (x1 + x2 + 3)) ≤ 4 :=
    relu_le_of_le (by linarith) (by norm_num)
  have s3 : relu ((-2) * x0 + (-1/2) * x2 + 1) ≤ 6 :=
    relu_le_of_le (by linarith) (by norm_num)
  have n0 := relu_nonneg' (a00 * x0 + (1 + a01) * x1 + (1 + a02) * x2 + (3 + c0))
  have n1 := relu_nonneg' (a10 * x0 + (-1 + a11) * x1 + (-1 + a12) * x2 + (-3 + c1))
  have n2 := relu_nonneg' ((1/2 + a20) * x0 + (-1 + a21) * x1 + (-1 + a22) * x2 + (-2 + c2))
  have n3 := relu_nonneg' ((-2 + a30) * x0 + a31 * x1 + (-1/2 + a32) * x2 + (1 + c3))
  generalize relu (a00 * x0 + (1 + a01) * x1 + (1 + a02) * x2 + (3 + c0)) = R0 at *
  generalize relu (a10 * x0 + (-1 + a11) * x1 + (-1 + a12) * x2 + (-3 + c1)) = R1 at *
  generalize relu ((1/2 + a20) * x0 + (-1 + a21) * x1 + (-1 + a22) * x2 + (-2 + c2)) = R2 at *
  generalize relu ((-2 + a30) * x0 + a31 * x1 + (-1/2 + a32) * x2 + (1 + c3)) = R3 at *
  have q0 := abs_le.mp (pert_abs_mul ho0 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R0| ≤ 9))
  have q1 := abs_le.mp (pert_abs_mul ho1 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R1| ≤ 2))
  have q2 := abs_le.mp (pert_abs_mul ho2 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R2| ≤ 5))
  have q3 := abs_le.mp (pert_abs_mul ho3 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R3| ≤ 7))
  have qc := abs_le.mp hoc
  have h : (-1 + o0) * R0 + (1 + o1) * R1 + (-1 + o2) * R2 + (1/2 + o3) * R3 + oc
      - ((-1) * (max (x1 + x2 + 3) ((1/2) * x0 + 1))
         + (1/2) * (max ((-2) * x0 + (-1/2) * x2 + 1) 0))
      = -(R0 - relu (x1 + x2 + 3)) + (R1 - relu (-(x1 + x2 + 3)))
        - (R2 - relu ((1/2) * x0 + 1 - (x1 + x2 + 3)))
        + (1/2) * (R3 - relu ((-2) * x0 + (-1/2) * x2 + 1))
        + o0 * R0 + o1 * R1 + o2 * R2 + o3 * R3 + oc := by
    rw [← id2, ← id3]; linear_combination id1
  rw [h, abs_le]
  constructor <;> linarith [r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, r3.1, r3.2, q0.1, q0.2, q1.1, q1.2,
    q2.1, q2.2, q3.1, q3.2, qc.1, qc.2]

theorem net_robust : StatementRobust net := by
  intro dW db hW x0 x1 x2 l0 u0 l1 u1 l2 u2
  obtain ⟨hw, hb⟩ := hW
  refine ⟨(-1 + dW 1 0 0) * relu (dW 0 0 0 * x0 + (1 + dW 0 0 1) * x1 + (1 + dW 0 0 2) * x2 + (3 + db 0 0))
      + (1 + dW 1 0 1) * relu (dW 0 1 0 * x0 + (-1 + dW 0 1 1) * x1 + (-1 + dW 0 1 2) * x2 + (-3 + db 0 1))
      + (-1 + dW 1 0 2) * relu ((1/2 + dW 0 2 0) * x0 + (-1 + dW 0 2 1) * x1 + (-1 + dW 0 2 2) * x2 + (-2 + db 0 2))
      + (1/2 + dW 1 0 3) * relu ((-2 + dW 0 3 0) * x0 + dW 0 3 1 * x1 + (-1/2 + dW 0 3 2) * x2 + (1 + db 0 3))
      + db 1 0, ?_, ?_⟩
  · simp [net, Net.evalP, hiddenP, rowsP, dotP]
    try ring_nf
  · exact key (hw 0 0 0) (hw 0 0 1) (hw 0 0 2) (hb 0 0) (hw 0 1 0) (hw 0 1 1) (hw 0 1 2) (hb 0 1)
      (hw 0 2 0) (hw 0 2 1) (hw 0 2 2) (hb 0 2) (hw 0 3 0) (hw 0 3 1) (hw 0 3 2) (hb 0 3)
      (hw 1 0 0) (hw 1 0 1) (hw 1 0 2) (hw 1 0 3) (hb 1 0) l0 u0 l1 u1 l2 u2
end Lane4.Case
