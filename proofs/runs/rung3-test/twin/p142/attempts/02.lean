namespace Lane4.Case
open Lane4

theorem tb {d x B : ℝ} (hd : |d| ≤ 1/1000) (hx : |x| ≤ B) :
    -(B/1000) ≤ d * x ∧ d * x ≤ B/1000 := by
  have h := abs_le.mp (pert_abs_mul hd hx)
  constructor <;> linarith [h.1, h.2]

set_option maxHeartbeats 8000000 in
theorem ex {x0 x1 x2 : ℝ} (l0 : -2 ≤ x0) (u0 : x0 ≤ 4) (l1 : -2 ≤ x1) (u1 : x1 ≤ 4)
    (l2 : -2 ≤ x2) (u2 : x2 ≤ 1) :
    |(-1259/512) * relu (-13/64 * x0 + 13/32 * x1 + 13/32 * x2 + 833/1024)
      + (-605/1024) * relu (811/1024 * x0 + 0 * x1 + 97/512 * x2 + -103/256)
      + (-67/512) * relu (251/1024 * x0 + 1/1024 * x1 + -877/1024 * x2 + 1323/1024)
      + (829/1024) * relu (-29/16 * x0 + 0 * x1 + -229/512 * x2 + 233/256) + (-547/512)
      - ((-1) * (max (x1 + x2 + 3) ((1/2) * x0 + 1))
          + (1/2) * (max ((-2) * x0 + (-1/2) * x2 + 1) 0))| ≤ 1/50 := by
  unfold relu
  have m0 := max_choice (-13/64 * x0 + 13/32 * x1 + 13/32 * x2 + 833/1024) 0
  have m1 := max_choice (811/1024 * x0 + 0 * x1 + 97/512 * x2 + -103/256) 0
  have m2 := max_choice (251/1024 * x0 + 1/1024 * x1 + -877/1024 * x2 + 1323/1024) 0
  have m3 := max_choice (-29/16 * x0 + 0 * x1 + -229/512 * x2 + 233/256) 0
  have m4 := max_choice (x1 + x2 + 3) ((1/2) * x0 + 1)
  have m5 := max_choice ((-2) * x0 + (-1/2) * x2 + 1) 0
  have a0 := le_max_left (-13/64 * x0 + 13/32 * x1 + 13/32 * x2 + 833/1024) 0
  have a1 := le_max_left (811/1024 * x0 + 0 * x1 + 97/512 * x2 + -103/256) 0
  have a2 := le_max_left (251/1024 * x0 + 1/1024 * x1 + -877/1024 * x2 + 1323/1024) 0
  have a3 := le_max_left (-29/16 * x0 + 0 * x1 + -229/512 * x2 + 233/256) 0
  have a4 := le_max_left (x1 + x2 + 3) ((1/2) * x0 + 1)
  have a5 := le_max_right (x1 + x2 + 3) ((1/2) * x0 + 1)
  have a6 := le_max_left ((-2) * x0 + (-1/2) * x2 + 1) 0
  have b0 := le_max_right (-13/64 * x0 + 13/32 * x1 + 13/32 * x2 + 833/1024) 0
  have b1 := le_max_right (811/1024 * x0 + 0 * x1 + 97/512 * x2 + -103/256) 0
  have b2 := le_max_right (251/1024 * x0 + 1/1024 * x1 + -877/1024 * x2 + 1323/1024) 0
  have b3 := le_max_right (-29/16 * x0 + 0 * x1 + -229/512 * x2 + 233/256) 0
  have b6 := le_max_right ((-2) * x0 + (-1/2) * x2 + 1) 0
  rw [abs_le]
  rcases m0 with m0 | m0 <;> rcases m1 with m1 | m1 <;> rcases m2 with m2 | m2 <;>
    rcases m3 with m3 | m3 <;> rcases m4 with m4 | m4 <;> rcases m5 with m5 | m5 <;>
    constructor <;> linarith

set_option maxHeartbeats 4000000 in
theorem key {a00 a01 a02 c0 a10 a11 a12 c1 a20 a21 a22 c2 a30 a31 a32 c3
    o0 o1 o2 o3 oc x0 x1 x2 : ℝ}
    (h00 : |a00| ≤ 1/1000) (h01 : |a01| ≤ 1/1000) (h02 : |a02| ≤ 1/1000) (hc0 : |c0| ≤ 1/1000)
    (h10 : |a10| ≤ 1/1000) (h11 : |a11| ≤ 1/1000) (h12 : |a12| ≤ 1/1000) (hc1 : |c1| ≤ 1/1000)
    (h20 : |a20| ≤ 1/1000) (h21 : |a21| ≤ 1/1000) (h22 : |a22| ≤ 1/1000) (hc2 : |c2| ≤ 1/1000)
    (h30 : |a30| ≤ 1/1000) (h31 : |a31| ≤ 1/1000) (h32 : |a32| ≤ 1/1000) (hc3 : |c3| ≤ 1/1000)
    (ho0 : |o0| ≤ 1/1000) (ho1 : |o1| ≤ 1/1000) (ho2 : |o2| ≤ 1/1000) (ho3 : |o3| ≤ 1/1000)
    (hoc : |oc| ≤ 1/1000)
    (l0 : -2 ≤ x0) (u0 : x0 ≤ 4) (l1 : -2 ≤ x1) (u1 : x1 ≤ 4) (l2 : -2 ≤ x2) (u2 : x2 ≤ 1) :
    |((-1259/512) + o0) * relu ((-13/64 + a00) * x0 + (13/32 + a01) * x1 + (13/32 + a02) * x2 + (833/1024 + c0))
      + ((-605/1024) + o1) * relu ((811/1024 + a10) * x0 + (0 + a11) * x1 + (97/512 + a12) * x2 + (-103/256 + c1))
      + ((-67/512) + o2) * relu ((251/1024 + a20) * x0 + (1/1024 + a21) * x1 + (-877/1024 + a22) * x2 + (1323/1024 + c2))
      + ((829/1024) + o3) * relu ((-29/16 + a30) * x0 + (0 + a31) * x1 + (-229/512 + a32) * x2 + (233/256 + c3))
      + ((-547/512) + oc)
      - ((-1) * (max (x1 + x2 + 3) ((1/2) * x0 + 1))
          + (1/2) * (max ((-2) * x0 + (-1/2) * x2 + 1) 0))| ≤ 11/20 := by
  have bx0 : |x0| ≤ 4 := abs_le.mpr ⟨by linarith, u0⟩
  have bx1 : |x1| ≤ 4 := abs_le.mpr ⟨by linarith, u1⟩
  have bx2 : |x2| ≤ 2 := abs_le.mpr ⟨l2, by linarith⟩
  have t00 := tb h00 bx0
  have t01 := tb h01 bx1
  have t02 := tb h02 bx2
  have t10 := tb h10 bx0
  have t11 := tb h11 bx1
  have t12 := tb h12 bx2
  have t20 := tb h20 bx0
  have t21 := tb h21 bx1
  have t22 := tb h22 bx2
  have t30 := tb h30 bx0
  have t31 := tb h31 bx1
  have t32 := tb h32 bx2
  have c0' := abs_le.mp hc0
  have c1' := abs_le.mp hc1
  have c2' := abs_le.mp hc2
  have c3' := abs_le.mp hc3
  have e0 : |((-13/64 + a00) * x0 + (13/32 + a01) * x1 + (13/32 + a02) * x2 + (833/1024 + c0))
      - (-13/64 * x0 + 13/32 * x1 + 13/32 * x2 + 833/1024)| ≤ 12/1000 := by
    rw [abs_le]; constructor <;> nlinarith [t00, t01, t02, c0']
  have e1 : |((811/1024 + a10) * x0 + (0 + a11) * x1 + (97/512 + a12) * x2 + (-103/256 + c1))
      - (811/1024 * x0 + 0 * x1 + 97/512 * x2 + -103/256)| ≤ 12/1000 := by
    rw [abs_le]; constructor <;> nlinarith [t10, t11, t12, c1']
  have e2 : |((251/1024 + a20) * x0 + (1/1024 + a21) * x1 + (-877/1024 + a22) * x2 + (1323/1024 + c2))
      - (251/1024 * x0 + 1/1024 * x1 + -877/1024 * x2 + 1323/1024)| ≤ 12/1000 := by
    rw [abs_le]; constructor <;> nlinarith [t20, t21, t22, c2']
  have e3 : |((-29/16 + a30) * x0 + (0 + a31) * x1 + (-229/512 + a32) * x2 + (233/256 + c3))
      - (-29/16 * x0 + 0 * x1 + -229/512 * x2 + 233/256)| ≤ 12/1000 := by
    rw [abs_le]; constructor <;> nlinarith [t30, t31, t32, c3']
  have r0 := abs_le.mp (relu_pert e0)
  have r1 := abs_le.mp (relu_pert e1)
  have r2 := abs_le.mp (relu_pert e2)
  have r3 := abs_le.mp (relu_pert e3)
  have X := abs_le.mp (ex l0 u0 l1 u1 l2 u2)
  have s0 : relu (-13/64 * x0 + 13/32 * x1 + 13/32 * x2 + 833/1024) ≤ 6 :=
    relu_le_of_le (by linarith) (by norm_num)
  have s1 : relu (811/1024 * x0 + 0 * x1 + 97/512 * x2 + -103/256) ≤ 6 :=
    relu_le_of_le (by linarith) (by norm_num)
  have s2 : relu (251/1024 * x0 + 1/1024 * x1 + -877/1024 * x2 + 1323/1024) ≤ 6 :=
    relu_le_of_le (by linarith) (by norm_num)
  have s3 : relu (-29/16 * x0 + 0 * x1 + -229/512 * x2 + 233/256) ≤ 6 :=
    relu_le_of_le (by linarith) (by norm_num)
  have n0 := relu_nonneg' (-13/64 * x0 + 13/32 * x1 + 13/32 * x2 + 833/1024)
  have n1 := relu_nonneg' (811/1024 * x0 + 0 * x1 + 97/512 * x2 + -103/256)
  have n2 := relu_nonneg' (251/1024 * x0 + 1/1024 * x1 + -877/1024 * x2 + 1323/1024)
  have n3 := relu_nonneg' (-29/16 * x0 + 0 * x1 + -229/512 * x2 + 233/256)
  generalize relu ((-13/64 + a00) * x0 + (13/32 + a01) * x1 + (13/32 + a02) * x2 + (833/1024 + c0)) = R0 at *
  generalize relu ((811/1024 + a10) * x0 + (0 + a11) * x1 + (97/512 + a12) * x2 + (-103/256 + c1)) = R1 at *
  generalize relu ((251/1024 + a20) * x0 + (1/1024 + a21) * x1 + (-877/1024 + a22) * x2 + (1323/1024 + c2)) = R2 at *
  generalize relu ((-29/16 + a30) * x0 + (0 + a31) * x1 + (-229/512 + a32) * x2 + (233/256 + c3)) = R3 at *
  generalize relu (-13/64 * x0 + 13/32 * x1 + 13/32 * x2 + 833/1024) = Q0 at *
  generalize relu (811/1024 * x0 + 0 * x1 + 97/512 * x2 + -103/256) = Q1 at *
  generalize relu (251/1024 * x0 + 1/1024 * x1 + -877/1024 * x2 + 1323/1024) = Q2 at *
  generalize relu (-29/16 * x0 + 0 * x1 + -229/512 * x2 + 233/256) = Q3 at *
  have q0 := tb ho0 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R0| ≤ 7)
  have q1 := tb ho1 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R1| ≤ 7)
  have q2 := tb ho2 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R2| ≤ 7)
  have q3 := tb ho3 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R3| ≤ 7)
  have qc := abs_le.mp hoc
  rw [abs_le]
  constructor <;> linarith [r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, r3.1, r3.2, q0.1, q0.2,
    q1.1, q1.2, q2.1, q2.2, q3.1, q3.2, qc.1, qc.2, X.1, X.2]

theorem twin_robust : StatementRobustTwin := by
  intro dW db hW x0 x1 x2 l0 u0 l1 u1 l2 u2
  obtain ⟨hw, hb⟩ := hW
  refine ⟨((-1259/512) + dW 1 0 0) * relu ((-13/64 + dW 0 0 0) * x0 + (13/32 + dW 0 0 1) * x1 + (13/32 + dW 0 0 2) * x2 + (833/1024 + db 0 0))
      + ((-605/1024) + dW 1 0 1) * relu ((811/1024 + dW 0 1 0) * x0 + (0 + dW 0 1 1) * x1 + (97/512 + dW 0 1 2) * x2 + (-103/256 + db 0 1))
      + ((-67/512) + dW 1 0 2) * relu ((251/1024 + dW 0 2 0) * x0 + (1/1024 + dW 0 2 1) * x1 + (-877/1024 + dW 0 2 2) * x2 + (1323/1024 + db 0 2))
      + ((829/1024) + dW 1 0 3) * relu ((-29/16 + dW 0 3 0) * x0 + (0 + dW 0 3 1) * x1 + (-229/512 + dW 0 3 2) * x2 + (233/256 + db 0 3))
      + ((-547/512) + db 1 0), ?_, ?_⟩
  · simp [twin, Net.evalP, hiddenP, rowsP, dotP]
    try ring_nf
  · unfold spec
    exact key (hw 0 0 0) (hw 0 0 1) (hw 0 0 2) (hb 0 0) (hw 0 1 0) (hw 0 1 1) (hw 0 1 2) (hb 0 1)
      (hw 0 2 0) (hw 0 2 1) (hw 0 2 2) (hb 0 2) (hw 0 3 0) (hw 0 3 1) (hw 0 3 2) (hb 0 3)
      (hw 1 0 0) (hw 1 0 1) (hw 1 0 2) (hw 1 0 3) (hb 1 0) l0 u0 l1 u1 l2 u2
end Lane4.Case
