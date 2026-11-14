namespace Lane4.Case
open Lane4

def net : Net :=
  { hidden := [{ W := [[1, 0], [-1, 0], [1, -1/2]], b := [-3, 3, -5] },
               { W := [[1, -1, -1], [-1, 1, 1]], b := [0, 0] }],
    out := { W := [[1, 1]], b := [0] } }

theorem preerr {a b d x0 x1 : ℝ} (ha : |a| ≤ 1/1000) (hb : |b| ≤ 1/1000) (hd : |d| ≤ 1/1000)
    (bx0 : |x0| ≤ 4) (bx1 : |x1| ≤ 4) : |a * x0 + b * x1 + d| ≤ 9/1000 :=
  le_trans (abs_add3_le (pert_abs_mul ha bx0) (pert_abs_mul hb bx1) hd) (by norm_num)

theorem stage3 {P0 P1 o0 o1 oc m : ℝ} (hm : -4 ≤ m) (hm' : m ≤ 1)
    (h0 : |P0 - m| ≤ 43/1000) (h1 : |P1 - (-m)| ≤ 43/1000)
    (ho0 : |o0| ≤ 1/1000) (ho1 : |o1| ≤ 1/1000) (hoc : |oc| ≤ 1/1000) :
    |(1 + o0) * relu P0 + (1 + o1) * relu P1 + oc - abs m| ≤ 1/5 := by
  have r0 := abs_le.mp (relu_pert h0)
  have r1 := abs_le.mp (relu_pert h1)
  have idd := relu_add_relu_neg m
  have s0 : relu m ≤ 1 := relu_le_of_le hm' (by norm_num)
  have s1 : relu (-m) ≤ 4 := relu_le_of_le (by linarith) (by norm_num)
  have n0 := relu_nonneg' P0
  have n1 := relu_nonneg' P1
  have n2 := relu_nonneg' m
  have n3 := relu_nonneg' (-m)
  have h : (1 + o0) * relu P0 + (1 + o1) * relu P1 + oc - abs m
      = (relu P0 - relu m) + (relu P1 - relu (-m)) + o0 * relu P0 + o1 * relu P1 + oc := by
    linear_combination idd
  have q0 := abs_le.mp (pert_abs_mul ho0 (abs_le.mpr ⟨by linarith, by linarith⟩ : |relu P0| ≤ 5))
  have q1 := abs_le.mp (pert_abs_mul ho1 (abs_le.mpr ⟨by linarith, by linarith⟩ : |relu P1| ≤ 5))
  have qc := abs_le.mp hoc
  rw [h, abs_le]
  constructor <;> linarith [r0.1, r0.2, r1.1, r1.2, q0.1, q0.2, q1.1, q1.2, qc.1, qc.2]

theorem key {x0 x1 a00 a01 c0 a10 a11 c1 a20 a21 c2 g00 g01 g02 gc0 g10 g11 g12 gc1 o0 o1 oc : ℝ}
    (h00 : |a00| ≤ 1/1000) (h01 : |a01| ≤ 1/1000) (hc0 : |c0| ≤ 1/1000)
    (h10 : |a10| ≤ 1/1000) (h11 : |a11| ≤ 1/1000) (hc1 : |c1| ≤ 1/1000)
    (h20 : |a20| ≤ 1/1000) (h21 : |a21| ≤ 1/1000) (hc2 : |c2| ≤ 1/1000)
    (k00 : |g00| ≤ 1/1000) (k01 : |g01| ≤ 1/1000) (k02 : |g02| ≤ 1/1000) (kc0 : |gc0| ≤ 1/1000)
    (k10 : |g10| ≤ 1/1000) (k11 : |g11| ≤ 1/1000) (k12 : |g12| ≤ 1/1000) (kc1 : |gc1| ≤ 1/1000)
    (ho0 : |o0| ≤ 1/1000) (ho1 : |o1| ≤ 1/1000) (hoc : |oc| ≤ 1/1000)
    (l0 : -1 ≤ x0) (u0 : x0 ≤ 4) (l1 : -4 ≤ x1) (u1 : x1 ≤ 1) :
    |(1 + o0) * relu ((1 + g00) * relu ((1 + a00) * x0 + a01 * x1 + (-3 + c0))
          + (-1 + g01) * relu ((-1 + a10) * x0 + a11 * x1 + (3 + c1))
          + (-1 + g02) * relu ((1 + a20) * x0 + (-1/2 + a21) * x1 + (-5 + c2)) + gc0)
      + (1 + o1) * relu ((-1 + g10) * relu ((1 + a00) * x0 + a01 * x1 + (-3 + c0))
          + (1 + g11) * relu ((-1 + a10) * x0 + a11 * x1 + (3 + c1))
          + (1 + g12) * relu ((1 + a20) * x0 + (-1/2 + a21) * x1 + (-5 + c2)) + gc1)
      + oc - spec x0 x1| ≤ 1/5 := by
  have bx0 : |x0| ≤ 4 := abs_le.mpr ⟨by linarith, u0⟩
  have bx1 : |x1| ≤ 4 := abs_le.mpr ⟨l1, by linarith⟩
  have e0 : |((1 + a00) * x0 + a01 * x1 + (-3 + c0)) - (x0 + -3)| ≤ 9/1000 := by
    have h : ((1 + a00) * x0 + a01 * x1 + (-3 + c0)) - (x0 + -3) = a00 * x0 + a01 * x1 + c0 := by ring
    rw [h]; exact preerr h00 h01 hc0 bx0 bx1
  have e1 : |((-1 + a10) * x0 + a11 * x1 + (3 + c1)) - (-(x0 + -3))| ≤ 9/1000 := by
    have h : ((-1 + a10) * x0 + a11 * x1 + (3 + c1)) - (-(x0 + -3)) = a10 * x0 + a11 * x1 + c1 := by ring
    rw [h]; exact preerr h10 h11 hc1 bx0 bx1
  have e2 : |((1 + a20) * x0 + (-1/2 + a21) * x1 + (-5 + c2)) - ((x0 + -3) - (1/2 * x1 + 2))| ≤ 9/1000 := by
    have h : ((1 + a20) * x0 + (-1/2 + a21) * x1 + (-5 + c2)) - ((x0 + -3) - (1/2 * x1 + 2)) = a20 * x0 + a21 * x1 + c2 := by ring
    rw [h]; exact preerr h20 h21 hc2 bx0 bx1
  have r0 := abs_le.mp (relu_pert e0)
  have r1 := abs_le.mp (relu_pert e1)
  have r2 := abs_le.mp (relu_pert e2)
  have s0 : relu (x0 + -3) ≤ 1 := relu_le_of_le (by linarith) (by norm_num)
  have s1 : relu (-(x0 + -3)) ≤ 4 := relu_le_of_le (by linarith) (by norm_num)
  have s2 : relu ((x0 + -3) - (1/2 * x1 + 2)) ≤ 1 := relu_le_of_le (by linarith) (by norm_num)
  have t0 := relu_nonneg' (x0 + -3)
  have t1 := relu_nonneg' (-(x0 + -3))
  have t2 := relu_nonneg' ((x0 + -3) - (1/2 * x1 + 2))
  have n0 := relu_nonneg' ((1 + a00) * x0 + a01 * x1 + (-3 + c0))
  have n1 := relu_nonneg' ((-1 + a10) * x0 + a11 * x1 + (3 + c1))
  have n2 := relu_nonneg' ((1 + a20) * x0 + (-1/2 + a21) * x1 + (-5 + c2))
  have idm : min (x0 + -3) (1/2 * x1 + 2)
      = relu (x0 + -3) - relu (-(x0 + -3)) - relu ((x0 + -3) - (1/2 * x1 + 2)) := by
    have i1 := relu_sub_relu_neg (x0 + -3)
    have i2 := sub_relu_sub (x0 + -3) (1/2 * x1 + 2)
    linarith
  have mlo : -4 ≤ min (x0 + -3) (1/2 * x1 + 2) := le_min (by linarith) (by linarith)
  have mhi : min (x0 + -3) (1/2 * x1 + 2) ≤ 1 := le_trans (min_le_left _ _) (by linarith)
  generalize relu ((1 + a00) * x0 + a01 * x1 + (-3 + c0)) = U0 at *
  generalize relu ((-1 + a10) * x0 + a11 * x1 + (3 + c1)) = U1 at *
  generalize relu ((1 + a20) * x0 + (-1/2 + a21) * x1 + (-5 + c2)) = U2 at *
  have bU0 : |U0| ≤ 5 := abs_le.mpr ⟨by linarith, by linarith⟩
  have bU1 : |U1| ≤ 5 := abs_le.mpr ⟨by linarith, by linarith⟩
  have bU2 : |U2| ≤ 5 := abs_le.mpr ⟨by linarith, by linarith⟩
  have p00 := abs_le.mp (pert_abs_mul k00 bU0)
  have p01 := abs_le.mp (pert_abs_mul k01 bU1)
  have p02 := abs_le.mp (pert_abs_mul k02 bU2)
  have p10 := abs_le.mp (pert_abs_mul k10 bU0)
  have p11 := abs_le.mp (pert_abs_mul k11 bU1)
  have p12 := abs_le.mp (pert_abs_mul k12 bU2)
  have cc0 := abs_le.mp kc0
  have cc1 := abs_le.mp kc1
  have hP0 : |((1 + g00) * U0 + (-1 + g01) * U1 + (-1 + g02) * U2 + gc0)
      - min (x0 + -3) (1/2 * x1 + 2)| ≤ 43/1000 := by
    rw [idm, abs_le]
    constructor <;> linarith
  have hP1 : |((-1 + g10) * U0 + (1 + g11) * U1 + (1 + g12) * U2 + gc1)
      - (-min (x0 + -3) (1/2 * x1 + 2))| ≤ 43/1000 := by
    rw [idm, abs_le]
    constructor <;> linarith
  have := stage3 mlo mhi hP0 hP1 ho0 ho1 hoc
  unfold spec
  exact this


theorem net_robust : StatementRobust net := by
  intro dW db hW x0 x1 l0 u0 l1 u1
  obtain ⟨hw, hb⟩ := hW
  refine ⟨(1 + dW 2 0 0) * relu ((1 + dW 1 0 0) * relu ((1 + dW 0 0 0) * x0 + dW 0 0 1 * x1 + (-3 + db 0 0))
          + (-1 + dW 1 0 1) * relu ((-1 + dW 0 1 0) * x0 + dW 0 1 1 * x1 + (3 + db 0 1))
          + (-1 + dW 1 0 2) * relu ((1 + dW 0 2 0) * x0 + (-1/2 + dW 0 2 1) * x1 + (-5 + db 0 2)) + db 1 0)
      + (1 + dW 2 0 1) * relu ((-1 + dW 1 1 0) * relu ((1 + dW 0 0 0) * x0 + dW 0 0 1 * x1 + (-3 + db 0 0))
          + (1 + dW 1 1 1) * relu ((-1 + dW 0 1 0) * x0 + dW 0 1 1 * x1 + (3 + db 0 1))
          + (1 + dW 1 1 2) * relu ((1 + dW 0 2 0) * x0 + (-1/2 + dW 0 2 1) * x1 + (-5 + db 0 2)) + db 1 1)
      + db 2 0, ?_, ?_⟩
  · simp [net, Net.evalP, hiddenP, rowsP, dotP]
    try ring_nf
  · exact key (hw 0 0 0) (hw 0 0 1) (hb 0 0) (hw 0 1 0) (hw 0 1 1) (hb 0 1)
      (hw 0 2 0) (hw 0 2 1) (hb 0 2) (hw 1 0 0) (hw 1 0 1) (hw 1 0 2) (hb 1 0)
      (hw 1 1 0) (hw 1 1 1) (hw 1 1 2) (hb 1 1) (hw 2 0 0) (hw 2 0 1) (hb 2 0) l0 u0 l1 u1

end Lane4.Case
