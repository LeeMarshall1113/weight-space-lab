namespace Lane4.Case
open Lane4

def net : Net :=
  { hidden := [{ W := [[0, 0, 1/2], [0, 0, 1/2], [-1/2, 0, 1], [-1, 0, 1]], b := [1, -1/2, 0, -2] },
               { W := [[1, -1, 0, 0], [-1, 1, 1, -1]], b := [0, 0] }],
    out := { W := [[1, 1]], b := [1/2] } }

noncomputable def R0 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu ((0 + dW 0 0 0) * x0 + (0 + dW 0 0 1) * x1 + (1/2 + dW 0 0 2) * x2 + (1 + db 0 0))
noncomputable def R1 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu ((0 + dW 0 1 0) * x0 + (0 + dW 0 1 1) * x1 + (1/2 + dW 0 1 2) * x2 + (-1/2 + db 0 1))
noncomputable def R2 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu ((-1/2 + dW 0 2 0) * x0 + (0 + dW 0 2 1) * x1 + (1 + dW 0 2 2) * x2 + (0 + db 0 2))
noncomputable def R3 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu ((-1 + dW 0 3 0) * x0 + (0 + dW 0 3 1) * x1 + (1 + dW 0 3 2) * x2 + (-2 + db 0 3))
noncomputable def Q0 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu ((1 + dW 1 0 0) * R0 dW db x0 x1 x2 + (-1 + dW 1 0 1) * R1 dW db x0 x1 x2
    + (0 + dW 1 0 2) * R2 dW db x0 x1 x2 + (0 + dW 1 0 3) * R3 dW db x0 x1 x2 + (0 + db 1 0))
noncomputable def Q1 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu ((-1 + dW 1 1 0) * R0 dW db x0 x1 x2 + (1 + dW 1 1 1) * R1 dW db x0 x1 x2
    + (1 + dW 1 1 2) * R2 dW db x0 x1 x2 + (-1 + dW 1 1 3) * R3 dW db x0 x1 x2 + (0 + db 1 1))
noncomputable def Yv (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  (1 + dW 2 0 0) * Q0 dW db x0 x1 x2 + (1 + dW 2 0 1) * Q1 dW db x0 x1 x2 + (1/2 + db 2 0)

theorem lz_unit1 {x0 x1 x2 w0 w1 w2 w3 d0 d1 d2 dc E : ℝ}
    (hE : E = w0 * x0 + w1 * x1 + w2 * x2 + w3)
    (h0 : |d0| ≤ 1/1000) (h1 : |d1| ≤ 1/1000) (h2 : |d2| ≤ 1/1000) (hc : |dc| ≤ 1/1000)
    (b0 : |x0| ≤ 2) (b1 : |x1| ≤ 4) (b2 : |x2| ≤ 8) :
    |relu ((w0 + d0) * x0 + (w1 + d1) * x1 + (w2 + d2) * x2 + (w3 + dc)) - relu E| ≤ 3/200 := by
  apply relu_pert
  have h : (w0 + d0) * x0 + (w1 + d1) * x1 + (w2 + d2) * x2 + (w3 + dc) - E
      = d0 * x0 + d1 * x1 + d2 * x2 + dc := by rw [hE]; ring
  rw [h]
  have t0 := abs_le.mp (pert_abs_mul h0 b0)
  have t1 := abs_le.mp (pert_abs_mul h1 b1)
  have t2 := abs_le.mp (pert_abs_mul h2 b2)
  have tc := abs_le.mp hc
  rw [abs_le]
  constructor <;> linarith [t0.1, t0.2, t1.1, t1.2, t2.1, t2.2, tc.1, tc.2]

theorem lz_unit2 {w0 w1 w2 w3 w4 d0 d1 d2 d3 dc v0 v1 v2 v3 V0 V1 V2 V3 E : ℝ}
    (hE : E = w0 * v0 + w1 * v1 + w2 * v2 + w3 * v3 + w4)
    (hw0 : |w0| ≤ 1) (hw1 : |w1| ≤ 1) (hw2 : |w2| ≤ 1) (hw3 : |w3| ≤ 1)
    (h0 : |d0| ≤ 1/1000) (h1 : |d1| ≤ 1/1000) (h2 : |d2| ≤ 1/1000) (h3 : |d3| ≤ 1/1000)
    (hc : |dc| ≤ 1/1000)
    (hv0 : |v0| ≤ 4) (hv1 : |v1| ≤ 4) (hv2 : |v2| ≤ 4) (hv3 : |v3| ≤ 4)
    (e0 : |V0 - v0| ≤ 3/200) (e1 : |V1 - v1| ≤ 3/200) (e2 : |V2 - v2| ≤ 3/200)
    (e3 : |V3 - v3| ≤ 3/200) :
    |relu ((w0 + d0) * V0 + (w1 + d1) * V1 + (w2 + d2) * V2 + (w3 + d3) * V3 + (w4 + dc))
      - relu E| ≤ 4/50 := by
  apply relu_pert
  subst hE
  have t0 := abs_le.mp (pert_mul (a := w0) h0 e0 hv0)
  have t1 := abs_le.mp (pert_mul (a := w1) h1 e1 hv1)
  have t2 := abs_le.mp (pert_mul (a := w2) h2 e2 hv2)
  have t3 := abs_le.mp (pert_mul (a := w3) h3 e3 hv3)
  have m0 : |w0| * (3/200) ≤ 3/200 := mul_le_of_le_one_left (by norm_num) hw0
  have m1 : |w1| * (3/200) ≤ 3/200 := mul_le_of_le_one_left (by norm_num) hw1
  have m2 : |w2| * (3/200) ≤ 3/200 := mul_le_of_le_one_left (by norm_num) hw2
  have m3 : |w3| * (3/200) ≤ 3/200 := mul_le_of_le_one_left (by norm_num) hw3
  have tc := abs_le.mp hc
  rw [abs_le]
  constructor <;> linarith [t0.1, t0.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, tc.1, tc.2]

theorem lz_aff2 {w0 w1 w2 d0 d1 dc v0 v1 V0 V1 S : ℝ}
    (hS : S = w0 * v0 + w1 * v1 + w2)
    (hw0 : |w0| ≤ 1) (hw1 : |w1| ≤ 1)
    (h0 : |d0| ≤ 1/1000) (h1 : |d1| ≤ 1/1000) (hc : |dc| ≤ 1/1000)
    (hv0 : |v0| ≤ 4) (hv1 : |v1| ≤ 4)
    (e0 : |V0 - v0| ≤ 4/50) (e1 : |V1 - v1| ≤ 4/50) :
    |(w0 + d0) * V0 + (w1 + d1) * V1 + (w2 + dc) - S| ≤ 1/5 := by
  subst hS
  have t0 := abs_le.mp (pert_mul (a := w0) h0 e0 hv0)
  have t1 := abs_le.mp (pert_mul (a := w1) h1 e1 hv1)
  have m0 : |w0| * (4/50) ≤ 4/50 := mul_le_of_le_one_left (by norm_num) hw0
  have m1 : |w1| * (4/50) ≤ 4/50 := mul_le_of_le_one_left (by norm_num) hw1
  have tc := abs_le.mp hc
  rw [abs_le]
  constructor <;> linarith [t0.1, t0.2, t1.1, t1.2, tc.1, tc.2]

theorem lz_med (P Q R : ℝ) (h : Q ≤ R) :
    max (min P Q) (min (max P Q) R) = max Q (min P R) := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem lz_cl (A : ℝ) : min (max A (1/2)) 2 = max (1/2) (min A 2) := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem lz_dom (T Q m : ℝ) (h : Q ≤ T) : max T (max Q m) = max T m := by
  simp only [max_def]
  split_ifs <;> linarith

theorem lz_e2 (a b r u : ℝ) (h : u ≤ r) :
    relu (relu a - relu (a - b) - r + u) = relu (min a b - (r - u)) := by
  simp only [relu, max_def, min_def]
  split_ifs <;> linarith

theorem lz_fin (Mv m : ℝ) :
    max Mv (m + 1/2) = 1/2 + (Mv - 1/2) + relu (m - (Mv - 1/2)) := by
  have h := Lane4.add_relu_sub Mv (m + 1/2)
  have h2 : m + 1/2 - Mv = m - (Mv - 1/2) := by ring
  rw [h2] at h
  rw [← h]
  ring

theorem exact_id (x0 x1 x2 : ℝ) (l0 : -2 ≤ x0) (u1 : x1 ≤ 2) :
    spec x0 x1 x2 = 1/2 + relu (relu ((1/2) * x2 + 1) - relu ((1/2) * x2 - 1/2))
      + relu (relu ((-1/2) * x0 + x2) - relu (x2 - x0 - 2) - relu ((1/2) * x2 + 1)
          + relu ((1/2) * x2 - 1/2)) := by
  have hQR : x1 + (-3/2) ≤ (1/2) * x0 + (5/2) := by linarith
  have hQT : x1 + (-3/2) ≤ max (1/2) (min ((1/2) * x2 + (3/2)) 2) :=
    le_max_of_le_left (by linarith)
  have hs : spec x0 x1 x2 = max (max (1/2) (min ((1/2) * x2 + (3/2)) 2))
      (min ((-1/2) * x0 + x2 + (1/2)) ((1/2) * x0 + (5/2))) := by
    unfold spec
    rw [lz_med _ _ _ hQR, lz_cl]
    exact lz_dom _ _ _ hQT
  have e1 : relu (relu ((1/2) * x2 + 1) - relu ((1/2) * x2 - 1/2))
      = max (1/2) (min ((1/2) * x2 + (3/2)) 2) - 1/2 := by
    simp only [relu, max_def, min_def]
    split_ifs <;> linarith
  have hur : relu ((1/2) * x2 - 1/2) ≤ relu ((1/2) * x2 + 1) := by
    unfold relu
    exact max_le_max (by linarith) le_rfl
  have e1' : relu ((1/2) * x2 + 1) - relu ((1/2) * x2 - 1/2)
      = max (1/2) (min ((1/2) * x2 + (3/2)) 2) - 1/2 := by
    have := relu_of_nonneg (sub_nonneg.2 hur)
    linarith
  have e2 := lz_e2 ((-1/2) * x0 + x2) ((1/2) * x0 + 2) (relu ((1/2) * x2 + 1))
    (relu ((1/2) * x2 - 1/2)) hur
  have hv : (-1/2) * x0 + x2 - ((1/2) * x0 + 2) = x2 - x0 - 2 := by ring
  rw [hv] at e2
  have hm : min ((-1/2) * x0 + x2 + (1/2)) ((1/2) * x0 + (5/2))
      = min ((-1/2) * x0 + x2) ((1/2) * x0 + 2) + 1/2 := by
    simp only [min_def]
    split_ifs <;> linarith
  rw [e2, hs, e1, e1', hm]
  exact lz_fin _ _

theorem key (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ)
    (hw : ∀ l i j, |dW l i j| ≤ 1/1000) (hb : ∀ l i, |db l i| ≤ 1/1000)
    (x0 x1 x2 : ℝ) (l0 : -2 ≤ x0) (u0 : x0 ≤ 2) (l1 : -4 ≤ x1) (u1 : x1 ≤ 2)
    (l2 : -8 ≤ x2) (u2 : x2 ≤ 2) :
    |Yv dW db x0 x1 x2 - spec x0 x1 x2| ≤ 1/5 := by
  have bx0 : |x0| ≤ 2 := abs_le.mpr ⟨by linarith, u0⟩
  have bx1 : |x1| ≤ 4 := abs_le.mpr ⟨l1, by linarith⟩
  have bx2 : |x2| ≤ 8 := abs_le.mpr ⟨l2, by linarith⟩
  have s0 : |R0 dW db x0 x1 x2 - relu ((1/2) * x2 + 1)| ≤ 3/200 :=
    lz_unit1 (w0 := 0) (w1 := 0) (w2 := 1/2) (w3 := 1) (by ring)
      (hw 0 0 0) (hw 0 0 1) (hw 0 0 2) (hb 0 0) bx0 bx1 bx2
  have s1 : |R1 dW db x0 x1 x2 - relu ((1/2) * x2 - 1/2)| ≤ 3/200 :=
    lz_unit1 (w0 := 0) (w1 := 0) (w2 := 1/2) (w3 := -1/2) (by ring)
      (hw 0 1 0) (hw 0 1 1) (hw 0 1 2) (hb 0 1) bx0 bx1 bx2
  have s2 : |R2 dW db x0 x1 x2 - relu ((-1/2) * x0 + x2)| ≤ 3/200 :=
    lz_unit1 (w0 := -1/2) (w1 := 0) (w2 := 1) (w3 := 0) (by ring)
      (hw 0 2 0) (hw 0 2 1) (hw 0 2 2) (hb 0 2) bx0 bx1 bx2
  have s3 : |R3 dW db x0 x1 x2 - relu (x2 - x0 - 2)| ≤ 3/200 :=
    lz_unit1 (w0 := -1) (w1 := 0) (w2 := 1) (w3 := -2) (by ring)
      (hw 0 3 0) (hw 0 3 1) (hw 0 3 2) (hb 0 3) bx0 bx1 bx2
  have hr : relu ((1/2) * x2 + 1) ≤ 2 := relu_le_of_le (by linarith) (by norm_num)
  have hu : relu ((1/2) * x2 - 1/2) ≤ 1/2 := relu_le_of_le (by linarith) (by norm_num)
  have hg : relu ((-1/2) * x0 + x2) ≤ 3 := relu_le_of_le (by linarith) (by norm_num)
  have hv : relu (x2 - x0 - 2) ≤ 2 := relu_le_of_le (by linarith) (by norm_num)
  have nr := relu_nonneg' ((1/2) * x2 + 1)
  have nu := relu_nonneg' ((1/2) * x2 - 1/2)
  have ng := relu_nonneg' ((-1/2) * x0 + x2)
  have nv := relu_nonneg' (x2 - x0 - 2)
  have av0 : |relu ((1/2) * x2 + 1)| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  have av1 : |relu ((1/2) * x2 - 1/2)| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  have av2 : |relu ((-1/2) * x0 + x2)| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  have av3 : |relu (x2 - x0 - 2)| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hP0 : relu (relu ((1/2) * x2 + 1) - relu ((1/2) * x2 - 1/2)) ≤ 4 :=
    relu_le_of_le (by linarith) (by norm_num)
  have hP1 : relu (relu ((-1/2) * x0 + x2) - relu (x2 - x0 - 2) - relu ((1/2) * x2 + 1)
      + relu ((1/2) * x2 - 1/2)) ≤ 4 :=
    relu_le_of_le (by linarith) (by norm_num)
  have nP0 := relu_nonneg' (relu ((1/2) * x2 + 1) - relu ((1/2) * x2 - 1/2))
  have nP1 := relu_nonneg' (relu ((-1/2) * x0 + x2) - relu (x2 - x0 - 2)
      - relu ((1/2) * x2 + 1) + relu ((1/2) * x2 - 1/2))
  have av4 : |relu (relu ((1/2) * x2 + 1) - relu ((1/2) * x2 - 1/2))| ≤ 4 :=
    abs_le.mpr ⟨by linarith, hP0⟩
  have av5 : |relu (relu ((-1/2) * x0 + x2) - relu (x2 - x0 - 2) - relu ((1/2) * x2 + 1)
      + relu ((1/2) * x2 - 1/2))| ≤ 4 := abs_le.mpr ⟨by linarith, hP1⟩
  have q0 : |Q0 dW db x0 x1 x2
      - relu (relu ((1/2) * x2 + 1) - relu ((1/2) * x2 - 1/2))| ≤ 4/50 :=
    lz_unit2 (w0 := 1) (w1 := -1) (w2 := 0) (w3 := 0) (w4 := 0) (by ring)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hw 1 0 0) (hw 1 0 1) (hw 1 0 2) (hw 1 0 3) (hb 1 0)
      av0 av1 av2 av3 s0 s1 s2 s3
  have q1 : |Q1 dW db x0 x1 x2
      - relu (relu ((-1/2) * x0 + x2) - relu (x2 - x0 - 2) - relu ((1/2) * x2 + 1)
          + relu ((1/2) * x2 - 1/2))| ≤ 4/50 :=
    lz_unit2 (w0 := -1) (w1 := 1) (w2 := 1) (w3 := -1) (w4 := 0) (by ring)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hw 1 1 0) (hw 1 1 1) (hw 1 1 2) (hw 1 1 3) (hb 1 1)
      av0 av1 av2 av3 s0 s1 s2 s3
  have hs := exact_id x0 x1 x2 l0 u1
  exact lz_aff2 (w0 := 1) (w1 := 1) (w2 := 1/2) (by rw [hs]; ring)
    (by norm_num) (by norm_num) (hw 2 0 0) (hw 2 0 1) (hb 2 0) av4 av5 q0 q1

theorem net_robust : StatementRobust net := by
  intro dW db hW x0 x1 x2 l0 u0 l1 u1 l2 u2
  obtain ⟨hw, hb⟩ := hW
  refine ⟨Yv dW db x0 x1 x2, ?_, key dW db hw hb x0 x1 x2 l0 u0 l1 u1 l2 u2⟩
  simp [net, Net.evalP, hiddenP, rowsP, dotP, Yv, Q0, Q1, R0, R1, R2, R3]
  try ring_nf

end Lane4.Case
