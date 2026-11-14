namespace Lane4.Case
open Lane4

def net : Net :=
  { hidden :=
      [ { W := [[2/5, 0, -2/5], [0, 4/5, 0], [1, -1/2, 0], [-7/10, 7/20, 0]],
          b := [-1, -1, 1, -7/10] },
        { W := [[10, -10, 0, 0], [35/4, 0, 0, 0], [0, 5/2, 0, 0], [0, 0, 5/2, 25/7]],
          b := [0, 0, 0, 0] },
        { W := [[3/4, -6/7, 0, 6/5], [-3/4, 0, -3, 6/5], [-1, 8/7, 0, 0]],
          b := [0, 0, 0] } ],
    out := { W := [[1/3, -1/3, 1/4]], b := [0] } }

noncomputable def nu1 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu ((2/5 + dW 0 0 0) * x0 + ((0 + dW 0 0 1) * x1 + (-2/5 + dW 0 0 2) * x2) + (-1 + db 0 0))
noncomputable def nu2 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu ((0 + dW 0 1 0) * x0 + ((4/5 + dW 0 1 1) * x1 + (0 + dW 0 1 2) * x2) + (-1 + db 0 1))
noncomputable def nu3 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu ((1 + dW 0 2 0) * x0 + ((-1/2 + dW 0 2 1) * x1 + (0 + dW 0 2 2) * x2) + (1 + db 0 2))
noncomputable def nu4 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu ((-7/10 + dW 0 3 0) * x0 + ((7/20 + dW 0 3 1) * x1 + (0 + dW 0 3 2) * x2) + (-7/10 + db 0 3))

noncomputable def nu5 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (v1 v2 v3 v4 : ℝ) : ℝ :=
  relu ((10 + dW 1 0 0) * v1 + ((-10 + dW 1 0 1) * v2 + ((0 + dW 1 0 2) * v3 + (0 + dW 1 0 3) * v4)) + (0 + db 1 0))
noncomputable def nu6 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (v1 v2 v3 v4 : ℝ) : ℝ :=
  relu ((35/4 + dW 1 1 0) * v1 + ((0 + dW 1 1 1) * v2 + ((0 + dW 1 1 2) * v3 + (0 + dW 1 1 3) * v4)) + (0 + db 1 1))
noncomputable def nu7 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (v1 v2 v3 v4 : ℝ) : ℝ :=
  relu ((0 + dW 1 2 0) * v1 + ((5/2 + dW 1 2 1) * v2 + ((0 + dW 1 2 2) * v3 + (0 + dW 1 2 3) * v4)) + (0 + db 1 2))
noncomputable def nu8 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (v1 v2 v3 v4 : ℝ) : ℝ :=
  relu ((0 + dW 1 3 0) * v1 + ((0 + dW 1 3 1) * v2 + ((5/2 + dW 1 3 2) * v3 + (25/7 + dW 1 3 3) * v4)) + (0 + db 1 3))

noncomputable def nu9 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (v5 v6 v7 v8 : ℝ) : ℝ :=
  relu ((3/4 + dW 2 0 0) * v5 + ((-6/7 + dW 2 0 1) * v6 + ((0 + dW 2 0 2) * v7 + (6/5 + dW 2 0 3) * v8)) + (0 + db 2 0))
noncomputable def nu10 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (v5 v6 v7 v8 : ℝ) : ℝ :=
  relu ((-3/4 + dW 2 1 0) * v5 + ((0 + dW 2 1 1) * v6 + ((-3 + dW 2 1 2) * v7 + (6/5 + dW 2 1 3) * v8)) + (0 + db 2 1))
noncomputable def nu11 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (v5 v6 v7 v8 : ℝ) : ℝ :=
  relu ((-1 + dW 2 2 0) * v5 + ((8/7 + dW 2 2 1) * v6 + ((0 + dW 2 2 2) * v7 + (0 + dW 2 2 3) * v8)) + (0 + db 2 2))

noncomputable def nuo (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (v9 v10 v11 : ℝ) : ℝ :=
  (1/3 + dW 3 0 0) * v9 + ((-1/3 + dW 3 0 1) * v10 + (1/4 + dW 3 0 2) * v11) + (0 + db 3 0)

noncomputable def Yout (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  let v1 := nu1 dW db x0 x1 x2
  let v2 := nu2 dW db x0 x1 x2
  let v3 := nu3 dW db x0 x1 x2
  let v4 := nu4 dW db x0 x1 x2
  let v5 := nu5 dW db v1 v2 v3 v4
  let v6 := nu6 dW db v1 v2 v3 v4
  let v7 := nu7 dW db v1 v2 v3 v4
  let v8 := nu8 dW db v1 v2 v3 v4
  nuo dW db (nu9 dW db v5 v6 v7 v8) (nu10 dW db v5 v6 v7 v8) (nu11 dW db v5 v6 v7 v8)

theorem eval_eq (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) :
    Net.evalP net dW db [x0, x1, x2] = [Yout dW db x0 x1 x2] := by
  simp [net, Net.evalP, hiddenP, rowsP, dotP, Yout, nuo, nu1, nu2, nu3, nu4, nu5, nu6, nu7,
    nu8, nu9, nu10, nu11] <;> try ring_nf

theorem w_relu_mul {c z : ℝ} (hc : 0 ≤ c) : relu (c * z) = c * relu z := by
  unfold relu
  rcases le_total z 0 with h | h
  · have h1 : c * z ≤ 0 := by nlinarith
    rw [max_eq_right h, max_eq_right h1] <;> ring
  · have h1 : 0 ≤ c * z := mul_nonneg hc h
    rw [max_eq_left h, max_eq_left h1]

theorem w_relu_dev {pre z c k η e : ℝ} (hc : 0 < c) (hk : c * k = 1) (hk0 : 0 < k)
    (h : pre = c * z + η) (he : |η| ≤ e) : |k * relu pre - relu z| ≤ k * e := by
  have h1 : relu (c * z) = c * relu z := w_relu_mul hc.le
  have h2 : |relu pre - c * relu z| ≤ e := by
    rw [← h1]
    refine le_trans (relu_sub_le _ _) ?_
    rw [h]
    have h3 : c * z + η - c * z = η := by ring
    rw [h3]
    exact he
  have h3 : k * relu pre - relu z = k * (relu pre - c * relu z) := by
    linear_combination (relu z) * hk
  rw [h3, abs_mul, abs_of_pos hk0]
  exact mul_le_mul_of_nonneg_left h2 hk0.le

theorem w_dev3 {d0 d1 d2 db v0 v1 v2 B0 B1 B2 : ℝ}
    (h0 : |d0| ≤ 1/1000) (h1 : |d1| ≤ 1/1000) (h2 : |d2| ≤ 1/1000) (hb : |db| ≤ 1/1000)
    (b0 : |v0| ≤ B0) (b1 : |v1| ≤ B1) (b2 : |v2| ≤ B2) :
    |d0 * v0 + d1 * v1 + d2 * v2 + db| ≤ (B0 + B1 + B2 + 1) / 1000 := by
  have t := abs_add3_le (pert_abs_mul h0 b0) (pert_abs_mul h1 b1) (pert_abs_mul h2 b2)
  have t2 := abs_add_le (d0 * v0 + d1 * v1 + d2 * v2) db
  linarith

theorem w_dev4 {d0 d1 d2 d3 db v0 v1 v2 v3 B0 B1 B2 B3 : ℝ}
    (h0 : |d0| ≤ 1/1000) (h1 : |d1| ≤ 1/1000) (h2 : |d2| ≤ 1/1000) (h3 : |d3| ≤ 1/1000)
    (hb : |db| ≤ 1/1000)
    (b0 : |v0| ≤ B0) (b1 : |v1| ≤ B1) (b2 : |v2| ≤ B2) (b3 : |v3| ≤ B3) :
    |d0 * v0 + d1 * v1 + d2 * v2 + d3 * v3 + db| ≤ (B0 + B1 + B2 + B3 + 1) / 1000 := by
  have t := abs_add3_le (pert_abs_mul h0 b0) (pert_abs_mul h1 b1) (pert_abs_mul h2 b2)
  have t2 := abs_add_le (d0 * v0 + d1 * v1 + d2 * v2) (d3 * v3)
  have t3 := abs_add_le (d0 * v0 + d1 * v1 + d2 * v2 + d3 * v3) db
  have t4 := pert_abs_mul h3 b3
  linarith

theorem w_lipmin {A B a b M : ℝ} (hA : |A - a| ≤ M) (hB : |B - b| ≤ M) :
    |min A B - min a b| ≤ M := by
  obtain ⟨hA1, hA2⟩ := abs_le.mp hA
  obtain ⟨hB1, hB2⟩ := abs_le.mp hB
  rw [abs_le]
  simp only [min_def]
  constructor <;> split_ifs <;> linarith

theorem w_lipmax {A B a b M : ℝ} (hA : |A - a| ≤ M) (hB : |B - b| ≤ M) :
    |max A B - max a b| ≤ M := by
  obtain ⟨hA1, hA2⟩ := abs_le.mp hA
  obtain ⟨hB1, hB2⟩ := abs_le.mp hB
  rw [abs_le]
  simp only [max_def]
  constructor <;> split_ifs <;> linarith

theorem w_med_lip {A B C a b c M : ℝ} (hA : |A - a| ≤ M) (hB : |B - b| ≤ M) (hC : |C - c| ≤ M) :
    |max (min A B) (min (max A B) C) - max (min a b) (min (max a b) c)| ≤ M :=
  w_lipmax (w_lipmin hA hB) (w_lipmin (w_lipmax hA hB) hC)

theorem w_med_relu {a c : ℝ} (b : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    max (min a (relu b)) (min (max a (relu b)) c) = max (min a b) (min (max a b) c) := by
  rcases le_total b 0 with hb | hb
  · rw [relu_of_nonpos hb]
    simp only [max_def, min_def]
    split_ifs <;> linarith
  · rw [relu_of_nonneg hb]

theorem w_F_eq {A B : ℝ} (C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    relu (A - relu (A - B)) + relu (C - A + relu (A - B)) - relu (C - B - relu (A - B))
      = max (min A B) (min (max A B) C) := by
  rcases le_total A B with h | h
  · rw [relu_of_nonpos (by linarith : A - B ≤ 0)]
    simp only [relu, max_def, min_def]
    split_ifs <;> linarith
  · rw [relu_of_nonneg (by linarith : 0 ≤ A - B)]
    simp only [relu, max_def, min_def]
    split_ifs <;> linarith

theorem w_core {A B C D' A2 B2 C2 T1 T2 LO Y dd da db dc d1 d2 dl dO : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hd : |D' - relu (A - B)| ≤ dd) (ha : |A2 - relu A| ≤ da) (hb : |B2 - relu B| ≤ db)
    (hc : |C2 - relu C| ≤ dc)
    (h1 : |T1 - relu (C2 - A2 + D')| ≤ d1) (h2 : |T2 - relu (C2 - B2 - D')| ≤ d2)
    (h3 : |LO - relu (A2 - D')| ≤ dl) (hy : |Y - (LO + T1 - T2)| ≤ dO) :
    |Y - max (min A B) (min (max A B) C)|
      ≤ dO + d1 + d2 + dl + 2 * da + 2 * dc + db + 3 * dd := by
  rw [← w_F_eq C hA hB]
  have rA : relu A = A := relu_of_nonneg hA
  have rB : relu B = B := relu_of_nonneg hB
  have rC : relu C = C := relu_of_nonneg hC
  rw [rA] at ha
  rw [rB] at hb
  rw [rC] at hc
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  obtain ⟨hd1, hd2⟩ := abs_le.mp hd
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  have hdA : relu (A - B) ≤ A := relu_le_of_le (by linarith) hA
  have hd0 : 0 ≤ relu (A - B) := relu_nonneg' _
  have rl : relu (A - relu (A - B)) = A - relu (A - B) := relu_of_nonneg (by linarith)
  have s1 : |relu (C2 - A2 + D') - relu (C - A + relu (A - B))| ≤ dc + da + dd := by
    refine le_trans (relu_sub_le _ _) ?_
    rw [abs_le]
    constructor <;> linarith
  have s2 : |relu (C2 - B2 - D') - relu (C - B - relu (A - B))| ≤ dc + db + dd := by
    refine le_trans (relu_sub_le _ _) ?_
    rw [abs_le]
    constructor <;> linarith
  have s3 : |relu (A2 - D') - relu (A - relu (A - B))| ≤ da + dd := by
    refine le_trans (relu_sub_le _ _) ?_
    rw [abs_le]
    constructor <;> linarith
  have t1 := le_trans (abs_sub_le T1 (relu (C2 - A2 + D')) (relu (C - A + relu (A - B))))
    (add_le_add h1 s1)
  have t2 := le_trans (abs_sub_le T2 (relu (C2 - B2 - D')) (relu (C - B - relu (A - B))))
    (add_le_add h2 s2)
  have t3 := le_trans (abs_sub_le LO (relu (A2 - D')) (relu (A - relu (A - B))))
    (add_le_add h3 s3)
  obtain ⟨t11, t12⟩ := abs_le.mp t1
  obtain ⟨t21, t22⟩ := abs_le.mp t2
  obtain ⟨t31, t32⟩ := abs_le.mp t3
  rw [abs_le]
  constructor <;> linarith

set_option maxHeartbeats 4000000 in
theorem key (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ)
    (hw : ∀ l i j, |dW l i j| ≤ 1/1000) (hb : ∀ l i, |db l i| ≤ 1/1000)
    (l0 : -2 ≤ x0) (m0 : x0 ≤ 1) (l1 : -2 ≤ x1) (m1 : x1 ≤ 8) (l2 : -4 ≤ x2) (m2 : x2 ≤ 4)
    (V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 y : ℝ)
    (h1 : V1 = nu1 dW db x0 x1 x2) (h2 : V2 = nu2 dW db x0 x1 x2)
    (h3 : V3 = nu3 dW db x0 x1 x2) (h4 : V4 = nu4 dW db x0 x1 x2)
    (h5 : V5 = nu5 dW db V1 V2 V3 V4) (h6 : V6 = nu6 dW db V1 V2 V3 V4)
    (h7 : V7 = nu7 dW db V1 V2 V3 V4) (h8 : V8 = nu8 dW db V1 V2 V3 V4)
    (h9 : V9 = nu9 dW db V5 V6 V7 V8) (h10 : V10 = nu10 dW db V5 V6 V7 V8)
    (h11 : V11 = nu11 dW db V5 V6 V7 V8) (hy : y = nuo dW db V9 V10 V11) :
    |y - spec x0 x1 x2| ≤ 1/4 := by
  unfold nu1 at h1
  unfold nu2 at h2
  unfold nu3 at h3
  unfold nu4 at h4
  unfold nu5 at h5
  unfold nu6 at h6
  unfold nu7 at h7
  unfold nu8 at h8
  unfold nu9 at h9
  unfold nu10 at h10
  unfold nu11 at h11
  unfold nuo at hy
  have hx0 : |x0| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hx1 : |x1| ≤ 8 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hx2 : |x2| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  have e1 := w_dev3 (hw 0 0 0) (hw 0 0 1) (hw 0 0 2) (hb 0 0) hx0 hx1 hx2
  have e2 := w_dev3 (hw 0 1 0) (hw 0 1 1) (hw 0 1 2) (hb 0 1) hx0 hx1 hx2
  have e3 := w_dev3 (hw 0 2 0) (hw 0 2 1) (hw 0 2 2) (hb 0 2) hx0 hx1 hx2
  have e4 := w_dev3 (hw 0 3 0) (hw 0 3 1) (hw 0 3 2) (hb 0 3) hx0 hx1 hx2
  have q1 : |(5/2) * V1 - relu (x0 + (-1) * x2 + (-5/2))| ≤ (5/2) * (3/200) := by
    rw [h1]
    exact le_trans (w_relu_dev (c := 2/5) (by norm_num) (by norm_num) (by norm_num) (by ring) e1)
      (by norm_num)
  have q2 : |(5/2) * V2 - relu (2 * x1 + (-5/2))| ≤ (5/2) * (3/200) := by
    rw [h2]
    exact le_trans (w_relu_dev (c := 2/5) (by norm_num) (by norm_num) (by norm_num) (by ring) e2)
      (by norm_num)
  have q3 : |1 * V3 - relu (x0 + (-1/2) * x1 + 1)| ≤ 1 * (3/200) := by
    rw [h3]
    exact le_trans (w_relu_dev (c := 1) (by norm_num) (by norm_num) (by norm_num) (by ring) e3)
      (by norm_num)
  have q4 : |(10/7) * V4 - relu (-(x0 + (-1/2) * x1 + 1))| ≤ (10/7) * (3/200) := by
    rw [h4]
    exact le_trans (w_relu_dev (c := 7/10) (by norm_num) (by norm_num) (by norm_num) (by ring) e4)
      (by norm_num)
  obtain ⟨q1a, q1b⟩ := abs_le.mp q1
  obtain ⟨q2a, q2b⟩ := abs_le.mp q2
  obtain ⟨q3a, q3b⟩ := abs_le.mp q3
  obtain ⟨q4a, q4b⟩ := abs_le.mp q4
  have n1 : 0 ≤ V1 := by rw [h1]; exact relu_nonneg' _
  have n2 : 0 ≤ V2 := by rw [h2]; exact relu_nonneg' _
  have n3 : 0 ≤ V3 := by rw [h3]; exact relu_nonneg' _
  have n4 : 0 ≤ V4 := by rw [h4]; exact relu_nonneg' _
  have ru : relu (x0 + (-1) * x2 + (-5/2)) ≤ 5/2 := relu_le_of_le (by linarith) (by norm_num)
  have rb : relu (2 * x1 + (-5/2)) ≤ 27/2 := relu_le_of_le (by linarith) (by norm_num)
  have rv : relu (x0 + (-1/2) * x1 + 1) ≤ 3 := relu_le_of_le (by linarith) (by norm_num)
  have rn : relu (-(x0 + (-1/2) * x1 + 1)) ≤ 5 := relu_le_of_le (by linarith) (by norm_num)
  have hv : relu (x0 + (-1/2) * x1 + 1) + relu (-(x0 + (-1/2) * x1 + 1))
      = |x0 + (-1/2) * x1 + 1| := relu_add_relu_neg _
  have habs : |x0 + (-1/2) * x1 + 1| ≤ 5 := abs_le.mpr ⟨by linarith, by linarith⟩
  have aV1 : |V1| ≤ 21/20 := abs_le.mpr ⟨by linarith, by linarith⟩
  have aV2 : |V2| ≤ 11/2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have aV3 : |V3| ≤ 31/10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have aV4 : |V4| ≤ 18/5 := abs_le.mpr ⟨by linarith, by linarith⟩
  have f1 := w_dev4 (hw 1 0 0) (hw 1 0 1) (hw 1 0 2) (hw 1 0 3) (hb 1 0) aV1 aV2 aV3 aV4
  have f2 := w_dev4 (hw 1 1 0) (hw 1 1 1) (hw 1 1 2) (hw 1 1 3) (hb 1 1) aV1 aV2 aV3 aV4
  have f3 := w_dev4 (hw 1 2 0) (hw 1 2 1) (hw 1 2 2) (hw 1 2 3) (hb 1 2) aV1 aV2 aV3 aV4
  have f4 := w_dev4 (hw 1 3 0) (hw 1 3 1) (hw 1 3 2) (hw 1 3 3) (hb 1 3) aV1 aV2 aV3 aV4
  have q5 : |(1/4) * V5 - relu ((5/2) * V1 - (5/2) * V2)| ≤ (1/4) * (57/4000) := by
    rw [h5]
    exact le_trans (w_relu_dev (c := 4) (by norm_num) (by norm_num) (by norm_num) (by ring) f1)
      (by norm_num)
  have q6 : |(2/7) * V6 - relu ((5/2) * V1)| ≤ (2/7) * (57/4000) := by
    rw [h6]
    exact le_trans (w_relu_dev (c := 7/2) (by norm_num) (by norm_num) (by norm_num) (by ring) f2)
      (by norm_num)
  have q7 : |1 * V7 - relu ((5/2) * V2)| ≤ 1 * (57/4000) := by
    rw [h7]
    exact le_trans (w_relu_dev (c := 1) (by norm_num) (by norm_num) (by norm_num) (by ring) f3)
      (by norm_num)
  have q8 : |(2/5) * V8 - relu (V3 + (10/7) * V4)| ≤ (2/5) * (57/4000) := by
    rw [h8]
    exact le_trans (w_relu_dev (c := 5/2) (by norm_num) (by norm_num) (by norm_num) (by ring) f4)
      (by norm_num)
  obtain ⟨q5a, q5b⟩ := abs_le.mp q5
  obtain ⟨q6a, q6b⟩ := abs_le.mp q6
  obtain ⟨q7a, q7b⟩ := abs_le.mp q7
  obtain ⟨q8a, q8b⟩ := abs_le.mp q8
  have n5 : 0 ≤ V5 := by rw [h5]; exact relu_nonneg' _
  have n6 : 0 ≤ V6 := by rw [h6]; exact relu_nonneg' _
  have n7 : 0 ≤ V7 := by rw [h7]; exact relu_nonneg' _
  have n8 : 0 ≤ V8 := by rw [h8]; exact relu_nonneg' _
  have rA : relu ((5/2) * V1) = (5/2) * V1 := relu_of_nonneg (by linarith)
  have rB : relu ((5/2) * V2) = (5/2) * V2 := relu_of_nonneg (by linarith)
  have rC : relu (V3 + (10/7) * V4) = V3 + (10/7) * V4 := relu_of_nonneg (by linarith)
  have rAB : relu ((5/2) * V1 - (5/2) * V2) ≤ (5/2) * V1 :=
    relu_le_of_le (by linarith) (by linarith)
  have hC5 : V3 + (10/7) * V4 ≤ 126/25 := by linarith
  have aV5 : |V5| ≤ 11 := abs_le.mpr ⟨by linarith, by linarith⟩
  have aV6 : |V6| ≤ 9 := abs_le.mpr ⟨by linarith, by linarith⟩
  have aV7 : |V7| ≤ 14 := abs_le.mpr ⟨by linarith, by linarith⟩
  have aV8 : |V8| ≤ 13 := abs_le.mpr ⟨by linarith, by linarith⟩
  have g1 := w_dev4 (hw 2 0 0) (hw 2 0 1) (hw 2 0 2) (hw 2 0 3) (hb 2 0) aV5 aV6 aV7 aV8
  have g2 := w_dev4 (hw 2 1 0) (hw 2 1 1) (hw 2 1 2) (hw 2 1 3) (hb 2 1) aV5 aV6 aV7 aV8
  have g3 := w_dev4 (hw 2 2 0) (hw 2 2 1) (hw 2 2 2) (hw 2 2 3) (hb 2 2) aV5 aV6 aV7 aV8
  have q9 : |(1/3) * V9 - relu ((2/5) * V8 - (2/7) * V6 + (1/4) * V5)| ≤ (1/3) * (6/125) := by
    rw [h9]
    exact le_trans (w_relu_dev (c := 3) (by norm_num) (by norm_num) (by norm_num) (by ring) g1)
      (by norm_num)
  have q10 : |(1/3) * V10 - relu ((2/5) * V8 - 1 * V7 - (1/4) * V5)| ≤ (1/3) * (6/125) := by
    rw [h10]
    exact le_trans (w_relu_dev (c := 3) (by norm_num) (by norm_num) (by norm_num) (by ring) g2)
      (by norm_num)
  have q11 : |(1/4) * V11 - relu ((2/7) * V6 - (1/4) * V5)| ≤ (1/4) * (6/125) := by
    rw [h11]
    exact le_trans (w_relu_dev (c := 4) (by norm_num) (by norm_num) (by norm_num) (by ring) g3)
      (by norm_num)
  obtain ⟨q9a, q9b⟩ := abs_le.mp q9
  obtain ⟨q10a, q10b⟩ := abs_le.mp q10
  obtain ⟨q11a, q11b⟩ := abs_le.mp q11
  have n9 : 0 ≤ V9 := by rw [h9]; exact relu_nonneg' _
  have n10 : 0 ≤ V10 := by rw [h10]; exact relu_nonneg' _
  have n11 : 0 ≤ V11 := by rw [h11]; exact relu_nonneg' _
  have rz9 : relu ((2/5) * V8 - (2/7) * V6 + (1/4) * V5) ≤ 51/10 :=
    relu_le_of_le (by linarith) (by norm_num)
  have rz10 : relu ((2/5) * V8 - 1 * V7 - (1/4) * V5) ≤ 51/10 :=
    relu_le_of_le (by linarith) (by norm_num)
  have rz11 : relu ((2/7) * V6 - (1/4) * V5) ≤ 13/5 :=
    relu_le_of_le (by linarith) (by norm_num)
  have aV9 : |V9| ≤ 16 := abs_le.mpr ⟨by linarith, by linarith⟩
  have aV10 : |V10| ≤ 16 := abs_le.mpr ⟨by linarith, by linarith⟩
  have aV11 : |V11| ≤ 11 := abs_le.mpr ⟨by linarith, by linarith⟩
  have k1 := w_dev3 (hw 3 0 0) (hw 3 0 1) (hw 3 0 2) (hb 3 0) aV9 aV10 aV11
  have hyb : |y - ((1/4) * V11 + (1/3) * V9 - (1/3) * V10)| ≤ 11/250 := by
    have h : y - ((1/4) * V11 + (1/3) * V9 - (1/3) * V10)
        = dW 3 0 0 * V9 + dW 3 0 1 * V10 + dW 3 0 2 * V11 + db 3 0 := by
      rw [hy]; ring
    rw [h]
    exact le_trans k1 (by norm_num)
  have hcore := w_core (A := (5/2) * V1) (B := (5/2) * V2) (C := V3 + (10/7) * V4)
    (D' := (1/4) * V5) (A2 := (2/7) * V6) (B2 := 1 * V7) (C2 := (2/5) * V8)
    (T1 := (1/3) * V9) (T2 := (1/3) * V10) (LO := (1/4) * V11) (Y := y)
    (by linarith) (by linarith) (by linarith) q5 q6 q7 q8 q9 q10 q11 hyb
  have hA' : |(5/2) * V1 - relu (x0 + (-1) * x2 + (-5/2))| ≤ 3/80 :=
    le_trans q1 (by norm_num)
  have hB' : |(5/2) * V2 - relu (2 * x1 + (-5/2))| ≤ 3/80 :=
    le_trans q2 (by norm_num)
  have hC' : |(V3 + (10/7) * V4) - (|x0 + (-1/2) * x1 + 1|)| ≤ 3/80 := by
    rw [abs_le]
    constructor <;> linarith
  have hl := w_med_lip hA' hB' hC'
  have hspec : spec x0 x1 x2
      = max (min (relu (x0 + (-1) * x2 + (-5/2))) (relu (2 * x1 + (-5/2))))
          (min (max (relu (x0 + (-1) * x2 + (-5/2))) (relu (2 * x1 + (-5/2))))
            (|x0 + (-1/2) * x1 + 1|)) := by
    rw [w_med_relu _ (relu_nonneg' _) (abs_nonneg _)] <;> rfl
  rw [hspec]
  have hs := add_le_add hcore hl
  exact le_trans (abs_sub_le y _ _) (le_trans hs (by norm_num))

theorem net_robust : StatementRobust net := by
  intro dW db hW x0 x1 x2 l0 m0 l1 m1 l2 m2
  obtain ⟨hw, hb⟩ := hW
  refine ⟨Yout dW db x0 x1 x2, eval_eq dW db x0 x1 x2, ?_⟩
  exact key dW db x0 x1 x2 hw hb l0 m0 l1 m1 l2 m2 _ _ _ _ _ _ _ _ _ _ _ _
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

end Lane4.Case
