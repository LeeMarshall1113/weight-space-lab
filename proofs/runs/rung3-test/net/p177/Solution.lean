namespace Lane4.Case
open Lane4

def net : Net :=
  { hidden := [
      { W := [[(-1), 0, 3], [(1/2), 2, (1/2)], [0, 0, 3], [0, 0, (-1)], [0, 0, (-2)]],
        b := [(-1), (3/2), 6, 5, 9] },
      { W := [[(-2), 0, 2, 0, 0], [0, 2, 0, 1, 0], [0, (-4), 0, (-2), 0], [0, 0, 0, 0, 2]],
        b := [(-8), (-10), 20, 0] },
      { W := [[0, (3/2), (3/4), 0], [(-3/4), (3/2), (3/4), (-3/4)]],
        b := [1, 15] }],
    out := { W := [[(1/3), (-1/3)]], b := [(-1/4)] } }

noncomputable def A2 (a1 a2 c : ℚ) (d1 d2 dc v1 v2 : ℝ) : ℝ :=
  (((a1:ℝ) + d1) * v1 + (((a2:ℝ) + d2) * v2 + 0)) + ((c:ℝ) + dc)
noncomputable def A3 (a1 a2 a3 c : ℚ) (d1 d2 d3 dc v1 v2 v3 : ℝ) : ℝ :=
  (((a1:ℝ) + d1) * v1 + (((a2:ℝ) + d2) * v2 + (((a3:ℝ) + d3) * v3 + 0))) + ((c:ℝ) + dc)
noncomputable def A4 (a1 a2 a3 a4 c : ℚ) (d1 d2 d3 d4 dc v1 v2 v3 v4 : ℝ) : ℝ :=
  (((a1:ℝ) + d1) * v1 + (((a2:ℝ) + d2) * v2 + (((a3:ℝ) + d3) * v3 + (((a4:ℝ) + d4) * v4 + 0)))) + ((c:ℝ) + dc)
noncomputable def A5 (a1 a2 a3 a4 a5 c : ℚ) (d1 d2 d3 d4 d5 dc v1 v2 v3 v4 v5 : ℝ) : ℝ :=
  (((a1:ℝ) + d1) * v1 + (((a2:ℝ) + d2) * v2 + (((a3:ℝ) + d3) * v3 + (((a4:ℝ) + d4) * v4 + (((a5:ℝ) + d5) * v5 + 0))))) + ((c:ℝ) + dc)

noncomputable def m11 (x0 x1 x2 : ℝ) : ℝ := relu ((-1/2) * x0 + (3/2) * x2 + (-1/2))
noncomputable def m12 (x0 x1 x2 : ℝ) : ℝ := relu ((1/2) * x0 + 2 * x1 + (1/2) * x2 + (3/2))
noncomputable def m13 (x0 x1 x2 : ℝ) : ℝ := relu ((3/2) * x2 + 3)
noncomputable def m14 (x0 x1 x2 : ℝ) : ℝ := relu ((-1/2) * x2 + (5/2))
noncomputable def m15 (x0 x1 x2 : ℝ) : ℝ := relu ((-1) * x2 + (9/2))
noncomputable def m21 (x0 x1 x2 : ℝ) : ℝ := relu (m13 x0 x1 x2 - m11 x0 x1 x2 - 2)
noncomputable def m22 (x0 x1 x2 : ℝ) : ℝ := relu (m14 x0 x1 x2 + m12 x0 x1 x2 - 5)
noncomputable def m23 (x0 x1 x2 : ℝ) : ℝ := relu (5 - m14 x0 x1 x2 - m12 x0 x1 x2)
noncomputable def m24 (x0 x1 x2 : ℝ) : ℝ := relu (m15 x0 x1 x2)
noncomputable def m32 (x0 x1 x2 : ℝ) : ℝ := relu (m22 x0 x1 x2 + m23 x0 x1 x2 - m24 x0 x1 x2 + 5 - m21 x0 x1 x2)

noncomputable def P11 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu (A3 (-1) 0 3 (-1) (dW 0 0 0) (dW 0 0 1) (dW 0 0 2) (db 0 0) x0 x1 x2)
noncomputable def P12 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu (A3 (1/2) 2 (1/2) (3/2) (dW 0 1 0) (dW 0 1 1) (dW 0 1 2) (db 0 1) x0 x1 x2)
noncomputable def P13 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu (A3 0 0 3 6 (dW 0 2 0) (dW 0 2 1) (dW 0 2 2) (db 0 2) x0 x1 x2)
noncomputable def P14 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu (A3 0 0 (-1) 5 (dW 0 3 0) (dW 0 3 1) (dW 0 3 2) (db 0 3) x0 x1 x2)
noncomputable def P15 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu (A3 0 0 (-2) 9 (dW 0 4 0) (dW 0 4 1) (dW 0 4 2) (db 0 4) x0 x1 x2)
noncomputable def P21 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu (A5 (-2) 0 2 0 0 (-8) (dW 1 0 0) (dW 1 0 1) (dW 1 0 2) (dW 1 0 3) (dW 1 0 4) (db 1 0) (P11 dW db x0 x1 x2) (P12 dW db x0 x1 x2) (P13 dW db x0 x1 x2) (P14 dW db x0 x1 x2) (P15 dW db x0 x1 x2))
noncomputable def P22 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu (A5 0 2 0 1 0 (-10) (dW 1 1 0) (dW 1 1 1) (dW 1 1 2) (dW 1 1 3) (dW 1 1 4) (db 1 1) (P11 dW db x0 x1 x2) (P12 dW db x0 x1 x2) (P13 dW db x0 x1 x2) (P14 dW db x0 x1 x2) (P15 dW db x0 x1 x2))
noncomputable def P23 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu (A5 0 (-4) 0 (-2) 0 20 (dW 1 2 0) (dW 1 2 1) (dW 1 2 2) (dW 1 2 3) (dW 1 2 4) (db 1 2) (P11 dW db x0 x1 x2) (P12 dW db x0 x1 x2) (P13 dW db x0 x1 x2) (P14 dW db x0 x1 x2) (P15 dW db x0 x1 x2))
noncomputable def P24 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  relu (A5 0 0 0 0 2 0 (dW 1 3 0) (dW 1 3 1) (dW 1 3 2) (dW 1 3 3) (dW 1 3 4) (db 1 3) (P11 dW db x0 x1 x2) (P12 dW db x0 x1 x2) (P13 dW db x0 x1 x2) (P14 dW db x0 x1 x2) (P15 dW db x0 x1 x2))
noncomputable def PP (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  A4 0 (3/2) (3/4) 0 1 (dW 2 0 0) (dW 2 0 1) (dW 2 0 2) (dW 2 0 3) (db 2 0) (P21 dW db x0 x1 x2) (P22 dW db x0 x1 x2) (P23 dW db x0 x1 x2) (P24 dW db x0 x1 x2)
noncomputable def ZZ (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) : ℝ :=
  A4 (-3/4) (3/2) (3/4) (-3/4) 15 (dW 2 1 0) (dW 2 1 1) (dW 2 1 2) (dW 2 1 3) (db 2 1) (P21 dW db x0 x1 x2) (P22 dW db x0 x1 x2) (P23 dW db x0 x1 x2) (P24 dW db x0 x1 x2)

theorem aas {X t B b : ℝ} (hX : |X| ≤ B) (ht : |t| ≤ b) : |X + t| ≤ B + b :=
  le_trans (abs_add_le _ _) (add_le_add hX ht)

theorem abs_diff2 {a b τ : ℝ} (ha : |a| ≤ τ) (hb : |b| ≤ τ) : |a - b| ≤ 2 * τ := by
  obtain ⟨h1, h2⟩ := abs_le.mp ha
  obtain ⟨h3, h4⟩ := abs_le.mp hb
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem my_min_lip {a b c d M : ℝ} (h1 : |a - c| ≤ M) (h2 : |b - d| ≤ M) :
    |min a b - min c d| ≤ M := by
  obtain ⟨h1l, h1r⟩ := abs_le.mp h1
  obtain ⟨h2l, h2r⟩ := abs_le.mp h2
  rcases le_total a b with h | h <;> rcases le_total c d with h' | h'
  · rw [min_eq_left h, min_eq_left h']; exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [min_eq_left h, min_eq_right h']; exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [min_eq_right h, min_eq_left h']; exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [min_eq_right h, min_eq_right h']; exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem relu_scale_eq {s t : ℝ} (hs : 0 ≤ s) : s * relu t = relu (s * t) := by
  unfold relu
  rw [mul_max_of_nonneg _ _ hs]
  simp

theorem P3 {a1 a2 a3 c : ℚ} {d1 d2 d3 dc w1 w2 w3 v1 v2 v3 τ α1 α2 α3 e1 e2 e3 B1 B2 B3 X : ℝ}
    (ha1 : |(a1:ℝ)| ≤ α1)
    (ha2 : |(a2:ℝ)| ≤ α2)
    (ha3 : |(a3:ℝ)| ≤ α3)
    (hd1 : |d1| ≤ τ)
    (hd2 : |d2| ≤ τ)
    (hd3 : |d3| ≤ τ)
    (hdc : |dc| ≤ τ)
    (hv1 : |w1 - v1| ≤ e1)
    (hv2 : |w2 - v2| ≤ e2)
    (hv3 : |w3 - v3| ≤ e3)
    (hB1 : |v1| ≤ B1)
    (hB2 : |v2| ≤ B2)
    (hB3 : |v3| ≤ B3)
    (hx : (a1:ℝ) * v1 + (a2:ℝ) * v2 + (a3:ℝ) * v3 + (c:ℝ) = X) :
    |A3 a1 a2 a3 c d1 d2 d3 dc w1 w2 w3 - X| ≤ (α1 * e1 + τ * (B1 + e1)) + (α2 * e2 + τ * (B2 + e2)) + (α3 * e3 + τ * (B3 + e3)) + τ := by
  subst hx
  have k1 : |((a1:ℝ) + d1) * w1 - a1 * v1| ≤ α1 * e1 + τ * (B1 + e1) := by
    have h1 := pert_mul (a := (a1:ℝ)) hd1 hv1 hB1
    have h2 := mul_le_mul_of_nonneg_right ha1 (le_trans (abs_nonneg _) hv1)
    linarith
  have k2 : |((a2:ℝ) + d2) * w2 - a2 * v2| ≤ α2 * e2 + τ * (B2 + e2) := by
    have h1 := pert_mul (a := (a2:ℝ)) hd2 hv2 hB2
    have h2 := mul_le_mul_of_nonneg_right ha2 (le_trans (abs_nonneg _) hv2)
    linarith
  have k3 : |((a3:ℝ) + d3) * w3 - a3 * v3| ≤ α3 * e3 + τ * (B3 + e3) := by
    have h1 := pert_mul (a := (a3:ℝ)) hd3 hv3 hB3
    have h2 := mul_le_mul_of_nonneg_right ha3 (le_trans (abs_nonneg _) hv3)
    linarith
  have heq : A3 a1 a2 a3 c d1 d2 d3 dc w1 w2 w3 - ((a1:ℝ) * v1 + (a2:ℝ) * v2 + (a3:ℝ) * v3 + (c:ℝ)) = (((a1:ℝ) + d1) * w1 - a1 * v1) + (((a2:ℝ) + d2) * w2 - a2 * v2) + (((a3:ℝ) + d3) * w3 - a3 * v3) + dc := by
    unfold A3; ring
  rw [heq]
  exact aas (abs_add3_le k1 k2 k3) hdc

theorem P4 {a1 a2 a3 a4 c : ℚ} {d1 d2 d3 d4 dc w1 w2 w3 w4 v1 v2 v3 v4 τ α1 α2 α3 α4 e1 e2 e3 e4 B1 B2 B3 B4 X : ℝ}
    (ha1 : |(a1:ℝ)| ≤ α1)
    (ha2 : |(a2:ℝ)| ≤ α2)
    (ha3 : |(a3:ℝ)| ≤ α3)
    (ha4 : |(a4:ℝ)| ≤ α4)
    (hd1 : |d1| ≤ τ)
    (hd2 : |d2| ≤ τ)
    (hd3 : |d3| ≤ τ)
    (hd4 : |d4| ≤ τ)
    (hdc : |dc| ≤ τ)
    (hv1 : |w1 - v1| ≤ e1)
    (hv2 : |w2 - v2| ≤ e2)
    (hv3 : |w3 - v3| ≤ e3)
    (hv4 : |w4 - v4| ≤ e4)
    (hB1 : |v1| ≤ B1)
    (hB2 : |v2| ≤ B2)
    (hB3 : |v3| ≤ B3)
    (hB4 : |v4| ≤ B4)
    (hx : (a1:ℝ) * v1 + (a2:ℝ) * v2 + (a3:ℝ) * v3 + (a4:ℝ) * v4 + (c:ℝ) = X) :
    |A4 a1 a2 a3 a4 c d1 d2 d3 d4 dc w1 w2 w3 w4 - X| ≤ (α1 * e1 + τ * (B1 + e1)) + (α2 * e2 + τ * (B2 + e2)) + (α3 * e3 + τ * (B3 + e3)) + (α4 * e4 + τ * (B4 + e4)) + τ := by
  subst hx
  have k1 : |((a1:ℝ) + d1) * w1 - a1 * v1| ≤ α1 * e1 + τ * (B1 + e1) := by
    have h1 := pert_mul (a := (a1:ℝ)) hd1 hv1 hB1
    have h2 := mul_le_mul_of_nonneg_right ha1 (le_trans (abs_nonneg _) hv1)
    linarith
  have k2 : |((a2:ℝ) + d2) * w2 - a2 * v2| ≤ α2 * e2 + τ * (B2 + e2) := by
    have h1 := pert_mul (a := (a2:ℝ)) hd2 hv2 hB2
    have h2 := mul_le_mul_of_nonneg_right ha2 (le_trans (abs_nonneg _) hv2)
    linarith
  have k3 : |((a3:ℝ) + d3) * w3 - a3 * v3| ≤ α3 * e3 + τ * (B3 + e3) := by
    have h1 := pert_mul (a := (a3:ℝ)) hd3 hv3 hB3
    have h2 := mul_le_mul_of_nonneg_right ha3 (le_trans (abs_nonneg _) hv3)
    linarith
  have k4 : |((a4:ℝ) + d4) * w4 - a4 * v4| ≤ α4 * e4 + τ * (B4 + e4) := by
    have h1 := pert_mul (a := (a4:ℝ)) hd4 hv4 hB4
    have h2 := mul_le_mul_of_nonneg_right ha4 (le_trans (abs_nonneg _) hv4)
    linarith
  have heq : A4 a1 a2 a3 a4 c d1 d2 d3 d4 dc w1 w2 w3 w4 - ((a1:ℝ) * v1 + (a2:ℝ) * v2 + (a3:ℝ) * v3 + (a4:ℝ) * v4 + (c:ℝ)) = (((a1:ℝ) + d1) * w1 - a1 * v1) + (((a2:ℝ) + d2) * w2 - a2 * v2) + (((a3:ℝ) + d3) * w3 - a3 * v3) + (((a4:ℝ) + d4) * w4 - a4 * v4) + dc := by
    unfold A4; ring
  rw [heq]
  exact aas (aas (abs_add3_le k1 k2 k3) k4) hdc

theorem P5 {a1 a2 a3 a4 a5 c : ℚ} {d1 d2 d3 d4 d5 dc w1 w2 w3 w4 w5 v1 v2 v3 v4 v5 τ α1 α2 α3 α4 α5 e1 e2 e3 e4 e5 B1 B2 B3 B4 B5 X : ℝ}
    (ha1 : |(a1:ℝ)| ≤ α1)
    (ha2 : |(a2:ℝ)| ≤ α2)
    (ha3 : |(a3:ℝ)| ≤ α3)
    (ha4 : |(a4:ℝ)| ≤ α4)
    (ha5 : |(a5:ℝ)| ≤ α5)
    (hd1 : |d1| ≤ τ)
    (hd2 : |d2| ≤ τ)
    (hd3 : |d3| ≤ τ)
    (hd4 : |d4| ≤ τ)
    (hd5 : |d5| ≤ τ)
    (hdc : |dc| ≤ τ)
    (hv1 : |w1 - v1| ≤ e1)
    (hv2 : |w2 - v2| ≤ e2)
    (hv3 : |w3 - v3| ≤ e3)
    (hv4 : |w4 - v4| ≤ e4)
    (hv5 : |w5 - v5| ≤ e5)
    (hB1 : |v1| ≤ B1)
    (hB2 : |v2| ≤ B2)
    (hB3 : |v3| ≤ B3)
    (hB4 : |v4| ≤ B4)
    (hB5 : |v5| ≤ B5)
    (hx : (a1:ℝ) * v1 + (a2:ℝ) * v2 + (a3:ℝ) * v3 + (a4:ℝ) * v4 + (a5:ℝ) * v5 + (c:ℝ) = X) :
    |A5 a1 a2 a3 a4 a5 c d1 d2 d3 d4 d5 dc w1 w2 w3 w4 w5 - X| ≤ (α1 * e1 + τ * (B1 + e1)) + (α2 * e2 + τ * (B2 + e2)) + (α3 * e3 + τ * (B3 + e3)) + (α4 * e4 + τ * (B4 + e4)) + (α5 * e5 + τ * (B5 + e5)) + τ := by
  subst hx
  have k1 : |((a1:ℝ) + d1) * w1 - a1 * v1| ≤ α1 * e1 + τ * (B1 + e1) := by
    have h1 := pert_mul (a := (a1:ℝ)) hd1 hv1 hB1
    have h2 := mul_le_mul_of_nonneg_right ha1 (le_trans (abs_nonneg _) hv1)
    linarith
  have k2 : |((a2:ℝ) + d2) * w2 - a2 * v2| ≤ α2 * e2 + τ * (B2 + e2) := by
    have h1 := pert_mul (a := (a2:ℝ)) hd2 hv2 hB2
    have h2 := mul_le_mul_of_nonneg_right ha2 (le_trans (abs_nonneg _) hv2)
    linarith
  have k3 : |((a3:ℝ) + d3) * w3 - a3 * v3| ≤ α3 * e3 + τ * (B3 + e3) := by
    have h1 := pert_mul (a := (a3:ℝ)) hd3 hv3 hB3
    have h2 := mul_le_mul_of_nonneg_right ha3 (le_trans (abs_nonneg _) hv3)
    linarith
  have k4 : |((a4:ℝ) + d4) * w4 - a4 * v4| ≤ α4 * e4 + τ * (B4 + e4) := by
    have h1 := pert_mul (a := (a4:ℝ)) hd4 hv4 hB4
    have h2 := mul_le_mul_of_nonneg_right ha4 (le_trans (abs_nonneg _) hv4)
    linarith
  have k5 : |((a5:ℝ) + d5) * w5 - a5 * v5| ≤ α5 * e5 + τ * (B5 + e5) := by
    have h1 := pert_mul (a := (a5:ℝ)) hd5 hv5 hB5
    have h2 := mul_le_mul_of_nonneg_right ha5 (le_trans (abs_nonneg _) hv5)
    linarith
  have heq : A5 a1 a2 a3 a4 a5 c d1 d2 d3 d4 d5 dc w1 w2 w3 w4 w5 - ((a1:ℝ) * v1 + (a2:ℝ) * v2 + (a3:ℝ) * v3 + (a4:ℝ) * v4 + (a5:ℝ) * v5 + (c:ℝ)) = (((a1:ℝ) + d1) * w1 - a1 * v1) + (((a2:ℝ) + d2) * w2 - a2 * v2) + (((a3:ℝ) + d3) * w3 - a3 * v3) + (((a4:ℝ) + d4) * w4 - a4 * v4) + (((a5:ℝ) + d5) * w5 - a5 * v5) + dc := by
    unfold A5; ring
  rw [heq]
  exact aas (aas (aas (abs_add3_le k1 k2 k3) k4) k5) hdc

theorem U3 {a1 a2 a3 c : ℚ} {d1 d2 d3 dc w1 w2 w3 v1 v2 v3 τ α1 α2 α3 e1 e2 e3 B1 B2 B3 s t : ℝ}
    (hs : 0 ≤ s)
    (ha1 : |(a1:ℝ)| ≤ α1)
    (ha2 : |(a2:ℝ)| ≤ α2)
    (ha3 : |(a3:ℝ)| ≤ α3)
    (hd1 : |d1| ≤ τ)
    (hd2 : |d2| ≤ τ)
    (hd3 : |d3| ≤ τ)
    (hdc : |dc| ≤ τ)
    (hv1 : |w1 - v1| ≤ e1)
    (hv2 : |w2 - v2| ≤ e2)
    (hv3 : |w3 - v3| ≤ e3)
    (hB1 : |v1| ≤ B1)
    (hB2 : |v2| ≤ B2)
    (hB3 : |v3| ≤ B3)
    (hx : (a1:ℝ) * v1 + (a2:ℝ) * v2 + (a3:ℝ) * v3 + (c:ℝ) = s * t) :
    |relu (A3 a1 a2 a3 c d1 d2 d3 dc w1 w2 w3) - s * relu t| ≤ (α1 * e1 + τ * (B1 + e1)) + (α2 * e2 + τ * (B2 + e2)) + (α3 * e3 + τ * (B3 + e3)) + τ := by
  have h := P3 ha1 ha2 ha3 hd1 hd2 hd3 hdc hv1 hv2 hv3 hB1 hB2 hB3 hx
  rw [relu_scale_eq hs]
  exact le_trans (relu_sub_le _ _) h

theorem U4 {a1 a2 a3 a4 c : ℚ} {d1 d2 d3 d4 dc w1 w2 w3 w4 v1 v2 v3 v4 τ α1 α2 α3 α4 e1 e2 e3 e4 B1 B2 B3 B4 s t : ℝ}
    (hs : 0 ≤ s)
    (ha1 : |(a1:ℝ)| ≤ α1)
    (ha2 : |(a2:ℝ)| ≤ α2)
    (ha3 : |(a3:ℝ)| ≤ α3)
    (ha4 : |(a4:ℝ)| ≤ α4)
    (hd1 : |d1| ≤ τ)
    (hd2 : |d2| ≤ τ)
    (hd3 : |d3| ≤ τ)
    (hd4 : |d4| ≤ τ)
    (hdc : |dc| ≤ τ)
    (hv1 : |w1 - v1| ≤ e1)
    (hv2 : |w2 - v2| ≤ e2)
    (hv3 : |w3 - v3| ≤ e3)
    (hv4 : |w4 - v4| ≤ e4)
    (hB1 : |v1| ≤ B1)
    (hB2 : |v2| ≤ B2)
    (hB3 : |v3| ≤ B3)
    (hB4 : |v4| ≤ B4)
    (hx : (a1:ℝ) * v1 + (a2:ℝ) * v2 + (a3:ℝ) * v3 + (a4:ℝ) * v4 + (c:ℝ) = s * t) :
    |relu (A4 a1 a2 a3 a4 c d1 d2 d3 d4 dc w1 w2 w3 w4) - s * relu t| ≤ (α1 * e1 + τ * (B1 + e1)) + (α2 * e2 + τ * (B2 + e2)) + (α3 * e3 + τ * (B3 + e3)) + (α4 * e4 + τ * (B4 + e4)) + τ := by
  have h := P4 ha1 ha2 ha3 ha4 hd1 hd2 hd3 hd4 hdc hv1 hv2 hv3 hv4 hB1 hB2 hB3 hB4 hx
  rw [relu_scale_eq hs]
  exact le_trans (relu_sub_le _ _) h

theorem U5 {a1 a2 a3 a4 a5 c : ℚ} {d1 d2 d3 d4 d5 dc w1 w2 w3 w4 w5 v1 v2 v3 v4 v5 τ α1 α2 α3 α4 α5 e1 e2 e3 e4 e5 B1 B2 B3 B4 B5 s t : ℝ}
    (hs : 0 ≤ s)
    (ha1 : |(a1:ℝ)| ≤ α1)
    (ha2 : |(a2:ℝ)| ≤ α2)
    (ha3 : |(a3:ℝ)| ≤ α3)
    (ha4 : |(a4:ℝ)| ≤ α4)
    (ha5 : |(a5:ℝ)| ≤ α5)
    (hd1 : |d1| ≤ τ)
    (hd2 : |d2| ≤ τ)
    (hd3 : |d3| ≤ τ)
    (hd4 : |d4| ≤ τ)
    (hd5 : |d5| ≤ τ)
    (hdc : |dc| ≤ τ)
    (hv1 : |w1 - v1| ≤ e1)
    (hv2 : |w2 - v2| ≤ e2)
    (hv3 : |w3 - v3| ≤ e3)
    (hv4 : |w4 - v4| ≤ e4)
    (hv5 : |w5 - v5| ≤ e5)
    (hB1 : |v1| ≤ B1)
    (hB2 : |v2| ≤ B2)
    (hB3 : |v3| ≤ B3)
    (hB4 : |v4| ≤ B4)
    (hB5 : |v5| ≤ B5)
    (hx : (a1:ℝ) * v1 + (a2:ℝ) * v2 + (a3:ℝ) * v3 + (a4:ℝ) * v4 + (a5:ℝ) * v5 + (c:ℝ) = s * t) :
    |relu (A5 a1 a2 a3 a4 a5 c d1 d2 d3 d4 d5 dc w1 w2 w3 w4 w5) - s * relu t| ≤ (α1 * e1 + τ * (B1 + e1)) + (α2 * e2 + τ * (B2 + e2)) + (α3 * e3 + τ * (B3 + e3)) + (α4 * e4 + τ * (B4 + e4)) + (α5 * e5 + τ * (B5 + e5)) + τ := by
  have h := P5 ha1 ha2 ha3 ha4 ha5 hd1 hd2 hd3 hd4 hd5 hdc hv1 hv2 hv3 hv4 hv5 hB1 hB2 hB3 hB4 hB5 hx
  rw [relu_scale_eq hs]
  exact le_trans (relu_sub_le _ _) h

theorem wterm {δ d w v γ τ e B : ℝ} (hδ : |δ| ≤ γ) (hd : |d| ≤ 2 * τ) (hv : |w - v| ≤ e)
    (hB : |v| ≤ B) : |δ * (w - v) + d * w| ≤ γ * e + 2 * τ * (B + e) := by
  have h3 : |w| ≤ B + e := by
    have : w = v + (w - v) := by ring
    rw [this]
    exact le_trans (abs_add_le _ _) (add_le_add hB hv)
  have h1 : |δ * (w - v)| ≤ γ * e := by
    rw [abs_mul]
    exact mul_le_mul hδ hv (abs_nonneg _) (le_trans (abs_nonneg _) hδ)
  have h2 : |d * w| ≤ 2 * τ * (B + e) := by
    rw [abs_mul]
    exact mul_le_mul hd h3 (abs_nonneg _) (le_trans (abs_nonneg _) hd)
  exact le_trans (abs_add_le _ _) (add_le_add h1 h2)

theorem Wl {p1 p2 p3 p4 cP q1 q2 q3 q4 cZ : ℚ} {dp1 dp2 dp3 dp4 dPc dz1 dz2 dz3 dz4 dZc w1 w2 w3 w4 v1 v2 v3 v4 τ γ1 γ2 γ3 γ4 e1 e2 e3 e4 B1 B2 B3 B4 X : ℝ}
    (hg1 : |(p1:ℝ) - (q1:ℝ)| ≤ γ1)
    (hg2 : |(p2:ℝ) - (q2:ℝ)| ≤ γ2)
    (hg3 : |(p3:ℝ) - (q3:ℝ)| ≤ γ3)
    (hg4 : |(p4:ℝ) - (q4:ℝ)| ≤ γ4)
    (hp1 : |dp1| ≤ τ)
    (hp2 : |dp2| ≤ τ)
    (hp3 : |dp3| ≤ τ)
    (hp4 : |dp4| ≤ τ)
    (hpc : |dPc| ≤ τ)
    (hz1 : |dz1| ≤ τ)
    (hz2 : |dz2| ≤ τ)
    (hz3 : |dz3| ≤ τ)
    (hz4 : |dz4| ≤ τ)
    (hzc : |dZc| ≤ τ)
    (hv1 : |w1 - v1| ≤ e1)
    (hv2 : |w2 - v2| ≤ e2)
    (hv3 : |w3 - v3| ≤ e3)
    (hv4 : |w4 - v4| ≤ e4)
    (hB1 : |v1| ≤ B1)
    (hB2 : |v2| ≤ B2)
    (hB3 : |v3| ≤ B3)
    (hB4 : |v4| ≤ B4)
    (hx : ((p1:ℝ) - (q1:ℝ)) * v1 + ((p2:ℝ) - (q2:ℝ)) * v2 + ((p3:ℝ) - (q3:ℝ)) * v3 + ((p4:ℝ) - (q4:ℝ)) * v4 + ((cP:ℝ) - (cZ:ℝ)) = X) :
    |(A4 p1 p2 p3 p4 cP dp1 dp2 dp3 dp4 dPc w1 w2 w3 w4 - A4 q1 q2 q3 q4 cZ dz1 dz2 dz3 dz4 dZc w1 w2 w3 w4) - X| ≤ (γ1 * e1 + 2 * τ * (B1 + e1)) + (γ2 * e2 + 2 * τ * (B2 + e2)) + (γ3 * e3 + 2 * τ * (B3 + e3)) + (γ4 * e4 + 2 * τ * (B4 + e4)) + 2 * τ := by
  subst hx
  have k1 := wterm hg1 (abs_diff2 hp1 hz1) hv1 hB1
  have k2 := wterm hg2 (abs_diff2 hp2 hz2) hv2 hB2
  have k3 := wterm hg3 (abs_diff2 hp3 hz3) hv3 hB3
  have k4 := wterm hg4 (abs_diff2 hp4 hz4) hv4 hB4
  have heq : (A4 p1 p2 p3 p4 cP dp1 dp2 dp3 dp4 dPc w1 w2 w3 w4 - A4 q1 q2 q3 q4 cZ dz1 dz2 dz3 dz4 dZc w1 w2 w3 w4) - (((p1:ℝ) - (q1:ℝ)) * v1 + ((p2:ℝ) - (q2:ℝ)) * v2 + ((p3:ℝ) - (q3:ℝ)) * v3 + ((p4:ℝ) - (q4:ℝ)) * v4 + ((cP:ℝ) - (cZ:ℝ))) = (((p1:ℝ) - (q1:ℝ)) * (w1 - v1) + (dp1 - dz1) * w1) + (((p2:ℝ) - (q2:ℝ)) * (w2 - v2) + (dp2 - dz2) * w2) + (((p3:ℝ) - (q3:ℝ)) * (w3 - v3) + (dp3 - dz3) * w3) + (((p4:ℝ) - (q4:ℝ)) * (w4 - v4) + (dp4 - dz4) * w4) + (dPc - dZc) := by
    unfold A4; ring
  rw [heq]
  exact aas (aas (abs_add3_le k1 k2 k3) k4) (abs_diff2 hpc hzc)

theorem FIN {pp zz Bt Q o1 o2 oc τ eP eW M Mp Mz : ℝ}
    (hBt0 : 0 ≤ Bt) (hBt : Bt ≤ 5)
    (hP : |pp - (3 * Bt + 1)| ≤ eP) (hW : |(pp - zz) - (3 * Q + 1)| ≤ eW)
    (heP1 : eP ≤ 1) (heP : eP ≤ M) (heW : eW ≤ M)
    (hMp : 3 * 5 + 1 + eP ≤ Mp) (hz0 : relu zz ≤ Mz)
    (ho1 : |o1| ≤ τ) (ho2 : |o2| ≤ τ) (hoc : |oc| ≤ τ) :
    |A2 (1/3) (-1/3) (-1/4) o1 o2 oc (relu pp) (relu zz) - (min Bt Q + 1/12)|
      ≤ M / 3 + τ * (Mp + Mz + 1) := by
  have heP0 : 0 ≤ eP := le_trans (abs_nonneg _) hP
  obtain ⟨hPl, hPr⟩ := abs_le.mp hP
  have hpp : 0 ≤ pp := by linarith
  have hr : relu pp = pp := relu_of_nonneg hpp
  have hT : relu pp - relu zz = min pp (pp - zz) := by
    have h := sub_relu_sub pp (pp - zz)
    rw [sub_sub_cancel] at h
    rw [hr]; exact h
  have hmin : min (3 * Bt + 1) (3 * Q + 1) = 3 * min Bt Q + 1 := by
    rcases le_total Bt Q with h | h
    · rw [min_eq_left h, min_eq_left (show 3 * Bt + 1 ≤ 3 * Q + 1 by linarith)]
    · rw [min_eq_right h, min_eq_right (show 3 * Q + 1 ≤ 3 * Bt + 1 by linarith)]
  have hT2 : |min pp (pp - zz) - (3 * min Bt Q + 1)| ≤ M := by
    rw [← hmin]
    exact my_min_lip (le_trans hP heP) (le_trans hW heW)
  have hdiff : A2 (1/3) (-1/3) (-1/4) o1 o2 oc (relu pp) (relu zz) - (min Bt Q + 1/12)
      = (1/3) * (min pp (pp - zz) - (3 * min Bt Q + 1)) + o1 * relu pp + o2 * relu zz + oc := by
    unfold A2
    push_cast
    rw [← hT]
    ring
  have hpb : |relu pp| ≤ Mp := abs_le.mpr ⟨by linarith [relu_nonneg' pp], by linarith⟩
  have hzb : |relu zz| ≤ Mz := abs_le.mpr ⟨by linarith [relu_nonneg' zz], hz0⟩
  obtain ⟨t1, t2⟩ := abs_le.mp hT2
  obtain ⟨q1, q2⟩ := abs_le.mp (pert_abs_mul ho1 hpb)
  obtain ⟨r1, r2⟩ := abs_le.mp (pert_abs_mul ho2 hzb)
  obtain ⟨c1, c2⟩ := abs_le.mp hoc
  rw [hdiff, abs_le]
  constructor <;> linarith

set_option maxHeartbeats 2000000 in
theorem med_approx (A B E a1 : ℝ) (hB : 0 ≤ B) (hA : A ≤ a1) (hE : E = -2 * a1 + 1/2) :
    min B (max A E) ≤ max (min A B) (min (max A B) E) ∧
    max (min A B) (min (max A B) E) ≤ min B (max A E) + 1/6 := by
  constructor
  · simp only [min_def, max_def]
    split_ifs <;> linarith
  · simp only [min_def, max_def]
    split_ifs <;> linarith

set_option maxHeartbeats 2000000 in
theorem facts (x0 x1 x2 : ℝ) (l0 : (-8) ≤ x0) (u0 : x0 ≤ 4) (l1 : (-2) ≤ x1) (u1 : x1 ≤ 2)
    (l2 : (-2) ≤ x2) (u2 : x2 ≤ 4) :
    (0 ≤ m11 x0 x1 x2 ∧ m11 x0 x1 x2 ≤ 19/2) ∧ (0 ≤ m12 x0 x1 x2 ∧ m12 x0 x1 x2 ≤ 19/2) ∧
    (0 ≤ m13 x0 x1 x2 ∧ m13 x0 x1 x2 ≤ 9) ∧ (0 ≤ m14 x0 x1 x2 ∧ m14 x0 x1 x2 ≤ 7/2) ∧
    (0 ≤ m15 x0 x1 x2 ∧ m15 x0 x1 x2 ≤ 13/2) ∧ (0 ≤ m21 x0 x1 x2 ∧ m21 x0 x1 x2 ≤ 7) ∧
    (0 ≤ m22 x0 x1 x2 ∧ m22 x0 x1 x2 ≤ 5) ∧ (0 ≤ m23 x0 x1 x2 ∧ m23 x0 x1 x2 ≤ 9/2) ∧
    (0 ≤ m24 x0 x1 x2 ∧ m24 x0 x1 x2 ≤ 13/2) ∧ m22 x0 x1 x2 + m23 x0 x1 x2 ≤ 5 ∧
    m22 x0 x1 x2 + m23 x0 x1 x2 = |max ((1/2) * x0 + 2 * x1 + (-1)) ((-1/2) * x2 + (-5/2))| ∧
    m24 x0 x1 x2 - 5 + m21 x0 x1 x2 = max (min ((1/2) * x2 + (1/2)) ((1/2) * x0 + (-1) * x2 + 1)) ((-1) * x2 + (-1/2)) := by
  have n11 : 0 ≤ m11 x0 x1 x2 := by unfold m11; exact relu_nonneg' _
  have n12 : 0 ≤ m12 x0 x1 x2 := by unfold m12; exact relu_nonneg' _
  have n13 : 0 ≤ m13 x0 x1 x2 := by unfold m13; exact relu_nonneg' _
  have n14 : 0 ≤ m14 x0 x1 x2 := by unfold m14; exact relu_nonneg' _
  have n15 : 0 ≤ m15 x0 x1 x2 := by unfold m15; exact relu_nonneg' _
  have n21 : 0 ≤ m21 x0 x1 x2 := by unfold m21; exact relu_nonneg' _
  have n22 : 0 ≤ m22 x0 x1 x2 := by unfold m22; exact relu_nonneg' _
  have n23 : 0 ≤ m23 x0 x1 x2 := by unfold m23; exact relu_nonneg' _
  have n24 : 0 ≤ m24 x0 x1 x2 := by unfold m24; exact relu_nonneg' _
  have b11 : m11 x0 x1 x2 ≤ 19/2 := by unfold m11; exact relu_le_of_le (by linarith) (by norm_num)
  have b12 : m12 x0 x1 x2 ≤ 19/2 := by unfold m12; exact relu_le_of_le (by linarith) (by norm_num)
  have b13 : m13 x0 x1 x2 ≤ 9 := by unfold m13; exact relu_le_of_le (by linarith) (by norm_num)
  have b14 : m14 x0 x1 x2 ≤ 7/2 := by unfold m14; exact relu_le_of_le (by linarith) (by norm_num)
  have b15 : m15 x0 x1 x2 ≤ 13/2 := by unfold m15; exact relu_le_of_le (by linarith) (by norm_num)
  have b21 : m21 x0 x1 x2 ≤ 7 := by unfold m21; exact relu_le_of_le (by linarith) (by norm_num)
  have hm14 : m14 x0 x1 x2 = (-1/2) * x2 + (5/2) := by
    unfold m14; exact relu_of_nonneg (by linarith)
  have hm13 : m13 x0 x1 x2 = (3/2) * x2 + 3 := by
    unfold m13; exact relu_of_nonneg (by linarith)
  have hm15 : m15 x0 x1 x2 = (-1) * x2 + (9/2) := by
    unfold m15; exact relu_of_nonneg (by linarith)
  have hm24 : m24 x0 x1 x2 = (-1) * x2 + (9/2) := by
    unfold m24; rw [relu_of_nonneg n15]; exact hm15
  have hm12 : m12 x0 x1 x2 = relu (((1/2) * x0 + 2 * x1 + (-1)) - ((-1/2) * x2 + (-5/2))) := by
    have h : (1/2) * x0 + 2 * x1 + (1/2) * x2 + (3/2) = ((1/2) * x0 + 2 * x1 + (-1)) - ((-1/2) * x2 + (-5/2)) := by ring
    unfold m12; rw [h]
  have hMq : m14 x0 x1 x2 + m12 x0 x1 x2 - 5 = max ((1/2) * x0 + 2 * x1 + (-1)) ((-1/2) * x2 + (-5/2)) := by
    rw [max_comm, ← add_relu_sub ((-1/2) * x2 + (-5/2)) ((1/2) * x0 + 2 * x1 + (-1))]
    rw [hm14, hm12]; ring
  have hm22 : m22 x0 x1 x2 = relu (max ((1/2) * x0 + 2 * x1 + (-1)) ((-1/2) * x2 + (-5/2))) := by
    unfold m22; rw [hMq]
  have hm23 : m23 x0 x1 x2 = relu (-(max ((1/2) * x0 + 2 * x1 + (-1)) ((-1/2) * x2 + (-5/2)))) := by
    have h : 5 - m14 x0 x1 x2 - m12 x0 x1 x2 = -(max ((1/2) * x0 + 2 * x1 + (-1)) ((-1/2) * x2 + (-5/2))) := by rw [← hMq]; ring
    unfold m23; rw [h]
  have hMle : max ((1/2) * x0 + 2 * x1 + (-1)) ((-1/2) * x2 + (-5/2)) ≤ 5 := max_le (by linarith) (by linarith)
  have hMge : (-9/2) ≤ max ((1/2) * x0 + 2 * x1 + (-1)) ((-1/2) * x2 + (-5/2)) := le_trans (by linarith) (le_max_right _ _)
  have b22 : m22 x0 x1 x2 ≤ 5 := by rw [hm22]; exact relu_le_of_le hMle (by norm_num)
  have b23 : m23 x0 x1 x2 ≤ 9/2 := by rw [hm23]; exact relu_le_of_le (by linarith) (by norm_num)
  have b24 : m24 x0 x1 x2 ≤ 13/2 := by rw [hm24]; linarith
  have hBt : m22 x0 x1 x2 + m23 x0 x1 x2 = |max ((1/2) * x0 + 2 * x1 + (-1)) ((-1/2) * x2 + (-5/2))| := by
    rw [hm22, hm23]; exact relu_add_relu_neg _
  have hBt5 : m22 x0 x1 x2 + m23 x0 x1 x2 ≤ 5 := by
    rw [hBt]; exact abs_le.mpr ⟨by linarith, hMle⟩
  have hm11 : m11 x0 x1 x2 = relu (((1/2) * x2 + (1/2)) - ((1/2) * x0 + (-1) * x2 + 1)) := by
    have h : (-1/2) * x0 + (3/2) * x2 + (-1/2) = ((1/2) * x2 + (1/2)) - ((1/2) * x0 + (-1) * x2 + 1) := by ring
    unfold m11; rw [h]
  have hA : min ((1/2) * x2 + (1/2)) ((1/2) * x0 + (-1) * x2 + 1) = ((1/2) * x2 + (1/2)) - m11 x0 x1 x2 := by
    rw [hm11]; exact (sub_relu_sub _ _).symm
  have hm21 : m21 x0 x1 x2 = relu (min ((1/2) * x2 + (1/2)) ((1/2) * x0 + (-1) * x2 + 1) - ((-1) * x2 + (-1/2))) := by
    have h : m13 x0 x1 x2 - m11 x0 x1 x2 - 2 = min ((1/2) * x2 + (1/2)) ((1/2) * x0 + (-1) * x2 + 1) - ((-1) * x2 + (-1/2)) := by
      rw [hA, hm13]; ring
    unfold m21; rw [h]
  have hQ : m24 x0 x1 x2 - 5 + m21 x0 x1 x2 = max (min ((1/2) * x2 + (1/2)) ((1/2) * x0 + (-1) * x2 + 1)) ((-1) * x2 + (-1/2)) := by
    rw [max_comm, ← add_relu_sub ((-1) * x2 + (-1/2)) (min ((1/2) * x2 + (1/2)) ((1/2) * x0 + (-1) * x2 + 1)), hm24, hm21]; ring
  exact ⟨⟨n11, b11⟩, ⟨n12, b12⟩, ⟨n13, b13⟩, ⟨n14, b14⟩, ⟨n15, b15⟩, ⟨n21, b21⟩, ⟨n22, b22⟩,
    ⟨n23, b23⟩, ⟨n24, b24⟩, hBt5, hBt, hQ⟩

set_option maxHeartbeats 4000000 in
theorem net_robust : StatementRobust net := by
  intro dW db hW x0 x1 x2 l0 u0 l1 u1 l2 u2
  obtain ⟨hw, hb⟩ := hW
  obtain ⟨⟨n11, b11⟩, ⟨n12, b12⟩, ⟨n13, b13⟩, ⟨n14, b14⟩, ⟨n15, b15⟩, ⟨n21, b21⟩, ⟨n22, b22⟩, ⟨n23, b23⟩, ⟨n24, b24⟩, hBt5, hBt, hQ⟩ := facts x0 x1 x2 l0 u0 l1 u1 l2 u2
  have bx0 : |x0| ≤ 8 := abs_le.mpr ⟨by linarith, by linarith⟩
  have bx1 : |x1| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have bx2 : |x2| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  have z0 : |x0 - x0| ≤ (0:ℝ) := by simp
  have z1 : |x1 - x1| ≤ (0:ℝ) := by simp
  have z2 : |x2 - x2| ≤ (0:ℝ) := by simp
  have V11 : |2 * m11 x0 x1 x2| ≤ 19 := abs_le.mpr ⟨by linarith, by linarith⟩
  have V12 : |1 * m12 x0 x1 x2| ≤ (19/2) := abs_le.mpr ⟨by linarith, by linarith⟩
  have V13 : |2 * m13 x0 x1 x2| ≤ 18 := abs_le.mpr ⟨by linarith, by linarith⟩
  have V14 : |2 * m14 x0 x1 x2| ≤ 7 := abs_le.mpr ⟨by linarith, by linarith⟩
  have V15 : |2 * m15 x0 x1 x2| ≤ 13 := abs_le.mpr ⟨by linarith, by linarith⟩
  have V21 : |4 * m21 x0 x1 x2| ≤ 28 := abs_le.mpr ⟨by linarith, by linarith⟩
  have V22 : |2 * m22 x0 x1 x2| ≤ 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have V23 : |4 * m23 x0 x1 x2| ≤ 18 := abs_le.mpr ⟨by linarith, by linarith⟩
  have V24 : |4 * m24 x0 x1 x2| ≤ 26 := abs_le.mpr ⟨by linarith, by linarith⟩
  have E11 : |P11 dW db x0 x1 x2 - 2 * m11 x0 x1 x2| ≤ (3/200) := by
    refine le_trans (U3 (s := 2) (t := (-1/2) * x0 + (3/2) * x2 + (-1/2)) (by norm_num)
      (show |(((-1):ℚ):ℝ)| ≤ 1 by rw [abs_le]; constructor <;> norm_num) (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |((3:ℚ):ℝ)| ≤ 3 by rw [abs_le]; constructor <;> norm_num)
      (hw 0 0 0) (hw 0 0 1) (hw 0 0 2) (hb 0 0) z0 z1 z2 bx0 bx1 bx2 (by push_cast; ring)) (by norm_num)
  have E12 : |P12 dW db x0 x1 x2 - 1 * m12 x0 x1 x2| ≤ (3/200) := by
    refine le_trans (U3 (s := 1) (t := (1/2) * x0 + 2 * x1 + (1/2) * x2 + (3/2)) (by norm_num)
      (show |(((1/2):ℚ):ℝ)| ≤ (1/2) by rw [abs_le]; constructor <;> norm_num) (show |((2:ℚ):ℝ)| ≤ 2 by rw [abs_le]; constructor <;> norm_num) (show |(((1/2):ℚ):ℝ)| ≤ (1/2) by rw [abs_le]; constructor <;> norm_num)
      (hw 0 1 0) (hw 0 1 1) (hw 0 1 2) (hb 0 1) z0 z1 z2 bx0 bx1 bx2 (by push_cast; ring)) (by norm_num)
  have E13 : |P13 dW db x0 x1 x2 - 2 * m13 x0 x1 x2| ≤ (3/200) := by
    refine le_trans (U3 (s := 2) (t := (3/2) * x2 + 3) (by norm_num)
      (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |((3:ℚ):ℝ)| ≤ 3 by rw [abs_le]; constructor <;> norm_num)
      (hw 0 2 0) (hw 0 2 1) (hw 0 2 2) (hb 0 2) z0 z1 z2 bx0 bx1 bx2 (by push_cast; ring)) (by norm_num)
  have E14 : |P14 dW db x0 x1 x2 - 2 * m14 x0 x1 x2| ≤ (3/200) := by
    refine le_trans (U3 (s := 2) (t := (-1/2) * x2 + (5/2)) (by norm_num)
      (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |(((-1):ℚ):ℝ)| ≤ 1 by rw [abs_le]; constructor <;> norm_num)
      (hw 0 3 0) (hw 0 3 1) (hw 0 3 2) (hb 0 3) z0 z1 z2 bx0 bx1 bx2 (by push_cast; ring)) (by norm_num)
  have E15 : |P15 dW db x0 x1 x2 - 2 * m15 x0 x1 x2| ≤ (3/200) := by
    refine le_trans (U3 (s := 2) (t := (-1) * x2 + (9/2)) (by norm_num)
      (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |(((-2):ℚ):ℝ)| ≤ 2 by rw [abs_le]; constructor <;> norm_num)
      (hw 0 4 0) (hw 0 4 1) (hw 0 4 2) (hb 0 4) z0 z1 z2 bx0 bx1 bx2 (by push_cast; ring)) (by norm_num)
  have E21 : |P21 dW db x0 x1 x2 - 4 * m21 x0 x1 x2| ≤ (319/2500) := by
    refine le_trans (U5 (s := 4) (t := m13 x0 x1 x2 - m11 x0 x1 x2 - 2) (by norm_num)
      (show |(((-2):ℚ):ℝ)| ≤ 2 by rw [abs_le]; constructor <;> norm_num) (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |((2:ℚ):ℝ)| ≤ 2 by rw [abs_le]; constructor <;> norm_num) (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num)
      (hw 1 0 0) (hw 1 0 1) (hw 1 0 2) (hw 1 0 3) (hw 1 0 4) (hb 1 0) E11 E12 E13 E14 E15 V11 V12 V13 V14 V15 (by push_cast; ring)) (by norm_num)
  have E22 : |P22 dW db x0 x1 x2 - 2 * m22 x0 x1 x2| ≤ (563/5000) := by
    refine le_trans (U5 (s := 2) (t := m14 x0 x1 x2 + m12 x0 x1 x2 - 5) (by norm_num)
      (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |((2:ℚ):ℝ)| ≤ 2 by rw [abs_le]; constructor <;> norm_num) (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |((1:ℚ):ℝ)| ≤ 1 by rw [abs_le]; constructor <;> norm_num) (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num)
      (hw 1 1 0) (hw 1 1 1) (hw 1 1 2) (hw 1 1 3) (hw 1 1 4) (hb 1 1) E11 E12 E13 E14 E15 V11 V12 V13 V14 V15 (by push_cast; ring)) (by norm_num)
  have E23 : |P23 dW db x0 x1 x2 - 4 * m23 x0 x1 x2| ≤ (197/1250) := by
    refine le_trans (U5 (s := 4) (t := 5 - m14 x0 x1 x2 - m12 x0 x1 x2) (by norm_num)
      (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |(((-4):ℚ):ℝ)| ≤ 4 by rw [abs_le]; constructor <;> norm_num) (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |(((-2):ℚ):ℝ)| ≤ 2 by rw [abs_le]; constructor <;> norm_num) (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num)
      (hw 1 2 0) (hw 1 2 1) (hw 1 2 2) (hw 1 2 3) (hw 1 2 4) (hb 1 2) E11 E12 E13 E14 E15 V11 V12 V13 V14 V15 (by push_cast; ring)) (by norm_num)
  have E24 : |P24 dW db x0 x1 x2 - 4 * m24 x0 x1 x2| ≤ (61/625) := by
    refine le_trans (U5 (s := 4) (t := m15 x0 x1 x2) (by norm_num)
      (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |((2:ℚ):ℝ)| ≤ 2 by rw [abs_le]; constructor <;> norm_num)
      (hw 1 3 0) (hw 1 3 1) (hw 1 3 2) (hw 1 3 3) (hw 1 3 4) (hb 1 3) E11 E12 E13 E14 E15 V11 V12 V13 V14 V15 (by push_cast; ring)) (by norm_num)
  have EPh : |PP dW db x0 x1 x2 - (3 * (m22 x0 x1 x2 + m23 x0 x1 x2) + 1)| ≤ (1853/5000) := by
    refine le_trans (P4 (X := 3 * (m22 x0 x1 x2 + m23 x0 x1 x2) + 1)
      (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |(((3/2):ℚ):ℝ)| ≤ (3/2) by rw [abs_le]; constructor <;> norm_num) (show |(((3/4):ℚ):ℝ)| ≤ (3/4) by rw [abs_le]; constructor <;> norm_num) (show |((0:ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num)
      (hw 2 0 0) (hw 2 0 1) (hw 2 0 2) (hw 2 0 3) (hb 2 0) E21 E22 E23 E24 V21 V22 V23 V24 (by push_cast; ring)) (by norm_num)
  have EZh : |relu (ZZ dW db x0 x1 x2) - 3 * m32 x0 x1 x2| ≤ (1079/2000) := by
    refine le_trans (U4 (s := 3) (t := m22 x0 x1 x2 + m23 x0 x1 x2 - m24 x0 x1 x2 + 5 - m21 x0 x1 x2) (by norm_num)
      (show |(((-3/4):ℚ):ℝ)| ≤ (3/4) by rw [abs_le]; constructor <;> norm_num) (show |(((3/2):ℚ):ℝ)| ≤ (3/2) by rw [abs_le]; constructor <;> norm_num) (show |(((3/4):ℚ):ℝ)| ≤ (3/4) by rw [abs_le]; constructor <;> norm_num) (show |(((-3/4):ℚ):ℝ)| ≤ (3/4) by rw [abs_le]; constructor <;> norm_num)
      (hw 2 1 0) (hw 2 1 1) (hw 2 1 2) (hw 2 1 3) (hb 2 1) E21 E22 E23 E24 V21 V22 V23 V24 (by push_cast; ring)) (by norm_num)
  have EWh : |(PP dW db x0 x1 x2 - ZZ dW db x0 x1 x2) - (3 * (m24 x0 x1 x2 - 5 + m21 x0 x1 x2) + 1)| ≤ (3359/10000) := by
    refine le_trans (Wl (X := 3 * (m24 x0 x1 x2 - 5 + m21 x0 x1 x2) + 1) (show |((0:ℚ):ℝ) - (((-3/4):ℚ):ℝ)| ≤ (3/4) by rw [abs_le]; constructor <;> norm_num) (show |(((3/2):ℚ):ℝ) - (((3/2):ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |(((3/4):ℚ):ℝ) - (((3/4):ℚ):ℝ)| ≤ 0 by rw [abs_le]; constructor <;> norm_num) (show |((0:ℚ):ℝ) - (((-3/4):ℚ):ℝ)| ≤ (3/4) by rw [abs_le]; constructor <;> norm_num)
      (hw 2 0 0) (hw 2 0 1) (hw 2 0 2) (hw 2 0 3) (hb 2 0) (hw 2 1 0) (hw 2 1 1) (hw 2 1 2) (hw 2 1 3) (hb 2 1) E21 E22 E23 E24 V21 V22 V23 V24 (by push_cast; ring)) (by norm_num)
  have hz0 : relu (ZZ dW db x0 x1 x2) ≤ (61079/2000) := by
    have h := abs_le.mp EZh
    have h32 : m32 x0 x1 x2 ≤ 10 := by unfold m32; exact relu_le_of_le (by linarith) (by norm_num)
    linarith [h.1, h.2]
  have hF := FIN (Bt := m22 x0 x1 x2 + m23 x0 x1 x2) (Q := m24 x0 x1 x2 - 5 + m21 x0 x1 x2) (M := (1853/5000)) (Mp := (81853/5000)) (Mz := (61079/2000)) (add_nonneg n22 n23) hBt5 EPh EWh (by norm_num) (by norm_num) (by norm_num) (by norm_num) hz0 (hw 3 0 0) (hw 3 0 1) (hb 3 0)
  rw [hBt, hQ] at hF
  have hmed := med_approx (min ((1/2) * x2 + (1/2)) ((1/2) * x0 + (-1) * x2 + 1)) |max ((1/2) * x0 + 2 * x1 + (-1)) ((-1/2) * x2 + (-5/2))| ((-1) * x2 + (-1/2)) ((1/2) * x2 + (1/2)) (abs_nonneg _) (min_le_left _ _) (by ring)
  have hs : spec x0 x1 x2 = max (min (min ((1/2) * x2 + (1/2)) ((1/2) * x0 + (-1) * x2 + 1)) |max ((1/2) * x0 + 2 * x1 + (-1)) ((-1/2) * x2 + (-5/2))|) (min (max (min ((1/2) * x2 + (1/2)) ((1/2) * x0 + (-1) * x2 + 1)) |max ((1/2) * x0 + 2 * x1 + (-1)) ((-1/2) * x2 + (-5/2))|) ((-1) * x2 + (-1/2))) := rfl
  obtain ⟨h1, h2⟩ := hmed
  have f := abs_le.mp hF
  refine ⟨A2 (1/3) (-1/3) (-1/4) (dW 3 0 0) (dW 3 0 1) (db 3 0) (relu (PP dW db x0 x1 x2)) (relu (ZZ dW db x0 x1 x2)), ?_, ?_⟩
  · first | exact rfl | simp [net, Net.evalP, hiddenP, rowsP, dotP, A2, A3, A4, A5, PP, ZZ, P11, P12, P13, P14, P15, P21, P22, P23, P24]
  · rw [hs, abs_le]
    constructor <;> linarith [f.1, f.2]

end Lane4.Case
