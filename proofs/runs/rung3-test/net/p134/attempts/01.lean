namespace Lane4.Case
open Lane4

def net : Net :=
  { hidden := [{ W := [[1, 0], [-1, 0], [0, 2], [0, -2]], b := [3/2, -3/2, 3, -3] },
               { W := [[-1, -1, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]], b := [-1, 0, 0] }],
    out := { W := [[-1, 1, 1]], b := [0] } }

noncomputable def lp (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ :=
  relu ((1 + dW 0 0 0) * x0 + (0 + dW 0 0 1) * x1 + (3/2 + db 0 0))
noncomputable def lq (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ :=
  relu ((-1 + dW 0 1 0) * x0 + (0 + dW 0 1 1) * x1 + (-3/2 + db 0 1))
noncomputable def lr (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ :=
  relu ((0 + dW 0 2 0) * x0 + (2 + dW 0 2 1) * x1 + (3 + db 0 2))
noncomputable def ls (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ :=
  relu ((0 + dW 0 3 0) * x0 + (-2 + dW 0 3 1) * x1 + (-3 + db 0 3))

noncomputable def mw (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ :=
  relu ((-1 + dW 1 0 0) * lp dW db x0 x1 + (-1 + dW 1 0 1) * lq dW db x0 x1
    + (1 + dW 1 0 2) * lr dW db x0 x1 + (0 + dW 1 0 3) * ls dW db x0 x1 + (-1 + db 1 0))
noncomputable def mr (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ :=
  relu ((0 + dW 1 1 0) * lp dW db x0 x1 + (0 + dW 1 1 1) * lq dW db x0 x1
    + (1 + dW 1 1 2) * lr dW db x0 x1 + (0 + dW 1 1 3) * ls dW db x0 x1 + (0 + db 1 1))
noncomputable def ms (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ :=
  relu ((0 + dW 1 2 0) * lp dW db x0 x1 + (0 + dW 1 2 1) * lq dW db x0 x1
    + (0 + dW 1 2 2) * lr dW db x0 x1 + (1 + dW 1 2 3) * ls dW db x0 x1 + (0 + db 1 2))

noncomputable def yout (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ :=
  (-1 + dW 2 0 0) * mw dW db x0 x1 + (1 + dW 2 0 1) * mr dW db x0 x1
    + (1 + dW 2 0 2) * ms dW db x0 x1 + (0 + db 2 0)

theorem absrelu {t B : ℝ} (h : t ≤ B) (hB : 0 ≤ B) : |relu t| ≤ B := by
  rw [abs_of_nonneg (relu_nonneg' t)]; exact relu_le_of_le h hB

theorem step1 {a1 a2 c d1 d2 dc x0 x1 t : ℝ} (h1 : |d1| ≤ 1/1000) (h2 : |d2| ≤ 1/1000)
    (hc : |dc| ≤ 1/1000) (b0 : |x0| ≤ 8) (b1 : |x1| ≤ 8) (ht : t = a1*x0 + a2*x1 + c) :
    |relu ((a1 + d1) * x0 + (a2 + d2) * x1 + (c + dc)) - relu t| ≤ 17/1000 := by
  refine relu_pert ?_
  have h : ((a1 + d1) * x0 + (a2 + d2) * x1 + (c + dc)) - t = d1 * x0 + d2 * x1 + dc := by
    rw [ht]; ring
  rw [h]
  exact le_trans (abs_add3_le (pert_abs_mul h1 b0) (pert_abs_mul h2 b1) hc) (by norm_num)

theorem step2 {a1 a2 a3 a4 c d1 d2 d3 d4 dc v1 v2 v3 v4 u1 u2 u3 u4 e B1 B2 B3 B4 t A : ℝ}
    (h1 : |d1| ≤ 1/1000) (h2 : |d2| ≤ 1/1000) (h3 : |d3| ≤ 1/1000) (h4 : |d4| ≤ 1/1000)
    (hc : |dc| ≤ 1/1000)
    (e1 : |u1 - v1| ≤ e) (e2 : |u2 - v2| ≤ e) (e3 : |u3 - v3| ≤ e) (e4 : |u4 - v4| ≤ e)
    (g1 : |v1| ≤ B1) (g2 : |v2| ≤ B2) (g3 : |v3| ≤ B3) (g4 : |v4| ≤ B4)
    (hA : |a1| + |a2| + |a3| + |a4| ≤ A)
    (ht : t = a1*v1 + a2*v2 + a3*v3 + a4*v4 + c) :
    |relu ((a1 + d1) * u1 + (a2 + d2) * u2 + (a3 + d3) * u3 + (a4 + d4) * u4 + (c + dc))
      - relu t| ≤ A * e + 1/1000 * ((B1 + e) + (B2 + e) + (B3 + e) + (B4 + e)) + 1/1000 := by
  refine relu_pert ?_
  have he : 0 ≤ e := le_trans (abs_nonneg _) e1
  have m1 := abs_le.mp (pert_mul (a := a1) h1 e1 g1)
  have m2 := abs_le.mp (pert_mul (a := a2) h2 e2 g2)
  have m3 := abs_le.mp (pert_mul (a := a3) h3 e3 g3)
  have m4 := abs_le.mp (pert_mul (a := a4) h4 e4 g4)
  have hAe := mul_le_mul_of_nonneg_right hA he
  have c1 := abs_le.mp hc
  subst ht
  rw [abs_le]
  constructor <;>
    linarith [m1.1, m1.2, m2.1, m2.2, m3.1, m3.2, m4.1, m4.2, c1.1, c1.2]

theorem step3 {a1 a2 a3 c d1 d2 d3 dc v1 v2 v3 u1 u2 u3 e1 e2 e3 B1 B2 B3 T : ℝ}
    (h1 : |d1| ≤ 1/1000) (h2 : |d2| ≤ 1/1000) (h3 : |d3| ≤ 1/1000) (hc : |dc| ≤ 1/1000)
    (f1 : |u1 - v1| ≤ e1) (f2 : |u2 - v2| ≤ e2) (f3 : |u3 - v3| ≤ e3)
    (g1 : |v1| ≤ B1) (g2 : |v2| ≤ B2) (g3 : |v3| ≤ B3)
    (ha1 : |a1| ≤ 1) (ha2 : |a2| ≤ 1) (ha3 : |a3| ≤ 1)
    (ht : T = a1*v1 + a2*v2 + a3*v3 + c) :
    |(a1 + d1) * u1 + (a2 + d2) * u2 + (a3 + d3) * u3 + (c + dc) - T|
      ≤ e1 + e2 + e3 + 1/1000 * ((B1 + e1) + (B2 + e2) + (B3 + e3)) + 1/1000 := by
  have n1 : 0 ≤ e1 := le_trans (abs_nonneg _) f1
  have n2 : 0 ≤ e2 := le_trans (abs_nonneg _) f2
  have n3 : 0 ≤ e3 := le_trans (abs_nonneg _) f3
  have m1 := abs_le.mp (pert_mul (a := a1) h1 f1 g1)
  have m2 := abs_le.mp (pert_mul (a := a2) h2 f2 g2)
  have m3 := abs_le.mp (pert_mul (a := a3) h3 f3 g3)
  have k1 := mul_le_of_le_one_left n1 ha1
  have k2 := mul_le_of_le_one_left n2 ha2
  have k3 := mul_le_of_le_one_left n3 ha3
  have c1 := abs_le.mp hc
  subst ht
  rw [abs_le]
  constructor <;>
    linarith [m1.1, m1.2, m2.1, m2.2, m3.1, m3.2, c1.1, c1.2]

theorem ident (x0 x1 : ℝ) :
    -relu (relu (2*x1+3) - relu (x0+3/2) - relu (-x0-3/2) - 1)
      + relu (relu (2*x1+3)) + relu (relu (-2*x1-3)) = spec x0 x1 := by
  unfold spec
  simp only [relu, max_def, min_def, abs_eq_max_neg]
  split_ifs <;> linarith

theorem net_robust : StatementRobust net := by
  intro dW db hW x0 x1 l0 u0 l1 u1
  obtain ⟨hw, hb⟩ := hW
  refine ⟨yout dW db x0 x1, ?_, ?_⟩
  · simp [net, Net.evalP, hiddenP, rowsP, dotP, yout, mw, mr, ms, lp, lq, lr, ls]
    try ring_nf
  · have bx0 : |x0| ≤ 8 := abs_le.mpr ⟨by linarith, by linarith⟩
    have bx1 : |x1| ≤ 8 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hp : |lp dW db x0 x1 - relu (x0 + 3/2)| ≤ 17/1000 :=
      step1 (a1 := 1) (a2 := 0) (c := 3/2) (hw 0 0 0) (hw 0 0 1) (hb 0 0) bx0 bx1 (by ring)
    have hq : |lq dW db x0 x1 - relu (-x0 - 3/2)| ≤ 17/1000 :=
      step1 (a1 := -1) (a2 := 0) (c := -3/2) (hw 0 1 0) (hw 0 1 1) (hb 0 1) bx0 bx1 (by ring)
    have hr : |lr dW db x0 x1 - relu (2*x1 + 3)| ≤ 17/1000 :=
      step1 (a1 := 0) (a2 := 2) (c := 3) (hw 0 2 0) (hw 0 2 1) (hb 0 2) bx0 bx1 (by ring)
    have hs : |ls dW db x0 x1 - relu (-2*x1 - 3)| ≤ 17/1000 :=
      step1 (a1 := 0) (a2 := -2) (c := -3) (hw 0 3 0) (hw 0 3 1) (hb 0 3) bx0 bx1 (by ring)
    have gP : |relu (x0 + 3/2)| ≤ 5/2 := absrelu (by linarith) (by norm_num)
    have gQ : |relu (-x0 - 3/2)| ≤ 13/2 := absrelu (by linarith) (by norm_num)
    have gR : |relu (2*x1 + 3)| ≤ 19 := absrelu (by linarith) (by norm_num)
    have gS : |relu (-2*x1 - 3)| ≤ 5 := absrelu (by linarith) (by norm_num)
    have hW : |mw dW db x0 x1
        - relu (relu (2*x1+3) - relu (x0+3/2) - relu (-x0-3/2) - 1)|
        ≤ 3 * (17/1000) + 1/1000 * (((5/2) + 17/1000) + ((13/2) + 17/1000)
            + (19 + 17/1000) + (5 + 17/1000)) + 1/1000 :=
      step2 (a1 := -1) (a2 := -1) (a3 := 1) (a4 := 0) (c := -1)
        (hw 1 0 0) (hw 1 0 1) (hw 1 0 2) (hw 1 0 3) (hb 1 0) hp hq hr hs gP gQ gR gS
        (by norm_num) (by ring)
    have hR2 : |mr dW db x0 x1 - relu (relu (2*x1+3))|
        ≤ 1 * (17/1000) + 1/1000 * (((5/2) + 17/1000) + ((13/2) + 17/1000)
            + (19 + 17/1000) + (5 + 17/1000)) + 1/1000 :=
      step2 (a1 := 0) (a2 := 0) (a3 := 1) (a4 := 0) (c := 0)
        (hw 1 1 0) (hw 1 1 1) (hw 1 1 2) (hw 1 1 3) (hb 1 1) hp hq hr hs gP gQ gR gS
        (by norm_num) (by ring)
    have hS2 : |ms dW db x0 x1 - relu (relu (-2*x1-3))|
        ≤ 1 * (17/1000) + 1/1000 * (((5/2) + 17/1000) + ((13/2) + 17/1000)
            + (19 + 17/1000) + (5 + 17/1000)) + 1/1000 :=
      step2 (a1 := 0) (a2 := 0) (a3 := 0) (a4 := 1) (c := 0)
        (hw 1 2 0) (hw 1 2 1) (hw 1 2 2) (hw 1 2 3) (hb 1 2) hp hq hr hs gP gQ gR gS
        (by norm_num) (by ring)
    have gW : |relu (relu (2*x1+3) - relu (x0+3/2) - relu (-x0-3/2) - 1)| ≤ 19 :=
      absrelu (by linarith [(abs_le.mp gR).2, relu_nonneg' (x0+3/2), relu_nonneg' (-x0-3/2)])
        (by norm_num)
    have gR2 : |relu (relu (2*x1+3))| ≤ 19 :=
      absrelu (by linarith [(abs_le.mp gR).2]) (by norm_num)
    have gS2 : |relu (relu (-2*x1-3))| ≤ 5 :=
      absrelu (by linarith [(abs_le.mp gS).2]) (by norm_num)
    have hY := step3 (a1 := -1) (a2 := 1) (a3 := 1) (c := 0)
        (T := -relu (relu (2*x1+3) - relu (x0+3/2) - relu (-x0-3/2) - 1)
          + relu (relu (2*x1+3)) + relu (relu (-2*x1-3)))
        (hw 2 0 0) (hw 2 0 1) (hw 2 0 2) (hb 2 0) hW hR2 hS2 gW gR2 gS2
        (by norm_num) (by norm_num) (by norm_num) (by ring)
    rw [ident] at hY
    exact le_trans hY (by norm_num)
end Lane4.Case
