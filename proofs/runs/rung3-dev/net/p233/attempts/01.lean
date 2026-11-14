namespace Lane4.Case
open Lane4

def net : Net :=
  { hidden := [ { W := [[0, 5], [0, 7], [2, 0], [0, -1]], b := [-8, 2, 2, 2] },
                { W := [[-2, 0, 2, 2], [0, 2, 0, 0], [2, 0, 0, 0], [0, 0, 0, 2]], b := [-10, 0, 0, 0] },
                { W := [[-1, 1, -1, 0], [0, 1, 0, 1]], b := [0, 0] } ],
    out := { W := [[-1/4, 1/4]], b := [0] } }

noncomputable def u2 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (l i : ℕ) (a0 a1 c x0 x1 : ℝ) : ℝ :=
  relu ((a0 + dW l i 0) * x0 + (a1 + dW l i 1) * x1 + (c + db l i))

noncomputable def u4 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (l i : ℕ) (a0 a1 a2 a3 c x0 x1 x2 x3 : ℝ) : ℝ :=
  relu ((a0 + dW l i 0) * x0 + ((a1 + dW l i 1) * x1 + ((a2 + dW l i 2) * x2 + (a3 + dW l i 3) * x3))
    + (c + db l i))

noncomputable def pR1 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ := u2 dW db 0 0 0 5 (-8) x0 x1
noncomputable def pQ1 (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ := u2 dW db 0 1 0 7 2 x0 x1
noncomputable def pW (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ := u2 dW db 0 2 2 0 2 x0 x1
noncomputable def pDD (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ := u2 dW db 0 3 0 (-1) 2 x0 x1
noncomputable def pT (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ :=
  u4 dW db 1 0 (-2) 0 2 2 (-10) (pR1 dW db x0 x1) (pQ1 dW db x0 x1) (pW dW db x0 x1) (pDD dW db x0 x1)
noncomputable def pQc (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ :=
  u4 dW db 1 1 0 2 0 0 0 (pR1 dW db x0 x1) (pQ1 dW db x0 x1) (pW dW db x0 x1) (pDD dW db x0 x1)
noncomputable def pRc (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ :=
  u4 dW db 1 2 2 0 0 0 0 (pR1 dW db x0 x1) (pQ1 dW db x0 x1) (pW dW db x0 x1) (pDD dW db x0 x1)
noncomputable def pDc (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ :=
  u4 dW db 1 3 0 0 0 2 0 (pR1 dW db x0 x1) (pQ1 dW db x0 x1) (pW dW db x0 x1) (pDD dW db x0 x1)
noncomputable def pS (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ :=
  u4 dW db 2 0 (-1) 1 (-1) 0 0 (pT dW db x0 x1) (pQc dW db x0 x1) (pRc dW db x0 x1) (pDc dW db x0 x1)
noncomputable def pQQ (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ :=
  u4 dW db 2 1 0 1 0 1 0 (pT dW db x0 x1) (pQc dW db x0 x1) (pRc dW db x0 x1) (pDc dW db x0 x1)
noncomputable def pY (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x0 x1 : ℝ) : ℝ :=
  (-1/4 + dW 3 0 0) * pS dW db x0 x1 + (1/4 + dW 3 0 1) * pQQ dW db x0 x1 + (0 + db 3 0)

-- exact (unperturbed) values
noncomputable def eR1 (x0 x1 : ℝ) : ℝ := relu (0 * x0 + 5 * x1 + (-8))
noncomputable def eQ1 (x0 x1 : ℝ) : ℝ := relu (0 * x0 + 7 * x1 + 2)
noncomputable def eW (x0 x1 : ℝ) : ℝ := relu (2 * x0 + 0 * x1 + 2)
noncomputable def eDD (x0 x1 : ℝ) : ℝ := relu (0 * x0 + (-1) * x1 + 2)
noncomputable def eT (x0 x1 : ℝ) : ℝ :=
  relu ((-2) * eR1 x0 x1 + 0 * eQ1 x0 x1 + 2 * eW x0 x1 + 2 * eDD x0 x1 + (-10))
noncomputable def eQc (x0 x1 : ℝ) : ℝ :=
  relu (0 * eR1 x0 x1 + 2 * eQ1 x0 x1 + 0 * eW x0 x1 + 0 * eDD x0 x1 + 0)
noncomputable def eRc (x0 x1 : ℝ) : ℝ :=
  relu (2 * eR1 x0 x1 + 0 * eQ1 x0 x1 + 0 * eW x0 x1 + 0 * eDD x0 x1 + 0)
noncomputable def eDc (x0 x1 : ℝ) : ℝ :=
  relu (0 * eR1 x0 x1 + 0 * eQ1 x0 x1 + 0 * eW x0 x1 + 2 * eDD x0 x1 + 0)
noncomputable def eS (x0 x1 : ℝ) : ℝ :=
  relu ((-1) * eT x0 x1 + 1 * eQc x0 x1 + (-1) * eRc x0 x1 + 0 * eDc x0 x1 + 0)
noncomputable def eQQ (x0 x1 : ℝ) : ℝ :=
  relu (0 * eT x0 x1 + 1 * eQc x0 x1 + 0 * eRc x0 x1 + 1 * eDc x0 x1 + 0)

theorem abs_add5_le' {a b c d e A B C D E : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) (he : |e| ≤ E) : |a + b + c + d + e| ≤ A + B + C + D + E :=
  abs_add3_le (abs_add3_le ha hb hc) hd he

theorem u2_err {dW : ℕ → ℕ → ℕ → ℝ} {db : ℕ → ℕ → ℝ}
    (hw : ∀ l i j, |dW l i j| ≤ 1/1000) (hb : ∀ l i, |db l i| ≤ 1/1000)
    (l i : ℕ) (a0 a1 c x0 x1 y0 y1 e0 e1 B0 B1 : ℝ)
    (h0 : |y0 - x0| ≤ e0) (h1 : |y1 - x1| ≤ e1) (b0 : |x0| ≤ B0) (b1 : |x1| ≤ B1) :
    |u2 dW db l i a0 a1 c y0 y1 - relu (a0 * x0 + a1 * x1 + c)|
      ≤ |a0| * e0 + |a1| * e1 + 1/1000 * ((B0 + e0) + (B1 + e1)) + 1/1000 := by
  unfold u2
  have t0 := pert_mul (a := a0) (hw l i 0) h0 b0
  have t1 := pert_mul (a := a1) (hw l i 1) h1 b1
  have key : (a0 + dW l i 0) * y0 + (a1 + dW l i 1) * y1 + (c + db l i) - (a0 * x0 + a1 * x1 + c)
      = ((a0 + dW l i 0) * y0 - a0 * x0) + ((a1 + dW l i 1) * y1 - a1 * x1) + db l i := by ring
  refine le_trans (relu_pert (e := |a0| * e0 + 1/1000 * (B0 + e0) + (|a1| * e1 + 1/1000 * (B1 + e1)) + 1/1000) ?_) (le_of_eq (by ring))
  rw [key]
  exact abs_add3_le t0 t1 (hb l i)

theorem u4_err {dW : ℕ → ℕ → ℕ → ℝ} {db : ℕ → ℕ → ℝ}
    (hw : ∀ l i j, |dW l i j| ≤ 1/1000) (hb : ∀ l i, |db l i| ≤ 1/1000)
    (l i : ℕ) (a0 a1 a2 a3 c x0 x1 x2 x3 y0 y1 y2 y3 e0 e1 e2 e3 B0 B1 B2 B3 : ℝ)
    (h0 : |y0 - x0| ≤ e0) (h1 : |y1 - x1| ≤ e1) (h2 : |y2 - x2| ≤ e2) (h3 : |y3 - x3| ≤ e3)
    (b0 : |x0| ≤ B0) (b1 : |x1| ≤ B1) (b2 : |x2| ≤ B2) (b3 : |x3| ≤ B3) :
    |u4 dW db l i a0 a1 a2 a3 c y0 y1 y2 y3 - relu (a0 * x0 + a1 * x1 + a2 * x2 + a3 * x3 + c)|
      ≤ |a0| * e0 + |a1| * e1 + |a2| * e2 + |a3| * e3
        + 1/1000 * ((B0 + e0) + (B1 + e1) + (B2 + e2) + (B3 + e3)) + 1/1000 := by
  unfold u4
  have t0 := pert_mul (a := a0) (hw l i 0) h0 b0
  have t1 := pert_mul (a := a1) (hw l i 1) h1 b1
  have t2 := pert_mul (a := a2) (hw l i 2) h2 b2
  have t3 := pert_mul (a := a3) (hw l i 3) h3 b3
  have key : (a0 + dW l i 0) * y0 + ((a1 + dW l i 1) * y1 + ((a2 + dW l i 2) * y2 + (a3 + dW l i 3) * y3))
      + (c + db l i) - (a0 * x0 + a1 * x1 + a2 * x2 + a3 * x3 + c)
      = ((a0 + dW l i 0) * y0 - a0 * x0) + ((a1 + dW l i 1) * y1 - a1 * x1)
        + ((a2 + dW l i 2) * y2 - a2 * x2) + ((a3 + dW l i 3) * y3 - a3 * x3) + db l i := by ring
  refine le_trans (relu_pert (e := (|a0| * e0 + 1/1000 * (B0 + e0)) + (|a1| * e1 + 1/1000 * (B1 + e1))
    + (|a2| * e2 + 1/1000 * (B2 + e2)) + (|a3| * e3 + 1/1000 * (B3 + e3)) + 1/1000) ?_)
    (le_of_eq (by ring))
  rw [key]
  exact abs_add5_le' t0 t1 t2 t3 (hb l i)

theorem o2_err {dW : ℕ → ℕ → ℕ → ℝ} {db : ℕ → ℕ → ℝ}
    (hw : ∀ l i j, |dW l i j| ≤ 1/1000) (hb : ∀ l i, |db l i| ≤ 1/1000)
    (l i : ℕ) (a0 a1 c x0 x1 y0 y1 e0 e1 B0 B1 : ℝ)
    (h0 : |y0 - x0| ≤ e0) (h1 : |y1 - x1| ≤ e1) (b0 : |x0| ≤ B0) (b1 : |x1| ≤ B1) :
    |(a0 + dW l i 0) * y0 + (a1 + dW l i 1) * y1 + (c + db l i) - (a0 * x0 + a1 * x1 + c)|
      ≤ |a0| * e0 + |a1| * e1 + 1/1000 * ((B0 + e0) + (B1 + e1)) + 1/1000 := by
  have t0 := pert_mul (a := a0) (hw l i 0) h0 b0
  have t1 := pert_mul (a := a1) (hw l i 1) h1 b1
  have key : (a0 + dW l i 0) * y0 + (a1 + dW l i 1) * y1 + (c + db l i) - (a0 * x0 + a1 * x1 + c)
      = ((a0 + dW l i 0) * y0 - a0 * x0) + ((a1 + dW l i 1) * y1 - a1 * x1) + db l i := by ring
  rw [key]
  refine le_trans (abs_add3_le t0 t1 (hb l i)) (le_of_eq (by ring))

theorem relu_abs_le {a B : ℝ} (h : a ≤ B) (hB : 0 ≤ B) : |relu a| ≤ B := by
  rw [abs_of_nonneg (relu_nonneg' a)]
  exact relu_le_of_le h hB

theorem rf2 {v a : ℝ} (h : v = relu a) : 0 ≤ v ∧ a ≤ v ∧ (v = 0 ∨ v = a) := by
  subst h
  unfold relu
  refine ⟨le_max_right _ _, le_max_left _ _, ?_⟩
  rcases le_total a 0 with h | h
  · left; exact max_eq_right h
  · right; exact max_eq_left h

theorem exact_facts (x0 x1 : ℝ) (l0 : -1 ≤ x0) (u0 : x0 ≤ 4) (l1 : -8 ≤ x1) (u1 : x1 ≤ 2) :
    eQQ x0 x1 ≤ 32 ∧ eS x0 x1 ≤ 32 ∧
      (-1/4) * eS x0 x1 + (1/4) * eQQ x0 x1 + 0 = spec x0 x1 := by
  have nR : 0 ≤ eR1 x0 x1 := relu_nonneg' _
  have nQ : 0 ≤ eQ1 x0 x1 := relu_nonneg' _
  have nD : 0 ≤ eDD x0 x1 := relu_nonneg' _
  have hW : eW x0 x1 = 2 * x0 + 2 := by
    unfold eW; rw [relu_of_nonneg (by linarith)]; ring
  have hD : eDD x0 x1 = 2 - x1 := by
    unfold eDD; rw [relu_of_nonneg (by linarith)]; ring
  have hQc : eQc x0 x1 = 2 * eQ1 x0 x1 := by
    unfold eQc; rw [relu_of_nonneg (by linarith)]; ring
  have hRc : eRc x0 x1 = 2 * eR1 x0 x1 := by
    unfold eRc; rw [relu_of_nonneg (by linarith)]; ring
  have hDc : eDc x0 x1 = 2 * eDD x0 x1 := by
    unfold eDc; rw [relu_of_nonneg (by linarith)]; ring
  have hQQ : eQQ x0 x1 = eQc x0 x1 + eDc x0 x1 := by
    unfold eQQ; rw [relu_of_nonneg (by linarith)]; ring
  have fR := rf2 (v := eR1 x0 x1) (a := 0 * x0 + 5 * x1 + (-8)) rfl
  have fQ := rf2 (v := eQ1 x0 x1) (a := 0 * x0 + 7 * x1 + 2) rfl
  have fT := rf2 (v := eT x0 x1)
    (a := (-2) * eR1 x0 x1 + 0 * eQ1 x0 x1 + 2 * eW x0 x1 + 2 * eDD x0 x1 + (-10)) rfl
  have fS := rf2 (v := eS x0 x1)
    (a := (-1) * eT x0 x1 + 1 * eQc x0 x1 + (-1) * eRc x0 x1 + 0 * eDc x0 x1 + 0) rfl
  obtain ⟨fR0, fR1, fR2⟩ := fR
  obtain ⟨fQ0, fQ1, fQ2⟩ := fQ
  obtain ⟨fT0, fT1, fT2⟩ := fT
  obtain ⟨fS0, fS1, fS2⟩ := fS
  refine ⟨?_, ?_, ?_⟩
  · rcases fQ2 with h | h <;> linarith
  · rcases fQ2 with h | h <;> rcases fR2 with h' | h' <;> rcases fT2 with h'' | h'' <;>
      rcases fS2 with h''' | h''' <;> linarith
  · simp only [spec, max_def, min_def]
    rcases fQ2 with h | h <;> rcases fR2 with h' | h' <;> rcases fT2 with h'' | h'' <;>
      rcases fS2 with h''' | h''' <;> split_ifs <;> linarith

theorem key (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ)
    (hw : ∀ l i j, |dW l i j| ≤ 1/1000) (hb : ∀ l i, |db l i| ≤ 1/1000)
    (x0 x1 : ℝ) (l0 : -1 ≤ x0) (u0 : x0 ≤ 4) (l1 : -8 ≤ x1) (u1 : x1 ≤ 2) :
    |pY dW db x0 x1 - spec x0 x1| ≤ 6/25 := by
  have bx0 : |x0| ≤ 4 := abs_le.mpr ⟨by linarith, u0⟩
  have bx1 : |x1| ≤ 8 := abs_le.mpr ⟨by linarith, by linarith⟩
  have nR : 0 ≤ eR1 x0 x1 := relu_nonneg' _
  have bR : |eR1 x0 x1| ≤ 2 := relu_abs_le (by linarith) (by norm_num)
  have bQ : |eQ1 x0 x1| ≤ 16 := relu_abs_le (by linarith) (by norm_num)
  have bW : |eW x0 x1| ≤ 10 := relu_abs_le (by linarith) (by norm_num)
  have bD : |eDD x0 x1| ≤ 10 := relu_abs_le (by linarith) (by norm_num)
  have bR' := abs_le.mp bR
  have bQ' := abs_le.mp bQ
  have bW' := abs_le.mp bW
  have bD' := abs_le.mp bD
  have bT : |eT x0 x1| ≤ 30 := relu_abs_le (by linarith) (by norm_num)
  have bQc : |eQc x0 x1| ≤ 32 := relu_abs_le (by linarith) (by norm_num)
  have bRc : |eRc x0 x1| ≤ 4 := relu_abs_le (by linarith) (by norm_num)
  have bDc : |eDc x0 x1| ≤ 20 := relu_abs_le (by linarith) (by norm_num)
  obtain ⟨fQQ, fSS, hid⟩ := exact_facts x0 x1 l0 u0 l1 u1
  have bS : |eS x0 x1| ≤ 32 := by
    rw [abs_of_nonneg (relu_nonneg' _)]; exact fSS
  have bQQ : |eQQ x0 x1| ≤ 32 := by
    rw [abs_of_nonneg (relu_nonneg' _)]; exact fQQ
  -- layer 1
  have g1 : |pR1 dW db x0 x1 - eR1 x0 x1| ≤ 13/1000 :=
    le_trans (u2_err hw hb 0 0 0 5 (-8) x0 x1 x0 x1 0 0 4 8 (by simp) (by simp) bx0 bx1)
      (by norm_num)
  have g2 : |pQ1 dW db x0 x1 - eQ1 x0 x1| ≤ 13/1000 :=
    le_trans (u2_err hw hb 0 1 0 7 2 x0 x1 x0 x1 0 0 4 8 (by simp) (by simp) bx0 bx1)
      (by norm_num)
  have g3 : |pW dW db x0 x1 - eW x0 x1| ≤ 13/1000 :=
    le_trans (u2_err hw hb 0 2 2 0 2 x0 x1 x0 x1 0 0 4 8 (by simp) (by simp) bx0 bx1)
      (by norm_num)
  have g4 : |pDD dW db x0 x1 - eDD x0 x1| ≤ 13/1000 :=
    le_trans (u2_err hw hb 0 3 0 (-1) 2 x0 x1 x0 x1 0 0 4 8 (by simp) (by simp) bx0 bx1)
      (by norm_num)
  -- layer 2
  have gT : |pT dW db x0 x1 - eT x0 x1| ≤ 118/1000 :=
    le_trans (u4_err hw hb 1 0 (-2) 0 2 2 (-10) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g1 g2 g3 g4 bR bQ bW bD)
      (by norm_num)
  have gQc : |pQc dW db x0 x1 - eQc x0 x1| ≤ 66/1000 :=
    le_trans (u4_err hw hb 1 1 0 2 0 0 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g1 g2 g3 g4 bR bQ bW bD)
      (by norm_num)
  have gRc : |pRc dW db x0 x1 - eRc x0 x1| ≤ 66/1000 :=
    le_trans (u4_err hw hb 1 2 2 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g1 g2 g3 g4 bR bQ bW bD)
      (by norm_num)
  have gDc : |pDc dW db x0 x1 - eDc x0 x1| ≤ 66/1000 :=
    le_trans (u4_err hw hb 1 3 0 0 0 2 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g1 g2 g3 g4 bR bQ bW bD)
      (by norm_num)
  -- layer 3
  have gS : |pS dW db x0 x1 - eS x0 x1| ≤ 338/1000 :=
    le_trans (u4_err hw hb 2 0 (-1) 1 (-1) 0 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gT gQc gRc gDc bT bQc bRc bDc)
      (by norm_num)
  have gQQ : |pQQ dW db x0 x1 - eQQ x0 x1| ≤ 220/1000 :=
    le_trans (u4_err hw hb 2 1 0 1 0 1 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gT gQc gRc gDc bT bQc bRc bDc)
      (by norm_num)
  -- output
  have gY := o2_err hw hb 3 0 (-1/4) (1/4) 0 _ _ _ _ _ _ _ _ gS gQQ bS bQQ
  rw [← hid]
  unfold pY
  refine le_trans gY ?_
  norm_num [abs_div]

theorem net_robust : StatementRobust net := by
  intro dW db hW x0 x1 l0 u0 l1 u1
  obtain ⟨hw, hb⟩ := hW
  refine ⟨pY dW db x0 x1, ?_, key dW db hw hb x0 x1 l0 u0 l1 u1⟩
  simp [net, Net.evalP, hiddenP, rowsP, dotP, pY, pS, pQQ, pT, pQc, pRc, pDc, pR1, pQ1, pW, pDD, u2, u4]
  try ring_nf

end Lane4.Case
