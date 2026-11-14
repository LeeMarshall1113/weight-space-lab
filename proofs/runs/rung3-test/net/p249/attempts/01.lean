namespace Lane4.Case
open Lane4

def net : Net :=
  { hidden := [{ W := [[-3, 0], [-3, 0], [1, 0], [-1, 0], [0, 1/2], [0, -1/2]],
                 b := [-3/2, -2, 0, 0, 0, 0] },
               { W := [[-1, 1, -1, 1, -1, 1], [-1, 1, -1, 1, 0, 0], [1, -1, 1, -1, 0, 0]],
                 b := [3, 1, -1] }],
    out := { W := [[-1, 1, -1]], b := [0] } }

theorem unit2 {a b c d e g x0 x1 : ℝ} (hd : |d| ≤ 1/1000) (he : |e| ≤ 1/1000)
    (hg : |g| ≤ 1/1000) (bx0 : |x0| ≤ 4) (bx1 : |x1| ≤ 8) :
    |relu ((a + d) * x0 + (b + e) * x1 + (c + g)) - relu (a * x0 + b * x1 + c)| ≤ 13/1000 := by
  apply relu_pert
  have h : ((a + d) * x0 + (b + e) * x1 + (c + g)) - (a * x0 + b * x1 + c)
      = d * x0 + e * x1 + g := by ring
  rw [h]
  exact le_trans (abs_add3_le (pert_abs_mul hd bx0) (pert_abs_mul he bx1) hg) (by norm_num)

theorem term {w d h t e B : ℝ} (hw : |w| ≤ 1) (hd : |d| ≤ 1/1000) (he : |h - t| ≤ e)
    (hB : |t| ≤ B) : |(w + d) * h - w * t| ≤ e + 1/1000 * (B + e) := by
  have h1 := pert_mul (a := w) hd he hB
  have e0 : 0 ≤ e := le_trans (abs_nonneg _) he
  have h2 : |w| * e ≤ e := by nlinarith [mul_nonneg (sub_nonneg.2 hw) e0]
  linarith

theorem lin6 {w0 w1 w2 w3 w4 w5 d0 d1 d2 d3 d4 d5 h0 h1 h2 h3 h4 h5 t0 t1 t2 t3 t4 t5 c g : ℝ}
    (w0b : |w0| ≤ 1) (w1b : |w1| ≤ 1) (w2b : |w2| ≤ 1) (w3b : |w3| ≤ 1) (w4b : |w4| ≤ 1)
    (w5b : |w5| ≤ 1)
    (d0b : |d0| ≤ 1/1000) (d1b : |d1| ≤ 1/1000) (d2b : |d2| ≤ 1/1000) (d3b : |d3| ≤ 1/1000)
    (d4b : |d4| ≤ 1/1000) (d5b : |d5| ≤ 1/1000)
    (e0 : |h0 - t0| ≤ 13/1000) (e1 : |h1 - t1| ≤ 13/1000) (e2 : |h2 - t2| ≤ 13/1000)
    (e3 : |h3 - t3| ≤ 13/1000) (e4 : |h4 - t4| ≤ 13/1000) (e5 : |h5 - t5| ≤ 13/1000)
    (b0 : |t0| ≤ 5) (b1 : |t1| ≤ 5) (b2 : |t2| ≤ 5) (b3 : |t3| ≤ 5) (b4 : |t4| ≤ 5)
    (b5 : |t5| ≤ 5) (hg : |g| ≤ 1/1000) :
    |((w0 + d0) * h0 + (w1 + d1) * h1 + (w2 + d2) * h2 + (w3 + d3) * h3 + (w4 + d4) * h4
        + (w5 + d5) * h5 + (c + g))
      - (w0 * t0 + w1 * t1 + w2 * t2 + w3 * t3 + w4 * t4 + w5 * t5 + c)| ≤ 11/100 := by
  have k0 := abs_le.mp (term w0b d0b e0 b0)
  have k1 := abs_le.mp (term w1b d1b e1 b1)
  have k2 := abs_le.mp (term w2b d2b e2 b2)
  have k3 := abs_le.mp (term w3b d3b e3 b3)
  have k4 := abs_le.mp (term w4b d4b e4 b4)
  have k5 := abs_le.mp (term w5b d5b e5 b5)
  have g' := abs_le.mp hg
  rw [abs_le]
  constructor <;> nlinarith [k0.1, k0.2, k1.1, k1.2, k2.1, k2.2, k3.1, k3.2, k4.1, k4.2, k5.1, k5.2, g'.1, g'.2]

theorem lin3 {w0 w1 w2 d0 d1 d2 h0 h1 h2 t0 t1 t2 c g : ℝ}
    (w0b : |w0| ≤ 1) (w1b : |w1| ≤ 1) (w2b : |w2| ≤ 1)
    (d0b : |d0| ≤ 1/1000) (d1b : |d1| ≤ 1/1000) (d2b : |d2| ≤ 1/1000)
    (e0 : |h0 - t0| ≤ 11/100) (b0 : |t0| ≤ 9) (e1 : |h1 - t1| ≤ 11/100) (b1 : |t1| ≤ 3)
    (e2 : |h2 - t2| ≤ 11/100) (b2 : |t2| ≤ 7/2) (hg : |g| ≤ 1/1000) :
    |((w0 + d0) * h0 + (w1 + d1) * h1 + (w2 + d2) * h2 + (c + g))
      - (w0 * t0 + w1 * t1 + w2 * t2 + c)| ≤ 2/5 := by
  have k0 := abs_le.mp (term w0b d0b e0 b0)
  have k1 := abs_le.mp (term w1b d1b e1 b1)
  have k2 := abs_le.mp (term w2b d2b e2 b2)
  have g' := abs_le.mp hg
  rw [abs_le]
  constructor <;> nlinarith [k0.1, k0.2, k1.1, k1.2, k2.1, k2.2, g'.1, g'.2]

theorem exactpart {x0 x1 tA tB tP tN tU tV tR tFp tFm : ℝ}
    (l0 : -2 ≤ x0) (u0 : x0 ≤ 4) (l1 : -8 ≤ x1) (u1 : x1 ≤ 8)
    (hA : tA = relu ((-3) * x0 + 0 * x1 + (-3/2)))
    (hB : tB = relu ((-3) * x0 + 0 * x1 + (-2)))
    (hP : tP = relu (1 * x0 + 0 * x1 + 0))
    (hN : tN = relu ((-1) * x0 + 0 * x1 + 0))
    (hU : tU = relu (0 * x0 + (1/2) * x1 + 0))
    (hV : tV = relu (0 * x0 + (-1/2) * x1 + 0))
    (hR : tR = relu ((-1) * tA + 1 * tB + (-1) * tP + 1 * tN + (-1) * tU + 1 * tV + 3))
    (hFp : tFp = relu ((-1) * tA + 1 * tB + (-1) * tP + 1 * tN + 0 * tU + 0 * tV + 1))
    (hFm : tFm = relu (1 * tA + (-1) * tB + 1 * tP + (-1) * tN + 0 * tU + 0 * tV + (-1))) :
    |tA| ≤ 5 ∧ |tB| ≤ 5 ∧ |tP| ≤ 5 ∧ |tN| ≤ 5 ∧ |tU| ≤ 5 ∧ |tV| ≤ 5 ∧ |tR| ≤ 9 ∧ |tFp| ≤ 3
      ∧ |tFm| ≤ 7/2 ∧ tFp - tFm - tR = spec x0 x1 := by
  have eP : tP = relu x0 := by rw [hP]; congr 1; ring
  have eN : tN = relu (-x0) := by rw [hN]; congr 1; ring
  have eU : tU = relu ((1/2) * x1) := by rw [hU]; congr 1; ring
  have eV : tV = relu (-((1/2) * x1)) := by rw [hV]; congr 1; ring
  have hPN := relu_sub_relu_neg x0
  have hUV := relu_sub_relu_neg ((1/2) * x1)
  have nA : 0 ≤ tA := by rw [hA]; exact relu_nonneg' _
  have nB : 0 ≤ tB := by rw [hB]; exact relu_nonneg' _
  have nP : 0 ≤ tP := by rw [hP]; exact relu_nonneg' _
  have nN : 0 ≤ tN := by rw [hN]; exact relu_nonneg' _
  have nU : 0 ≤ tU := by rw [hU]; exact relu_nonneg' _
  have nV : 0 ≤ tV := by rw [hV]; exact relu_nonneg' _
  have sA : tA ≤ 9/2 := by rw [hA]; exact relu_le_of_le (by linarith) (by norm_num)
  have sB : tB ≤ 4 := by rw [hB]; exact relu_le_of_le (by linarith) (by norm_num)
  have sP : tP ≤ 4 := by rw [hP]; exact relu_le_of_le (by linarith) (by norm_num)
  have sN : tN ≤ 2 := by rw [hN]; exact relu_le_of_le (by linarith) (by norm_num)
  have sU : tU ≤ 4 := by rw [hU]; exact relu_le_of_le (by linarith) (by norm_num)
  have sV : tV ≤ 4 := by rw [hV]; exact relu_le_of_le (by linarith) (by norm_num)
  have hAB : 0 ≤ tA - tB ∧ tA - tB ≤ 1/2 := by
    rw [hA, hB]
    simp only [relu, max_def]
    split_ifs <;> constructor <;> linarith
  have hfm : max (min ((-1) * x0 + 1) ((-1) * x0 + (1/2)))
      (min (max ((-1) * x0 + 1) ((-1) * x0 + (1/2))) (2 * x0 + (5/2)))
      = -x0 + 1 - (tA - tB) := by
    rw [hA, hB]
    simp only [relu, max_def, min_def]
    split_ifs <;> linarith
  have hs : spec x0 x1 = min (-x0 + 1 - (tA - tB)) ((1/2) * x1 + (-2)) := by
    unfold spec; rw [hfm]
  have hFp' : (-1) * tA + 1 * tB + (-1) * tP + 1 * tN + 0 * tU + 0 * tV + 1
      = -x0 + 1 - (tA - tB) := by linarith
  have hFm' : 1 * tA + (-1) * tB + 1 * tP + (-1) * tN + 0 * tU + 0 * tV + (-1)
      = -(-x0 + 1 - (tA - tB)) := by linarith
  have hR' : (-1) * tA + 1 * tB + (-1) * tP + 1 * tN + (-1) * tU + 1 * tV + 3
      = (-x0 + 1 - (tA - tB)) - ((1/2) * x1 + (-2)) := by linarith
  rw [hFp'] at hFp
  rw [hFm'] at hFm
  rw [hR'] at hR
  have hf3 : -x0 + 1 - (tA - tB) ≤ 3 := by linarith [hAB.1]
  have hfl : -7/2 ≤ -x0 + 1 - (tA - tB) := by linarith [hAB.2]
  have pR : 0 ≤ tR ∧ tR ≤ 9 :=
    ⟨by rw [hR]; exact relu_nonneg' _, by rw [hR]; exact relu_le_of_le (by linarith) (by norm_num)⟩
  have pFp : 0 ≤ tFp ∧ tFp ≤ 3 :=
    ⟨by rw [hFp]; exact relu_nonneg' _, by rw [hFp]; exact relu_le_of_le hf3 (by norm_num)⟩
  have pFm : 0 ≤ tFm ∧ tFm ≤ 7/2 :=
    ⟨by rw [hFm]; exact relu_nonneg' _, by rw [hFm]; exact relu_le_of_le (by linarith) (by norm_num)⟩
  have h1 := relu_sub_relu_neg (-x0 + 1 - (tA - tB))
  have h2 := sub_relu_sub (-x0 + 1 - (tA - tB)) ((1/2) * x1 + (-2))
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩,
    abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩,
    abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩,
    abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩,
    abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
  rw [hs]
  linarith

theorem net_robust : StatementRobust net := by
  intro dW db hW x0 x1 l0 u0 l1 u1
  obtain ⟨hw, hb⟩ := hW
  have bx0 : |x0| ≤ 4 := abs_le.mpr ⟨by linarith, u0⟩
  have bx1 : |x1| ≤ 8 := abs_le.mpr ⟨by linarith, u1⟩
  obtain ⟨tA, hA⟩ : ∃ v : ℝ, v = relu ((-3) * x0 + 0 * x1 + (-3/2)) := ⟨_, rfl⟩
  obtain ⟨tB, hB⟩ : ∃ v : ℝ, v = relu ((-3) * x0 + 0 * x1 + (-2)) := ⟨_, rfl⟩
  obtain ⟨tP, hP⟩ : ∃ v : ℝ, v = relu (1 * x0 + 0 * x1 + 0) := ⟨_, rfl⟩
  obtain ⟨tN, hN⟩ : ∃ v : ℝ, v = relu ((-1) * x0 + 0 * x1 + 0) := ⟨_, rfl⟩
  obtain ⟨tU, hU⟩ : ∃ v : ℝ, v = relu (0 * x0 + (1/2) * x1 + 0) := ⟨_, rfl⟩
  obtain ⟨tV, hV⟩ : ∃ v : ℝ, v = relu (0 * x0 + (-1/2) * x1 + 0) := ⟨_, rfl⟩
  obtain ⟨tR, hR⟩ : ∃ v : ℝ,
      v = relu ((-1) * tA + 1 * tB + (-1) * tP + 1 * tN + (-1) * tU + 1 * tV + 3) := ⟨_, rfl⟩
  obtain ⟨tFp, hFp⟩ : ∃ v : ℝ,
      v = relu ((-1) * tA + 1 * tB + (-1) * tP + 1 * tN + 0 * tU + 0 * tV + 1) := ⟨_, rfl⟩
  obtain ⟨tFm, hFm⟩ : ∃ v : ℝ,
      v = relu (1 * tA + (-1) * tB + 1 * tP + (-1) * tN + 0 * tU + 0 * tV + (-1)) := ⟨_, rfl⟩
  obtain ⟨bA, bB, bP, bN, bU, bV, bR, bFp, bFm, hspec⟩ :=
    exactpart l0 u0 l1 u1 hA hB hP hN hU hV hR hFp hFm
  obtain ⟨H0, hH0⟩ : ∃ v : ℝ,
      v = relu ((-3 + dW 0 0 0) * x0 + (0 + dW 0 0 1) * x1 + (-3/2 + db 0 0)) := ⟨_, rfl⟩
  obtain ⟨H1, hH1⟩ : ∃ v : ℝ,
      v = relu ((-3 + dW 0 1 0) * x0 + (0 + dW 0 1 1) * x1 + (-2 + db 0 1)) := ⟨_, rfl⟩
  obtain ⟨H2, hH2⟩ : ∃ v : ℝ,
      v = relu ((1 + dW 0 2 0) * x0 + (0 + dW 0 2 1) * x1 + (0 + db 0 2)) := ⟨_, rfl⟩
  obtain ⟨H3, hH3⟩ : ∃ v : ℝ,
      v = relu ((-1 + dW 0 3 0) * x0 + (0 + dW 0 3 1) * x1 + (0 + db 0 3)) := ⟨_, rfl⟩
  obtain ⟨H4, hH4⟩ : ∃ v : ℝ,
      v = relu ((0 + dW 0 4 0) * x0 + (1/2 + dW 0 4 1) * x1 + (0 + db 0 4)) := ⟨_, rfl⟩
  obtain ⟨H5, hH5⟩ : ∃ v : ℝ,
      v = relu ((0 + dW 0 5 0) * x0 + (-1/2 + dW 0 5 1) * x1 + (0 + db 0 5)) := ⟨_, rfl⟩
  obtain ⟨G0, hG0⟩ : ∃ v : ℝ,
      v = relu ((-1 + dW 1 0 0) * H0 + (1 + dW 1 0 1) * H1 + (-1 + dW 1 0 2) * H2
        + (1 + dW 1 0 3) * H3 + (-1 + dW 1 0 4) * H4 + (1 + dW 1 0 5) * H5 + (3 + db 1 0)) :=
    ⟨_, rfl⟩
  obtain ⟨G1, hG1⟩ : ∃ v : ℝ,
      v = relu ((-1 + dW 1 1 0) * H0 + (1 + dW 1 1 1) * H1 + (-1 + dW 1 1 2) * H2
        + (1 + dW 1 1 3) * H3 + (0 + dW 1 1 4) * H4 + (0 + dW 1 1 5) * H5 + (1 + db 1 1)) :=
    ⟨_, rfl⟩
  obtain ⟨G2, hG2⟩ : ∃ v : ℝ,
      v = relu ((1 + dW 1 2 0) * H0 + (-1 + dW 1 2 1) * H1 + (1 + dW 1 2 2) * H2
        + (-1 + dW 1 2 3) * H3 + (0 + dW 1 2 4) * H4 + (0 + dW 1 2 5) * H5 + (-1 + db 1 2)) :=
    ⟨_, rfl⟩
  refine ⟨(-1 + dW 2 0 0) * G0 + (1 + dW 2 0 1) * G1 + (-1 + dW 2 0 2) * G2 + (0 + db 2 0),
    ?_, ?_⟩
  · subst hG0 hG1 hG2 hH0 hH1 hH2 hH3 hH4 hH5
    simp [net, Net.evalP, hiddenP, rowsP, dotP]
    try push_cast
    try ring_nf
  · have eH0 : |H0 - tA| ≤ 13/1000 := by
      rw [hH0, hA]; exact unit2 (hw 0 0 0) (hw 0 0 1) (hb 0 0) bx0 bx1
    have eH1 : |H1 - tB| ≤ 13/1000 := by
      rw [hH1, hB]; exact unit2 (hw 0 1 0) (hw 0 1 1) (hb 0 1) bx0 bx1
    have eH2 : |H2 - tP| ≤ 13/1000 := by
      rw [hH2, hP]; exact unit2 (hw 0 2 0) (hw 0 2 1) (hb 0 2) bx0 bx1
    have eH3 : |H3 - tN| ≤ 13/1000 := by
      rw [hH3, hN]; exact unit2 (hw 0 3 0) (hw 0 3 1) (hb 0 3) bx0 bx1
    have eH4 : |H4 - tU| ≤ 13/1000 := by
      rw [hH4, hU]; exact unit2 (hw 0 4 0) (hw 0 4 1) (hb 0 4) bx0 bx1
    have eH5 : |H5 - tV| ≤ 13/1000 := by
      rw [hH5, hV]; exact unit2 (hw 0 5 0) (hw 0 5 1) (hb 0 5) bx0 bx1
    have eG0 : |G0 - tR| ≤ 11/100 := by
      rw [hG0, hR]
      exact relu_pert (lin6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (hw 1 0 0) (hw 1 0 1) (hw 1 0 2) (hw 1 0 3) (hw 1 0 4)
        (hw 1 0 5) eH0 eH1 eH2 eH3 eH4 eH5 bA bB bP bN bU bV (hb 1 0))
    have eG1 : |G1 - tFp| ≤ 11/100 := by
      rw [hG1, hFp]
      exact relu_pert (lin6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (hw 1 1 0) (hw 1 1 1) (hw 1 1 2) (hw 1 1 3) (hw 1 1 4)
        (hw 1 1 5) eH0 eH1 eH2 eH3 eH4 eH5 bA bB bP bN bU bV (hb 1 1))
    have eG2 : |G2 - tFm| ≤ 11/100 := by
      rw [hG2, hFm]
      exact relu_pert (lin6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (hw 1 2 0) (hw 1 2 1) (hw 1 2 2) (hw 1 2 3) (hw 1 2 4)
        (hw 1 2 5) eH0 eH1 eH2 eH3 eH4 eH5 bA bB bP bN bU bV (hb 1 2))
    have hsp : spec x0 x1 = (-1) * tR + 1 * tFp + (-1) * tFm + 0 := by linarith
    rw [hsp]
    exact lin3 (by norm_num) (by norm_num) (by norm_num) (hw 2 0 0) (hw 2 0 1) (hw 2 0 2)
      eG0 bR eG1 bFp eG2 bFm (hb 2 0)

end Lane4.Case
