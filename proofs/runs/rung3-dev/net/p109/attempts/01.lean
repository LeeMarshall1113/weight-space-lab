namespace Lane4.Case
open Lane4

def net : Net :=
  { hidden :=
      [ { W := [[0, 2], [0, 4], [4, 0], [0, 2]], b := [-1, -18, 16, 16] },
        { W := [[2, -1, 1, -4], [-4, 2, 0, 0], [0, 0, -2, 0]], b := [34, 32, 56] },
        { W := [[-2, -1, -1], [0, 0, 1/2]], b := [24, 0] } ],
    out := { W := [[-1/8, -1/4]], b := [0] } }

theorem aw (w W : ℝ) (h1 : -W ≤ w) (h2 : w ≤ W) : |w| ≤ W := abs_le.mpr ⟨h1, h2⟩

theorem aadd4 {a b c d A B C D : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) (hd : |d| ≤ D) :
    |a + b + c + d| ≤ A + B + C + D :=
  le_trans (abs_add_le _ _) (add_le_add (abs_add3_le ha hb hc) hd)

theorem aadd5 {a b c d e A B C D E : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) (he : |e| ≤ E) :
    |a + b + c + d + e| ≤ A + B + C + D + E :=
  le_trans (abs_add_le _ _) (add_le_add (aadd4 ha hb hc hd) he)

theorem lin2 {w0 w1 W0 W1 c d0 d1 dc v0 v1 u0 u1 t e0 e1 B0 B1 : ℝ}
    (hw0 : |w0| ≤ W0) (hw1 : |w1| ≤ W1)
    (hd0 : |d0| ≤ t) (hd1 : |d1| ≤ t) (hdc : |dc| ≤ t)
    (h0 : |u0 - v0| ≤ e0) (h1 : |u1 - v1| ≤ e1) (b0 : |v0| ≤ B0) (b1 : |v1| ≤ B1) :
    |((w0 + d0) * u0 + (w1 + d1) * u1 + (c + dc)) - (w0 * v0 + w1 * v1 + c)|
      ≤ (W0 * e0 + t * (B0 + e0)) + (W1 * e1 + t * (B1 + e1)) + t := by
  have p0 : |(w0 + d0) * u0 - w0 * v0| ≤ W0 * e0 + t * (B0 + e0) :=
    le_trans (pert_mul hd0 h0 b0)
      (by linarith [mul_le_mul_of_nonneg_right hw0 (le_trans (abs_nonneg _) h0)])
  have p1 : |(w1 + d1) * u1 - w1 * v1| ≤ W1 * e1 + t * (B1 + e1) :=
    le_trans (pert_mul hd1 h1 b1)
      (by linarith [mul_le_mul_of_nonneg_right hw1 (le_trans (abs_nonneg _) h1)])
  have e : ((w0 + d0) * u0 + (w1 + d1) * u1 + (c + dc)) - (w0 * v0 + w1 * v1 + c)
      = ((w0 + d0) * u0 - w0 * v0) + ((w1 + d1) * u1 - w1 * v1) + dc := by ring
  rw [e]
  exact abs_add3_le p0 p1 hdc

theorem lin3 {w0 w1 w2 W0 W1 W2 c d0 d1 d2 dc v0 v1 v2 u0 u1 u2 t e0 e1 e2 B0 B1 B2 : ℝ}
    (hw0 : |w0| ≤ W0) (hw1 : |w1| ≤ W1) (hw2 : |w2| ≤ W2)
    (hd0 : |d0| ≤ t) (hd1 : |d1| ≤ t) (hd2 : |d2| ≤ t) (hdc : |dc| ≤ t)
    (h0 : |u0 - v0| ≤ e0) (h1 : |u1 - v1| ≤ e1) (h2 : |u2 - v2| ≤ e2)
    (b0 : |v0| ≤ B0) (b1 : |v1| ≤ B1) (b2 : |v2| ≤ B2) :
    |((w0 + d0) * u0 + (w1 + d1) * u1 + (w2 + d2) * u2 + (c + dc))
        - (w0 * v0 + w1 * v1 + w2 * v2 + c)|
      ≤ (W0 * e0 + t * (B0 + e0)) + (W1 * e1 + t * (B1 + e1)) + (W2 * e2 + t * (B2 + e2)) + t := by
  have p0 : |(w0 + d0) * u0 - w0 * v0| ≤ W0 * e0 + t * (B0 + e0) :=
    le_trans (pert_mul hd0 h0 b0)
      (by linarith [mul_le_mul_of_nonneg_right hw0 (le_trans (abs_nonneg _) h0)])
  have p1 : |(w1 + d1) * u1 - w1 * v1| ≤ W1 * e1 + t * (B1 + e1) :=
    le_trans (pert_mul hd1 h1 b1)
      (by linarith [mul_le_mul_of_nonneg_right hw1 (le_trans (abs_nonneg _) h1)])
  have p2 : |(w2 + d2) * u2 - w2 * v2| ≤ W2 * e2 + t * (B2 + e2) :=
    le_trans (pert_mul hd2 h2 b2)
      (by linarith [mul_le_mul_of_nonneg_right hw2 (le_trans (abs_nonneg _) h2)])
  have e : ((w0 + d0) * u0 + (w1 + d1) * u1 + (w2 + d2) * u2 + (c + dc))
        - (w0 * v0 + w1 * v1 + w2 * v2 + c)
      = ((w0 + d0) * u0 - w0 * v0) + ((w1 + d1) * u1 - w1 * v1)
        + ((w2 + d2) * u2 - w2 * v2) + dc := by ring
  rw [e]
  exact aadd4 p0 p1 p2 hdc

theorem lin4 {w0 w1 w2 w3 W0 W1 W2 W3 c d0 d1 d2 d3 dc v0 v1 v2 v3 u0 u1 u2 u3 t
    e0 e1 e2 e3 B0 B1 B2 B3 : ℝ}
    (hw0 : |w0| ≤ W0) (hw1 : |w1| ≤ W1) (hw2 : |w2| ≤ W2) (hw3 : |w3| ≤ W3)
    (hd0 : |d0| ≤ t) (hd1 : |d1| ≤ t) (hd2 : |d2| ≤ t) (hd3 : |d3| ≤ t) (hdc : |dc| ≤ t)
    (h0 : |u0 - v0| ≤ e0) (h1 : |u1 - v1| ≤ e1) (h2 : |u2 - v2| ≤ e2) (h3 : |u3 - v3| ≤ e3)
    (b0 : |v0| ≤ B0) (b1 : |v1| ≤ B1) (b2 : |v2| ≤ B2) (b3 : |v3| ≤ B3) :
    |((w0 + d0) * u0 + (w1 + d1) * u1 + (w2 + d2) * u2 + (w3 + d3) * u3 + (c + dc))
        - (w0 * v0 + w1 * v1 + w2 * v2 + w3 * v3 + c)|
      ≤ (W0 * e0 + t * (B0 + e0)) + (W1 * e1 + t * (B1 + e1)) + (W2 * e2 + t * (B2 + e2))
        + (W3 * e3 + t * (B3 + e3)) + t := by
  have p0 : |(w0 + d0) * u0 - w0 * v0| ≤ W0 * e0 + t * (B0 + e0) :=
    le_trans (pert_mul hd0 h0 b0)
      (by linarith [mul_le_mul_of_nonneg_right hw0 (le_trans (abs_nonneg _) h0)])
  have p1 : |(w1 + d1) * u1 - w1 * v1| ≤ W1 * e1 + t * (B1 + e1) :=
    le_trans (pert_mul hd1 h1 b1)
      (by linarith [mul_le_mul_of_nonneg_right hw1 (le_trans (abs_nonneg _) h1)])
  have p2 : |(w2 + d2) * u2 - w2 * v2| ≤ W2 * e2 + t * (B2 + e2) :=
    le_trans (pert_mul hd2 h2 b2)
      (by linarith [mul_le_mul_of_nonneg_right hw2 (le_trans (abs_nonneg _) h2)])
  have p3 : |(w3 + d3) * u3 - w3 * v3| ≤ W3 * e3 + t * (B3 + e3) :=
    le_trans (pert_mul hd3 h3 b3)
      (by linarith [mul_le_mul_of_nonneg_right hw3 (le_trans (abs_nonneg _) h3)])
  have e : ((w0 + d0) * u0 + (w1 + d1) * u1 + (w2 + d2) * u2 + (w3 + d3) * u3 + (c + dc))
        - (w0 * v0 + w1 * v1 + w2 * v2 + w3 * v3 + c)
      = ((w0 + d0) * u0 - w0 * v0) + ((w1 + d1) * u1 - w1 * v1)
        + ((w2 + d2) * u2 - w2 * v2) + ((w3 + d3) * u3 - w3 * v3) + dc := by ring
  rw [e]
  exact aadd5 p0 p1 p2 p3 hdc

theorem rb {R a M : ℝ} (h : R = relu a) (ha : a ≤ M) (hM : 0 ≤ M) :
    0 ≤ R ∧ R ≤ M ∧ |R| ≤ M := by
  have h0 : 0 ≤ R := by rw [h]; exact relu_nonneg' a
  have h1 : R ≤ M := by rw [h]; exact relu_le_of_le ha hM
  exact ⟨h0, h1, by rw [abs_of_nonneg h0]; exact h1⟩

theorem rc' {R a : ℝ} (h : R = relu a) : (R = a ∧ 0 ≤ a) ∨ (R = 0 ∧ a ≤ 0) := by
  rcases le_total 0 a with ha | ha
  · left
    exact ⟨by rw [h]; exact relu_of_nonneg ha, ha⟩
  · right
    exact ⟨by rw [h]; exact relu_of_nonpos ha, ha⟩

theorem exact_id {x0 x1 A B P Q T U V Z C : ℝ}
    (l0 : -4 ≤ x0) (u0 : x0 ≤ 1) (l1 : -8 ≤ x1) (u1 : x1 ≤ 8)
    (hA : A = relu (0 * x0 + 2 * x1 + -1)) (hB : B = relu (0 * x0 + 4 * x1 + -18))
    (hP : P = relu (4 * x0 + 0 * x1 + 16)) (hQ : Q = relu (0 * x0 + 2 * x1 + 16))
    (hT : T = relu (2 * A + -1 * B + 1 * P + -4 * Q + 34))
    (hU : U = relu (-4 * A + 2 * B + 0 * P + 0 * Q + 32))
    (hV : V = relu (0 * A + 0 * B + -2 * P + 0 * Q + 56))
    (hZ : Z = relu (-2 * T + -1 * U + -1 * V + 24))
    (hC : C = relu (0 * T + 0 * U + 1/2 * V + 0)) :
    -1/8 * Z + -1/4 * C + 0 = spec x0 x1 := by
  have eP : P = 4 * x0 + 16 := by
    rw [hP, relu_of_nonneg (show (0:ℝ) ≤ 4 * x0 + 0 * x1 + 16 by linarith)]; ring
  have eQ : Q = 2 * x1 + 16 := by
    rw [hQ, relu_of_nonneg (show (0:ℝ) ≤ 0 * x0 + 2 * x1 + 16 by linarith)]; ring
  have eV : V = 24 - 8 * x0 := by
    rw [hV, eP, relu_of_nonneg
      (show (0:ℝ) ≤ 0 * A + 0 * B + -2 * (4 * x0 + 16) + 0 * Q + 56 by linarith)]; ring
  have eC : C = 12 - 4 * x0 := by
    rw [hC, eV, relu_of_nonneg
      (show (0:ℝ) ≤ 0 * T + 0 * U + 1/2 * (24 - 8 * x0) + 0 by linarith)]; ring
  rcases rc' hA with ⟨a1, a2⟩ | ⟨a1, a2⟩
  all_goals rcases rc' hB with ⟨b1, b2⟩ | ⟨b1, b2⟩
  all_goals try (exfalso; linarith)
  all_goals rcases rc' hU with ⟨c1, c2⟩ | ⟨c1, c2⟩
  all_goals try (exfalso; linarith)
  all_goals rcases rc' hT with ⟨d1, d2⟩ | ⟨d1, d2⟩
  all_goals try (exfalso; linarith)
  all_goals rcases rc' hZ with ⟨f1, f2⟩ | ⟨f1, f2⟩
  all_goals try (exfalso; linarith)
  all_goals (simp only [spec, max_def, min_def]; split_ifs <;> linarith)

theorem net_robust : StatementRobust net := by
  intro dW db hW x0 x1 l0 u0 l1 u1
  obtain ⟨hw, hb⟩ := hW
  have bx0 : |x0| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  have bx1 : |x1| ≤ 8 := abs_le.mpr ⟨by linarith, by linarith⟩
  have z0 : |x0 - x0| ≤ 0 := by simp
  have z1 : |x1 - x1| ≤ 0 := by simp
  obtain ⟨A, hA⟩ : ∃ v : ℝ, v = relu (0 * x0 + 2 * x1 + -1) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ v : ℝ, v = relu (0 * x0 + 4 * x1 + -18) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ v : ℝ, v = relu (4 * x0 + 0 * x1 + 16) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ v : ℝ, v = relu (0 * x0 + 2 * x1 + 16) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ v : ℝ, v = relu (2 * A + -1 * B + 1 * P + -4 * Q + 34) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ v : ℝ, v = relu (-4 * A + 2 * B + 0 * P + 0 * Q + 32) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ v : ℝ, v = relu (0 * A + 0 * B + -2 * P + 0 * Q + 56) := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ v : ℝ, v = relu (-2 * T + -1 * U + -1 * V + 24) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ v : ℝ, v = relu (0 * T + 0 * U + 1/2 * V + 0) := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ : ∃ v : ℝ,
      v = relu ((0 + dW 0 0 0) * x0 + (2 + dW 0 0 1) * x1 + (-1 + db 0 0)) := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ v : ℝ,
      v = relu ((0 + dW 0 1 0) * x0 + (4 + dW 0 1 1) * x1 + (-18 + db 0 1)) := ⟨_, rfl⟩
  obtain ⟨P', hP'⟩ : ∃ v : ℝ,
      v = relu ((4 + dW 0 2 0) * x0 + (0 + dW 0 2 1) * x1 + (16 + db 0 2)) := ⟨_, rfl⟩
  obtain ⟨Q', hQ'⟩ : ∃ v : ℝ,
      v = relu ((0 + dW 0 3 0) * x0 + (2 + dW 0 3 1) * x1 + (16 + db 0 3)) := ⟨_, rfl⟩
  obtain ⟨T', hT'⟩ : ∃ v : ℝ,
      v = relu ((2 + dW 1 0 0) * A' + (-1 + dW 1 0 1) * B' + (1 + dW 1 0 2) * P'
        + (-4 + dW 1 0 3) * Q' + (34 + db 1 0)) := ⟨_, rfl⟩
  obtain ⟨U', hU'⟩ : ∃ v : ℝ,
      v = relu ((-4 + dW 1 1 0) * A' + (2 + dW 1 1 1) * B' + (0 + dW 1 1 2) * P'
        + (0 + dW 1 1 3) * Q' + (32 + db 1 1)) := ⟨_, rfl⟩
  obtain ⟨V', hV'⟩ : ∃ v : ℝ,
      v = relu ((0 + dW 1 2 0) * A' + (0 + dW 1 2 1) * B' + (-2 + dW 1 2 2) * P'
        + (0 + dW 1 2 3) * Q' + (56 + db 1 2)) := ⟨_, rfl⟩
  obtain ⟨Z', hZ'⟩ : ∃ v : ℝ,
      v = relu ((-2 + dW 2 0 0) * T' + (-1 + dW 2 0 1) * U' + (-1 + dW 2 0 2) * V'
        + (24 + db 2 0)) := ⟨_, rfl⟩
  obtain ⟨C', hC'⟩ : ∃ v : ℝ,
      v = relu ((0 + dW 2 1 0) * T' + (0 + dW 2 1 1) * U' + (1/2 + dW 2 1 2) * V'
        + (0 + db 2 1)) := ⟨_, rfl⟩
  -- bounds on exact values
  obtain ⟨nA, uA, bA⟩ := rb (M := 15) hA (by linarith) (by norm_num)
  obtain ⟨nB, uB, bB⟩ := rb (M := 14) hB (by linarith) (by norm_num)
  obtain ⟨nP, uP, bP⟩ := rb (M := 20) hP (by linarith) (by norm_num)
  obtain ⟨nQ, uQ, bQ⟩ := rb (M := 32) hQ (by linarith) (by norm_num)
  obtain ⟨nT, uT, bT⟩ := rb (M := 84) hT (by linarith) (by norm_num)
  obtain ⟨nU, uU, bU⟩ := rb (M := 60) hU (by linarith) (by norm_num)
  obtain ⟨nV, uV, bV⟩ := rb (M := 56) hV (by linarith) (by norm_num)
  obtain ⟨nZ, uZ, bZ⟩ := rb (M := 24) hZ (by linarith) (by norm_num)
  obtain ⟨nC, uC, bC⟩ := rb (M := 28) hC (by linarith) (by norm_num)
  -- errors, layer 0
  have eA : |A' - A| ≤ 13/1000 := by
    rw [hA', hA]
    exact relu_pert (le_trans (lin2 (aw 0 0 (by norm_num) (by norm_num))
      (aw 2 2 (by norm_num) (by norm_num)) (hw 0 0 0) (hw 0 0 1) (hb 0 0) z0 z1 bx0 bx1)
      (by norm_num))
  have eB : |B' - B| ≤ 13/1000 := by
    rw [hB', hB]
    exact relu_pert (le_trans (lin2 (aw 0 0 (by norm_num) (by norm_num))
      (aw 4 4 (by norm_num) (by norm_num)) (hw 0 1 0) (hw 0 1 1) (hb 0 1) z0 z1 bx0 bx1)
      (by norm_num))
  have eP : |P' - P| ≤ 13/1000 := by
    rw [hP', hP]
    exact relu_pert (le_trans (lin2 (aw 4 4 (by norm_num) (by norm_num))
      (aw 0 0 (by norm_num) (by norm_num)) (hw 0 2 0) (hw 0 2 1) (hb 0 2) z0 z1 bx0 bx1)
      (by norm_num))
  have eQ : |Q' - Q| ≤ 13/1000 := by
    rw [hQ', hQ]
    exact relu_pert (le_trans (lin2 (aw 0 0 (by norm_num) (by norm_num))
      (aw 2 2 (by norm_num) (by norm_num)) (hw 0 3 0) (hw 0 3 1) (hb 0 3) z0 z1 bx0 bx1)
      (by norm_num))
  -- layer 1
  have eT : |T' - T| ≤ 187/1000 := by
    rw [hT', hT]
    exact relu_pert (le_trans (lin4 (aw 2 2 (by norm_num) (by norm_num))
      (aw (-1) 1 (by norm_num) (by norm_num)) (aw 1 1 (by norm_num) (by norm_num))
      (aw (-4) 4 (by norm_num) (by norm_num))
      (hw 1 0 0) (hw 1 0 1) (hw 1 0 2) (hw 1 0 3) (hb 1 0) eA eB eP eQ bA bB bP bQ)
      (by norm_num))
  have eU : |U' - U| ≤ 161/1000 := by
    rw [hU', hU]
    exact relu_pert (le_trans (lin4 (aw (-4) 4 (by norm_num) (by norm_num))
      (aw 2 2 (by norm_num) (by norm_num)) (aw 0 0 (by norm_num) (by norm_num))
      (aw 0 0 (by norm_num) (by norm_num))
      (hw 1 1 0) (hw 1 1 1) (hw 1 1 2) (hw 1 1 3) (hb 1 1) eA eB eP eQ bA bB bP bQ)
      (by norm_num))
  have eV : |V' - V| ≤ 109/1000 := by
    rw [hV', hV]
    exact relu_pert (le_trans (lin4 (aw 0 0 (by norm_num) (by norm_num))
      (aw 0 0 (by norm_num) (by norm_num)) (aw (-2) 2 (by norm_num) (by norm_num))
      (aw 0 0 (by norm_num) (by norm_num))
      (hw 1 2 0) (hw 1 2 1) (hw 1 2 2) (hw 1 2 3) (hb 1 2) eA eB eP eQ bA bB bP bQ)
      (by norm_num))
  -- layer 2
  have eZ : |Z' - Z| ≤ 846/1000 := by
    rw [hZ', hZ]
    exact relu_pert (le_trans (lin3 (aw (-2) 2 (by norm_num) (by norm_num))
      (aw (-1) 1 (by norm_num) (by norm_num)) (aw (-1) 1 (by norm_num) (by norm_num))
      (hw 2 0 0) (hw 2 0 1) (hw 2 0 2) (hb 2 0) eT eU eV bT bU bV)
      (by norm_num))
  have eC : |C' - C| ≤ 256/1000 := by
    rw [hC', hC]
    exact relu_pert (le_trans (lin3 (aw 0 0 (by norm_num) (by norm_num))
      (aw 0 0 (by norm_num) (by norm_num)) (aw (1/2) (1/2) (by norm_num) (by norm_num))
      (hw 2 1 0) (hw 2 1 1) (hw 2 1 2) (hb 2 1) eT eU eV bT bU bV)
      (by norm_num))
  have hev : net.evalP dW db [x0, x1]
      = [(-1/8 + dW 3 0 0) * Z' + (-1/4 + dW 3 0 1) * C' + (0 + db 3 0)] := by
    subst hC' hZ' hT' hU' hV' hA' hB' hP' hQ'
    first
      | (simp [net, Net.evalP, hiddenP, rowsP, dotP]; done)
      | (simp [net, Net.evalP, hiddenP, rowsP, dotP]; ring_nf; done)
      | ((conv_lhs => simp [net, Net.evalP, hiddenP, rowsP, dotP]); ring_nf; done)
      | (simp only [net, Net.evalP, hiddenP, rowsP, dotP, List.map_cons, List.map_nil,
          List.length_cons, List.length_nil]; push_cast; ring_nf; done)
  refine ⟨_, hev, ?_⟩
  have fin := lin2 (aw (-1/8) (1/8) (by norm_num) (by norm_num))
    (aw (-1/4) (1/4) (by norm_num) (by norm_num)) (hw 3 0 0) (hw 3 0 1) (hb 3 0)
    eZ eC bZ bC
  have idn := exact_id l0 u0 l1 u1 hA hB hP hQ hT hU hV hZ hC
  rw [← idn]
  exact le_trans fin (by norm_num)

end Lane4.Case
