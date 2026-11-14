namespace Lane4.Case
open Lane4

def net : Net :=
  { hidden := [ { W := [[0, 1, 0], [3, 0, 0], [-2, 1, 0], [0, 0, 1], [1/2, -1, 1/2]],
                  b := [1, -3/2, -4, 2, 1] },
                { W := [[-3, -2, 1, -1/2, 1], [-3, -2, 1, 0, 0]], b := [5, 19] } ],
    out := { W := [[-1, 1]], b := [-12] } }

theorem unit3 {w0 w1 w2 c a0 a1 a2 d x0 x1 x2 E : ℝ}
    (ha0 : |a0| ≤ 1/1000) (ha1 : |a1| ≤ 1/1000) (ha2 : |a2| ≤ 1/1000) (hd : |d| ≤ 1/1000)
    (hx0 : |x0| ≤ 4) (hx1 : |x1| ≤ 4) (hx2 : |x2| ≤ 4)
    (hE : w0 * x0 + w1 * x1 + w2 * x2 + c = E) :
    |relu ((w0 + a0) * x0 + (w1 + a1) * x1 + (w2 + a2) * x2 + (c + d)) - relu E| ≤ 13/1000 := by
  subst hE
  apply relu_pert
  have h : (w0 + a0) * x0 + (w1 + a1) * x1 + (w2 + a2) * x2 + (c + d)
      - (w0 * x0 + w1 * x1 + w2 * x2 + c) = a0 * x0 + a1 * x1 + a2 * x2 + d := by ring
  rw [h]
  have t0 := abs_le.mp (pert_abs_mul ha0 hx0)
  have t1 := abs_le.mp (pert_abs_mul ha1 hx1)
  have t2 := abs_le.mp (pert_abs_mul ha2 hx2)
  have t3 := abs_le.mp hd
  rw [abs_le]
  constructor <;> linarith [t0.1, t0.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2]

theorem unit5 {w0 w1 w2 w3 w4 c g0 g1 g2 g3 g4 d H0 H1 H2 H3 H4 h0 h1 h2 h3 h4 E : ℝ}
    (hg0 : |g0| ≤ 1/1000) (hg1 : |g1| ≤ 1/1000) (hg2 : |g2| ≤ 1/1000)
    (hg3 : |g3| ≤ 1/1000) (hg4 : |g4| ≤ 1/1000) (hd : |d| ≤ 1/1000)
    (e0 : |H0 - h0| ≤ 13/1000) (e1 : |H1 - h1| ≤ 13/1000) (e2 : |H2 - h2| ≤ 13/1000)
    (e3 : |H3 - h3| ≤ 13/1000) (e4 : |H4 - h4| ≤ 13/1000)
    (b0 : |h0| ≤ 6) (b1 : |h1| ≤ 6) (b2 : |h2| ≤ 6) (b3 : |h3| ≤ 6) (b4 : |h4| ≤ 6)
    (hW : |w0| + |w1| + |w2| + |w3| + |w4| ≤ 15/2)
    (hE : w0 * h0 + w1 * h1 + w2 * h2 + w3 * h3 + w4 * h4 + c = E) :
    |relu ((w0 + g0) * H0 + (w1 + g1) * H1 + (w2 + g2) * H2 + (w3 + g3) * H3
        + (w4 + g4) * H4 + (c + d)) - relu E| ≤ 13/100 := by
  subst hE
  apply relu_pert
  have t0 := abs_le.mp (pert_mul (a := w0) hg0 e0 b0)
  have t1 := abs_le.mp (pert_mul (a := w1) hg1 e1 b1)
  have t2 := abs_le.mp (pert_mul (a := w2) hg2 e2 b2)
  have t3 := abs_le.mp (pert_mul (a := w3) hg3 e3 b3)
  have t4 := abs_le.mp (pert_mul (a := w4) hg4 e4 b4)
  have td := abs_le.mp hd
  have h : (w0 + g0) * H0 + (w1 + g1) * H1 + (w2 + g2) * H2 + (w3 + g3) * H3
        + (w4 + g4) * H4 + (c + d) - (w0 * h0 + w1 * h1 + w2 * h2 + w3 * h3 + w4 * h4 + c)
      = ((w0 + g0) * H0 - w0 * h0) + ((w1 + g1) * H1 - w1 * h1) + ((w2 + g2) * H2 - w2 * h2)
        + ((w3 + g3) * H3 - w3 * h3) + ((w4 + g4) * H4 - w4 * h4) + d := by ring
  rw [h, abs_le]
  constructor <;> linarith [t0.1, t0.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2, td.1, td.2]

theorem key {x0 x1 x2 H0 H1 H2 H3 H4 g00 g01 g02 g03 g04 k0 g10 g11 g12 g13 g14 k1 o0 o1 oc : ℝ}
    (hg00 : |g00| ≤ 1/1000) (hg01 : |g01| ≤ 1/1000) (hg02 : |g02| ≤ 1/1000)
    (hg03 : |g03| ≤ 1/1000) (hg04 : |g04| ≤ 1/1000) (hk0 : |k0| ≤ 1/1000)
    (hg10 : |g10| ≤ 1/1000) (hg11 : |g11| ≤ 1/1000) (hg12 : |g12| ≤ 1/1000)
    (hg13 : |g13| ≤ 1/1000) (hg14 : |g14| ≤ 1/1000) (hk1 : |k1| ≤ 1/1000)
    (ho0 : |o0| ≤ 1/1000) (ho1 : |o1| ≤ 1/1000) (hoc : |oc| ≤ 1/1000)
    (hH0 : |H0 - relu (x1 + 1)| ≤ 13/1000)
    (hH1 : |H1 - relu (3 * x0 - 3/2)| ≤ 13/1000)
    (hH2 : |H2 - relu (x1 - 2 * x0 - 4)| ≤ 13/1000)
    (hH3 : |H3 - relu (x2 + 2)| ≤ 13/1000)
    (hH4 : |H4 - relu (x0/2 - x1 + x2/2 + 1)| ≤ 13/1000)
    (l0 : -4 ≤ x0) (u0 : x0 ≤ 2) (l1 : -1 ≤ x1) (u1 : x1 ≤ 2) (l2 : -2 ≤ x2) (u2 : x2 ≤ 2) :
    |(-1 + o0) * relu ((-3 + g00) * H0 + (-2 + g01) * H1 + (1 + g02) * H2 + (-1/2 + g03) * H3
        + (1 + g04) * H4 + (5 + k0))
      + (1 + o1) * relu ((-3 + g10) * H0 + (-2 + g11) * H1 + (1 + g12) * H2 + (0 + g13) * H3
        + (0 + g14) * H4 + (19 + k1))
      + (-12 + oc) - spec x0 x1 x2| ≤ 3/4 := by
  have n1 := relu_nonneg' (3 * x0 - 3/2)
  have n2 := relu_nonneg' (x1 - 2 * x0 - 4)
  have n3 := relu_nonneg' (x0/2 - x1 + x2/2 + 1)
  have v1 : relu (3 * x0 - 3/2) ≤ 9/2 := relu_le_of_le (by linarith) (by norm_num)
  have v2 : relu (x1 - 2 * x0 - 4) ≤ 6 := relu_le_of_le (by linarith) (by norm_num)
  have v3 : relu (x0/2 - x1 + x2/2 + 1) ≤ 4 := relu_le_of_le (by linarith) (by norm_num)
  have ep : relu (x1 + 1) = x1 + 1 := relu_of_nonneg (by linarith)
  have es : relu (x2 + 2) = x2 + 2 := relu_of_nonneg (by linarith)
  rw [ep] at hH0
  rw [es] at hH3
  have s1 : max (x1 + (-1)) (3 * x0 + x1 + (-5/2)) = (x1 + (-1)) + relu (3 * x0 - 3/2) := by
    have := add_relu_sub (x1 + (-1)) (3 * x0 + x1 + (-5/2))
    have h : 3 * x0 + x1 + (-5/2) - (x1 + (-1)) = 3 * x0 - 3/2 := by ring
    rw [h] at this
    exact this.symm
  have s2 : min (x1 + (-2)) (2 * x0 + 2) = (x1 + (-2)) - relu (x1 - 2 * x0 - 4) := by
    have := sub_relu_sub (x1 + (-2)) (2 * x0 + 2)
    have h : x1 + (-2) - (2 * x0 + 2) = x1 - 2 * x0 - 4 := by ring
    rw [h] at this
    exact this.symm
  have s3 : min ((1/2) * x2 + 3) ((-1/2) * x0 + x1 + 2)
      = ((1/2) * x2 + 3) - relu (x0/2 - x1 + x2/2 + 1) := by
    have := sub_relu_sub ((1/2) * x2 + 3) ((-1/2) * x0 + x1 + 2)
    have h : (1/2) * x2 + 3 - ((-1/2) * x0 + x1 + 2) = x0/2 - x1 + x2/2 + 1 := by ring
    rw [h] at this
    exact this.symm
  generalize relu (3 * x0 - 3/2) = R1 at *
  generalize relu (x1 - 2 * x0 - 4) = R2 at *
  generalize relu (x0/2 - x1 + x2/2 + 1) = R3 at *
  have hs : spec x0 x1 x2 = (-3 * x1 + 4 - 2 * R1 + R2)
      - relu ((-3 * x1 + 4 - 2 * R1 + R2) - ((1/2) * x2 + 3 - R3)) := by
    rw [sub_relu_sub]
    unfold spec
    rw [s1, s2, s3]
    congr 1 <;> ring
  have b0 : |x1 + 1| ≤ 6 := abs_le.mpr ⟨by linarith, by linarith⟩
  have b1 : |R1| ≤ 6 := abs_le.mpr ⟨by linarith, by linarith⟩
  have b2 : |R2| ≤ 6 := abs_le.mpr ⟨by linarith, by linarith⟩
  have b3 : |x2 + 2| ≤ 6 := abs_le.mpr ⟨by linarith, by linarith⟩
  have b4 : |R3| ≤ 6 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hT := unit5 (w0 := -3) (w1 := -2) (w2 := 1) (w3 := -1/2) (w4 := 1) (c := 5)
    hg00 hg01 hg02 hg03 hg04 hk0 hH0 hH1 hH2 hH3 hH4 b0 b1 b2 b3 b4 (by norm_num)
    (E := (-3 * x1 + 4 - 2 * R1 + R2) - ((1/2) * x2 + 3 - R3)) (by ring)
  have ha := unit5 (w0 := -3) (w1 := -2) (w2 := 1) (w3 := 0) (w4 := 0) (c := 19)
    hg10 hg11 hg12 hg13 hg14 hk1 hH0 hH1 hH2 hH3 hH4 b0 b1 b2 b3 b4 (by norm_num)
    (E := -3 * x1 + 4 - 2 * R1 + R2 + 12) (by ring)
  have ea : relu (-3 * x1 + 4 - 2 * R1 + R2 + 12) = -3 * x1 + 4 - 2 * R1 + R2 + 12 :=
    relu_of_nonneg (by linarith)
  rw [ea] at ha
  have tq0 := relu_nonneg' ((-3 * x1 + 4 - 2 * R1 + R2) - ((1/2) * x2 + 3 - R3))
  have tq1 : relu ((-3 * x1 + 4 - 2 * R1 + R2) - ((1/2) * x2 + 3 - R3)) ≤ 30 :=
    relu_le_of_le (by linarith) (by norm_num)
  have hBt : |relu ((-3 * x1 + 4 - 2 * R1 + R2) - ((1/2) * x2 + 3 - R3))| ≤ 30 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hBa : |-3 * x1 + 4 - 2 * R1 + R2 + 12| ≤ 30 := abs_le.mpr ⟨by linarith, by linarith⟩
  have q0 := abs_le.mp (pert_mul (a := -1) ho0 hT hBt)
  have q1 := abs_le.mp (pert_mul (a := 1) ho1 ha hBa)
  have qc := abs_le.mp hoc
  have m1 : |(-1 : ℝ)| = 1 := by norm_num
  have m2 : |(1 : ℝ)| = 1 := abs_one
  rw [hs, abs_le]
  constructor <;> linarith [q0.1, q0.2, q1.1, q1.2, qc.1, qc.2]

theorem net_robust : StatementRobust net := by
  intro dW db hW x0 x1 x2 l0 u0 l1 u1 l2 u2
  obtain ⟨hw, hb⟩ := hW
  have bx0 : |x0| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  have bx1 : |x1| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  have bx2 : |x2| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  refine ⟨_, ?_, key (hw 1 0 0) (hw 1 0 1) (hw 1 0 2) (hw 1 0 3) (hw 1 0 4) (hb 1 0)
    (hw 1 1 0) (hw 1 1 1) (hw 1 1 2) (hw 1 1 3) (hw 1 1 4) (hb 1 1)
    (hw 2 0 0) (hw 2 0 1) (hb 2 0)
    (unit3 (w0 := 0) (w1 := 1) (w2 := 0) (c := 1) (hw 0 0 0) (hw 0 0 1) (hw 0 0 2) (hb 0 0)
      bx0 bx1 bx2 (by ring))
    (unit3 (w0 := 3) (w1 := 0) (w2 := 0) (c := -3/2) (hw 0 1 0) (hw 0 1 1) (hw 0 1 2) (hb 0 1)
      bx0 bx1 bx2 (by ring))
    (unit3 (w0 := -2) (w1 := 1) (w2 := 0) (c := -4) (hw 0 2 0) (hw 0 2 1) (hw 0 2 2) (hb 0 2)
      bx0 bx1 bx2 (by ring))
    (unit3 (w0 := 0) (w1 := 0) (w2 := 1) (c := 2) (hw 0 3 0) (hw 0 3 1) (hw 0 3 2) (hb 0 3)
      bx0 bx1 bx2 (by ring))
    (unit3 (w0 := 1/2) (w1 := -1) (w2 := 1/2) (c := 1) (hw 0 4 0) (hw 0 4 1) (hw 0 4 2) (hb 0 4)
      bx0 bx1 bx2 (by ring))
    l0 u0 l1 u1 l2 u2⟩
  simp [net, Net.evalP, hiddenP, rowsP, dotP]
  try ring_nf
end Lane4.Case
