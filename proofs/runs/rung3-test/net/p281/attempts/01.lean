namespace Lane4.Case
open Lane4

def lyr1 : Layer := { W := [[-1, 4], [0, 1], [0, -1], [1, 0], [1/8, 0]], b := [7/2, 6, 3, -3, 1] }
def lyr2 : Layer := { W := [[-3, 3/2, 0, 0, 0], [0, 0, 3/2, 0, 0], [0, 0, 0, 3/2, 0], [0, 0, 0, 0, 4]], b := [0, 0, 0, 0] }
def lyr3 : Layer := { W := [[-1, 1, 0, 0], [1, -1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], b := [0, 0, 0, 0] }
def lyr4 : Layer := { W := [[2/3, 2/3, 2/3, -2], [0, 0, 0, 4]], b := [17/2, 0] }
def lyrO : Layer := { W := [[-1, -1/2]], b := [17/2] }
def net : Net := { hidden := [lyr1, lyr2, lyr3, lyr4], out := lyrO }

noncomputable def lay (L : Layer) (l : ℕ) (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x : List ℝ) : List ℝ :=
  (rowsP L.W L.b (dW l) (db l) x 0).map relu

theorem w_noise2 {a1 a2 c : ℚ} {A1 A2 C : ℝ}
    (hA1 : (a1:ℝ) = A1) (hA2 : (a2:ℝ) = A2) (hC : (c:ℝ) = C)
    {d : ℕ → ℝ} {dc y1 y2 M1 M2 : ℝ} (hd : ∀ k, |d k| ≤ 1/1000) (hdc : |dc| ≤ 1/1000)
    (h1 : |y1| ≤ M1) (h2 : |y2| ≤ M2) :
    |dotP [a1, a2] [y1, y2] d 0 + ((c:ℝ) + dc) - (A1 * y1 + A2 * y2 + C)| ≤ 1/1000 * (M1 + M2 + 1) := by
  subst hA1 hA2 hC
  have e : dotP [a1, a2] [y1, y2] d 0 = (((a1:ℝ) + d (0)) * y1 + (((a2:ℝ) + d (0+1)) * y2 + 0)) := rfl
  have p1 := abs_le.mp (pert_abs_mul (hd (0)) h1)
  have p2 := abs_le.mp (pert_abs_mul (hd (0+1)) h2)
  obtain ⟨p1l, p1u⟩ := p1
  obtain ⟨p2l, p2u⟩ := p2
  have key : ∀ u : ℝ, u = d (0) * y1 + d (0+1) * y2 + dc → |u| ≤ 1/1000 * (M1 + M2 + 1) := by
    intro u hu
    obtain ⟨q1, q2⟩ := abs_le.mp hdc
    rw [hu, abs_le]
    constructor <;> linarith
  apply key
  rw [e]
  ring

theorem w_noise4 {a1 a2 a3 a4 c : ℚ} {A1 A2 A3 A4 C : ℝ}
    (hA1 : (a1:ℝ) = A1) (hA2 : (a2:ℝ) = A2) (hA3 : (a3:ℝ) = A3) (hA4 : (a4:ℝ) = A4) (hC : (c:ℝ) = C)
    {d : ℕ → ℝ} {dc y1 y2 y3 y4 M1 M2 M3 M4 : ℝ} (hd : ∀ k, |d k| ≤ 1/1000) (hdc : |dc| ≤ 1/1000)
    (h1 : |y1| ≤ M1) (h2 : |y2| ≤ M2) (h3 : |y3| ≤ M3) (h4 : |y4| ≤ M4) :
    |dotP [a1, a2, a3, a4] [y1, y2, y3, y4] d 0 + ((c:ℝ) + dc) - (A1 * y1 + A2 * y2 + A3 * y3 + A4 * y4 + C)| ≤ 1/1000 * (M1 + M2 + M3 + M4 + 1) := by
  subst hA1 hA2 hA3 hA4 hC
  have e : dotP [a1, a2, a3, a4] [y1, y2, y3, y4] d 0 = (((a1:ℝ) + d (0)) * y1 + (((a2:ℝ) + d (0+1)) * y2 + (((a3:ℝ) + d (0+1+1)) * y3 + (((a4:ℝ) + d (0+1+1+1)) * y4 + 0)))) := rfl
  have p1 := abs_le.mp (pert_abs_mul (hd (0)) h1)
  have p2 := abs_le.mp (pert_abs_mul (hd (0+1)) h2)
  have p3 := abs_le.mp (pert_abs_mul (hd (0+1+1)) h3)
  have p4 := abs_le.mp (pert_abs_mul (hd (0+1+1+1)) h4)
  obtain ⟨p1l, p1u⟩ := p1
  obtain ⟨p2l, p2u⟩ := p2
  obtain ⟨p3l, p3u⟩ := p3
  obtain ⟨p4l, p4u⟩ := p4
  have key : ∀ u : ℝ, u = d (0) * y1 + d (0+1) * y2 + d (0+1+1) * y3 + d (0+1+1+1) * y4 + dc → |u| ≤ 1/1000 * (M1 + M2 + M3 + M4 + 1) := by
    intro u hu
    obtain ⟨q1, q2⟩ := abs_le.mp hdc
    rw [hu, abs_le]
    constructor <;> linarith
  apply key
  rw [e]
  ring

theorem w_noise5 {a1 a2 a3 a4 a5 c : ℚ} {A1 A2 A3 A4 A5 C : ℝ}
    (hA1 : (a1:ℝ) = A1) (hA2 : (a2:ℝ) = A2) (hA3 : (a3:ℝ) = A3) (hA4 : (a4:ℝ) = A4) (hA5 : (a5:ℝ) = A5) (hC : (c:ℝ) = C)
    {d : ℕ → ℝ} {dc y1 y2 y3 y4 y5 M1 M2 M3 M4 M5 : ℝ} (hd : ∀ k, |d k| ≤ 1/1000) (hdc : |dc| ≤ 1/1000)
    (h1 : |y1| ≤ M1) (h2 : |y2| ≤ M2) (h3 : |y3| ≤ M3) (h4 : |y4| ≤ M4) (h5 : |y5| ≤ M5) :
    |dotP [a1, a2, a3, a4, a5] [y1, y2, y3, y4, y5] d 0 + ((c:ℝ) + dc) - (A1 * y1 + A2 * y2 + A3 * y3 + A4 * y4 + A5 * y5 + C)| ≤ 1/1000 * (M1 + M2 + M3 + M4 + M5 + 1) := by
  subst hA1 hA2 hA3 hA4 hA5 hC
  have e : dotP [a1, a2, a3, a4, a5] [y1, y2, y3, y4, y5] d 0 = (((a1:ℝ) + d (0)) * y1 + (((a2:ℝ) + d (0+1)) * y2 + (((a3:ℝ) + d (0+1+1)) * y3 + (((a4:ℝ) + d (0+1+1+1)) * y4 + (((a5:ℝ) + d (0+1+1+1+1)) * y5 + 0))))) := rfl
  have p1 := abs_le.mp (pert_abs_mul (hd (0)) h1)
  have p2 := abs_le.mp (pert_abs_mul (hd (0+1)) h2)
  have p3 := abs_le.mp (pert_abs_mul (hd (0+1+1)) h3)
  have p4 := abs_le.mp (pert_abs_mul (hd (0+1+1+1)) h4)
  have p5 := abs_le.mp (pert_abs_mul (hd (0+1+1+1+1)) h5)
  obtain ⟨p1l, p1u⟩ := p1
  obtain ⟨p2l, p2u⟩ := p2
  obtain ⟨p3l, p3u⟩ := p3
  obtain ⟨p4l, p4u⟩ := p4
  obtain ⟨p5l, p5u⟩ := p5
  have key : ∀ u : ℝ, u = d (0) * y1 + d (0+1) * y2 + d (0+1+1) * y3 + d (0+1+1+1) * y4 + d (0+1+1+1+1) * y5 + dc → |u| ≤ 1/1000 * (M1 + M2 + M3 + M4 + M5 + 1) := by
    intro u hu
    obtain ⟨q1, q2⟩ := abs_le.mp hdc
    rw [hu, abs_le]
    constructor <;> linarith
  apply key
  rw [e]
  ring

theorem w_pe {r P Q E : ℝ} (hr : r = relu P) (h : |P - Q| ≤ E) : |r - relu Q| ≤ E := by
  rw [hr]
  exact relu_pert h

theorem w_rp {a b : ℝ} (h : 0 ≤ a) (e : a = b) : relu a = b := by
  rw [relu_of_nonneg h]
  exact e

theorem w_minlip {a b c d e : ℝ} (h1 : |a - c| ≤ e) (h2 : |b - d| ≤ e) :
    |min a b - min c d| ≤ e := by
  rw [abs_le] at h1 h2 ⊢
  obtain ⟨h1l, h1u⟩ := h1
  obtain ⟨h2l, h2u⟩ := h2
  rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd
  · rw [min_eq_left hab, min_eq_left hcd]
    exact ⟨by linarith, by linarith⟩
  · rw [min_eq_left hab, min_eq_right hcd]
    exact ⟨by linarith, by linarith⟩
  · rw [min_eq_right hab, min_eq_left hcd]
    exact ⟨by linarith, by linarith⟩
  · rw [min_eq_right hab, min_eq_right hcd]
    exact ⟨by linarith, by linarith⟩

theorem w_sum {P0 P1 b0 b1 b2 b3 y0 y1 e0 e1 pw E : ℝ}
    (n0 : |P0 - ((-1) * b0 + 1 * b1 + 0 * b2 + 0 * b3 + 0)| ≤ pw)
    (n1 : |P1 - (1 * b0 + (-1) * b1 + 0 * b2 + 0 * b3 + 0)| ≤ pw)
    (f0 : |b0 - y0| ≤ e0) (f1 : |b1 - y1| ≤ e1) (hE : e0 + e1 + 2 * pw ≤ E) :
    |relu P0 + relu P1 - |y1 - y0|| ≤ E := by
  have h0 : |relu P0 - relu (b1 - b0)| ≤ pw := by
    apply relu_pert
    have e : P0 - (b1 - b0) = P0 - ((-1) * b0 + 1 * b1 + 0 * b2 + 0 * b3 + 0) := by ring
    rw [e]
    exact n0
  have h1 : |relu P1 - relu (-(b1 - b0))| ≤ pw := by
    apply relu_pert
    have e : P1 - (-(b1 - b0)) = P1 - (1 * b0 + (-1) * b1 + 0 * b2 + 0 * b3 + 0) := by ring
    rw [e]
    exact n1
  have h2 : relu (b1 - b0) + relu (-(b1 - b0)) = |b1 - b0| := relu_add_relu_neg _
  have h3 := abs_sub_abs_le_abs_sub (b1 - b0) (y1 - y0)
  have h3' := abs_sub_abs_le_abs_sub (y1 - y0) (b1 - b0)
  obtain ⟨f0l, f0u⟩ := abs_le.mp f0
  obtain ⟨f1l, f1u⟩ := abs_le.mp f1
  have h4 : |(b1 - b0) - (y1 - y0)| ≤ e0 + e1 := by
    rw [abs_le]
    constructor <;> linarith
  have h4' : |(y1 - y0) - (b1 - b0)| ≤ e0 + e1 := by
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨h0l, h0u⟩ := abs_le.mp h0
  obtain ⟨h1l, h1u⟩ := abs_le.mp h1
  rw [abs_le]
  constructor <;> linarith

theorem w_s01 {y0 y1 y2 y3 s0 s1 : ℝ}
    (h0 : s0 = relu ((-1) * y0 + 1 * y1 + 0 * y2 + 0 * y3 + 0))
    (h1 : s1 = relu (1 * y0 + (-1) * y1 + 0 * y2 + 0 * y3 + 0)) :
    s0 + s1 = |y1 - y0| := by
  have e0 : (-1) * y0 + 1 * y1 + 0 * y2 + 0 * y3 + 0 = y1 - y0 := by ring
  have e1 : 1 * y0 + (-1) * y1 + 0 * y2 + 0 * y3 + 0 = -(y1 - y0) := by ring
  rw [h0, h1, e0, e1]
  exact relu_add_relu_neg _

theorem w_z3 {x0 x1 z3 : ℝ} (h : z3 = relu (1 * x0 + 0 * x1 + (-3))) :
    z3 = 2 * max ((1/2) * x0 + (-3/2)) 0 := by
  rw [h]
  unfold relu
  simp only [max_def]
  split_ifs <;> linarith

theorem w_med {x0 x1 z0 z1 y0 y1 : ℝ} (h1 : -4 ≤ x1) (h2 : x1 ≤ 1)
    (hz0 : z0 = relu ((-1) * x0 + 4 * x1 + 7/2)) (hz1 : z1 = x1 + 6)
    (hy0 : y0 = relu ((-3) * z0 + (3/2) * z1)) (hy1 : y1 = 9/2 - (3/2) * x1) :
    y1 - y0 = 3 * max (min ((-1) * x1 + (-3/2)) ((-1/2) * x1 + (3/2)))
      (min (max ((-1) * x1 + (-3/2)) ((-1/2) * x1 + (3/2))) ((-1) * x0 + 3 * x1 + 2)) := by
  subst hy0 hy1 hz1 hz0
  unfold relu
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem w_spec_eq {x0 x1 R med : ℝ} (hR : R = max ((1/2) * x0 + (-3/2)) 0)
    (hm : med = max (min ((-1) * x1 + (-3/2)) ((-1/2) * x1 + (3/2)))
      (min (max ((-1) * x1 + (-3/2)) ((-1/2) * x1 + (3/2))) ((-1) * x0 + 3 * x1 + 2))) :
    spec x0 x1 = min ((-2) * R + (-2) * |med|) ((-1) * x0 + (1/2)) := by
  subst hR hm
  rfl

theorem w_fin {Y P0 P1 d0 d1 c0 c1 c2 c3 s0 s1 s2 s3 A B PI4 PIO ES E32 E33 EM : ℝ}
    (hd0 : d0 = relu P0) (hd1 : d1 = relu P1)
    (hP0 : |P0 - ((2/3) * c0 + (2/3) * c1 + (2/3) * c2 + (-2) * c3 + 17/2)| ≤ PI4)
    (hP1 : |P1 - (0 * c0 + 0 * c1 + 0 * c2 + 4 * c3 + 0)| ≤ PI4)
    (hY : |Y - ((-1) * d0 + (-1/2) * d1 + 17/2)| ≤ PIO)
    (hc3 : 0 ≤ c3)
    (hS : |c0 + c1 - (s0 + s1)| ≤ ES) (h2 : |c2 - s2| ≤ E32) (h3 : |c3 - s3| ≤ E33)
    (hA : A = -((2/3) * (s0 + s1 + s2))) (hB : B = 17/2 - 2 * s3)
    (hN : PI4 / 2 + EM + PIO ≤ 1/2) (hN1 : PI4 + (2/3) * (ES + E32) ≤ EM)
    (hN2 : 2 * E33 ≤ EM) :
    |Y - min A B| ≤ 1/2 := by
  subst hA hB
  have hr4 : relu (4 * c3) = 4 * c3 := relu_of_nonneg (by linarith)
  have hd1' : |d1 - 4 * c3| ≤ PI4 := by
    rw [hd1]
    have hh : |P1 - 4 * c3| ≤ PI4 := by
      have e : P1 - 4 * c3 = P1 - (0 * c0 + 0 * c1 + 0 * c2 + 4 * c3 + 0) := by ring
      rw [e]
      exact hP1
    have h5 := relu_pert hh
    rw [hr4] at h5
    exact h5
  have hmin : 17/2 - 2 * c3 - d0 = min (-(P0 - (17/2 - 2 * c3))) (17/2 - 2 * c3) := by
    have h5 := sub_relu_sub (17/2 - 2 * c3) (-(P0 - (17/2 - 2 * c3)))
    have e : (17/2 - 2 * c3) - (-(P0 - (17/2 - 2 * c3))) = P0 := by ring
    rw [e] at h5
    rw [hd0, h5, min_comm]
  obtain ⟨p0l, p0u⟩ := abs_le.mp hP0
  obtain ⟨sl, su⟩ := abs_le.mp hS
  obtain ⟨l2, u2⟩ := abs_le.mp h2
  obtain ⟨l3, u3⟩ := abs_le.mp h3
  have hl : |(-(P0 - (17/2 - 2 * c3))) - (-((2/3) * (s0 + s1 + s2)))| ≤ EM := by
    rw [abs_le]
    constructor <;> linarith
  have hr : |(17/2 - 2 * c3) - (17/2 - 2 * s3)| ≤ EM := by
    rw [abs_le]
    constructor <;> linarith
  have hm := w_minlip hl hr
  obtain ⟨ml, mu⟩ := abs_le.mp hm
  obtain ⟨yl, yu⟩ := abs_le.mp hY
  obtain ⟨dl, du⟩ := abs_le.mp hd1'
  rw [abs_le]
  constructor <;> linarith

theorem w_lay1 {dW : ℕ → ℕ → ℕ → ℝ} {db : ℕ → ℕ → ℝ} (hw : ∀ l i j, |dW l i j| ≤ 1/1000)
    (hb : ∀ l i, |db l i| ≤ 1/1000) (l : ℕ) {y0 y1 : ℝ}
    (m0 : |y0| ≤ 8) (m1 : |y1| ≤ 4) :
    ∃ r0 r1 r2 r3 r4 P0 P1 P2 P3 P4 : ℝ, lay lyr1 l dW db [y0, y1] = [r0, r1, r2, r3, r4] ∧
      r0 = relu P0 ∧ r1 = relu P1 ∧ r2 = relu P2 ∧ r3 = relu P3 ∧ r4 = relu P4 ∧
      |P0 - ((-1) * y0 + 4 * y1 + (7/2))| ≤ 13/1000 ∧ |P1 - (0 * y0 + 1 * y1 + 6)| ≤ 13/1000 ∧ |P2 - (0 * y0 + (-1) * y1 + 3)| ≤ 13/1000 ∧ |P3 - (1 * y0 + 0 * y1 + (-3))| ≤ 13/1000 ∧ |P4 - ((1/8) * y0 + 0 * y1 + 1)| ≤ 13/1000 := by
  refine ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (w_noise2 (by norm_num) (by norm_num) (by norm_num) (fun k => hw _ _ k) (hb _ _) m0 m1) (by norm_num)
  · exact le_trans (w_noise2 (by norm_num) (by norm_num) (by norm_num) (fun k => hw _ _ k) (hb _ _) m0 m1) (by norm_num)
  · exact le_trans (w_noise2 (by norm_num) (by norm_num) (by norm_num) (fun k => hw _ _ k) (hb _ _) m0 m1) (by norm_num)
  · exact le_trans (w_noise2 (by norm_num) (by norm_num) (by norm_num) (fun k => hw _ _ k) (hb _ _) m0 m1) (by norm_num)
  · exact le_trans (w_noise2 (by norm_num) (by norm_num) (by norm_num) (fun k => hw _ _ k) (hb _ _) m0 m1) (by norm_num)

theorem w_lay2 {dW : ℕ → ℕ → ℕ → ℝ} {db : ℕ → ℕ → ℝ} (hw : ∀ l i j, |dW l i j| ≤ 1/1000)
    (hb : ∀ l i, |db l i| ≤ 1/1000) (l : ℕ) {y0 y1 y2 y3 y4 : ℝ}
    (m0 : |y0| ≤ 15513/1000) (m1 : |y1| ≤ 7013/1000) (m2 : |y2| ≤ 7013/1000) (m3 : |y3| ≤ 5013/1000) (m4 : |y4| ≤ 2013/1000) :
    ∃ r0 r1 r2 r3 P0 P1 P2 P3 : ℝ, lay lyr2 l dW db [y0, y1, y2, y3, y4] = [r0, r1, r2, r3] ∧
      r0 = relu P0 ∧ r1 = relu P1 ∧ r2 = relu P2 ∧ r3 = relu P3 ∧
      |P0 - ((-3) * y0 + (3/2) * y1 + 0 * y2 + 0 * y3 + 0 * y4 + 0)| ≤ 47/1250 ∧ |P1 - (0 * y0 + 0 * y1 + (3/2) * y2 + 0 * y3 + 0 * y4 + 0)| ≤ 47/1250 ∧ |P2 - (0 * y0 + 0 * y1 + 0 * y2 + (3/2) * y3 + 0 * y4 + 0)| ≤ 47/1250 ∧ |P3 - (0 * y0 + 0 * y1 + 0 * y2 + 0 * y3 + 4 * y4 + 0)| ≤ 47/1250 := by
  refine ⟨_, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact le_trans (w_noise5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun k => hw _ _ k) (hb _ _) m0 m1 m2 m3 m4) (by norm_num)
  · exact le_trans (w_noise5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun k => hw _ _ k) (hb _ _) m0 m1 m2 m3 m4) (by norm_num)
  · exact le_trans (w_noise5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun k => hw _ _ k) (hb _ _) m0 m1 m2 m3 m4) (by norm_num)
  · exact le_trans (w_noise5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun k => hw _ _ k) (hb _ _) m0 m1 m2 m3 m4) (by norm_num)

theorem w_lay3 {dW : ℕ → ℕ → ℕ → ℝ} {db : ℕ → ℕ → ℝ} (hw : ∀ l i j, |dW l i j| ≤ 1/1000)
    (hb : ∀ l i, |db l i| ≤ 1/1000) (l : ℕ) {y0 y1 y2 y3 : ℝ}
    (m0 : |y0| ≤ 105961/10000) (m1 : |y1| ≤ 105571/10000) (m2 : |y2| ≤ 75571/10000) (m3 : |y3| ≤ 5056/625) :
    ∃ r0 r1 r2 r3 P0 P1 P2 P3 : ℝ, lay lyr3 l dW db [y0, y1, y2, y3] = [r0, r1, r2, r3] ∧
      r0 = relu P0 ∧ r1 = relu P1 ∧ r2 = relu P2 ∧ r3 = relu P3 ∧
      |P0 - ((-1) * y0 + 1 * y1 + 0 * y2 + 0 * y3 + 0)| ≤ 189/5000 ∧ |P1 - (1 * y0 + (-1) * y1 + 0 * y2 + 0 * y3 + 0)| ≤ 189/5000 ∧ |P2 - (0 * y0 + 0 * y1 + 1 * y2 + 0 * y3 + 0)| ≤ 189/5000 ∧ |P3 - (0 * y0 + 0 * y1 + 0 * y2 + 1 * y3 + 0)| ≤ 189/5000 := by
  refine ⟨_, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact le_trans (w_noise4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun k => hw _ _ k) (hb _ _) m0 m1 m2 m3) (by norm_num)
  · exact le_trans (w_noise4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun k => hw _ _ k) (hb _ _) m0 m1 m2 m3) (by norm_num)
  · exact le_trans (w_noise4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun k => hw _ _ k) (hb _ _) m0 m1 m2 m3) (by norm_num)
  · exact le_trans (w_noise4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun k => hw _ _ k) (hb _ _) m0 m1 m2 m3) (by norm_num)

theorem w_lay4 {dW : ℕ → ℕ → ℕ → ℝ} {db : ℕ → ℕ → ℝ} (hw : ∀ l i j, |dW l i j| ≤ 1/1000)
    (hb : ∀ l i, |db l i| ≤ 1/1000) (l : ℕ) {y0 y1 y2 y3 : ℝ}
    (m0 : |y0| ≤ 10691/1000) (m1 : |y1| ≤ 10691/1000) (m2 : |y2| ≤ 75949/10000) (m3 : |y3| ≤ 40637/5000) :
    ∃ r0 r1 P0 P1 : ℝ, lay lyr4 l dW db [y0, y1, y2, y3] = [r0, r1] ∧
      r0 = relu P0 ∧ r1 = relu P1 ∧
      |P0 - ((2/3) * y0 + (2/3) * y1 + (2/3) * y2 + (-2) * y3 + (17/2))| ≤ 191/5000 ∧ |P1 - (0 * y0 + 0 * y1 + 0 * y2 + 4 * y3 + 0)| ≤ 191/5000 := by
  refine ⟨_, _, _, _, rfl, rfl, rfl, ?_, ?_⟩
  · exact le_trans (w_noise4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun k => hw _ _ k) (hb _ _) m0 m1 m2 m3) (by norm_num)
  · exact le_trans (w_noise4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun k => hw _ _ k) (hb _ _) m0 m1 m2 m3) (by norm_num)

theorem w_out {dW : ℕ → ℕ → ℕ → ℝ} {db : ℕ → ℕ → ℝ} (hw : ∀ l i j, |dW l i j| ≤ 1/1000)
    (hb : ∀ l i, |db l i| ≤ 1/1000) (l : ℕ) {d0 d1 : ℝ}
    (m0 : |d0| ≤ 21111/1000) (m1 : |d1| ≤ 162739/5000) :
    ∃ Y : ℝ, rowsP lyrO.W lyrO.b (dW l) (db l) [d0, d1] 0 = [Y] ∧
      |Y - ((-1) * d0 + (-1/2) * d1 + 17/2)| ≤ 547/10000 := by
  refine ⟨_, rfl, ?_⟩
  exact le_trans (w_noise2 (by norm_num) (by norm_num) (by norm_num) (fun k => hw _ _ k) (hb _ _) m0 m1) (by norm_num)

theorem net_robust : StatementRobust net := by
  intro dW db hW x0 x1 l0 u0 l1 u1
  obtain ⟨hw, hb⟩ := hW
  have hx0 : |x0| ≤ 8 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hx1 : |x1| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨z0, hz0⟩ : ∃ z : ℝ, z = relu ((-1) * x0 + 4 * x1 + (7/2)) := ⟨_, rfl⟩
  have bz0l : 0 ≤ z0 := by rw [hz0]; exact relu_nonneg' _
  have bz0u : z0 ≤ 31/2 := by rw [hz0]; exact relu_le_of_le (by linarith) (by norm_num)
  obtain ⟨z1, hz1⟩ : ∃ z : ℝ, z = relu (0 * x0 + 1 * x1 + 6) := ⟨_, rfl⟩
  have bz1l : 0 ≤ z1 := by rw [hz1]; exact relu_nonneg' _
  have bz1u : z1 ≤ 7 := by rw [hz1]; exact relu_le_of_le (by linarith) (by norm_num)
  obtain ⟨z2, hz2⟩ : ∃ z : ℝ, z = relu (0 * x0 + (-1) * x1 + 3) := ⟨_, rfl⟩
  have bz2l : 0 ≤ z2 := by rw [hz2]; exact relu_nonneg' _
  have bz2u : z2 ≤ 7 := by rw [hz2]; exact relu_le_of_le (by linarith) (by norm_num)
  obtain ⟨z3, hz3⟩ : ∃ z : ℝ, z = relu (1 * x0 + 0 * x1 + (-3)) := ⟨_, rfl⟩
  have bz3l : 0 ≤ z3 := by rw [hz3]; exact relu_nonneg' _
  have bz3u : z3 ≤ 5 := by rw [hz3]; exact relu_le_of_le (by linarith) (by norm_num)
  obtain ⟨z4, hz4⟩ : ∃ z : ℝ, z = relu ((1/8) * x0 + 0 * x1 + 1) := ⟨_, rfl⟩
  have bz4l : 0 ≤ z4 := by rw [hz4]; exact relu_nonneg' _
  have bz4u : z4 ≤ 2 := by rw [hz4]; exact relu_le_of_le (by linarith) (by norm_num)
  have ez1 : z1 = x1 + 6 := by rw [hz1]; exact w_rp (by linarith) (by ring)
  have ez2 : z2 = 3 - x1 := by rw [hz2]; exact w_rp (by linarith) (by ring)
  have ez4 : z4 = x0 / 8 + 1 := by rw [hz4]; exact w_rp (by linarith) (by ring)
  have ez3 := w_z3 hz3
  obtain ⟨a0, a1, a2, a3, a4, pa0, pa1, pa2, pa3, pa4, h1, ra0, ra1, ra2, ra3, ra4, na0, na1, na2, na3, na4⟩ := w_lay1 hw hb 0 hx0 hx1
  obtain ⟨na0l, na0u⟩ := abs_le.mp na0
  obtain ⟨na1l, na1u⟩ := abs_le.mp na1
  obtain ⟨na2l, na2u⟩ := abs_le.mp na2
  obtain ⟨na3l, na3u⟩ := abs_le.mp na3
  obtain ⟨na4l, na4u⟩ := abs_le.mp na4
  have f1_0 : |a0 - z0| ≤ 13/1000 := by rw [hz0]; exact w_pe ra0 (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨f1_0l, f1_0u⟩ := abs_le.mp f1_0
  have f1_1 : |a1 - z1| ≤ 13/1000 := by rw [hz1]; exact w_pe ra1 (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨f1_1l, f1_1u⟩ := abs_le.mp f1_1
  have f1_2 : |a2 - z2| ≤ 13/1000 := by rw [hz2]; exact w_pe ra2 (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨f1_2l, f1_2u⟩ := abs_le.mp f1_2
  have f1_3 : |a3 - z3| ≤ 13/1000 := by rw [hz3]; exact w_pe ra3 (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨f1_3l, f1_3u⟩ := abs_le.mp f1_3
  have f1_4 : |a4 - z4| ≤ 13/1000 := by rw [hz4]; exact w_pe ra4 (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨f1_4l, f1_4u⟩ := abs_le.mp f1_4
  have m2_0 : |a0| ≤ 15513/1000 := abs_le.mpr ⟨by linarith, by linarith⟩
  have m2_1 : |a1| ≤ 7013/1000 := abs_le.mpr ⟨by linarith, by linarith⟩
  have m2_2 : |a2| ≤ 7013/1000 := abs_le.mpr ⟨by linarith, by linarith⟩
  have m2_3 : |a3| ≤ 5013/1000 := abs_le.mpr ⟨by linarith, by linarith⟩
  have m2_4 : |a4| ≤ 2013/1000 := abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨y0, hy0⟩ : ∃ z : ℝ, z = relu ((-3) * z0 + (3/2) * z1 + 0 * z2 + 0 * z3 + 0 * z4 + 0) := ⟨_, rfl⟩
  have qy0l : 0 ≤ y0 := by rw [hy0]; exact relu_nonneg' _
  have qy0u : y0 ≤ 21/2 := by rw [hy0]; exact relu_le_of_le (by linarith) (by norm_num)
  obtain ⟨y1, hy1⟩ : ∃ z : ℝ, z = relu (0 * z0 + 0 * z1 + (3/2) * z2 + 0 * z3 + 0 * z4 + 0) := ⟨_, rfl⟩
  have qy1l : 0 ≤ y1 := by rw [hy1]; exact relu_nonneg' _
  have qy1u : y1 ≤ 21/2 := by rw [hy1]; exact relu_le_of_le (by linarith) (by norm_num)
  obtain ⟨y2, hy2⟩ : ∃ z : ℝ, z = relu (0 * z0 + 0 * z1 + 0 * z2 + (3/2) * z3 + 0 * z4 + 0) := ⟨_, rfl⟩
  have qy2l : 0 ≤ y2 := by rw [hy2]; exact relu_nonneg' _
  have qy2u : y2 ≤ 15/2 := by rw [hy2]; exact relu_le_of_le (by linarith) (by norm_num)
  obtain ⟨y3, hy3⟩ : ∃ z : ℝ, z = relu (0 * z0 + 0 * z1 + 0 * z2 + 0 * z3 + 4 * z4 + 0) := ⟨_, rfl⟩
  have qy3l : 0 ≤ y3 := by rw [hy3]; exact relu_nonneg' _
  have qy3u : y3 ≤ 8 := by rw [hy3]; exact relu_le_of_le (by linarith) (by norm_num)
  have ey1 : y1 = 9/2 - (3/2) * x1 := by rw [hy1]; exact w_rp (by linarith) (by linarith)
  have ey2 : y2 = (3/2) * z3 := by rw [hy2]; exact w_rp (by linarith) (by ring)
  have ey3 : y3 = 4 * z4 := by rw [hy3]; exact w_rp (by linarith) (by ring)
  obtain ⟨b0, b1, b2, b3, pb0, pb1, pb2, pb3, h2, rb0, rb1, rb2, rb3, nb0, nb1, nb2, nb3⟩ := w_lay2 hw hb 1 m2_0 m2_1 m2_2 m2_3 m2_4
  obtain ⟨nb0l, nb0u⟩ := abs_le.mp nb0
  obtain ⟨nb1l, nb1u⟩ := abs_le.mp nb1
  obtain ⟨nb2l, nb2u⟩ := abs_le.mp nb2
  obtain ⟨nb3l, nb3u⟩ := abs_le.mp nb3
  have f2_0 : |b0 - y0| ≤ 961/10000 := by rw [hy0]; exact w_pe rb0 (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨f2_0l, f2_0u⟩ := abs_le.mp f2_0
  have f2_1 : |b1 - y1| ≤ 571/10000 := by rw [hy1]; exact w_pe rb1 (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨f2_1l, f2_1u⟩ := abs_le.mp f2_1
  have f2_2 : |b2 - y2| ≤ 571/10000 := by rw [hy2]; exact w_pe rb2 (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨f2_2l, f2_2u⟩ := abs_le.mp f2_2
  have f2_3 : |b3 - y3| ≤ 56/625 := by rw [hy3]; exact w_pe rb3 (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨f2_3l, f2_3u⟩ := abs_le.mp f2_3
  have m3_0 : |b0| ≤ 105961/10000 := abs_le.mpr ⟨by linarith, by linarith⟩
  have m3_1 : |b1| ≤ 105571/10000 := abs_le.mpr ⟨by linarith, by linarith⟩
  have m3_2 : |b2| ≤ 75571/10000 := abs_le.mpr ⟨by linarith, by linarith⟩
  have m3_3 : |b3| ≤ 5056/625 := abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨s0, hs0⟩ : ∃ z : ℝ, z = relu ((-1) * y0 + 1 * y1 + 0 * y2 + 0 * y3 + 0) := ⟨_, rfl⟩
  have bs0l : 0 ≤ s0 := by rw [hs0]; exact relu_nonneg' _
  have bs0u : s0 ≤ 21/2 := by rw [hs0]; exact relu_le_of_le (by linarith) (by norm_num)
  obtain ⟨s1, hs1⟩ : ∃ z : ℝ, z = relu (1 * y0 + (-1) * y1 + 0 * y2 + 0 * y3 + 0) := ⟨_, rfl⟩
  have bs1l : 0 ≤ s1 := by rw [hs1]; exact relu_nonneg' _
  have bs1u : s1 ≤ 21/2 := by rw [hs1]; exact relu_le_of_le (by linarith) (by norm_num)
  obtain ⟨s2, hs2⟩ : ∃ z : ℝ, z = relu (0 * y0 + 0 * y1 + 1 * y2 + 0 * y3 + 0) := ⟨_, rfl⟩
  have bs2l : 0 ≤ s2 := by rw [hs2]; exact relu_nonneg' _
  have bs2u : s2 ≤ 15/2 := by rw [hs2]; exact relu_le_of_le (by linarith) (by norm_num)
  obtain ⟨s3, hs3⟩ : ∃ z : ℝ, z = relu (0 * y0 + 0 * y1 + 0 * y2 + 1 * y3 + 0) := ⟨_, rfl⟩
  have bs3l : 0 ≤ s3 := by rw [hs3]; exact relu_nonneg' _
  have bs3u : s3 ≤ 8 := by rw [hs3]; exact relu_le_of_le (by linarith) (by norm_num)
  have hs01 : s0 + s1 = |y1 - y0| := w_s01 hs0 hs1
  have es2 : s2 = y2 := by rw [hs2]; exact w_rp (by linarith) (by ring)
  have es3 : s3 = y3 := by rw [hs3]; exact w_rp (by linarith) (by ring)
  obtain ⟨c0, c1, c2, c3, pc0, pc1, pc2, pc3, h3, rc0, rc1, rc2, rc3, nc0, nc1, nc2, nc3⟩ := w_lay3 hw hb 2 m3_0 m3_1 m3_2 m3_3
  obtain ⟨nc0l, nc0u⟩ := abs_le.mp nc0
  obtain ⟨nc1l, nc1u⟩ := abs_le.mp nc1
  obtain ⟨nc2l, nc2u⟩ := abs_le.mp nc2
  obtain ⟨nc3l, nc3u⟩ := abs_le.mp nc3
  have f3_0 : |c0 - s0| ≤ 191/1000 := by rw [hs0]; exact w_pe rc0 (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨f3_0l, f3_0u⟩ := abs_le.mp f3_0
  have f3_1 : |c1 - s1| ≤ 191/1000 := by rw [hs1]; exact w_pe rc1 (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨f3_1l, f3_1u⟩ := abs_le.mp f3_1
  have f3_2 : |c2 - s2| ≤ 949/10000 := by rw [hs2]; exact w_pe rc2 (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨f3_2l, f3_2u⟩ := abs_le.mp f3_2
  have f3_3 : |c3 - s3| ≤ 637/5000 := by rw [hs3]; exact w_pe rc3 (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨f3_3l, f3_3u⟩ := abs_le.mp f3_3
  have hS0 := w_sum nc0 nc1 f2_0 f2_1 (E := 143/625) (by norm_num)
  have hS : |c0 + c1 - (s0 + s1)| ≤ 143/625 := by rw [rc0, rc1, hs01]; exact hS0
  have m4_0 : |c0| ≤ 10691/1000 := abs_le.mpr ⟨by linarith, by linarith⟩
  have m4_1 : |c1| ≤ 10691/1000 := abs_le.mpr ⟨by linarith, by linarith⟩
  have m4_2 : |c2| ≤ 75949/10000 := abs_le.mpr ⟨by linarith, by linarith⟩
  have m4_3 : |c3| ≤ 40637/5000 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hc3 : 0 ≤ c3 := by rw [rc3]; exact relu_nonneg' _
  have hab : |y1 - y0| ≤ 21/2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hs01b : s0 + s1 ≤ 21/2 := by linarith
  obtain ⟨t, ht⟩ : ∃ z : ℝ, z = relu ((2/3) * s0 + (2/3) * s1 + (2/3) * s2 + (-2) * s3 + (17/2)) := ⟨_, rfl⟩
  have bt0 : 0 ≤ t := by rw [ht]; exact relu_nonneg' _
  have bt1 : t ≤ 41/2 := by rw [ht]; exact relu_le_of_le (by linarith) (by norm_num)
  obtain ⟨xx, hxx⟩ : ∃ z : ℝ, z = relu (0 * s0 + 0 * s1 + 0 * s2 + 4 * s3 + 0) := ⟨_, rfl⟩
  have bx0 : 0 ≤ xx := by rw [hxx]; exact relu_nonneg' _
  have bx1 : xx ≤ 32 := by rw [hxx]; exact relu_le_of_le (by linarith) (by norm_num)
  obtain ⟨d0, d1, pd0, pd1, h4, rd0, rd1, nd0, nd1⟩ := w_lay4 hw hb 3 m4_0 m4_1 m4_2 m4_3
  obtain ⟨nd0l, nd0u⟩ := abs_le.mp nd0
  obtain ⟨nd1l, nd1u⟩ := abs_le.mp nd1
  have f4_0 : |d0 - t| ≤ 611/1000 := by rw [ht]; exact w_pe rd0 (by rw [abs_le]; constructor <;> linarith)
  have f4_1 : |d1 - xx| ≤ 2739/5000 := by rw [hxx]; exact w_pe rd1 (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨f4_0l, f4_0u⟩ := abs_le.mp f4_0
  obtain ⟨f4_1l, f4_1u⟩ := abs_le.mp f4_1
  have m5_0 : |d0| ≤ 21111/1000 := abs_le.mpr ⟨by linarith, by linarith⟩
  have m5_1 : |d1| ≤ 162739/5000 := abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨Y, hY, nY⟩ := w_out hw hb 4 m5_0 m5_1
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max ((1/2) * x0 + (-3/2)) 0 := ⟨_, rfl⟩
  obtain ⟨med, hmed⟩ : ∃ m : ℝ, m = max (min ((-1) * x1 + (-3/2)) ((-1/2) * x1 + (3/2))) (min (max ((-1) * x1 + (-3/2)) ((-1/2) * x1 + (3/2))) ((-1) * x0 + 3 * x1 + 2)) := ⟨_, rfl⟩
  have hy0' : y0 = relu ((-3) * z0 + (3/2) * z1) := by rw [hy0]; congr 1; ring
  have hmed3 : y1 - y0 = 3 * med := by rw [hmed]; exact w_med (by linarith) (by linarith) hz0 ez1 hy0' ey1
  have habs : |y1 - y0| = 3 * |med| := by rw [hmed3, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
  have hA : (-2) * R + (-2) * |med| = -((2/3) * (s0 + s1 + s2)) := by linarith
  have hB : (-1) * x0 + (1/2) = 17/2 - 2 * s3 := by linarith
  have hev : Net.evalP net dW db [x0, x1] = rowsP lyrO.W lyrO.b (dW 4) (db 4) (lay lyr4 3 dW db (lay lyr3 2 dW db (lay lyr2 1 dW db (lay lyr1 0 dW db [x0, x1])))) 0 := by
    first | rfl | simp [Net.evalP, net, hiddenP, lay]
  rw [h1, h2, h3, h4] at hev
  refine ⟨Y, ?_, ?_⟩
  · rw [hev]; exact hY
  · rw [w_spec_eq hR hmed]
    exact w_fin rd0 rd1 nd0 nd1 nY hc3 hS f3_2 f3_3 hA hB (EM := 637/2500) (by norm_num) (by norm_num) (by norm_num)

end Lane4.Case
