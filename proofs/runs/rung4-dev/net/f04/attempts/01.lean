namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

def zr : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0]

/-- State: [U, a, c, Aslot, Hslot, 1, fl i, fl n]. -/
def hh : Head :=
  { A := [zr, zr, zr, zr, zr, [0, 0, 0, 0, 0, 0, -1, 0], zr, [-2, 0, 0, 0, 0, 0, 0, 0]],
    V := [zr, zr, zr, [0, 1, 0, 0, 0, 0, 0, 0], zr, zr, zr, zr],
    mask := Mask.causal }

def blk : Block :=
  { heads := [hh], W1 := [[0, 0, 1, 1, 0, 0, 0, 0]], b1 := [-1],
    W2 := [[0], [0], [0], [0], [1], [0], [0], [0]], b2 := zr }

def net : TNet :=
  { embed := [[1, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 1, 1, 0, 0], [0, 0, 0, 0, 0],
              [1, 0, 0, 0, 0], [0, 0, 1, 0, 0]],
    blocks := [blk],
    outW := [0, 0, 1, 1, -2, 0, 0, 0],
    outB := 0 }

def uT (t : ℕ) : ℚ := if t = 0 ∨ t = 4 then 1 else 0
def aT (t : ℕ) : ℚ := if t = 2 then 1 else 0
def cT (t : ℕ) : ℚ := if t = 2 ∨ t = 5 then 1 else 0

noncomputable def suv (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (uT (tokAt w j)) (p.E (tokAt w j) 0)
noncomputable def sav (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (aT (tokAt w j)) (p.E (tokAt w j) 1)
noncomputable def scv (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (cT (tokAt w j)) (p.E (tokAt w j) 2)

noncomputable def Sc (fl : ℝ → ℝ) (s5 s7 pn pk su : ℝ) : ℝ :=
  fl (fl (s5 * pk) + fl (pn * fl (s7 * su)))

noncomputable def outF (fl : ℝ → ℝ) (w1 w2 w3 w4 w5 w6 b c A : ℝ) : ℝ :=
  fl (fl (fl (w4 * c) + fl (w5 * A)) +
    fl (w6 * fl (w3 * relu (fl (fl (fl (w1 * c) + fl (w2 * A)) + b)))))

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem fl_suv {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ) :
    fl (suv fl p w j) = suv fl p w j := by
  unfold suv; exact fl_sw hr _ _

theorem fl_sav {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ) :
    fl (sav fl p w j) = sav fl p w j := by
  unfold sav; exact fl_sw hr _ _

theorem fl_scv {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ) :
    fl (scv fl p w j) = scv fl p w j := by
  unfold scv; exact fl_sw hr _ _

theorem fl_ravg {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (S : List ℕ) (f : ℕ → ℝ) :
    fl (ravg fl S f) = ravg fl S f := by
  unfold ravg; exact hr.idem _

theorem ravg_zero_on {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (S : List ℕ) (f : ℕ → ℝ)
    (h : ∀ j ∈ S, f j = 0) : ravg fl S f = 0 := by
  unfold ravg
  rw [rsum_zeros hr _ (by
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    exact h j hj)]
  simp [hr.zero]

theorem init_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [suv fl p w j, sav fl p w j, scv fl p w j, 0, 0] ++ pos fl j (w.length + 1) := by
  have h6 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 ∨
      tokAt w j = 5 := by
    have := tok_le w hw j
    omega
  rcases h6 with h | h | h | h | h | h <;>
    simp [TNet.init, net, suv, sav, scv, uT, aT, cT, swRow, h, sw_zero hr]

theorem score_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (a b c qi qn a' b' c' qk qn' : ℝ) :
    hh.score fl dA [a, b, c, 0, 0, 1, qi, qn] [a', b', c', 0, 0, 1, qk, qn']
      = fl (fl (sw fl (-1) (dA 5 6) * qk) + fl (qn * fl (sw fl (-2) (dA 7 0) * a'))) := by
  simp [Head.score, hh, zr, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem]

theorem score_at {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i k : ℕ) :
    hh.score fl (p.A 0 0) (net.init fl p w i) (net.init fl p w k)
      = Sc fl (sw fl (-1) (p.A 0 0 5 6)) (sw fl (-2) (p.A 0 0 7 0))
          (fl ((w.length + 1 : ℕ) : ℝ)) (fl (k : ℝ)) (suv fl p w k) := by
  rw [init_eq hr p w hw i, init_eq hr p w hw k]
  simp only [pos, List.cons_append, List.nil_append]
  exact score_eq hr _ _ _ _ _ _ _ _ _ _ _

theorem attn_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (dV : ℕ → ℕ → ℝ) (S : List ℕ) :
    attnRows fl hh.V dV S (net.init fl p w) 0
      = [0, 0, 0, ravg fl S (fun j => fl (sw fl 1 (dV 3 1) * sav fl p w j)), 0, 0, 0, 0] := by
  rw [show hh.V = [zr, zr, zr, [0, 1, 0, 0, 0, 0, 0, 0], zr, zr, zr, zr] from rfl]
  simp [attnRows, init_eq hr p w hw, rdot, pos, zr, sw_zero hr, hr.zero, hr.idem, ravg_zero hr]

theorem out_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) (S : List ℕ)
    (hsel : hh.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = S) :
    net.out fl p w i
      = outF fl (sw fl 1 (p.W1 0 0 2)) (sw fl 1 (p.W1 0 0 3)) (sw fl 1 (p.W2 0 4 0))
          (sw fl 1 (p.oW 2)) (sw fl 1 (p.oW 3)) (sw fl (-2) (p.oW 4)) (sw fl (-1) (p.b1 0 0))
          (scv fl p w i)
          (ravg fl S (fun j => fl (sw fl 1 (p.V 0 0 3 1) * sav fl p w j))) := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 0, 1, 1, -2, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [runFrom, Block.apply, blk, headsApply, Head.attn, hsel, attn_eq hr p w hw]
  simp [outF, init_eq hr p w hw, pos, raffine, rdot, radd, zr, sw_zero hr, hr.zero, hr.idem,
    hr.one, fl_suv hr, fl_sav hr, fl_scv hr, fl_ravg hr]

/-! ### numeric lemmas -/

theorem swb {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    (w : ℚ) (r : ℝ) (hw : (w : ℝ) = r) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    |sw fl w d - r| ≤ 51 / 10000 * |r| := by
  have h := sw_rel hr hu0 w hd (ε := 51 / 10000) (by linarith)
  rw [hw] at h
  exact h

theorem swp1 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {d : ℝ} (hd : |d| ≤ 1 / 200) : |sw fl 1 d - 1| ≤ 51 / 10000 * 1 := by
  have h := swb hr hu0 hu1 1 1 (by norm_num) hd
  rw [abs_one] at h
  exact h

theorem swm1 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {d : ℝ} (hd : |d| ≤ 1 / 200) : |sw fl (-1) d - (-1)| ≤ 51 / 10000 * 1 := by
  have h := swb hr hu0 hu1 (-1) (-1) (by norm_num) hd
  have h2 : |(-1 : ℝ)| = 1 := by norm_num
  rw [h2] at h
  exact h

theorem swm2 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {d : ℝ} (hd : |d| ≤ 1 / 200) : |sw fl (-2) d - (-2)| ≤ 51 / 10000 * 2 := by
  have h := swb hr hu0 hu1 (-2) (-2) (by norm_num) hd
  have h2 : |(-2 : ℝ)| = 2 := by norm_num
  rw [h2] at h
  exact h

theorem flb {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {x : ℝ} (hx : |x| ≤ 16) : |fl x - x| ≤ 1 / 1000000 := by
  have h := hr.err hu0 hx
  linarith

theorem mulerr {s S v V E f : ℝ} (hs : |s - S| ≤ E) (hv : |v - V| ≤ f) :
    |s * v - S * V| ≤ E * (|V| + f) + |S| * f := by
  have hE : 0 ≤ E := le_trans (abs_nonneg _) hs
  have hv' : |v| ≤ |V| + f := by
    have := abs_sub_abs_le_abs_sub v V
    linarith
  have h1 : s * v - S * V = (s - S) * v + S * (v - V) := by ring
  have h2 : |(s - S) * v + S * (v - V)| ≤ |(s - S) * v| + |S * (v - V)| := abs_add_le _ _
  have h3 : |(s - S) * v| ≤ E * (|V| + f) := by
    rw [abs_mul]
    exact mul_le_mul hs hv' (abs_nonneg _) hE
  have h4 : |S * (v - V)| ≤ |S| * f := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hv (abs_nonneg _)
  rw [h1]
  linarith

theorem fmul {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {s S v V f k N : ℝ} (hs : |s - S| ≤ 51 / 10000 * k) (hk : |S| = k) (hk2 : k ≤ 2)
    (hv : |v - V| ≤ f) (hV : |V| ≤ 1) (hf : f ≤ 1 / 10) (hN : S * V = N) :
    |fl (s * v) - N| ≤ 51 / 10000 * k * (|V| + f) + k * f + 1 / 1000000 := by
  subst hN
  have h1 := mulerr hs hv
  rw [hk] at h1
  have hk0 : 0 ≤ k := by rw [← hk]; exact abs_nonneg _
  have hf0 : 0 ≤ f := le_trans (abs_nonneg _) hv
  have hs' : |s| ≤ 3 := by
    have := abs_sub_abs_le_abs_sub s S
    linarith
  have hv' : |v| ≤ 3 := by
    have := abs_sub_abs_le_abs_sub v V
    linarith
  have hsv : |s * v| ≤ 16 := by
    rw [abs_mul]
    have := mul_le_mul hs' hv' (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
    linarith
  have h2 := flb hr hu0 hu1 hsv
  have h3 := abs_sub_le (fl (s * v)) (s * v) (S * V)
  linarith

theorem fadd {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {x y X Y ex ey : ℝ} (hx : |x - X| ≤ ex) (hy : |y - Y| ≤ ey) (hX : |X| ≤ 2) (hY : |Y| ≤ 2)
    (hex : ex ≤ 1) (hey : ey ≤ 1) :
    |fl (x + y) - (X + Y)| ≤ ex + ey + 1 / 1000000 := by
  have hx' : |x| ≤ 3 := by
    have := abs_sub_abs_le_abs_sub x X
    linarith
  have hy' : |y| ≤ 3 := by
    have := abs_sub_abs_le_abs_sub y Y
    linarith
  have hxy : |x + y| ≤ 16 := by
    have := abs_add_le x y
    linarith
  have h2 := flb hr hu0 hu1 hxy
  have h3 := abs_sub_le (fl (x + y)) (x + y) (X + Y)
  have h4 : |x + y - (X + Y)| ≤ |x - X| + |y - Y| := by
    have : x + y - (X + Y) = (x - X) + (y - Y) := by ring
    rw [this]
    exact abs_add_le _ _
  linarith

theorem relu_lip (a b : ℝ) : |relu a - relu b| ≤ |a - b| := by
  unfold relu
  have h1 := neg_abs_le (a - b)
  have h2 := le_abs_self (a - b)
  have h3 := abs_nonneg (a - b)
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [max_eq_right ha, max_eq_right hb, abs_le]
    constructor <;> linarith
  · rw [max_eq_right ha, max_eq_left hb, abs_le]
    constructor <;> linarith
  · rw [max_eq_left ha, max_eq_right hb, abs_le]
    constructor <;> linarith
  · rw [max_eq_left ha, max_eq_left hb]

theorem relu_bit (a c : ℝ) (ha : a = 0 ∨ a = 1) (hc : c = 0 ∨ c = 1) :
    relu (a + c - 1) = a * c := by
  rcases ha with rfl | rfl <;> rcases hc with rfl | rfl
  · rw [relu_of_nonpos (show ((0 : ℝ) + 0 - 1) ≤ 0 by norm_num)]; norm_num
  · rw [relu_of_nonneg (show (0 : ℝ) ≤ 0 + 1 - 1 by norm_num)]; norm_num
  · rw [relu_of_nonneg (show (0 : ℝ) ≤ 1 + 0 - 1 by norm_num)]; norm_num
  · rw [relu_of_nonneg (show (0 : ℝ) ≤ 1 + 1 - 1 by norm_num)]; norm_num

theorem fnum {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {a0 c0 A c w1 w2 w3 w4 w5 w6 b : ℝ} (ha0 : a0 = 0 ∨ a0 = 1) (hc0 : c0 = 0 ∨ c0 = 1)
    (hA : |A - a0| ≤ 11 / 1000) (hc : |c - c0| ≤ 11 / 1000)
    (h1 : |w1 - 1| ≤ 51 / 10000 * 1) (h2 : |w2 - 1| ≤ 51 / 10000 * 1)
    (h3 : |w3 - 1| ≤ 51 / 10000 * 1) (h4 : |w4 - 1| ≤ 51 / 10000 * 1)
    (h5 : |w5 - 1| ≤ 51 / 10000 * 1) (h6 : |w6 - (-2)| ≤ 51 / 10000 * 2)
    (hb : |b - (-1)| ≤ 51 / 10000 * 1) :
    |outF fl w1 w2 w3 w4 w5 w6 b c A - (a0 + c0 - 2 * (a0 * c0))| ≤ 1 / 4 := by
  unfold outF
  have ha1 : 0 ≤ a0 ∧ a0 ≤ 1 := by
    rcases ha0 with h | h <;> rw [h] <;> norm_num
  have hc1 : 0 ≤ c0 ∧ c0 ≤ 1 := by
    rcases hc0 with h | h <;> rw [h] <;> norm_num
  have hac : 0 ≤ a0 * c0 ∧ a0 * c0 ≤ 1 :=
    ⟨mul_nonneg ha1.1 hc1.1, by nlinarith [ha1.1, ha1.2, hc1.1, hc1.2]⟩
  have habsa : |a0| ≤ 1 := abs_le.mpr ⟨by linarith [ha1.1], ha1.2⟩
  have habsc : |c0| ≤ 1 := abs_le.mpr ⟨by linarith [hc1.1], hc1.2⟩
  have habsh : |a0 * c0| ≤ 1 := abs_le.mpr ⟨by linarith [hac.1], hac.2⟩
  -- hidden pre-activation
  have t1 := fmul hr hu0 hu1 (S := 1) (V := c0) (k := 1) (N := c0) h1 (by norm_num)
    (by norm_num) hc habsc (by norm_num) (one_mul c0)
  have t1' : |fl (w1 * c) - c0| ≤ 17 / 1000 := by linarith
  have t2 := fmul hr hu0 hu1 (S := 1) (V := a0) (k := 1) (N := a0) h2 (by norm_num)
    (by norm_num) hA habsa (by norm_num) (one_mul a0)
  have t2' : |fl (w2 * A) - a0| ≤ 17 / 1000 := by linarith
  have t12 := fadd hr hu0 hu1 t1' t2' (by linarith) (by linarith) (by norm_num) (by norm_num)
  have t12' : |fl (fl (w1 * c) + fl (w2 * A)) - (c0 + a0)| ≤ 35 / 1000 := by linarith
  have hpre := fadd hr hu0 hu1 t12' hb (Y := -1)
    (abs_le.mpr ⟨by linarith [ha1.1, hc1.1], by linarith [ha1.2, hc1.2]⟩)
    (by norm_num) (by norm_num) (by norm_num)
  have hX1 : c0 + a0 + -1 = a0 + c0 - 1 := by ring
  rw [hX1] at hpre
  have hrelu := relu_lip (fl (fl (fl (w1 * c) + fl (w2 * A)) + b)) (a0 + c0 - 1)
  rw [relu_bit a0 c0 ha0 hc0] at hrelu
  have hv : |relu (fl (fl (fl (w1 * c) + fl (w2 * A)) + b)) - a0 * c0| ≤ 41 / 1000 :=
    le_trans hrelu (by linarith)
  have tH := fmul hr hu0 hu1 (S := 1) (V := a0 * c0) (k := 1) (N := a0 * c0) h3 (by norm_num)
    (by norm_num) hv habsh (by norm_num) (one_mul _)
  have tH' : |fl (w3 * relu (fl (fl (fl (w1 * c) + fl (w2 * A)) + b))) - a0 * c0| ≤ 47 / 1000 := by
    linarith
  -- output
  have o1 := fmul hr hu0 hu1 (S := 1) (V := c0) (k := 1) (N := c0) h4 (by norm_num)
    (by norm_num) hc habsc (by norm_num) (one_mul c0)
  have o1' : |fl (w4 * c) - c0| ≤ 17 / 1000 := by linarith
  have o2 := fmul hr hu0 hu1 (S := 1) (V := a0) (k := 1) (N := a0) h5 (by norm_num)
    (by norm_num) hA habsa (by norm_num) (one_mul a0)
  have o2' : |fl (w5 * A) - a0| ≤ 17 / 1000 := by linarith
  have o12 := fadd hr hu0 hu1 o1' o2' (by linarith) (by linarith) (by norm_num) (by norm_num)
  have o12' : |fl (fl (w4 * c) + fl (w5 * A)) - (c0 + a0)| ≤ 35 / 1000 := by linarith
  have o3 := fmul hr hu0 hu1 (S := -2) (V := a0 * c0) (k := 2) (N := (-2) * (a0 * c0)) h6
    (by norm_num) (by norm_num) tH' habsh (by norm_num) rfl
  have o3' : |fl (w6 * fl (w3 * relu (fl (fl (fl (w1 * c) + fl (w2 * A)) + b))))
      - (-2) * (a0 * c0)| ≤ 105 / 1000 := by linarith
  have fin := fadd hr hu0 hu1 o12' o3' (by linarith)
    (abs_le.mpr ⟨by linarith [hac.2], by linarith [hac.1]⟩) (by norm_num) (by norm_num)
  have e : c0 + a0 + (-2) * (a0 * c0) = a0 + c0 - 2 * (a0 * c0) := by ring
  rw [e] at fin
  exact le_trans fin (by norm_num)

/-! ### selection -/

theorem Sc_marked {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (s5 s7 pn pk : ℝ) :
    Sc fl s5 s7 pn pk 0 = fl (s5 * pk) := by
  simp [Sc, hr.zero, hr.idem]

theorem flN {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) {N x : ℝ}
    (hn : u * N ≤ 1 / 256) (h1 : -(4 * N) ≤ x) (h2 : x ≤ 4 * N) : |fl x - x| ≤ 1 / 64 := by
  have h := hr.err hu0 (abs_le.mpr ⟨h1, h2⟩ : |x| ≤ 4 * N)
  nlinarith [h, hn]

theorem m5_bd {N s5 pk : ℝ} (h5a : -10051 / 10000 ≤ s5) (h5b : s5 ≤ -9949 / 10000)
    (hk0 : 0 ≤ pk) (hk1 : pk ≤ N + 1 / 256) :
    -(10051 / 10000 * (N + 1 / 256)) ≤ s5 * pk ∧ s5 * pk ≤ 0 := by
  constructor
  · nlinarith [mul_nonneg (show 0 ≤ s5 + 10051 / 10000 by linarith) hk0]
  · nlinarith [mul_nonneg (show 0 ≤ -s5 by linarith) hk0]

theorem Sc_lt_marked {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    {N s5 s7 pn pj pk : ℝ} (hn : u * N ≤ 1 / 256) (hN : 2 ≤ N)
    (h5a : -10051 / 10000 ≤ s5) (h5b : s5 ≤ -9949 / 10000)
    (hj0 : 0 ≤ pj) (hj1 : pj ≤ N + 1 / 256) (hk0 : 0 ≤ pk) (hk1 : pk ≤ N + 1 / 256)
    (hjk : pj + 127 / 128 ≤ pk) : Sc fl s5 s7 pn pk 0 < Sc fl s5 s7 pn pj 0 := by
  rw [Sc_marked hr, Sc_marked hr]
  obtain ⟨a1, a2⟩ := m5_bd (N := N) h5a h5b hk0 hk1
  obtain ⟨b1, b2⟩ := m5_bd (N := N) h5a h5b hj0 hj1
  have hprod := mul_le_mul_of_nonneg_right (show (9949 / 10000 : ℝ) ≤ -s5 by linarith)
    (show (0 : ℝ) ≤ pk - pj by linarith)
  apply hr.lt_of_gap hu0 (B := 4 * N)
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · nlinarith [hprod, hn]

theorem Sc_lt_unmarked {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    {N s5 s7 pn pj pk su : ℝ} (hn : u * N ≤ 1 / 256) (hN : 2 ≤ N)
    (h5a : -10051 / 10000 ≤ s5) (h5b : s5 ≤ -9949 / 10000)
    (h7a : -20102 / 10000 ≤ s7) (h7b : s7 ≤ -19898 / 10000)
    (hpn1 : N - 1 / 256 ≤ pn) (hpn2 : pn ≤ N + 1 / 256)
    (hj0 : 0 ≤ pj) (hj1 : pj ≤ N + 1 / 256) (hk0 : 0 ≤ pk) (hk1 : pk ≤ N + 1 / 256)
    (hsu1 : 9949 / 10000 ≤ su) (hsu2 : su ≤ 10051 / 10000) :
    Sc fl s5 s7 pn pk su < Sc fl s5 s7 pn pj 0 := by
  rw [Sc_marked hr]
  unfold Sc
  have hpn0 : 0 ≤ pn := by linarith
  obtain ⟨a1, a2⟩ := m5_bd (N := N) h5a h5b hk0 hk1
  obtain ⟨b1, b2⟩ := m5_bd (N := N) h5a h5b hj0 hj1
  have m1 : s7 * su ≤ -19796 / 10000 := by
    nlinarith [mul_nonneg (show 0 ≤ -s7 by linarith) (show 0 ≤ su - 9949 / 10000 by linarith)]
  have m2 : -20205 / 10000 ≤ s7 * su := by
    nlinarith [mul_nonneg (show 0 ≤ -s7 by linarith) (show 0 ≤ 10051 / 10000 - su by linarith)]
  obtain ⟨c1, c2⟩ := abs_le.mp (flN hr hu0 hn (x := s7 * su) (by linarith) (by linarith))
  have m3 : fl (s7 * su) ≤ -19639 / 10000 := by linarith
  have m4 : -20362 / 10000 ≤ fl (s7 * su) := by linarith
  have q1 : pn * fl (s7 * su) ≤ pn * (-19639 / 10000) := mul_le_mul_of_nonneg_left m3 hpn0
  have q2 : pn * (-20362 / 10000) ≤ pn * fl (s7 * su) := mul_le_mul_of_nonneg_left m4 hpn0
  obtain ⟨d1, d2⟩ := abs_le.mp
    (flN hr hu0 hn (x := pn * fl (s7 * su)) (by linarith) (by linarith))
  obtain ⟨e1, e2⟩ := abs_le.mp (flN hr hu0 hn (x := s5 * pk) (by linarith) (by linarith))
  obtain ⟨f1, f2⟩ := abs_le.mp (flN hr hu0 hn (x := s5 * pj) (by linarith) (by linarith))
  obtain ⟨g1, g2⟩ := abs_le.mp
    (flN hr hu0 hn (x := fl (s5 * pk) + fl (pn * fl (s7 * su))) (by linarith) (by linarith))
  linarith

/-! ### cases on tokens -/

theorem uT_cases (t : ℕ) (ht : t ≤ 5) :
    (code t = 0 ∧ uT t = 1) ∨ (code t ≠ 0 ∧ uT t = 0) := by
  interval_cases t <;> simp [code, uT]

theorem aT_cases (t : ℕ) (ht : t ≤ 5) :
    (code t = 2 ∧ aT t = 1) ∨ (code t ≠ 2 ∧ aT t = 0) := by
  interval_cases t <;> simp [code, aT]

theorem cT_cases (t : ℕ) (ht : t ≤ 5) :
    (cbit t = 0 ∧ cT t = 0) ∨ (cbit t = 1 ∧ cT t = 1) := by
  interval_cases t <;> simp [cbit, cT]

theorem suv_cases {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    (code (tokAt w j) = 0 ∧ |suv fl p w j - 1| ≤ 51 / 10000) ∨
      (code (tokAt w j) ≠ 0 ∧ suv fl p w j = 0) := by
  rcases uT_cases (tokAt w j) (tok_le w hw j) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨h1, ?_⟩
    have h := swb hr hu0 hu1 (uT (tokAt w j)) 1 (by simp [h2]) (hp.E (tokAt w j) 0)
    rw [abs_one, mul_one] at h
    unfold suv
    exact h
  · right
    refine ⟨h1, ?_⟩
    unfold suv
    rw [h2]
    exact sw_zero hr _

theorem sav_cases {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    (code (tokAt w j) = 2 ∧ |sav fl p w j - 1| ≤ 51 / 10000) ∨
      (code (tokAt w j) ≠ 2 ∧ sav fl p w j = 0) := by
  rcases aT_cases (tokAt w j) (tok_le w hw j) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨h1, ?_⟩
    have h := swb hr hu0 hu1 (aT (tokAt w j)) 1 (by simp [h2]) (hp.E (tokAt w j) 1)
    rw [abs_one, mul_one] at h
    unfold sav
    exact h
  · right
    refine ⟨h1, ?_⟩
    unfold sav
    rw [h2]
    exact sw_zero hr _

theorem scv_cases {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    (cbit (tokAt w j) = 0 ∧ scv fl p w j = 0) ∨
      (cbit (tokAt w j) = 1 ∧ |scv fl p w j - 1| ≤ 51 / 10000) := by
  rcases cT_cases (tokAt w j) (tok_le w hw j) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨h1, ?_⟩
    unfold scv
    rw [h2]
    exact sw_zero hr _
  · right
    refine ⟨h1, ?_⟩
    have h := swb hr hu0 hu1 (cT (tokAt w j)) 1 (by simp [h2]) (hp.E (tokAt w j) 2)
    rw [abs_one, mul_one] at h
    unfold scv
    exact h

/-! ### first marked token -/

theorem firstc_append (p : List ℕ) (t : ℕ) :
    firstc (p ++ [t]) = if firstc p = 0 then code t else firstc p := by
  simp [firstc, List.foldl_append]

theorem first_struct (w : List ℕ) : ∀ i : ℕ, i ≤ w.length →
    ((∀ k, 1 ≤ k → k ≤ i → code (tokAt w k) = 0) ∧ firstc (w.take i) = 0) ∨
    (∃ j, 1 ≤ j ∧ j ≤ i ∧ code (tokAt w j) ≠ 0 ∧
      (∀ k, 1 ≤ k → k < j → code (tokAt w k) = 0) ∧
      firstc (w.take i) = code (tokAt w j)) := by
  intro i
  induction i with
  | zero =>
    intro _
    left
    exact ⟨fun k h1 h2 => by omega, by simp [firstc]⟩
  | succ n ih =>
    intro hi
    have ih' := ih (by omega)
    have hlt : n < w.length := by omega
    have htake : w.take (n + 1) = w.take n ++ [tokAt w (n + 1)] := by
      rw [Lane4.Seq.tokAt_succ w n hlt]
      first
        | exact List.take_succ_eq_append_getElem hlt
        | (rw [List.take_succ, List.getElem?_eq_getElem hlt]; rfl)
    rw [htake, firstc_append]
    rcases ih' with ⟨hall, hf0⟩ | ⟨j, hj1, hjn, hjm, hbef, hfj⟩
    · rw [hf0, if_pos rfl]
      by_cases hc : code (tokAt w (n + 1)) = 0
      · left
        refine ⟨fun k h1 h2 => ?_, hc⟩
        by_cases hk : k = n + 1
        · subst hk; exact hc
        · exact hall k h1 (by omega)
      · right
        exact ⟨n + 1, by omega, le_refl _, hc, fun k h1 h2 => hall k h1 (by omega), rfl⟩
    · right
      have hne : firstc (w.take n) ≠ 0 := by rw [hfj]; exact hjm
      rw [if_neg hne]
      exact ⟨j, hj1, by omega, hjm, hbef, hfj⟩

theorem tokAt_getD (w : List ℕ) (i : ℕ) (hi : 1 ≤ i) : tokAt w i = w.getD (i - 1) 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  simp [tokAt]

theorem hxor (a c : ℕ) (ha : a ≤ 1) (hc : c ≤ 1) :
    (((a + c) % 2 : ℕ) : ℝ) = (a : ℝ) + c - 2 * ((a : ℝ) * c) := by
  interval_cases a <;> interval_cases c <;> norm_num

theorem sel_first {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) (j : ℕ) (hj1 : 1 ≤ j) (hji : j ≤ i)
    (hjm : code (tokAt w j) ≠ 0) (hbef : ∀ k, 1 ≤ k → k < j → code (tokAt w k) = 0) :
    hh.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = [j] := by
  apply Head.sel_unique
  · rw [show hh.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal]
    exact hji
  · intro k hk hne
    rw [show hh.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal] at hk
    rw [score_at hr p w hw i k, score_at hr p w hw i j]
    have hN2 : (2 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
      have : 2 ≤ w.length + 1 := by omega
      exact_mod_cast this
    have h5 := swm1 hr hu0 hu1 (hp.A 0 0 5 6)
    have h7 := swm2 hr hu0 hu1 (hp.A 0 0 7 0)
    obtain ⟨h5a, h5b⟩ := abs_le.mp h5
    obtain ⟨h7a, h7b⟩ := abs_le.mp h7
    obtain ⟨hpn1, hpn2⟩ := abs_le.mp (hr.natCast_near (w.length + 1))
    have hkb := hr.pos_le hu0 (show k ≤ w.length + 1 by omega) hn
    have hjb := hr.pos_le hu0 (show j ≤ w.length + 1 by omega) hn
    by_cases hkm : code (tokAt w k) = 0
    · have hsk : |suv fl p w k - 1| ≤ 51 / 10000 := by
        rcases suv_cases hr hu0 hu1 p hp w hw k with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd hkm h
      have hsj : suv fl p w j = 0 := by
        rcases suv_cases hr hu0 hu1 p hp w hw j with ⟨h, _⟩ | ⟨_, h⟩
        · exact absurd h hjm
        · exact h
      rw [hsj]
      obtain ⟨s1, s2⟩ := abs_le.mp hsk
      exact Sc_lt_unmarked hr hu0 hn hN2 (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) hjb.1 hjb.2 hkb.1 hkb.2 (by linarith)
        (by linarith)
    · have hjk : j < k := by
        rcases lt_or_gt_of_ne hne with h | h
        · exfalso
          by_cases hk0 : k = 0
          · apply hkm
            subst hk0
            simp [Lane4.Seq.tokAt_zero, code]
          · exact hkm (hbef k (by omega) h)
        · exact h
      have hsk : suv fl p w k = 0 := by
        rcases suv_cases hr hu0 hu1 p hp w hw k with ⟨h, _⟩ | ⟨_, h⟩
        · exact absurd h hkm
        · exact h
      have hsj : suv fl p w j = 0 := by
        rcases suv_cases hr hu0 hu1 p hp w hw j with ⟨h, _⟩ | ⟨_, h⟩
        · exact absurd h hjm
        · exact h
      rw [hsk, hsj]
      have hg := hr.pos_gap hu0 hjk (show k ≤ w.length + 1 by omega) hn
      exact Sc_lt_marked hr hu0 hn hN2 (by linarith) (by linarith) hjb.1 hjb.2 hkb.1 hkb.2 hg

theorem net_ok : Statement net := by
  intro u fl hr hu0 hu1 p hp w hw hn i hi1 hi
  obtain ⟨S, hSdef⟩ : ∃ S, hh.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = S :=
    ⟨_, rfl⟩
  have hout := out_eq hr p w hw i S hSdef
  have hcx : ∃ c0 : ℝ, (c0 = 0 ∨ c0 = 1) ∧ |scv fl p w i - c0| ≤ 11 / 1000 ∧
      c0 = ((cbit (tokAt w i) : ℕ) : ℝ) := by
    rcases scv_cases hr hu0 hu1 p hp w hw i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨0, Or.inl rfl, ?_, ?_⟩
      · rw [h2]; norm_num
      · rw [h1]; norm_num
    · refine ⟨1, Or.inr rfl, le_trans h2 (by norm_num), ?_⟩
      rw [h1]; norm_num
  have hax : ∃ a0 : ℝ, (a0 = 0 ∨ a0 = 1) ∧
      |ravg fl S (fun j => fl (sw fl 1 (p.V 0 0 3 1) * sav fl p w j)) - a0| ≤ 11 / 1000 ∧
      a0 = ((if firstc (w.take i) = 2 then 1 else 0 : ℕ) : ℝ) := by
    rcases first_struct w i hi with ⟨hall, hf0⟩ | ⟨j, hj1, hji, hjm, hbef, hfj⟩
    · have hAv : ravg fl S (fun j => fl (sw fl 1 (p.V 0 0 3 1) * sav fl p w j)) = 0 := by
        apply ravg_zero_on hr
        intro k hk
        rw [← hSdef] at hk
        obtain ⟨hkc, _⟩ := (Head.mem_sel hh fl (p.A 0 0) (w.length + 1) (net.init fl p w) i k).mp hk
        have hki : k ≤ i := by
          rw [show hh.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal] at hkc
          exact hkc
        have hck : code (tokAt w k) = 0 := by
          by_cases hk0 : k = 0
          · subst hk0
            simp [Lane4.Seq.tokAt_zero, code]
          · exact hall k (by omega) hki
        have hsa : sav fl p w k = 0 := by
          rcases sav_cases hr hu0 hu1 p hp w hw k with ⟨h, _⟩ | ⟨_, h⟩
          · rw [hck] at h; exact absurd h (by norm_num)
          · exact h
        show fl (sw fl 1 (p.V 0 0 3 1) * sav fl p w k) = 0
        rw [hsa]
        simp [hr.zero]
      refine ⟨0, Or.inl rfl, ?_, ?_⟩
      · rw [hAv]; norm_num
      · rw [hf0]; norm_num
    · have hsel := sel_first hr hu0 hu1 p hp w hw hn i hi1 hi j hj1 hji hjm hbef
      have hSj : S = [j] := by rw [← hSdef]; exact hsel
      have e : ravg fl S (fun j => fl (sw fl 1 (p.V 0 0 3 1) * sav fl p w j))
          = fl (sw fl 1 (p.V 0 0 3 1) * sav fl p w j) := by
        rw [hSj, ravg_singleton hr]
        exact hr.idem _
      rcases sav_cases hr hu0 hu1 p hp w hw j with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · refine ⟨1, Or.inr rfl, ?_, ?_⟩
        · rw [e]
          have hs := swp1 hr hu0 hu1 (hp.V 0 0 3 1)
          have hfm := fmul hr hu0 hu1 (S := 1) (V := 1) (k := 1) (N := 1) hs (by norm_num)
            (by norm_num) h3 (by norm_num) (by norm_num) (by norm_num)
          rw [abs_one] at hfm
          have : |fl (sw fl 1 (p.V 0 0 3 1) * sav fl p w j) - 1| ≤ 11 / 1000 := by linarith
          exact this
        · rw [hfj, if_pos h2]; norm_num
      · refine ⟨0, Or.inl rfl, ?_, ?_⟩
        · rw [e, h3]
          simp [hr.zero]
        · rw [hfj, if_neg h2]; norm_num
  obtain ⟨c0, hc0, hc, hc0e⟩ := hcx
  obtain ⟨a0, ha0, hA, ha0e⟩ := hax
  have hnum := fnum hr hu0 hu1 ha0 hc0 hA hc
    (swp1 hr hu0 hu1 (hp.W1 0 0 2)) (swp1 hr hu0 hu1 (hp.W1 0 0 3))
    (swp1 hr hu0 hu1 (hp.W2 0 4 0)) (swp1 hr hu0 hu1 (hp.oW 2))
    (swp1 hr hu0 hu1 (hp.oW 3)) (swm2 hr hu0 hu1 (hp.oW 4))
    (swm1 hr hu0 hu1 (hp.b1 0 0))
  have hcb1 : cbit (tokAt w i) ≤ 1 := by
    rcases cT_cases (tokAt w i) (tok_le w hw i) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hab1 : (if firstc (w.take i) = 2 then 1 else 0 : ℕ) ≤ 1 := by
    split_ifs <;> omega
  have htg : ((target w i : ℕ) : ℝ) = a0 + c0 - 2 * (a0 * c0) := by
    unfold target
    rw [← tokAt_getD w i hi1, hxor _ _ hab1 hcb1, ha0e, hc0e]
  rw [hout, htg]
  exact hnum

end Lane4.Case
