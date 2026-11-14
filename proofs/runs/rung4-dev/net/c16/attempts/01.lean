namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

/-- State: [z, k, c, h, 1, fl i, fl n] (width 7). z: propagate flag, k: generate flag. -/
def z7 : List ℚ := [0, 0, 0, 0, 0, 0, 0]

def hd : Head :=
  { A := [z7, z7, z7, z7, [0, 0, 0, 0, 0, 1, 0], z7, [-4, 0, 0, 0, 0, 0, 0]],
    V := [z7, z7, [0, 1, 0, 0, 0, 0, 0], z7, z7, z7, z7],
    mask := Mask.strict }

def blk : Block :=
  { heads := [hd], W1 := [[0, 1, 1, 0, 0, 0, 0]], b1 := [-1],
    W2 := [[0], [0], [0], [-3], [0], [0], [0]], b2 := z7 }

def net : TNet :=
  { embed := [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
    blocks := [blk],
    outW := [1, 2, 1, 1, 0, 0, 0],
    outB := 0 }

/-! ### real-number helper lemmas -/

theorem fc {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {x : ℝ} (hx : |x| ≤ 8) : |fl x - x| ≤ 1 / 2000000 := by
  have h := hr.err hu0 hx
  linarith

theorem mul_err {a b s t e1 e2 : ℝ} (ha : |a - s| ≤ e1) (hb : |b - t| ≤ e2) :
    |a * b - s * t| ≤ e1 * |t| + e1 * e2 + |s| * e2 := by
  have h : a * b - s * t = (a - s) * (b - t) + (a - s) * t + s * (b - t) := by ring
  have h1 : |(a - s) * (b - t)| ≤ e1 * e2 := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) (le_trans (abs_nonneg _) ha)
  have h2 : |(a - s) * t| ≤ e1 * |t| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have h3 : |s * (b - t)| ≤ |s| * e2 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  rw [h]
  have := abs_add_le ((a - s) * (b - t) + (a - s) * t) (s * (b - t))
  have := abs_add_le ((a - s) * (b - t)) ((a - s) * t)
  linarith

theorem step_mul {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {a b s t e1 e2 S T E : ℝ} (ha : |a - s| ≤ e1) (hb : |b - t| ≤ e2)
    (hs : |s| ≤ S) (ht : |t| ≤ T) (hE : e1 * T + e1 * e2 + S * e2 + 1 / 2000000 ≤ E)
    (hB : S * T + E ≤ 8) : |fl (a * b) - s * t| ≤ E := by
  have e1nn : 0 ≤ e1 := le_trans (abs_nonneg _) ha
  have e2nn : 0 ≤ e2 := le_trans (abs_nonneg _) hb
  have h1 := mul_err ha hb
  have h2 : e1 * |t| ≤ e1 * T := mul_le_mul_of_nonneg_left ht e1nn
  have h3 : |s| * e2 ≤ S * e2 := mul_le_mul_of_nonneg_right hs e2nn
  have h4 : |s * t| ≤ S * T := by
    rw [abs_mul]
    exact mul_le_mul hs ht (abs_nonneg _) (le_trans (abs_nonneg _) hs)
  have h5 : |a * b| ≤ 8 := by
    have := abs_add_le (s * t) (a * b - s * t)
    rw [show s * t + (a * b - s * t) = a * b by ring] at this
    linarith
  have h6 := fc hr hu0 hu1 h5
  have h7 := abs_add_le (fl (a * b) - a * b) (a * b - s * t)
  rw [show fl (a * b) - a * b + (a * b - s * t) = fl (a * b) - s * t by ring] at h7
  linarith

theorem step_add {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {a b p q e1 e2 E P : ℝ} (ha : |a - p| ≤ e1) (hb : |b - q| ≤ e2)
    (hE : e1 + e2 + 1 / 2000000 ≤ E) (hP : |p + q| ≤ P) (hB : P + E ≤ 8) :
    |fl (a + b) - (p + q)| ≤ E := by
  have e1nn : 0 ≤ e1 := le_trans (abs_nonneg _) ha
  have e2nn : 0 ≤ e2 := le_trans (abs_nonneg _) hb
  have h1 : |a + b - (p + q)| ≤ e1 + e2 := by
    have := abs_add_le (a - p) (b - q)
    rw [show a - p + (b - q) = a + b - (p + q) by ring] at this
    linarith
  have h5 : |a + b| ≤ 8 := by
    have := abs_add_le (p + q) (a + b - (p + q))
    rw [show p + q + (a + b - (p + q)) = a + b by ring] at this
    linarith
  have h6 := fc hr hu0 hu1 h5
  have h7 := abs_add_le (fl (a + b) - (a + b)) (a + b - (p + q))
  rw [show fl (a + b) - (a + b) + (a + b - (p + q)) = fl (a + b) - (p + q) by ring] at h7
  linarith

theorem relu_lip {x y e : ℝ} (h : |x - y| ≤ e) : |relu x - relu y| ≤ e := by
  show |max x 0 - max y 0| ≤ e
  obtain ⟨h1, h2⟩ := abs_le.mp h
  rw [abs_le]
  rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy
  · rw [max_eq_right hx, max_eq_right hy]; constructor <;> linarith
  · rw [max_eq_right hx, max_eq_left hy]; constructor <;> linarith
  · rw [max_eq_left hx, max_eq_right hy]; constructor <;> linarith
  · rw [max_eq_left hx, max_eq_left hy]; constructor <;> linarith

theorem relu_nn (x : ℝ) : 0 ≤ relu x := le_max_right x 0

theorem relu_le_one {x : ℝ} (hx : x ≤ 1) : relu x ≤ 1 := max_le hx (by norm_num)

theorem sw_ok {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    (w : ℚ) (x e : ℝ) (hx : (w : ℝ) = x) {d : ℝ} (hd : |d| ≤ 1 / 200)
    (he : 11 / 2000 * |x| ≤ e) : |sw fl w d - x| ≤ e := by
  have h := sw_rel (ε := 11 / 2000) hr hu0 w hd (by linarith)
  rw [hx] at h
  linarith

/-! ### the three stored embedding entries and the closed forms -/

theorem tok_le5 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

noncomputable def zS (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (if tokAt w j = 3 then 1 else 0) (p.E (tokAt w j) 0)

noncomputable def kS (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (if tokAt w j = 1 ∨ tokAt w j = 4 then 1 else 0) (p.E (tokAt w j) 1)

theorem fl_zS {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ) :
    fl (zS fl p w j) = zS fl p w j := by
  unfold zS sw
  exact hr.idem _

theorem fl_kS {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ) :
    fl (kS fl p w j) = kS fl p w j := by
  unfold kS sw
  exact hr.idem _

theorem init_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [zS fl p w j, kS fl p w j, 0, 0] ++ pos fl j (w.length + 1) := by
  have h6 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 ∨
      tokAt w j = 5 := by
    have := tok_le5 w hw j
    omega
  rcases h6 with h | h | h | h | h | h <;>
    simp [TNet.init, net, swRow, zS, kS, h, sw_zero hr]

theorem zS_ne {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ)
    (h : tokAt w j ≠ 3) : zS fl p w j = 0 := by
  unfold zS
  rw [if_neg h]
  exact sw_zero hr _

theorem kS_ne {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ)
    (h : ¬ (tokAt w j = 1 ∨ tokAt w j = 4)) : kS fl p w j = 0 := by
  unfold kS
  rw [if_neg h]
  exact sw_zero hr _

theorem zS_one {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {p : Pert} (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ)
    (h : tokAt w j = 3) : |zS fl p w j - 1| ≤ 11 / 2000 := by
  unfold zS
  rw [if_pos h]
  exact sw_ok hr hu0 hu1 1 1 (11 / 2000) (by norm_num) (hp.E _ 0) (by norm_num)

theorem kS_one {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {p : Pert} (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ)
    (h : tokAt w j = 1 ∨ tokAt w j = 4) : |kS fl p w j - 1| ≤ 11 / 2000 := by
  unfold kS
  rw [if_pos h]
  exact sw_ok hr hu0 hu1 1 1 (11 / 2000) (by norm_num) (hp.E _ 1) (by norm_num)

theorem zS_near {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {p : Pert} (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ) :
    |zS fl p w j - (if tokAt w j = 3 then 1 else 0)| ≤ 11 / 2000 := by
  by_cases h : tokAt w j = 3
  · rw [if_pos h]
    exact zS_one hr hu0 hu1 hp w j h
  · rw [if_neg h, zS_ne hr p w j h]
    norm_num

theorem kS_near {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {p : Pert} (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ) :
    |kS fl p w j - (if tokAt w j = 1 ∨ tokAt w j = 4 then 1 else 0)| ≤ 11 / 2000 := by
  by_cases h : tokAt w j = 1 ∨ tokAt w j = 4
  · rw [if_pos h]
    exact kS_one hr hu0 hu1 hp w j h
  · rw [if_neg h, kS_ne hr p w j h]
    norm_num

/-! ### the score -/

theorem score_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (zi ki ci hi qi qn zj kj cj hj qk qn' : ℝ) :
    hd.score fl dA [zi, ki, ci, hi, 1, qi, qn] [zj, kj, cj, hj, 1, qk, qn']
      = fl (fl (sw fl 1 (dA 4 5) * qk) + fl (qn * fl (sw fl (-4) (dA 6 0) * zj))) := by
  simp [Head.score, hd, z7, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem]

theorem prop_lt {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {bb a zk N fn fk fj : ℝ} (hN2 : 2 ≤ N) (hn : u * N ≤ 1 / 256)
    (hfn1 : N - 1 / 256 ≤ fn) (hfn2 : fn ≤ N + 1 / 256) (hk0 : 0 ≤ fk)
    (hk1 : fk ≤ N + 1 / 256) (hj0 : 0 ≤ fj) (hbb : |bb - 1| ≤ 11 / 2000)
    (haa : |a - (-4)| ≤ 11 / 500) (hz : |zk - 1| ≤ 11 / 2000) :
    fl (fl (bb * fk) + fl (fn * fl (a * zk))) < fl (bb * fj) := by
  obtain ⟨hbl, hbu⟩ := abs_le.mp hbb
  have hY := step_mul (S := 4) (T := 1) (E := 45 / 1000) hr hu0 hu1 haa hz (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hYl, hYu⟩ := abs_le.mp hY
  have hfn0 : 0 ≤ fn := by linarith
  have hx2u : fn * fl (a * zk) ≤ fn * (-39 / 10) :=
    mul_le_mul_of_nonneg_left (by linarith) hfn0
  have hx2l : fn * (-41 / 10) ≤ fn * fl (a * zk) :=
    mul_le_mul_of_nonneg_left (by linarith) hfn0
  have hx2abs : |fn * fl (a * zk)| ≤ 5 * N := abs_le.mpr ⟨by linarith, by linarith⟩
  have hT2 := hr.upper hu0 hx2abs
  have hx1 : bb * fk ≤ (1 + 11 / 2000) * (N + 1 / 256) :=
    mul_le_mul (by linarith) hk1 hk0 (by norm_num)
  have hx1n : 0 ≤ bb * fk := mul_nonneg (by linarith) hk0
  have hx1abs : |bb * fk| ≤ 2 * N := abs_le.mpr ⟨by linarith, by linarith⟩
  have hT1 := hr.upper hu0 hx1abs
  have hsum : fl (bb * fk) + fl (fn * fl (a * zk)) ≤ -1 := by linarith
  have hm := hr.mono _ _ hsum
  have hneg : fl (-1) = -1 := by rw [hr.neg, hr.one]
  rw [hneg] at hm
  have hsj : 0 ≤ fl (bb * fj) := hr.nonneg (mul_nonneg (by linarith) hj0)
  linarith

theorem nonprop_lt {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {bb N fk fj : ℝ} (hN2 : 2 ≤ N) (hn : u * N ≤ 1 / 256)
    (hbb : |bb - 1| ≤ 11 / 2000) (hk0 : 0 ≤ fk) (hk1 : fk ≤ N + 1 / 256)
    (hj1 : fj ≤ N + 1 / 256) (hg : fk + 127 / 128 ≤ fj) :
    fl (bb * fk) < fl (bb * fj) := by
  obtain ⟨hbl, hbu⟩ := abs_le.mp hbb
  have hbb0 : 0 ≤ bb := by linarith
  have hj0 : 0 ≤ fj := by linarith
  have hx : bb * fk ≤ (1 + 11 / 2000) * (N + 1 / 256) :=
    mul_le_mul (by linarith) hk1 hk0 (by norm_num)
  have hy : bb * fj ≤ (1 + 11 / 2000) * (N + 1 / 256) :=
    mul_le_mul (by linarith) hj1 hj0 (by norm_num)
  have hxn : 0 ≤ bb * fk := mul_nonneg hbb0 hk0
  have hyn : 0 ≤ bb * fj := mul_nonneg hbb0 hj0
  have h1 := mul_le_mul_of_nonneg_left hg hbb0
  apply hr.lt_of_gap hu0 (B := 2 * N)
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · linarith

theorem sel_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i j : ℕ) (hji : j < i) (hi : i ≤ w.length) (htj : tokAt w j ≠ 3)
    (hk3 : ∀ k, j < k → k < i → tokAt w k = 3) :
    hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = [j] := by
  have hbb := sw_ok hr hu0 hu1 1 1 (11 / 2000) (by norm_num) (hp.A 0 0 4 5) (by norm_num)
  have haa := sw_ok hr hu0 hu1 (-4) (-4) (11 / 500) (by norm_num) (hp.A 0 0 6 0) (by norm_num)
  have hN2 : (2 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    have : 2 ≤ w.length + 1 := by omega
    exact_mod_cast this
  have hNn := abs_le.mp (hr.natCast_near (w.length + 1))
  have hfn1 : ((w.length + 1 : ℕ) : ℝ) - 1 / 256 ≤ fl ((w.length + 1 : ℕ) : ℝ) := by
    linarith [hNn.1]
  have hfn2 : fl ((w.length + 1 : ℕ) : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) + 1 / 256 := by
    linarith [hNn.2]
  apply Head.sel_unique
  · rw [show hd.mask = Mask.strict from rfl, Lane4.Seq.mem_cand_strict]
    exact hji
  · intro k hk hne
    rw [show hd.mask = Mask.strict from rfl, Lane4.Seq.mem_cand_strict] at hk
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    have hk' := hr.pos_le hu0 (show k ≤ w.length + 1 by omega) hn
    have hj' := hr.pos_le hu0 (show j ≤ w.length + 1 by omega) hn
    rw [zS_ne hr p w j htj]
    by_cases hkz : tokAt w k = 3
    · simp only [score_eq hr, mul_zero, hr.zero, add_zero, hr.idem]
      exact prop_lt hr hu0 hu1 hN2 hn hfn1 hfn2 hk'.1 hk'.2 hj'.1 hbb haa
        (zS_one hr hu0 hu1 hp w k hkz)
    · have hkj : k < j := by
        rcases lt_or_gt_of_ne hne with h | h
        · exact h
        · exact absurd (hk3 k h hk) hkz
      rw [zS_ne hr p w k hkz]
      simp only [score_eq hr, mul_zero, hr.zero, add_zero, hr.idem]
      exact nonprop_lt hr hu0 hu1 hN2 hn hbb hk'.1 hk'.2 hj'.2
        (hr.pos_gap hu0 hkj (show j ≤ w.length + 1 by omega) hn)

/-! ### the output in closed form -/

noncomputable def Cv (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  fl (sw fl 1 (p.V 0 0 2 1) * kS fl p w j)

noncomputable def preV (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (i j : ℕ) : ℝ :=
  fl (fl (fl (sw fl 1 (p.W1 0 0 1) * kS fl p w i) + fl (sw fl 1 (p.W1 0 0 2) * Cv fl p w j))
    + sw fl (-1) (p.b1 0 0))

noncomputable def HnV (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (i j : ℕ) : ℝ :=
  fl (sw fl (-3) (p.W2 0 3 0) * relu (preV fl p w i j))

theorem out_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i j : ℕ)
    (hsel : hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = [j]) :
    net.out fl p w i
      = fl (fl (fl (fl (sw fl 1 (p.oW 0) * zS fl p w i) + fl (sw fl 2 (p.oW 1) * kS fl p w i))
          + fl (sw fl 1 (p.oW 2) * Cv fl p w j)) + fl (sw fl 1 (p.oW 3) * HnV fl p w i j)) := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [1, 2, 1, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  have hV : hd.V = [z7, z7, [0, 1, 0, 0, 0, 0, 0], z7, z7, z7, z7] := rfl
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [runFrom, Block.apply, blk, headsApply, Head.attn, hsel, hV, attnRows,
    ravg_singleton hr]
  simp only [init_eq hr p w hw]
  simp [Cv, preV, HnV, z7, pos, rdot, radd, raffine, sw_zero hr, hr.zero, hr.idem, hr.one,
    fl_sw hr, fl_zS hr, fl_kS hr]

/-! ### error bounds -/

theorem preB {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {kS C s1 s2 sb K c : ℝ} (hK : 0 ≤ K ∧ K ≤ 1)
    (hc : 0 ≤ c ∧ c ≤ 1) (hkS : |kS - K| ≤ 11 / 2000) (hC : |C - c| ≤ 1 / 80)
    (hs1 : |s1 - 1| ≤ 11 / 2000) (hs2 : |s2 - 1| ≤ 11 / 2000)
    (hsb : |sb - (-1)| ≤ 11 / 2000) :
    |fl (fl (fl (s1 * kS) + fl (s2 * C)) + sb) - (K + c - 1)| ≤ 349 / 10000 := by
  obtain ⟨hK0, hK1⟩ := hK
  obtain ⟨hc0, hc1⟩ := hc
  have hKa : |K| ≤ 1 := abs_le.mpr ⟨by linarith, hK1⟩
  have hca : |c| ≤ 1 := abs_le.mpr ⟨by linarith, hc1⟩
  have a1 := step_mul (S := 1) (T := 1) (E := 111 / 10000) hr hu0 hu1 hs1 hkS (by norm_num) hKa
    (by norm_num) (by norm_num)
  have a1' := step_mul (S := 1) (T := 1) (E := 181 / 10000) hr hu0 hu1 hs2 hC (by norm_num) hca
    (by norm_num) (by norm_num)
  have a2 := step_add (P := 2) (E := 293 / 10000) hr hu0 hu1 a1 a1' (by norm_num)
    (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)
  have a3 := step_add (P := 2) (E := 349 / 10000) hr hu0 hu1 a2 hsb (by norm_num)
    (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)
  obtain ⟨l, r⟩ := abs_le.mp a3
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem HnB {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {sh pre K c : ℝ} (hK : 0 ≤ K ∧ K ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1)
    (hsh : |sh - (-3)| ≤ 33 / 2000) (hp : |pre - (K + c - 1)| ≤ 349 / 10000) :
    |fl (sh * relu pre) - (-3) * relu (K + c - 1)| ≤ 1218 / 10000 := by
  have hl := relu_lip hp
  have hR0 := relu_nn (K + c - 1)
  have hR1 : relu (K + c - 1) ≤ 1 := relu_le_one (by linarith [hK.2, hc.2])
  have hRa : |relu (K + c - 1)| ≤ 1 := abs_le.mpr ⟨by linarith, hR1⟩
  exact step_mul (S := 3) (T := 1) (E := 1218 / 10000) hr hu0 hu1 hsh hl (by norm_num) hRa
    (by norm_num) (by norm_num)

theorem finB {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {zS kS C Hn o0 o1 o2 o3 Z K c : ℝ}
    (hZ : 0 ≤ Z ∧ Z ≤ 1) (hK : 0 ≤ K ∧ K ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1)
    (hzS : |zS - Z| ≤ 11 / 2000) (hkS : |kS - K| ≤ 11 / 2000) (hC : |C - c| ≤ 1 / 80)
    (ho0 : |o0 - 1| ≤ 11 / 2000) (ho1 : |o1 - 2| ≤ 11 / 1000) (ho2 : |o2 - 1| ≤ 11 / 2000)
    (ho3 : |o3 - 1| ≤ 11 / 2000)
    (hHn : |Hn - (-3) * relu (K + c - 1)| ≤ 1218 / 10000) :
    |fl (fl (fl (fl (o0 * zS) + fl (o1 * kS)) + fl (o2 * C)) + fl (o3 * Hn))
      - (Z + 2 * K + c + (-3) * relu (K + c - 1))| ≤ 1 / 5 := by
  obtain ⟨hZ0, hZ1⟩ := hZ
  obtain ⟨hK0, hK1⟩ := hK
  obtain ⟨hc0, hc1⟩ := hc
  have hZa : |Z| ≤ 1 := abs_le.mpr ⟨by linarith, hZ1⟩
  have hKa : |K| ≤ 1 := abs_le.mpr ⟨by linarith, hK1⟩
  have hca : |c| ≤ 1 := abs_le.mpr ⟨by linarith, hc1⟩
  have hR0 := relu_nn (K + c - 1)
  have hR1 : relu (K + c - 1) ≤ 1 := relu_le_one (by linarith)
  have hRa : |(-3) * relu (K + c - 1)| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  have P0 := step_mul (S := 1) (T := 1) (E := 111 / 10000) hr hu0 hu1 ho0 hzS (by norm_num) hZa
    (by norm_num) (by norm_num)
  have P1 := step_mul (S := 2) (T := 1) (E := 221 / 10000) hr hu0 hu1 ho1 hkS (by norm_num) hKa
    (by norm_num) (by norm_num)
  have S1 := step_add (P := 3) (E := 333 / 10000) hr hu0 hu1 P0 P1 (by norm_num)
    (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)
  have P2 := step_mul (S := 1) (T := 1) (E := 181 / 10000) hr hu0 hu1 ho2 hC (by norm_num) hca
    (by norm_num) (by norm_num)
  have S2 := step_add (P := 4) (E := 515 / 10000) hr hu0 hu1 S1 P2 (by norm_num)
    (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)
  have P3 := step_mul (S := 1) (T := 3) (E := 139 / 1000) hr hu0 hu1 ho3 hHn (by norm_num) hRa
    (by norm_num) (by norm_num)
  have S3 := step_add (P := 4) (E := 1906 / 10000) hr hu0 hu1 S2 P3 (by norm_num)
    (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)
  obtain ⟨l, r⟩ := abs_le.mp S3
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem Cv_near {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {p : Pert} (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ) :
    |Cv fl p w j - (if tokAt w j = 1 ∨ tokAt w j = 4 then 1 else 0)| ≤ 1 / 80 := by
  have hv := sw_ok hr hu0 hu1 1 1 (11 / 2000) (by norm_num) (hp.V 0 0 2 1) (by norm_num)
  have hk := kS_near hr hu0 hu1 hp w j
  have hKb : |(if tokAt w j = 1 ∨ tokAt w j = 4 then (1 : ℝ) else 0)| ≤ 1 := by
    split_ifs <;> norm_num
  have := step_mul (S := 1) (T := 1) (E := 111 / 10000) hr hu0 hu1 hv hk (by norm_num) hKb
    (by norm_num) (by norm_num)
  rw [one_mul] at this
  unfold Cv
  exact le_trans this (by norm_num)

theorem preV_near {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {p : Pert} (hp : p.Within (1 / 200)) (w : List ℕ) (i j : ℕ) :
    |preV fl p w i j - ((if tokAt w i = 1 ∨ tokAt w i = 4 then 1 else 0)
      + (if tokAt w j = 1 ∨ tokAt w j = 4 then 1 else 0) - 1)| ≤ 349 / 10000 := by
  have hs1 := sw_ok hr hu0 hu1 1 1 (11 / 2000) (by norm_num) (hp.W1 0 0 1) (by norm_num)
  have hs2 := sw_ok hr hu0 hu1 1 1 (11 / 2000) (by norm_num) (hp.W1 0 0 2) (by norm_num)
  have hsb := sw_ok hr hu0 hu1 (-1) (-1) (11 / 2000) (by norm_num) (hp.b1 0 0) (by norm_num)
  unfold preV
  exact preB hr hu0 hu1 (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
    (kS_near hr hu0 hu1 hp w i) (Cv_near hr hu0 hu1 hp w j) hs1 hs2 hsb

theorem HnV_near {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {p : Pert} (hp : p.Within (1 / 200)) (w : List ℕ) (i j : ℕ) :
    |HnV fl p w i j - (-3) * relu ((if tokAt w i = 1 ∨ tokAt w i = 4 then 1 else 0)
      + (if tokAt w j = 1 ∨ tokAt w j = 4 then 1 else 0) - 1)| ≤ 1218 / 10000 := by
  have hsh := sw_ok hr hu0 hu1 (-3) (-3) (33 / 2000) (by norm_num) (hp.W2 0 3 0) (by norm_num)
  unfold HnV
  exact HnB hr hu0 hu1 (by split_ifs <;> norm_num) (by split_ifs <;> norm_num) hsh
    (preV_near hr hu0 hu1 hp w i j)

/-! ### the carry -/

theorem carry_ex (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) :
    ∀ m, m ≤ w.length → ∃ j, j ≤ m ∧ tokAt w j ≠ 3 ∧
      (∀ k, j < k → k ≤ m → tokAt w k = 3) ∧
      carry (w.take m) = (if (tokAt w j = 1 ∨ tokAt w j = 4) then 1 else 0) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨0, le_refl _, ?_, ?_, ?_⟩
    · rw [Lane4.Seq.tokAt_zero]; norm_num
    · intro k hk1 hk2; omega
    · rw [Lane4.Seq.tokAt_zero]; simp [carry]
  | succ m ih =>
    intro hm
    obtain ⟨j, hjm, hjt, hjk, hjc⟩ := ih (by omega)
    have hlt : m < w.length := by omega
    have htk : tokAt w (m + 1) = w[m] := Lane4.Seq.tokAt_succ w m hlt
    have hw5 := hw w[m] (List.getElem_mem hlt)
    have htake : w.take (m + 1) = w.take m ++ [w[m]] := by
      first
        | exact List.take_succ_eq_append_getElem hlt
        | simp [List.take_succ, List.getElem?_eq_getElem hlt]
    have hcar : carry (w.take (m + 1)) = if cls w[m] = 2 then carry (w.take m) else cls w[m] := by
      rw [htake]
      simp [carry, List.foldl_append]
    by_cases h3 : w[m] = 3
    · refine ⟨j, by omega, hjt, ?_, ?_⟩
      · intro k hk1 hk2
        by_cases hkm : k ≤ m
        · exact hjk k hk1 hkm
        · have hk : k = m + 1 := by omega
          subst hk
          rw [htk]
          exact h3
      · rw [hcar, h3]
        simp [cls, hjc]
    · refine ⟨m + 1, le_refl _, ?_, ?_, ?_⟩
      · rw [htk]; exact h3
      · intro k hk1 hk2; omega
      · rw [hcar, htk]
        have h4 : w[m] = 1 ∨ w[m] = 2 ∨ w[m] = 4 ∨ w[m] = 5 := by omega
        rcases h4 with h | h | h | h <;> simp [cls, h]

theorem ideal_eq (t : ℕ) (ht : 1 ≤ t ∧ t ≤ 5) (g : Prop) [Decidable g] :
    (((dg t + (if g then 1 else 0)) % 3 : ℕ) : ℝ)
      = (if t = 3 then 1 else 0) + 2 * (if t = 1 ∨ t = 4 then 1 else 0)
        + (if g then 1 else 0)
        + (-3) * relu ((if t = 1 ∨ t = 4 then 1 else 0) + (if g then 1 else 0) - 1) := by
  obtain ⟨h1, h5⟩ := ht
  by_cases hg : g
  · simp only [if_pos hg]
    interval_cases t <;> norm_num [dg, relu, max_def]
  · simp only [if_neg hg]
    interval_cases t <;> norm_num [dg, relu, max_def]

/-! ### main theorem -/

theorem net_ok : Statement net := by
  intro u fl hr hu0 hu1 p hp w hw hn i hi1 hi
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hm : m < w.length := by omega
  obtain ⟨j, hjm, hjt, hjk, hjc⟩ := carry_ex w hw m (by omega)
  have hsel := sel_eq hr hu0 hu1 p hp w hw hn (m + 1) j (by omega) hi hjt
    (fun k hk1 hk2 => hjk k hk1 (by omega))
  rw [out_eq hr p w hw (m + 1) j hsel]
  have htok : 1 ≤ tokAt w (m + 1) ∧ tokAt w (m + 1) ≤ 5 := by
    rw [Lane4.Seq.tokAt_succ w m hm]
    exact hw _ (List.getElem_mem hm)
  have hid : ((target w (m + 1) : ℕ) : ℝ)
      = (if tokAt w (m + 1) = 3 then 1 else 0)
        + 2 * (if tokAt w (m + 1) = 1 ∨ tokAt w (m + 1) = 4 then 1 else 0)
        + (if tokAt w j = 1 ∨ tokAt w j = 4 then 1 else 0)
        + (-3) * relu ((if tokAt w (m + 1) = 1 ∨ tokAt w (m + 1) = 4 then 1 else 0)
          + (if tokAt w j = 1 ∨ tokAt w j = 4 then 1 else 0) - 1) := by
    have htg : target w (m + 1) = (dg (tokAt w (m + 1)) + carry (w.take m)) % 3 := by
      simp [target, tokAt]
    rw [htg, hjc]
    exact ideal_eq _ htok (tokAt w j = 1 ∨ tokAt w j = 4)
  rw [hid]
  have ho0 := sw_ok hr hu0 hu1 1 1 (11 / 2000) (by norm_num) (hp.oW 0) (by norm_num)
  have ho1 := sw_ok hr hu0 hu1 2 2 (11 / 1000) (by norm_num) (hp.oW 1) (by norm_num)
  have ho2 := sw_ok hr hu0 hu1 1 1 (11 / 2000) (by norm_num) (hp.oW 2) (by norm_num)
  have ho3 := sw_ok hr hu0 hu1 1 1 (11 / 2000) (by norm_num) (hp.oW 3) (by norm_num)
  have key := finB hr hu0 hu1 (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
    (by split_ifs <;> norm_num) (zS_near hr hu0 hu1 hp w (m + 1))
    (kS_near hr hu0 hu1 hp w (m + 1)) (Cv_near hr hu0 hu1 hp w j) ho0 ho1 ho2 ho3
    (HnV_near hr hu0 hu1 hp w (m + 1) j)
  obtain ⟨l, r⟩ := abs_le.mp key
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Lane4.Case
