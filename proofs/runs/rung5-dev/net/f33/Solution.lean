namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false

def z9 : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0, 0]
def z1 : List ℚ := [0]

def blk0 : Block :=
  { heads := [], W1 := [[-4, 0, 0, 0, 0, 0, 0, 0, 0]], b1 := [1],
    W2 := [z1, z1, z1, [-1], z1, z1, z1, z1, z1], b2 := [0, 0, 0, 1, 0, 0, 0, 0, 0] }

def hdA : Head :=
  { A := [z9, z9, z9, z9, z9, z9, [0, 0, 0, 0, 0, 0, 0, -20, 0], z9,
          [0, 0, 0, 60, 0, 0, 0, 0, 0]],
    V := [z9, z9, z9, z9, [0, 1, 0, 0, 0, 0, 0, 0, 0], z9, z9, z9, z9],
    mask := Mask.causal }

def blk1 : Block :=
  { heads := [hdA], W1 := [[0, 0, 1, 0, 1, 0, 0, 0, 0]], b1 := [-1],
    W2 := [z1, z1, z1, z1, z1, [-2], z1, z1, z1], b2 := z9 }

def net : TNet :=
  { embed := [[0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0],
              [0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0]],
    blocks := [blk0, blk1],
    outW := [0, 0, 1, 0, 1, 1, 0, 0, 0],
    outB := 0 }

def mq (t : ℕ) : ℚ := if t = 1 ∨ t = 4 then 1 else 0
def aq (t : ℕ) : ℚ := if t = 1 then 1 else 0
def cq (t : ℕ) : ℚ := if t = 2 ∨ t = 3 then 1 else 0

theorem mq_01 (t : ℕ) : mq t = 0 ∨ mq t = 1 := by
  unfold mq; split_ifs <;> simp
theorem aq_01 (t : ℕ) : aq t = 0 ∨ aq t = 1 := by
  unfold aq; split_ifs <;> simp
theorem cq_01 (t : ℕ) : cq t = 0 ∨ cq t = 1 := by
  unfold cq; split_ifs <;> simp

theorem mq_one {t : ℕ} : mq t = 1 ↔ (t = 1 ∨ t = 4) := by
  unfold mq; split_ifs with h <;> simp [h]
theorem mq_zero {t : ℕ} : mq t = 0 ↔ ¬ (t = 1 ∨ t = 4) := by
  unfold mq; split_ifs with h <;> simp [h]
theorem aq_one {t : ℕ} : aq t = 1 ↔ t = 1 := by
  unfold aq; split_ifs with h <;> simp [h]
theorem aq_zero {t : ℕ} : aq t = 0 ↔ t ≠ 1 := by
  unfold aq; split_ifs with h <;> simp [h]
theorem cq_one {t : ℕ} : cq t = 1 ↔ (t = 2 ∨ t = 3) := by
  unfold cq; split_ifs with h <;> simp [h]

noncomputable def eM (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (mq (tokAt w j)) (p.E (tokAt w j) 0)
noncomputable def eA (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (aq (tokAt w j)) (p.E (tokAt w j) 1)
noncomputable def eC (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (cq (tokAt w j)) (p.E (tokAt w j) 2)

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) : tokAt w j ≤ 4 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) :
    net.init fl p w j = [eM fl p w j, eA fl p w j, eC fl p w j, 0, 0, 0]
      ++ pos fl j (w.length + 1) := by
  have h5 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 := by
    have := tok_le w hw j
    omega
  rcases h5 with h | h | h | h | h <;>
    simp [TNet.init, net, eM, eA, eC, mq, aq, cq, swRow, h, sw_zero hr]

section kit
variable {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {n : ℕ}

structure Env (u η M : ℝ) (fl : ℝ → ℝ) (p : Pert) (n : ℕ) : Prop where
  hr : Rnd u η M fl
  hu0 : 0 ≤ u
  hu1 : u ≤ 1 / 2 ^ 24
  hη : η ≤ 1 / 2 ^ 149
  hp : p.Within (1 / 200)
  hn1 : 1 ≤ n
  hun : u * (n : ℝ) ≤ 1 / 256
  hM : 1000 * (n : ℝ) ≤ M

theorem Env.hnR (E : Env u η M fl p n) : (1 : ℝ) ≤ n := by exact_mod_cast E.hn1
theorem Env.hM1 (E : Env u η M fl p n) : (1000 : ℝ) ≤ M := by
  have := E.hnR; linarith [E.hM]
theorem Env.hnM (E : Env u η M fl p n) : (n : ℝ) ≤ M := by
  have := E.hnR; linarith [E.hM]

theorem hε_ok (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) :
    (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by
  have h : u ≤ 1 / 10 ^ 7 := le_trans hu (by norm_num)
  linarith

theorem swn (E : Env u η M fl p n) (q : ℚ) (c : ℝ) (hq : (q : ℝ) = c) (hc : |c| ≤ 100)
    {d : ℝ} (hd : |d| ≤ 1 / 200) (e : ℝ) (he : |c| / 199 + 1 / 10 ^ 30 ≤ e) :
    |sw fl q d - c| ≤ e := by
  have h1 := Lane4.RSoft.sw_near E.hr E.hu0 q hd (by norm_num)
    (by rw [hq]; linarith [E.hM1]) (hε_ok E.hu0 E.hu1)
  rw [hq] at h1
  have h2 := eta_tiny E.hη
  have h3 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 10 ^ 30 := by norm_num
  linarith

theorem flswg (E : Env u η M fl p n) (q : ℚ) (c : ℝ) (hq : (q : ℝ) = c) (hc : |c| ≤ 100)
    {d : ℝ} (hd : |d| ≤ 1 / 200) : fl (sw fl q d) = sw fl q d :=
  Lane4.RSoft.fl_sw E.hr q hd (by norm_num) (by rw [hq]; linarith [E.hM1])

theorem sw01 (E : Env u η M fl p n) (q : ℚ) (hq : q = 0 ∨ q = 1) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    (q = 0 ∧ sw fl q d = 0) ∨ (q = 1 ∧ |sw fl q d - 1| ≤ 51 / 10000) := by
  rcases hq with h | h
  · left; subst h; exact ⟨rfl, sw_zero E.hr d⟩
  · right; subst h
    exact ⟨rfl, swn E 1 1 (by norm_num) (by norm_num) hd _ (by norm_num)⟩

theorem flsw01 (E : Env u η M fl p n) (q : ℚ) (hq : q = 0 ∨ q = 1) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    fl (sw fl q d) = sw fl q d := by
  rcases hq with h | h
  · subst h; rw [sw_zero E.hr, E.hr.zero]
  · subst h; exact flswg E 1 1 (by norm_num) (by norm_num) hd

theorem fl_e (E : Env u η M fl p n) {x : ℝ} (hx : |x| ≤ 100 * (n : ℝ)) :
    |fl x - x| ≤ 2 / 5 := by
  have hMn : 100 * (n : ℝ) ≤ M := by have := E.hnR; linarith [E.hM]
  have h1 := E.hr.abs E.hu0 hx hMn
  have h2 := eta_tiny E.hη
  have h3 : u * (100 * (n : ℝ)) = 100 * (u * (n : ℝ)) := by ring
  have h4 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100 := by norm_num
  linarith [E.hun]

theorem fl_small (E : Env u η M fl p n) {x B : ℝ} (hx : |x| ≤ B) (hB : B ≤ 100) :
    |fl x - x| ≤ 1 / 10 ^ 5 := by
  have hBM : B ≤ M := by linarith [E.hM1]
  have h1 := E.hr.abs E.hu0 hx hBM
  have h2 := eta_tiny E.hη
  have h3 : u * B ≤ 1 / 2 ^ 24 * 100 := by
    have h0 : 0 ≤ B := le_trans (abs_nonneg _) hx
    calc u * B ≤ u * 100 := mul_le_mul_of_nonneg_left hB E.hu0
      _ ≤ 1 / 2 ^ 24 * 100 := by nlinarith [E.hu1]
  have h4 : (1 : ℝ) / 2 ^ 24 * 100 + 1 / 10 ^ 40 ≤ 1 / 10 ^ 5 := by norm_num
  linarith


theorem absmul_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hA : 0 ≤ A) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) hA

theorem swle (E : Env u η M fl p n) (q : ℚ) (c : ℝ) (hq : (q : ℝ) = c) (hc : |c| ≤ 4)
    {d : ℝ} (hd : |d| ≤ 1 / 200) : |sw fl q d| ≤ 5 := by
  have h := swn E q c hq (by linarith) hd (|c| / 199 + 1 / 10 ^ 30) le_rfl
  have h2 := abs_sub_abs_le_abs_sub (sw fl q d) c
  have h3 : |c| / 199 ≤ 1 / 10 := by linarith
  have h4 : (1 : ℝ) / 10 ^ 30 ≤ 1 / 10 := by norm_num
  linarith

theorem fl_pos_fix (E : Env u η M fl p n) {k : ℕ} (hk : k ≤ n) :
    fl (fl (k : ℝ)) = fl (k : ℝ) := by
  apply E.hr.idem
  rw [abs_of_nonneg (Nat.cast_nonneg k)]
  have : (k : ℝ) ≤ n := by exact_mod_cast hk
  linarith [E.hnM]

noncomputable def hv (fl : ℝ → ℝ) (p : Pert) (m : ℝ) : ℝ :=
  relu (fl (fl (sw fl (-4) (p.W1 0 0 0) * m) + sw fl 1 (p.b1 0 0)))

noncomputable def mmf (fl : ℝ → ℝ) (p : Pert) (h : ℝ) : ℝ :=
  fl (fl (sw fl (-1) (p.W2 0 3 0) * h) + sw fl 1 (p.b2 0 3))

theorem hv_marked (E : Env u η M fl p n) {m : ℝ} (hm : |m - 1| ≤ 51 / 10000) :
    hv fl p m = 0 := by
  have hr := E.hr
  have hw4 := swn E (-4) (-4) (by norm_num) (by norm_num) (E.hp.W1 0 0 0) (21 / 1000)
    (by norm_num)
  have hsb := swn E 1 1 (by norm_num) (by norm_num) (E.hp.b1 0 0) (51 / 10000) (by norm_num)
  obtain ⟨hw1, hw2⟩ := abs_le.mp hw4
  obtain ⟨hm1, hm2⟩ := abs_le.mp hm
  obtain ⟨hs1, hs2⟩ := abs_le.mp hsb
  have hm0 : 0 ≤ m := by linarith
  have hY1 : sw fl (-4) (p.W1 0 0 0) * m ≤ -7 / 2 := by
    have := mul_le_mul_of_nonneg_right
      (show sw fl (-4) (p.W1 0 0 0) ≤ -3979 / 1000 by linarith) hm0
    linarith
  have hY2 : -5 ≤ sw fl (-4) (p.W1 0 0 0) * m := by
    have := mul_le_mul_of_nonneg_right
      (show -4021 / 1000 ≤ sw fl (-4) (p.W1 0 0 0) by linarith) hm0
    linarith
  have hYa : |sw fl (-4) (p.W1 0 0 0) * m| ≤ 5 := abs_le.mpr ⟨hY2, by linarith⟩
  have hs5 := fl_small E hYa (by norm_num)
  obtain ⟨hf1, hf2⟩ := abs_le.mp hs5
  have hx : fl (sw fl (-4) (p.W1 0 0 0) * m) + sw fl 1 (p.b1 0 0) ≤ 0 := by linarith
  have hxM : -M ≤ fl (sw fl (-4) (p.W1 0 0 0) * m) + sw fl 1 (p.b1 0 0) := by
    linarith [E.hM1]
  have hfl := hr.nonpos hx hxM
  unfold hv
  exact relu_of_nonpos hfl

theorem hv_unm (E : Env u η M fl p n) : hv fl p 0 = sw fl 1 (p.b1 0 0) := by
  have hsb := swn E 1 1 (by norm_num) (by norm_num) (E.hp.b1 0 0) (51 / 10000) (by norm_num)
  have hfix := flsw01 E 1 (Or.inr rfl) (E.hp.b1 0 0)
  have hpos : 0 ≤ sw fl 1 (p.b1 0 0) := by
    obtain ⟨h1, h2⟩ := abs_le.mp hsb
    linarith
  unfold hv
  rw [mul_zero, E.hr.zero, zero_add, hfix]
  exact relu_of_nonneg hpos

theorem mm_marked (E : Env u η M fl p n) : mmf fl p 0 = sw fl 1 (p.b2 0 3) := by
  unfold mmf
  rw [mul_zero, E.hr.zero, zero_add, flsw01 E 1 (Or.inr rfl) (E.hp.b2 0 3)]

theorem mm_unm (E : Env u η M fl p n) : |mmf fl p (sw fl 1 (p.b1 0 0))| ≤ 16 / 1000 := by
  have hr := E.hr
  have hW := swn E (-1) (-1) (by norm_num) (by norm_num) (E.hp.W2 0 3 0) (51 / 10000)
    (by norm_num)
  have hsb := swn E 1 1 (by norm_num) (by norm_num) (E.hp.b1 0 0) (51 / 10000) (by norm_num)
  have hb2 := swn E 1 1 (by norm_num) (by norm_num) (E.hp.b2 0 3) (51 / 10000) (by norm_num)
  obtain ⟨hw1, hw2⟩ := abs_le.mp hW
  obtain ⟨hs1, hs2⟩ := abs_le.mp hsb
  obtain ⟨hc1, hc2⟩ := abs_le.mp hb2
  have hs0 : 0 ≤ sw fl 1 (p.b1 0 0) := by linarith
  have hP1 : -10103 / 10000 ≤ sw fl (-1) (p.W2 0 3 0) * sw fl 1 (p.b1 0 0) := by
    have := mul_le_mul_of_nonneg_right
      (show -10051 / 10000 ≤ sw fl (-1) (p.W2 0 3 0) by linarith) hs0
    linarith
  have hP2 : sw fl (-1) (p.W2 0 3 0) * sw fl 1 (p.b1 0 0) ≤ -9898 / 10000 := by
    have := mul_le_mul_of_nonneg_right
      (show sw fl (-1) (p.W2 0 3 0) ≤ -9949 / 10000 by linarith) hs0
    linarith
  have hPa : |sw fl (-1) (p.W2 0 3 0) * sw fl 1 (p.b1 0 0)| ≤ 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hf := fl_small E hPa (by norm_num)
  obtain ⟨hf1, hf2⟩ := abs_le.mp hf
  have hXa : |fl (sw fl (-1) (p.W2 0 3 0) * sw fl 1 (p.b1 0 0)) + sw fl 1 (p.b2 0 3)| ≤ 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hg := fl_small E hXa (by norm_num)
  obtain ⟨hg1, hg2⟩ := abs_le.mp hg
  unfold mmf
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem blk0_state (E : Env u η M fl p n) (x : ℕ → Vec) (j : ℕ) (m a c pj pn : ℝ)
    (hx : x j = [m, a, c, 0, 0, 0, 1, pj, pn])
    (hmk : |m - 1| ≤ 51 / 10000 ∨ m = 0)
    (hm : fl m = m) (ha : fl a = a) (hc : fl c = c) (hpj : fl pj = pj) (hpn : fl pn = pn) :
    sblock blk0 fl ex p 0 n x j = [m, a, c, mmf fl p (hv fl p m), 0, 0, 1, pj, pn] := by
  have hr := E.hr
  have hM1 := E.hM1
  have hm2 : |m| ≤ 2 := by
    rcases hmk with h | h
    · obtain ⟨h1, h2⟩ := abs_le.mp h
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [h]; norm_num
  have hhv : |hv fl p m| ≤ 2 := by
    rcases hmk with h | h
    · rw [hv_marked E h]; norm_num
    · have hsb := swn E 1 1 (by norm_num) (by norm_num) (E.hp.b1 0 0) (51 / 10000)
        (by norm_num)
      obtain ⟨h1, h2⟩ := abs_le.mp hsb
      rw [h, hv_unm E]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hs4 := swle E (-4) (-4) (by norm_num) (by norm_num) (E.hp.W1 0 0 0)
  have hs1 := swle E (-1) (-1) (by norm_num) (by norm_num) (E.hp.W2 0 3 0)
  have hb2 := swle E 1 1 (by norm_num) (by norm_num) (E.hp.b2 0 3)
  have hY : fl (fl (sw fl (-4) (p.W1 0 0 0) * m)) = fl (sw fl (-4) (p.W1 0 0 0) * m) := by
    apply hr.idem
    have := absmul_le hs4 hm2 (by norm_num)
    linarith
  have hP : |sw fl (-1) (p.W2 0 3 0) * hv fl p m| ≤ 10 := by
    have := absmul_le hs1 hhv (by norm_num)
    linarith
  have hI3 : fl (fl (sw fl (-1) (p.W2 0 3 0) * hv fl p m))
      = fl (sw fl (-1) (p.W2 0 3 0) * hv fl p m) := hr.idem _ (by linarith)
  have hmm : fl (mmf fl p (hv fl p m)) = mmf fl p (hv fl p m) := by
    unfold mmf
    apply hr.idem
    have h1 := fl_small E hP (by norm_num)
    obtain ⟨h2, h2'⟩ := abs_le.mp h1
    obtain ⟨h3, h3'⟩ := abs_le.mp hP
    obtain ⟨h4, h4'⟩ := abs_le.mp hb2
    rw [abs_le]
    constructor <;> linarith
  have hh : sblock blk0 fl ex p 0 n x j
      = radd fl (x j) (raffine fl blk0.W2 blk0.b2
          ((raffine fl blk0.W1 blk0.b1 (x j) (p.W1 0) (p.b1 0) 0).map relu)
          (p.W2 0) (p.b2 0) 0) := rfl
  have e1 : (raffine fl blk0.W1 blk0.b1 [m, a, c, 0, 0, 0, 1, pj, pn] (p.W1 0) (p.b1 0) 0).map relu
      = [hv fl p m] := by
    simp [blk0, raffine, rdot, sw_zero hr, hr.zero, hY, hv]
  have e2 : raffine fl blk0.W2 blk0.b2 [hv fl p m] (p.W2 0) (p.b2 0) 0
      = [0, 0, 0, mmf fl p (hv fl p m), 0, 0, 0, 0, 0] := by
    simp [blk0, raffine, rdot, sw_zero hr, hr.zero, hI3, z1, mmf]
  rw [hh, hx, e1, e2]
  simp [radd, hr.zero, hr.one, hm, ha, hc, hpj, hpn, hmm]

theorem x1_eq (w : List ℕ) (E : Env u η M fl p (w.length + 1)) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ)
    (hj : j ≤ w.length + 1) :
    sblock blk0 fl ex p 0 (w.length + 1) (net.init fl p w) j
      = [eM fl p w j, eA fl p w j, eC fl p w j, mmf fl p (hv fl p (eM fl p w j)), 0, 0, 1,
         fl (j : ℝ), fl ((w.length + 1 : ℕ) : ℝ)] := by
  apply blk0_state E
  · rw [init_eq E.hr p w hw j]
    simp [pos]
  · rcases sw01 E (mq (tokAt w j)) (mq_01 _) (E.hp.E (tokAt w j) 0) with h | h
    · right; exact h.2
    · left; exact h.2
  · exact flsw01 E _ (mq_01 _) (E.hp.E (tokAt w j) 0)
  · exact flsw01 E _ (aq_01 _) (E.hp.E (tokAt w j) 1)
  · exact flsw01 E _ (cq_01 _) (E.hp.E (tokAt w j) 2)
  · exact fl_pos_fix E hj
  · exact fl_pos_fix E le_rfl

theorem mmv_marked (E : Env u η M fl p n) {m : ℝ} (hm : |m - 1| ≤ 51 / 10000) :
    mmf fl p (hv fl p m) = sw fl 1 (p.b2 0 3) := by
  rw [hv_marked E hm]; exact mm_marked E

theorem mmv_unm (E : Env u η M fl p n) :
    mmf fl p (hv fl p 0) = mmf fl p (sw fl 1 (p.b1 0 0)) := by
  rw [hv_unm E]


theorem rdot_zero_row {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) :
    ∀ (w : List ℚ), (∀ a ∈ w, a = 0) → ∀ (v : List ℝ) (d : ℕ → ℝ) (j : ℕ),
      rdot fl w v d j 0 = 0 := by
  intro w
  induction w with
  | nil => intro _ v d j; cases v <;> simp [rdot]
  | cons a t ih =>
    intro h v d j
    have ha : a = 0 := h a (by simp)
    subst ha
    cases v with
    | nil => simp [rdot]
    | cons x v' =>
      have := ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) v' d (j + 1)
      simpa [rdot, sw_zero hr, hr.zero] using this

theorem score_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (q0 q1 q2 q3 qj qn k0 k1 k2 k3 kj kn : ℝ)
    (hI1 : fl (fl (sw fl (-20) (dA 6 7) * kj)) = fl (sw fl (-20) (dA 6 7) * kj))
    (hI2 : fl (fl (sw fl 60 (dA 8 3) * k3)) = fl (sw fl 60 (dA 8 3) * k3)) :
    hdA.score fl dA [q0, q1, q2, q3, 0, 0, 1, qj, qn] [k0, k1, k2, k3, 0, 0, 1, kj, kn]
      = fl (fl (sw fl (-20) (dA 6 7) * kj) + fl (qn * fl (sw fl 60 (dA 8 3) * k3))) := by
  simp [Head.score, hdA, z9, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.one, hI1, hI2]

theorem val_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ)
    (k0 k1 k2 k3 k4 k5 k6 k7 k8 : ℝ)
    (hI : fl (fl (sw fl 1 (dV 1) * k1)) = fl (sw fl 1 (dV 1) * k1)) :
    rdot fl [0, 1, 0, 0, 0, 0, 0, 0, 0] [k0, k1, k2, k3, k4, k5, k6, k7, k8] dV 0 0
      = fl (sw fl 1 (dV 1) * k1) := by
  simp [rdot, sw_zero hr, hr.zero, hI]

theorem attn_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (dA dV : ℕ → ℕ → ℝ) (n : ℕ)
    (x : ℕ → Vec) (i : ℕ) :
    sattn hdA fl ex dA dV n x i
      = [0, 0, 0, 0, savg fl ex (cand Mask.causal n i) (hscore hdA fl dA x i)
            (fun j => rdot fl [0, 1, 0, 0, 0, 0, 0, 0, 0] (x j) (dV 4) 0 0), 0, 0, 0, 0] := by
  have hV : hdA.V = [z9, z9, z9, z9, [0, 1, 0, 0, 0, 0, 0, 0, 0], z9, z9, z9, z9] := rfl
  have hm : hdA.mask = Mask.causal := rfl
  have hz : ∀ d : ℕ → ℝ, savg fl ex (cand Mask.causal n i) (hscore hdA fl dA x i)
        (fun j => rdot fl z9 (x j) d 0 0) = 0 := by
    intro d
    apply soft_zeros hr
    intro k _
    exact rdot_zero_row hr z9 (by simp [z9]) _ d 0
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz]

theorem sc_pre (E : Env u η M fl p n) {Sw : ℝ} (hS1 : Sw ≤ -19899 / 1000)
    (hS2 : -20101 / 1000 ≤ Sw) {m : ℕ} (hm : m ≤ n) :
    |Sw * fl (m : ℝ)| ≤ 21 * (n : ℝ) := by
  have hr := E.hr
  have hnR := E.hnR
  have hSabs : |Sw| ≤ 20101 / 1000 := abs_le.mpr ⟨by linarith, by linarith⟩
  have h1 := hr.pos_le E.hu0 E.hη (k := m) (n := n) hm E.hun E.hnM
  have h2 : |fl (m : ℝ)| ≤ n + 1 / 100 := by rw [abs_of_nonneg h1.1]; exact h1.2
  have h3 := absmul_le hSabs h2 (by norm_num)
  linarith

theorem sc_same (E : Env u η M fl p n) {Sw Z : ℝ} (hS1 : Sw ≤ -19899 / 1000)
    (hS2 : -20101 / 1000 ≤ Sw) (hZ : |Z| ≤ 62 * (n : ℝ)) {j k : ℕ} (hjk : j < k)
    (hkn : k ≤ n) :
    fl (fl (Sw * fl (k : ℝ)) + Z) ≤ fl (fl (Sw * fl (j : ℝ)) + Z) - 16 * ((k : ℝ) - j) := by
  have hr := E.hr
  have hnR := E.hnR
  have hnM := E.hnM
  have hj := hr.pos_near E.hu0 E.hη (k := j) (n := n) (by omega) E.hun hnM
  have hk := hr.pos_near E.hu0 E.hη (k := k) (n := n) hkn E.hun hnM
  have hpg := hr.pos_gap E.hu0 E.hη (le_of_lt hjk) hkn E.hun hnM
  have hjR : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
  have hXj := sc_pre E hS1 hS2 (m := j) (by omega)
  have hXk := sc_pre E hS1 hS2 (m := k) hkn
  have eXj := abs_le.mp (fl_e E (x := Sw * fl (j : ℝ)) (by linarith))
  have eXk := abs_le.mp (fl_e E (x := Sw * fl (k : ℝ)) (by linarith))
  have hAj : |fl (Sw * fl (j : ℝ))| ≤ 22 * (n : ℝ) := by
    obtain ⟨a1, a2⟩ := abs_le.mp hXj
    exact abs_le.mpr ⟨by linarith [eXj.1], by linarith [eXj.2]⟩
  have hAk : |fl (Sw * fl (k : ℝ))| ≤ 22 * (n : ℝ) := by
    obtain ⟨a1, a2⟩ := abs_le.mp hXk
    exact abs_le.mpr ⟨by linarith [eXk.1], by linarith [eXk.2]⟩
  have hSj : |fl (Sw * fl (j : ℝ)) + Z| ≤ 100 * (n : ℝ) := by
    have := abs_add_le (fl (Sw * fl (j : ℝ))) Z
    linarith
  have hSk : |fl (Sw * fl (k : ℝ)) + Z| ≤ 100 * (n : ℝ) := by
    have := abs_add_le (fl (Sw * fl (k : ℝ))) Z
    linarith
  have esj := abs_le.mp (fl_e E hSj)
  have esk := abs_le.mp (fl_e E hSk)
  have hD : 0 ≤ fl (k : ℝ) - fl (j : ℝ) := by linarith
  have hprod := mul_le_mul_of_nonneg_right (show (19899 / 1000 : ℝ) ≤ -Sw by linarith) hD
  have hSd : Sw * fl (j : ℝ) - Sw * fl (k : ℝ) = (-Sw) * (fl (k : ℝ) - fl (j : ℝ)) := by ring
  linarith [esj.1, esj.2, esk.1, esk.2, eXj.1, eXj.2, eXk.1, eXk.2]

theorem sc_diff (E : Env u η M fl p n) {Sw Zj Zk : ℝ} (hS1 : Sw ≤ -19899 / 1000)
    (hS2 : -20101 / 1000 ≤ Sw) (hZj : |Zj| ≤ 62 * (n : ℝ)) (hZk : |Zk| ≤ 62 * (n : ℝ))
    (hdiff : Zk + 55 * (n : ℝ) ≤ Zj) {j k : ℕ} (hjn : j ≤ n) (hkn : k ≤ n) :
    fl (fl (Sw * fl (k : ℝ)) + Zk) ≤ fl (fl (Sw * fl (j : ℝ)) + Zj) - 16 * |(j : ℝ) - k| := by
  have hr := E.hr
  have hnR := E.hnR
  have hnM := E.hnM
  have hj := hr.pos_near E.hu0 E.hη (k := j) (n := n) hjn E.hun hnM
  have hk := hr.pos_near E.hu0 E.hη (k := k) (n := n) hkn E.hun hnM
  have hjR : (j : ℝ) ≤ n := by exact_mod_cast hjn
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hSabs : |Sw| ≤ 20101 / 1000 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hXj := sc_pre E hS1 hS2 hjn
  have hXk := sc_pre E hS1 hS2 hkn
  have eXj := abs_le.mp (fl_e E (x := Sw * fl (j : ℝ)) (by linarith))
  have eXk := abs_le.mp (fl_e E (x := Sw * fl (k : ℝ)) (by linarith))
  have hAj : |fl (Sw * fl (j : ℝ))| ≤ 22 * (n : ℝ) := by
    obtain ⟨a1, a2⟩ := abs_le.mp hXj
    exact abs_le.mpr ⟨by linarith [eXj.1], by linarith [eXj.2]⟩
  have hAk : |fl (Sw * fl (k : ℝ))| ≤ 22 * (n : ℝ) := by
    obtain ⟨a1, a2⟩ := abs_le.mp hXk
    exact abs_le.mpr ⟨by linarith [eXk.1], by linarith [eXk.2]⟩
  have hSj : |fl (Sw * fl (j : ℝ)) + Zj| ≤ 100 * (n : ℝ) := by
    have := abs_add_le (fl (Sw * fl (j : ℝ))) Zj
    linarith
  have hSk : |fl (Sw * fl (k : ℝ)) + Zk| ≤ 100 * (n : ℝ) := by
    have := abs_add_le (fl (Sw * fl (k : ℝ))) Zk
    linarith
  have esj := abs_le.mp (fl_e E hSj)
  have esk := abs_le.mp (fl_e E hSk)
  have hdd : |fl (j : ℝ) - fl (k : ℝ)| ≤ |(j : ℝ) - k| + 1 / 100 := by
    have e : fl (j : ℝ) - fl (k : ℝ) = ((j : ℝ) - k) + (fl (j : ℝ) - j) + (-(fl (k : ℝ) - k)) := by
      ring
    rw [e]
    have h1 := abs_add_three ((j : ℝ) - k) (fl (j : ℝ) - j) (-(fl (k : ℝ) - k))
    rw [abs_neg] at h1
    linarith
  have hprod := absmul_le hSabs hdd (by norm_num)
  have hSd : Sw * (fl (j : ℝ) - fl (k : ℝ)) = Sw * fl (j : ℝ) - Sw * fl (k : ℝ) := by ring
  rw [hSd] at hprod
  obtain ⟨hp1, hp2⟩ := abs_le.mp hprod
  have hdn : |(j : ℝ) - k| ≤ n := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith [esj.1, esj.2, esk.1, esk.2, eXj.1, eXj.2, eXk.1, eXk.2]

theorem Zbd (E : Env u η M fl p n) {fn Q : ℝ} (hfn : |fn - n| ≤ 1 / 200) (hQ : |Q| ≤ 62) :
    |fl (fn * fl Q) - fn * Q| ≤ 2 / 5 + (n : ℝ) / 1000 := by
  have hnR := E.hnR
  have e1 := fl_small E hQ (by norm_num)
  have hfa : |fn| ≤ n + 1 / 200 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hfn
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have e2 : |fn * fl Q - fn * Q| ≤ (n + 1 / 200) * (1 / 10 ^ 5) := by
    have : fn * fl Q - fn * Q = fn * (fl Q - Q) := by ring
    rw [this]
    exact absmul_le hfa e1 (by positivity)
  have hflQ : |fl Q| ≤ 63 := by
    obtain ⟨a1, a2⟩ := abs_le.mp e1
    obtain ⟨b1, b2⟩ := abs_le.mp hQ
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hb : |fn * fl Q| ≤ 100 * (n : ℝ) := by
    have := absmul_le hfa hflQ (by positivity)
    linarith
  have e3 := fl_e E hb
  have h4 := abs_add_le (fl (fn * fl Q) - fn * fl Q) (fn * fl Q - fn * Q)
  have h5 : fl (fn * fl Q) - fn * fl Q + (fn * fl Q - fn * Q) = fl (fn * fl Q) - fn * Q := by
    ring
  rw [h5] at h4
  linarith

theorem Zm_bd (E : Env u η M fl p n) {fn Ww mm : ℝ} (hfn : |fn - n| ≤ 1 / 200)
    (hW1 : 59698 / 1000 ≤ Ww) (hW2 : Ww ≤ 60302 / 1000) (hm1 : 9949 / 10000 ≤ mm)
    (hm2 : mm ≤ 10051 / 10000) :
    58 * (n : ℝ) ≤ fl (fn * fl (Ww * mm)) ∧ fl (fn * fl (Ww * mm)) ≤ 62 * (n : ℝ) := by
  have hnR := E.hnR
  have hm0 : 0 ≤ mm := by linarith
  have hQ1 : 59 ≤ Ww * mm := by
    have := mul_le_mul_of_nonneg_right hW1 hm0
    linarith
  have hQ2 : Ww * mm ≤ 61 := by
    have := mul_le_mul_of_nonneg_right hW2 hm0
    linarith
  have hQa : |Ww * mm| ≤ 62 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hz := abs_le.mp (Zbd E hfn hQa)
  obtain ⟨hf1, hf2⟩ := abs_le.mp hfn
  have hfn0 : 0 ≤ fn := by linarith
  have h1 := mul_le_mul_of_nonneg_left hQ1 hfn0
  have h2 := mul_le_mul_of_nonneg_left hQ2 hfn0
  constructor <;> linarith [hz.1, hz.2]

theorem Zu_bd (E : Env u η M fl p n) {fn Ww mm : ℝ} (hfn : |fn - n| ≤ 1 / 200)
    (hW1 : 59698 / 1000 ≤ Ww) (hW2 : Ww ≤ 60302 / 1000) (hm : |mm| ≤ 16 / 1000) :
    |fl (fn * fl (Ww * mm))| ≤ 2 * (n : ℝ) := by
  have hnR := E.hnR
  have hWa : |Ww| ≤ 60302 / 1000 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hQ1 : |Ww * mm| ≤ 60302 / 1000 * (16 / 1000) := absmul_le hWa hm (by norm_num)
  have hQa : |Ww * mm| ≤ 1 := by linarith
  have hQb : |Ww * mm| ≤ 62 := by linarith
  have hz := abs_le.mp (Zbd E hfn hQb)
  have hfa : |fn| ≤ n + 1 / 200 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hfn
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h1 := absmul_le hfa hQa (by positivity)
  obtain ⟨h2, h3⟩ := abs_le.mp h1
  exact abs_le.mpr ⟨by linarith [hz.1, hz.2], by linarith [hz.1, hz.2]⟩


noncomputable def hv1 (fl : ℝ → ℝ) (p : Pert) (c A : ℝ) : ℝ :=
  relu (fl (fl (fl (sw fl 1 (p.W1 1 0 2) * c) + fl (sw fl 1 (p.W1 1 0 4) * A))
    + sw fl (-1) (p.b1 1 0)))

noncomputable def mo (fl : ℝ → ℝ) (p : Pert) (h : ℝ) : ℝ :=
  fl (sw fl (-2) (p.W2 1 5 0) * h)

theorem blk1_gen {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (n : ℕ)
    (x : ℕ → Vec) (i : ℕ) (m a c mm pj pn A : ℝ)
    (hx : x i = [m, a, c, mm, 0, 0, 1, pj, pn])
    (hattn : sattn hdA fl ex (p.A 1 0) (p.V 1 0) n x i = [0, 0, 0, 0, A, 0, 0, 0, 0])
    (hm : fl m = m) (ha : fl a = a) (hc : fl c = c) (hmm : fl mm = mm) (hpj : fl pj = pj)
    (hpn : fl pn = pn) (hA : fl A = A)
    (hIc : fl (fl (sw fl 1 (p.W1 1 0 2) * c)) = fl (sw fl 1 (p.W1 1 0 2) * c))
    (hIZ : fl (fl (fl (sw fl 1 (p.W1 1 0 2) * c) + fl (sw fl 1 (p.W1 1 0 4) * A)))
        = fl (fl (sw fl 1 (p.W1 1 0 2) * c) + fl (sw fl 1 (p.W1 1 0 4) * A)))
    (hIh : fl (fl (sw fl (-2) (p.W2 1 5 0) * hv1 fl p c A))
        = fl (sw fl (-2) (p.W2 1 5 0) * hv1 fl p c A)) :
    sblock blk1 fl ex p 1 n x i = [m, a, c, mm, A, mo fl p (hv1 fl p c A), 1, pj, pn] := by
  have hmo : fl (mo fl p (hv1 fl p c A)) = mo fl p (hv1 fl p c A) := hIh
  have hh : sblock blk1 fl ex p 1 n x i
      = radd fl (radd fl (x i) (sattn hdA fl ex (p.A 1 0) (p.V 1 0) n x i))
        (raffine fl blk1.W2 blk1.b2
          ((raffine fl blk1.W1 blk1.b1
            (radd fl (x i) (sattn hdA fl ex (p.A 1 0) (p.V 1 0) n x i)) (p.W1 1) (p.b1 1) 0).map
            relu)
          (p.W2 1) (p.b2 1) 0) := rfl
  have hy : radd fl [m, a, c, mm, 0, 0, 1, pj, pn] [0, 0, 0, 0, A, 0, 0, 0, 0]
      = [m, a, c, mm, A, 0, 1, pj, pn] := by
    simp [radd, hr.zero, hr.one, hm, ha, hc, hmm, hpj, hpn, hA]
  have e1 : (raffine fl blk1.W1 blk1.b1 [m, a, c, mm, A, 0, 1, pj, pn] (p.W1 1) (p.b1 1) 0).map
      relu = [hv1 fl p c A] := by
    simp [blk1, raffine, rdot, sw_zero hr, hr.zero, hIc, hIZ, hv1]
  have e2 : raffine fl blk1.W2 blk1.b2 [hv1 fl p c A] (p.W2 1) (p.b2 1) 0
      = [0, 0, 0, 0, 0, mo fl p (hv1 fl p c A), 0, 0, 0] := by
    simp [blk1, raffine, rdot, sw_zero hr, hr.zero, hIh, z1, z9, mo]
  rw [hh, hattn, hx, hy, e1, e2]
  simp [radd, hr.zero, hr.one, hm, ha, hc, hmm, hpj, hpn, hA, hmo]

theorem read_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dW : ℕ → ℝ) (oB : ℝ)
    (m a c mm A V5 pj pn : ℝ)
    (hIc : fl (fl (sw fl 1 (dW 2) * c)) = fl (sw fl 1 (dW 2) * c))
    (hIZ : fl (fl (fl (fl (sw fl 1 (dW 2) * c) + fl (sw fl 1 (dW 4) * A))
        + fl (sw fl 1 (dW 5) * V5)))
        = fl (fl (fl (sw fl 1 (dW 2) * c) + fl (sw fl 1 (dW 4) * A))
        + fl (sw fl 1 (dW 5) * V5))) :
    fl (rdot fl [0, 0, 1, 0, 1, 1, 0, 0, 0] [m, a, c, mm, A, V5, 1, pj, pn] dW 0 0
        + sw fl 0 oB)
      = fl (fl (fl (sw fl 1 (dW 2) * c) + fl (sw fl 1 (dW 4) * A))
        + fl (sw fl 1 (dW 5) * V5)) := by
  simp [rdot, sw_zero hr, hr.zero, hIc, hIZ]


noncomputable def X1 (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) : ℕ → Vec :=
  sblock blk0 fl ex p 0 (w.length + 1) (net.init fl p w)

noncomputable def mmv (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  mmf fl p (hv fl p (eM fl p w j))

theorem X1_eq (w : List ℕ) (E : Env u η M fl p (w.length + 1)) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4)
    (j : ℕ) (hj : j ≤ w.length + 1) :
    X1 fl ex p w j
      = [eM fl p w j, eA fl p w j, eC fl p w j, mmv fl p w j, 0, 0, 1,
         fl (j : ℝ), fl ((w.length + 1 : ℕ) : ℝ)] := x1_eq w E hw j hj

theorem mmv_stat (E : Env u η M fl p n) (w : List ℕ) (j : ℕ) :
    (mq (tokAt w j) = 1 ∧ |eM fl p w j - 1| ≤ 51 / 10000 ∧ mmv fl p w j = sw fl 1 (p.b2 0 3)) ∨
    (mq (tokAt w j) = 0 ∧ eM fl p w j = 0 ∧
      mmv fl p w j = mmf fl p (sw fl 1 (p.b1 0 0))) := by
  rcases sw01 E (mq (tokAt w j)) (mq_01 _) (E.hp.E (tokAt w j) 0) with h | h
  · right
    have h0 : eM fl p w j = 0 := h.2
    refine ⟨h.1, h0, ?_⟩
    show mmf fl p (hv fl p (eM fl p w j)) = _
    rw [h0]
    exact mmv_unm E
  · left
    have h1 : |eM fl p w j - 1| ≤ 51 / 10000 := h.2
    refine ⟨h.1, h1, ?_⟩
    show mmf fl p (hv fl p (eM fl p w j)) = _
    exact mmv_marked E h1

theorem mmv_abs (E : Env u η M fl p n) (w : List ℕ) (j : ℕ) : |mmv fl p w j| ≤ 2 := by
  have hb2 := swn E 1 1 (by norm_num) (by norm_num) (E.hp.b2 0 3) (51 / 10000) (by norm_num)
  obtain ⟨h1, h2⟩ := abs_le.mp hb2
  rcases mmv_stat E w j with h | h
  · rw [h.2.2]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [h.2.2]
    have := mm_unm E
    linarith

theorem hv_le (E : Env u η M fl p n) {m : ℝ} (hmk : |m - 1| ≤ 51 / 10000 ∨ m = 0) :
    |hv fl p m| ≤ 2 := by
  rcases hmk with h | h
  · rw [hv_marked E h]; norm_num
  · have hsb := swn E 1 1 (by norm_num) (by norm_num) (E.hp.b1 0 0) (51 / 10000) (by norm_num)
    obtain ⟨h1, h2⟩ := abs_le.mp hsb
    rw [h, hv_unm E]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem mmf_fix (E : Env u η M fl p n) {h : ℝ} (hh : |h| ≤ 2) :
    fl (mmf fl p h) = mmf fl p h := by
  have hr := E.hr
  have hs1 := swle E (-1) (-1) (by norm_num) (by norm_num) (E.hp.W2 0 3 0)
  have hb2 := swle E 1 1 (by norm_num) (by norm_num) (E.hp.b2 0 3)
  have hP : |sw fl (-1) (p.W2 0 3 0) * h| ≤ 10 := by
    have := absmul_le hs1 hh (by norm_num)
    linarith
  unfold mmf
  apply hr.idem
  have h1 := fl_small E hP (by norm_num)
  obtain ⟨h2, h2'⟩ := abs_le.mp h1
  obtain ⟨h3, h3'⟩ := abs_le.mp hP
  obtain ⟨h4, h4'⟩ := abs_le.mp hb2
  have hM1 := E.hM1
  rw [abs_le]
  constructor <;> linarith

theorem mmf_idem3 (E : Env u η M fl p n) {h : ℝ} (hh : |h| ≤ 2) :
    fl (fl (sw fl (-1) (p.W2 0 3 0) * h)) = fl (sw fl (-1) (p.W2 0 3 0) * h) := by
  have hs1 := swle E (-1) (-1) (by norm_num) (by norm_num) (E.hp.W2 0 3 0)
  have := absmul_le hs1 hh (by norm_num)
  exact E.hr.idem _ (by linarith [E.hM1])

theorem mq_tok0 (w : List ℕ) : mq (tokAt w 0) = 0 := by
  rw [Lane4.Seq.tokAt_zero]; simp [mq]

theorem tok_succ (w : List ℕ) (k : ℕ) : tokAt w (k + 1) = w.getD k 0 := by
  simp [tokAt]

theorem take_getD' : ∀ (w : List ℕ) (i k : ℕ), k < i → (w.take i).getD k 0 = w.getD k 0
  | [], i, k, h => by simp
  | a :: t, 0, k, h => by omega
  | a :: t, i + 1, 0, h => by simp [List.take_succ_cons]
  | a :: t, i + 1, k + 1, h => by
    have := take_getD' t i k (by omega)
    simpa [List.take_succ_cons] using this

theorem foldl_ne (s : ℕ) (hs : s ≠ 0) (l : List ℕ) :
    l.foldl (fun s t => if s = 0 then code t else s) s = s := by
  induction l with
  | nil => rfl
  | cons a t ih => simpa [List.foldl, hs] using ih

theorem firstc_cases (l : List ℕ) :
    (firstc l = 0 ∧ ∀ k < l.length, code (l.getD k 0) = 0) ∨
    ∃ k < l.length, (∀ k' < k, code (l.getD k' 0) = 0) ∧ code (l.getD k 0) ≠ 0 ∧
      firstc l = code (l.getD k 0) := by
  induction l with
  | nil => left; exact ⟨rfl, fun k hk => by simp at hk⟩
  | cons a t ih =>
    have hf : firstc (a :: t) = t.foldl (fun s t => if s = 0 then code t else s) (code a) := by
      simp [firstc, List.foldl]
    by_cases hca : code a = 0
    · have hf2 : firstc (a :: t) = firstc t := by rw [hf, hca]; rfl
      rcases ih with ⟨h0, hall⟩ | ⟨k, hk, hb, hne, hfc⟩
      · left
        refine ⟨by rw [hf2]; exact h0, ?_⟩
        intro k hk
        cases k with
        | zero => simpa using hca
        | succ k' => simpa using hall k' (by simpa using hk)
      · right
        refine ⟨k + 1, by simpa using hk, ?_, by simpa using hne, by rw [hf2]; simpa using hfc⟩
        intro k' hk'
        cases k' with
        | zero => simpa using hca
        | succ k'' => simpa using hb k'' (by omega)
    · right
      refine ⟨0, by simp, fun k' hk' => absurd hk' (by omega), by simpa using hca, ?_⟩
      rw [hf, foldl_ne _ hca]
      simp

theorem mq_of_code {t : ℕ} (h : code t = 0) : mq t = 0 := by
  rw [mq_zero]
  intro h1
  unfold code at h
  rcases h1 with h1 | h1 <;> simp [h1] at h

theorem mq_of_code_ne {t : ℕ} (h : code t ≠ 0) : mq t = 1 := by
  by_cases h1 : t = 1 ∨ t = 4
  · exact mq_one.mpr h1
  · exfalso
    apply h
    push_neg at h1
    simp [code, h1.1, h1.2]

theorem code_eq_two {t : ℕ} : code t = 2 ↔ t = 1 := by
  unfold code
  split_ifs <;> simp_all

theorem cbit_cq (t : ℕ) : (cbit t = 1 ∧ cq t = 1) ∨ (cbit t = 0 ∧ cq t = 0) := by
  unfold cbit cq
  split_ifs <;> simp_all

theorem exist_js (w : List ℕ) (i : ℕ) (hi : i ≤ w.length) :
    ∃ js, js ≤ i ∧ (∀ k, 1 ≤ k → k < js → mq (tokAt w k) = 0) ∧
      (js = 0 → ∀ k, 1 ≤ k → k ≤ i → mq (tokAt w k) = 0) ∧
      (js ≠ 0 → mq (tokAt w js) = 1) ∧
      (if firstc (w.take i) = 2 then 1 else 0) = (if tokAt w js = 1 then 1 else 0) := by
  have hlen : (w.take i).length = i := by simp [List.length_take]; omega
  rcases firstc_cases (w.take i) with ⟨h0, hall⟩ | ⟨k, hk, hb, hne, hfc⟩
  · refine ⟨0, by omega, fun k hk1 hk2 => by omega, ?_, fun h => absurd rfl h, ?_⟩
    · intro _ k hk1 hki
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have h1 := hall k' (by omega)
      rw [take_getD' w i k' (by omega)] at h1
      rw [tok_succ]
      exact mq_of_code h1
    · rw [h0, Lane4.Seq.tokAt_zero]; simp
  · have hG : (w.take i).getD k 0 = tokAt w (k + 1) := by
      rw [take_getD' w i k (by omega), tok_succ]
    refine ⟨k + 1, by omega, ?_, fun h => absurd h (Nat.succ_ne_zero k), ?_, ?_⟩
    · intro k' hk1 hk2
      obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
      have h1 := hb k'' (by omega)
      rw [take_getD' w i k'' (by omega)] at h1
      rw [tok_succ]
      exact mq_of_code h1
    · intro _
      rw [hG] at hne
      exact mq_of_code_ne hne
    · rw [hfc, hG]
      simp [code_eq_two]


noncomputable def Zc (fl : ℝ → ℝ) (p : Pert) (n : ℕ) (mm : ℝ) : ℝ :=
  fl (fl (n : ℝ) * fl (sw fl 60 (p.A 1 0 8 3) * mm))

theorem fn_near (E : Env u η M fl p n) : |fl (n : ℝ) - n| ≤ 1 / 200 :=
  E.hr.pos_near E.hu0 E.hη le_rfl E.hun E.hnM

theorem Zc_marked (E : Env u η M fl p n) :
    58 * (n : ℝ) ≤ Zc fl p n (sw fl 1 (p.b2 0 3)) ∧
      Zc fl p n (sw fl 1 (p.b2 0 3)) ≤ 62 * (n : ℝ) := by
  have hWw := swn E 60 60 (by norm_num) (by norm_num) (E.hp.A 1 0 8 3) (302 / 1000) (by norm_num)
  have hb2 := swn E 1 1 (by norm_num) (by norm_num) (E.hp.b2 0 3) (51 / 10000) (by norm_num)
  obtain ⟨w1, w2⟩ := abs_le.mp hWw
  obtain ⟨b1, b2⟩ := abs_le.mp hb2
  unfold Zc
  exact Zm_bd E (fn_near E) (by linarith) (by linarith) (by linarith) (by linarith)

theorem Zc_unm (E : Env u η M fl p n) :
    |Zc fl p n (mmf fl p (sw fl 1 (p.b1 0 0)))| ≤ 2 * (n : ℝ) := by
  have hWw := swn E 60 60 (by norm_num) (by norm_num) (E.hp.A 1 0 8 3) (302 / 1000) (by norm_num)
  obtain ⟨w1, w2⟩ := abs_le.mp hWw
  unfold Zc
  exact Zu_bd E (fn_near E) (by linarith) (by linarith) (mm_unm E)

theorem Zc_abs (w : List ℕ) (E : Env u η M fl p (w.length + 1)) (j : ℕ) :
    |Zc fl p (w.length + 1) (mmv fl p w j)| ≤ 62 * ((w.length + 1 : ℕ) : ℝ) := by
  have hnR := E.hnR
  rcases mmv_stat E w j with h | h
  · rw [h.2.2]
    have := Zc_marked E
    exact abs_le.mpr ⟨by linarith [this.1], this.2⟩
  · rw [h.2.2]
    have := Zc_unm E
    linarith

theorem hsk_eq (w : List ℕ) (E : Env u η M fl p (w.length + 1))
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i j : ℕ) (hi : i ≤ w.length) (hj : j ≤ w.length + 1) :
    hscore hdA fl (p.A 1 0) (X1 fl ex p w) i j
      = fl (fl (sw fl (-20) (p.A 1 0 6 7) * fl (j : ℝ))
          + Zc fl p (w.length + 1) (mmv fl p w j)) := by
  have hSw := swn E (-20) (-20) (by norm_num) (by norm_num) (E.hp.A 1 0 6 7) (101 / 1000)
    (by norm_num)
  have hWw := swn E 60 60 (by norm_num) (by norm_num) (E.hp.A 1 0 8 3) (302 / 1000) (by norm_num)
  obtain ⟨s1, s2⟩ := abs_le.mp hSw
  obtain ⟨w1, w2⟩ := abs_le.mp hWw
  have hI1 : fl (fl (sw fl (-20) (p.A 1 0 6 7) * fl (j : ℝ)))
      = fl (sw fl (-20) (p.A 1 0 6 7) * fl (j : ℝ)) := by
    apply E.hr.idem
    have := sc_pre E (Sw := sw fl (-20) (p.A 1 0 6 7)) (by linarith) (by linarith) hj
    linarith [E.hM, E.hnR]
  have hI2 : fl (fl (sw fl 60 (p.A 1 0 8 3) * mmv fl p w j))
      = fl (sw fl 60 (p.A 1 0 8 3) * mmv fl p w j) := by
    apply E.hr.idem
    have hWa : |sw fl 60 (p.A 1 0 8 3)| ≤ 61 := abs_le.mpr ⟨by linarith, by linarith⟩
    have := absmul_le hWa (mmv_abs E w j) (by norm_num)
    linarith [E.hM1]
  show hdA.score fl (p.A 1 0) (X1 fl ex p w i) (X1 fl ex p w j) = _
  rw [X1_eq w E hw i (by omega), X1_eq w E hw j hj]
  exact score_eq E.hr (p.A 1 0) _ _ _ _ _ _ _ _ _ _ _ _ hI1 hI2

theorem hscore_abs (w : List ℕ) (E : Env u η M fl p (w.length + 1))
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i j : ℕ) (hi : i ≤ w.length) (hj : j ≤ w.length + 1) :
    |hscore hdA fl (p.A 1 0) (X1 fl ex p w) i j| ≤ 100 * ((w.length + 1 : ℕ) : ℝ) := by
  have hnR := E.hnR
  have hSw := swn E (-20) (-20) (by norm_num) (by norm_num) (E.hp.A 1 0 6 7) (101 / 1000)
    (by norm_num)
  obtain ⟨s1, s2⟩ := abs_le.mp hSw
  rw [hsk_eq w E hw i j hi hj]
  have hX := sc_pre E (Sw := sw fl (-20) (p.A 1 0 6 7)) (by linarith) (by linarith) hj
  have eX := abs_le.mp (fl_e E (x := sw fl (-20) (p.A 1 0 6 7) * fl (j : ℝ)) (by linarith))
  obtain ⟨x1, x2⟩ := abs_le.mp hX
  have hZ := Zc_abs w E j
  obtain ⟨z1, z2⟩ := abs_le.mp hZ
  have hS : |fl (sw fl (-20) (p.A 1 0 6 7) * fl (j : ℝ))
      + Zc fl p (w.length + 1) (mmv fl p w j)| ≤ 84 * ((w.length + 1 : ℕ) : ℝ) :=
    abs_le.mpr ⟨by linarith [eX.1], by linarith [eX.2]⟩
  have e2 := abs_le.mp (fl_e E (le_trans hS (by linarith)))
  obtain ⟨y1, y2⟩ := abs_le.mp hS
  exact abs_le.mpr ⟨by linarith [e2.1], by linarith [e2.2]⟩

theorem gap_all (w : List ℕ) (E : Env u η M fl p (w.length + 1))
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) (hi : i ≤ w.length) (js : ℕ) (hjs : js ≤ i)
    (h1 : ∀ k, 1 ≤ k → k < js → mq (tokAt w k) = 0)
    (h2 : js = 0 → ∀ k, 1 ≤ k → k ≤ i → mq (tokAt w k) = 0)
    (h3 : js ≠ 0 → mq (tokAt w js) = 1) :
    ∀ k ∈ cand Mask.causal (w.length + 1) i, k ≠ js →
      hscore hdA fl (p.A 1 0) (X1 fl ex p w) i k
        ≤ hscore hdA fl (p.A 1 0) (X1 fl ex p w) i js - 16 * (ndist js k : ℝ) := by
  intro k hk hne
  rw [Lane4.Seq.mem_cand_causal] at hk
  have hnR := E.hnR
  have hSw := swn E (-20) (-20) (by norm_num) (by norm_num) (E.hp.A 1 0 6 7) (101 / 1000)
    (by norm_num)
  obtain ⟨s1, s2⟩ := abs_le.mp hSw
  have hS1 : sw fl (-20) (p.A 1 0 6 7) ≤ -19899 / 1000 := by linarith
  have hS2 : -20101 / 1000 ≤ sw fl (-20) (p.A 1 0 6 7) := by linarith
  rw [hsk_eq w E hw i k hi (by omega), hsk_eq w E hw i js hi (by omega), ndist_cast]
  have hZM := Zc_marked E
  have hZU := Zc_unm E
  have hZUa := abs_le.mp hZU
  have hstat : ∀ j, (mq (tokAt w j) = 1 → mmv fl p w j = sw fl 1 (p.b2 0 3)) ∧
      (mq (tokAt w j) = 0 → mmv fl p w j = mmf fl p (sw fl 1 (p.b1 0 0))) := by
    intro j
    rcases mmv_stat E w j with h | h
    · exact ⟨fun _ => h.2.2, fun h0 => by rw [h.1] at h0; exact absurd h0 (by norm_num)⟩
    · exact ⟨fun h0 => by rw [h.1] at h0; exact absurd h0 (by norm_num), fun _ => h.2.2⟩
  have sK : ∀ k', k' ≤ i → k' < js → mq (tokAt w k') = 0 := by
    intro k' hk' hlt
    rcases Nat.eq_zero_or_pos k' with h0 | h0
    · rw [h0]; exact mq_tok0 w
    · exact h1 k' h0 hlt
  have sK2 : js = 0 → ∀ k', k' ≤ i → mq (tokAt w k') = 0 := by
    intro hj0 k' hk'
    rcases Nat.eq_zero_or_pos k' with h0 | h0
    · rw [h0]; exact mq_tok0 w
    · exact h2 hj0 k' h0 hk'
  have hjn : js ≤ w.length + 1 := by omega
  have hkn : k ≤ w.length + 1 := by omega
  have diff_case : mq (tokAt w js) = 1 → mq (tokAt w k) = 0 →
      fl (fl (sw fl (-20) (p.A 1 0 6 7) * fl (k : ℝ))
          + Zc fl p (w.length + 1) (mmv fl p w k))
        ≤ fl (fl (sw fl (-20) (p.A 1 0 6 7) * fl (js : ℝ))
          + Zc fl p (w.length + 1) (mmv fl p w js)) - 16 * |(js : ℝ) - k| := by
    intro sj sk
    rw [(hstat js).1 sj, (hstat k).2 sk]
    exact sc_diff E hS1 hS2 (abs_le.mpr ⟨by linarith [hZM.1], hZM.2⟩)
      (abs_le.mpr ⟨by linarith [hZUa.1], by linarith [hZUa.2]⟩)
      (by linarith [hZM.1, hZUa.2]) hjn hkn
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hjs0 : js ≠ 0 := by omega
    exact diff_case (h3 hjs0) (sK k hk hlt)
  · have hgtR : (js : ℝ) < k := by exact_mod_cast hgt
    have habs : |(js : ℝ) - k| = (k : ℝ) - js := by
      rw [abs_of_nonpos (by linarith)]; ring
    by_cases hj0 : js = 0
    · have sk := sK2 hj0 k hk
      have sj : mq (tokAt w js) = 0 := by rw [hj0]; exact mq_tok0 w
      rw [(hstat js).2 sj, (hstat k).2 sk, habs]
      exact sc_same E hS1 hS2 (abs_le.mpr ⟨by linarith [hZUa.1], by linarith [hZUa.2]⟩) hgt hkn
    · have sj := h3 hj0
      rcases mq_01 (tokAt w k) with sk | sk
      · exact diff_case sj sk
      · rw [(hstat js).1 sj, (hstat k).1 sk, habs]
        exact sc_same E hS1 hS2 (abs_le.mpr ⟨by linarith [hZM.1], hZM.2⟩) hgt hkn


theorem eA_cases (E : Env u η M fl p n) (w : List ℕ) (j : ℕ) :
    (aq (tokAt w j) = 0 ∧ eA fl p w j = 0) ∨
    (aq (tokAt w j) = 1 ∧ |eA fl p w j - 1| ≤ 51 / 10000) :=
  sw01 E (aq (tokAt w j)) (aq_01 _) (E.hp.E (tokAt w j) 1)

theorem eC_cases (E : Env u η M fl p n) (w : List ℕ) (j : ℕ) :
    (cq (tokAt w j) = 0 ∧ eC fl p w j = 0) ∨
    (cq (tokAt w j) = 1 ∧ |eC fl p w j - 1| ≤ 51 / 10000) :=
  sw01 E (cq (tokAt w j)) (cq_01 _) (E.hp.E (tokAt w j) 2)

theorem prodA {w x t b T : ℝ} (hw : |w - 1| ≤ 51 / 10000) (hx : |x - t| ≤ b) (ht : |t| ≤ T) :
    |w * x - t| ≤ 51 / 10000 * T + b + 51 / 10000 * b := by
  have h := mul_near hw hx
  rw [abs_one] at h
  have h2 : w * x - 1 * t = w * x - t := by ring
  rw [h2] at h
  have hb : 0 ≤ b := le_trans (abs_nonneg _) hx
  linarith [h, ht]

theorem blk1_idem (E : Env u η M fl p n) {c A : ℝ} (hc : |c| ≤ 2) (hA : |A| ≤ 3) :
    fl (fl (sw fl 1 (p.W1 1 0 2) * c)) = fl (sw fl 1 (p.W1 1 0 2) * c) ∧
    fl (fl (fl (sw fl 1 (p.W1 1 0 2) * c) + fl (sw fl 1 (p.W1 1 0 4) * A)))
      = fl (fl (sw fl 1 (p.W1 1 0 2) * c) + fl (sw fl 1 (p.W1 1 0 4) * A)) ∧
    fl (fl (sw fl (-2) (p.W2 1 5 0) * hv1 fl p c A))
      = fl (sw fl (-2) (p.W2 1 5 0) * hv1 fl p c A) := by
  have hM1 := E.hM1
  have s1 := swle E 1 1 (by norm_num) (by norm_num) (E.hp.W1 1 0 2)
  have s2 := swle E 1 1 (by norm_num) (by norm_num) (E.hp.W1 1 0 4)
  have sb := swle E (-1) (-1) (by norm_num) (by norm_num) (E.hp.b1 1 0)
  have so := swle E (-2) (-2) (by norm_num) (by norm_num) (E.hp.W2 1 5 0)
  have hX : |sw fl 1 (p.W1 1 0 2) * c| ≤ 10 := by
    have := absmul_le s1 hc (by norm_num)
    linarith
  have hY : |sw fl 1 (p.W1 1 0 4) * A| ≤ 15 := by
    have := absmul_le s2 hA (by norm_num)
    linarith
  have f1 := abs_le.mp (fl_small E hX (by norm_num))
  have f2 := abs_le.mp (fl_small E hY (by norm_num))
  obtain ⟨x1, x2⟩ := abs_le.mp hX
  obtain ⟨y1, y2⟩ := abs_le.mp hY
  have hS1 : |fl (sw fl 1 (p.W1 1 0 2) * c) + fl (sw fl 1 (p.W1 1 0 4) * A)| ≤ 26 :=
    abs_le.mpr ⟨by linarith [f1.1, f2.1], by linarith [f1.2, f2.2]⟩
  have f3 := abs_le.mp (fl_small E hS1 (by norm_num))
  obtain ⟨p1, p2⟩ := abs_le.mp hS1
  obtain ⟨b1, b2⟩ := abs_le.mp sb
  have hS2 : |fl (fl (sw fl 1 (p.W1 1 0 2) * c) + fl (sw fl 1 (p.W1 1 0 4) * A))
      + sw fl (-1) (p.b1 1 0)| ≤ 32 :=
    abs_le.mpr ⟨by linarith [f3.1], by linarith [f3.2]⟩
  have f4 := abs_le.mp (fl_small E hS2 (by norm_num))
  obtain ⟨q1, q2⟩ := abs_le.mp hS2
  have hh : |hv1 fl p c A| ≤ 33 := by
    unfold hv1 relu
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [f4.1, f4.2]) (by norm_num)
  have hP := absmul_le so hh (by norm_num)
  refine ⟨E.hr.idem _ (by linarith), E.hr.idem _ (by linarith), E.hr.idem _ (by linarith)⟩

theorem hv1_near (E : Env u η M fl p n) {AT cT A c ht : ℝ} (hAT : |AT| ≤ 1) (hcT : |cT| ≤ 1)
    (hht : ht = max (AT + cT - 1) 0) (hA : |A - AT| ≤ 31 / 1000) (hc : |c - cT| ≤ 51 / 10000)
    (hcb : |c| ≤ 2) (hAb : |A| ≤ 3) : |hv1 fl p c A - ht| ≤ 52 / 1000 := by
  have w1 := swn E 1 1 (by norm_num) (by norm_num) (E.hp.W1 1 0 2) (51 / 10000) (by norm_num)
  have w2 := swn E 1 1 (by norm_num) (by norm_num) (E.hp.W1 1 0 4) (51 / 10000) (by norm_num)
  have wb := swn E (-1) (-1) (by norm_num) (by norm_num) (E.hp.b1 1 0) (51 / 10000)
    (by norm_num)
  have s1 := swle E 1 1 (by norm_num) (by norm_num) (E.hp.W1 1 0 2)
  have s2 := swle E 1 1 (by norm_num) (by norm_num) (E.hp.W1 1 0 4)
  have sb := swle E (-1) (-1) (by norm_num) (by norm_num) (E.hp.b1 1 0)
  have eX := prodA (T := 1) w1 hc hcT
  have eY := prodA (T := 1) w2 hA hAT
  have hX : |sw fl 1 (p.W1 1 0 2) * c| ≤ 10 := by
    have := absmul_le s1 hcb (by norm_num)
    linarith
  have hY : |sw fl 1 (p.W1 1 0 4) * A| ≤ 15 := by
    have := absmul_le s2 hAb (by norm_num)
    linarith
  have f1 := abs_le.mp (fl_small E hX (by norm_num))
  have f2 := abs_le.mp (fl_small E hY (by norm_num))
  obtain ⟨x1, x2⟩ := abs_le.mp hX
  obtain ⟨y1, y2⟩ := abs_le.mp hY
  have hS1 : |fl (sw fl 1 (p.W1 1 0 2) * c) + fl (sw fl 1 (p.W1 1 0 4) * A)| ≤ 26 :=
    abs_le.mpr ⟨by linarith [f1.1, f2.1], by linarith [f1.2, f2.2]⟩
  have f3 := abs_le.mp (fl_small E hS1 (by norm_num))
  obtain ⟨p1, p2⟩ := abs_le.mp hS1
  obtain ⟨b1, b2⟩ := abs_le.mp sb
  have hS2 : |fl (fl (sw fl 1 (p.W1 1 0 2) * c) + fl (sw fl 1 (p.W1 1 0 4) * A))
      + sw fl (-1) (p.b1 1 0)| ≤ 32 :=
    abs_le.mpr ⟨by linarith [f3.1], by linarith [f3.2]⟩
  have f4 := abs_le.mp (fl_small E hS2 (by norm_num))
  have eX' := abs_le.mp eX
  have eY' := abs_le.mp eY
  have wb' := abs_le.mp wb
  have hV : |fl (fl (fl (sw fl 1 (p.W1 1 0 2) * c) + fl (sw fl 1 (p.W1 1 0 4) * A))
      + sw fl (-1) (p.b1 1 0)) - (AT + cT - 1)| ≤ 52 / 1000 :=
    abs_le.mpr ⟨by linarith [f1.1, f2.1, f3.1, f4.1, eX'.1, eY'.1, wb'.1],
      by linarith [f1.2, f2.2, f3.2, f4.2, eX'.2, eY'.2, wb'.2]⟩
  rw [hht]
  unfold hv1 relu
  exact le_trans (abs_max_sub_max_le_abs _ _ _) hV

theorem mo_near (E : Env u η M fl p n) {ht h : ℝ} (hht0 : 0 ≤ ht) (hht1 : ht ≤ 1)
    (hh : |h - ht| ≤ 52 / 1000) : |mo fl p h - (-2 * ht)| ≤ 115 / 1000 := by
  have wo := swn E (-2) (-2) (by norm_num) (by norm_num) (E.hp.W2 1 5 0) (101 / 10000)
    (by norm_num)
  have so := swle E (-2) (-2) (by norm_num) (by norm_num) (E.hp.W2 1 5 0)
  have em := mul_near wo hh
  have h2 : |(-2 : ℝ)| = 2 := by norm_num
  rw [h2, abs_of_nonneg hht0] at em
  have habs : |h| ≤ 2 := by
    obtain ⟨a, b⟩ := abs_le.mp hh
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hb : |sw fl (-2) (p.W2 1 5 0) * h| ≤ 100 := by
    have := absmul_le so habs (by norm_num)
    linarith
  have f := abs_le.mp (fl_small E hb (le_refl _))
  have em' := abs_le.mp em
  unfold mo
  exact abs_le.mpr ⟨by linarith [f.1, em'.1], by linarith [f.2, em'.2]⟩

theorem read_idem (E : Env u η M fl p n) {c A mo' : ℝ} (hc : |c| ≤ 2) (hA : |A| ≤ 3)
    (hm : |mo'| ≤ 3) :
    fl (fl (sw fl 1 (p.oW 2) * c)) = fl (sw fl 1 (p.oW 2) * c) ∧
    fl (fl (fl (fl (sw fl 1 (p.oW 2) * c) + fl (sw fl 1 (p.oW 4) * A))
        + fl (sw fl 1 (p.oW 5) * mo')))
      = fl (fl (fl (sw fl 1 (p.oW 2) * c) + fl (sw fl 1 (p.oW 4) * A))
        + fl (sw fl 1 (p.oW 5) * mo')) := by
  have hM1 := E.hM1
  have s1 := swle E 1 1 (by norm_num) (by norm_num) (E.hp.oW 2)
  have s2 := swle E 1 1 (by norm_num) (by norm_num) (E.hp.oW 4)
  have s3 := swle E 1 1 (by norm_num) (by norm_num) (E.hp.oW 5)
  have hX : |sw fl 1 (p.oW 2) * c| ≤ 10 := by
    have := absmul_le s1 hc (by norm_num)
    linarith
  have hY : |sw fl 1 (p.oW 4) * A| ≤ 15 := by
    have := absmul_le s2 hA (by norm_num)
    linarith
  have hZ : |sw fl 1 (p.oW 5) * mo'| ≤ 15 := by
    have := absmul_le s3 hm (by norm_num)
    linarith
  have f1 := abs_le.mp (fl_small E hX (by norm_num))
  have f2 := abs_le.mp (fl_small E hY (by norm_num))
  have f3 := abs_le.mp (fl_small E hZ (by norm_num))
  obtain ⟨x1, x2⟩ := abs_le.mp hX
  obtain ⟨y1, y2⟩ := abs_le.mp hY
  obtain ⟨z1, z2⟩ := abs_le.mp hZ
  have hS1 : |fl (sw fl 1 (p.oW 2) * c) + fl (sw fl 1 (p.oW 4) * A)| ≤ 26 :=
    abs_le.mpr ⟨by linarith [f1.1, f2.1], by linarith [f1.2, f2.2]⟩
  have f4 := abs_le.mp (fl_small E hS1 (by norm_num))
  obtain ⟨p1, p2⟩ := abs_le.mp hS1
  have hS2 : |fl (fl (sw fl 1 (p.oW 2) * c) + fl (sw fl 1 (p.oW 4) * A))
      + fl (sw fl 1 (p.oW 5) * mo')| ≤ 50 :=
    abs_le.mpr ⟨by linarith [f4.1, f3.1], by linarith [f4.2, f3.2]⟩
  obtain ⟨q1, q2⟩ := abs_le.mp hS2
  exact ⟨E.hr.idem _ (by linarith), E.hr.idem _ (by linarith)⟩

theorem out_near (E : Env u η M fl p n) {AT cT A c ht mo' : ℝ} (hAT : |AT| ≤ 1) (hcT : |cT| ≤ 1)
    (hA : |A - AT| ≤ 31 / 1000) (hc : |c - cT| ≤ 51 / 10000) (hcb : |c| ≤ 2) (hAb : |A| ≤ 3)
    (hht0 : 0 ≤ ht) (hht1 : ht ≤ 1) (hmo : |mo' - (-2 * ht)| ≤ 115 / 1000) :
    |fl (fl (fl (sw fl 1 (p.oW 2) * c) + fl (sw fl 1 (p.oW 4) * A))
        + fl (sw fl 1 (p.oW 5) * mo')) - (AT + cT - 2 * ht)| ≤ 1 / 5 := by
  have r1 := swn E 1 1 (by norm_num) (by norm_num) (E.hp.oW 2) (51 / 10000) (by norm_num)
  have r2 := swn E 1 1 (by norm_num) (by norm_num) (E.hp.oW 4) (51 / 10000) (by norm_num)
  have r3 := swn E 1 1 (by norm_num) (by norm_num) (E.hp.oW 5) (51 / 10000) (by norm_num)
  have s1 := swle E 1 1 (by norm_num) (by norm_num) (E.hp.oW 2)
  have s2 := swle E 1 1 (by norm_num) (by norm_num) (E.hp.oW 4)
  have s3 := swle E 1 1 (by norm_num) (by norm_num) (E.hp.oW 5)
  have ht2 : |-2 * ht| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith
  have hm3 : |mo'| ≤ 3 := by
    obtain ⟨a, b⟩ := abs_le.mp hmo
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have eX := abs_le.mp (prodA (T := 1) r1 hc hcT)
  have eY := abs_le.mp (prodA (T := 1) r2 hA hAT)
  have eZ := abs_le.mp (prodA (T := 2) r3 hmo ht2)
  have hX : |sw fl 1 (p.oW 2) * c| ≤ 10 := by
    have := absmul_le s1 hcb (by norm_num)
    linarith
  have hY : |sw fl 1 (p.oW 4) * A| ≤ 15 := by
    have := absmul_le s2 hAb (by norm_num)
    linarith
  have hZ : |sw fl 1 (p.oW 5) * mo'| ≤ 15 := by
    have := absmul_le s3 hm3 (by norm_num)
    linarith
  have f1 := abs_le.mp (fl_small E hX (by norm_num))
  have f2 := abs_le.mp (fl_small E hY (by norm_num))
  have f3 := abs_le.mp (fl_small E hZ (by norm_num))
  obtain ⟨x1, x2⟩ := abs_le.mp hX
  obtain ⟨y1, y2⟩ := abs_le.mp hY
  obtain ⟨z1, z2⟩ := abs_le.mp hZ
  have hS1 : |fl (sw fl 1 (p.oW 2) * c) + fl (sw fl 1 (p.oW 4) * A)| ≤ 26 :=
    abs_le.mpr ⟨by linarith [f1.1, f2.1], by linarith [f1.2, f2.2]⟩
  have f4 := abs_le.mp (fl_small E hS1 (by norm_num))
  obtain ⟨p1, p2⟩ := abs_le.mp hS1
  have hS2 : |fl (fl (sw fl 1 (p.oW 2) * c) + fl (sw fl 1 (p.oW 4) * A))
      + fl (sw fl 1 (p.oW 5) * mo')| ≤ 50 :=
    abs_le.mpr ⟨by linarith [f4.1, f3.1], by linarith [f4.2, f3.2]⟩
  have f5 := abs_le.mp (fl_small E hS2 (by norm_num))
  exact abs_le.mpr ⟨by linarith [f1.1, f2.1, f3.1, f4.1, f5.1, eX.1, eY.1, eZ.1],
    by linarith [f1.2, f2.2, f3.2, f4.2, f5.2, eX.2, eY.2, eZ.2]⟩

theorem tgt_eq (a c : ℕ) (ha : a = 0 ∨ a = 1) (hc : c = 0 ∨ c = 1) :
    (((a + c) % 2 : ℕ) : ℝ) = (a : ℝ) + c - 2 * max ((a : ℝ) + c - 1) 0 := by
  rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num [max_def]


end kit

set_option maxHeartbeats 4000000 in
theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη p hp w hw hn hnη hM i hi1 hi
  have hn1 : 1 ≤ w.length + 1 := by omega
  have hM1000 : 1000 * ((w.length + 1 : ℕ) : ℝ) ≤ M :=
    range_lin hM hn1 (by norm_num) (by norm_num)
  have E : Env u η M fl p (w.length + 1) := ⟨hr, hu0, hu1, hη, hp, hn1, hn, hM1000⟩
  have hnR := E.hnR
  have hM1 := E.hM1
  obtain ⟨js, hjs, h1, h2, h3, hAT⟩ := exist_js w i hi
  have hgap := gap_all (ex := ex) w E hw i hi js hjs h1 h2 h3
  have hjc : js ∈ cand Mask.causal (w.length + 1) i := by
    rw [Lane4.Seq.mem_cand_causal]; exact hjs
  have hlen : (cand Mask.causal (w.length + 1) i).length ≤ w.length + 1 := by
    simp [cand]; omega
  -- values
  have hTT := swn E 1 1 (by norm_num) (by norm_num) (hp.V 1 0 4 1) (51 / 10000) (by norm_num)
  have hTs := swle E 1 1 (by norm_num) (by norm_num) (hp.V 1 0 4 1)
  obtain ⟨t1, t2⟩ := abs_le.mp hTT
  have hfk : ∀ j, j ≤ w.length + 1 →
      rdot fl [0, 1, 0, 0, 0, 0, 0, 0, 0] (X1 fl ex p w j) (p.V 1 0 4) 0 0
        = fl (sw fl 1 (p.V 1 0 4 1) * eA fl p w j) := by
    intro j hj
    have hAb : |eA fl p w j| ≤ 2 := by
      rcases eA_cases E w j with h | h
      · rw [h.2]; norm_num
      · obtain ⟨a1, a2⟩ := abs_le.mp h.2
        exact abs_le.mpr ⟨by linarith, by linarith⟩
    have := absmul_le hTs hAb (by norm_num)
    rw [X1_eq w E hw j hj]
    exact val_eq hr (p.V 1 0 4) _ _ _ _ _ _ _ _ _ (hr.idem _ (by linarith))
  have hfval : ∀ j, j ≤ w.length + 1 → |fl (sw fl 1 (p.V 1 0 4 1) * eA fl p w j)| ≤ 2 := by
    intro j hj
    rcases eA_cases E w j with h | h
    · rw [h.2, mul_zero, hr.zero]; norm_num
    · obtain ⟨a1, a2⟩ := abs_le.mp h.2
      have hTa : |sw fl 1 (p.V 1 0 4 1)| ≤ 10051 / 10000 :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      have hEa : |eA fl p w j| ≤ 10051 / 10000 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hP := absmul_le hTa hEa (by norm_num)
      have hf := fl_small E (le_trans hP (by norm_num : (10051 / 10000 : ℝ) * (10051 / 10000) ≤ 2))
        (by norm_num)
      obtain ⟨p1, p2⟩ := abs_le.mp hP
      obtain ⟨f1, f2⟩ := abs_le.mp hf
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hSb : ∀ k ∈ cand Mask.causal (w.length + 1) i,
      |hscore hdA fl (p.A 1 0) (X1 fl ex p w) i k| ≤ 100 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    rw [Lane4.Seq.mem_cand_causal] at hk
    exact hscore_abs w E hw i k hi (by omega)
  have hfB : ∀ k ∈ cand Mask.causal (w.length + 1) i,
      |(fun j => rdot fl [0, 1, 0, 0, 0, 0, 0, 0, 0] (X1 fl ex p w j) (p.V 1 0 4) 0 0) k| ≤ 2 := by
    intro k hk
    rw [Lane4.Seq.mem_cand_causal] at hk
    show |rdot fl [0, 1, 0, 0, 0, 0, 0, 0, 0] (X1 fl ex p w k) (p.V 1 0 4) 0 0| ≤ 2
    rw [hfk k (by omega)]
    exact hfval k (by omega)
  obtain ⟨hA1, hA2⟩ := soft_near hr he hu0 hu1 hη0 hη (Lane4.Seq.cand_nodup _ _ _) hlen hn hnη
    (s := hscore hdA fl (p.A 1 0) (X1 fl ex p w) i)
    (f := fun j => rdot fl [0, 1, 0, 0, 0, 0, 0, 0, 0] (X1 fl ex p w j) (p.V 1 0 4) 0 0)
    (j := js) hjc hgap (Sb := 100 * ((w.length + 1 : ℕ) : ℝ)) hSb (by linarith [E.hM])
    (B := 2) hfB (by linarith)
  have hat := attn_eq (ex := ex) hr (p.A 1 0) (p.V 1 0) (w.length + 1) (X1 fl ex p w) i
  generalize hAdef : savg fl ex (cand Mask.causal (w.length + 1) i)
    (hscore hdA fl (p.A 1 0) (X1 fl ex p w) i)
    (fun j => rdot fl [0, 1, 0, 0, 0, 0, 0, 0, 0] (X1 fl ex p w j) (p.V 1 0 4) 0 0) = A at hA1 hA2 hat
  have hA1' : |A - fl (sw fl 1 (p.V 1 0 4 1) * eA fl p w js)| ≤ 2 / 100 + 1 / 2 ^ 90 := by
    simpa [hfk js (by omega)] using hA1
  have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 10 ^ 5 := by norm_num
  -- the first-marked value
  obtain ⟨aN, haNdef⟩ : ∃ aN : ℕ, aN = (if firstc (w.take i) = 2 then 1 else 0) := ⟨_, rfl⟩
  rw [← haNdef] at hAT
  have haN : aN = 0 ∨ aN = 1 := by rw [haNdef]; split_ifs <;> simp
  have hAfin : |A - (aN : ℝ)| ≤ 31 / 1000 := by
    by_cases ht1 : tokAt w js = 1
    · have hN : aN = 1 := by rw [hAT]; simp [ht1]
      rcases eA_cases E w js with h | h
      · rw [ht1] at h; simp [aq] at h
      · have hP := prodA (T := 1) (w := sw fl 1 (p.V 1 0 4 1)) (x := eA fl p w js) (t := 1)
          (b := 51 / 10000) hTT h.2 (by norm_num)
        have hP' : |sw fl 1 (p.V 1 0 4 1) * eA fl p w js| ≤ 2 := by
          obtain ⟨a1, a2⟩ := abs_le.mp hP
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        have hf := abs_le.mp (fl_small E hP' (by norm_num))
        have hP2 := abs_le.mp hP
        rw [hN]
        obtain ⟨a1, a2⟩ := abs_le.mp hA1'
        push_cast
        exact abs_le.mpr ⟨by linarith [hf.1, hf.2, hP2.1, hP2.2], by linarith [hf.1, hf.2, hP2.1, hP2.2]⟩
    · have hN : aN = 0 := by rw [hAT]; simp [ht1]
      rcases eA_cases E w js with h | h
      · have : fl (sw fl 1 (p.V 1 0 4 1) * eA fl p w js) = 0 := by
          rw [h.2, mul_zero, hr.zero]
        rw [this] at hA1'
        rw [hN]
        obtain ⟨a1, a2⟩ := abs_le.mp hA1'
        push_cast
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · exfalso
        have : tokAt w js = 1 := aq_one.mp h.1
        exact ht1 this
  have hAb : |A| ≤ 3 := by
    have hfv := hfval js (by omega)
    obtain ⟨a1, a2⟩ := abs_le.mp hA1'
    obtain ⟨b1, b2⟩ := abs_le.mp hfv
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- the token bit
  have hti : w.getD (i - 1) 0 = tokAt w i := by
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    simp [tok_succ]
  obtain ⟨cN, hcNdef⟩ : ∃ cN : ℕ, cN = cbit (tokAt w i) := ⟨_, rfl⟩
  have hcfin : |eC fl p w i - (cN : ℝ)| ≤ 51 / 10000 ∧ (cN = 0 ∨ cN = 1) := by
    rcases cbit_cq (tokAt w i) with ⟨hb, hq⟩ | ⟨hb, hq⟩ <;>
      rcases eC_cases E w i with ⟨hq', he'⟩ | ⟨hq', he'⟩
    · rw [hq] at hq'; exact absurd hq' (by norm_num)
    · rw [← hcNdef] at hb
      rw [hb]
      exact ⟨by simpa using he', Or.inr rfl⟩
    · rw [← hcNdef] at hb
      rw [hb]
      exact ⟨by norm_num [he'], Or.inl rfl⟩
    · rw [hq] at hq'; exact absurd hq' (by norm_num)
  obtain ⟨hcfin, hcN⟩ := hcfin
  have hcb : |eC fl p w i| ≤ 2 := by
    have hcN1 : |(cN : ℝ)| ≤ 1 := by
      rcases hcN with h | h <;> rw [h] <;> norm_num
    obtain ⟨a1, a2⟩ := abs_le.mp hcfin
    obtain ⟨b1, b2⟩ := abs_le.mp hcN1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- block 1
  have hmk : |eM fl p w i - 1| ≤ 51 / 10000 ∨ eM fl p w i = 0 := by
    rcases mmv_stat E w i with h | h
    · left; exact h.2.1
    · right; exact h.2.1
  have hmm : fl (mmv fl p w i) = mmv fl p w i :=
    mmf_fix E (h := hv fl p (eM fl p w i)) (hv_le E hmk)
  obtain ⟨hIc, hIZ, hIh⟩ := blk1_idem E hcb hAb
  have hb1 := blk1_gen hr p (w.length + 1) (X1 fl ex p w) i (eM fl p w i) (eA fl p w i)
    (eC fl p w i) (mmv fl p w i) (fl (i : ℝ)) (fl ((w.length + 1 : ℕ) : ℝ)) A
    (X1_eq w E hw i (by omega)) hat
    (flsw01 E _ (mq_01 _) (hp.E (tokAt w i) 0))
    (flsw01 E _ (aq_01 _) (hp.E (tokAt w i) 1))
    (flsw01 E _ (cq_01 _) (hp.E (tokAt w i) 2))
    hmm (fl_pos_fix E (by omega)) (fl_pos_fix E le_rfl) hA2 hIc hIZ hIh
  -- numbers
  have hAT01 : |(aN : ℝ)| ≤ 1 := by
    rcases haN with h | h <;> rw [h] <;> norm_num
  have hcT01 : |(cN : ℝ)| ≤ 1 := by
    rcases hcN with h | h <;> rw [h] <;> norm_num
  obtain ⟨ht, hht⟩ : ∃ ht : ℝ, ht = max ((aN : ℝ) + cN - 1) 0 := ⟨_, rfl⟩
  have hht01 : 0 ≤ ht ∧ ht ≤ 1 := by
    rw [hht]
    refine ⟨le_max_right _ _, max_le ?_ (by norm_num)⟩
    rcases haN with h | h <;> rcases hcN with h' | h' <;> rw [h, h'] <;> norm_num
  have hhv := hv1_near E hAT01 hcT01 hht hAfin hcfin hcb hAb
  have hmo := mo_near E hht01.1 hht01.2 hhv
  have hmo3 : |mo fl p (hv1 fl p (eC fl p w i) A)| ≤ 3 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hmo
    exact abs_le.mpr ⟨by linarith [hht01.1, hht01.2], by linarith [hht01.1, hht01.2]⟩
  obtain ⟨hIc', hIZ'⟩ := read_idem E hcb hAb hmo3
  have hs : sout net fl ex p w i
      = fl (fl (fl (sw fl 1 (p.oW 2) * eC fl p w i) + fl (sw fl 1 (p.oW 4) * A))
        + fl (sw fl 1 (p.oW 5) * mo fl p (hv1 fl p (eC fl p w i) A))) := by
    have e : sout net fl ex p w i
        = fl (rdot fl [0, 0, 1, 0, 1, 1, 0, 0, 0]
            (sblock blk1 fl ex p 1 (w.length + 1) (X1 fl ex p w) i) p.oW 0 0 + sw fl 0 p.oB) := rfl
    rw [e, hb1]
    exact read_eq hr p.oW p.oB _ _ _ _ _ _ _ _ hIc' hIZ'
  have hout := out_near E hAT01 hcT01 hAfin hcfin hcb hAb hht01.1 hht01.2 hmo
  have htg : ((target w i : ℕ) : ℝ) = (aN : ℝ) + cN - 2 * max ((aN : ℝ) + cN - 1) 0 := by
    have := tgt_eq aN cN haN hcN
    unfold target
    rw [hti, ← haNdef, ← hcNdef]
    exact this
  rw [hs, htg, ← hht]
  exact le_trans hout (by norm_num)

end Lane4.Case

