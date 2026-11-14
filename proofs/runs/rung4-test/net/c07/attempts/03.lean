set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

def z8 : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0]
def v4 : List ℚ := [0, 1, 0, 0, 0, 0, 0, 0]

def hd1 : Head :=
  { A := [[0, 0, 0, 0, 0, 0, 4, 0], z8, z8, z8, z8, [0, 0, 0, 0, 0, 0, -1, 0], z8, z8],
    V := [z8, z8, z8, [0, 0, 0, 0, 0, 0, 1, 0], z8, z8, z8, z8],
    mask := Mask.causal }

def hd2 : Head :=
  { A := [z8, z8, z8, z8, z8, [0, 0, 0, 1, 0, 0, 0, 0], z8, z8],
    V := [z8, z8, z8, z8, v4, z8, z8, z8],
    mask := Mask.strict }

def blk1 : Block :=
  { heads := [hd1], W1 := [], b1 := [], W2 := [[], [], [], [], [], [], [], []], b2 := z8 }

def blk2 : Block :=
  { heads := [hd2], W1 := [[0, 0, 1, 0, 1, 0, 0, 0]], b1 := [-2],
    W2 := [[0], [0], [0], [0], [-3], [0], [0], [0]], b2 := z8 }

def net : TNet :=
  { embed := [[0, 0, 0, 0, 0], [1, 1, 2, 0, 0], [1, 0, 2, 0, 0], [0, 0, 2, 0, 0],
              [0, 0, 1, 0, 0], [0, 0, 1, 0, 0]],
    blocks := [blk1, blk2],
    outW := [0, 0, 1, 0, 1, 0, 0, 0],
    outB := 0 }

def fc (t : ℕ) : ℚ := if t = 1 ∨ t = 2 then 1 else 0
def gc (t : ℕ) : ℚ := if t = 1 then 1 else 0
def dc (t : ℕ) : ℚ := ((dg t : ℕ) : ℚ)

theorem fc_cases (t : ℕ) : fc t = 1 ∨ fc t = 0 := by
  unfold fc
  split_ifs <;> simp

theorem fc_eq_one (t : ℕ) : fc t = 1 ↔ (t = 1 ∨ t = 2) := by
  unfold fc
  split_ifs with h
  · simp [h]
  · simp [h]

theorem fc_zero : fc 0 = 0 := by simp [fc]

theorem gc_of_fc (t : ℕ) (h : fc t ≠ 1) : gc t = 0 := by
  have h1 : t ≠ 1 := fun ht => h ((fc_eq_one t).mpr (Or.inl ht))
  unfold gc
  rw [if_neg h1]

theorem dg_cases (t : ℕ) (h1 : 1 ≤ t) (h5 : t ≤ 5) : dg t = 1 ∨ dg t = 2 := by
  interval_cases t <;> simp [dg]

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

/-! ### numeric lemmas -/

theorem flb {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu : 0 ≤ u) {x B : ℝ}
    (hx : |x| ≤ B) (hB : u * B ≤ 1 / 20) : |fl x - x| ≤ 1 / 20 :=
  le_trans (hr.err hu hx) hB

theorem flθ {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216) :
    ∀ x : ℝ, |x| ≤ 100 → |fl x - x| ≤ 1 / 100000 := by
  intro x hx
  have h1 := hr.err hu0 hx
  have h2 : u * 100 ≤ 1 / 100000 := by linarith
  linarith

theorem fl_pos' {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu1 : u ≤ 1 / 16777216) {x : ℝ}
    (hx : 0 < x) : 0 < fl x := by
  have h := hr.rel x
  rw [abs_of_pos hx] at h
  have h1 := (abs_le.mp h).1
  have h2 : 0 ≤ (1 / 2 - u) * x := mul_nonneg (by linarith) hx.le
  nlinarith

theorem fl_neg' {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu1 : u ≤ 1 / 16777216) {x : ℝ}
    (hx : x < 0) : fl x < 0 := by
  have h := hr.neg (-x)
  rw [neg_neg] at h
  have := fl_pos' hr hu1 (neg_pos.mpr hx)
  linarith

theorem swv {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    (w : ℚ) (v : ℝ) (hv : (w : ℝ) = v) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    |sw fl w d - v| ≤ (1 / 190) * |v| := by
  have h := sw_rel hr hu0 w hd (ε := 1 / 190) (by linarith)
  rw [hv] at h
  exact h

theorem sw1b {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {d : ℝ} (hd : |d| ≤ 1 / 200) : |sw fl 1 d - 1| ≤ 1 / 190 := by
  have h := swv hr hu0 hu1 1 1 (by norm_num) hd
  rw [abs_one] at h
  linarith

theorem sw4b {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {d : ℝ} (hd : |d| ≤ 1 / 200) : |sw fl 4 d - 4| ≤ 4 / 190 := by
  have h := swv hr hu0 hu1 4 4 (by norm_num) hd
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)] at h
  linarith

theorem swm1 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {d : ℝ} (hd : |d| ≤ 1 / 200) : |sw fl (-1) d - (-1)| ≤ 1 / 190 := by
  have h := swv hr hu0 hu1 (-1) (-1) (by norm_num) hd
  rw [abs_neg, abs_one] at h
  linarith

theorem swm2 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {d : ℝ} (hd : |d| ≤ 1 / 200) : |sw fl (-2) d - (-2)| ≤ 2 / 190 := by
  have h := swv hr hu0 hu1 (-2) (-2) (by norm_num) hd
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  linarith

theorem swm3 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {d : ℝ} (hd : |d| ≤ 1 / 200) : |sw fl (-3) d - (-3)| ≤ 3 / 190 := by
  have h := swv hr hu0 hu1 (-3) (-3) (by norm_num) hd
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at h
  linarith

theorem Nfacts {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216) (L : ℕ)
    (hn : u * ((L + 1 : ℕ) : ℝ) ≤ 1 / 256) :
    1 ≤ ((L + 1 : ℕ) : ℝ) + 1 / 256 ∧ u * (10 * (((L + 1 : ℕ) : ℝ) + 1 / 256)) ≤ 1 / 20 := by
  constructor
  · have : (1 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by
      have h1 : 1 ≤ L + 1 := by omega
      exact_mod_cast h1
    linarith
  · nlinarith [hn, hu0, hu1]

theorem flmul_le {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu : 0 ≤ u) {c p N : ℝ}
    (hc1 : 9 / 10 ≤ c) (hc2 : c ≤ 11 / 10) (hp0 : 0 ≤ p) (hpN : p ≤ N) (hN : 1 ≤ N)
    (huN : u * (10 * N) ≤ 1 / 20) : fl (c * p) ≤ 2 * N := by
  have hcp : |c * p| ≤ 10 * N := by
    rw [abs_of_nonneg (mul_nonneg (by linarith) hp0)]
    nlinarith [mul_le_mul_of_nonneg_right hc2 hp0]
  have := (abs_le.mp (flb hr hu hcp huN)).2
  nlinarith [mul_le_mul_of_nonneg_right hc2 hp0]

theorem fl_mul_gap {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu : 0 ≤ u) {c x y g N : ℝ}
    (hc1 : 9 / 10 ≤ c) (hc2 : c ≤ 11 / 10) (hx0 : 0 ≤ x) (hxy : x + g ≤ y) (hg : 0 ≤ g)
    (hyN : y ≤ 2 * N) (hN : 1 ≤ N) (huN : u * (10 * N) ≤ 1 / 20) :
    fl (c * x) + (9 / 10 * g - 1 / 10) ≤ fl (c * y) := by
  have hy0 : 0 ≤ y := by linarith
  have hcx : |c * x| ≤ 10 * N := by
    rw [abs_of_nonneg (mul_nonneg (by linarith) hx0)]
    nlinarith [mul_le_mul_of_nonneg_right hc2 hx0]
  have hcy : |c * y| ≤ 10 * N := by
    rw [abs_of_nonneg (mul_nonneg (by linarith) hy0)]
    nlinarith [mul_le_mul_of_nonneg_right hc2 hy0]
  have e1 := abs_le.mp (flb hr hu hcx huN)
  have e2 := abs_le.mp (flb hr hu hcy huN)
  have e3 : 9 / 10 * g ≤ c * g := by nlinarith [mul_le_mul_of_nonneg_right hc1 hg]
  have e4 : c * g ≤ c * (y - x) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith [e1.1, e1.2, e2.1, e2.2]

theorem t1_close {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu : 0 ≤ u) {a sK p N : ℝ}
    (ha : |a - 1| ≤ 1 / 190) (hsK : |sK - 4| ≤ 4 / 190) (hp0 : 0 ≤ p) (hpN : p ≤ N)
    (hN : 1 ≤ N) (huN : u * (10 * N) ≤ 1 / 20) :
    |fl (a * fl (sK * p)) - a * sK * p| ≤ 11 / 100 := by
  have ha' := abs_le.mp ha
  have hs' := abs_le.mp hsK
  have hsp2 : sK * p ≤ 5 * N := by
    nlinarith [mul_le_mul_of_nonneg_right (show sK ≤ 5 by linarith) hp0]
  have hsp0 : 0 ≤ sK * p := mul_nonneg (by linarith) hp0
  have hsp : |sK * p| ≤ 10 * N := by
    rw [abs_of_nonneg hsp0]
    linarith
  have e1 := flb hr hu hsp huN
  have e1' := abs_le.mp e1
  have hu1b : |fl (sK * p)| ≤ 11 / 2 * N := by
    rw [abs_le]
    constructor <;> linarith
  have haabs : |a| ≤ 11 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hau : |a * fl (sK * p)| ≤ 10 * N := by
    rw [abs_mul]
    calc |a| * |fl (sK * p)| ≤ (11 / 10) * (11 / 2 * N) :=
          mul_le_mul haabs hu1b (abs_nonneg _) (by norm_num)
      _ ≤ 10 * N := by linarith
  have e2 := flb hr hu hau huN
  have h3 : |a * fl (sK * p) - a * (sK * p)| ≤ 11 / 200 := by
    rw [← mul_sub, abs_mul]
    calc |a| * |fl (sK * p) - sK * p| ≤ (11 / 10) * (1 / 20) :=
          mul_le_mul haabs e1 (abs_nonneg _) (by norm_num)
      _ = 11 / 200 := by norm_num
  have a2 := abs_le.mp e2
  have a3 := abs_le.mp h3
  rw [abs_le]
  constructor <;> linarith

theorem t2_close {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu : 0 ≤ u) {m p N : ℝ}
    (hm : |m - (-1)| ≤ 1 / 190) (hp0 : 0 ≤ p) (hpN : p ≤ N) (hN : 1 ≤ N)
    (huN : u * (10 * N) ≤ 1 / 20) : |fl (m * p) - m * p| ≤ 1 / 20 := by
  have hm' := abs_le.mp hm
  have h1 : |m * p| ≤ 10 * N := by
    rw [abs_le]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right (show (-2 : ℝ) ≤ m by linarith) hp0]
    · nlinarith [mul_le_mul_of_nonneg_right (show m ≤ 0 by linarith) hp0]
  exact flb hr hu h1 huN

theorem s1_lt {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu : 0 ≤ u) {a sK m pk pi N : ℝ}
    (ha : |a - 1| ≤ 1 / 190) (hsK : |sK - 4| ≤ 4 / 190) (hm : |m - (-1)| ≤ 1 / 190)
    (hk0 : 0 ≤ pk) (hgap : pk + 127 / 128 ≤ pi) (hpi : pi ≤ N) (hN : 1 ≤ N)
    (huN : u * (10 * N) ≤ 1 / 20) :
    fl (fl (a * fl (sK * pk)) + fl (m * pk)) < fl (fl (a * fl (sK * pi)) + fl (m * pi)) := by
  have hkN : pk ≤ N := by linarith
  have hi0 : 0 ≤ pi := by linarith
  have c1k := abs_le.mp (t1_close hr hu ha hsK hk0 hkN hN huN)
  have c1i := abs_le.mp (t1_close hr hu ha hsK hi0 hpi hN huN)
  have c2k := abs_le.mp (t2_close hr hu hm hk0 hkN hN huN)
  have c2i := abs_le.mp (t2_close hr hu hm hi0 hpi hN huN)
  have ha' := abs_le.mp ha
  have hs' := abs_le.mp hsK
  have hm' := abs_le.mp hm
  have hc_lo : 99 / 100 * (39 / 10) ≤ a * sK :=
    mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
  have hc_hi : a * sK ≤ 11 / 10 * (41 / 10) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have hq : 28 / 10 ≤ a * sK + m := by linarith
  have hprod : (28 / 10) * (pi - pk) ≤ (a * sK + m) * (pi - pk) :=
    mul_le_mul_of_nonneg_right hq (by linarith)
  have hmk1 : (-11 / 10) * pk ≤ m * pk := mul_le_mul_of_nonneg_right (by linarith) hk0
  have hmk2 : m * pk ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_right (show m ≤ 0 by linarith) hk0]
  have hmi1 : (-11 / 10) * pi ≤ m * pi := mul_le_mul_of_nonneg_right (by linarith) hi0
  have hmi2 : m * pi ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_right (show m ≤ 0 by linarith) hi0]
  have hcp1 : 0 ≤ (a * sK) * pk := mul_nonneg (by linarith) hk0
  have hcp2 : (a * sK) * pk ≤ (11 / 10 * (41 / 10)) * pk :=
    mul_le_mul_of_nonneg_right hc_hi hk0
  have hci1 : 0 ≤ (a * sK) * pi := mul_nonneg (by linarith) hi0
  have hci2 : (a * sK) * pi ≤ (11 / 10 * (41 / 10)) * pi :=
    mul_le_mul_of_nonneg_right hc_hi hi0
  apply hr.lt_of_gap hu (B := 10 * N)
  · rw [abs_le]
    constructor <;> linarith [c1k.1, c1k.2, c2k.1, c2k.2]
  · rw [abs_le]
    constructor <;> linarith [c1i.1, c1i.2, c2i.1, c2i.2]
  · linarith [c1k.1, c1k.2, c1i.1, c1i.2, c2k.1, c2k.2, c2i.1, c2i.2]

/-! ### Head scores -/

theorem score1_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (a b c qi qn a' b' c' d' e' qk qn' : ℝ) :
    hd1.score fl dA [a, b, c, 0, 0, 1, qi, qn] [a', b', c', d', e', 1, qk, qn'] =
      fl (fl (a * fl (sw fl 4 (dA 0 6) * qk)) + fl (sw fl (-1) (dA 5 6) * qk)) := by
  simp [Head.score, hd1, z8, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem]

theorem score2_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (a b c d e qi qn a' b' c' d' e' qk qn' : ℝ) :
    hd2.score fl dA [a, b, c, d, e, 1, qi, qn] [a', b', c', d', e', 1, qk, qn'] =
      fl (sw fl 1 (dA 5 3) * d') := by
  simp [Head.score, hd2, z8, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem]

/-! ### initial state -/

theorem init_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j =
      [sw fl (fc (tokAt w j)) (p.E (tokAt w j) 0), sw fl (gc (tokAt w j)) (p.E (tokAt w j) 1),
       sw fl (dc (tokAt w j)) (p.E (tokAt w j) 2), 0, 0, 1, fl (j : ℝ),
       fl (((w.length + 1 : ℕ)) : ℝ)] := by
  have h3 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 ∨
      tokAt w j = 5 := by
    have := tok_le w hw j
    omega
  rcases h3 with h | h | h | h | h | h <;>
    simp [TNet.init, net, swRow, h, fc, gc, dc, dg, sw_zero hr, pos]

/-! ### selection in block 1 -/

theorem sel1_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi : i ≤ w.length) :
    hd1.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i =
      [if fc (tokAt w i) = 1 then i else 0] := by
  obtain ⟨hN1, huN⟩ := Nfacts hu0 hu1 w.length hn
  have hsK := sw4b hr hu0 hu1 (hp.A 0 0 0 6)
  have hm := swm1 hr hu0 hu1 (hp.A 0 0 5 6)
  rcases fc_cases (tokAt w i) with hf | hf
  · rw [if_pos hf]
    apply Head.sel_unique
    · rw [show hd1.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal]
    · intro k hk hne
      rw [show hd1.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal] at hk
      have hki : k < i := lt_of_le_of_ne hk hne
      simp only [init_eq hr p w hw, hf]
      rw [score1_eq hr, score1_eq hr]
      have ha := sw1b hr hu0 hu1 (hp.E (tokAt w i) 0)
      have hgap := hr.pos_gap hu0 hki (show i ≤ w.length + 1 by omega) hn
      have hk0 := (hr.pos_le hu0 (show k ≤ w.length + 1 by omega) hn).1
      have hiN := (hr.pos_le hu0 (show i ≤ w.length + 1 by omega) hn).2
      exact s1_lt hr hu0 ha hsK hm hk0 hgap hiN hN1 huN
  · rw [if_neg (by rw [hf]; norm_num)]
    apply Head.sel_unique
    · rw [show hd1.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal]
      exact Nat.zero_le _
    · intro k hk hne
      rw [show hd1.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal] at hk
      simp only [init_eq hr p w hw, hf]
      rw [score1_eq hr, score1_eq hr]
      simp only [sw_zero hr, zero_mul, hr.zero, zero_add, hr.idem, Nat.cast_zero, mul_zero]
      have hk1 : 0 < k := Nat.pos_of_ne_zero hne
      have hg := hr.pos_gap hu0 hk1 (show k ≤ w.length + 1 by omega) hn
      simp only [Nat.cast_zero, hr.zero, zero_add] at hg
      have hm' := abs_le.mp hm
      have hneg : sw fl (-1) (p.A 0 0 5 6) * fl (k : ℝ) < 0 :=
        mul_neg_of_neg_of_pos (by linarith) (by linarith)
      exact fl_neg' hr hu1 hneg

noncomputable def F1 (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  if fc (tokAt w j) = 1 then fl (sw fl 1 (p.V 0 0 3 6) * fl (j : ℝ)) else 0

theorem fl_F1 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ) :
    fl (F1 fl p w j) = F1 fl p w j := by
  unfold F1
  split_ifs
  · exact hr.idem _
  · exact hr.zero

noncomputable def st1 (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : Vec :=
  [sw fl (fc (tokAt w j)) (p.E (tokAt w j) 0), sw fl (gc (tokAt w j)) (p.E (tokAt w j) 1),
   sw fl (dc (tokAt w j)) (p.E (tokAt w j) 2), F1 fl p w j, 0, 1, fl (j : ℝ),
   fl (((w.length + 1 : ℕ)) : ℝ)]

theorem blk1_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi : i ≤ w.length) :
    Block.apply blk1 fl p 0 (w.length + 1) (net.init fl p w) i = st1 fl p w i := by
  have hs := sel1_eq hr hu0 hu1 p hp w hw hn i hi
  have hV : hd1.V = [z8, z8, z8, [0, 0, 0, 0, 0, 0, 1, 0], z8, z8, z8, z8] := rfl
  rcases fc_cases (tokAt w i) with hf | hf
  · rw [if_pos hf] at hs
    simp only [Block.apply, blk1, headsApply, Head.attn, hs, hV, attnRows, ravg_singleton hr]
    simp only [init_eq hr p w hw]
    simp [st1, F1, hf, z8, pos, rdot, radd, raffine, sw_zero hr, hr.zero, hr.idem, hr.one,
      fl_sw hr]
  · rw [if_neg (by rw [hf]; norm_num)] at hs
    simp only [Block.apply, blk1, headsApply, Head.attn, hs, hV, attnRows, ravg_singleton hr]
    simp only [init_eq hr p w hw]
    simp [st1, F1, hf, z8, pos, rdot, radd, raffine, sw_zero hr, hr.zero, hr.idem, hr.one,
      fl_sw hr]

/-! ### selection in block 2 -/

theorem selOf_all (c : List ℕ) (s : ℕ → ℝ) (h : ∀ k ∈ c, ∀ l ∈ c, s k = s l) :
    selOf c s = c := by
  unfold selOf
  rw [List.filter_eq_self]
  intro j hj
  rw [decide_eq_true_eq]
  intro k hk
  exact le_of_eq (h k hk j hj)

theorem sel2_none {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi : i ≤ w.length) (hnone : ∀ k, k < i → fc (tokAt w k) ≠ 1) :
    hd2.sel fl (p.A 1 0) (w.length + 1)
      (Block.apply blk1 fl p 0 (w.length + 1) (net.init fl p w)) i = List.range i := by
  have hsc : ∀ k, k < i →
      hd2.score fl (p.A 1 0) (Block.apply blk1 fl p 0 (w.length + 1) (net.init fl p w) i)
        (Block.apply blk1 fl p 0 (w.length + 1) (net.init fl p w) k) = 0 := by
    intro k hk
    rw [blk1_eq hr hu0 hu1 p hp w hw hn i hi, blk1_eq hr hu0 hu1 p hp w hw hn k (by omega)]
    simp only [st1]
    rw [score2_eq hr]
    have h0 : F1 fl p w k = 0 := by
      unfold F1
      rw [if_neg (hnone k hk)]
    rw [h0, mul_zero, hr.zero]
  have h := selOf_all (cand hd2.mask (w.length + 1) i)
    (fun j => hd2.score fl (p.A 1 0) (Block.apply blk1 fl p 0 (w.length + 1) (net.init fl p w) i)
      (Block.apply blk1 fl p 0 (w.length + 1) (net.init fl p w) j))
    (by
      intro k hk l hl
      have hk' : k < i := by
        rw [show hd2.mask = Mask.strict from rfl, Lane4.Seq.mem_cand_strict] at hk
        exact hk
      have hl' : l < i := by
        rw [show hd2.mask = Mask.strict from rfl, Lane4.Seq.mem_cand_strict] at hl
        exact hl
      exact (hsc k hk').trans (hsc l hl').symm)
  unfold Head.sel
  rw [h]
  rfl

theorem sel2_some {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi : i ≤ w.length) (L : ℕ) (hL1 : 1 ≤ L) (hLi : L < i)
    (hLf : fc (tokAt w L) = 1) (hafter : ∀ k, L < k → k < i → fc (tokAt w k) ≠ 1) :
    hd2.sel fl (p.A 1 0) (w.length + 1)
      (Block.apply blk1 fl p 0 (w.length + 1) (net.init fl p w)) i = [L] := by
  obtain ⟨hN1, huN⟩ := Nfacts hu0 hu1 w.length hn
  have hsA := sw1b hr hu0 hu1 (hp.A 1 0 5 3)
  have hsV := sw1b hr hu0 hu1 (hp.V 0 0 3 6)
  have hsA' := abs_le.mp hsA
  have hsV' := abs_le.mp hsV
  have hLw : L ≤ w.length := by omega
  have hpL := hr.pos_le hu0 (show L ≤ w.length + 1 by omega) hn
  have hgL := hr.pos_gap hu0 (show 0 < L by omega) (show L ≤ w.length + 1 by omega) hn
  simp only [Nat.cast_zero, hr.zero, zero_add] at hgL
  apply Head.sel_unique
  · rw [show hd2.mask = Mask.strict from rfl, Lane4.Seq.mem_cand_strict]
    exact hLi
  · intro k hk hne
    rw [show hd2.mask = Mask.strict from rfl, Lane4.Seq.mem_cand_strict] at hk
    rw [blk1_eq hr hu0 hu1 p hp w hw hn i hi, blk1_eq hr hu0 hu1 p hp w hw hn k (by omega),
      blk1_eq hr hu0 hu1 p hp w hw hn L hLw]
    simp only [st1]
    rw [score2_eq hr, score2_eq hr]
    by_cases hkf : fc (tokAt w k) = 1
    · have hkL : k < L := by
        by_contra hcon
        exact hafter k (lt_of_le_of_ne (not_lt.mp hcon) (Ne.symm hne)) hk hkf
      have hgap := hr.pos_gap hu0 hkL (show L ≤ w.length + 1 by omega) hn
      have hk0 := (hr.pos_le hu0 (show k ≤ w.length + 1 by omega) hn).1
      unfold F1
      rw [if_pos hkf, if_pos hLf]
      have g1 := fl_mul_gap hr hu0 (c := sw fl 1 (p.V 0 0 3 6)) (x := fl (k : ℝ))
        (y := fl (L : ℝ)) (g := 127 / 128) (N := ((w.length + 1 : ℕ) : ℝ) + 1 / 256)
        (by linarith) (by linarith) hk0 hgap (by norm_num) (by linarith [hpL.2]) hN1 huN
      have hx2 : 0 ≤ fl (sw fl 1 (p.V 0 0 3 6) * fl (k : ℝ)) :=
        hr.nonneg (mul_nonneg (by linarith) hk0)
      have hy2 : fl (sw fl 1 (p.V 0 0 3 6) * fl (L : ℝ)) ≤
          2 * (((w.length + 1 : ℕ) : ℝ) + 1 / 256) :=
        flmul_le hr hu0 (by linarith) (by linarith) hpL.1 hpL.2 hN1 huN
      have g2 := fl_mul_gap hr hu0 (c := sw fl 1 (p.A 1 0 5 3))
        (x := fl (sw fl 1 (p.V 0 0 3 6) * fl (k : ℝ)))
        (y := fl (sw fl 1 (p.V 0 0 3 6) * fl (L : ℝ)))
        (g := 9 / 10 * (127 / 128) - 1 / 10) (N := ((w.length + 1 : ℕ) : ℝ) + 1 / 256)
        (by linarith) (by linarith) hx2 g1 (by norm_num) hy2 hN1 huN
      linarith [g2]
    · unfold F1
      rw [if_neg hkf, if_pos hLf, mul_zero, hr.zero]
      apply fl_pos' hr hu1
      have hpos : 0 < fl (sw fl 1 (p.V 0 0 3 6) * fl (L : ℝ)) := by
        apply fl_pos' hr hu1
        exact mul_pos (by linarith) (by linarith)
      exact mul_pos (by linarith) hpos

/-! ### block 2 and the readout -/

theorem ravg_eq_zero {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (S : List ℕ) (f : ℕ → ℝ)
    (h : ∀ j ∈ S, f j = 0) : ravg fl S f = 0 := by
  have h2 : S.map f = S.map (fun _ => (0 : ℝ)) := List.map_congr_left h
  have := ravg_zero hr S
  unfold ravg at this ⊢
  rw [h2]
  exact this

noncomputable def Fexpr (fl : ℝ → ℝ) (oa ob D Cr wa wb sb wm : ℝ) : ℝ :=
  fl (fl (oa * D) + fl (ob * fl (fl Cr + fl (wm * relu (fl (fl (fl (wa * D) + fl (wb * fl Cr)) + sb))))))

theorem out_blk2 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (x1 : ℕ → Vec) (hx1 : ∀ j, j ≤ w.length → x1 j = st1 fl p w j)
    (i : ℕ) (hi : i ≤ w.length) (S : List ℕ) (hSle : ∀ j ∈ S, j ≤ w.length) (Cr : ℝ)
    (hS : hd2.sel fl (p.A 1 0) (w.length + 1) x1 i = S)
    (hC : ravg fl S (fun j => rdot fl v4 (x1 j) (p.V 1 0 4) 0 0) = Cr) :
    fl (rdot fl net.outW (Block.apply blk2 fl p 1 (w.length + 1) x1 i) p.oW 0 0 +
        sw fl net.outB p.oB) =
      Fexpr fl (sw fl 1 (p.oW 2)) (sw fl 1 (p.oW 4))
        (sw fl (dc (tokAt w i)) (p.E (tokAt w i) 2)) Cr (sw fl 1 (p.W1 1 0 2))
        (sw fl 1 (p.W1 1 0 4)) (sw fl (-2) (p.b1 1 0)) (sw fl (-3) (p.W2 1 4 0)) := by
  have hz : ∀ (d : ℕ → ℝ), ravg fl S (fun j => rdot fl z8 (x1 j) d 0 0) = 0 := by
    intro d
    apply ravg_eq_zero hr
    intro j hj
    rw [hx1 j (hSle j hj)]
    simp [st1, z8, rdot, sw_zero hr, hr.zero]
  have hV2 : hd2.V = [z8, z8, z8, z8, v4, z8, z8, z8] := rfl
  have ho : net.outW = [0, 0, 1, 0, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  rw [ho, hc]
  simp only [Block.apply, blk2, headsApply, Head.attn, hS, hV2, attnRows, hz, hC]
  rw [hx1 i hi]
  simp [Fexpr, st1, v4, z8, pos, rdot, radd, raffine, sw_zero hr, hr.zero, hr.idem, hr.one,
    fl_sw hr, fl_F1 hr]

theorem Cr_some {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (x1 : ℕ → Vec) (L : ℕ) (hx : x1 L = st1 fl p w L) :
    ravg fl [L] (fun j => rdot fl v4 (x1 j) (p.V 1 0 4) 0 0) =
      fl (sw fl 1 (p.V 1 0 4 1) * sw fl (gc (tokAt w L)) (p.E (tokAt w L) 1)) := by
  simp only [ravg_singleton hr, hx]
  simp [st1, v4, rdot, sw_zero hr, hr.zero, hr.idem]

/-! ### the numeric finish -/

theorem mulc {w c v t e E B K : ℝ} (hw : |w - c| ≤ e) (hv : |v - t| ≤ E) (hB : |v| ≤ B)
    (hc : |c| ≤ K) : |w * v - c * t| ≤ e * B + K * E := by
  have h : w * v - c * t = (w - c) * v + c * (v - t) := by ring
  rw [h]
  have h1 : |(w - c) * v| ≤ e * B := by
    rw [abs_mul]
    exact mul_le_mul hw hB (abs_nonneg _) (le_trans (abs_nonneg _) hw)
  have h2 : |c * (v - t)| ≤ K * E := by
    rw [abs_mul]
    exact mul_le_mul hc hv (abs_nonneg _) (le_trans (abs_nonneg _) hc)
  exact le_trans (abs_add_le _ _) (add_le_add h1 h2)

theorem rnd {fl : ℝ → ℝ} {θ : ℝ} (fb : ∀ x : ℝ, |x| ≤ 100 → |fl x - x| ≤ θ) {x t e : ℝ}
    (hx : |x - t| ≤ e) (ht : |t| ≤ 50) (he : e ≤ 1) : |fl x - t| ≤ e + θ := by
  have h1 : |x| ≤ 100 := by
    have := abs_sub_abs_le_abs_sub x t
    linarith
  have h2 := fb x h1
  have h3 := abs_add_le (fl x - x) (x - t)
  have h4 : fl x - x + (x - t) = fl x - t := by ring
  rw [h4] at h3
  linarith

theorem relu_lip (a b : ℝ) : |relu a - relu b| ≤ |a - b| := by
  unfold relu
  rcases le_total a 0 with h1 | h1 <;> rcases le_total b 0 with h2 | h2
  · rw [max_eq_right h1, max_eq_right h2]
    exact abs_le.mpr ⟨by linarith [neg_abs_le (a - b), le_abs_self (a - b), neg_le_abs (a - b), abs_nonneg (a - b)], by linarith [neg_abs_le (a - b), le_abs_self (a - b), neg_le_abs (a - b), abs_nonneg (a - b)]⟩
  · rw [max_eq_right h1, max_eq_left h2]
    exact abs_le.mpr ⟨by linarith [neg_abs_le (a - b), le_abs_self (a - b), neg_le_abs (a - b), abs_nonneg (a - b)], by linarith [neg_abs_le (a - b), le_abs_self (a - b), neg_le_abs (a - b), abs_nonneg (a - b)]⟩
  · rw [max_eq_left h1, max_eq_right h2]
    exact abs_le.mpr ⟨by linarith [neg_abs_le (a - b), le_abs_self (a - b), neg_le_abs (a - b), abs_nonneg (a - b)], by linarith [neg_abs_le (a - b), le_abs_self (a - b), neg_le_abs (a - b), abs_nonneg (a - b)]⟩
  · rw [max_eq_left h1, max_eq_left h2]

theorem final_num {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (d0 c0 tg D Cr wa wb sb wm oa ob : ℝ)
    (hcase : (d0 = 1 ∧ c0 = 0 ∧ tg = 1) ∨ (d0 = 1 ∧ c0 = 1 ∧ tg = 2) ∨
      (d0 = 2 ∧ c0 = 0 ∧ tg = 2) ∨ (d0 = 2 ∧ c0 = 1 ∧ tg = 0))
    (hD : |D - d0| ≤ 2 / 190) (hC : |Cr - c0| ≤ 1 / 94) (hCfix : fl Cr = Cr)
    (hwa : |wa - 1| ≤ 1 / 190) (hwb : |wb - 1| ≤ 1 / 190) (hsb : |sb - (-2)| ≤ 2 / 190)
    (hwm : |wm - (-3)| ≤ 3 / 190) (hoa : |oa - 1| ≤ 1 / 190) (hob : |ob - 1| ≤ 1 / 190) :
    |Fexpr fl oa ob D Cr wa wb sb wm - tg| ≤ 1 / 4 := by
  have fb := flθ hr hu0 hu1
  obtain ⟨H0, hH0a, hH0b, htg, hH0r⟩ : ∃ H0 : ℝ, 0 ≤ H0 ∧ H0 ≤ 1 ∧ tg = d0 + c0 - 3 * H0 ∧
      relu (d0 + c0 - 2) = H0 := by
    rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · refine ⟨0, le_refl _, by norm_num, ?_, ?_⟩
      · rw [h1, h2, h3]; norm_num
      · rw [h1, h2]; simp only [relu]; norm_num [max_def]
    · refine ⟨0, le_refl _, by norm_num, ?_, ?_⟩
      · rw [h1, h2, h3]; norm_num
      · rw [h1, h2]; simp only [relu]; norm_num [max_def]
    · refine ⟨0, le_refl _, by norm_num, ?_, ?_⟩
      · rw [h1, h2, h3]; norm_num
      · rw [h1, h2]; simp only [relu]; norm_num [max_def]
    · refine ⟨1, by norm_num, le_refl _, ?_, ?_⟩
      · rw [h1, h2, h3]; norm_num
      · rw [h1, h2]; simp only [relu]; norm_num [max_def]
  obtain ⟨hd1', hd2'⟩ : 1 ≤ d0 ∧ d0 ≤ 2 := by
    rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
      constructor <;> linarith
  obtain ⟨hc1', hc2'⟩ : 0 ≤ c0 ∧ c0 ≤ 1 := by
    rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
      constructor <;> linarith
  have hDa := abs_le.mp hD
  have hCa := abs_le.mp hC
  have hDb : |D| ≤ 51 / 25 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hCb : |Cr| ≤ 51 / 50 := abs_le.mpr ⟨by linarith, by linarith⟩
  have one_abs : |(1 : ℝ)| ≤ 1 := by norm_num
  have m3_abs : |(-3 : ℝ)| ≤ 3 := by norm_num
  unfold Fexpr
  rw [hCfix]
  set P1 := fl (wa * D) with hP1
  set P2 := fl (wb * Cr) with hP2
  set Q := fl (P1 + P2) with hQ
  set S1 := fl (Q + sb) with hS1
  set z := fl (wm * relu S1) with hz
  set Cp := fl (Cr + z) with hCp
  set R3 := fl (ob * Cp) with hR3
  set R2 := fl (oa * D) with hR2
  have q1 : |wa * D - d0| ≤ 1 / 190 * (51 / 25) + 2 / 190 := by
    have h := mulc hwa hD hDb one_abs
    simpa only [one_mul] using h
  have p1 : |P1 - d0| ≤ 213 / 10000 :=
    le_trans (rnd fb q1 (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)) (by norm_num)
  have q2 : |wb * Cr - c0| ≤ 1 / 190 * (51 / 50) + 1 / 94 := by
    have h := mulc hwb hC hCb one_abs
    simpa only [one_mul] using h
  have p2 : |P2 - c0| ≤ 161 / 10000 :=
    le_trans (rnd fb q2 (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)) (by norm_num)
  have q3 : |(P1 + P2) - (d0 + c0)| ≤ 374 / 10000 := by
    have a1 := abs_le.mp p1
    have a2 := abs_le.mp p2
    rw [abs_le]
    constructor <;> linarith
  have p3 : |Q - (d0 + c0)| ≤ 375 / 10000 :=
    le_trans (rnd fb q3 (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)) (by norm_num)
  have q4 : |(Q + sb) - (d0 + c0 - 2)| ≤ 375 / 10000 + 2 / 190 := by
    have a3 := abs_le.mp p3
    have a4 := abs_le.mp hsb
    rw [abs_le]
    constructor <;> linarith
  have p4 : |S1 - (d0 + c0 - 2)| ≤ 481 / 10000 :=
    le_trans (rnd fb q4 (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)) (by norm_num)
  have hh : |relu S1 - H0| ≤ 481 / 10000 := by
    have h1 := relu_lip S1 (d0 + c0 - 2)
    rw [hH0r] at h1
    exact le_trans h1 p4
  have hha := abs_le.mp hh
  have hhB : |relu S1| ≤ 21 / 20 := abs_le.mpr ⟨by linarith, by linarith⟩
  have q5 : |wm * relu S1 - (-3) * H0| ≤ 3 / 190 * (21 / 20) + 3 * (481 / 10000) :=
    mulc hwm hh hhB m3_abs
  have p5 : |z - (-3) * H0| ≤ 1609 / 10000 :=
    le_trans (rnd fb q5 (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)) (by norm_num)
  have q6 : |(Cr + z) - (c0 + (-3) * H0)| ≤ 1 / 94 + 1609 / 10000 := by
    have a5 := abs_le.mp p5
    rw [abs_le]
    constructor <;> linarith
  have p6 : |Cp - (c0 + (-3) * H0)| ≤ 1716 / 10000 :=
    le_trans (rnd fb q6 (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)) (by norm_num)
  have hCpB : |Cp| ≤ 16 / 5 := by
    have a6 := abs_le.mp p6
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have q7 : |ob * Cp - (c0 + (-3) * H0)| ≤ 1 / 190 * (16 / 5) + 1716 / 10000 := by
    have h := mulc hob p6 hCpB one_abs
    simpa only [one_mul] using h
  have p7 : |R3 - (c0 + (-3) * H0)| ≤ 1885 / 10000 :=
    le_trans (rnd fb q7 (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)) (by norm_num)
  have q8 : |oa * D - d0| ≤ 1 / 190 * (51 / 25) + 2 / 190 := by
    have h := mulc hoa hD hDb one_abs
    simpa only [one_mul] using h
  have p8 : |R2 - d0| ≤ 213 / 10000 :=
    le_trans (rnd fb q8 (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)) (by norm_num)
  have q9 : |(R2 + R3) - (d0 + (c0 + (-3) * H0))| ≤ 2098 / 10000 := by
    have a7 := abs_le.mp p7
    have a8 := abs_le.mp p8
    rw [abs_le]
    constructor <;> linarith
  have p9 : |fl (R2 + R3) - (d0 + (c0 + (-3) * H0))| ≤ 2099 / 10000 :=
    le_trans (rnd fb q9 (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)) (by norm_num)
  have a9 := abs_le.mp p9
  rw [abs_le]
  constructor <;> linarith

theorem glue {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (D Cr wa wb sb wm oa ob : ℝ) (dgv cv : ℕ)
    (hdg : dgv = 1 ∨ dgv = 2) (hcv : cv = 0 ∨ cv = 1)
    (hD : |D - (dgv : ℝ)| ≤ 2 / 190) (hC : |Cr - (cv : ℝ)| ≤ 1 / 94) (hCfix : fl Cr = Cr)
    (hwa : |wa - 1| ≤ 1 / 190) (hwb : |wb - 1| ≤ 1 / 190) (hsb : |sb - (-2)| ≤ 2 / 190)
    (hwm : |wm - (-3)| ≤ 3 / 190) (hoa : |oa - 1| ≤ 1 / 190) (hob : |ob - 1| ≤ 1 / 190) :
    |Fexpr fl oa ob D Cr wa wb sb wm - (((dgv + cv) % 3 : ℕ) : ℝ)| ≤ 1 / 4 := by
  rcases hdg with rfl | rfl <;> rcases hcv with rfl | rfl
  · have h := final_num hr hu0 hu1 1 0 1 D Cr wa wb sb wm oa ob (Or.inl ⟨rfl, rfl, rfl⟩)
      (by simpa using hD) (by simpa using hC) hCfix hwa hwb hsb hwm hoa hob
    simpa using h
  · have h := final_num hr hu0 hu1 1 1 2 D Cr wa wb sb wm oa ob
      (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
      (by simpa using hD) (by simpa using hC) hCfix hwa hwb hsb hwm hoa hob
    simpa using h
  · have h := final_num hr hu0 hu1 2 0 2 D Cr wa wb sb wm oa ob
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
      (by simpa using hD) (by simpa using hC) hCfix hwa hwb hsb hwm hoa hob
    simpa using h
  · have h := final_num hr hu0 hu1 2 1 0 D Cr wa wb sb wm oa ob
      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))
      (by simpa using hD) (by simpa using hC) hCfix hwa hwb hsb hwm hoa hob
    simpa using h

/-! ### carry -/

theorem carry_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) :
    ∀ m, m ≤ w.length →
      carry (w.take m) =
        if tokAt w (Nat.findGreatest (fun j => fc (tokAt w j) = 1) m) = 1 then 1 else 0 := by
  intro m
  induction m with
  | zero =>
    intro _
    simp [carry, Lane4.Seq.tokAt_zero]
  | succ m ih =>
    intro hm
    have ih' := ih (by omega)
    have htm : tokAt w (m + 1) = w[m] := Lane4.Seq.tokAt_succ w m (by omega)
    have hmem : w[m] ∈ w := List.getElem_mem (by omega)
    have hb := hw _ hmem
    have htake : w.take (m + 1) = w.take m ++ [w[m]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (show m < w.length by omega)]
      rfl
    have hfold : carry (w.take (m + 1)) =
        (fun c t => if cls t = 2 then c else cls t) (carry (w.take m)) w[m] := by
      rw [htake]
      unfold carry
      rw [List.foldl_append]
      rfl
    rw [hfold, ih']
    by_cases hP : fc (tokAt w (m + 1)) = 1
    · have h12 : w[m] = 1 ∨ w[m] = 2 := by
        rw [← htm]
        exact (fc_eq_one _).mp hP
      rw [Nat.findGreatest_succ]
      simp only [if_pos hP]
      rw [htm]
      rcases h12 with h | h <;> simp [h, cls]
    · have hnot : ¬ (w[m] = 1 ∨ w[m] = 2) := by
        intro h
        apply hP
        rw [htm]
        exact (fc_eq_one _).mpr h
      have h345 : w[m] = 3 ∨ w[m] = 4 ∨ w[m] = 5 := by omega
      have hcls : cls w[m] = 2 := by
        rcases h345 with h | h | h <;> simp [cls, h]
      rw [Nat.findGreatest_succ]
      simp only [if_neg hP]
      simp [hcls]

/-! ### crb -/

theorem crb1 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) :
    |fl (sw fl 1 (p.V 1 0 4 1) * sw fl (gc 1) (p.E 1 1)) - 1| ≤ 1 / 94 := by
  have hg : gc 1 = 1 := by simp [gc]
  rw [hg]
  have ha := sw1b hr hu0 hu1 (hp.V 1 0 4 1)
  have hb := sw1b hr hu0 hu1 (hp.E 1 1)
  have hba := abs_le.mp hb
  have hB : |sw fl 1 (p.E 1 1)| ≤ 191 / 190 := abs_le.mpr ⟨by linarith, by linarith⟩
  have q := mulc ha hb hB (show |(1 : ℝ)| ≤ 1 by norm_num)
  simp only [one_mul, mul_one] at q
  exact le_trans (rnd (flθ hr hu0 hu1) q (by norm_num) (by norm_num)) (by norm_num)

theorem crb2 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) :
    fl (sw fl 1 (p.V 1 0 4 1) * sw fl (gc 2) (p.E 2 1)) = 0 := by
  have hg : gc 2 = 0 := by simp [gc]
  rw [hg, sw_zero hr, mul_zero, hr.zero]

/-! ### finish -/

theorem finish {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length)
    (S : List ℕ) (hSle : ∀ j ∈ S, j ≤ w.length) (Cr : ℝ) (cv : ℕ) (hcv : cv = 0 ∨ cv = 1)
    (hS : hd2.sel fl (p.A 1 0) (w.length + 1)
      (Block.apply blk1 fl p 0 (w.length + 1) (net.init fl p w)) i = S)
    (hC : ravg fl S (fun j => rdot fl v4
      (Block.apply blk1 fl p 0 (w.length + 1) (net.init fl p w) j) (p.V 1 0 4) 0 0) = Cr)
    (hCb : |Cr - (cv : ℝ)| ≤ 1 / 94) (hCfix : fl Cr = Cr)
    (hcar : carry (w.take (i - 1)) = cv) :
    |net.out fl p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  have hx1 : ∀ j, j ≤ w.length →
      Block.apply blk1 fl p 0 (w.length + 1) (net.init fl p w) j = st1 fl p w j :=
    fun j hj => blk1_eq hr hu0 hu1 p hp w hw hn j hj
  have hrun : net.out fl p w i =
      fl (rdot fl net.outW (Block.apply blk2 fl p 1 (w.length + 1)
        (Block.apply blk1 fl p 0 (w.length + 1) (net.init fl p w)) i) p.oW 0 0 +
        sw fl net.outB p.oB) := rfl
  have hti : tokAt w i ∈ w := by
    have h := Lane4.Seq.tokAt_succ w (i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at h
    rw [h]
    exact List.getElem_mem (by omega)
  obtain ⟨ht1, ht5⟩ := hw _ hti
  have hget : tokAt w i = w.getD (i - 1) 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp [tokAt]
  have htarget : target w i = (dg (tokAt w i) + carry (w.take (i - 1))) % 3 := by
    unfold target
    rw [hget]
  have hdg : dg (tokAt w i) = 1 ∨ dg (tokAt w i) = 2 := dg_cases _ ht1 ht5
  have hdgR : ((dg (tokAt w i) : ℕ) : ℝ) ≤ 2 := by
    rcases hdg with h | h <;> rw [h] <;> norm_num
  have hD : |sw fl (dc (tokAt w i)) (p.E (tokAt w i) 2) - ((dg (tokAt w i) : ℕ) : ℝ)| ≤ 2 / 190 := by
    have h := swv hr hu0 hu1 (dc (tokAt w i)) ((dg (tokAt w i) : ℕ) : ℝ) (by simp [dc])
      (hp.E (tokAt w i) 2)
    rw [abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ ((dg (tokAt w i) : ℕ) : ℝ))] at h
    linarith
  have hwa := sw1b hr hu0 hu1 (hp.W1 1 0 2)
  have hwb := sw1b hr hu0 hu1 (hp.W1 1 0 4)
  have hsb := swm2 hr hu0 hu1 (hp.b1 1 0)
  have hwm := swm3 hr hu0 hu1 (hp.W2 1 4 0)
  have hoa := sw1b hr hu0 hu1 (hp.oW 2)
  have hob := sw1b hr hu0 hu1 (hp.oW 4)
  rw [hrun, out_blk2 hr p w (Block.apply blk1 fl p 0 (w.length + 1) (net.init fl p w)) hx1 i hi
    S hSle Cr hS hC, htarget, hcar]
  exact glue hr hu0 hu1 _ Cr _ _ _ _ _ _ (dg (tokAt w i)) cv hdg hcv hD hCb hCfix hwa hwb hsb hwm
    hoa hob

theorem net_ok : Statement net := by
  intro u fl hr hu0 hu1 p hp w hw hn i hi1 hi
  have hx1 : ∀ j, j ≤ w.length →
      Block.apply blk1 fl p 0 (w.length + 1) (net.init fl p w) j = st1 fl p w j :=
    fun j hj => blk1_eq hr hu0 hu1 p hp w hw hn j hj
  have hcar := carry_eq w hw (i - 1) (by omega)
  by_cases hL : Nat.findGreatest (fun j => fc (tokAt w j) = 1) (i - 1) = 0
  · have hnone : ∀ k, k < i → fc (tokAt w k) ≠ 1 := by
      intro k hk
      by_cases hk0 : k = 0
      · subst hk0
        rw [Lane4.Seq.tokAt_zero, fc_zero]
        norm_num
      · exact fun h => (Nat.findGreatest_eq_zero_iff.mp hL (Nat.pos_of_ne_zero hk0) (by omega)) h
    have hsel := sel2_none hr hu0 hu1 p hp w hw hn i hi hnone
    have hSle : ∀ j ∈ List.range i, j ≤ w.length := by
      intro j hj
      have := List.mem_range.mp hj
      omega
    have hC : ravg fl (List.range i) (fun j => rdot fl v4
        (Block.apply blk1 fl p 0 (w.length + 1) (net.init fl p w) j) (p.V 1 0 4) 0 0) = 0 := by
      apply ravg_eq_zero hr
      intro j hj
      have hj' := List.mem_range.mp hj
      rw [hx1 j (by omega)]
      have hg : gc (tokAt w j) = 0 := gc_of_fc _ (hnone j hj')
      simp [st1, v4, rdot, hg, sw_zero hr, hr.zero]
    have hcar0 : carry (w.take (i - 1)) = 0 := by
      rw [hcar, hL, Lane4.Seq.tokAt_zero]
      simp
    exact finish hr hu0 hu1 p hp w hw hn i hi1 hi (List.range i) hSle 0 0 (Or.inl rfl) hsel hC
      (by simp) hr.zero hcar0
  · set L := Nat.findGreatest (fun j => fc (tokAt w j) = 1) (i - 1) with hLdef
    have hLle : L ≤ i - 1 := Nat.findGreatest_le _
    have hLf : fc (tokAt w L) = 1 := Nat.findGreatest_of_ne_zero rfl hL
    have hafter : ∀ k, L < k → k < i → fc (tokAt w k) ≠ 1 := by
      intro k hk1 hk2 h
      exact Nat.findGreatest_is_greatest hk1 (by omega) h
    have hsel := sel2_some hr hu0 hu1 p hp w hw hn i hi L (Nat.pos_of_ne_zero hL) (by omega) hLf
      hafter
    have hSle : ∀ j ∈ [L], j ≤ w.length := by
      intro j hj
      have := List.mem_singleton.mp hj
      omega
    have hC := Cr_some hr p w (Block.apply blk1 fl p 0 (w.length + 1) (net.init fl p w)) L
      (hx1 L (by omega))
    rcases (fc_eq_one _).mp hLf with ht | ht
    · have hcar1 : carry (w.take (i - 1)) = 1 := by
        rw [hcar, if_pos ht]
      have hCb : |fl (sw fl 1 (p.V 1 0 4 1) * sw fl (gc (tokAt w L)) (p.E (tokAt w L) 1)) -
          ((1 : ℕ) : ℝ)| ≤ 1 / 94 := by
        rw [ht]
        simpa using crb1 hr hu0 hu1 p hp
      exact finish hr hu0 hu1 p hp w hw hn i hi1 hi [L] hSle _ 1 (Or.inr rfl) hsel hC hCb
        (hr.idem _) hcar1
    · have hcar0 : carry (w.take (i - 1)) = 0 := by
        rw [hcar, if_neg (by rw [ht]; norm_num)]
      have hCz : fl (sw fl 1 (p.V 1 0 4 1) * sw fl (gc (tokAt w L)) (p.E (tokAt w L) 1)) = 0 := by
        rw [ht]
        exact crb2 hr p
      have hCb : |fl (sw fl 1 (p.V 1 0 4 1) * sw fl (gc (tokAt w L)) (p.E (tokAt w L) 1)) -
          ((0 : ℕ) : ℝ)| ≤ 1 / 94 := by
        rw [hCz]
        norm_num
      exact finish hr hu0 hu1 p hp w hw hn i hi1 hi [L] hSle _ 0 (Or.inl rfl) hsel hC hCb
        (hr.idem _) hcar0

end Lane4.Case
