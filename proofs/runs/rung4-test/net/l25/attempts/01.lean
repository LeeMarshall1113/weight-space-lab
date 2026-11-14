namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

/-- State: [val, gate, res, 1, fl i, fl n] (width 6). -/
def z6 : List ℚ := [0, 0, 0, 0, 0, 0]

/-- Causal head. Score = (stored 1) * position of the key  +  n * (stored 2) * gate(key).
The gate is 0 on marked tokens and about -1 on unmarked ones, so marked keys win and the
latest marked key wins among them. Value: write the key's `val` into slot `res`. -/
def hh : Head :=
  { A := [z6, z6, z6, [0, 0, 0, 0, 1, 0], z6, [0, 2, 0, 0, 0, 0]],
    V := [z6, z6, [1, 0, 0, 0, 0, 0], z6, z6, z6],
    mask := Mask.causal }

def blk1 : Block :=
  { heads := [], W1 := [[-2, 0, 0, 0, 0, 0]], b1 := [1],
    W2 := [[0], [-1], [0], [0], [0], [0]], b2 := z6 }

def blk2 : Block :=
  { heads := [hh], W1 := [], b1 := [], W2 := [[], [], [], [], [], []], b2 := z6 }

def net : TNet :=
  { embed := [[0, 0, 0], [2, 0, 0], [2, 0, 0], [3, 0, 0], [0, 0, 0], [1, 0, 0]],
    blocks := [blk1, blk2],
    outW := [0, 0, 1, 0, 0, 0],
    outB := 0 }

/-! ### generic lemmas -/

theorem sw_neg {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (w : ℚ) (d : ℝ) :
    sw fl (-w) d = -sw fl w d := by
  unfold sw
  have : ((-w : ℚ) : ℝ) * (1 + d) = -((w : ℝ) * (1 + d)) := by push_cast; ring
  rw [this, hr.neg]

theorem sw_pos {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (w : ℚ) (hw : 0 ≤ (w : ℝ)) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    (w : ℝ) * (247 / 250) ≤ sw fl w d ∧ sw fl w d ≤ (w : ℝ) * (253 / 250) := by
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 3 / 250 := by linarith
  have h := sw_rel hr hu0 w hd hε
  rw [abs_of_nonneg hw] at h
  have h2 := abs_le.mp h
  constructor <;> linarith [h2.1, h2.2]

theorem sw_one_bnd {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    247 / 250 ≤ sw fl 1 d ∧ sw fl 1 d ≤ 253 / 250 := by
  have h := sw_pos hr hu0 hu1 1 (by norm_num) hd
  have e : ((1 : ℚ) : ℝ) = 1 := by norm_num
  rw [e] at h
  constructor <;> linarith [h.1, h.2]

theorem sw_two_bnd {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    247 / 125 ≤ sw fl 2 d ∧ sw fl 2 d ≤ 253 / 125 := by
  have h := sw_pos hr hu0 hu1 2 (by norm_num) hd
  have e : ((2 : ℚ) : ℝ) = 2 := by norm_num
  rw [e] at h
  constructor <;> linarith [h.1, h.2]

theorem fl_ravg {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (S : List ℕ) (f : ℕ → ℝ) :
    fl (ravg fl S f) = ravg fl S f := by
  unfold ravg
  exact hr.idem _

theorem ravg_zero_on {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (S : List ℕ) (f : ℕ → ℝ)
    (h : ∀ j ∈ S, f j = 0) : ravg fl S f = 0 := by
  have hm : S.map f = S.map (fun _ => (0 : ℝ)) := List.map_congr_left (fun a ha => h a ha)
  have h0 := ravg_zero hr S
  unfold ravg at h0 ⊢
  rw [hm]
  exact h0

/-! ### numeric lemmas about scores -/

theorem unm_le {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {σ κ g qn fk N : ℝ} (hσ0 : 247 / 250 ≤ σ) (hσ1 : σ ≤ 253 / 250)
    (hκ : 247 / 125 ≤ κ) (hg : g ≤ -(9 / 10)) (hqn1 : N - 1 / 256 ≤ qn)
    (hqn2 : qn ≤ N + 1 / 256) (hfk0 : 0 ≤ fk) (hfk1 : fk ≤ N + 1 / 256) (hN : 1 ≤ N)
    (hn : u * N ≤ 1 / 256) :
    fl (fl (σ * fk) + fl (qn * fl (κ * g))) ≤ 0 := by
  have hx0 : 0 ≤ σ * fk := mul_nonneg (by linarith) hfk0
  have hx1 : σ * fk ≤ 253 / 250 * (N + 1 / 256) := mul_le_mul hσ1 hfk1 hfk0 (by norm_num)
  have hP : fl (σ * fk) ≤ 6 / 5 * N := by
    have h := hr.upper hu0 (x := σ * fk) (B := 253 / 250 * (N + 1 / 256))
      (abs_le.mpr ⟨by linarith, hx1⟩)
    nlinarith [hn, hu1, hu0, hx1, hN, h]
  have hκg : κ * g ≤ 247 / 125 * g := mul_le_mul_of_nonpos_right hκ (by linarith)
  have hq1 : κ * g ≤ -(177 / 100) := by linarith
  have hQ : fl (κ * g) ≤ -(17 / 10) := by
    have h1 := hr.mono _ _ hq1
    have h2 := hr.upper hu0 (x := -(177 / 100 : ℝ)) (B := 177 / 100)
      (abs_le.mpr ⟨by linarith, by linarith⟩)
    linarith
  have hqn0 : 0 ≤ qn := by linarith
  have hxq : qn * fl (κ * g) ≤ qn * (-(17 / 10)) := mul_le_mul_of_nonneg_left hQ hqn0
  have hR : fl (qn * fl (κ * g)) ≤ -(17 / 10) * qn + u * (17 / 10 * qn) := by
    have h1 := hr.mono _ _ (show qn * fl (κ * g) ≤ -(17 / 10) * qn by linarith)
    have h2 := hr.upper hu0 (x := -(17 / 10) * qn) (B := 17 / 10 * qn)
      (abs_le.mpr ⟨by linarith, by linarith⟩)
    linarith
  have hu_qn : u * qn ≤ u * (N + 1 / 256) := mul_le_mul_of_nonneg_left hqn2 hu0
  have hsum : fl (σ * fk) + fl (qn * fl (κ * g)) ≤ 0 := by
    nlinarith [hP, hR, hqn1, hu_qn, hn, hu1, hN, hu0]
  have := hr.mono _ _ hsum
  rwa [hr.zero] at this

theorem mk_pos {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {σ fj : ℝ} (hσ : 247 / 250 ≤ σ) (hfj : 1 ≤ fj) :
    0 < fl (σ * fj) := by
  have hm := mul_le_mul hσ hfj (by norm_num) (by linarith)
  have hx : 247 / 250 ≤ σ * fj := by linarith
  have h1 := hr.mono _ _ hx
  have h2 := hr.lower hu0 (x := (247 / 250 : ℝ)) (B := 247 / 250)
    (abs_le.mpr ⟨by linarith, by linarith⟩)
  linarith

theorem mk_lt {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {σ fk fj N : ℝ} (hσ0 : 247 / 250 ≤ σ) (hσ1 : σ ≤ 253 / 250)
    (hfk0 : 0 ≤ fk) (hgap : fk + 127 / 128 ≤ fj) (hfj : fj ≤ N + 1 / 256) (hN : 1 ≤ N)
    (hn : u * N ≤ 1 / 256) : fl (σ * fk) < fl (σ * fj) := by
  have hxk0 : 0 ≤ σ * fk := mul_nonneg (by linarith) hfk0
  have hfj0 : 0 ≤ fj := by linarith
  have hxj0 : 0 ≤ σ * fj := mul_nonneg (by linarith) hfj0
  have hfk1 : fk ≤ N + 1 / 256 := by linarith
  have hxk1 : σ * fk ≤ 253 / 250 * (N + 1 / 256) := mul_le_mul hσ1 hfk1 hfk0 (by norm_num)
  have hxj1 : σ * fj ≤ 253 / 250 * (N + 1 / 256) := mul_le_mul hσ1 hfj hfj0 (by norm_num)
  apply hr.lt_of_gap hu0 (B := 253 / 250 * (N + 1 / 256))
  · exact abs_le.mpr ⟨by linarith, hxk1⟩
  · exact abs_le.mpr ⟨by linarith, hxj1⟩
  · have := mul_le_mul_of_nonneg_left hgap (show 0 ≤ σ by linarith)
    nlinarith [this, hn, hu0, hu1, hσ0]

/-! ### tokens, values, targets -/

theorem val_zero : val 0 = 0 := by simp [val]

theorem val_le (t : ℕ) : val t ≤ 3 := by
  unfold val
  split_ifs <;> omega

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem lastv_succ (w : List ℕ) (i : ℕ) (hi : i < w.length) :
    lastv (w.take (i + 1)) = if val w[i] = 0 then lastv (w.take i) else val w[i] := by
  rw [List.take_succ, List.getElem?_eq_getElem hi]
  by_cases h : val w[i] = 0 <;> simp [lastv, List.foldl_append, h]

theorem last_char (w : List ℕ) : ∀ i, i ≤ w.length →
    ((∀ j, j ≤ i → val (tokAt w j) = 0) ∧ lastv (w.take i) = 0) ∨
    (∃ j, 1 ≤ j ∧ j ≤ i ∧ val (tokAt w j) ≠ 0 ∧
      (∀ k, j < k → k ≤ i → val (tokAt w k) = 0) ∧ lastv (w.take i) = val (tokAt w j)) := by
  intro i
  induction i with
  | zero =>
    intro _
    left
    refine ⟨?_, by simp [lastv]⟩
    intro j hj
    have : j = 0 := by omega
    subst this
    rw [Lane4.Seq.tokAt_zero]
    exact val_zero
  | succ i ih =>
    intro hi
    have hi' : i < w.length := by omega
    have hsucc := lastv_succ w i hi'
    have htok : tokAt w (i + 1) = w[i] := Lane4.Seq.tokAt_succ w i hi'
    by_cases h : val (tokAt w (i + 1)) = 0
    · have hw0 : val w[i] = 0 := by rw [← htok]; exact h
      rw [if_pos hw0] at hsucc
      rcases ih (by omega) with ⟨hz, hl⟩ | ⟨j, hj1, hji, hjm, hlast, hl⟩
      · left
        refine ⟨?_, by rw [hsucc]; exact hl⟩
        intro j hj
        by_cases hj' : j = i + 1
        · subst hj'; exact h
        · exact hz j (by omega)
      · right
        refine ⟨j, hj1, by omega, hjm, ?_, by rw [hsucc]; exact hl⟩
        intro k hjk hki
        by_cases hk' : k = i + 1
        · subst hk'; exact h
        · exact hlast k hjk (by omega)
    · have hw0 : ¬ val w[i] = 0 := by rw [← htok]; exact h
      rw [if_neg hw0] at hsucc
      right
      refine ⟨i + 1, by omega, le_refl _, h, ?_, by rw [hsucc, htok]⟩
      intro k hk1 hk2
      omega

/-! ### the network's states -/

/-- The stored `val` entry at position `j`. -/
noncomputable def ev (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl ((val (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 0)

/-- The gate computed by block 1. -/
noncomputable def ug (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  fl (sw fl (-1) (p.W2 0 1 0) *
    relu (fl (fl (sw fl (-2) (p.W1 0 0 0) * ev fl p w j) + sw fl 1 (p.b1 0 0))))

/-- State after block 1. -/
noncomputable def x1 (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : Vec :=
  [ev fl p w j, ug fl p w j, 0, 1, fl (j : ℝ), fl ((w.length + 1 : ℕ) : ℝ)]

theorem fl_ev {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ) :
    fl (ev fl p w j) = ev fl p w j := by
  unfold ev
  exact fl_sw hr _ _

theorem ev_zero {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ)
    (h : val (tokAt w j) = 0) : ev fl p w j = 0 := by
  unfold ev
  rw [h, Nat.cast_zero]
  exact sw_zero hr _

theorem ev_ge {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ)
    (hj : val (tokAt w j) ≠ 0) : 247 / 250 ≤ ev fl p w j := by
  unfold ev
  have h := sw_pos hr hu0 hu1 ((val (tokAt w j) : ℕ) : ℚ)
    (Rat.cast_nonneg.mpr (Nat.cast_nonneg _)) (hp.E (tokAt w j) 0)
  have hv : (1 : ℝ) ≤ (val (tokAt w j) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
  rw [Rat.cast_natCast] at h
  linarith [h.1]

theorem init_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [ev fl p w j, 0, 0] ++ pos fl j (w.length + 1) := by
  have h6 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨
      tokAt w j = 4 ∨ tokAt w j = 5 := by
    have := tok_le w hw j
    omega
  rcases h6 with h | h | h | h | h | h <;>
    simp [TNet.init, net, ev, swRow, h, val, sw_zero hr]

theorem blk1_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (n j : ℕ) :
    blk1.apply fl p 0 n (net.init fl p w) j = x1 fl p w j := by
  simp only [Block.apply, blk1, headsApply, init_eq hr p w hw]
  simp [x1, ug, z6, pos, raffine, rdot, radd, sw_zero hr, hr.zero, hr.idem, hr.one,
    fl_sw hr, fl_ev hr]

theorem ug_marked {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ)
    (hj : val (tokAt w j) ≠ 0) : ug fl p w j = 0 := by
  have hev := ev_ge hr hu0 hu1 p hp w j hj
  have hk := sw_two_bnd hr hu0 hu1 (hp.W1 0 0 0)
  have hb := sw_one_bnd hr hu0 hu1 (hp.b1 0 0)
  have hprod : (247 / 125) * (247 / 250) ≤ sw fl 2 (p.W1 0 0 0) * ev fl p w j :=
    mul_le_mul hk.1 hev (by norm_num) (by linarith [hk.1])
  have hx : sw fl (-2) (p.W1 0 0 0) * ev fl p w j ≤ -(19 / 10) := by
    rw [sw_neg hr]
    nlinarith [hprod]
  have ha : fl (sw fl (-2) (p.W1 0 0 0) * ev fl p w j) ≤ -(9 / 5) := by
    have h1 := hr.mono _ _ hx
    have h2 := hr.upper hu0 (x := -(19 / 10 : ℝ)) (B := 19 / 10)
      (abs_le.mpr ⟨by linarith, by linarith⟩)
    linarith
  have hpre : fl (fl (sw fl (-2) (p.W1 0 0 0) * ev fl p w j) + sw fl 1 (p.b1 0 0)) ≤ 0 := by
    have := hr.mono _ _ (show fl (sw fl (-2) (p.W1 0 0 0) * ev fl p w j)
      + sw fl 1 (p.b1 0 0) ≤ 0 by linarith [hb.2])
    rwa [hr.zero] at this
  unfold ug
  rw [relu_of_nonpos hpre, mul_zero, hr.zero]

theorem ug_unmarked {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ)
    (hj : val (tokAt w j) = 0) :
    ug fl p w j = fl (sw fl (-1) (p.W2 0 1 0) * sw fl 1 (p.b1 0 0)) := by
  have hb := sw_one_bnd hr hu0 hu1 (hp.b1 0 0)
  have hb0 : 0 ≤ sw fl 1 (p.b1 0 0) := by linarith [hb.1]
  unfold ug
  rw [ev_zero hr p w j hj, mul_zero, hr.zero, zero_add, fl_sw hr, relu_of_nonneg hb0]

theorem ug_unm_le {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (k : ℕ)
    (hk : val (tokAt w k) = 0) : ug fl p w k ≤ -(9 / 10) := by
  rw [ug_unmarked hr hu0 hu1 p hp w k hk, sw_neg hr]
  have hω := sw_one_bnd hr hu0 hu1 (hp.W2 0 1 0)
  have hβ := sw_one_bnd hr hu0 hu1 (hp.b1 0 0)
  have hprod : (247 / 250) * (247 / 250) ≤ sw fl 1 (p.W2 0 1 0) * sw fl 1 (p.b1 0 0) :=
    mul_le_mul hω.1 hβ.1 (by norm_num) (by linarith [hω.1])
  have h1 := hr.mono _ _ (show -sw fl 1 (p.W2 0 1 0) * sw fl 1 (p.b1 0 0) ≤ -(97 / 100) by
    nlinarith [hprod])
  have h2 := hr.upper hu0 (x := -(97 / 100 : ℝ)) (B := 97 / 100)
    (abs_le.mpr ⟨by linarith, by linarith⟩)
  linarith

/-! ### the head -/

theorem score_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (a b c qi qn a' b' c' qk qn' : ℝ) :
    hh.score fl dA [a, b, c, 1, qi, qn] [a', b', c', 1, qk, qn']
      = fl (fl (sw fl 1 (dA 3 4) * qk) + fl (qn * fl (sw fl 2 (dA 5 1) * b'))) := by
  simp [Head.score, hh, z6, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem, hr.one]

theorem sel_B {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi : i ≤ w.length) (j : ℕ) (hj1 : 1 ≤ j) (hji : j ≤ i)
    (hjm : val (tokAt w j) ≠ 0) (hlast : ∀ k, j < k → k ≤ i → val (tokAt w k) = 0) :
    hh.sel fl (p.A 1 0) (w.length + 1) (x1 fl p w) i = [j] := by
  have hN1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    have : 1 ≤ w.length + 1 := by omega
    exact_mod_cast this
  have hqn := hr.pos_le hu0 (le_refl (w.length + 1)) hn
  have hqn' := abs_le.mp (hr.natCast_near (w.length + 1))
  have hσ := sw_one_bnd hr hu0 hu1 (hp.A 1 0 3 4)
  have hκ := sw_two_bnd hr hu0 hu1 (hp.A 1 0 5 1)
  have hfj1 : 1 ≤ fl (j : ℝ) := by
    have := hr.mono 1 (j : ℝ) (by exact_mod_cast hj1)
    rwa [hr.one] at this
  have hug_j := ug_marked hr hu0 hu1 p hp w j hjm
  apply Head.sel_unique
  · rw [show hh.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal]
    exact hji
  · intro k hk hne
    rw [show hh.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal] at hk
    have hkn : k ≤ w.length + 1 := by omega
    have hjn : j ≤ w.length + 1 := by omega
    have hkp := hr.pos_le hu0 hkn hn
    have hjp := hr.pos_le hu0 hjn hn
    simp only [x1]
    rw [score_eq hr, score_eq hr, hug_j]
    simp only [mul_zero, hr.zero, add_zero, hr.idem]
    by_cases hkm : val (tokAt w k) = 0
    · have hg := ug_unm_le hr hu0 hu1 p hp w k hkm
      refine lt_of_le_of_lt (unm_le hr hu0 hu1 hσ.1 hσ.2 hκ.1 hg ?_ ?_ hkp.1 hkp.2 hN1 hn)
        (mk_pos hr hu0 hu1 hσ.1 hfj1)
      · linarith [hqn'.1, hn]
      · exact hqn.2
    · have hkj : k < j := by
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · exact h
        · exact absurd (hlast k h hk) hkm
      have hgap := hr.pos_gap hu0 hkj hjn hn
      rw [ug_marked hr hu0 hu1 p hp w k hkm]
      simp only [mul_zero, hr.zero, add_zero, hr.idem]
      exact mk_lt hr hu0 hu1 hσ.1 hσ.2 hkp.1 hgap hjp.2 hN1 hn

theorem out_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) (S : List ℕ)
    (hsel : hh.sel fl (p.A 1 0) (w.length + 1) (x1 fl p w) i = S) :
    net.out fl p w i = fl (sw fl 1 (p.oW 2) * ravg fl S
      (fun j => fl (sw fl 1 (p.V 1 0 2 0) * ev fl p w j))) := by
  have hrun : net.run fl p w = blk2.apply fl p 1 (w.length + 1)
      (blk1.apply fl p 0 (w.length + 1) (net.init fl p w)) := rfl
  have hx1 : blk1.apply fl p 0 (w.length + 1) (net.init fl p w) = x1 fl p w :=
    funext (blk1_eq hr p w hw (w.length + 1))
  have ho : net.outW = [0, 0, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  have hV : hh.V = [z6, z6, [1, 0, 0, 0, 0, 0], z6, z6, z6] := rfl
  unfold TNet.out
  rw [hrun, hx1, ho, hc]
  simp only [Block.apply, blk2, headsApply, Head.attn, hsel, hV, attnRows]
  simp [x1, z6, rdot, radd, raffine, sw_zero hr, hr.zero, hr.idem, hr.one, fl_sw hr,
    fl_ev hr, fl_ravg hr, ravg_zero hr]

/-! ### final bound on the value read out -/

theorem final_bound {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {dO dV dE : ℝ} (hO : |dO| ≤ 1 / 200) (hV : |dV| ≤ 1 / 200)
    (hE : |dE| ≤ 1 / 200) (v : ℕ) (hv : v ≤ 3) :
    |fl (sw fl 1 dO * fl (sw fl 1 dV * sw fl (v : ℚ) dE)) - (v : ℝ)| ≤ 1 / 4 := by
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 3 / 250 := by linarith
  have hE' := sw_rel hr hu0 (v : ℚ) hE hε
  have hT := sw_rel hr hu0 1 hV hε
  have hO' := sw_rel hr hu0 1 hO hε
  have h1 := rel_fl hr hu0 (rel_mul hT hE' (c := 1 / 40) (by norm_num)) (c := 13 / 500)
    (by linarith)
  have h2 := rel_fl hr hu0 (rel_mul hO' h1 (c := 1 / 25) (by norm_num)) (c := 21 / 500)
    (by linarith)
  simp only [Rat.cast_one, Rat.cast_natCast, one_mul] at h2
  have htr : |(v : ℝ)| ≤ 3 := by
    rw [abs_of_nonneg (Nat.cast_nonneg v)]
    exact_mod_cast hv
  have := mul_le_mul_of_nonneg_left htr (show (0 : ℝ) ≤ 21 / 500 by norm_num)
  linarith

theorem net_ok : Statement net := by
  intro u fl hr hu0 hu1 p hp w hw hn i hi1 hi
  rcases last_char w i hi with ⟨hz, ht⟩ | ⟨j, hj1, hji, hjm, hlast, ht⟩
  · have hout := out_eq hr p w hw i _ rfl
    have hrav : ravg fl (hh.sel fl (p.A 1 0) (w.length + 1) (x1 fl p w) i)
        (fun j => fl (sw fl 1 (p.V 1 0 2 0) * ev fl p w j)) = 0 := by
      apply ravg_zero_on hr
      intro k hk
      have hk' := ((Head.mem_sel hh fl (p.A 1 0) (w.length + 1) (x1 fl p w) i k).mp hk).1
      rw [show hh.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal] at hk'
      show fl (sw fl 1 (p.V 1 0 2 0) * ev fl p w k) = 0
      rw [ev_zero hr p w k (hz k hk'), mul_zero, hr.zero]
    rw [hout, hrav]
    have htar : target w i = 0 := ht
    rw [htar]
    norm_num [hr.zero]
  · have hsel := sel_B hr hu0 hu1 p hp w hw hn i hi j hj1 hji hjm hlast
    rw [out_eq hr p w hw i [j] hsel]
    simp only [ravg_singleton hr, hr.idem]
    have htar : target w i = val (tokAt w j) := ht
    rw [htar]
    unfold ev
    exact final_bound hr hu0 hu1 (hp.oW 2) (hp.V 1 0 2 0) (hp.E (tokAt w j) 0)
      (val (tokAt w j)) (val_le _)

end Lane4.Case
