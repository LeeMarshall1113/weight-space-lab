namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

/-- State: [val, q, res, 1, fl i, fl n] (width 6). -/
def z6 : List ℚ := [0, 0, 0, 0, 0, 0]

/-- Score of key j: position of j, minus 4 * (fl n) * q_j, where q_j is exactly 0 for marked
tokens and about 1 for unmarked ones. Causal mask. Value: copy `val` into `res`. -/
def hd : Head :=
  { A := [z6, z6, z6, [0, 0, 0, 0, 1, 0], z6, [0, -4, 0, 0, 0, 0]],
    V := [z6, z6, [1, 0, 0, 0, 0, 0], z6, z6, z6],
    mask := Mask.causal }

def blk : Block :=
  { heads := [hd], W1 := [], b1 := [], W2 := [[], [], [], [], [], []], b2 := z6 }

def net : TNet :=
  { embed := [[0, 1, 0], [3, 0, 0], [1, 0, 0], [0, 1, 0], [1, 0, 0], [0, 1, 0]],
    blocks := [blk],
    outW := [0, 0, 1, 0, 0, 0],
    outB := 0 }

def qQ (t : ℕ) : ℚ := if val t = 0 then 1 else 0

noncomputable def ev (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl ((val (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 0)

noncomputable def eqq (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (qQ (tokAt w j)) (p.E (tokAt w j) 1)

theorem val_le3 (t : ℕ) : val t ≤ 3 := by
  unfold val
  split_ifs <;> omega

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [ev fl p w j, eqq fl p w j, 0] ++ pos fl j (w.length + 1) := by
  have h6 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 ∨
      tokAt w j = 5 := by
    have := tok_le w hw j
    omega
  rcases h6 with h | h | h | h | h | h <;>
    simp [TNet.init, net, ev, eqq, swRow, h, qQ, val, sw_zero hr]

theorem ev_zero {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ)
    (h : val (tokAt w j) = 0) : ev fl p w j = 0 := by
  simp [ev, h, sw_zero hr]

theorem eqq_marked {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ)
    (h : val (tokAt w j) ≠ 0) : eqq fl p w j = 0 := by
  simp [eqq, qQ, h, sw_zero hr]

theorem sw1_bounds {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (d : ℝ) (hdd : |d| ≤ 1 / 200) :
    49 / 50 ≤ sw fl 1 d ∧ sw fl 1 d ≤ 51 / 50 := by
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 3 / 250 := by linarith
  have h := sw_rel hr hu0 1 hdd hε
  simp only [Rat.cast_one, abs_one, mul_one] at h
  have := abs_le.mp h
  constructor <;> linarith

theorem swm4_bounds {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (d : ℝ) (hdd : |d| ≤ 1 / 200) :
    sw fl (-4) d ≤ -39 / 10 ∧ -41 / 10 ≤ sw fl (-4) d := by
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 3 / 250 := by linarith
  have h := sw_rel hr hu0 (-4) hdd hε
  have h5 : |(((-4 : ℚ)) : ℝ)| = 4 := by norm_num
  have h4 : (((-4 : ℚ)) : ℝ) = -4 := by norm_num
  rw [h5, h4] at h
  have := abs_le.mp h
  constructor <;> linarith

theorem eqq_unmarked {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ)
    (h : val (tokAt w j) = 0) : 49 / 50 ≤ eqq fl p w j ∧ eqq fl p w j ≤ 51 / 50 := by
  have hq : qQ (tokAt w j) = 1 := by simp [qQ, h]
  unfold eqq
  rw [hq]
  exact sw1_bounds hr hu0 hu1 _ (hp.E _ 1)

noncomputable def scr (fl : ℝ → ℝ) (sS sT pk qn b : ℝ) : ℝ :=
  fl (fl (sS * pk) + fl (qn * fl (sT * b)))

theorem score_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (a b c qi qn a' b' c' qk qn' : ℝ) :
    hd.score fl dA [a, b, c, 1, qi, qn] [a', b', c', 1, qk, qn']
      = scr fl (sw fl 1 (dA 3 4)) (sw fl (-4) (dA 5 1)) qk qn b' := by
  simp [Head.score, hd, z6, pdot, rmat, rdot, scr, sw_zero hr, hr.zero, hr.idem]

theorem scr_marked_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (sS sT pk qn : ℝ) :
    scr fl sS sT pk qn 0 = fl (sS * pk) := by
  simp [scr, hr.zero, hr.idem]

theorem mm_lt {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {sS pk pm N : ℝ} (hN2 : 2 ≤ N) (hn : u * N ≤ 1 / 256)
    (hS1 : 49 / 50 ≤ sS) (hS2 : sS ≤ 51 / 50)
    (hk0 : 0 ≤ pk) (hk1 : pk ≤ N + 1 / 256) (hgap : pk + 127 / 128 ≤ pm)
    (hm1 : pm ≤ N + 1 / 256) : fl (sS * pk) < fl (sS * pm) := by
  have hpm : 0 ≤ pm := by linarith
  have hs0 : 0 ≤ sS := by linarith
  have h1 : sS * pk ≤ 51 / 50 * (N + 1 / 256) := by
    nlinarith [mul_nonneg hk0 (sub_nonneg.2 hS2)]
  have h2 : sS * pm ≤ 51 / 50 * (N + 1 / 256) := by
    nlinarith [mul_nonneg hpm (sub_nonneg.2 hS2)]
  have ha : |sS * pk| ≤ 2 * (N + 1) := by
    rw [abs_of_nonneg (mul_nonneg hs0 hk0)]; linarith
  have hb : |sS * pm| ≤ 2 * (N + 1) := by
    rw [abs_of_nonneg (mul_nonneg hs0 hpm)]; linarith
  have h3 := mul_nonneg hs0 (show (0 : ℝ) ≤ pm - pk - 127 / 128 by linarith)
  have hg : sS * pk + 2 * (u * (2 * (N + 1))) < sS * pm := by nlinarith
  exact hr.lt_of_gap hu0 ha hb hg

theorem m_pos {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {sS pm N : ℝ} (hN2 : 2 ≤ N) (hn : u * N ≤ 1 / 256)
    (hS1 : 49 / 50 ≤ sS) (hS2 : sS ≤ 51 / 50)
    (hm0 : 127 / 128 ≤ pm) (hm1 : pm ≤ N + 1 / 256) : 0 < fl (sS * pm) := by
  have hpm : 0 ≤ pm := by linarith
  have hs0 : 0 ≤ sS := by linarith
  have h2 : sS * pm ≤ 51 / 50 * (N + 1 / 256) := by
    nlinarith [mul_nonneg hpm (sub_nonneg.2 hS2)]
  have hb : |sS * pm| ≤ 2 * (N + 1) := by
    rw [abs_of_nonneg (mul_nonneg hs0 hpm)]; linarith
  have h3 := mul_nonneg (sub_nonneg.2 hS1) hpm
  have hg : (0 : ℝ) + 2 * (u * (2 * (N + 1))) < sS * pm := by nlinarith
  have h := hr.lt_of_gap hu0 (a := 0) (b := sS * pm) (B := 2 * (N + 1))
    (by rw [abs_zero]; linarith) hb hg
  rwa [hr.zero] at h

theorem um_le0 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {sS sT pk qn b N : ℝ} (hN2 : 2 ≤ N) (hn : u * N ≤ 1 / 256)
    (hS1 : 49 / 50 ≤ sS) (hS2 : sS ≤ 51 / 50) (hT1 : sT ≤ -39 / 10) (hT2 : -41 / 10 ≤ sT)
    (hb1 : 49 / 50 ≤ b) (hb2 : b ≤ 51 / 50) (hk0 : 0 ≤ pk) (hk1 : pk ≤ N + 1 / 256)
    (hq1 : N - 1 / 256 ≤ qn) (hq2 : qn ≤ N + 1 / 256) : scr fl sS sT pk qn b ≤ 0 := by
  have hp1 : sT * b ≤ -38 / 10 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ -sT by linarith)
      (show (0 : ℝ) ≤ b - 49 / 50 by linarith)]
  have hp2 : -43 / 10 ≤ sT * b := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ sT + 41 / 10 by linarith)
      (show (0 : ℝ) ≤ b by linarith)]
  have hy1 : fl (sT * b) ≤ -37 / 10 := by
    have := hr.upper hu0 (x := sT * b) (B := 5) (abs_le.2 ⟨by linarith, by linarith⟩)
    linarith
  have hy2 : -5 ≤ fl (sT * b) := by
    have := hr.lower hu0 (x := sT * b) (B := 5) (abs_le.2 ⟨by linarith, by linarith⟩)
    linarith
  have hqn0 : 0 ≤ qn := by linarith
  unfold scr
  generalize fl (sT * b) = y at hy1 hy2 ⊢
  have hpy1 : qn * y ≤ -37 / 10 * qn := by
    nlinarith [mul_nonneg hqn0 (show (0 : ℝ) ≤ -37 / 10 - y by linarith)]
  have hpy2 : -5 * qn ≤ qn * y := by
    nlinarith [mul_nonneg hqn0 (show (0 : ℝ) ≤ y + 5 by linarith)]
  have habs : |qn * y| ≤ 5 * (N + 1 / 256) := abs_le.2 ⟨by linarith, by linarith⟩
  have hb' := hr.upper hu0 habs
  have hu5 : u * (5 * (N + 1 / 256)) ≤ 1 / 40 := by nlinarith
  have hsp : sS * pk ≤ 51 / 50 * (N + 1 / 256) := by
    nlinarith [mul_nonneg hk0 (sub_nonneg.2 hS2)]
  have hsp0 : 0 ≤ sS * pk := mul_nonneg (by linarith) hk0
  have ha' := hr.upper hu0 (x := sS * pk) (B := 51 / 50 * (N + 1 / 256))
    (by rw [abs_of_nonneg hsp0]; exact hsp)
  have hu6 : u * (51 / 50 * (N + 1 / 256)) ≤ 1 / 40 := by nlinarith
  have hsum : fl (sS * pk) + fl (qn * y) ≤ 0 := by linarith
  calc fl (fl (sS * pk) + fl (qn * y)) ≤ fl 0 := hr.mono _ _ hsum
    _ = 0 := hr.zero

/-- Position of the last marked token (if any) and the target. -/
theorem lastv_step (w : List ℕ) (j : ℕ) (hj : j < w.length) :
    lastv (w.take (j + 1))
      = if val (tokAt w (j + 1)) = 0 then lastv (w.take j) else val (tokAt w (j + 1)) := by
  have h1 : w.take (j + 1) = w.take j ++ [w[j]] := by
    first
      | exact List.take_succ_eq_append_getElem hj
      | (rw [List.take_succ]; simp [hj])
  rw [Lane4.Seq.tokAt_succ w j hj, h1]
  unfold lastv
  rw [List.foldl_append]
  simp

theorem last_char (w : List ℕ) : ∀ i, i ≤ w.length →
    (∃ m, 1 ≤ m ∧ m ≤ i ∧ val (tokAt w m) ≠ 0 ∧
        (∀ j, m < j → j ≤ i → val (tokAt w j) = 0) ∧
        lastv (w.take i) = val (tokAt w m)) ∨
    ((∀ j, 1 ≤ j → j ≤ i → val (tokAt w j) = 0) ∧ lastv (w.take i) = 0) := by
  intro i
  induction i with
  | zero =>
    intro _
    right
    refine ⟨fun j h1 h2 => by omega, ?_⟩
    simp [lastv]
  | succ k ih =>
    intro hk
    have hk' : k < w.length := by omega
    have ih' := ih (by omega)
    have hstep := lastv_step w k hk'
    by_cases hv : val (tokAt w (k + 1)) = 0
    · rw [if_pos hv] at hstep
      rcases ih' with ⟨m, hm1, hmk, hmv, hlast, hl⟩ | ⟨hall, hl⟩
      · left
        refine ⟨m, hm1, by omega, hmv, ?_, by rw [hstep, hl]⟩
        intro j hj1 hj2
        by_cases hjk : j = k + 1
        · subst hjk; exact hv
        · exact hlast j hj1 (by omega)
      · right
        refine ⟨?_, by rw [hstep, hl]⟩
        intro j hj1 hj2
        by_cases hjk : j = k + 1
        · subst hjk; exact hv
        · exact hall j hj1 (by omega)
    · rw [if_neg hv] at hstep
      left
      exact ⟨k + 1, by omega, le_refl _, hv, fun j hj1 hj2 => by omega, hstep⟩

/-- When a marked position exists, the head selects the last one. -/
theorem sel_A {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) (m : ℕ) (hm1 : 1 ≤ m) (hmi : m ≤ i)
    (hmv : val (tokAt w m) ≠ 0) (hlast : ∀ j, m < j → j ≤ i → val (tokAt w j) = 0) :
    hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = [m] := by
  apply Head.sel_unique
  · rw [show hd.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal]
    exact hmi
  · intro k hk hne
    rw [show hd.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal] at hk
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    rw [score_eq hr, score_eq hr]
    rw [eqq_marked hr p w m hmv, scr_marked_eq hr]
    have hN2 : (2 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
      have : 2 ≤ w.length + 1 := by omega
      exact_mod_cast this
    obtain ⟨hS1, hS2⟩ := sw1_bounds hr hu0 hu1 (p.A 0 0 3 4) (hp.A 0 0 3 4)
    obtain ⟨hT1, hT2⟩ := swm4_bounds hr hu0 hu1 (p.A 0 0 5 1) (hp.A 0 0 5 1)
    have hkp := hr.pos_le hu0 (show k ≤ w.length + 1 by omega) hn
    have hmp := hr.pos_le hu0 (show m ≤ w.length + 1 by omega) hn
    have hnn := abs_le.mp (hr.natCast_near (w.length + 1))
    have hq1 : ((w.length + 1 : ℕ) : ℝ) - 1 / 256 ≤ fl ((w.length + 1 : ℕ) : ℝ) := by
      linarith [hnn.1]
    have hq2 : fl ((w.length + 1 : ℕ) : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) + 1 / 256 := by
      linarith [hnn.2]
    have h0 : fl ((0 : ℕ) : ℝ) = 0 := by rw [Nat.cast_zero]; exact hr.zero
    have hm0 : (127 / 128 : ℝ) ≤ fl (m : ℝ) := by
      have := hr.pos_gap hu0 (show 0 < m by omega) (show m ≤ w.length + 1 by omega) hn
      linarith [this, h0]
    by_cases hkv : val (tokAt w k) = 0
    · have hq := eqq_unmarked hr hu0 hu1 p hp w k hkv
      refine lt_of_le_of_lt
        (um_le0 hr hu0 hu1 hN2 hn hS1 hS2 hT1 hT2 hq.1 hq.2 hkp.1 hkp.2 hq1 hq2) ?_
      exact m_pos hr hu0 hu1 hN2 hn hS1 hS2 hm0 hmp.2
    · rw [eqq_marked hr p w k hkv, scr_marked_eq hr]
      have hkm : k < m := by
        rcases Nat.lt_or_ge k m with h | h
        · exact h
        · exfalso
          have h' : m < k := by omega
          exact hkv (hlast k h' hk)
      have hg := hr.pos_gap hu0 hkm (show m ≤ w.length + 1 by omega) hn
      exact mm_lt hr hu0 hu1 hN2 hn hS1 hS2 hkp.1 hkp.2 hg hmp.2

theorem fl_ravg {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (S : List ℕ) (f : ℕ → ℝ) :
    fl (ravg fl S f) = ravg fl S f := by
  unfold ravg
  exact hr.idem _

theorem ravg_zero_on {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (S : List ℕ) (f : ℕ → ℝ)
    (h : ∀ j ∈ S, f j = 0) : ravg fl S f = 0 := by
  unfold ravg
  rw [rsum_zeros hr _ (by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    exact h j hj)]
  simp [hr.zero]

/-- The output in closed form, given the selected set. -/
theorem out_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) (S : List ℕ)
    (hsel : hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = S) :
    net.out fl p w i
      = fl (sw fl 1 (p.oW 2) * ravg fl S (fun j => fl (sw fl 1 (p.V 0 0 2 0) * ev fl p w j))) := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 0, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  have hV : hd.V = [z6, z6, [1, 0, 0, 0, 0, 0], z6, z6, z6] := rfl
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [runFrom, Block.apply, blk, headsApply, Head.attn, hsel, hV, attnRows]
  simp only [init_eq hr p w hw]
  simp [z6, pos, rdot, radd, raffine, sw_zero hr, hr.zero, hr.idem, hr.one, fl_sw hr,
    ravg_zero hr, fl_ravg hr]

theorem ev_close {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (m : ℕ) :
    |fl (sw fl 1 (p.oW 2) * fl (sw fl 1 (p.V 0 0 2 0) * ev fl p w m))
        - ((val (tokAt w m) : ℕ) : ℝ)| ≤ 21 / 500 * ((val (tokAt w m) : ℕ) : ℝ) := by
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 3 / 250 := by linarith
  have hE := sw_rel hr hu0 ((val (tokAt w m) : ℕ) : ℚ) (hp.E (tokAt w m) 0) hε
  have hT := sw_rel hr hu0 1 (hp.V 0 0 2 0) hε
  have hO := sw_rel hr hu0 1 (hp.oW 2) hε
  have h1 := rel_fl hr hu0 (rel_mul hT hE (c := 1 / 40) (by norm_num)) (c := 13 / 500)
    (by linarith)
  have h2 := rel_fl hr hu0 (rel_mul hO h1 (c := 1 / 25) (by norm_num)) (c := 21 / 500)
    (by linarith)
  simp only [Rat.cast_one, Rat.cast_natCast, one_mul] at h2
  have hv : |((val (tokAt w m) : ℕ) : ℝ)| = ((val (tokAt w m) : ℕ) : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  rw [hv] at h2
  exact h2

theorem net_ok : Statement net := by
  intro u fl hr hu0 hu1 p hp w hw hn i hi1 hi
  unfold target
  rcases last_char w i hi with ⟨m, hm1, hmi, hmv, hlast, hl⟩ | ⟨hall, hl⟩
  · have hsel := sel_A hr hu0 hu1 p hp w hw hn i hi1 hi m hm1 hmi hmv hlast
    rw [out_eq hr p w hw i [m] hsel, hl]
    simp only [ravg_singleton hr, hr.idem]
    have hv3 : ((val (tokAt w m) : ℕ) : ℝ) ≤ 3 := by exact_mod_cast val_le3 _
    exact le_trans (ev_close hr hu0 hu1 p hp w m) (by linarith)
  · have hS : ∀ j ∈ hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i,
        ev fl p w j = 0 := by
      intro j hj
      have hjc := ((Head.mem_sel hd fl (p.A 0 0) (w.length + 1) (net.init fl p w) i j).1 hj).1
      rw [show hd.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal] at hjc
      apply ev_zero hr
      by_cases hj0 : j = 0
      · subst hj0
        simp [Lane4.Seq.tokAt_zero, val]
      · exact hall j (by omega) hjc
    have hout := out_eq hr p w hw i _
      (rfl : hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = _)
    rw [hout, hl]
    have hR : ravg fl (hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i)
        (fun j => fl (sw fl 1 (p.V 0 0 2 0) * ev fl p w j)) = 0 :=
      ravg_zero_on hr _ _ (fun j hj => by simp [hS j hj, hr.zero])
    rw [hR]
    norm_num [hr.zero]

end Lane4.Case
