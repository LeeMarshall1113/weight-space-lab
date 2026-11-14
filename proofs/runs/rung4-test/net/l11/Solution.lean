namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

/-- Written value of the embedding's `val` slot and `unmarked` slot. -/
def vw (t : ℕ) : ℚ := if t = 2 ∨ t = 3 then 2 else if t = 4 then 3 else 0
def uw (t : ℕ) : ℚ := if t = 2 ∨ t = 3 ∨ t = 4 then 0 else 1

/-- State: [val, unmarked, res, 1, fl i, fl n] (width 6). -/
def z6 : List ℚ := [0, 0, 0, 0, 0, 0]

/-- Score of key j = S1 * (position of j) - 2 * n * (unmarked flag of j): marked keys (flag
exactly 0) beat every unmarked key and are ordered by position. -/
def hd : Head :=
  { A := [z6, z6, z6, [0, 0, 0, 0, 1, 0], z6, [0, -2, 0, 0, 0, 0]],
    V := [z6, z6, [1, 0, 0, 0, 0, 0], z6, z6, z6],
    mask := Mask.causal }

def blk : Block :=
  { heads := [hd], W1 := [], b1 := [], W2 := [[], [], [], [], [], []], b2 := z6 }

def net : TNet :=
  { embed := [[0, 1, 0], [0, 1, 0], [2, 0, 0], [2, 0, 0], [3, 0, 0], [0, 1, 0]],
    blocks := [blk],
    outW := [0, 0, 1, 0, 0, 0],
    outB := 0 }

noncomputable def ev (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (vw (tokAt w j)) (p.E (tokAt w j) 0)

noncomputable def eu (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (uw (tokAt w j)) (p.E (tokAt w j) 1)

theorem tok_le5 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem val_cases (t : ℕ) (ht : t ≤ 5) :
    (val t = 0 ∧ (t = 0 ∨ t = 1 ∨ t = 5)) ∨ (val t ≠ 0 ∧ (t = 2 ∨ t = 3 ∨ t = 4)) := by
  interval_cases t <;> simp [val]

theorem init_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [ev fl p w j, eu fl p w j, 0, 1, fl (j : ℝ),
      fl (((w.length + 1 : ℕ)) : ℝ)] := by
  have h6 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 ∨
      tokAt w j = 5 := by
    have := tok_le5 w hw j
    omega
  rcases h6 with h | h | h | h | h | h <;>
    simp [TNet.init, net, ev, eu, vw, uw, swRow, pos, h, sw_zero hr]

theorem ev_unmarked {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ)
    (h : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 5) : ev fl p w j = 0 := by
  have h0 : vw (tokAt w j) = 0 := by
    rcases h with h | h | h <;> simp [vw, h]
  unfold ev
  rw [h0]
  exact sw_zero hr _

theorem eu_marked {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ)
    (h : tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4) : eu fl p w j = 0 := by
  have h0 : uw (tokAt w j) = 0 := by
    rcases h with h | h | h <;> simp [uw, h]
  unfold eu
  rw [h0]
  exact sw_zero hr _

theorem eu_unmarked {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ)
    (h : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 5) :
    247 / 250 ≤ eu fl p w j ∧ eu fl p w j ≤ 253 / 250 := by
  have hu : uw (tokAt w j) = 1 := by
    rcases h with h | h | h <;> simp [uw, h]
  have h1 := sw_rel hr hu0 (uw (tokAt w j)) (hp.E (tokAt w j) 1) (ε := 3 / 250) (by linarith)
  rw [hu] at h1
  simp only [Rat.cast_one, abs_one, mul_one] at h1
  have h2 := abs_le.mp h1
  unfold eu
  rw [hu]
  constructor <;> linarith [h2.1, h2.2]

/-- The score in closed form. -/
theorem score_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (a b c qi qn a' b' c' qk qn' : ℝ) :
    hd.score fl dA [a, b, c, 1, qi, qn] [a', b', c', 1, qk, qn']
      = fl (fl (sw fl 1 (dA 3 4) * qk) + fl (qn * fl (sw fl (-2) (dA 5 1) * b'))) := by
  simp [Head.score, hd, z6, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem]

theorem score_marked {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i k : ℕ)
    (hk : tokAt w k = 2 ∨ tokAt w k = 3 ∨ tokAt w k = 4) :
    hd.score fl (p.A 0 0) (net.init fl p w i) (net.init fl p w k)
      = fl (sw fl 1 (p.A 0 0 3 4) * fl (k : ℝ)) := by
  rw [init_eq hr p w hw i, init_eq hr p w hw k, score_eq hr, eu_marked hr p w k hk]
  simp [hr.zero, hr.idem]

theorem score_unmarked {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i k : ℕ) :
    hd.score fl (p.A 0 0) (net.init fl p w i) (net.init fl p w k)
      = fl (fl (sw fl 1 (p.A 0 0 3 4) * fl (k : ℝ)) +
          fl (fl (((w.length + 1 : ℕ)) : ℝ) * fl (sw fl (-2) (p.A 0 0 5 1) * eu fl p w k))) := by
  rw [init_eq hr p w hw i, init_eq hr p w hw k, score_eq hr]

theorem unmarked_neg {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {N S1 S2 e q qn : ℝ} (hN : 2 ≤ N) (hun : u * N ≤ 1 / 256)
    (hS1l : 247 / 250 ≤ S1) (hS1u : S1 ≤ 253 / 250) (hS2l : -253 / 125 ≤ S2)
    (hS2u : S2 ≤ -247 / 125) (hel : 247 / 250 ≤ e) (heu : e ≤ 253 / 250) (hq0 : 0 ≤ q)
    (hq1 : q ≤ N) (hqnl : N - 1 / 256 ≤ qn) (hqnu : qn ≤ N + 1 / 256) :
    fl (fl (S1 * q) + fl (qn * fl (S2 * e))) < 0 := by
  have hqn0 : 0 ≤ qn := by linarith
  have ha0 : 0 ≤ S1 * q := mul_nonneg (by linarith) hq0
  have ha1 : S1 * q ≤ 253 / 250 * q := by
    nlinarith [mul_nonneg (sub_nonneg.2 hS1u) hq0]
  have haB : |S1 * q| ≤ 2 * N := by
    rw [abs_of_nonneg ha0]; linarith
  have hfa := hr.upper hu0 haB
  have hfa0 := hr.nonneg ha0
  have hx1 : S2 * e ≤ S2 * (247 / 250) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hel) (show 0 ≤ -S2 by linarith)]
  have hx2 : S2 * (253 / 250) ≤ S2 * e := by
    nlinarith [mul_nonneg (sub_nonneg.2 heu) (show 0 ≤ -S2 by linarith)]
  have hx5u : S2 * e ≤ -39 / 20 := by linarith
  have hx5l : -211 / 100 ≤ S2 * e := by linarith
  have hx5B : |S2 * e| ≤ 3 := by
    rw [abs_le]; constructor <;> linarith
  have hy1 := hr.upper hu0 hx5B
  have hy2 := hr.lower hu0 hx5B
  have hy3 : u * 3 ≤ 1 / 1000 := by linarith
  generalize hy : fl (S2 * e) = y at hy1 hy2 ⊢
  have hyu : y ≤ -19 / 10 := by linarith
  have hyl : -212 / 100 ≤ y := by linarith
  have hm1 : qn * y ≤ qn * (-19 / 10) := by
    nlinarith [mul_nonneg hqn0 (show 0 ≤ -19 / 10 - y by linarith)]
  have hm2 : qn * (-212 / 100) ≤ qn * y := by
    nlinarith [mul_nonneg hqn0 (show 0 ≤ y - (-212 / 100) by linarith)]
  have hmB : |qn * y| ≤ 3 * N := by
    rw [abs_le]; constructor <;> linarith
  have hfm1 := hr.upper hu0 hmB
  have hfm2 := hr.lower hu0 hmB
  have e1 : u * (2 * N) = 2 * (u * N) := by ring
  have e2 : u * (3 * N) = 3 * (u * N) := by ring
  have e3 : u * (4 * N) = 4 * (u * N) := by ring
  have hsB : |fl (S1 * q) + fl (qn * y)| ≤ 4 * N := by
    rw [abs_le]; constructor <;> linarith
  have hfs1 := hr.upper hu0 hsB
  linarith

theorem marked_pos {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    {N S1 q : ℝ} (hN : 2 ≤ N) (hun : u * N ≤ 1 / 256)
    (hS1l : 247 / 250 ≤ S1) (hS1u : S1 ≤ 253 / 250) (hql : 127 / 128 ≤ q) (hqu : q ≤ N) :
    0 < fl (S1 * q) := by
  have hq0 : 0 ≤ q := by linarith
  have h0 : 0 ≤ S1 * q := mul_nonneg (by linarith) hq0
  have hlow : 9 / 10 ≤ S1 * q := by
    nlinarith [mul_nonneg (sub_nonneg.2 hS1l) hq0]
  have hB : |S1 * q| ≤ 2 * N := by
    rw [abs_of_nonneg h0]
    nlinarith [mul_nonneg (sub_nonneg.2 hS1u) hq0]
  have h1 := hr.lower hu0 hB
  have e1 : u * (2 * N) = 2 * (u * N) := by ring
  linarith

theorem marked_gap {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    {N S1 q1 q2 : ℝ} (hN : 2 ≤ N) (hun : u * N ≤ 1 / 256)
    (hS1l : 247 / 250 ≤ S1) (hS1u : S1 ≤ 253 / 250) (hq1 : 0 ≤ q1)
    (hgap : q1 + 127 / 128 ≤ q2) (hq2 : q2 ≤ N) :
    fl (S1 * q1) < fl (S1 * q2) := by
  have hq2' : 0 ≤ q2 := by linarith
  have h1 : 0 ≤ S1 * q1 := mul_nonneg (by linarith) hq1
  have h2 : 0 ≤ S1 * q2 := mul_nonneg (by linarith) hq2'
  have hB1 : |S1 * q1| ≤ 2 * N := by
    rw [abs_of_nonneg h1]
    nlinarith [mul_nonneg (sub_nonneg.2 hS1u) hq1]
  have hB2 : |S1 * q2| ≤ 2 * N := by
    rw [abs_of_nonneg h2]
    nlinarith [mul_nonneg (sub_nonneg.2 hS1u) hq2']
  apply hr.lt_of_gap hu0 hB1 hB2
  have e1 : u * (2 * N) = 2 * (u * N) := by ring
  nlinarith [mul_nonneg (show 0 ≤ S1 by linarith) (show 0 ≤ q2 - q1 - 127 / 128 by linarith)]

theorem fl_ravg {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (S : List ℕ) (f : ℕ → ℝ) :
    fl (ravg fl S f) = ravg fl S f := by
  unfold ravg
  exact hr.idem _

theorem ravg_eq_zero {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (S : List ℕ) (f : ℕ → ℝ)
    (h : ∀ j ∈ S, f j = 0) : ravg fl S f = 0 := by
  have hs : rsum fl (S.map f) 0 = 0 :=
    rsum_zeros hr _ (by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      exact h j hj)
  unfold ravg
  rw [hs]
  simp [hr.zero]

set_option maxHeartbeats 1600000 in
theorem out_gen {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) (S : List ℕ)
    (hsel : hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = S) :
    net.out fl p w i
      = fl (sw fl 1 (p.oW 2) *
          ravg fl S (fun j => fl (sw fl 1 (p.V 0 0 2 0) * ev fl p w j))) := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 0, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  have hV : hd.V = [z6, z6, [1, 0, 0, 0, 0, 0], z6, z6, z6] := rfl
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [runFrom, Block.apply, blk, headsApply, Head.attn, hsel, hV, attnRows]
  simp only [init_eq hr p w hw]
  simp [ev, z6, pos, rdot, radd, raffine, sw_zero hr, hr.zero, hr.idem, hr.one, fl_sw hr,
    fl_ravg hr, ravg_zero hr]

theorem lastv_succ (w : List ℕ) (i : ℕ) (hi : i < w.length) :
    lastv (w.take (i + 1)) =
      if val (tokAt w (i + 1)) = 0 then lastv (w.take i) else val (tokAt w (i + 1)) := by
  rw [Lane4.Seq.tokAt_succ w i hi, List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [lastv, Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem sem (w : List ℕ) : ∀ i, i ≤ w.length →
    (lastv (w.take i) = 0 ∧ ∀ j, j ≤ i → val (tokAt w j) = 0) ∨
    (∃ j, 1 ≤ j ∧ j ≤ i ∧ val (tokAt w j) ≠ 0 ∧ lastv (w.take i) = val (tokAt w j) ∧
      ∀ k, j < k → k ≤ i → val (tokAt w k) = 0) := by
  intro i
  induction i with
  | zero =>
    intro _
    left
    refine ⟨by simp [lastv], ?_⟩
    intro j hj
    have : j = 0 := by omega
    subst this
    simp [Lane4.Seq.tokAt_zero, val]
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    have hl := lastv_succ w i (by omega)
    by_cases hv : val (tokAt w (i + 1)) = 0
    · rw [if_pos hv] at hl
      rcases ih' with ⟨h0, hall⟩ | ⟨j, hj1, hji, hjv, hjl, hrest⟩
      · left
        refine ⟨by rw [hl]; exact h0, ?_⟩
        intro j hj
        by_cases hji : j ≤ i
        · exact hall j hji
        · have : j = i + 1 := by omega
          subst this
          exact hv
      · right
        refine ⟨j, hj1, by omega, hjv, by rw [hl]; exact hjl, ?_⟩
        intro k hjk hki
        by_cases hk : k ≤ i
        · exact hrest k hjk hk
        · have : k = i + 1 := by omega
          subst this
          exact hv
    · rw [if_neg hv] at hl
      right
      refine ⟨i + 1, by omega, le_refl _, hv, hl, ?_⟩
      intro k hk hk2
      omega

theorem sel2 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) (j : ℕ) (hj1 : 1 ≤ j) (hji : j ≤ i)
    (hjm : tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4)
    (hrest : ∀ k, j < k → k ≤ i → val (tokAt w k) = 0) :
    hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = [j] := by
  have hNeq : (((w.length + 1 : ℕ)) : ℝ) = (w.length : ℝ) + 1 := by push_cast; ring
  have hL1 : (1 : ℝ) ≤ (w.length : ℝ) := by exact_mod_cast (le_trans hi1 hi)
  have hLn : u * (w.length : ℝ) ≤ 1 / 256 := by
    rw [hNeq] at hn
    nlinarith [hu0, hn]
  have hN2 : (2 : ℝ) ≤ (((w.length + 1 : ℕ)) : ℝ) := by rw [hNeq]; linarith
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 3 / 250 := by linarith
  have hS1 := sw_rel hr hu0 1 (hp.A 0 0 3 4) (ε := 3 / 250) hε
  simp only [Rat.cast_one, abs_one, mul_one] at hS1
  obtain ⟨hS1a, hS1b⟩ := abs_le.mp hS1
  have hS2 := sw_rel hr hu0 (-2) (hp.A 0 0 5 1) (ε := 3 / 250) hε
  have hc2 : (((-2 : ℚ)) : ℝ) = -2 := by norm_num
  have hc2' : |(-2 : ℝ)| = 2 := by norm_num
  rw [hc2, hc2'] at hS2
  obtain ⟨hS2a, hS2b⟩ := abs_le.mp hS2
  have hqn := abs_le.mp (hr.natCast_near (w.length + 1))
  have hqn' : u * (((w.length + 1 : ℕ)) : ℝ) ≤ 1 / 256 := hn
  have hqj := hr.pos_le hu0 (show j ≤ w.length by omega) hLn
  have hgj0 := hr.pos_gap hu0 (show 0 < j by omega) (show j ≤ w.length by omega) hLn
  have hgj : (127 / 128 : ℝ) ≤ fl (j : ℝ) := by simpa [hr.zero] using hgj0
  apply Head.sel_unique
  · rw [show hd.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal]
    exact hji
  · intro k hk hne
    rw [show hd.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal] at hk
    have hqk := hr.pos_le hu0 (show k ≤ w.length by omega) hLn
    rcases val_cases (tokAt w k) (tok_le5 w hw k) with ⟨_, hku⟩ | ⟨hkv, hkm⟩
    · -- unmarked key
      rw [score_unmarked hr p w hw i k, score_marked hr p w hw i j hjm]
      have heu := eu_unmarked hr hu0 hu1 p hp w k hku
      have h1 := unmarked_neg hr hu0 hu1 (N := (((w.length + 1 : ℕ)) : ℝ))
        (S1 := sw fl 1 (p.A 0 0 3 4)) (S2 := sw fl (-2) (p.A 0 0 5 1)) (e := eu fl p w k)
        (q := fl (k : ℝ)) (qn := fl (((w.length + 1 : ℕ)) : ℝ)) hN2 hn
        (by linarith) (by linarith) (by linarith) (by linarith) heu.1 heu.2 hqk.1
        (by rw [hNeq]; linarith [hqk.2]) (by linarith [hqn.1, hqn.2]) (by linarith [hqn.1, hqn.2])
      have h2 := marked_pos hr hu0 (N := (((w.length + 1 : ℕ)) : ℝ))
        (S1 := sw fl 1 (p.A 0 0 3 4)) (q := fl (j : ℝ)) hN2 hn
        (by linarith) (by linarith) hgj
        (by rw [hNeq]; linarith [hqj.2])
      linarith
    · -- marked key, earlier than j
      have hkj : k < j := by
        by_contra hcon
        have hlt : j < k := by omega
        exact hkv (hrest k hlt hk)
      rw [score_marked hr p w hw i k hkm, score_marked hr p w hw i j hjm]
      have hgap := hr.pos_gap hu0 hkj (show j ≤ w.length by omega) hLn
      exact marked_gap hr hu0 (N := (((w.length + 1 : ℕ)) : ℝ))
        (S1 := sw fl 1 (p.A 0 0 3 4)) hN2 hn (by linarith) (by linarith) hqk.1 hgap
        (by rw [hNeq]; linarith [hqj.2])

theorem chain_bound {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {a b x e : ℝ} (hx0 : 0 ≤ x) (hx3 : x ≤ 3)
    (ha : |a - 1| ≤ 3 / 250) (hb : |b - 1| ≤ 3 / 250) (he : |e - x| ≤ 3 / 250 * |x|) :
    |fl (b * fl (a * e)) - x| ≤ 1 / 4 := by
  have ha' : |a - 1| ≤ 3 / 250 * |(1 : ℝ)| := by simpa using ha
  have hb' : |b - 1| ≤ 3 / 250 * |(1 : ℝ)| := by simpa using hb
  have h1 := rel_fl hr hu0 (rel_mul ha' he (c := 1 / 40) (by norm_num)) (c := 13 / 500)
    (by linarith)
  have h2 := rel_fl hr hu0 (rel_mul hb' h1 (c := 1 / 25) (by norm_num)) (c := 21 / 500)
    (by linarith)
  simp only [one_mul] at h2
  rw [abs_of_nonneg hx0] at h2
  linarith

theorem net_ok : Statement net := by
  intro u fl hr hu0 hu1 p hp w hw hn i hi1 hi
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 3 / 250 := by linarith
  rcases sem w i hi with ⟨hl, hall⟩ | ⟨j, hj1, hji, hjv, hlast, hrest⟩
  · -- no marked token up to i
    obtain ⟨S, hS⟩ : ∃ S, hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = S :=
      ⟨_, rfl⟩
    have hR : ravg fl S (fun j => fl (sw fl 1 (p.V 0 0 2 0) * ev fl p w j)) = 0 := by
      apply ravg_eq_zero hr
      intro j hj
      have hj' : j ∈ hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i := by
        rw [hS]; exact hj
      have hmem := ((Head.mem_sel hd fl (p.A 0 0) (w.length + 1) (net.init fl p w) i j).1 hj').1
      rw [show hd.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal] at hmem
      have hv0 := hall j hmem
      rcases val_cases (tokAt w j) (tok_le5 w hw j) with ⟨_, hju⟩ | ⟨hne, _⟩
      · rw [ev_unmarked hr p w j hju, mul_zero, hr.zero]
      · exact absurd hv0 hne
    rw [out_gen hr p w hw i S hS, hR, mul_zero, hr.zero]
    have htg : target w i = 0 := by
      unfold target
      exact hl
    rw [htg]
    norm_num
  · -- last marked token at j
    have hjm : tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 := by
      rcases val_cases (tokAt w j) (tok_le5 w hw j) with ⟨h0, _⟩ | ⟨_, hm⟩
      · exact absurd h0 hjv
      · exact hm
    have hsel := sel2 hr hu0 hu1 p hp w hw hn i hi1 hi j hj1 hji hjm hrest
    rw [out_gen hr p w hw i [j] hsel]
    simp only [ravg_singleton hr, hr.idem]
    have htg : target w i = val (tokAt w j) := by
      unfold target
      exact hlast
    rw [htg]
    have hx : (((vw (tokAt w j) : ℚ)) : ℝ) = ((val (tokAt w j) : ℕ) : ℝ) := by
      rcases hjm with h | h | h <;> simp [vw, val, h]
    have hv3 : val (tokAt w j) ≤ 3 := by
      rcases hjm with h | h | h <;> simp [val, h]
    have hx3 : ((val (tokAt w j) : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hv3
    have hx0 : (0 : ℝ) ≤ ((val (tokAt w j) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hE := sw_rel hr hu0 (vw (tokAt w j)) (hp.E (tokAt w j) 0) (ε := 3 / 250) hε
    rw [hx] at hE
    have he : |ev fl p w j - ((val (tokAt w j) : ℕ) : ℝ)| ≤
        3 / 250 * |((val (tokAt w j) : ℕ) : ℝ)| := hE
    have hT := sw_rel hr hu0 1 (hp.V 0 0 2 0) (ε := 3 / 250) hε
    have hO := sw_rel hr hu0 1 (hp.oW 2) (ε := 3 / 250) hε
    simp only [Rat.cast_one, abs_one, mul_one] at hT hO
    exact chain_bound hr hu0 hu1 hx0 hx3 hT hO he

end Lane4.Case
