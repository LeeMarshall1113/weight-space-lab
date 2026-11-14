namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

def z6 : List ℚ := [0, 0, 0, 0, 0, 0]

def hd : Head :=
  { A := [z6, z6, z6, [0, 0, 0, 0, 1, 0], z6, [0, -2, 0, 0, 0, 0]],
    V := [z6, z6, [1, 0, 0, 0, 0, 0], z6, z6, z6],
    mask := Mask.strict }

def blk : Block :=
  { heads := [hd], W1 := [[0, 0, 1, 0, 0, 0]], b1 := [-2],
    W2 := [[0], [0], [-3], [0], [0], [0]], b2 := z6 }

def net : TNet :=
  { embed := [[0, 0, 0], [0, 1, 2], [0, 0, 0], [0, 0, 1], [0, 0, 1], [1, 0, 0]],
    blocks := [blk],
    outW := [0, 0, 1, 0, 0, 0],
    outB := 0 }

def gwn (t : ℕ) : ℕ := if t = 5 then 1 else 0
def pwn (t : ℕ) : ℕ := if t = 1 then 1 else 0

theorem dg_le (t : ℕ) : dg t ≤ 2 := by
  unfold dg; split_ifs <;> omega

theorem gwn_le (t : ℕ) : gwn t ≤ 1 := by
  unfold gwn; split_ifs <;> omega

/-- the last non-propagate position `≤ k` -/
def lm (w : List ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if tokAt w (k + 1) = 1 then lm w k else k + 1

theorem lm_le (w : List ℕ) : ∀ k, lm w k ≤ k := by
  intro k
  induction k with
  | zero => simp [lm]
  | succ k ih =>
    simp only [lm]
    split_ifs <;> omega

theorem lm_tok (w : List ℕ) : ∀ k, tokAt w (lm w k) ≠ 1 := by
  intro k
  induction k with
  | zero => simp [lm, Lane4.Seq.tokAt_zero]
  | succ k ih =>
    simp only [lm]
    split_ifs with h
    · exact ih
    · exact h

theorem lm_max (w : List ℕ) : ∀ k j, lm w k < j → j ≤ k → tokAt w j = 1 := by
  intro k
  induction k with
  | zero =>
    intro j h1 h2
    simp [lm] at h1
    omega
  | succ k ih =>
    intro j h1 h2
    simp only [lm] at h1
    split_ifs at h1 with h
    · by_cases hj : j = k + 1
      · subst hj; exact h
      · exact ih j h1 (by omega)
    · omega

theorem carry_lm (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) : ∀ k, k ≤ w.length →
    List.foldl (fun c t => if cls t = 2 then c else cls t) 0 (w.take k)
      = gwn (tokAt w (lm w k)) := by
  intro k
  induction k with
  | zero => intro _; simp [lm, Lane4.Seq.tokAt_zero, gwn]
  | succ k ih =>
    intro hk
    have hk' : k < w.length := by omega
    have ih' := ih (by omega)
    have htok : tokAt w (k + 1) = w[k] := Lane4.Seq.tokAt_succ w k hk'
    have ht := hw w[k] (List.getElem_mem hk')
    rw [List.take_succ, List.getElem?_eq_getElem hk']
    simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil, ih']
    simp only [lm]
    generalize w[k] = t at ht htok ⊢
    obtain ⟨ht1, ht5⟩ := ht
    interval_cases t <;> simp [cls, gwn, htok]

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j =
      [sw fl ((gwn (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 0),
       sw fl ((pwn (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 1),
       sw fl ((dg (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 2),
       1, fl (j : ℝ), fl (((w.length + 1 : ℕ)) : ℝ)] := by
  have h3 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨
      tokAt w j = 4 ∨ tokAt w j = 5 := by
    have := tok_le w hw j
    omega
  rcases h3 with h | h | h | h | h | h <;>
    simp [TNet.init, net, swRow, pos, gwn, pwn, dg, h, sw_zero hr]

theorem score_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (a0 a1 a2 b0 b1 b2 qi qn qk qn' : ℝ) :
    hd.score fl dA [a0, a1, a2, 1, qi, qn] [b0, b1, b2, 1, qk, qn']
      = fl (fl (sw fl 1 (dA 3 4) * qk) + fl (qn * fl (sw fl (-2) (dA 5 1) * b1))) := by
  simp [Head.score, hd, z6, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem, hr.one]

theorem cast_m2 : ((-2 : ℚ) : ℝ) = -2 := by norm_num
theorem cast_m2a : |((-2 : ℚ) : ℝ)| = 2 := by rw [cast_m2]; norm_num
theorem cast_m3 : ((-3 : ℚ) : ℝ) = -3 := by norm_num
theorem cast_m3a : |((-3 : ℚ) : ℝ)| = 3 := by rw [cast_m3]; norm_num

theorem flc {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {x B : ℝ} (hx : |x| ≤ B) (hB : B ≤ 16) : |fl x - x| ≤ 1 / 1000000 := by
  have h1 := hr.err hu0 hx
  have h2 : u * B ≤ (1 / 16777216) * 16 :=
    mul_le_mul hu1 hB (le_trans (abs_nonneg x) hx) (by norm_num)
  linarith

theorem sel_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = [lm w (i - 1)] := by
  have hmle := lm_le w (i - 1)
  have hmtok := lm_tok w (i - 1)
  apply Head.sel_unique
  · rw [show hd.mask = Mask.strict from rfl, Lane4.Seq.mem_cand_strict]
    omega
  · intro k hk hne
    rw [show hd.mask = Mask.strict from rfl, Lane4.Seq.mem_cand_strict] at hk
    simp only [init_eq hr p w hw]
    rw [score_eq hr, score_eq hr]
    have hn0 := hn
    obtain ⟨N, hN⟩ : ∃ N : ℝ, ((w.length + 1 : ℕ) : ℝ) = N := ⟨_, rfl⟩
    rw [hN] at hn
    rw [hN]
    have hN2 : (2 : ℝ) ≤ N := by
      rw [← hN]
      exact_mod_cast (by omega : 2 ≤ w.length + 1)
    have hnN := hr.natCast_near (w.length + 1)
    rw [hN] at hnN
    obtain ⟨hf1, hf2⟩ := abs_le.mp hnN
    have hfn0 : 0 ≤ fl N := by
      rw [← hN]; exact hr.nonneg (Nat.cast_nonneg _)
    have hS := sw_rel hr hu0 1 (hp.A 0 0 3 4) (ε := 3 / 500) (by linarith)
    simp only [Rat.cast_one, abs_one, mul_one] at hS
    obtain ⟨hS1, hS2⟩ := abs_le.mp hS
    set S := sw fl 1 (p.A 0 0 3 4) with hSdef
    have hS0 : 0 ≤ S := by linarith
    have hSle : S ≤ 1006 / 1000 := by linarith
    have hpm : pwn (tokAt w (lm w (i - 1))) = 0 := by simp [pwn, hmtok]
    have hm0 := hr.pos_le hu0 (show lm w (i - 1) ≤ w.length + 1 by omega) hn0
    rw [hN] at hm0
    have hSm0 : 0 ≤ S * fl ((lm w (i - 1) : ℕ) : ℝ) := mul_nonneg hS0 hm0.1
    have hSmB : S * fl ((lm w (i - 1) : ℕ) : ℝ) ≤ 2 * (N + 1 / 256) :=
      le_trans (mul_le_mul_of_nonneg_right hSle hm0.1) (by linarith [hm0.2])
    by_cases hk1 : tokAt w k = 1
    · have hp1 : pwn 1 = 1 := by simp [pwn]
      simp only [hk1, hp1, hpm, Nat.cast_zero, Nat.cast_one, sw_zero hr, mul_zero, hr.zero,
        add_zero, hr.idem]
      have hP := sw_rel hr hu0 1 (hp.E 1 1) (ε := 3 / 500) (by linarith)
      simp only [Rat.cast_one, abs_one, mul_one] at hP
      have ha2 := sw_rel hr hu0 (-2) (hp.A 0 0 5 1) (ε := 3 / 500) (by linarith)
      rw [cast_m2a, cast_m2] at ha2
      obtain ⟨hP1, hP2⟩ := abs_le.mp hP
      obtain ⟨ha1, ha2'⟩ := abs_le.mp ha2
      have hprod1 : sw fl (-2) (p.A 0 0 5 1) * sw fl 1 (p.E 1 1) ≤ -19 / 10 := by
        nlinarith [mul_nonneg
          (show 0 ≤ -(1988 / 1000) - sw fl (-2) (p.A 0 0 5 1) by linarith)
          (show 0 ≤ sw fl 1 (p.E 1 1) - 994 / 1000 by linarith)]
      have hprod2 : -21 / 10 ≤ sw fl (-2) (p.A 0 0 5 1) * sw fl 1 (p.E 1 1) := by
        nlinarith [mul_nonneg
          (show 0 ≤ -(sw fl (-2) (p.A 0 0 5 1)) by linarith)
          (show 0 ≤ 1006 / 1000 - sw fl 1 (p.E 1 1) by linarith)]
      have hQ := flc hr hu0 hu1
        (x := sw fl (-2) (p.A 0 0 5 1) * sw fl 1 (p.E 1 1)) (B := 3)
        (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)
      obtain ⟨hQ1, hQ2⟩ := abs_le.mp hQ
      have hQu : fl (sw fl (-2) (p.A 0 0 5 1) * sw fl 1 (p.E 1 1)) ≤ -189 / 100 := by linarith
      have hQl : -211 / 100 ≤ fl (sw fl (-2) (p.A 0 0 5 1) * sw fl 1 (p.E 1 1)) := by linarith
      have hX1 := mul_le_mul_of_nonneg_left hQu hfn0
      have hX2 := mul_le_mul_of_nonneg_left hQl hfn0
      have hT := hr.err hu0
        (x := fl N * fl (sw fl (-2) (p.A 0 0 5 1) * sw fl 1 (p.E 1 1))) (B := 3 * (N + 1 / 256))
        (abs_le.mpr ⟨by linarith, by linarith⟩)
      obtain ⟨hT1, hT2⟩ := abs_le.mp hT
      have hg := hr.pos_gap hu0 (show k < w.length + 1 by omega) (le_refl _) hn0
      rw [hN] at hg
      have hk0 : 0 ≤ fl (k : ℝ) := hr.nonneg (Nat.cast_nonneg k)
      have hS_k : S * fl (k : ℝ) ≤ 1006 / 1000 * fl (k : ℝ) :=
        mul_le_mul_of_nonneg_right hSle hk0
      have hSk0 : 0 ≤ S * fl (k : ℝ) := mul_nonneg hS0 hk0
      have hSkB : |S * fl (k : ℝ)| ≤ 2 * (N + 1 / 256) :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      have hM3 := hr.err hu0 hSkB
      obtain ⟨hM31, hM32⟩ := abs_le.mp hM3
      have hM30 : 0 ≤ fl (S * fl (k : ℝ)) := hr.nonneg hSk0
      apply hr.lt_of_gap hu0 (B := 8 * (N + 1))
      · exact abs_le.mpr ⟨by linarith, by linarith⟩
      · exact abs_le.mpr ⟨by linarith, by linarith⟩
      · linarith
    · have hlt : k < lm w (i - 1) := by
        by_contra hcon
        exact hk1 (lm_max w (i - 1) k (by omega) (by omega))
      have hpk : pwn (tokAt w k) = 0 := by simp [pwn, hk1]
      simp only [hpk, hpm, Nat.cast_zero, sw_zero hr, mul_zero, hr.zero, add_zero, hr.idem]
      have hg := hr.pos_gap hu0 hlt (show lm w (i - 1) ≤ w.length + 1 by omega) hn0
      have hk' := hr.pos_le hu0 (show k ≤ w.length + 1 by omega) hn0
      rw [hN] at hk'
      apply hr.lt_of_gap hu0 (B := 2 * (N + 1 / 256))
      · rw [abs_of_nonneg (mul_nonneg hS0 hk'.1)]
        exact mul_le_mul (by linarith) hk'.2 hk'.1 (by norm_num)
      · rw [abs_of_nonneg hSm0]
        exact hSmB
      · have h1 := mul_le_mul_of_nonneg_left hg hS0
        nlinarith [h1, hn, hu0, hu1, hS1]

/-- the tail of the network, after the head has written the sum `s` into slot 2 -/
noncomputable def tail (fl : ℝ → ℝ) (s eW eB eW2 eO : ℝ) : ℝ :=
  fl (sw fl 1 eO * fl (s + fl (sw fl (-3) eW2 *
    relu (fl (fl (sw fl 1 eW * s) + sw fl (-2) eB)))))

theorem out_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ)
    (hsel : hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = [lm w (i - 1)]) :
    net.out fl p w i
      = tail fl (fl (sw fl ((dg (tokAt w i) : ℕ) : ℚ) (p.E (tokAt w i) 2)
          + fl (sw fl 1 (p.V 0 0 2 0)
              * sw fl ((gwn (tokAt w (lm w (i - 1))) : ℕ) : ℚ) (p.E (tokAt w (lm w (i - 1))) 0))))
        (p.W1 0 0 2) (p.b1 0 0) (p.W2 0 2 0) (p.oW 2) := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 0, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  have hV : hd.V = [z6, z6, [1, 0, 0, 0, 0, 0], z6, z6, z6] := rfl
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [runFrom, Block.apply, blk, headsApply, Head.attn, hsel, hV, attnRows,
    ravg_singleton hr]
  simp only [init_eq hr p w hw]
  simp [tail, z6, pos, rdot, radd, raffine, sw_zero hr, hr.zero, hr.idem, hr.one, fl_sw hr]

theorem fin_step {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {z T eO : ℝ} (h4 : |eO| ≤ 1 / 200) (hz : |z - T| ≤ 21 / 100)
    (hT0 : 0 ≤ T) (hT2 : T ≤ 2) : |fl (sw fl 1 eO * z) - T| ≤ 1 / 4 := by
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 3 / 500 := by linarith
  have hO := sw_rel hr hu0 1 h4 hε
  simp only [Rat.cast_one, abs_one, mul_one] at hO
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  have hzabs : |z| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hs := near_scale (t := z) hO
  obtain ⟨hs1, hs2⟩ := abs_le.mp hs
  have hsz : |sw fl 1 eO * z| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hf := flc hr hu0 hu1 hsz (by norm_num)
  obtain ⟨hf1, hf2⟩ := abs_le.mp hf
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem core {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    (s : ℝ) (m : ℕ) (hm : m ≤ 3) (hs : |s - m| ≤ 27 / 1000) (hfs : fl s = s)
    {eW eB eW2 eO : ℝ} (h1 : |eW| ≤ 1 / 200) (h2 : |eB| ≤ 1 / 200) (h3 : |eW2| ≤ 1 / 200)
    (h4 : |eO| ≤ 1 / 200) :
    |tail fl s eW eB eW2 eO - ((m % 3 : ℕ) : ℝ)| ≤ 1 / 4 := by
  unfold tail
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 3 / 500 := by linarith
  have hA := sw_rel hr hu0 1 h1 hε
  simp only [Rat.cast_one, abs_one, mul_one] at hA
  have hB := sw_rel hr hu0 (-2) h2 hε
  rw [cast_m2a, cast_m2] at hB
  have hC := sw_rel hr hu0 (-3) h3 hε
  rw [cast_m3a, cast_m3] at hC
  have hmR : (m : ℝ) ≤ 3 := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  obtain ⟨hs1, hs2⟩ := abs_le.mp hs
  have hsabs : |s| ≤ 31 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hT := near_scale (t := s) hA
  obtain ⟨hT1, hT2⟩ := abs_le.mp hT
  have hts : |sw fl 1 eW * s| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hu1' := flc hr hu0 hu1 hts (by norm_num)
  obtain ⟨hu11, hu12⟩ := abs_le.mp hu1'
  obtain ⟨hB1, hB2⟩ := abs_le.mp hB
  have hsum : |fl (sw fl 1 eW * s) + sw fl (-2) eB| ≤ 8 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hpb' := flc hr hu0 hu1 hsum (by norm_num)
  obtain ⟨hpb1, hpb2⟩ := abs_le.mp hpb'
  set pb := fl (fl (sw fl 1 eW * s) + sw fl (-2) eB) with hpbdef
  have hpb : |pb - (s - 2)| ≤ 31 / 1000 := abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨hpbL, hpbU⟩ := abs_le.mp hpb
  have hb0 : 0 ≤ relu pb := le_max_right _ _
  have hbU : relu pb ≤ 11 / 10 := max_le (by linarith) (by norm_num)
  have hC' : |sw fl (-3) eW2 + 3| ≤ 9 / 500 := by
    have := hC
    rw [sub_neg_eq_add] at this
    linarith
  have hXb : |sw fl (-3) eW2 * relu pb + 3 * relu pb| ≤ 9 / 500 * relu pb := by
    have : sw fl (-3) eW2 * relu pb + 3 * relu pb = (sw fl (-3) eW2 + 3) * relu pb := by ring
    rw [this, abs_mul, abs_of_nonneg hb0]
    exact mul_le_mul_of_nonneg_right hC' hb0
  obtain ⟨hX1, hX2⟩ := abs_le.mp hXb
  have hxabs : |sw fl (-3) eW2 * relu pb| ≤ 16 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hx1 := flc hr hu0 hu1 hxabs (by norm_num)
  obtain ⟨hx11, hx12⟩ := abs_le.mp hx1
  set x1 := fl (sw fl (-3) eW2 * relu pb) with hx1def
  have hzs : |s + x1| ≤ 16 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hz' := flc hr hu0 hu1 hzs (by norm_num)
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz'
  set z := fl (s + x1) with hzdef
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl | rfl
  · push_cast at hs1 hs2
    have hT0 : (((0 % 3 : ℕ)) : ℝ) = 0 := by norm_num
    rw [hT0]
    have hb : relu pb = 0 := relu_of_nonpos (by linarith)
    exact fin_step hr hu0 hu1 h4 (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)
      (by norm_num)
  · push_cast at hs1 hs2
    have hT0 : (((1 % 3 : ℕ)) : ℝ) = 1 := by norm_num
    rw [hT0]
    have hb : relu pb = 0 := relu_of_nonpos (by linarith)
    exact fin_step hr hu0 hu1 h4 (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)
      (by norm_num)
  · push_cast at hs1 hs2
    have hT0 : (((2 % 3 : ℕ)) : ℝ) = 2 := by norm_num
    rw [hT0]
    have hbU2 : relu pb ≤ 58 / 1000 := max_le (by linarith) (by norm_num)
    exact fin_step hr hu0 hu1 h4 (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)
      (by norm_num)
  · push_cast at hs1 hs2
    have hT0 : (((3 % 3 : ℕ)) : ℝ) = 0 := by norm_num
    rw [hT0]
    have hb : relu pb = pb := relu_of_nonneg (by linarith)
    exact fin_step hr hu0 hu1 h4 (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)
      (by norm_num)

theorem s_bound {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (d0 g0 : ℕ) (hd : d0 ≤ 2) (hg : g0 ≤ 1) {e1 e2 e3 : ℝ}
    (h1 : |e1| ≤ 1 / 200) (h2 : |e2| ≤ 1 / 200) (h3 : |e3| ≤ 1 / 200) :
    |fl (sw fl (d0 : ℚ) e1 + fl (sw fl 1 e3 * sw fl (g0 : ℚ) e2)) - ((d0 + g0 : ℕ) : ℝ)|
      ≤ 27 / 1000 := by
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 3 / 500 := by linarith
  have hD := sw_rel hr hu0 (d0 : ℚ) h1 hε
  have hG := sw_rel hr hu0 (g0 : ℚ) h2 hε
  have hV := sw_rel hr hu0 1 h3 hε
  simp only [Rat.cast_one, abs_one, mul_one] at hV
  rw [Rat.cast_natCast, abs_of_nonneg (Nat.cast_nonneg d0)] at hD
  rw [Rat.cast_natCast, abs_of_nonneg (Nat.cast_nonneg g0)] at hG
  have hd' : (d0 : ℝ) ≤ 2 := by exact_mod_cast hd
  have hg' : (g0 : ℝ) ≤ 1 := by exact_mod_cast hg
  have hd0 : (0 : ℝ) ≤ d0 := Nat.cast_nonneg d0
  have hg0 : (0 : ℝ) ≤ g0 := Nat.cast_nonneg g0
  obtain ⟨hD1, hD2⟩ := abs_le.mp hD
  obtain ⟨hG1, hG2⟩ := abs_le.mp hG
  obtain ⟨hV1, hV2⟩ := abs_le.mp hV
  have hGabs : |sw fl (g0 : ℚ) e2| ≤ 11 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hT := near_scale (t := sw fl (g0 : ℚ) e2) hV
  obtain ⟨hT1, hT2⟩ := abs_le.mp hT
  have hc0 : |sw fl 1 e3 * sw fl (g0 : ℚ) e2| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hcv := flc hr hu0 hu1 hc0 (by norm_num)
  obtain ⟨hcv1, hcv2⟩ := abs_le.mp hcv
  have hsum : |sw fl (d0 : ℚ) e1 + fl (sw fl 1 e3 * sw fl (g0 : ℚ) e2)| ≤ 5 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hs := flc hr hu0 hu1 hsum (by norm_num)
  obtain ⟨hs1, hs2⟩ := abs_le.mp hs
  rw [abs_le]
  push_cast
  constructor <;> linarith

theorem net_ok : Statement net := by
  intro u fl hr hu0 hu1 p hp w hw hn i hi1 hi
  have hsel := sel_eq hr hu0 hu1 p hp w hw hn i hi1 hi
  rw [out_eq hr p w hw i hsel]
  have hd2 : dg (tokAt w i) ≤ 2 := dg_le _
  have hg1 : gwn (tokAt w (lm w (i - 1))) ≤ 1 := gwn_le _
  have hs := s_bound hr hu0 hu1 (dg (tokAt w i)) (gwn (tokAt w (lm w (i - 1)))) hd2 hg1
    (hp.E (tokAt w i) 2) (hp.E (tokAt w (lm w (i - 1))) 0) (hp.V 0 0 2 0)
  have hc := core hr hu0 hu1 _ (dg (tokAt w i) + gwn (tokAt w (lm w (i - 1)))) (by omega) hs
    (hr.idem _) (hp.W1 0 0 2) (hp.b1 0 0) (hp.W2 0 2 0) (hp.oW 2)
  have htar : target w i = (dg (tokAt w i) + gwn (tokAt w (lm w (i - 1)))) % 3 := by
    unfold target
    have h1 : w.getD (i - 1) 0 = tokAt w i := by
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      simp [tokAt]
    rw [h1]
    have := carry_lm w hw (i - 1) (by omega)
    unfold carry
    rw [this]
  rw [htar]
  exact hc

end Lane4.Case
