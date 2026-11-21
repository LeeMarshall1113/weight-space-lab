namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-! ### The network -/

def z4 : List ℚ := [0, 0, 0, 0]

def head1 : AHead :=
  { A := [z4, z4, z4, z4], V := [z4, z4, z4, [1/8, 0, 0, 0]], mask := Mask.strict, m := 24,
    g := [-1, 0, 0, 0], gb := 1/2 }

def blk1 : ABlock :=
  { heads := [head1], W1 := [], b1 := [], W2 := [[], [], [], []], b2 := z4 }

def head2 : AHead :=
  { A := [z4, z4, z4, z4], V := [z4, z4, [0, 1, 0, 0], z4], mask := Mask.causal, m := 24,
    g := [-1, 0, 0, 8], gb := 1/2 }

def blk2 : ABlock :=
  { heads := [head2], W1 := [[0, 0, 1, 0]], b1 := [-1], W2 := [[0], [0], [-2], [0]], b2 := z4 }

def net : ANet :=
  { embed := [[0, 0, 0, 0], [1, 0, 0, 0], [1, 1, 1, 0], [0, 0, 1, 0], [0, 0, 0, 0]],
    blocks := [blk1, blk2], outW := [0, 0, 1, 0], outB := 0 }

def mkq (t : ℕ) : ℚ := if t = 1 ∨ t = 2 then 1 else 0
def aq (t : ℕ) : ℚ := if t = 2 then 1 else 0
def cq (t : ℕ) : ℚ := if t = 2 ∨ t = 3 then 1 else 0

theorem embed_row {t : ℕ} (h : t ≤ 4) : net.embed.getD t [] = [mkq t, aq t, cq t, 0] := by
  interval_cases t <;> first | rfl | simp [net, mkq, aq, cq]

theorem mkq_01 (t : ℕ) : mkq t = 0 ∨ mkq t = 1 := by
  unfold mkq; split_ifs <;> simp
theorem aq_01 (t : ℕ) : aq t = 0 ∨ aq t = 1 := by
  unfold aq; split_ifs <;> simp
theorem cq_01 (t : ℕ) : cq t = 0 ∨ cq t = 1 := by
  unfold cq; split_ifs <;> simp

theorem mkq_iff {t : ℕ} (h : t ≤ 4) : mkq t = 1 ↔ code t ≠ 0 := by
  interval_cases t <;> simp [mkq, code]
theorem mkq_iff0 {t : ℕ} (h : t ≤ 4) : mkq t = 0 ↔ code t = 0 := by
  interval_cases t <;> simp [mkq, code]
theorem aq_iff {t : ℕ} (h : t ≤ 4) : aq t = 1 ↔ code t = 2 := by
  interval_cases t <;> simp [aq, code]
theorem cq_eq {t : ℕ} (h : t ≤ 4) : cq t = (cbit t : ℚ) := by
  interval_cases t <;> simp [cq, cbit]

/-! ### Context -/

structure Ctx (u η M : ℝ) (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) : Prop where
  hr : Rnd u η M fl
  he : ExpM u η ex
  hu0 : 0 ≤ u
  hu1 : u ≤ 1 / 2 ^ 24
  hη0 : 0 ≤ η
  hη1 : η ≤ 1 / 2 ^ 149
  hp : p.Within (1 / 1000)
  hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4
  hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256
  hnη : η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100
  hM : 2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M

section Steps

variable {u η M : ℝ} {fl ex : ℝ → ℝ} {p : APert} {w : List ℕ}

theorem Ctx.range (ev : Ctx u η M fl ex p w) (c : ℝ) (hc : c ≤ 2 ^ 40) : c ≤ M :=
  range_const ev.hM (by omega) hc

theorem Ctx.rangeN (ev : Ctx u η M fl ex p w) (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 2 ^ 40) :
    c * ((w.length + 1 : ℕ) : ℝ) ≤ M :=
  range_lin ev.hM (by omega) hc0 hc

theorem u_mul (ev : Ctx u η M fl ex p w) (c : ℝ) (hc : 0 ≤ c) :
    u * (c * ((w.length + 1 : ℕ) : ℝ)) ≤ c / 256 := by
  have h : u * (c * ((w.length + 1 : ℕ) : ℝ)) = c * (u * ((w.length + 1 : ℕ) : ℝ)) := by ring
  rw [h]
  have := mul_le_mul_of_nonneg_left ev.hn hc
  linarith

theorem Ctx.u7 (ev : Ctx u η M fl ex p w) : u ≤ 1 / 10000000 := by
  have h := ev.hu1
  have : (1 : ℝ) / 2 ^ 24 ≤ 1 / 10000000 := by norm_num
  linarith

theorem Ctx.η9 (ev : Ctx u η M fl ex p w) : η ≤ 1 / 1000000000 := by
  have h := eta_tiny ev.hη1
  have : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000000000 := by norm_num
  linarith

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) : tokAt w j ≤ 4 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem asw_c (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149)
    (hM : 4 ≤ M) (a : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 1000) (ha : |(a : ℝ)| ≤ 2) :
    |asw fl a d - (a : ℝ)| ≤ 1 / 500 := by
  have h := asw_near hr hu0 a hd (by linarith)
  have h1 : u * (|(a : ℝ)| + 1 / 1000) ≤ 1 / 2 ^ 24 * 3 :=
    mul_le_mul hu (by linarith) (by positivity) (by positivity)
  have h2 := eta_tiny hη
  have h3 : (1 : ℝ) / 2 ^ 24 * 3 + 1 / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

theorem close4 {a b c d a' b' c' d' e X : ℝ} (ha : |a - a'| ≤ e) (hb : |b - b'| ≤ e)
    (hc : |c - c'| ≤ e) (hd : |d - d'| ≤ e) (ha' : |a'| ≤ X) (hb' : |b'| ≤ X)
    (hc' : |c'| ≤ X) (hd' : |d'| ≤ X) :
    Close [a, b, c, d] [a', b', c', d'] e X := by
  refine ⟨rfl, ?_⟩
  intro k hk
  have hk4 : k < 4 := by simpa using hk
  interval_cases k
  · first | exact ⟨ha, ha'⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨ha, ha'⟩)
  · first | exact ⟨hb, hb'⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨hb, hb'⟩)
  · first | exact ⟨hc, hc'⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨hc, hc'⟩)
  · first | exact ⟨hd, hd'⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨hd, hd'⟩)

theorem ardotL (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 2 ^ 149) (hM : (2 : ℝ) ^ 30 ≤ M) (r : List ℚ) (x xh : List ℝ)
    (hl : r.length = x.length) (hl4 : r.length ≤ 4)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 8) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1 / 4)
    (hC : Close x xh e 1) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r x d 0 0 - dotQ r xh| ≤ absSum r * e + (r.length : ℝ) * (1 / 600) + 1 / 1000000000 := by
  have h20 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
  have key := ardot_near_abs u η M (1 / 1000) fl hr hu0 hu hη0 hη (by norm_num) (by norm_num)
    r x xh d 8 1 e hl (by omega) hC hd hW (by norm_num) (by norm_num) he0
    (by rw [h20]; linarith) hM
  have h16 : (2 : ℝ) ^ 16 = 65536 := by norm_num
  have h100 : (1 : ℝ) / 2 ^ 100 ≤ 1 / 1000000000 := by norm_num
  have hL0 : (0 : ℝ) ≤ (r.length : ℝ) := Nat.cast_nonneg _
  have hp := mul_nonneg hL0 (sub_nonneg.mpr he1)
  rw [h16] at key
  nlinarith [key, hp, h100]


theorem ardotL2 (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 2 ^ 149) (hM : (2 : ℝ) ^ 30 ≤ M) (r : List ℚ) (x xh : List ℝ)
    (hl : r.length = x.length) (hl4 : r.length ≤ 4)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 8) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1 / 4)
    (hC : Close x xh e 2) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r x d 0 0 - dotQ r xh| ≤ absSum r * e + (r.length : ℝ) * (1 / 300) + 1 / 1000000000 := by
  have h20 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
  have key := ardot_near_abs u η M (1 / 1000) fl hr hu0 hu hη0 hη (by norm_num) (by norm_num)
    r x xh d 8 2 e hl (by omega) hC hd hW (by norm_num) (by norm_num) he0
    (by rw [h20]; linarith) hM
  have h16 : (2 : ℝ) ^ 16 = 65536 := by norm_num
  have h100 : (1 : ℝ) / 2 ^ 100 ≤ 1 / 1000000000 := by norm_num
  have hL0 : (0 : ℝ) ≤ (r.length : ℝ) := Nat.cast_nonneg _
  have hp := mul_nonneg hL0 (sub_nonneg.mpr he1)
  rw [h16] at key
  nlinarith [key, hp, h100]

theorem close1 {a a' e X : ℝ} (ha : |a - a'| ≤ e) (ha' : |a'| ≤ X) : Close [a] [a'] e X := by
  refine ⟨rfl, ?_⟩
  intro k hk
  have hk1 : k < 1 := by simpa using hk
  interval_cases k
  first | exact ⟨ha, ha'⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨ha, ha'⟩)

end Steps

/-! ### Ideal values -/

noncomputable def mR (w : List ℕ) (j : ℕ) : ℝ := ((mkq (tokAt w j) : ℚ) : ℝ)
noncomputable def aR (w : List ℕ) (j : ℕ) : ℝ := ((aq (tokAt w j) : ℚ) : ℝ)
noncomputable def cR (w : List ℕ) (j : ℕ) : ℝ := ((cq (tokAt w j) : ℚ) : ℝ)

def mkd (w : List ℕ) (j : ℕ) : Prop := code (tokAt w j) ≠ 0
def HB (w : List ℕ) (i : ℕ) : Prop := ∃ k, k < i ∧ mkd w k

open Classical in
noncomputable def fv (w : List ℕ) (i : ℕ) : ℝ := if HB w i then (1 / 8 : ℝ) else 0

noncomputable def xh0 (w : List ℕ) (j : ℕ) : List ℝ := [mR w j, aR w j, cR w j, 0]

theorem fv_pos {w : List ℕ} {i : ℕ} (h : HB w i) : fv w i = 1 / 8 := by
  unfold fv; exact if_pos h
theorem fv_neg {w : List ℕ} {i : ℕ} (h : ¬ HB w i) : fv w i = 0 := by
  unfold fv; exact if_neg h
theorem fv_abs (w : List ℕ) (i : ℕ) : |fv w i| ≤ 1 := by
  by_cases h : HB w i
  · rw [fv_pos h]; norm_num
  · rw [fv_neg h]; norm_num

theorem q01_abs {q : ℚ} (h : q = 0 ∨ q = 1) : |(q : ℝ)| ≤ 1 := by
  rcases h with h | h <;> simp [h]

theorem mR_abs (w : List ℕ) (j : ℕ) : |mR w j| ≤ 1 := q01_abs (mkq_01 _)
theorem aR_abs (w : List ℕ) (j : ℕ) : |aR w j| ≤ 1 := q01_abs (aq_01 _)
theorem cR_abs (w : List ℕ) (j : ℕ) : |cR w j| ≤ 1 := q01_abs (cq_01 _)

section Steps2

variable {u η M : ℝ} {fl ex : ℝ → ℝ} {p : APert} {w : List ℕ}

theorem mR_one (ev : Ctx u η M fl ex p w) {j : ℕ} (h : mkd w j) : mR w j = 1 := by
  have h' := (mkq_iff (tok_le w ev.hw j)).mpr h
  unfold mR
  simp [h']

theorem mR_zero (ev : Ctx u η M fl ex p w) {j : ℕ} (h : ¬ mkd w j) : mR w j = 0 := by
  have h0 : code (tokAt w j) = 0 := by unfold mkd at h; exact not_not.mp h
  have h' := (mkq_iff0 (tok_le w ev.hw j)).mpr h0
  unfold mR
  simp [h']

theorem aR_two (ev : Ctx u η M fl ex p w) {j : ℕ} (h : code (tokAt w j) = 2) : aR w j = 1 := by
  have h' := (aq_iff (tok_le w ev.hw j)).mpr h
  unfold aR
  simp [h']

theorem aR_not_two (ev : Ctx u η M fl ex p w) {j : ℕ} (h : ¬ code (tokAt w j) = 2) :
    aR w j = 0 := by
  unfold aR
  rcases aq_01 (tokAt w j) with h0 | h0
  · simp [h0]
  · exact absurd ((aq_iff (tok_le w ev.hw j)).mp h0) h

/-! ### Step 0: the starting state -/

theorem init_eq (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (j : ℕ) (h : tokAt w j ≤ 4) :
    net.init fl p w j = [asw fl (mkq (tokAt w j)) (p.E (tokAt w j) 0),
      asw fl (aq (tokAt w j)) (p.E (tokAt w j) 1), asw fl (cq (tokAt w j)) (p.E (tokAt w j) 2),
      asw fl 0 (p.E (tokAt w j) 3)] := by
  show aswRow fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0 = _
  rw [embed_row h]
  rfl

theorem init_ent (ev : Ctx u η M fl ex p w) (j : ℕ) :
    ∃ a b c d : ℝ, net.init fl p w j = [a, b, c, d] ∧
      |a - mR w j| ≤ 1 / 500 ∧ |b - aR w j| ≤ 1 / 500 ∧ |c - cR w j| ≤ 1 / 500 ∧
      |d - 0| ≤ 1 / 500 := by
  have ht := tok_le w ev.hw j
  have hM4 : (4 : ℝ) ≤ M := ev.range 4 (by norm_num)
  refine ⟨_, _, _, _, init_eq fl p w j ht, ?_, ?_, ?_, ?_⟩
  · exact asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM4 _ (ev.hp.E _ 0)
      (le_trans (q01_abs (mkq_01 _)) (by norm_num))
  · exact asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM4 _ (ev.hp.E _ 1)
      (le_trans (q01_abs (aq_01 _)) (by norm_num))
  · exact asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM4 _ (ev.hp.E _ 2)
      (le_trans (q01_abs (cq_01 _)) (by norm_num))
  · have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM4 (0 : ℚ) (ev.hp.E (tokAt w j) 3) (by simp)
    simpa using h

theorem init_close (ev : Ctx u η M fl ex p w) (j : ℕ) :
    (net.init fl p w j).length = 4 ∧ Close (net.init fl p w j) (xh0 w j) (1 / 500) 1 := by
  obtain ⟨a, b, c, d, hx, ha, hb, hc, hd⟩ := init_ent ev j
  rw [hx]
  refine ⟨rfl, ?_⟩
  unfold xh0
  exact close4 ha hb hc hd (mR_abs w j) (aR_abs w j) (cR_abs w j) (by norm_num)

/-! ### Gates -/

theorem gate_gen (ev : Ctx u η M fl ex p w) (h : AHead) (dg : ℕ → ℝ) (dgb : ℝ) (x : Vec)
    (pre : ℝ) (hpre : |ardot fl h.g x dg 0 0 + asw fl h.gb dgb - pre| ≤ 2 / 5)
    (hb : |pre| ≤ 3 / 2) :
    (pre ≤ -1 / 2 → h.gate fl dg dgb x = 0) ∧ (1 / 2 ≤ pre → h.gate fl dg dgb x ≠ 0) := by
  unfold AHead.gate
  generalize ardot fl h.g x dg 0 0 + asw fl h.gb dgb = X at hpre ⊢
  obtain ⟨h1, h2⟩ := abs_le.mp hpre
  obtain ⟨h3, h4⟩ := abs_le.mp hb
  have hM2 : (2 : ℝ) ≤ M := ev.range 2 (by norm_num)
  have hX : |X| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  constructor
  · intro hn
    exact relu_fl_zero ev.hr (by linarith) (by linarith)
  · intro hp
    have hl := ev.hr.lower ev.hu0 hX hM2
    have hu := ev.u7
    have hη := ev.η9
    have hpos : 0 < fl X := by linarith
    intro h0
    unfold Lane4.relu at h0
    have := le_max_left (fl X) 0
    linarith

/-- the gate's ideal pre-activation, for a stored state close to an ideal one. -/
theorem gate_pre (ev : Ctx u η M fl ex p w) (h : AHead) (dg : ℕ → ℝ) (dgb : ℝ) (x xh : List ℝ)
    (hl : h.g.length = x.length) (hl4 : h.g.length ≤ 4) (hW : ∀ a ∈ h.g, |(a : ℝ)| ≤ 8)
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1 / 4) (hC : Close x xh e 1)
    (hd : ∀ k, |dg k| ≤ 1 / 1000) (hdb : |dgb| ≤ 1 / 1000)
    (hs : absSum h.g * e + (h.g.length : ℝ) * (1 / 600) + 1 / 1000000000 + 1 / 500 ≤ 2 / 5)
    (hgb : |((h.gb : ℚ) : ℝ)| ≤ 2) :
    |ardot fl h.g x dg 0 0 + asw fl h.gb dgb - (dotQ h.g xh + ((h.gb : ℚ) : ℝ))| ≤ 2 / 5 := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have h1 := ardotL ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 h.g x xh hl hl4 hW he0 he1 hC dg hd
  have h2 := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) h.gb hdb hgb
  have h3 := abs_add_le (ardot fl h.g x dg 0 0 - dotQ h.g xh) (asw fl h.gb dgb - ((h.gb : ℚ) : ℝ))
  have h4 : ardot fl h.g x dg 0 0 - dotQ h.g xh + (asw fl h.gb dgb - ((h.gb : ℚ) : ℝ)) =
      ardot fl h.g x dg 0 0 + asw fl h.gb dgb - (dotQ h.g xh + ((h.gb : ℚ) : ℝ)) := by ring
  rw [h4] at h3
  linarith

theorem gate1 (ev : Ctx u η M fl ex p w) (j : ℕ) :
    (mkd w j → head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) = 0) ∧
    (¬ mkd w j → head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) ≠ 0) := by
  obtain ⟨hlen, hC⟩ := init_close ev j
  have hq : dotQ head1.g (xh0 w j) = - mR w j := by
    first | (simp [dotQ, head1, xh0]; done) | (simp [dotQ, head1, xh0]; ring)
  have hgb : ((head1.gb : ℚ) : ℝ) = 1 / 2 := by norm_num [head1]
  have hs : absSum head1.g = 1 := by
    first | (norm_num [absSum, head1]; done) | simp [absSum, head1]
  have hgl : head1.g.length = 4 := rfl
  have hpre := gate_pre ev head1 (p.g 0 0) (p.gb 0 0) (net.init fl p w j) (xh0 w j)
    (by simp [hgl, hlen]) (by simp [hgl]) (by first | norm_num [head1] | simp [head1])
    (by norm_num : (0 : ℝ) ≤ 1 / 500) (by norm_num) hC (ev.hp.g 0 0) (ev.hp.gb 0 0)
    (by rw [hs, hgl]; norm_num) (by rw [hgb]; norm_num)
  rw [hq, hgb] at hpre
  have hb : |(- mR w j + 1 / 2)| ≤ 3 / 2 := by
    have := mR_abs w j
    rw [abs_le] at this ⊢
    constructor <;> linarith [this.1, this.2]
  have key := gate_gen ev head1 (p.g 0 0) (p.gb 0 0) (net.init fl p w j) _ hpre hb
  constructor
  · intro h
    rw [mR_one ev h] at key
    exact key.1 (by norm_num)
  · intro h
    rw [mR_zero ev h] at key
    exact key.2 (by norm_num)

/-! ### Layer 1: candidates, scores, softmax -/

noncomputable def cs1 (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : List ℕ :=
  head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

noncomputable def sc1 (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : ℕ → ℝ :=
  fun j => head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i j

noncomputable def att1 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (r : List ℚ) (k : ℕ) :
    ℝ :=
  savg fl ex (cs1 fl p w i) (sc1 fl p w i)
    (fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0)

theorem mem_cs1 (ev : Ctx u η M fl ex p w) (i j : ℕ) : j ∈ cs1 fl p w i ↔ j < i ∧ mkd w j := by
  unfold cs1
  rw [AHead.mem_cands]
  have hm : head1.mask = Mask.strict := rfl
  rw [hm, Lane4.Seq.mem_cand_strict]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra hn
    exact (gate1 ev j).2 hn h2
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (gate1 ev j).1 h2⟩

theorem cs1_nodup (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : (cs1 fl p w i).Nodup :=
  AHead.cands_nodup head1 fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

theorem cs1_len (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (hi : i ≤ w.length) :
    (cs1 fl p w i).length ≤ w.length + 1 := by
  have h1 : (cs1 fl p w i).length ≤ (cand Mask.strict (w.length + 1) i).length :=
    List.length_filter_le _ _
  have h2 : (cand Mask.strict (w.length + 1) i).length = i := by simp [cand]
  omega

theorem ardot_z4 (ev : Ctx u η M fl ex p w) (j : ℕ) (d : ℕ → ℝ) (hd : ∀ c, |d c| ≤ 1 / 1000) :
    |ardot fl z4 (net.init fl p w j) d 0 0 - 0| ≤ 1 / 100 := by
  obtain ⟨hlen, hC⟩ := init_close ev j
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have h := ardotL ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 z4 _ _
    (by simp [hlen, z4]) (by simp [z4]) (by norm_num [z4]) (by norm_num : (0 : ℝ) ≤ 1 / 500)
    (by norm_num) hC d hd
  have hs : absSum z4 = 0 := by simp [absSum, z4]
  have hl : (z4.length : ℝ) = 4 := by simp [z4]
  have hq : dotQ z4 (xh0 w j) = 0 := by simp [dotQ, z4, xh0]
  rw [hs, hl, hq] at h
  linarith

theorem content_small (ev : Ctx u η M fl ex p w) (i k : ℕ) :
    |Lane4.RSeq.pdot fl (net.init fl p w i)
        (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) 0| ≤ 1 / 10 := by
  obtain ⟨hli, hCi⟩ := init_close ev i
  have hrow : ∀ r : ℕ, |ardot fl z4 (net.init fl p w k) (p.A 0 0 r) 0 0 - 0| ≤ 1 / 100 :=
    fun r => ardot_z4 ev k (p.A 0 0 r) (ev.hp.A 0 0 r)
  have hy : armat fl head1.A (net.init fl p w k) (p.A 0 0) 0 =
      [ardot fl z4 (net.init fl p w k) (p.A 0 0 0) 0 0,
       ardot fl z4 (net.init fl p w k) (p.A 0 0 1) 0 0,
       ardot fl z4 (net.init fl p w k) (p.A 0 0 2) 0 0,
       ardot fl z4 (net.init fl p w k) (p.A 0 0 3) 0 0] := rfl
  have hCy : Close (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) [0, 0, 0, 0] (1 / 100) 0 := by
    rw [hy]
    exact close4 (hrow 0) (hrow 1) (hrow 2) (hrow 3) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hlen_y : (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0).length = 4 := by
    simp [hy]
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  obtain ⟨p1, -⟩ := pdot_near u η M fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (net.init fl p w i)
    (xh0 w i) (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) [0, 0, 0, 0] 1 0 (1 / 500)
    (1 / 100) (by rw [hli, hlen_y]) (by rw [hli]; norm_num) hCi hCy (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hM30
  have hdR : dotR (xh0 w i) [0, 0, 0, 0] = 0 := by simp [dotR, xh0]
  rw [hdR, sub_zero, hli] at p1
  refine le_trans p1 ?_
  norm_num

theorem head1_m : ((head1.m : ℚ) : ℝ) = 24 := by norm_num [head1]

theorem bias_abs (ev : Ctx u η M fl ex p w) (i t : ℕ) (hi : i ≤ w.length + 1)
    (ht : t ≤ w.length + 1) :
    |head1.bias fl (p.m 0 0) i t| ≤ 26 * ((w.length + 1 : ℕ) : ℝ) := by
  have hm := head1_m
  have habs : |((head1.m : ℚ) : ℝ)| = 24 := by rw [hm]; exact abs_of_nonneg (by norm_num)
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hM4 : (25 : ℝ) ≤ M := ev.range 25 (by norm_num)
  have hS := asw_bound ev.hr ev.hu0 head1.m (ev.hp.m 0 0) (by rw [habs]; linarith)
  rw [habs] at hS
  have hu25 : u * (24 + 1 / 1000) ≤ 1 / 2 ^ 24 * 25 :=
    mul_le_mul ev.hu1 (by norm_num) (by norm_num) (by positivity)
  have hη' := eta_tiny ev.hη1
  have hS2 : |asw fl head1.m (p.m 0 0)| ≤ 25 := by
    have h1 : (1 : ℝ) / 2 ^ 24 * 25 + 1 / 10 ^ 40 ≤ 1 / 2 := by norm_num
    linarith
  have hbias : head1.bias fl (p.m 0 0) i t
      = fl (asw fl head1.m (p.m 0 0) * ((t : ℝ) - (i : ℝ))) := by
    simp [AHead.bias]
  rw [hbias]
  generalize asw fl head1.m (p.m 0 0) = S at hS hS2 ⊢
  have ht' : (t : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast ht
  have hi' : (i : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hi
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hti : |(t : ℝ) - (i : ℝ)| ≤ ((w.length + 1 : ℕ) : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  have hab : |S * ((t : ℝ) - (i : ℝ))| ≤ 25 * ((w.length + 1 : ℕ) : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul hS2 hti (abs_nonneg _) (by norm_num)
  have hB := ev.rangeN 25 (by norm_num) (by norm_num)
  have h := ev.hr.bound ev.hu0 hab hB
  have hu25n := u_mul ev 25 (by norm_num)
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

theorem score_abs (ev : Ctx u η M fl ex p w) (i k : ℕ) (hi : i ≤ w.length + 1)
    (hk : k ≤ w.length + 1) :
    |head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i k| ≤ 28 * ((w.length + 1 : ℕ) : ℝ) := by
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hbk := bias_abs ev i k hi hk
  have hck := content_small ev i k
  have hB := ev.rangeN 27 (by norm_num) (by norm_num)
  have ha : |head1.bias fl (p.m 0 0) i k + Lane4.RSeq.pdot fl (net.init fl p w i)
      (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) 0| ≤ 27 * ((w.length + 1 : ℕ) : ℝ) :=
    le_trans (abs_add_le _ _) (by linarith)
  have h := ev.hr.bound ev.hu0 ha hB
  have hη' := eta_tiny ev.hη1
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have hu27 := u_mul ev 27 (by norm_num)
  unfold AHead.score
  linarith

theorem score_gap (ev : Ctx u η M fl ex p w) (i j k : ℕ) (hi : i ≤ w.length + 1)
    (hj : j ≤ w.length + 1) (hkj : k < j) :
    head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i k ≤
      head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i j - 16 * ((j : ℝ) - (k : ℝ)) := by
  have hm := head1_m
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hM12 : (2 : ℝ) ^ 12 * (((w.length + 1 : ℕ) : ℝ) + 1) ≤ M := by
    have := ev.rangeN 8192 (by norm_num) (by norm_num)
    have h12 : (2 : ℝ) ^ 12 = 4096 := by norm_num
    rw [h12]; linarith
  obtain ⟨hg1, -⟩ := bias_gap u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1
    (by norm_num) (by norm_num) head1 (p.m 0 0) (ev.hp.m 0 0) (by rw [hm]; norm_num)
    (by rw [hm]; norm_num) (w.length + 1) i j k hkj hj hi ev.hn ev.hnη hM12
  rw [hm] at hg1
  obtain ⟨hcj1, hcj2⟩ := abs_le.mp (content_small ev i j)
  obtain ⟨hck1, hck2⟩ := abs_le.mp (content_small ev i k)
  have hcj := content_small ev i j
  have hck := content_small ev i k
  have hbj := bias_abs ev i j hi hj
  have hbk := bias_abs ev i k hi (by omega)
  have hB := ev.rangeN 27 (by norm_num) (by norm_num)
  have ha : |head1.bias fl (p.m 0 0) i k + Lane4.RSeq.pdot fl (net.init fl p w i)
      (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) 0| ≤ 27 * ((w.length + 1 : ℕ) : ℝ) :=
    le_trans (abs_add_le _ _) (by linarith)
  have hb : |head1.bias fl (p.m 0 0) i j + Lane4.RSeq.pdot fl (net.init fl p w i)
      (armat fl head1.A (net.init fl p w j) (p.A 0 0) 0) 0| ≤ 27 * ((w.length + 1 : ℕ) : ℝ) :=
    le_trans (abs_add_le _ _) (by linarith)
  have hgap := ev.hr.gap ev.hu0 ha hb hB
  have hu27 := u_mul ev 27 (by norm_num)
  have hη' := eta_tiny ev.hη1
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have hjk : (k : ℝ) + 1 ≤ (j : ℝ) := by
    have h : k + 1 ≤ j := hkj
    exact_mod_cast h
  unfold AHead.score
  linarith

end Steps2

section Steps3

variable {u η M : ℝ} {fl ex : ℝ → ℝ} {p : APert} {w : List ℕ}

theorem savg_nil (hr : Rnd u η M fl) (s f : ℕ → ℝ) : savg fl ex [] s f = 0 := by
  have h : savg fl ex [] s f = fl (0 / 0) := rfl
  rw [h, div_zero, hr.zero]

theorem savg_single (hr : Rnd u η M fl) (he : ExpM u η ex) (s f : ℕ → ℝ) (j : ℕ)
    (hf : |f j| ≤ M) : savg fl ex [j] s f = fl (f j) := by
  have hsw : swt fl ex [j] s j = 1 := by
    unfold swt
    have : smax s [j] = s j := rfl
    rw [this, sub_self, hr.zero, he.zero]
  have h : savg fl ex [j] s f = fl (fl (0 + fl (swt fl ex [j] s j * f j)) / fl (0 + swt fl ex [j] s j)) := rfl
  rw [h, hsw, one_mul, zero_add, zero_add, hr.one, div_one, hr.idem _ hf, hr.idem _ hf]

theorem val_near1 (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr4 : r.length = 4)
    (habs : absSum r ≤ 1) (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 8) (j : ℕ) (d : ℕ → ℝ)
    (hd : ∀ c, |d c| ≤ 1 / 1000) :
    |ardot fl r (net.init fl p w j) d 0 0 - dotQ r (xh0 w j)| ≤ 1 / 100 := by
  obtain ⟨hlen, hC⟩ := init_close ev j
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have h := ardotL ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 r _ _ (by rw [hr4, hlen])
    (by omega) hW (by norm_num : (0 : ℝ) ≤ 1 / 500) (by norm_num) hC d hd
  have h4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
  rw [hr4, h4] at h
  have hm := mul_le_mul_of_nonneg_right habs (by norm_num : (0 : ℝ) ≤ 1 / 500)
  linarith

theorem att1_near (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr4 : r.length = 4)
    (habs : absSum r ≤ 1) (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 8) (v : ℝ) (hv : |v| ≤ 1 / 8)
    (hq : ∀ j, mkd w j → dotQ r (xh0 w j) = v) (k i : ℕ) (hi : i ≤ w.length) (s' : ℝ)
    (hs1 : HB w i → s' = v) (hs0 : ¬ HB w i → s' = 0) :
    |att1 fl ex p w i r k - s'| ≤ 1 / 80 := by
  classical
  by_cases hB : HB w i
  · obtain ⟨k0, hk0, hmk0⟩ := hB
    have hsv : s' = v := hs1 ⟨k0, hk0, hmk0⟩
    have hne : ((Finset.range i).filter (fun j => mkd w j)).Nonempty :=
      ⟨k0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk0, hmk0⟩⟩
    obtain ⟨j, hjS, hmax⟩ := Finset.exists_max_image ((Finset.range i).filter (fun j => mkd w j))
      (fun k => k) hne
    obtain ⟨hjr, hjm⟩ := Finset.mem_filter.mp hjS
    have hji : j < i := Finset.mem_range.mp hjr
    have hj : j ∈ cs1 fl p w i := (mem_cs1 ev i j).mpr ⟨hji, hjm⟩
    have hlen := cs1_len fl p w i hi
    have hgap : ∀ k' ∈ cs1 fl p w i, k' ≠ j →
        sc1 fl p w i k' ≤ sc1 fl p w i j - 16 * ((ndist j k' : ℕ) : ℝ) := by
      intro k' hk' hne'
      obtain ⟨hk'i, hk'm⟩ := (mem_cs1 ev i k').mp hk'
      have hle : k' ≤ j := hmax k' (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk'i, hk'm⟩)
      have hlt : k' < j := lt_of_le_of_ne hle hne'
      rw [ndist_cast]
      have hg := score_gap ev i j k' (by omega) (by omega) hlt
      have h1 : (k' : ℝ) + 1 ≤ (j : ℝ) := by
        have h : k' + 1 ≤ j := hlt
        exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      exact hg
    have hS : ∀ k' ∈ cs1 fl p w i, |sc1 fl p w i k'| ≤ 28 * ((w.length + 1 : ℕ) : ℝ) := by
      intro k' hk'
      have := (mem_cs1 ev i k').mp hk'
      exact score_abs ev i k' (by omega) (by omega)
    have hSM : 2 * (28 * ((w.length + 1 : ℕ) : ℝ)) ≤ M := by
      have := ev.rangeN 56 (by norm_num) (by norm_num)
      linarith
    have hf : ∀ k' ∈ cs1 fl p w i,
        |ardot fl r (net.init fl p w k') (p.V 0 0 k) 0 0| ≤ (1 / 7 : ℝ) := by
      intro k' hk'
      have hk'm := ((mem_cs1 ev i k').mp hk').2
      have h1 := val_near1 ev r hr4 habs hW k' (p.V 0 0 k) (ev.hp.V 0 0 k)
      rw [hq k' hk'm] at h1
      obtain ⟨h1a, h1b⟩ := abs_le.mp h1
      obtain ⟨h2a, h2b⟩ := abs_le.mp hv
      rw [abs_le]; constructor <;> linarith
    have hBM : 4 * (1 / 7 : ℝ) + 4 ≤ M := by
      have := ev.range 13 (by norm_num)
      linarith
    obtain ⟨hs1', -⟩ := soft_near (s := sc1 fl p w i)
      (f := fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0) ev.hr ev.he ev.hu0 ev.hu1
      ev.hη0 ev.hη1 (cs1_nodup fl p w i) hlen ev.hn ev.hnη hj hgap hS hSM hf hBM
    have key : |att1 fl ex p w i r k - ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0|
        ≤ (1 / 7 : ℝ) / 100 + 1 / 2 ^ 90 := hs1'
    have hv1 := val_near1 ev r hr4 habs hW j (p.V 0 0 k) (ev.hp.V 0 0 k)
    rw [hq j hjm, ← hsv] at hv1
    have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 1000000 := by norm_num
    have h3 := abs_sub_le (att1 fl ex p w i r k)
      (ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0) s'
    linarith
  · have hnil : cs1 fl p w i = [] := by
      by_contra hne
      obtain ⟨k', hk'⟩ := List.exists_mem_of_ne_nil _ hne
      have := (mem_cs1 ev i k').mp hk'
      exact hB ⟨k', this.1, this.2⟩
    have h0 : att1 fl ex p w i r k = 0 := by
      unfold att1
      rw [hnil, savg_nil ev.hr]
    rw [h0, hs0 hB]
    norm_num

theorem attz (ev : Ctx u η M fl ex p w) (k i : ℕ) (hi : i ≤ w.length) :
    |att1 fl ex p w i z4 k - 0| ≤ 1 / 80 :=
  att1_near ev z4 rfl (by simp [absSum, z4]) (by norm_num [z4]) 0 (by norm_num)
    (fun j _ => by simp [dotQ, z4, xh0]) k i hi 0 (fun _ => rfl) (fun _ => rfl)

theorem attf (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    |att1 fl ex p w i [1 / 8, 0, 0, 0] 3 - fv w i| ≤ 1 / 80 :=
  att1_near ev ([1 / 8, 0, 0, 0] : List ℚ) rfl (by norm_num [absSum]) (by norm_num) (1 / 8)
    (by norm_num)
    (fun j h => by
      have := mR_one ev h
      first | (norm_num [dotQ, xh0, this]; done) | (simp [dotQ, xh0, this]; norm_num))
    3 i hi (fv w i) (fun h => fv_pos h) (fun h => fv_neg h)

theorem mlp_small (ev : Ctx u η M fl ex p w) (d : ℝ) (hd : |d| ≤ 1 / 1000) :
    |fl (0 + asw fl 0 d)| ≤ 1 / 400 := by
  have h1 := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) (0 : ℚ) hd (by simp)
  have h1' : |asw fl 0 d| ≤ 1 / 500 := by simpa using h1
  have h2 : |(0 : ℝ) + asw fl 0 d| ≤ 1 / 500 := by rw [zero_add]; exact h1'
  have h3 := ev.hr.bound ev.hu0 h2 (ev.range (1 / 500) (by norm_num))
  have hu := ev.u7
  have hη := ev.η9
  linarith

theorem add_step (ev : Ctx u η M fl ex p w) {x s m t s' y e1 e2 : ℝ} (hx : |x - t| ≤ e1)
    (hs : |s - s'| ≤ e2) (hy : t + s' = y) (hy2 : |y| ≤ 2) (he1 : e1 ≤ 1 / 10)
    (he2 : e2 ≤ 1 / 10) (hm : |m| ≤ 1 / 400) :
    |fl (fl (x + s) + m) - y| ≤ e1 + e2 + 1 / 400 + 1 / 1000000 := by
  have hM3 : (3 : ℝ) ≤ M := ev.range 3 (by norm_num)
  have hu := ev.u7
  have hη := ev.η9
  have he10 : 0 ≤ e1 := le_trans (abs_nonneg _) hx
  have he20 : 0 ≤ e2 := le_trans (abs_nonneg _) hs
  obtain ⟨hxa, hxb⟩ := abs_le.mp hx
  obtain ⟨hsa, hsb⟩ := abs_le.mp hs
  obtain ⟨hya, hyb⟩ := abs_le.mp hy2
  obtain ⟨hma, hmb⟩ := abs_le.mp hm
  have h1 : |x + s - y| ≤ e1 + e2 := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |x + s| ≤ 3 := by
    rw [abs_le]; constructor <;> linarith
  have h3 := ev.hr.near ev.hu0 h1 h2 hM3
  obtain ⟨h3a, h3b⟩ := abs_le.mp h3
  have h4 : |fl (x + s) + m - y| ≤ e1 + e2 + (u * 3 + η) + 1 / 400 := by
    rw [abs_le]; constructor <;> linarith
  have h5 : |fl (x + s) + m| ≤ 3 := by
    rw [abs_le]; constructor <;> linarith
  have h6 := ev.hr.near ev.hu0 h4 h5 hM3
  linarith

theorem attn1_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
      (net.init fl p w) i =
    [att1 fl ex p w i z4 0, att1 fl ex p w i z4 1, att1 fl ex p w i z4 2,
     att1 fl ex p w i [1 / 8, 0, 0, 0] 3] := rfl

theorem stage1 (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : j ≤ w.length) :
    ∃ a b c d : ℝ, blk1.apply fl ex p 0 (w.length + 1) (net.init fl p w) j = [a, b, c, d] ∧
      |a - mR w j| ≤ 1 / 50 ∧ |b - aR w j| ≤ 1 / 50 ∧ |c - cR w j| ≤ 1 / 50 ∧
      |d - fv w j| ≤ 1 / 50 := by
  obtain ⟨a0, b0, c0, d0, hx, ha, hb, hc, hd⟩ := init_ent ev j
  have m0 := mlp_small ev (p.b2 0 0) (ev.hp.b2 0 0)
  have m1 := mlp_small ev (p.b2 0 1) (ev.hp.b2 0 1)
  have m2 := mlp_small ev (p.b2 0 2) (ev.hp.b2 0 2)
  have m3 := mlp_small ev (p.b2 0 3) (ev.hp.b2 0 3)
  have e1 := add_step ev ha (attz ev 0 j hj) (add_zero _)
    (le_trans (mR_abs w j) (by norm_num)) (by norm_num) (by norm_num) m0
  have e2 := add_step ev hb (attz ev 1 j hj) (add_zero _)
    (le_trans (aR_abs w j) (by norm_num)) (by norm_num) (by norm_num) m1
  have e3 := add_step ev hc (attz ev 2 j hj) (add_zero _)
    (le_trans (cR_abs w j) (by norm_num)) (by norm_num) (by norm_num) m2
  have e4 := add_step ev hd (attf ev j hj) (zero_add _)
    (le_trans (fv_abs w j) (by norm_num)) (by norm_num) (by norm_num) m3
  refine ⟨_, _, _, _, ?_, le_trans e1 (by norm_num), le_trans e2 (by norm_num),
    le_trans e3 (by norm_num), le_trans e4 (by norm_num)⟩
  have hh : blk1.apply fl ex p 0 (w.length + 1) (net.init fl p w) j =
      Lane4.RSeq.radd fl (Lane4.RSeq.radd fl (net.init fl p w j)
        (head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
          (net.init fl p w) j))
        [fl (0 + asw fl 0 (p.b2 0 0)), fl (0 + asw fl 0 (p.b2 0 1)),
         fl (0 + asw fl 0 (p.b2 0 2)), fl (0 + asw fl 0 (p.b2 0 3))] := rfl
  rw [hh, attn1_eq, hx]
  rfl

end Steps3

/-! ### Combinatorics of the first marked token -/

theorem firstc_snoc (l : List ℕ) (t : ℕ) :
    firstc (l ++ [t]) = if firstc l = 0 then code t else firstc l := by
  unfold firstc
  rw [List.foldl_append]
  rfl

theorem firstS (w : List ℕ) : ∀ i, i ≤ w.length →
    (firstc (w.take i) = 0 ∧ ∀ k, k ≤ i → code (tokAt w k) = 0) ∨
    (∃ q, q ≤ i ∧ code (tokAt w q) ≠ 0 ∧ (∀ k, k < q → code (tokAt w k) = 0) ∧
      firstc (w.take i) = code (tokAt w q)) := by
  intro i
  induction i with
  | zero =>
    intro _
    left
    refine ⟨by simp [firstc], ?_⟩
    intro k hk
    have : k = 0 := by omega
    subst this
    rw [Lane4.Seq.tokAt_zero]
    simp [code]
  | succ i ih =>
    intro hle
    have hlt : i < w.length := by omega
    have ih' := ih (by omega)
    have htake : w.take (i + 1) = w.take i ++ [w[i]] := by
      first
        | exact List.take_succ_eq_append_getElem hlt
        | (rw [List.take_succ]; simp [hlt])
    have htok : tokAt w (i + 1) = w[i] := Lane4.Seq.tokAt_succ w i hlt
    have hfc : firstc (w.take (i + 1)) =
        if firstc (w.take i) = 0 then code (tokAt w (i + 1)) else firstc (w.take i) := by
      rw [htake, firstc_snoc, htok]
    rcases ih' with ⟨h0, hall⟩ | ⟨q, hq, hqc, hqz, hqf⟩
    · by_cases hc : code (tokAt w (i + 1)) = 0
      · left
        refine ⟨?_, ?_⟩
        · rw [hfc, if_pos h0, hc]
        · intro k hk
          by_cases hki : k ≤ i
          · exact hall k hki
          · have : k = i + 1 := by omega
            rw [this]; exact hc
      · right
        refine ⟨i + 1, le_refl _, hc, ?_, ?_⟩
        · intro k hk
          exact hall k (by omega)
        · rw [hfc, if_pos h0]
    · right
      have hne : ¬ (firstc (w.take i) = 0) := by rw [hqf]; exact hqc
      refine ⟨q, by omega, hqc, hqz, ?_⟩
      rw [hfc, if_neg hne, hqf]

theorem cbit_01 (t : ℕ) : cbit t = 0 ∨ cbit t = 1 := by
  unfold cbit; split_ifs <;> simp

theorem getD_tokAt (w : List ℕ) (i : ℕ) (hi : 1 ≤ i) : w.getD (i - 1) 0 = tokAt w i := by
  cases i with
  | zero => omega
  | succ k => simp [tokAt]

theorem first_unique {w : List ℕ} {a b : ℕ} (ha : mkd w a ∧ ¬ HB w a) (hb : mkd w b ∧ ¬ HB w b) :
    a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact absurd (show HB w b from ⟨a, h, ha.1⟩) hb.2
  · exact h
  · exact absurd (show HB w a from ⟨b, h, hb.1⟩) ha.2

section Steps4

variable {u η M : ℝ} {fl ex : ℝ → ℝ} {p : APert} {w : List ℕ}

noncomputable def X1 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) : ℕ → Vec :=
  blk1.apply fl ex p 0 (w.length + 1) (net.init fl p w)

noncomputable def xh1 (w : List ℕ) (j : ℕ) : List ℝ := [mR w j, aR w j, cR w j, fv w j]

theorem x1_ent (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : j ≤ w.length) :
    ∃ a b c d : ℝ, X1 fl ex p w j = [a, b, c, d] ∧
      |a - mR w j| ≤ 1 / 50 ∧ |b - aR w j| ≤ 1 / 50 ∧ |c - cR w j| ≤ 1 / 50 ∧
      |d - fv w j| ≤ 1 / 50 := stage1 ev j hj

theorem x1_close (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : j ≤ w.length) :
    (X1 fl ex p w j).length = 4 ∧ Close (X1 fl ex p w j) (xh1 w j) (1 / 50) 1 := by
  obtain ⟨a, b, c, d, hx, ha, hb, hc, hd⟩ := x1_ent ev j hj
  rw [hx]
  refine ⟨rfl, ?_⟩
  unfold xh1
  exact close4 ha hb hc hd (mR_abs w j) (aR_abs w j) (cR_abs w j) (fv_abs w j)

theorem gate2 (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : j ≤ w.length) :
    (mkd w j ∧ ¬ HB w j → head2.gate fl (p.g 1 0) (p.gb 1 0) (X1 fl ex p w j) = 0) ∧
    (¬ (mkd w j ∧ ¬ HB w j) → head2.gate fl (p.g 1 0) (p.gb 1 0) (X1 fl ex p w j) ≠ 0) := by
  obtain ⟨hlen, hC⟩ := x1_close ev j hj
  have hq : dotQ head2.g (xh1 w j) = - mR w j + 8 * fv w j := by
    first | (simp [dotQ, head2, xh1]; done) | (simp [dotQ, head2, xh1]; ring)
  have hgb : ((head2.gb : ℚ) : ℝ) = 1 / 2 := by norm_num [head2]
  have hs : absSum head2.g = 9 := by
    first | (norm_num [absSum, head2]; done) | simp [absSum, head2]
  have hgl : head2.g.length = 4 := rfl
  have hpre := gate_pre ev head2 (p.g 1 0) (p.gb 1 0) (X1 fl ex p w j) (xh1 w j)
    (by simp [hgl, hlen]) (by simp [hgl]) (by first | norm_num [head2] | simp [head2])
    (by norm_num : (0 : ℝ) ≤ 1 / 50) (by norm_num) hC (ev.hp.g 1 0) (ev.hp.gb 1 0)
    (by rw [hs, hgl]; norm_num) (by rw [hgb]; norm_num)
  rw [hq, hgb] at hpre
  by_cases hm : mkd w j <;> by_cases hb : HB w j
  · have h1 := mR_one ev hm
    have h2 := fv_pos hb
    rw [h1, h2] at hpre
    have key := gate_gen ev head2 (p.g 1 0) (p.gb 1 0) (X1 fl ex p w j) _ hpre
      (by rw [abs_le]; constructor <;> norm_num)
    exact ⟨fun h => absurd hb h.2, fun _ => key.2 (by norm_num)⟩
  · have h1 := mR_one ev hm
    have h2 := fv_neg hb
    rw [h1, h2] at hpre
    have key := gate_gen ev head2 (p.g 1 0) (p.gb 1 0) (X1 fl ex p w j) _ hpre
      (by rw [abs_le]; constructor <;> norm_num)
    exact ⟨fun _ => key.1 (by norm_num), fun h => absurd ⟨hm, hb⟩ h⟩
  · have h1 := mR_zero ev hm
    have h2 := fv_pos hb
    rw [h1, h2] at hpre
    have key := gate_gen ev head2 (p.g 1 0) (p.gb 1 0) (X1 fl ex p w j) _ hpre
      (by rw [abs_le]; constructor <;> norm_num)
    exact ⟨fun h => absurd h.1 hm, fun _ => key.2 (by norm_num)⟩
  · have h1 := mR_zero ev hm
    have h2 := fv_neg hb
    rw [h1, h2] at hpre
    have key := gate_gen ev head2 (p.g 1 0) (p.gb 1 0) (X1 fl ex p w j) _ hpre
      (by rw [abs_le]; constructor <;> norm_num)
    exact ⟨fun h => absurd h.1 hm, fun _ => key.2 (by norm_num)⟩

noncomputable def cs2 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : List ℕ :=
  head2.cands fl (p.g 1 0) (p.gb 1 0) (w.length + 1) (X1 fl ex p w) i

noncomputable def att2 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (r : List ℚ) (k : ℕ) :
    ℝ :=
  savg fl ex (cs2 fl ex p w i) (fun j => head2.score fl (p.A 1 0) (p.m 1 0) (X1 fl ex p w) i j)
    (fun j => ardot fl r (X1 fl ex p w j) (p.V 1 0 k) 0 0)

theorem mem_cs2 (ev : Ctx u η M fl ex p w) (i j : ℕ) (hi : i ≤ w.length) :
    j ∈ cs2 fl ex p w i ↔ j ≤ i ∧ (mkd w j ∧ ¬ HB w j) := by
  unfold cs2
  rw [AHead.mem_cands]
  have hm : head2.mask = Mask.causal := rfl
  rw [hm, Lane4.Seq.mem_cand_causal]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra hn
    exact (gate2 ev j (by omega)).2 hn h2
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (gate2 ev j (by omega)).1 h2⟩

theorem att2_none (ev : Ctx u η M fl ex p w) (r : List ℚ) (k i : ℕ) (hi : i ≤ w.length)
    (hno : ∀ pp, pp ≤ i → ¬ (mkd w pp ∧ ¬ HB w pp)) : att2 fl ex p w i r k = 0 := by
  have hnil : cs2 fl ex p w i = [] := by
    by_contra hne
    obtain ⟨k', hk'⟩ := List.exists_mem_of_ne_nil _ hne
    have := (mem_cs2 ev i k' hi).mp hk'
    exact hno k' this.1 this.2
  unfold att2
  rw [hnil, savg_nil ev.hr]

theorem att2_one (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr4 : r.length = 4)
    (habs : absSum r ≤ 1) (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 8) (k i pp : ℕ) (hi : i ≤ w.length)
    (hp : pp ≤ i) (hm : mkd w pp) (hnb : ¬ HB w pp) (t : ℝ) (hq : dotQ r (xh1 w pp) = t)
    (ht : |t| ≤ 1) : |att2 fl ex p w i r k - t| ≤ 1 / 37 := by
  have hcs : cs2 fl ex p w i = [pp] := by
    unfold cs2 AHead.cands
    apply Lane4.Seq.filter_eq_singleton (Lane4.Seq.cand_nodup _ _ _)
    · exact Lane4.Seq.mem_cand_causal.mpr hp
    · exact decide_eq_true ((gate2 ev pp (by omega)).1 ⟨hm, hnb⟩)
    · intro k' hk' hne
      have hk'i : k' ≤ i := Lane4.Seq.mem_cand_causal.mp hk'
      apply decide_eq_false
      intro h0
      have hfm : mkd w k' ∧ ¬ HB w k' := by
        by_contra hn
        exact (gate2 ev k' (by omega)).2 hn h0
      exact hne (first_unique hfm ⟨hm, hnb⟩)
  obtain ⟨hlen, hC⟩ := x1_close ev pp (by omega)
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have h1 := ardotL ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 r _ _ (by rw [hr4, hlen]) (by omega)
    hW (by norm_num : (0 : ℝ) ≤ 1 / 50) (by norm_num) hC (p.V 1 0 k) (ev.hp.V 1 0 k)
  have h4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
  rw [hq, hr4, h4] at h1
  have hm' := mul_le_mul_of_nonneg_right habs (by norm_num : (0 : ℝ) ≤ 1 / 50)
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨hta, htb⟩ := abs_le.mp ht
  have hf2 : |ardot fl r (X1 fl ex p w pp) (p.V 1 0 k) 0 0| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith
  have hM2 : (2 : ℝ) ≤ M := ev.range 2 (by norm_num)
  have hs : att2 fl ex p w i r k = fl (ardot fl r (X1 fl ex p w pp) (p.V 1 0 k) 0 0) := by
    unfold att2
    rw [hcs]
    exact savg_single ev.hr ev.he _ _ pp (le_trans hf2 hM2)
  rw [hs]
  have h5 := ev.hr.abs ev.hu0 hf2 hM2
  obtain ⟨h5a, h5b⟩ := abs_le.mp h5
  have hu := ev.u7
  have hη := ev.η9
  rw [abs_le]
  constructor <;> linarith

theorem att2_z (ev : Ctx u η M fl ex p w) (k i : ℕ) (hi : i ≤ w.length) :
    |att2 fl ex p w i z4 k - 0| ≤ 1 / 37 := by
  by_cases hex : ∃ pp, pp ≤ i ∧ mkd w pp ∧ ¬ HB w pp
  · obtain ⟨pp, hp, hm, hnb⟩ := hex
    exact att2_one ev z4 rfl (by simp [absSum, z4]) (by norm_num [z4]) k i pp hi hp hm hnb 0
      (by simp [dotQ, z4, xh1]) (by norm_num)
  · rw [att2_none ev z4 k i hi (fun pp hp h => hex ⟨pp, hp, h⟩)]
    norm_num

theorem att2_a (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    ∃ t : ℝ, |att2 fl ex p w i [0, 1, 0, 0] 2 - t| ≤ 1 / 37 ∧ (t = 0 ∨ t = 1) ∧
      (t = 1 ↔ firstc (w.take i) = 2) := by
  by_cases hex : ∃ pp, pp ≤ i ∧ mkd w pp ∧ ¬ HB w pp
  · obtain ⟨pp, hp, hm, hnb⟩ := hex
    have hq : dotQ ([0, 1, 0, 0] : List ℚ) (xh1 w pp) = aR w pp := by
      first | (simp [dotQ, xh1]; done) | (simp [dotQ, xh1]; ring)
    refine ⟨aR w pp, att2_one ev ([0, 1, 0, 0] : List ℚ) rfl (by norm_num [absSum])
      (by first | norm_num | simp) 2 i pp hi hp hm hnb _ hq (aR_abs w pp), ?_, ?_⟩
    · rcases aq_01 (tokAt w pp) with h | h
      · left; unfold aR; simp [h]
      · right; unfold aR; simp [h]
    · rcases firstS w i hi with ⟨h0, hall⟩ | ⟨q, hq', hqc, hqz, hqf⟩
      · exact absurd (hall pp hp) hm
      · have hqfm : mkd w q ∧ ¬ HB w q := ⟨hqc, fun ⟨k, hk, hkm⟩ => hkm (hqz k hk)⟩
        have hqp : q = pp := first_unique hqfm ⟨hm, hnb⟩
        rw [hqp] at hqf
        rw [hqf]
        constructor
        · intro h
          by_contra hc
          have := aR_not_two ev hc
          rw [this] at h
          norm_num at h
        · intro h
          exact aR_two ev h
  · refine ⟨0, ?_, Or.inl rfl, ?_⟩
    · rw [att2_none ev [0, 1, 0, 0] 2 i hi (fun pp hp h => hex ⟨pp, hp, h⟩)]
      norm_num
    · constructor
      · intro h
        norm_num at h
      · intro h
        rcases firstS w i hi with ⟨h0, _⟩ | ⟨q, hq', hqc, hqz, hqf⟩
        · rw [h0] at h
          norm_num at h
        · exfalso
          exact hex ⟨q, hq', hqc, fun ⟨k, hk, hkm⟩ => hkm (hqz k hk)⟩

/-! ### Block 2: the MLP and the run -/

noncomputable def hid2 (fl : ℝ → ℝ) (p : APert) (Y : List ℝ) : ℝ :=
  Lane4.relu (fl (ardot fl ([0, 0, 1, 0] : List ℚ) Y (p.W1 1 0) 0 0 + asw fl (-1) (p.b1 1 0)))

noncomputable def mo (fl : ℝ → ℝ) (p : APert) (r : List ℚ) (k : ℕ) (h : ℝ) : ℝ :=
  fl (ardot fl r [h] (p.W2 1 k) 0 0 + asw fl 0 (p.b2 1 k))

theorem attn2_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    head2.attn fl ex (p.A 1 0) (p.V 1 0) (p.m 1 0) (p.g 1 0) (p.gb 1 0) (w.length + 1)
      (X1 fl ex p w) i =
    [att2 fl ex p w i z4 0, att2 fl ex p w i z4 1, att2 fl ex p w i [0, 1, 0, 0] 2,
     att2 fl ex p w i z4 3] := rfl

theorem run_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (a b c d s0 s1 s2 s3 : ℝ)
    (hX : X1 fl ex p w i = [a, b, c, d])
    (hA : head2.attn fl ex (p.A 1 0) (p.V 1 0) (p.m 1 0) (p.g 1 0) (p.gb 1 0) (w.length + 1)
      (X1 fl ex p w) i = [s0, s1, s2, s3]) (H : ℝ)
    (hH : H = hid2 fl p [fl (a + s0), fl (b + s1), fl (c + s2), fl (d + s3)]) :
    net.run fl ex p w i =
      [fl (fl (a + s0) + mo fl p [0] 0 H), fl (fl (b + s1) + mo fl p [0] 1 H),
       fl (fl (c + s2) + mo fl p [-2] 2 H), fl (fl (d + s3) + mo fl p [0] 3 H)] := by
  subst hH
  have hh : net.run fl ex p w i =
      Lane4.RSeq.radd fl (Lane4.RSeq.radd fl (X1 fl ex p w i)
        (head2.attn fl ex (p.A 1 0) (p.V 1 0) (p.m 1 0) (p.g 1 0) (p.gb 1 0) (w.length + 1)
          (X1 fl ex p w) i))
        (araffine fl [[0], [0], [-2], [0]] z4
          ((araffine fl [[0, 0, 1, 0]] [-1]
            (Lane4.RSeq.radd fl (X1 fl ex p w i)
              (head2.attn fl ex (p.A 1 0) (p.V 1 0) (p.m 1 0) (p.g 1 0) (p.gb 1 0)
                (w.length + 1) (X1 fl ex p w) i))
            (p.W1 1) (p.b1 1) 0).map Lane4.relu) (p.W2 1) (p.b2 1) 0) := rfl
  rw [hh, hX, hA]
  rfl

theorem add1 (ev : Ctx u η M fl ex p w) {x s t0 s' y e1 e2 : ℝ} (hx : |x - t0| ≤ e1)
    (hs : |s - s'| ≤ e2) (hy : t0 + s' = y) (hy2 : |y| ≤ 4) (he1 : e1 ≤ 1 / 4)
    (he2 : e2 ≤ 1 / 4) : |fl (x + s) - y| ≤ e1 + e2 + 1 / 1000000 := by
  have hM5 : (5 : ℝ) ≤ M := ev.range 5 (by norm_num)
  have hu := ev.u7
  have hη := ev.η9
  have he10 : 0 ≤ e1 := le_trans (abs_nonneg _) hx
  have he20 : 0 ≤ e2 := le_trans (abs_nonneg _) hs
  obtain ⟨hxa, hxb⟩ := abs_le.mp hx
  obtain ⟨hsa, hsb⟩ := abs_le.mp hs
  obtain ⟨hya, hyb⟩ := abs_le.mp hy2
  have h1 : |x + s - y| ≤ e1 + e2 := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |x + s| ≤ 5 := by
    rw [abs_le]; constructor <;> linarith
  have h3 := ev.hr.near ev.hu0 h1 h2 hM5
  linarith

theorem hid_near (ev : Ctx u η M fl ex p w) {y0 y1 y2 y3 z0 z1 z2 z3 : ℝ}
    (hC : Close [y0, y1, y2, y3] [z0, z1, z2, z3] (1 / 21) 2) (hz2 : |z2| ≤ 2) :
    |hid2 fl p [y0, y1, y2, y3] - max (z2 - 1) 0| ≤ 1 / 15 := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have h1 := ardotL2 ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 ([0, 0, 1, 0] : List ℚ)
    [y0, y1, y2, y3] [z0, z1, z2, z3] rfl (by simp) (by first | norm_num | simp)
    (by norm_num : (0 : ℝ) ≤ 1 / 21) (by norm_num) hC (p.W1 1 0) (ev.hp.W1 1 0)
  have hs : absSum ([0, 0, 1, 0] : List ℚ) = 1 := by
    first | (norm_num [absSum]; done) | simp [absSum]
  have hq : dotQ ([0, 0, 1, 0] : List ℚ) [z0, z1, z2, z3] = z2 := by
    first | (simp [dotQ]; done) | (simp [dotQ]; ring)
  have hl : ((([0, 0, 1, 0] : List ℚ).length : ℕ) : ℝ) = 4 := by simp
  have h2 := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) ((-1 : ℚ))
    (ev.hp.b1 1 0) (by norm_num)
  have hcast : (((-1 : ℚ)) : ℝ) = -1 := by norm_num
  rw [hcast] at h2
  rw [hs, hq, hl] at h1
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  obtain ⟨hza, hzb⟩ := abs_le.mp hz2
  have hP : |ardot fl ([0, 0, 1, 0] : List ℚ) [y0, y1, y2, y3] (p.W1 1 0) 0 0 +
      asw fl (-1) (p.b1 1 0) - (z2 - 1)| ≤ 63 / 1000 := by
    rw [abs_le]; constructor <;> linarith
  have hPB : |ardot fl ([0, 0, 1, 0] : List ℚ) [y0, y1, y2, y3] (p.W1 1 0) 0 0 +
      asw fl (-1) (p.b1 1 0)| ≤ 4 := by
    obtain ⟨hPa, hPb⟩ := abs_le.mp hP
    rw [abs_le]; constructor <;> linarith
  have h3 := ev.hr.near ev.hu0 hP hPB (ev.range 4 (by norm_num))
  have hu := ev.u7
  have hη := ev.η9
  have h4 := abs_max_sub_max_le_abs
    (fl (ardot fl ([0, 0, 1, 0] : List ℚ) [y0, y1, y2, y3] (p.W1 1 0) 0 0 +
      asw fl (-1) (p.b1 1 0))) (z2 - 1) 0
  have h5 : hid2 fl p [y0, y1, y2, y3] =
      max (fl (ardot fl ([0, 0, 1, 0] : List ℚ) [y0, y1, y2, y3] (p.W1 1 0) 0 0 +
        asw fl (-1) (p.b1 1 0))) 0 := rfl
  rw [h5]
  have h6 : |fl (ardot fl ([0, 0, 1, 0] : List ℚ) [y0, y1, y2, y3] (p.W1 1 0) 0 0 +
      asw fl (-1) (p.b1 1 0)) - (z2 - 1)| ≤ 1 / 15 := by
    refine le_trans h3 ?_
    linarith
  linarith

theorem mo_gen (ev : Ctx u η M fl ex p w) (r : List ℚ) (k : ℕ) (hr1 : r.length = 1)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 8) (H hh Δ t : ℝ) (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ 1 / 4)
    (hC : |H - hh| ≤ Δ) (hhb : |hh| ≤ 1) (hq : dotQ r [hh] = t) (ht : |t| ≤ 2)
    (habs : absSum r ≤ 2) :
    |mo fl p r k H - t| ≤ absSum r * Δ + 1 / 600 + 1 / 500 + 1 / 1000000 := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have h1 := ardotL ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 r [H] [hh] (by simp [hr1])
    (by omega) hW hΔ0 hΔ (close1 hC hhb) (p.W2 1 k) (ev.hp.W2 1 k)
  have h2 := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) (0 : ℚ)
    (ev.hp.b2 1 k) (by simp)
  have hz : (((0 : ℚ)) : ℝ) = 0 := by simp
  rw [hz] at h2
  have hl : (r.length : ℝ) = 1 := by rw [hr1]; simp
  rw [hq, hl] at h1
  have hm := mul_le_mul habs hΔ hΔ0 (by norm_num)
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  obtain ⟨hta, htb⟩ := abs_le.mp ht
  have hP : |ardot fl r [H] (p.W2 1 k) 0 0 + asw fl 0 (p.b2 1 k) - t| ≤
      absSum r * Δ + 1 / 600 + 1 / 500 + 1 / 1000000000 := by
    rw [abs_le]; constructor <;> linarith
  have hPB : |ardot fl r [H] (p.W2 1 k) 0 0 + asw fl 0 (p.b2 1 k)| ≤ 3 := by
    obtain ⟨hPa, hPb⟩ := abs_le.mp hP
    rw [abs_le]; constructor <;> linarith
  have h3 := ev.hr.near ev.hu0 hP hPB (ev.range 3 (by norm_num))
  have hu := ev.u7
  have hη := ev.η9
  unfold mo
  linarith

theorem mo_z (ev : Ctx u η M fl ex p w) (k : ℕ) (H hh : ℝ) (hH : |H - hh| ≤ 1 / 15)
    (hhb : |hh| ≤ 1) : |mo fl p [0] k H - 0| ≤ 1 / 200 := by
  have h := mo_gen ev ([0] : List ℚ) k rfl (by norm_num) H hh (1 / 15) 0 (by norm_num)
    (by norm_num) hH hhb (by simp [dotQ]) (by norm_num) (by norm_num [absSum])
  have hs : absSum ([0] : List ℚ) = 0 := by simp [absSum]
  rw [hs] at h
  linarith

theorem mo_m2 (ev : Ctx u η M fl ex p w) (H hh : ℝ) (hH : |H - hh| ≤ 1 / 15)
    (hhb : |hh| ≤ 1) : |mo fl p [-2] 2 H - (-2 * hh)| ≤ 1371 / 10000 := by
  have hq : dotQ ([-2] : List ℚ) [hh] = -2 * hh := by
    first | (simp [dotQ]; done) | (simp [dotQ]; ring)
  have hs : absSum ([-2] : List ℚ) = 2 := by
    first | (norm_num [absSum]; done) | simp [absSum]
  have habs : |(-2 * hh)| ≤ 2 := by
    rw [abs_le] at hhb ⊢
    constructor <;> linarith [hhb.1, hhb.2]
  have h := mo_gen ev ([-2] : List ℚ) 2 rfl (by norm_num) H hh (1 / 15) (-2 * hh) (by norm_num)
    (by norm_num) hH hhb hq habs (le_of_eq hs)
  rw [hs] at h
  linarith

end Steps4

section Steps5

variable {u η M : ℝ} {fl ex : ℝ → ℝ} {p : APert} {w : List ℕ}

theorem out_near (ev : Ctx u η M fl ex p w) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    |net.out fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  obtain ⟨a, b, c, d, hX, ha, hb, hc, hd⟩ := x1_ent ev i hi
  obtain ⟨t, hat, ht01, htA⟩ := att2_a ev i hi
  have ht1 : |t| ≤ 1 := by
    rcases ht01 with h | h <;> rw [h] <;> norm_num
  have z0 := att2_z ev 0 i hi
  have z1 := att2_z ev 1 i hi
  have z3 := att2_z ev 3 i hi
  have hA : head2.attn fl ex (p.A 1 0) (p.V 1 0) (p.m 1 0) (p.g 1 0) (p.gb 1 0) (w.length + 1)
      (X1 fl ex p w) i =
      [att2 fl ex p w i z4 0, att2 fl ex p w i z4 1, att2 fl ex p w i [0, 1, 0, 0] 2,
       att2 fl ex p w i z4 3] := rfl
  have hy2c : |cR w i + t| ≤ 2 :=
    le_trans (abs_add_le _ _) (by linarith [cR_abs w i, ht1])
  have y0 := add1 ev ha z0 (add_zero _) (le_trans (mR_abs w i) (by norm_num)) (by norm_num)
    (by norm_num)
  have y1 := add1 ev hb z1 (add_zero _) (le_trans (aR_abs w i) (by norm_num)) (by norm_num)
    (by norm_num)
  have y2 := add1 ev hc hat (rfl : cR w i + t = cR w i + t) (le_trans hy2c (by norm_num))
    (by norm_num) (by norm_num)
  have y3 := add1 ev hd z3 (add_zero _) (le_trans (fv_abs w i) (by norm_num)) (by norm_num)
    (by norm_num)
  have hCy := close4 (e := 1 / 21) (X := 2) (le_trans y0 (by norm_num)) (le_trans y1 (by norm_num))
    (le_trans y2 (by norm_num)) (le_trans y3 (by norm_num))
    (le_trans (mR_abs w i) (by norm_num)) (le_trans (aR_abs w i) (by norm_num)) hy2c
    (le_trans (fv_abs w i) (by norm_num))
  have hH := hid_near ev hCy hy2c
  have hrun := run_eq fl ex p w i a b c d _ _ _ _ hX hA _ rfl
  have hhat : |max (cR w i + t - 1) 0| ≤ 1 := by
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (by norm_num)
    have := cR_abs w i
    have h2 := abs_le.mp ht1
    have h3 := abs_le.mp this
    linarith [h2.2, h3.2]
  have m0 := mo_z ev 0 _ _ hH hhat
  have m1 := mo_z ev 1 _ _ hH hhat
  have m3 := mo_z ev 3 _ _ hH hhat
  have m2 := mo_m2 ev _ _ hH hhat
  obtain ⟨Xr, hXr⟩ : ∃ Xr : ℝ, Xr = cR w i + t + (-2 * max (cR w i + t - 1) 0) := ⟨_, rfl⟩
  -- the ideal output equals the target
  have hcb : cR w i = ((cbit (tokAt w i) : ℕ) : ℝ) := by
    unfold cR
    rw [cq_eq (tok_le w ev.hw i)]
    simp
  have htarget : ((target w i : ℕ) : ℝ) = Xr := by
    unfold target
    rw [getD_tokAt w i hi1]
    by_cases hf : firstc (w.take i) = 2
    · have ht' : t = 1 := htA.mpr hf
      rw [if_pos hf, hXr, ht', hcb]
      rcases cbit_01 (tokAt w i) with h | h <;> rw [h] <;> norm_num [max_def]
    · have ht' : t = 0 := by
        rcases ht01 with h | h
        · exact h
        · exact absurd (htA.mp h) hf
      rw [if_neg hf, hXr, ht', hcb]
      rcases cbit_01 (tokAt w i) with h | h <;> rw [h] <;> norm_num [max_def]
  have hXr1 : |Xr| ≤ 1 := by
    rw [← htarget]
    have : target w i < 2 := by
      unfold target
      exact Nat.mod_lt _ (by norm_num)
    have h' : target w i ≤ 1 := by omega
    have h'' : ((target w i : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h'
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact h''
  have z0' := add1 ev y0 m0 (add_zero _) (le_trans (mR_abs w i) (by norm_num)) (by norm_num)
    (by norm_num)
  have z1' := add1 ev y1 m1 (add_zero _) (le_trans (aR_abs w i) (by norm_num)) (by norm_num)
    (by norm_num)
  have z3' := add1 ev y3 m3 (add_zero _) (le_trans (fv_abs w i) (by norm_num)) (by norm_num)
    (by norm_num)
  have z2' := add1 ev y2 m2 hXr.symm (le_trans hXr1 (by norm_num)) (by norm_num) (by norm_num)
  have hCz := close4 (e := 3 / 16) (X := 1) (le_trans z0' (by norm_num)) (le_trans z1' (by norm_num))
    (le_trans z2' (by norm_num)) (le_trans z3' (by norm_num))
    (mR_abs w i) (aR_abs w i) hXr1 (fv_abs w i)
  have hout : net.out fl ex p w i =
      fl (ardot fl net.outW (net.run fl ex p w i) p.oW 0 0 + asw fl net.outB p.oB) := rfl
  rw [hout, hrun, htarget]
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have h1 := ardotL ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 net.outW _ _ (by simp [net])
    (by simp [net]) (by first | norm_num [net] | simp [net]) (by norm_num : (0 : ℝ) ≤ 3 / 16)
    (by norm_num) hCz p.oW ev.hp.oW
  have hq : dotQ net.outW [mR w i, aR w i, Xr, fv w i] = Xr := by
    first | (simp [dotQ, net]; done) | (simp [dotQ, net]; ring)
  have hs : absSum net.outW = 1 := by
    first | (norm_num [absSum, net]; done) | simp [absSum, net]
  have hl : ((net.outW.length : ℕ) : ℝ) = 4 := by simp [net]
  rw [hq, hs, hl] at h1
  have h2 := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) net.outB ev.hp.oB
    (by simp [net])
  have hz : ((net.outB : ℚ) : ℝ) = 0 := by simp [net]
  rw [hz] at h2
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  obtain ⟨hXa, hXb⟩ := abs_le.mp hXr1
  have key : ∀ S : ℝ, |S - Xr| ≤ 1 / 5 → |S| ≤ 3 → |fl S - Xr| ≤ 1 / 5 + (u * 3 + η) :=
    fun S h hB => ev.hr.near ev.hu0 h hB (ev.range 3 (by norm_num))
  have hu := ev.u7
  have hη := ev.η9
  refine le_trans (key _ ?_ ?_) ?_
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · linarith

end Steps5

theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη1 p hp w hw hn hnη hM i hi1 hi
  have ctx : Ctx u η M fl ex p w := ⟨hr, he, hu0, hu1, hη0, hη1, hp, hw, hn, hnη, hM⟩
  exact out_near ctx i hi1 hi

end Lane4.Case
