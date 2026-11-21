namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

/-! ### The network
State width 3, entries [flag, gen, dg]:
flag = 1 on propagate tokens, gen = 1 on generate tokens, dg = the digit.
One head (strict mask, slope 24) whose gate removes propagate keys, so the nearest
non-propagate earlier key wins; it copies its `gen` into the `dg` slot. The MLP then
computes dg + c - 2 relu (dg + c - 1), the XOR. -/

def z3 : List ℚ := [0, 0, 0]
def vrow : List ℚ := [0, 1, 0]
def gwt : List ℚ := [1, 0, 0]
def rW1 : List ℚ := [0, 0, 1]
def rZ : List ℚ := [0]
def rM : List ℚ := [-2]
def bb1 : ℚ := -1

def head1 : AHead :=
  { A := [z3, z3, z3], V := [z3, z3, vrow], mask := Mask.strict, m := 24, g := gwt,
    gb := -1 / 2 }

def blk : ABlock :=
  { heads := [head1], W1 := [rW1], b1 := [bb1], W2 := [rZ, rZ, rM], b2 := z3 }

def net : ANet :=
  { embed := [[0, 0, 0], [1, 0, 0], [0, 0, 0], [0, 1, 1], [1, 0, 1], [0, 1, 1]],
    blocks := [blk], outW := [0, 0, 1], outB := 0 }

/-! ### Ideal values -/

def flQ (t : ℕ) : ℚ := if t = 1 ∨ t = 4 then 1 else 0
def gnQ (t : ℕ) : ℚ := if t = 3 ∨ t = 5 then 1 else 0
def dgQ (t : ℕ) : ℚ := if t = 3 ∨ t = 4 ∨ t = 5 then 1 else 0

noncomputable def flR (t : ℕ) : ℝ := ((flQ t : ℚ) : ℝ)
noncomputable def gnR (t : ℕ) : ℝ := ((gnQ t : ℚ) : ℝ)
noncomputable def dgR (t : ℕ) : ℝ := ((dgQ t : ℚ) : ℝ)

noncomputable def xhat (w : List ℕ) (j : ℕ) : List ℝ :=
  [flR (tokAt w j), gnR (tokAt w j), dgR (tokAt w j)]

theorem flR_abs (t : ℕ) : |flR t| ≤ 1 := by
  unfold flR flQ
  split_ifs <;> norm_num

theorem gnR_abs (t : ℕ) : |gnR t| ≤ 1 := by
  unfold gnR gnQ
  split_ifs <;> norm_num

theorem dgR_abs (t : ℕ) : |dgR t| ≤ 1 := by
  unfold dgR dgQ
  split_ifs <;> norm_num

theorem flR_prop {t : ℕ} (h : t = 1 ∨ t = 4) : flR t = 1 := by
  unfold flR flQ
  rw [if_pos h]
  norm_num

theorem flR_nprop {t : ℕ} (h : ¬ (t = 1 ∨ t = 4)) : flR t = 0 := by
  unfold flR flQ
  rw [if_neg h]
  norm_num

theorem dgR_eq (t : ℕ) (ht : t ≤ 5) : dgR t = ((dg t : ℕ) : ℝ) := by
  interval_cases t <;> first
    | (simp [dgR, dgQ, dg]; done)
    | (norm_num [dgR, dgQ, dg]; done)

theorem gnR_cls (s : ℕ) (hs : s ≤ 5) (h : ¬ (s = 1 ∨ s = 4)) :
    gnR s = ((cls s : ℕ) : ℝ) := by
  interval_cases s <;> first
    | (exfalso; revert h; decide)
    | (simp [gnR, gnQ, cls]; done)
    | (norm_num [gnR, gnQ, cls]; done)

theorem cls_le (s : ℕ) (hs : s ≤ 5) : ¬ (s = 1 ∨ s = 4) → cls s ≤ 1 := by
  interval_cases s <;> decide

theorem cls_two (t : ℕ) (h1 : 1 ≤ t) (h5 : t ≤ 5) : cls t = 2 → (t = 1 ∨ t = 4) := by
  interval_cases t <;> decide

theorem dg_le (t : ℕ) : dg t ≤ 1 := by
  unfold dg
  split_ifs <;> omega

theorem xor_cast (a c : ℕ) (ha : a ≤ 1) (hc : c ≤ 1) :
    (((a + c) % 2 : ℕ) : ℝ) = (a : ℝ) + (c : ℝ) + -2 * Lane4.relu ((a : ℝ) + (c : ℝ) + -1) := by
  interval_cases a <;> interval_cases c <;> first
    | (norm_num [Lane4.relu, max_def]; done)
    | (simp [Lane4.relu]; norm_num; done)

theorem relu_lip {a b e : ℝ} (h : |a - b| ≤ e) : |Lane4.relu a - Lane4.relu b| ≤ e := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  unfold Lane4.relu
  rw [abs_le]
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [max_eq_right ha, max_eq_right hb]; constructor <;> linarith
  · rw [max_eq_right ha, max_eq_left hb]; constructor <;> linarith
  · rw [max_eq_left ha, max_eq_right hb]; constructor <;> linarith
  · rw [max_eq_left ha, max_eq_left hb]; constructor <;> linarith

theorem relu_unit {a : ℝ} (h : a ≤ 1) : |Lane4.relu a| ≤ 1 := by
  unfold Lane4.relu
  rw [abs_le]
  constructor
  · exact le_trans (by norm_num) (le_max_right a 0)
  · exact max_le h (by norm_num)

theorem z2_bound {D : ℝ} (h0 : 0 ≤ D) (h2 : D ≤ 2) :
    |D + -2 * Lane4.relu (D + -1)| ≤ 1 := by
  unfold Lane4.relu
  rw [abs_le]
  rcases le_total (D + -1) 0 with h | h
  · rw [max_eq_right h]; constructor <;> linarith
  · rw [max_eq_left h]; constructor <;> linarith

/-! ### Tokens and the carry -/

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem tok_real (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) (h1 : 1 ≤ i)
    (h2 : i ≤ w.length) : 1 ≤ tokAt w i ∧ tokAt w i ≤ 5 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < w.length := by omega
  rw [Lane4.Seq.tokAt_succ w k hk]
  exact hw _ (List.getElem_mem hk)

theorem target_eq' (w : List ℕ) (i : ℕ) (hi1 : 1 ≤ i) :
    target w i = (dg (tokAt w i) + carry (w.take (i - 1))) % 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have h : tokAt w (k + 1) = w.getD k 0 := by
    first | (simp [tokAt]; done) | rfl
  rw [h]
  rfl

theorem exists_last (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) :
    ∀ m, m ≤ w.length → ∃ j, j ≤ m ∧ ¬ (tokAt w j = 1 ∨ tokAt w j = 4) ∧
      (∀ k, j < k → k ≤ m → (tokAt w k = 1 ∨ tokAt w k = 4)) ∧
      carry (w.take m) = cls (tokAt w j) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨0, le_refl _, ?_, ?_, ?_⟩
    · rw [Lane4.Seq.tokAt_zero]; omega
    · intro k hk hk'; omega
    · rw [Lane4.Seq.tokAt_zero]; simp [carry, cls]
  | succ m ih =>
    intro hm
    obtain ⟨j, hjm, hj1, hj2, hj3⟩ := ih (by omega)
    have hmlen : m < w.length := by omega
    have htk : tokAt w (m + 1) = w[m] := Lane4.Seq.tokAt_succ w m hmlen
    have hmem : w[m] ∈ w := List.getElem_mem hmlen
    obtain ⟨h1, h5⟩ := hw _ hmem
    have htake : w.take (m + 1) = w.take m ++ [w[m]] := by
      first
        | (simp [List.take_succ, hmlen]; done)
        | (rw [List.take_succ]; simp [hmlen]; done)
        | exact List.take_succ_eq_append_getElem hmlen
    have hcar : carry (w.take (m + 1)) =
        (if cls w[m] = 2 then carry (w.take m) else cls w[m]) := by
      rw [htake]
      unfold carry
      rw [List.foldl_append]
      first | rfl | simp
    by_cases hp : (w[m] = 1 ∨ w[m] = 4)
    · refine ⟨j, by omega, hj1, ?_, ?_⟩
      · intro k hk hk'
        by_cases hkm : k = m + 1
        · rw [hkm, htk]; exact hp
        · exact hj2 k hk (by omega)
      · have hc2 : cls w[m] = 2 := by
          rcases hp with h | h <;> simp [cls, h]
        rw [hcar, if_pos hc2]; exact hj3
    · have hne : cls w[m] ≠ 2 := fun h2 => hp (cls_two _ h1 h5 h2)
      refine ⟨m + 1, le_refl _, by rw [htk]; exact hp, fun k hk hk' => by omega, ?_⟩
      rw [hcar, if_neg hne, htk]

/-! ### The context -/

structure Ctx (u η M : ℝ) (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) : Prop where
  hr : Rnd u η M fl
  he : ExpM u η ex
  hu0 : 0 ≤ u
  hu1 : u ≤ 1 / 2 ^ 24
  hη0 : 0 ≤ η
  hη1 : η ≤ 1 / 2 ^ 149
  hp : p.Within (1 / 1000)
  hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5
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

theorem rnd_small (ev : Ctx u η M fl ex p w) {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ 100) :
    u * B + η ≤ 1 / 100000 := by
  have h1 : u * B ≤ 1 / 2 ^ 24 * 100 := mul_le_mul ev.hu1 hB hB0 (by positivity)
  have h2 := eta_tiny ev.hη1
  have h3 : (1 : ℝ) / 2 ^ 24 * 100 + 1 / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  linarith

/-! ### Stored weights -/

theorem asw_c (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149)
    (hM : 4 ≤ M) (a : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 1000) (ha : |(a : ℝ)| ≤ 2) :
    |asw fl a d - (a : ℝ)| ≤ 1 / 500 := by
  have h := asw_near hr hu0 a hd (by linarith)
  have h1 : u * (|(a : ℝ)| + 1 / 1000) ≤ 1 / 2 ^ 24 * 3 :=
    mul_le_mul hu (by linarith) (by positivity) (by positivity)
  have h2 := eta_tiny hη
  have h3 : (1 : ℝ) / 2 ^ 24 * 3 + 1 / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

/-- Width-3 dot product with a row of written weights of size at most 1. -/
theorem ardot3 (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 2 ^ 149) (hM : (2 : ℝ) ^ 30 ≤ M) (r : List ℚ) (hr3 : r.length = 3)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) {S : ℝ} (hS : absSum r ≤ S) (x xh : List ℝ)
    (hx : x.length = 3) {X e : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 2) (he0 : 0 ≤ e) (he1 : e ≤ 1 / 5)
    (hC : Close x xh e X) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r x d 0 0 - dotQ r xh| ≤ S * e + 3 / 1000 * (X + e) + 1 / 2000 ∧
      |ardot fl r x d 0 0| ≤ 40 := by
  have h20 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
  have hT : (1 + 1) * (X + e + 1) ≤ (2 : ℝ) ^ 20 := by rw [h20]; linarith
  have k1 := ardot_near_abs u η M (1 / 1000) fl hr hu0 hu hη0 hη (by norm_num) (by norm_num)
    r x xh d 1 X e (by omega) (by omega) hC hd hW (by norm_num) hX0 he0 hT hM
  have k2 := (ardot_near u η M (1 / 1000) fl hr hu0 hu hη0 hη (by norm_num) (by norm_num)
    r x xh d 1 X e (by omega) (by omega) hC hd hW (by norm_num) hX0 he0 hT hM).2
  have hl : ((r.length : ℕ) : ℝ) = 3 := by rw [hr3]; norm_num
  have h16 : (2 : ℝ) ^ 16 = 65536 := by norm_num
  have h100 : (1 : ℝ) / 2 ^ 100 = 1 / 1267650600228229401496703205376 := by norm_num
  simp only [hl, h16, h100] at k1
  simp only [hl] at k2
  have hm := mul_le_mul_of_nonneg_right hS he0
  constructor
  · linarith
  · linarith

/-- Width-1 dot product with a row of written weights of size at most 2. -/
theorem ardot1 (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 2 ^ 149) (hM : (2 : ℝ) ^ 30 ≤ M) (r : List ℚ) (hr1 : r.length = 1)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 2) {S : ℝ} (hS : absSum r ≤ S) (x xh : List ℝ)
    (hx : x.length = 1) {X e : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 2) (he0 : 0 ≤ e) (he1 : e ≤ 1 / 5)
    (hC : Close x xh e X) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r x d 0 0 - dotQ r xh| ≤ S * e + 1 / 1000 * (X + e) + 1 / 2000 ∧
      |ardot fl r x d 0 0| ≤ 20 := by
  have h20 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
  have hT : (2 + 1) * (X + e + 1) ≤ (2 : ℝ) ^ 20 := by rw [h20]; linarith
  have k1 := ardot_near_abs u η M (1 / 1000) fl hr hu0 hu hη0 hη (by norm_num) (by norm_num)
    r x xh d 2 X e (by omega) (by omega) hC hd hW (by norm_num) hX0 he0 hT hM
  have k2 := (ardot_near u η M (1 / 1000) fl hr hu0 hu hη0 hη (by norm_num) (by norm_num)
    r x xh d 2 X e (by omega) (by omega) hC hd hW (by norm_num) hX0 he0 hT hM).2
  have hl : ((r.length : ℕ) : ℝ) = 1 := by rw [hr1]; norm_num
  have h16 : (2 : ℝ) ^ 16 = 65536 := by norm_num
  have h100 : (1 : ℝ) / 2 ^ 100 = 1 / 1267650600228229401496703205376 := by norm_num
  simp only [hl, h16, h100] at k1
  simp only [hl] at k2
  have hm := mul_le_mul_of_nonneg_right hS he0
  constructor
  · linarith
  · linarith

/-- `Close` for three entries. -/
theorem close3 {a b c a' b' c' e X : ℝ} (ha : |a - a'| ≤ e) (hb : |b - b'| ≤ e)
    (hc : |c - c'| ≤ e) (ha' : |a'| ≤ X) (hb' : |b'| ≤ X) (hc' : |c'| ≤ X) :
    Close [a, b, c] [a', b', c'] e X := by
  refine ⟨rfl, ?_⟩
  intro k hk
  have hk3 : k < 3 := by simpa using hk
  interval_cases k
  · first | exact ⟨ha, ha'⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨ha, ha'⟩)
  · first | exact ⟨hb, hb'⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨hb, hb'⟩)
  · first | exact ⟨hc, hc'⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨hc, hc'⟩)

theorem close1 {a a' e X : ℝ} (ha : |a - a'| ≤ e) (ha' : |a'| ≤ X) :
    Close [a] [a'] e X := by
  refine ⟨rfl, ?_⟩
  intro k hk
  have hk1 : k < 1 := by simpa using hk
  interval_cases k
  first | exact ⟨ha, ha'⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨ha, ha'⟩)

/-! ### Written rows -/

theorem z3_abs : absSum z3 ≤ 1 := by
  first | (norm_num [absSum, z3]; done) | (simp [absSum, z3]; done)

theorem vrow_abs : absSum vrow ≤ 1 := by
  first | (norm_num [absSum, vrow]; done) | (simp [absSum, vrow]; done)

theorem gwt_abs : absSum gwt ≤ 1 := by
  first | (norm_num [absSum, gwt]; done) | (simp [absSum, gwt]; done)

theorem rW1_abs : absSum rW1 ≤ 1 := by
  first | (norm_num [absSum, rW1]; done) | (simp [absSum, rW1]; done)

theorem rZ_abs : absSum rZ ≤ 2 := by
  first | (norm_num [absSum, rZ]; done) | (simp [absSum, rZ]; done)

theorem abs_neg_two : |((-2 : ℚ) : ℝ)| = 2 := by
  have h : ((-2 : ℚ) : ℝ) = -2 := by norm_num
  rw [h, abs_neg]
  exact abs_of_nonneg (by norm_num)

theorem rM_abs : absSum rM ≤ 2 := by
  unfold absSum rM
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [abs_neg_two]
  norm_num

theorem rM_ent : ∀ a ∈ rM, |(a : ℝ)| ≤ 2 := by
  intro a ha
  simp only [rM, List.mem_singleton] at ha
  exact le_of_eq (by rw [ha, abs_neg_two])

theorem dq0 (w : List ℕ) (j : ℕ) : dotQ z3 (xhat w j) = 0 := by
  simp [dotQ, z3, xhat]

theorem dq_vrow (w : List ℕ) (j : ℕ) : dotQ vrow (xhat w j) = gnR (tokAt w j) := by
  simp [dotQ, vrow, xhat]

theorem dqZ (h : ℝ) : dotQ rZ [h] = 0 := by simp [dotQ, rZ]

theorem dqM (h : ℝ) : dotQ rM [h] = -2 * h := by
  first
    | (simp [dotQ, rM]; done)
    | (simp [dotQ, rM]; ring)
    | (norm_num [dotQ, rM]; ring)

/-! ### Step 1: the starting state -/

theorem embed_row {t : ℕ} (h : t ≤ 5) : net.embed.getD t [] = [flQ t, gnQ t, dgQ t] := by
  interval_cases t <;> first | rfl | simp [net, flQ, gnQ, dgQ]

theorem init_eq (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (j : ℕ) (h : tokAt w j ≤ 5) :
    net.init fl p w j = [asw fl (flQ (tokAt w j)) (p.E (tokAt w j) 0),
      asw fl (gnQ (tokAt w j)) (p.E (tokAt w j) 1),
      asw fl (dgQ (tokAt w j)) (p.E (tokAt w j) 2)] := by
  show aswRow fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0 = _
  rw [embed_row h]
  rfl

theorem init_ent (ev : Ctx u η M fl ex p w) (j : ℕ) :
    ∃ a b c : ℝ, net.init fl p w j = [a, b, c] ∧
      |a - flR (tokAt w j)| ≤ 1 / 500 ∧ |b - gnR (tokAt w j)| ≤ 1 / 500 ∧
      |c - dgR (tokAt w j)| ≤ 1 / 500 := by
  have ht := tok_le w ev.hw j
  have hM4 : (4 : ℝ) ≤ M := ev.range 4 (by norm_num)
  refine ⟨_, _, _, init_eq fl p w j ht, ?_, ?_, ?_⟩
  · have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM4 (flQ (tokAt w j)) (ev.hp.E (tokAt w j) 0)
      (le_trans (flR_abs (tokAt w j)) (by norm_num))
    exact h
  · have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM4 (gnQ (tokAt w j)) (ev.hp.E (tokAt w j) 1)
      (le_trans (gnR_abs (tokAt w j)) (by norm_num))
    exact h
  · have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM4 (dgQ (tokAt w j)) (ev.hp.E (tokAt w j) 2)
      (le_trans (dgR_abs (tokAt w j)) (by norm_num))
    exact h

theorem init_close (ev : Ctx u η M fl ex p w) (j : ℕ) :
    (net.init fl p w j).length = 3 ∧ Close (net.init fl p w j) (xhat w j) (1 / 500) 1 := by
  obtain ⟨a, b, c, hx, ha, hb, hc⟩ := init_ent ev j
  rw [hx]
  refine ⟨rfl, ?_⟩
  unfold xhat
  exact close3 ha hb hc (flR_abs _) (gnR_abs _) (dgR_abs _)

/-! ### Step 2: the gate -/

noncomputable def gpre (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (j : ℕ) : ℝ :=
  ardot fl head1.g (net.init fl p w j) (p.g 0 0) 0 0 + asw fl head1.gb (p.gb 0 0)

theorem gate_pre (ev : Ctx u η M fl ex p w) (j : ℕ) :
    |gpre fl p w j - (flR (tokAt w j) - 1 / 2)| ≤ 1 / 100 ∧ |gpre fl p w j| ≤ 3 := by
  unfold gpre
  obtain ⟨hlen, hC⟩ := init_close ev j
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have h := ardot3 ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 head1.g rfl (by simp [head1, gwt])
    gwt_abs _ _ hlen (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hC (p.g 0 0) (ev.hp.g 0 0)
  have hq : dotQ head1.g (xhat w j) = flR (tokAt w j) := by simp [dotQ, head1, gwt, xhat]
  rw [hq] at h
  obtain ⟨h1, -⟩ := h
  have hgb : ((head1.gb : ℚ) : ℝ) = -1 / 2 := by norm_num [head1]
  have hb := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) head1.gb
    (ev.hp.gb 0 0) (by rw [hgb]; norm_num)
  rw [hgb] at hb
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨hba, hbb⟩ := abs_le.mp hb
  obtain ⟨hf1, hf2⟩ := abs_le.mp (flR_abs (tokAt w j))
  constructor
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

theorem gate_kept (ev : Ctx u η M fl ex p w) (j : ℕ) (h : ¬ (tokAt w j = 1 ∨ tokAt w j = 4)) :
    head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) = 0 := by
  obtain ⟨h1, h2⟩ := gate_pre ev j
  rw [flR_nprop h] at h1
  have hM3 : (3 : ℝ) ≤ M := ev.range 3 (by norm_num)
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  show Lane4.relu (fl (gpre fl p w j)) = 0
  exact relu_fl_zero ev.hr (by linarith) (by linarith)

theorem gate_rem (ev : Ctx u η M fl ex p w) (j : ℕ) (h : tokAt w j = 1 ∨ tokAt w j = 4) :
    head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) ≠ 0 := by
  obtain ⟨h1, h2⟩ := gate_pre ev j
  rw [flR_prop h] at h1
  have hM3 : (3 : ℝ) ≤ M := ev.range 3 (by norm_num)
  have hlow := ev.hr.lower ev.hu0 h2 hM3
  have hs := rnd_small ev (B := 3) (by norm_num) (by norm_num)
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  have hpos : 0 < fl (gpre fl p w j) := by linarith
  show Lane4.relu (fl (gpre fl p w j)) ≠ 0
  intro h0
  unfold Lane4.relu at h0
  rw [max_eq_left hpos.le] at h0
  linarith

/-! ### The candidates -/

noncomputable def cs (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : List ℕ :=
  head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

noncomputable def sc (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : ℕ → ℝ :=
  fun j => head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i j

noncomputable def att (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (r : List ℚ) (k : ℕ) :
    ℝ :=
  savg fl ex (cs fl p w i) (sc fl p w i) (fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0)

theorem mem_cs (ev : Ctx u η M fl ex p w) (i j : ℕ) :
    j ∈ cs fl p w i ↔ j < i ∧ ¬ (tokAt w j = 1 ∨ tokAt w j = 4) := by
  unfold cs
  rw [AHead.mem_cands]
  have hm : head1.mask = Mask.strict := rfl
  rw [hm, Lane4.Seq.mem_cand_strict]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hp => gate_rem ev j hp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, gate_kept ev j h2⟩

theorem cs_nodup (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : (cs fl p w i).Nodup :=
  AHead.cands_nodup head1 fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

theorem cs_len (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (hi : i ≤ w.length) :
    (cs fl p w i).length ≤ w.length + 1 := by
  have h1 : (cs fl p w i).length ≤ (cand Mask.strict (w.length + 1) i).length :=
    List.length_filter_le _ _
  have h2 : (cand Mask.strict (w.length + 1) i).length = i := by simp [cand]
  omega

theorem winner (ev : Ctx u η M fl ex p w) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    ∃ jw, jw ∈ cs fl p w i ∧ (∀ k' ∈ cs fl p w i, k' ≠ jw → k' < jw) ∧
      ¬ (tokAt w jw = 1 ∨ tokAt w jw = 4) ∧ carry (w.take (i - 1)) = cls (tokAt w jw) := by
  obtain ⟨j, hjm, hj1, hj2, hj3⟩ := exists_last w ev.hw (i - 1) (by omega)
  refine ⟨j, (mem_cs ev i j).mpr ⟨by omega, hj1⟩, ?_, hj1, hj3⟩
  intro k' hk' hne
  obtain ⟨hk1, hk2⟩ := (mem_cs ev i k').mp hk'
  by_contra hnot
  have hlt : j < k' := by omega
  exact hk2 (hj2 k' hlt (by omega))

/-! ### Step 3: scores -/

theorem val_near (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr3 : r.length = 3)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (hS : absSum r ≤ 1) (j : ℕ) (d : ℕ → ℝ)
    (hd : ∀ c, |d c| ≤ 1 / 1000) :
    |ardot fl r (net.init fl p w j) d 0 0 - dotQ r (xhat w j)| ≤ 1 / 150 := by
  obtain ⟨hlen, hC⟩ := init_close ev j
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have h := ardot3 ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 r hr3 hW hS _ _ hlen (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hC d hd
  have := h.1
  linarith [this]

theorem content_small (ev : Ctx u η M fl ex p w) (i k : ℕ) :
    |Lane4.RSeq.pdot fl (net.init fl p w i)
        (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) 0| ≤ 1 / 10 := by
  obtain ⟨hli, hCi⟩ := init_close ev i
  obtain ⟨hlk, hCk⟩ := init_close ev k
  have hrow : ∀ r : ℕ, |ardot fl z3 (net.init fl p w k) (p.A 0 0 r) 0 0 - 0| ≤ 1 / 150 := by
    intro r
    have h := val_near ev z3 rfl (by simp [z3]) z3_abs k (p.A 0 0 r) (ev.hp.A 0 0 r)
    rwa [dq0] at h
  have hy : armat fl head1.A (net.init fl p w k) (p.A 0 0) 0 =
      [ardot fl z3 (net.init fl p w k) (p.A 0 0 0) 0 0,
       ardot fl z3 (net.init fl p w k) (p.A 0 0 1) 0 0,
       ardot fl z3 (net.init fl p w k) (p.A 0 0 2) 0 0] := rfl
  have hCy : Close (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) [0, 0, 0] (1 / 150) 0 := by
    rw [hy]
    exact close3 (hrow 0) (hrow 1) (hrow 2) (by norm_num) (by norm_num) (by norm_num)
  have hlen_y : (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0).length = 3 := by
    simp [hy]
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  obtain ⟨p1, -⟩ := pdot_near u η M fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (net.init fl p w i)
    (xhat w i) (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) [0, 0, 0] 1 0 (1 / 500) (1 / 150)
    (by rw [hli, hlen_y]) (by rw [hli]; norm_num) hCi hCy (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hM30
  have hdR : dotR (xhat w i) [0, 0, 0] = 0 := by simp [dotR, xhat]
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
  generalize asw fl head1.m (p.m 0 0) = S at hS2 ⊢
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
    |head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i k| ≤
      28 * ((w.length + 1 : ℕ) : ℝ) := by
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

/-! ### Step 4: the head returns the value of the winner -/

theorem row_attn (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr3 : r.length = 3)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (hS1 : absSum r ≤ 1)
    (hq : ∀ j, |dotQ r (xhat w j)| ≤ 1) (k : ℕ)
    (i jw : ℕ) (hi : i ≤ w.length) (hj : jw ∈ cs fl p w i)
    (hmax : ∀ k' ∈ cs fl p w i, k' ≠ jw → k' < jw) :
    |att fl ex p w i r k - dotQ r (xhat w jw)| ≤ 1 / 50 := by
  have hlen := cs_len fl p w i hi
  have hjwi : jw < i := ((mem_cs ev i jw).mp hj).1
  have hgap : ∀ k' ∈ cs fl p w i, k' ≠ jw →
      sc fl p w i k' ≤ sc fl p w i jw - 16 * ((ndist jw k' : ℕ) : ℝ) := by
    intro k' hk' hne
    have hlt : k' < jw := hmax k' hk' hne
    rw [ndist_cast]
    have hg := score_gap ev i jw k' (by omega) (by omega) hlt
    have h1 : (k' : ℝ) + 1 ≤ (jw : ℝ) := by
      have h : k' + 1 ≤ jw := hlt
      exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    exact hg
  have hS : ∀ k' ∈ cs fl p w i, |sc fl p w i k'| ≤ 28 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k' hk'
    have := ((mem_cs ev i k').mp hk').1
    exact score_abs ev i k' (by omega) (by omega)
  have hSM : 2 * (28 * ((w.length + 1 : ℕ) : ℝ)) ≤ M := by
    have := ev.rangeN 56 (by norm_num) (by norm_num)
    linarith
  have hf : ∀ k' ∈ cs fl p w i,
      |ardot fl r (net.init fl p w k') (p.V 0 0 k) 0 0| ≤ (151 / 150 : ℝ) := by
    intro k' _
    have h1 := val_near ev r hr3 hW hS1 k' (p.V 0 0 k) (ev.hp.V 0 0 k)
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h2a, h2b⟩ := abs_le.mp (hq k')
    rw [abs_le]; constructor <;> linarith
  have hBM : 4 * (151 / 150 : ℝ) + 4 ≤ M := by
    have := ev.range 13 (by norm_num)
    linarith
  obtain ⟨hs1, -⟩ := soft_near (s := sc fl p w i)
    (f := fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0) ev.hr ev.he ev.hu0 ev.hu1
    ev.hη0 ev.hη1 (cs_nodup fl p w i) hlen ev.hn ev.hnη hj hgap hS hSM hf hBM
  have hs1' : |att fl ex p w i r k - ardot fl r (net.init fl p w jw) (p.V 0 0 k) 0 0|
      ≤ (151 / 150 : ℝ) / 100 + 1 / 2 ^ 90 := hs1
  have hv := val_near ev r hr3 hW hS1 jw (p.V 0 0 k) (ev.hp.V 0 0 k)
  have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 1000000 := by norm_num
  have h3 := abs_sub_le (att fl ex p w i r k)
    (ardot fl r (net.init fl p w jw) (p.V 0 0 k) 0 0) (dotQ r (xhat w jw))
  linarith

/-! ### Step 5: the forward pass, unfolded -/

noncomputable def Yv (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : Vec :=
  Lane4.RSeq.radd fl (net.init fl p w i)
    (head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
      (net.init fl p w) i)

noncomputable def hidv (fl : ℝ → ℝ) (p : APert) (y0 y1 y2 : ℝ) : ℝ :=
  Lane4.relu (fl (ardot fl rW1 [y0, y1, y2] (p.W1 0 0) 0 0 + asw fl bb1 (p.b1 0 0)))

theorem attn_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
      (net.init fl p w) i =
    [att fl ex p w i z3 0, att fl ex p w i z3 1, att fl ex p w i vrow 2] := rfl

theorem Yv_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (a b c : ℝ)
    (hx : net.init fl p w i = [a, b, c]) :
    Yv fl ex p w i = [fl (a + att fl ex p w i z3 0), fl (b + att fl ex p w i z3 1),
      fl (c + att fl ex p w i vrow 2)] := by
  unfold Yv
  rw [attn_eq, hx]
  rfl

theorem run_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (y0 y1 y2 : ℝ)
    (hY : Yv fl ex p w i = [y0, y1, y2]) :
    net.run fl ex p w i =
      [fl (y0 + fl (ardot fl rZ [hidv fl p y0 y1 y2] (p.W2 0 0) 0 0 + asw fl 0 (p.b2 0 0))),
       fl (y1 + fl (ardot fl rZ [hidv fl p y0 y1 y2] (p.W2 0 1) 0 0 + asw fl 0 (p.b2 0 1))),
       fl (y2 + fl (ardot fl rM [hidv fl p y0 y1 y2] (p.W2 0 2) 0 0 + asw fl 0 (p.b2 0 2)))] := by
  have h : net.run fl ex p w i = Lane4.RSeq.radd fl (Yv fl ex p w i)
      (araffine fl blk.W2 blk.b2
        ((araffine fl blk.W1 blk.b1 (Yv fl ex p w i) (p.W1 0) (p.b1 0) 0).map Lane4.relu)
        (p.W2 0) (p.b2 0) 0) := rfl
  rw [h, hY]
  rfl

/-! ### Step 6: the stages -/

theorem ystep (ev : Ctx u η M fl ex p w) {x s A B' : ℝ} (hx : |x - A| ≤ 1 / 500)
    (hs : |s - B'| ≤ 1 / 50) (hAB : |A + B'| ≤ 2) : |fl (x + s) - (A + B')| ≤ 1 / 40 := by
  have h1 : |x + s - (A + B')| ≤ 1 / 500 + 1 / 50 := by
    have := abs_add_le (x - A) (s - B')
    have e : x - A + (s - B') = x + s - (A + B') := by ring
    rw [e] at this
    linarith
  have h2 : |x + s| ≤ 3 := by
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h3a, h3b⟩ := abs_le.mp hAB
    rw [abs_le]; constructor <;> linarith
  have h3 := ev.hr.near ev.hu0 h1 h2 (ev.range 3 (by norm_num))
  have h4 := rnd_small ev (B := 3) (by norm_num) (by norm_num)
  linarith

theorem hid_step (ev : Ctx u η M fl ex p w) {y0 y1 y2 F G D : ℝ}
    (hy : Close [y0, y1, y2] [F, G, D] (1 / 40) 2) :
    |hidv fl p y0 y1 y2 - Lane4.relu (D + -1)| ≤ 1 / 25 := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  obtain ⟨k1, k2⟩ := ardot3 ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 rW1 rfl (by simp [rW1])
    rW1_abs [y0, y1, y2] [F, G, D] rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hy (p.W1 0 0) (ev.hp.W1 0 0)
  have hq : dotQ rW1 [F, G, D] = D := by simp [dotQ, rW1]
  rw [hq] at k1
  have hbb : ((bb1 : ℚ) : ℝ) = -1 := by norm_num [bb1]
  have hb := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) bb1 (ev.hp.b1 0 0)
    (by rw [hbb]; norm_num)
  rw [hbb] at hb
  obtain ⟨hba, hbb2⟩ := abs_le.mp hb
  have hbabs : |asw fl bb1 (p.b1 0 0)| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith
  have e1 : |ardot fl rW1 [y0, y1, y2] (p.W1 0 0) 0 0 + asw fl bb1 (p.b1 0 0) - (D + -1)|
      ≤ 7 / 200 := by
    have h := abs_add_le (ardot fl rW1 [y0, y1, y2] (p.W1 0 0) 0 0 - D)
      (asw fl bb1 (p.b1 0 0) - -1)
    have e : ardot fl rW1 [y0, y1, y2] (p.W1 0 0) 0 0 - D + (asw fl bb1 (p.b1 0 0) - -1)
        = ardot fl rW1 [y0, y1, y2] (p.W1 0 0) 0 0 + asw fl bb1 (p.b1 0 0) - (D + -1) := by
      ring
    rw [e] at h
    linarith
  have hB : |ardot fl rW1 [y0, y1, y2] (p.W1 0 0) 0 0 + asw fl bb1 (p.b1 0 0)| ≤ 100 := by
    have := abs_add_le (ardot fl rW1 [y0, y1, y2] (p.W1 0 0) 0 0) (asw fl bb1 (p.b1 0 0))
    linarith
  have h3 := ev.hr.near ev.hu0 e1 hB (ev.range 100 (by norm_num))
  have h4 := rnd_small ev (B := 100) (by norm_num) (by norm_num)
  have h5 : |fl (ardot fl rW1 [y0, y1, y2] (p.W1 0 0) 0 0 + asw fl bb1 (p.b1 0 0)) - (D + -1)|
      ≤ 1 / 25 := by linarith
  unfold hidv
  exact relu_lip h5

theorem mstep (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr1 : r.length = 1)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 2) (hS : absSum r ≤ 2) {h hh : ℝ}
    (hC : |h - hh| ≤ 1 / 25) (hhh : |hh| ≤ 1) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000)
    (db : ℝ) (hdb : |db| ≤ 1 / 1000) :
    |fl (ardot fl r [h] d 0 0 + asw fl 0 db) - dotQ r [hh]| ≤ 1 / 10 := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  obtain ⟨k1, k2⟩ := ardot1 ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 r hr1 hW hS [h] [hh]
    (by simp) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (close1 hC hhh) d hd
  have hz := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) (0 : ℚ) hdb (by simp)
  have hz' : |asw fl 0 db| ≤ 1 / 500 := by simpa using hz
  have e1 : |ardot fl r [h] d 0 0 + asw fl 0 db - dotQ r [hh]| ≤ 9 / 100 := by
    have h1 := abs_add_le (ardot fl r [h] d 0 0 - dotQ r [hh]) (asw fl 0 db)
    have e : ardot fl r [h] d 0 0 - dotQ r [hh] + asw fl 0 db
        = ardot fl r [h] d 0 0 + asw fl 0 db - dotQ r [hh] := by ring
    rw [e] at h1
    linarith
  have hB : |ardot fl r [h] d 0 0 + asw fl 0 db| ≤ 100 := by
    have := abs_add_le (ardot fl r [h] d 0 0) (asw fl 0 db)
    linarith
  have h3 := ev.hr.near ev.hu0 e1 hB (ev.range 100 (by norm_num))
  have h4 := rnd_small ev (B := 100) (by norm_num) (by norm_num)
  linarith

theorem zstep (ev : Ctx u η M fl ex p w) {y m Y' Mi : ℝ} (hy : |y - Y'| ≤ 1 / 40)
    (hm : |m - Mi| ≤ 1 / 10) (hY : |Y'| ≤ 2) (hMi : |Mi| ≤ 2) :
    |fl (y + m) - (Y' + Mi)| ≤ 1 / 7 := by
  have h1 : |y + m - (Y' + Mi)| ≤ 1 / 40 + 1 / 10 := by
    have := abs_add_le (y - Y') (m - Mi)
    have e : y - Y' + (m - Mi) = y + m - (Y' + Mi) := by ring
    rw [e] at this
    linarith
  have h2 : |y + m| ≤ 5 := by
    obtain ⟨a1, a2⟩ := abs_le.mp h1
    obtain ⟨b1, b2⟩ := abs_le.mp hY
    obtain ⟨c1, c2⟩ := abs_le.mp hMi
    rw [abs_le]; constructor <;> linarith
  have h3 := ev.hr.near ev.hu0 h1 h2 (ev.range 5 (by norm_num))
  have h4 := rnd_small ev (B := 5) (by norm_num) (by norm_num)
  linarith

theorem out_step (ev : Ctx u η M fl ex p w) {z0 z1 z2 Z0 Z1 Z2 : ℝ}
    (hz : Close [z0, z1, z2] [Z0, Z1, Z2] (1 / 7) 2) :
    |fl (ardot fl net.outW [z0, z1, z2] p.oW 0 0 + asw fl net.outB p.oB) - Z2| ≤ 1 / 4 := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have habs : absSum net.outW ≤ 1 := by
    first | (norm_num [absSum, net]; done) | (simp [absSum, net]; done)
  obtain ⟨k1, k2⟩ := ardot3 ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 net.outW rfl
    (by simp [net]) habs [z0, z1, z2] [Z0, Z1, Z2] rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hz p.oW ev.hp.oW
  have hq : dotQ net.outW [Z0, Z1, Z2] = Z2 := by simp [dotQ, net]
  rw [hq] at k1
  have hob := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) net.outB ev.hp.oB
    (by simp [net])
  have h0 : ((net.outB : ℚ) : ℝ) = 0 := by simp [net]
  rw [h0, sub_zero] at hob
  have e1 : |ardot fl net.outW [z0, z1, z2] p.oW 0 0 + asw fl net.outB p.oB - Z2| ≤ 8 / 50 := by
    have h1 := abs_add_le (ardot fl net.outW [z0, z1, z2] p.oW 0 0 - Z2)
      (asw fl net.outB p.oB)
    have e : ardot fl net.outW [z0, z1, z2] p.oW 0 0 - Z2 + asw fl net.outB p.oB
        = ardot fl net.outW [z0, z1, z2] p.oW 0 0 + asw fl net.outB p.oB - Z2 := by ring
    rw [e] at h1
    linarith
  have hB : |ardot fl net.outW [z0, z1, z2] p.oW 0 0 + asw fl net.outB p.oB| ≤ 100 := by
    have := abs_add_le (ardot fl net.outW [z0, z1, z2] p.oW 0 0) (asw fl net.outB p.oB)
    have hZ : |Z2| ≤ 2 := by
      have := close_cons (close_cons hz).2.2
      have h2 := close_cons this.2.2
      exact h2.2.1
    linarith [abs_sub_abs_le_abs_sub (ardot fl net.outW [z0, z1, z2] p.oW 0 0 + asw fl net.outB p.oB) Z2]
  have h3 := ev.hr.near ev.hu0 e1 hB (ev.range 100 (by norm_num))
  have h4 := rnd_small ev (B := 100) (by norm_num) (by norm_num)
  linarith

theorem tail_bound (ev : Ctx u η M fl ex p w) (i : ℕ) {y0 y1 y2 Y0 Y1 D : ℝ}
    (hY : Yv fl ex p w i = [y0, y1, y2])
    (hy0 : |y0 - Y0| ≤ 1 / 40) (hy1 : |y1 - Y1| ≤ 1 / 40) (hy2 : |y2 - D| ≤ 1 / 40)
    (hY0 : |Y0| ≤ 2) (hY1 : |Y1| ≤ 2) (hD0 : 0 ≤ D) (hD2 : D ≤ 2) :
    |net.out fl ex p w i - (D + -2 * Lane4.relu (D + -1))| ≤ 1 / 4 := by
  have hDabs : |D| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hy : Close [y0, y1, y2] [Y0, Y1, D] (1 / 40) 2 := close3 hy0 hy1 hy2 hY0 hY1 hDabs
  have hh := hid_step ev hy
  have hrel : |Lane4.relu (D + -1)| ≤ 1 := relu_unit (by linarith)
  have m0 := mstep ev rZ rfl (by simp [rZ]) rZ_abs hh hrel (p.W2 0 0) (ev.hp.W2 0 0)
    (p.b2 0 0) (ev.hp.b2 0 0)
  have m1 := mstep ev rZ rfl (by simp [rZ]) rZ_abs hh hrel (p.W2 0 1) (ev.hp.W2 0 1)
    (p.b2 0 1) (ev.hp.b2 0 1)
  have m2 := mstep ev rM rfl rM_ent rM_abs hh hrel (p.W2 0 2) (ev.hp.W2 0 2)
    (p.b2 0 2) (ev.hp.b2 0 2)
  rw [dqZ] at m0 m1
  rw [dqM] at m2
  have hmi : |-2 * Lane4.relu (D + -1)| ≤ 2 := by
    obtain ⟨r1, r2⟩ := abs_le.mp hrel
    rw [abs_le]; constructor <;> linarith
  have z0 := zstep ev hy0 m0 hY0 (by norm_num)
  have z1 := zstep ev hy1 m1 hY1 (by norm_num)
  have z2 := zstep ev hy2 m2 hDabs hmi
  have hz2 := z2_bound hD0 hD2
  have hz := close3 z0 z1 z2 (by rw [add_zero]; exact hY0) (by rw [add_zero]; exact hY1)
    (le_trans hz2 (by norm_num))
  unfold ANet.out
  rw [run_eq fl ex p w i y0 y1 y2 hY]
  exact out_step ev hz

/-! ### The theorem -/

theorem out_near (ev : Ctx u η M fl ex p w) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    |net.out fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  obtain ⟨jw, hjw, hmax, hjnp, hcar⟩ := winner ev i hi1 hi
  have hti := tok_real w ev.hw i hi1 hi
  have hjw5 := tok_le w ev.hw jw
  obtain ⟨a, b, c, hx, ha, hb, hc⟩ := init_ent ev i
  have r0 := row_attn ev z3 rfl (by simp [z3]) z3_abs (fun j => by rw [dq0]; norm_num) 0 i jw
    hi hjw hmax
  have r1 := row_attn ev z3 rfl (by simp [z3]) z3_abs (fun j => by rw [dq0]; norm_num) 1 i jw
    hi hjw hmax
  have r2 := row_attn ev vrow rfl (by simp [vrow]) vrow_abs
    (fun j => by rw [dq_vrow]; exact gnR_abs _) 2 i jw hi hjw hmax
  rw [dq0] at r0 r1
  rw [dq_vrow] at r2
  have y0b := ystep ev ha r0
    (by rw [add_zero]; exact le_trans (flR_abs _) (by norm_num))
  have y1b := ystep ev hb r1
    (by rw [add_zero]; exact le_trans (gnR_abs _) (by norm_num))
  have y2b := ystep ev hc r2
    (by
      have h1 := dgR_abs (tokAt w i)
      have h2 := gnR_abs (tokAt w jw)
      have h3 := abs_add_le (dgR (tokAt w i)) (gnR (tokAt w jw))
      linarith)
  have hY := Yv_eq fl ex p w i a b c hx
  have hdg0 : 0 ≤ dgR (tokAt w i) := by
    rw [dgR_eq _ hti.2]; exact Nat.cast_nonneg _
  have hgn0 : 0 ≤ gnR (tokAt w jw) := by
    rw [gnR_cls _ hjw5 hjnp]; exact Nat.cast_nonneg _
  have hdg1 : dgR (tokAt w i) ≤ 1 := le_trans (le_abs_self _) (dgR_abs _)
  have hgn1 : gnR (tokAt w jw) ≤ 1 := le_trans (le_abs_self _) (gnR_abs _)
  have htarget : ((target w i : ℕ) : ℝ) =
      (dgR (tokAt w i) + gnR (tokAt w jw)) +
        -2 * Lane4.relu ((dgR (tokAt w i) + gnR (tokAt w jw)) + -1) := by
    rw [target_eq' w i hi1, hcar]
    rw [xor_cast (dg (tokAt w i)) (cls (tokAt w jw)) (dg_le _) (cls_le _ hjw5 hjnp)]
    rw [dgR_eq _ hti.2, gnR_cls _ hjw5 hjnp]
  rw [htarget]
  exact tail_bound ev i hY y0b y1b y2b
    (by rw [add_zero]; exact le_trans (flR_abs _) (by norm_num))
    (by rw [add_zero]; exact le_trans (gnR_abs _) (by norm_num))
    (by linarith) (by linarith)

end Steps

theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη1 p hp w hw hn hnη hM i hi1 hi
  have ctx : Ctx u η M fl ex p w := ⟨hr, he, hu0, hu1, hη0, hη1, hp, hw, hn, hnη, hM⟩
  exact out_near ctx i hi1 hi

end Lane4.Case
