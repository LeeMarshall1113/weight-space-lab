namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1000000

/-! ### The network -/

def gn (t : ℕ) : ℕ := if t = 2 then 1 else 0
def pr (t : ℕ) : ℕ := if t = 3 then 1 else 0

def z3 : List ℚ := [0, 0, 0]

def head1 : AHead :=
  { A := [z3, z3, z3], V := [[0, 1, 0], z3, z3], mask := Mask.strict, m := 24,
    g := [0, 0, 1], gb := -1 / 2 }

def blk : ABlock :=
  { heads := [head1], W1 := [[1, 0, 0]], b1 := [-2], W2 := [[-3], [0], [0]], b2 := z3 }

def net : ANet :=
  { embed := [[0, 0, 0], [2, 0, 0], [0, 1, 0], [2, 0, 1], [2, 0, 0], [0, 0, 0]],
    blocks := [blk], outW := [1, 0, 0], outB := 0 }

/-! ### Ideal values and small facts -/

noncomputable def xhat (w : List ℕ) (j : ℕ) : List ℝ :=
  [((dg (tokAt w j) : ℕ) : ℝ), ((gn (tokAt w j) : ℕ) : ℝ), ((pr (tokAt w j) : ℕ) : ℝ)]

noncomputable def cs (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : List ℕ :=
  head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

noncomputable def sc (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : ℕ → ℝ :=
  fun j => head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i j

noncomputable def att (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (r : List ℚ) (k : ℕ) :
    ℝ :=
  savg fl ex (cs fl p w i) (sc fl p w i) (fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0)

noncomputable def hid (fl : ℝ → ℝ) (p : APert) (y : Vec) : ℝ :=
  Lane4.relu (fl (ardot fl [1, 0, 0] y (p.W1 0 0) 0 0 + asw fl (-2) (p.b1 0 0)))

noncomputable def mo (fl : ℝ → ℝ) (p : APert) (h : ℝ) (r : ℕ) (row : List ℚ) : ℝ :=
  fl (ardot fl row [h] (p.W2 0 r) 0 0 + asw fl 0 (p.b2 0 r))

theorem dg_le (t : ℕ) : dg t ≤ 2 := by unfold dg; split_ifs <;> omega
theorem gn_le (t : ℕ) : gn t ≤ 1 := by unfold gn; split_ifs <;> omega
theorem pr_le (t : ℕ) : pr t ≤ 1 := by unfold pr; split_ifs <;> omega

theorem dgR (t : ℕ) : |((dg t : ℕ) : ℝ)| ≤ 2 := by
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast dg_le t

theorem gnR (t : ℕ) : |((gn t : ℕ) : ℝ)| ≤ 1 := by
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast gn_le t

theorem prR (t : ℕ) : |((pr t : ℕ) : ℝ)| ≤ 1 := by
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast pr_le t

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem cq (n : ℕ) : (((n : ℕ) : ℚ) : ℝ) = (n : ℝ) := by simp

theorem embed_row {t : ℕ} (h : t ≤ 5) :
    net.embed.getD t [] = [((dg t : ℕ) : ℚ), ((gn t : ℕ) : ℚ), ((pr t : ℕ) : ℚ)] := by
  interval_cases t <;> first | rfl | (simp [net, dg, gn, pr]; done) | decide

theorem init_eq (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (j : ℕ) (h : tokAt w j ≤ 5) :
    net.init fl p w j = [asw fl ((dg (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 0),
      asw fl ((gn (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 1),
      asw fl ((pr (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 2)] := by
  show aswRow fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0 = _
  rw [embed_row h]
  rfl

theorem dotQ3 (a b c : ℚ) (x y z : ℝ) :
    dotQ [a, b, c] [x, y, z] = (a : ℝ) * x + (b : ℝ) * y + (c : ℝ) * z := by
  first
    | (simp [dotQ, add_assoc]; done)
    | (unfold dotQ; simp; ring)

theorem dotQ1 (a : ℚ) (x : ℝ) : dotQ [a] [x] = (a : ℝ) * x := by
  simp [dotQ]

theorem dq0 (w : List ℕ) (j : ℕ) : dotQ z3 (xhat w j) = 0 := by
  unfold xhat
  show dotQ [0, 0, 0] _ = 0
  rw [dotQ3]; simp

theorem dq010 (w : List ℕ) (j : ℕ) : dotQ [0, 1, 0] (xhat w j) = ((gn (tokAt w j) : ℕ) : ℝ) := by
  unfold xhat
  rw [dotQ3]; simp

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

theorem absle_of_list3 (a b c : ℚ) (W : ℝ) (ha : |(a : ℝ)| ≤ W) (hb : |(b : ℝ)| ≤ W)
    (hc : |(c : ℝ)| ≤ W) : ∀ x ∈ ([a, b, c] : List ℚ), |(x : ℝ)| ≤ W := by
  intro x hx
  simp at hx
  rcases hx with h | h | h <;> (subst h; assumption)

theorem absle_of_list1 (a : ℚ) (W : ℝ) (ha : |(a : ℝ)| ≤ W) :
    ∀ x ∈ ([a] : List ℚ), |(x : ℝ)| ≤ W := by
  intro x hx
  simp at hx
  subst hx
  exact ha

theorem absSum_cons (a : ℚ) (r : List ℚ) : absSum (a :: r) = |(a : ℝ)| + absSum r := by
  simp [absSum]

theorem absSum_nil : absSum ([] : List ℚ) = 0 := by simp [absSum]

theorem abs_m3 : |(((-3 : ℚ)) : ℝ)| = 3 := by
  have h : (((-3 : ℚ)) : ℝ) = -3 := by norm_num
  rw [h, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]

theorem abs_m2 : |(((-2 : ℚ)) : ℝ)| = 2 := by
  have h : (((-2 : ℚ)) : ℝ) = -2 := by norm_num
  rw [h, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

theorem absSum_100 : absSum ([1, 0, 0] : List ℚ) ≤ 1 := by
  rw [absSum_cons, absSum_cons, absSum_cons, absSum_nil]; norm_num

theorem absSum_010 : absSum ([0, 1, 0] : List ℚ) ≤ 1 := by
  rw [absSum_cons, absSum_cons, absSum_cons, absSum_nil]; norm_num

theorem absSum_m3 : absSum ([-3] : List ℚ) ≤ 3 := by
  rw [absSum_cons, absSum_nil, abs_m3]; norm_num

theorem absSum_0 : absSum ([0] : List ℚ) ≤ 0 := by
  rw [absSum_cons, absSum_nil]; norm_num

theorem z3_W : ∀ a ∈ z3, |(a : ℝ)| ≤ 1 :=
  absle_of_list3 0 0 0 1 (by norm_num) (by norm_num) (by norm_num)

theorem z3_S : absSum z3 ≤ 1 := by
  show absSum ([0, 0, 0] : List ℚ) ≤ 1
  rw [absSum_cons, absSum_cons, absSum_cons, absSum_nil]; norm_num

theorem relu_lip (a b : ℝ) : |Lane4.relu a - Lane4.relu b| ≤ |a - b| := by
  unfold Lane4.relu
  rw [abs_le]
  have hab := abs_le.mp (le_refl |a - b|)
  have hn := abs_nonneg (a - b)
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [max_eq_right ha, max_eq_right hb]; constructor <;> linarith
  · rw [max_eq_right ha, max_eq_left hb]; constructor <;> linarith
  · rw [max_eq_left ha, max_eq_right hb]; constructor <;> linarith
  · rw [max_eq_left ha, max_eq_left hb]; constructor <;> linarith

/-! ### Carry bookkeeping -/

theorem take_succ' (w : List ℕ) (k : ℕ) (hk : k < w.length) :
    w.take (k + 1) = w.take k ++ [w[k]] := by
  first
    | exact List.take_succ_eq_append_getElem hk
    | (rw [List.take_succ, List.getElem?_eq_getElem hk]; rfl)
    | (simp [List.take_succ, hk])

theorem carry_succ (w : List ℕ) (k : ℕ) (hk : k < w.length) :
    carry (w.take (k + 1)) =
      (if cls (tokAt w (k + 1)) = 2 then carry (w.take k) else cls (tokAt w (k + 1))) := by
  rw [take_succ' w k hk, Lane4.Seq.tokAt_succ w k hk]
  unfold carry
  rw [List.foldl_append]
  first | rfl | simp

theorem cls_cases (t : ℕ) (h : 1 ≤ t ∧ t ≤ 5) :
    (pr t = 1 ∧ cls t = 2 ∧ gn t = 0) ∨ (pr t = 0 ∧ cls t = gn t) := by
  obtain ⟨h1, h2⟩ := h
  interval_cases t <;> first | decide | simp [pr, cls, gn]

theorem last_np (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) :
    ∀ k : ℕ, k ≤ w.length → ∃ j, j ≤ k ∧ pr (tokAt w j) = 0 ∧
      (∀ l, j < l → l ≤ k → pr (tokAt w l) = 1) ∧ carry (w.take k) = gn (tokAt w j) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨0, le_refl _, ?_, ?_, ?_⟩
    · simp [Lane4.Seq.tokAt_zero, pr]
    · intro l h1 h2; omega
    · simp [carry, Lane4.Seq.tokAt_zero, gn]
  | succ k ih =>
    intro hk
    have hk' : k < w.length := by omega
    obtain ⟨j, hjk, hj0, hjl, hc⟩ := ih (by omega)
    have htk : tokAt w (k + 1) = w[k] := Lane4.Seq.tokAt_succ w k hk'
    have ht : 1 ≤ tokAt w (k + 1) ∧ tokAt w (k + 1) ≤ 5 := by
      rw [htk]; exact hw _ (List.getElem_mem hk')
    have hcs := carry_succ w k hk'
    rcases cls_cases _ ht with ⟨hp1, hc2, hg0⟩ | ⟨hp0, hcg⟩
    · refine ⟨j, by omega, hj0, ?_, ?_⟩
      · intro l h1 h2
        by_cases hl : l ≤ k
        · exact hjl l h1 hl
        · have : l = k + 1 := by omega
          rw [this]; exact hp1
      · rw [hcs, if_pos hc2]; exact hc
    · refine ⟨k + 1, le_refl _, hp0, ?_, ?_⟩
      · intro l h1 h2; omega
      · have hn2 : ¬ (cls (tokAt w (k + 1)) = 2) := by
          have := gn_le (tokAt w (k + 1)); omega
        rw [hcs, if_neg hn2]; exact hcg

theorem target_eq (w : List ℕ) (i : ℕ) (hi1 : 1 ≤ i) :
    target w i = (dg (tokAt w i) + carry (w.take (i - 1))) % 3 := by
  unfold target
  have h : w.getD (i - 1) 0 = tokAt w i := by
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    simp [tokAt]
  rw [h]

theorem ideal_val (t c : ℕ) (hc : c ≤ 1) (ht : 1 ≤ t ∧ t ≤ 5) :
    ((dg t : ℕ) : ℝ) + (c : ℝ) + -3 * Lane4.relu (((dg t : ℕ) : ℝ) + (c : ℝ) - 2) =
      (((dg t + c) % 3 : ℕ) : ℝ) := by
  obtain ⟨h1, h2⟩ := ht
  interval_cases t <;> interval_cases c <;> norm_num [dg, Lane4.relu, max_def]

/-! ### Context -/

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

theorem ucon (ev : Ctx u η M fl ex p w) {c : ℝ} (h0 : 0 ≤ c) : u * c ≤ c / 16000000 := by
  have h : (1 : ℝ) / 2 ^ 24 ≤ 1 / 16000000 := by norm_num
  calc u * c ≤ 1 / 2 ^ 24 * c := mul_le_mul_of_nonneg_right ev.hu1 h0
    _ ≤ 1 / 16000000 * c := mul_le_mul_of_nonneg_right h h0
    _ = c / 16000000 := by ring

theorem eta9 (ev : Ctx u η M fl ex p w) : η ≤ 1 / 1000000000 :=
  le_trans (eta_tiny ev.hη1) (by norm_num)

/-- Rounding a value within `e` of `t`. -/
theorem flN (ev : Ctx u η M fl ex p w) {x t e B : ℝ} (hx : |x - t| ≤ e) (hB : |x| ≤ B)
    (hB1 : B ≤ 1000) : |fl x - t| ≤ e + (B / 16000000 + 1 / 1000000000) := by
  have hBM : B ≤ M := le_trans hB1 (ev.range 1000 (by norm_num))
  have h := ev.hr.near ev.hu0 hx hB hBM
  have h2 := ucon ev (le_trans (abs_nonneg _) hB)
  have h3 := eta9 ev
  linarith

/-- A rounded sum of two approximations. -/
theorem addN (ev : Ctx u η M fl ex p w) {x s t s' e1 e2 Bt : ℝ} (hx : |x - t| ≤ e1)
    (hs : |s - s'| ≤ e2) (hB : |t + s'| ≤ Bt) (hB1 : Bt + e1 + e2 ≤ 1000) :
    |fl (x + s) - (t + s')| ≤ e1 + e2 + ((Bt + e1 + e2) / 16000000 + 1 / 1000000000) := by
  have h1 : |x + s - (t + s')| ≤ e1 + e2 := by
    have := abs_add_le (x - t) (s - s')
    have e : x - t + (s - s') = x + s - (t + s') := by ring
    rw [e] at this; linarith
  have h2 : |x + s| ≤ Bt + e1 + e2 := by
    have := abs_add_le (t + s') (x + s - (t + s'))
    have e : t + s' + (x + s - (t + s')) = x + s := by ring
    rw [e] at this; linarith
  have := flN ev h1 h2 hB1
  linarith

/-- A stored weight of size at most 3 is within 1/500 of its written value. -/
theorem asw_c (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149)
    (hM : 5 ≤ M) (a : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 1000) (ha : |(a : ℝ)| ≤ 3) :
    |asw fl a d - (a : ℝ)| ≤ 1 / 500 := by
  have h := asw_near hr hu0 a hd (by linarith)
  have h1 : u * (|(a : ℝ)| + 1 / 1000) ≤ 1 / 2 ^ 24 * 4 :=
    mul_le_mul hu (by linarith) (by positivity) (by positivity)
  have h2 := eta_tiny hη
  have h3 : (1 : ℝ) / 2 ^ 24 * 4 + 1 / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

theorem asw_nat (ev : Ctx u η M fl ex p w) (n : ℕ) (hn : n ≤ 2) {d : ℝ} (hd : |d| ≤ 1 / 1000) :
    |asw fl (n : ℚ) d - (n : ℝ)| ≤ 1 / 500 := by
  have hn3 : (n : ℝ) ≤ 3 := by
    have : n ≤ 3 := by omega
    exact_mod_cast this
  have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 5 (by norm_num)) (n : ℚ) hd
    (by rw [cq, abs_of_nonneg (Nat.cast_nonneg _)]; exact hn3)
  rwa [cq] at h

theorem asw0 (ev : Ctx u η M fl ex p w) {d : ℝ} (hd : |d| ≤ 1 / 1000) :
    |asw fl 0 d| ≤ 1 / 500 := by
  have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 5 (by norm_num)) (0 : ℚ) hd (by simp)
  simpa using h

/-- Rounded dot product of a short written row (at most 3 entries) with an approximate vector. -/
theorem zard (ev : Ctx u η M fl ex p w) {r : List ℚ} {x xh : List ℝ} {W X e S : ℝ}
    {d : ℕ → ℝ} (hC : Close x xh e X) (hl : r.length = x.length) (hl3 : r.length ≤ 3)
    (hd : ∀ k, |d k| ≤ 1 / 1000) (hW : ∀ a ∈ r, |(a : ℝ)| ≤ W) (hW0 : 0 ≤ W) (hX : 0 ≤ X)
    (he : 0 ≤ e) (hS : absSum r ≤ S) (hT : (W + 1) * (X + e + 1) ≤ 2 ^ 20) :
    |ardot fl r x d 0 0 - dotQ r xh| ≤
        S * e + 3 / 1000 * (X + e) + 3 * ((W + 1) * (X + e + 1)) / 65536 + 1 / 10 ^ 9
      ∧ |ardot fl r x d 0 0| ≤ 6 * ((W + 1) * (X + e + 1)) := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have k1 := ardot_near_abs u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1
    (by norm_num) (by norm_num) r x xh d W X e hl (by omega) hC hd hW hW0 hX he hT hM30
  have k2 := (ardot_near u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1
    (by norm_num) (by norm_num) r x xh d W X e hl (by omega) hC hd hW hW0 hX he hT hM30).2
  have hlen : (r.length : ℝ) ≤ 3 := by exact_mod_cast hl3
  have hP : 0 ≤ (W + 1) * (X + e + 1) := mul_nonneg (by linarith) (by linarith)
  have hXe : 0 ≤ X + e := by linarith
  have t0 : absSum r * e ≤ S * e := mul_le_mul_of_nonneg_right hS he
  have t1 : (r.length : ℝ) * (1 / 1000) * (X + e) ≤ 3 * (1 / 1000) * (X + e) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlen (by norm_num)) hXe
  have t2 : (r.length : ℝ) * (W + 1) * (X + e + 1) ≤ 3 * ((W + 1) * (X + e + 1)) := by
    calc (r.length : ℝ) * (W + 1) * (X + e + 1) = (r.length : ℝ) * ((W + 1) * (X + e + 1)) := by ring
      _ ≤ 3 * ((W + 1) * (X + e + 1)) := mul_le_mul_of_nonneg_right hlen hP
  have t3 : (r.length : ℝ) * (W + 1) * (X + e + 1) * 2 ≤ 6 * ((W + 1) * (X + e + 1)) := by
    linarith
  have h16 : (2 : ℝ) ^ 16 = 65536 := by norm_num
  have h100 : (1 : ℝ) / 2 ^ 100 ≤ 1 / 10 ^ 9 := by norm_num
  rw [h16] at k1
  constructor
  · linarith
  · linarith

/-! ### Step 1: the starting state -/

theorem init_ent (ev : Ctx u η M fl ex p w) (j : ℕ) :
    ∃ a b c : ℝ, net.init fl p w j = [a, b, c] ∧
      |a - ((dg (tokAt w j) : ℕ) : ℝ)| ≤ 1 / 500 ∧ |b - ((gn (tokAt w j) : ℕ) : ℝ)| ≤ 1 / 500 ∧
      |c - ((pr (tokAt w j) : ℕ) : ℝ)| ≤ 1 / 500 := by
  have ht := tok_le w ev.hw j
  refine ⟨_, _, _, init_eq fl p w j ht, ?_, ?_, ?_⟩
  · exact asw_nat ev _ (dg_le _) (ev.hp.E (tokAt w j) 0)
  · exact asw_nat ev _ (by have := gn_le (tokAt w j); omega) (ev.hp.E (tokAt w j) 1)
  · exact asw_nat ev _ (by have := pr_le (tokAt w j); omega) (ev.hp.E (tokAt w j) 2)

theorem init_close (ev : Ctx u η M fl ex p w) (j : ℕ) :
    (net.init fl p w j).length = 3 ∧ Close (net.init fl p w j) (xhat w j) (1 / 500) 2 := by
  obtain ⟨a, b, c, hx, ha, hb, hc⟩ := init_ent ev j
  rw [hx]
  refine ⟨rfl, ?_⟩
  unfold xhat
  exact close3 ha hb hc (dgR _) (le_trans (gnR _) (by norm_num)) (le_trans (prR _) (by norm_num))

/-- A written row of size at most 1 applied to a stored state. -/
theorem val_near (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr3 : r.length = 3)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (hS : absSum r ≤ 1) (j : ℕ) (d : ℕ → ℝ)
    (hd : ∀ c, |d c| ≤ 1 / 1000) :
    |ardot fl r (net.init fl p w j) d 0 0 - dotQ r (xhat w j)| ≤ 1 / 100 := by
  obtain ⟨hlen, hC⟩ := init_close ev j
  have h := zard ev (r := r) (W := 1) (S := 1) (d := d) hC (by rw [hlen, hr3]) (by omega) hd hW
    (by norm_num) (by norm_num) (by norm_num) hS (by norm_num)
  exact le_trans h.1 (by norm_num)

/-! ### Step 2: the gate -/

theorem gate_ard (ev : Ctx u η M fl ex p w) (j : ℕ) :
    |ardot fl head1.g (net.init fl p w j) (p.g 0 0) 0 0 - ((pr (tokAt w j) : ℕ) : ℝ)| ≤ 1 / 100 ∧
    |ardot fl head1.g (net.init fl p w j) (p.g 0 0) 0 0| ≤ 100 := by
  obtain ⟨hlen, hC⟩ := init_close ev j
  have h := zard ev (r := head1.g) (W := 1) (S := 1) (d := p.g 0 0) hC (by rw [hlen]; rfl)
    (by decide) (ev.hp.g 0 0) (absle_of_list3 0 0 1 1 (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by
      show absSum ([0, 0, 1] : List ℚ) ≤ 1
      rw [absSum_cons, absSum_cons, absSum_cons, absSum_nil]; norm_num)
    (by norm_num)
  have hq : dotQ head1.g (xhat w j) = ((pr (tokAt w j) : ℕ) : ℝ) := by
    show dotQ [0, 0, 1] (xhat w j) = _
    unfold xhat
    rw [dotQ3]; simp
  rw [hq] at h
  exact ⟨le_trans h.1 (by norm_num), le_trans h.2 (by norm_num)⟩

theorem gate_eq_zero (ev : Ctx u η M fl ex p w) (j : ℕ) (hp : pr (tokAt w j) = 0) :
    head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) = 0 := by
  obtain ⟨h1, h2⟩ := gate_ard ev j
  have hgb : ((head1.gb : ℚ) : ℝ) = -1 / 2 := by norm_num [head1]
  have hb := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 5 (by norm_num)) head1.gb
    (ev.hp.gb 0 0) (by rw [hgb]; norm_num)
  rw [hgb] at hb
  simp only [hp, Nat.cast_zero, sub_zero] at h1
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨hba, hbb⟩ := abs_le.mp hb
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  have hM3 : (200 : ℝ) ≤ M := ev.range 200 (by norm_num)
  unfold AHead.gate
  exact relu_fl_zero ev.hr (by linarith) (by linarith)

theorem gate_pos (ev : Ctx u η M fl ex p w) (j : ℕ) (hp : pr (tokAt w j) = 1) :
    0 < head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) := by
  obtain ⟨h1, h2⟩ := gate_ard ev j
  have hgb : ((head1.gb : ℚ) : ℝ) = -1 / 2 := by norm_num [head1]
  have hb := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 5 (by norm_num)) head1.gb
    (ev.hp.gb 0 0) (by rw [hgb]; norm_num)
  rw [hgb] at hb
  simp only [hp, Nat.cast_one] at h1
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨hba, hbb⟩ := abs_le.mp hb
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  have hB : |ardot fl head1.g (net.init fl p w j) (p.g 0 0) 0 0 + asw fl head1.gb (p.gb 0 0)|
      ≤ 102 := by
    rw [abs_le]; constructor <;> linarith
  have hfl := ev.hr.lower ev.hu0 hB (ev.range 102 (by norm_num))
  have hu' := ucon ev (by norm_num : (0 : ℝ) ≤ 102)
  have hη' := eta9 ev
  unfold AHead.gate Lane4.relu
  exact lt_max_of_lt_left (by linarith)

theorem mem_cs (ev : Ctx u η M fl ex p w) (i j : ℕ) :
    j ∈ cs fl p w i ↔ j < i ∧ pr (tokAt w j) = 0 := by
  unfold cs
  rw [AHead.mem_cands]
  have hm : head1.mask = Mask.strict := rfl
  rw [hm, Lane4.Seq.mem_cand_strict]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra hne
    have hp1 : pr (tokAt w j) = 1 := by have := pr_le (tokAt w j); omega
    exact (gate_pos ev j hp1).ne' h2
  · rintro ⟨h1, h2⟩
    exact ⟨h1, gate_eq_zero ev j h2⟩

theorem cs_nodup (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : (cs fl p w i).Nodup :=
  AHead.cands_nodup head1 fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

theorem cs_len (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (hi : i ≤ w.length) :
    (cs fl p w i).length ≤ w.length + 1 := by
  have h1 : (cs fl p w i).length ≤ (cand Mask.strict (w.length + 1) i).length :=
    List.length_filter_le _ _
  have h2 : (cand Mask.strict (w.length + 1) i).length = i := by simp [cand]
  omega

/-! ### Step 3: scores -/

theorem content_small (ev : Ctx u η M fl ex p w) (i k : ℕ) :
    |Lane4.RSeq.pdot fl (net.init fl p w i)
        (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) 0| ≤ 1 / 10 := by
  obtain ⟨hli, hCi⟩ := init_close ev i
  obtain ⟨hlk, hCk⟩ := init_close ev k
  have hrow : ∀ r : ℕ, |ardot fl z3 (net.init fl p w k) (p.A 0 0 r) 0 0 - 0| ≤ 1 / 75 := by
    intro r
    have h := val_near ev z3 rfl z3_W z3_S k (p.A 0 0 r) (ev.hp.A 0 0 r)
    rw [dq0] at h
    exact le_trans h (by norm_num)
  have hy : armat fl head1.A (net.init fl p w k) (p.A 0 0) 0 =
      [ardot fl z3 (net.init fl p w k) (p.A 0 0 0) 0 0,
       ardot fl z3 (net.init fl p w k) (p.A 0 0 1) 0 0,
       ardot fl z3 (net.init fl p w k) (p.A 0 0 2) 0 0] := rfl
  have hCy : Close (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) [0, 0, 0] (1 / 75) 0 := by
    rw [hy]
    exact close3 (hrow 0) (hrow 1) (hrow 2) (by norm_num) (by norm_num) (by norm_num)
  have hlen_y : (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0).length = 3 := by
    simp [hy]
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  obtain ⟨p1, -⟩ := pdot_near u η M fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (net.init fl p w i)
    (xhat w i) (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) [0, 0, 0] 2 0 (1 / 500) (1 / 75)
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

/-! ### Step 4: the head returns the value at the winner -/

theorem row_attn (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr3 : r.length = 3)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (hS : absSum r ≤ 1) (hq : ∀ j, |dotQ r (xhat w j)| ≤ 1)
    (k : ℕ) (i j : ℕ) (hj : j ∈ cs fl p w i) (hmax : ∀ k' ∈ cs fl p w i, k' ≠ j → k' < j)
    (hi : i ≤ w.length) :
    |att fl ex p w i r k - dotQ r (xhat w j)| ≤ 1 / 40 := by
  have hlen := cs_len fl p w i hi
  have hji : j < i := ((mem_cs ev i j).mp hj).1
  have hgap : ∀ k' ∈ cs fl p w i, k' ≠ j →
      sc fl p w i k' ≤ sc fl p w i j - 16 * ((ndist j k' : ℕ) : ℝ) := by
    intro k' hk' hne
    have hlt : k' < j := hmax k' hk' hne
    rw [ndist_cast]
    have hg := score_gap ev i j k' (by omega) (by omega) hlt
    have h1 : (k' : ℝ) + 1 ≤ (j : ℝ) := by
      have h : k' + 1 ≤ j := hlt
      exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    exact hg
  have hS' : ∀ k' ∈ cs fl p w i, |sc fl p w i k'| ≤ 28 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k' hk'
    have := ((mem_cs ev i k').mp hk').1
    exact score_abs ev i k' (by omega) (by omega)
  have hSM : 2 * (28 * ((w.length + 1 : ℕ) : ℝ)) ≤ M := by
    have := ev.rangeN 56 (by norm_num) (by norm_num)
    linarith
  have hf : ∀ k' ∈ cs fl p w i,
      |ardot fl r (net.init fl p w k') (p.V 0 0 k) 0 0| ≤ (101 / 100 : ℝ) := by
    intro k' _
    have h1 := val_near ev r hr3 hW hS k' (p.V 0 0 k) (ev.hp.V 0 0 k)
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h2a, h2b⟩ := abs_le.mp (hq k')
    rw [abs_le]; constructor <;> linarith
  have hBM : 4 * (101 / 100 : ℝ) + 4 ≤ M := by
    have := ev.range 13 (by norm_num)
    linarith
  obtain ⟨hs1, -⟩ := soft_near (s := sc fl p w i)
    (f := fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0) ev.hr ev.he ev.hu0 ev.hu1
    ev.hη0 ev.hη1 (cs_nodup fl p w i) hlen ev.hn ev.hnη hj hgap hS' hSM hf hBM
  have hs1' : |att fl ex p w i r k - ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0|
      ≤ (101 / 100 : ℝ) / 100 + 1 / 2 ^ 90 := hs1
  have hv := val_near ev r hr3 hW hS j (p.V 0 0 k) (ev.hp.V 0 0 k)
  have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 1000000 := by norm_num
  have h3 := abs_sub_le (att fl ex p w i r k)
    (ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0) (dotQ r (xhat w j))
  linarith

/-! ### Step 5: the forward pass after the head -/

theorem attn_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
      (net.init fl p w) i =
    [att fl ex p w i [0, 1, 0] 0, att fl ex p w i z3 1, att fl ex p w i z3 2] := rfl

theorem run_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (a b c y0 y1 y2 : ℝ)
    (hx : net.init fl p w i = [a, b, c])
    (h0 : y0 = fl (a + att fl ex p w i [0, 1, 0] 0))
    (h1 : y1 = fl (b + att fl ex p w i z3 1))
    (h2 : y2 = fl (c + att fl ex p w i z3 2)) :
    net.run fl ex p w i =
      [fl (y0 + mo fl p (hid fl p [y0, y1, y2]) 0 [-3]),
       fl (y1 + mo fl p (hid fl p [y0, y1, y2]) 1 [0]),
       fl (y2 + mo fl p (hid fl p [y0, y1, y2]) 2 [0])] := by
  have hY : Lane4.RSeq.radd fl (net.init fl p w i)
      (head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
        (net.init fl p w) i) = [y0, y1, y2] := by
    rw [hx, attn_eq, h0, h1, h2]; rfl
  have e : net.run fl ex p w i =
      Lane4.RSeq.radd fl
        (Lane4.RSeq.radd fl (net.init fl p w i)
          (head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
            (net.init fl p w) i))
        (araffine fl blk.W2 blk.b2
          ((araffine fl blk.W1 blk.b1
            (Lane4.RSeq.radd fl (net.init fl p w i)
              (head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0)
                (w.length + 1) (net.init fl p w) i))
            (p.W1 0) (p.b1 0) 0).map Lane4.relu)
          (p.W2 0) (p.b2 0) 0) := rfl
  rw [e, hY]
  rfl

theorem mo_m3 (ev : Ctx u η M fl ex p w) {h hs : ℝ} (hh : |h - hs| ≤ 1 / 24) (hs1 : |hs| ≤ 1) :
    |mo fl p h 0 [-3] - (-3 * hs)| ≤ 3 / 20 := by
  unfold mo
  have hC : Close [h] [hs] (1 / 24) 1 := close1 hh hs1
  have a1 := zard ev (r := [-3]) (W := 3) (S := 3) (d := p.W2 0 0) hC rfl (by simp)
    (ev.hp.W2 0 0) (absle_of_list1 (-3) 3 abs_m3.le) (by norm_num) (by norm_num) (by norm_num)
    absSum_m3 (by norm_num)
  rw [dotQ1] at a1
  have hq : (((-3 : ℚ)) : ℝ) = -3 := by norm_num
  rw [hq] at a1
  obtain ⟨a1, a2⟩ := a1
  have a1' : |ardot fl [-3] [h] (p.W2 0 0) 0 0 - (-3 * hs)| ≤ 129 / 1000 :=
    le_trans a1 (by norm_num)
  have a2' : |ardot fl [-3] [h] (p.W2 0 0) 0 0| ≤ 50 := le_trans a2 (by norm_num)
  have hb := asw0 ev (ev.hp.b2 0 0)
  have hx : |ardot fl [-3] [h] (p.W2 0 0) 0 0 + asw fl 0 (p.b2 0 0) - (-3 * hs)| ≤ 131 / 1000 := by
    obtain ⟨u1, u2⟩ := abs_le.mp a1'
    obtain ⟨v1, v2⟩ := abs_le.mp hb
    rw [abs_le]; constructor <;> linarith
  have hB : |ardot fl [-3] [h] (p.W2 0 0) 0 0 + asw fl 0 (p.b2 0 0)| ≤ 52 := by
    obtain ⟨u1, u2⟩ := abs_le.mp a2'
    obtain ⟨v1, v2⟩ := abs_le.mp hb
    rw [abs_le]; constructor <;> linarith
  exact le_trans (flN ev hx hB (by norm_num)) (by norm_num)

theorem mo_zero (ev : Ctx u η M fl ex p w) (r : ℕ) {h hs : ℝ} (hh : |h - hs| ≤ 1 / 24)
    (hs1 : |hs| ≤ 1) : |mo fl p h r [0] - 0| ≤ 1 / 150 := by
  unfold mo
  have hC : Close [h] [hs] (1 / 24) 1 := close1 hh hs1
  have a1 := zard ev (r := [0]) (W := 0) (S := 0) (d := p.W2 0 r) hC rfl (by simp)
    (ev.hp.W2 0 r) (absle_of_list1 0 0 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    absSum_0 (by norm_num)
  have hq : dotQ [0] [hs] = 0 := by rw [dotQ1]; simp
  rw [hq, sub_zero] at a1
  obtain ⟨a1, a2⟩ := a1
  have a1' : |ardot fl [0] [h] (p.W2 0 r) 0 0| ≤ 33 / 10000 := le_trans a1 (by norm_num)
  have a2' : |ardot fl [0] [h] (p.W2 0 r) 0 0| ≤ 13 := le_trans a2 (by norm_num)
  have hb := asw0 ev (ev.hp.b2 0 r)
  have hx : |ardot fl [0] [h] (p.W2 0 r) 0 0 + asw fl 0 (p.b2 0 r) - 0| ≤ 33 / 10000 + 1 / 500 := by
    obtain ⟨u1, u2⟩ := abs_le.mp a1'
    obtain ⟨v1, v2⟩ := abs_le.mp hb
    rw [abs_le]; constructor <;> linarith
  have hB : |ardot fl [0] [h] (p.W2 0 r) 0 0 + asw fl 0 (p.b2 0 r)| ≤ 20 := by
    obtain ⟨u1, u2⟩ := abs_le.mp a2'
    obtain ⟨v1, v2⟩ := abs_le.mp hb
    rw [abs_le]; constructor <;> linarith
  exact le_trans (flN ev hx hB (by norm_num)) (by norm_num)

theorem post_head (ev : Ctx u η M fl ex p w) (i : ℕ) {a b c : ℝ}
    (hx : net.init fl p w i = [a, b, c])
    {D G P c0 tv : ℝ} (hD0 : 0 ≤ D) (hD2 : D ≤ 2) (hG0 : 0 ≤ G) (hG1 : G ≤ 1)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hc00 : 0 ≤ c0) (hc01 : c0 ≤ 1)
    (ha : |a - D| ≤ 1 / 500) (hb : |b - G| ≤ 1 / 500) (hc : |c - P| ≤ 1 / 500)
    (hr0 : |att fl ex p w i [0, 1, 0] 0 - c0| ≤ 1 / 40)
    (hr1 : |att fl ex p w i z3 1 - 0| ≤ 1 / 40)
    (hr2 : |att fl ex p w i z3 2 - 0| ≤ 1 / 40)
    (htv : D + c0 + -3 * Lane4.relu (D + c0 - 2) = tv) (htv0 : 0 ≤ tv) (htv2 : tv ≤ 2) :
    |net.out fl ex p w i - tv| ≤ 1 / 4 := by
  obtain ⟨y0, hy0⟩ : ∃ y0, y0 = fl (a + att fl ex p w i [0, 1, 0] 0) := ⟨_, rfl⟩
  obtain ⟨y1, hy1⟩ : ∃ y1, y1 = fl (b + att fl ex p w i z3 1) := ⟨_, rfl⟩
  obtain ⟨y2, hy2⟩ : ∃ y2, y2 = fl (c + att fl ex p w i z3 2) := ⟨_, rfl⟩
  have hrun := run_eq fl ex p w i a b c y0 y1 y2 hx hy0 hy1 hy2
  -- the state after the head
  have e0 : |y0 - (D + c0)| ≤ 1 / 35 := by
    rw [hy0]
    exact le_trans (addN ev (Bt := 3) ha hr0
      (by rw [abs_le]; constructor <;> linarith) (by norm_num)) (by norm_num)
  have e1 : |y1 - G| ≤ 1 / 35 := by
    rw [hy1]
    have h := addN ev (Bt := 1) hb hr1 (by rw [abs_le]; constructor <;> linarith) (by norm_num)
    rw [add_zero] at h
    exact le_trans h (by norm_num)
  have e2 : |y2 - P| ≤ 1 / 35 := by
    rw [hy2]
    have h := addN ev (Bt := 1) hc hr2 (by rw [abs_le]; constructor <;> linarith) (by norm_num)
    rw [add_zero] at h
    exact le_trans h (by norm_num)
  have hCY : Close [y0, y1, y2] [D + c0, G, P] (1 / 35) 3 :=
    close3 e0 e1 e2 (by rw [abs_le]; constructor <;> linarith)
      (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith)
  -- the hidden neuron
  have hasw2 : |asw fl (-2) (p.b1 0 0) - (-2)| ≤ 1 / 500 := by
    have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 5 (by norm_num)) (-2 : ℚ)
      (ev.hp.b1 0 0) (by rw [abs_m2]; norm_num)
    have hc2 : (((-2 : ℚ)) : ℝ) = -2 := by norm_num
    rwa [hc2] at h
  have hard1 := zard ev (r := [1, 0, 0]) (W := 1) (S := 1) (d := p.W1 0 0) hCY rfl (by simp)
    (ev.hp.W1 0 0) (absle_of_list3 1 0 0 1 (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) absSum_100 (by norm_num)
  have hq1 : dotQ [1, 0, 0] [D + c0, G, P] = D + c0 := by rw [dotQ3]; simp
  rw [hq1] at hard1
  obtain ⟨hd1, hd2⟩ := hard1
  have hd1' : |ardot fl [1, 0, 0] [y0, y1, y2] (p.W1 0 0) 0 0 - (D + c0)| ≤ 381 / 10000 :=
    le_trans hd1 (by norm_num)
  have hd2' : |ardot fl [1, 0, 0] [y0, y1, y2] (p.W1 0 0) 0 0| ≤ 49 := le_trans hd2 (by norm_num)
  have hargerr : |ardot fl [1, 0, 0] [y0, y1, y2] (p.W1 0 0) 0 0 + asw fl (-2) (p.b1 0 0)
      - (D + c0 - 2)| ≤ 401 / 10000 := by
    obtain ⟨u1, u2⟩ := abs_le.mp hd1'
    obtain ⟨v1, v2⟩ := abs_le.mp hasw2
    rw [abs_le]; constructor <;> linarith
  have hargB : |ardot fl [1, 0, 0] [y0, y1, y2] (p.W1 0 0) 0 0 + asw fl (-2) (p.b1 0 0)| ≤ 52 := by
    obtain ⟨u1, u2⟩ := abs_le.mp hd2'
    obtain ⟨v1, v2⟩ := abs_le.mp hasw2
    rw [abs_le]; constructor <;> linarith
  have hfl1 := flN ev hargerr hargB (by norm_num)
  have hh : |hid fl p [y0, y1, y2] - Lane4.relu (D + c0 - 2)| ≤ 1 / 24 := by
    unfold hid
    exact le_trans (relu_lip _ _) (le_trans hfl1 (by norm_num))
  have hs0 : 0 ≤ Lane4.relu (D + c0 - 2) := by unfold Lane4.relu; exact le_max_right _ _
  have hs1 : Lane4.relu (D + c0 - 2) ≤ 1 := by
    unfold Lane4.relu; exact max_le (by linarith) (by norm_num)
  have hs1' : |Lane4.relu (D + c0 - 2)| ≤ 1 := by
    rw [abs_of_nonneg hs0]; exact hs1
  -- the MLP output
  have hm0 := mo_m3 ev hh hs1'
  have hm1 := mo_zero ev 1 hh hs1'
  have hm2 := mo_zero ev 2 hh hs1'
  have hz0 : |fl (y0 + mo fl p (hid fl p [y0, y1, y2]) 0 [-3]) - tv| ≤ 1 / 5 := by
    have h := addN ev (Bt := 2) e0 hm0 (by rw [htv, abs_of_nonneg htv0]; exact htv2)
      (by norm_num)
    rw [htv] at h
    exact le_trans h (by norm_num)
  have hz1 : |fl (y1 + mo fl p (hid fl p [y0, y1, y2]) 1 [0]) - G| ≤ 1 / 5 := by
    have h := addN ev (Bt := 1) e1 hm1 (by rw [abs_le]; constructor <;> linarith) (by norm_num)
    rw [add_zero] at h
    exact le_trans h (by norm_num)
  have hz2 : |fl (y2 + mo fl p (hid fl p [y0, y1, y2]) 2 [0]) - P| ≤ 1 / 5 := by
    have h := addN ev (Bt := 1) e2 hm2 (by rw [abs_le]; constructor <;> linarith) (by norm_num)
    rw [add_zero] at h
    exact le_trans h (by norm_num)
  have hCZ := close3 (X := 2) hz0 hz1 hz2 (by rw [abs_le]; constructor <;> linarith)
    (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith)
  -- the read-out
  have hard3 := zard ev (r := net.outW) (W := 1) (S := 1) (d := p.oW) hCZ (by simp [net])
    (by simp [net]) ev.hp.oW (absle_of_list3 1 0 0 1 (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) absSum_100 (by norm_num)
  have hq3 : dotQ net.outW [tv, G, P] = tv := by
    show dotQ [1, 0, 0] [tv, G, P] = tv
    rw [dotQ3]; simp
  rw [hq3] at hard3
  obtain ⟨hf1, hf2⟩ := hard3
  have hf1' := le_trans hf1 (by norm_num : _ ≤ (207 / 1000 : ℝ))
  have hf2' := le_trans hf2 (by norm_num : _ ≤ (39 : ℝ))
  have h0 : ((net.outB : ℚ) : ℝ) = 0 := by simp [net]
  have hob : |asw fl net.outB p.oB| ≤ 1 / 500 := by
    have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 5 (by norm_num)) net.outB ev.hp.oB
      (by rw [h0]; norm_num)
    rwa [h0, sub_zero] at h
  unfold ANet.out
  rw [hrun]
  refine le_trans (flN ev (t := tv) (e := 21 / 100) (B := 60) ?_ ?_ (by norm_num)) (by norm_num)
  · obtain ⟨u1, u2⟩ := abs_le.mp hf1'
    obtain ⟨v1, v2⟩ := abs_le.mp hob
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨u1, u2⟩ := abs_le.mp hf2'
    obtain ⟨v1, v2⟩ := abs_le.mp hob
    rw [abs_le]; constructor <;> linarith

/-! ### The theorem -/

theorem out_near (ev : Ctx u η M fl ex p w) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    |net.out fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  obtain ⟨a, b, c, hx, ha, hb, hc⟩ := init_ent ev i
  obtain ⟨j, hjk, hj0, hjl, hcar⟩ := last_np w ev.hw (i - 1) (by omega)
  have hjmem : j ∈ cs fl p w i := (mem_cs ev i j).mpr ⟨by omega, hj0⟩
  have hmax : ∀ k' ∈ cs fl p w i, k' ≠ j → k' < j := by
    intro k' hk' hne
    obtain ⟨h1, h2⟩ := (mem_cs ev i k').mp hk'
    by_contra hnl
    have h3 : pr (tokAt w k') = 1 := hjl k' (by omega) (by omega)
    omega
  have r0 := row_attn ev [0, 1, 0] rfl
    (absle_of_list3 0 1 0 1 (by norm_num) (by norm_num) (by norm_num)) absSum_010
    (fun j' => by rw [dq010]; exact gnR _) 0 i j hjmem hmax hi
  rw [dq010] at r0
  have r1 := row_attn ev z3 rfl z3_W z3_S (fun j' => by rw [dq0]; norm_num) 1 i j hjmem hmax hi
  rw [dq0] at r1
  have r2 := row_attn ev z3 rfl z3_W z3_S (fun j' => by rw [dq0]; norm_num) 2 i j hjmem hmax hi
  rw [dq0] at r2
  have htok : 1 ≤ tokAt w i ∧ tokAt w i ≤ 5 := by
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [Lane4.Seq.tokAt_succ w k (by omega)]
    exact ev.hw _ (List.getElem_mem (by omega))
  have hc01 : gn (tokAt w j) ≤ 1 := gn_le _
  have hval := ideal_val (tokAt w i) (gn (tokAt w j)) hc01 htok
  rw [target_eq w i hi1, hcar]
  have hmod : (dg (tokAt w i) + gn (tokAt w j)) % 3 ≤ 2 := by omega
  refine post_head ev i hx (D := ((dg (tokAt w i) : ℕ) : ℝ)) (G := ((gn (tokAt w i) : ℕ) : ℝ))
    (P := ((pr (tokAt w i) : ℕ) : ℝ)) (c0 := ((gn (tokAt w j) : ℕ) : ℝ))
    (tv := (((dg (tokAt w i) + gn (tokAt w j)) % 3 : ℕ) : ℝ))
    (Nat.cast_nonneg _) (by exact_mod_cast dg_le _) (Nat.cast_nonneg _)
    (by exact_mod_cast gn_le _) (Nat.cast_nonneg _) (by exact_mod_cast pr_le _)
    (Nat.cast_nonneg _) (by exact_mod_cast gn_le _) ha hb hc r0 r1 r2 hval (Nat.cast_nonneg _)
    (by exact_mod_cast hmod)

end Steps

theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη1 p hp w hw hn hnη hM i hi1 hi
  have ctx : Ctx u η M fl ex p w := ⟨hr, he, hu0, hu1, hη0, hη1, hp, hw, hn, hnη, hM⟩
  exact out_near ctx i hi1 hi

end Lane4.Case
