namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

/-! ### The network: state `[flag, value, res]`; flag 1 = unmarked, 0 = marked.
Gate `flag - 1/2 ≤ 0` keeps only marked keys; causal mask; slope 24 makes the LAST candidate
win; value row 2 copies `value` into `res`; read-out reads `res`. -/

def Fl (t : ℕ) : ℚ := if val t = 0 then 1 else 0

def z3 : List ℚ := [0, 0, 0]

def head1 : AHead :=
  { A := [z3, z3, z3], V := [z3, z3, [0, 1, 0]], mask := Mask.causal, m := 24,
    g := [1, 0, 0], gb := -1 / 2 }

def blk : ABlock :=
  { heads := [head1], W1 := [], b1 := [], W2 := [[], [], []], b2 := z3 }

def net : ANet :=
  { embed := [[1, 0, 0], [1, 0, 0], [0, 3, 0], [0, 2, 0], [1, 0, 0], [0, 1, 0]],
    blocks := [blk], outW := [0, 0, 1], outB := 0 }

/-! ### Pure facts -/

theorem val_le (t : ℕ) : val t ≤ 3 := by
  unfold val; split_ifs <;> omega

theorem Fl_pos {t : ℕ} (h : val t = 0) : Fl t = 1 := by simp [Fl, h]
theorem Fl_neg {t : ℕ} (h : val t ≠ 0) : Fl t = 0 := by simp [Fl, h]

theorem Fl_abs (t : ℕ) : |((Fl t : ℚ) : ℝ)| ≤ 1 := by
  unfold Fl; split_ifs <;> simp

theorem val_abs (t : ℕ) : |((val t : ℕ) : ℝ)| ≤ 3 := by
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast val_le t

theorem val_cast_abs (t : ℕ) : |((((val t : ℕ) : ℚ)) : ℝ)| ≤ 3 := by
  rw [Rat.cast_natCast]; exact val_abs t

theorem last_marked (w : List ℕ) : ∀ i, i ≤ w.length →
    ((∀ j, 1 ≤ j → j ≤ i → val (tokAt w j) = 0) ∧ lastv (w.take i) = 0) ∨
    (∃ j, 1 ≤ j ∧ j ≤ i ∧ val (tokAt w j) ≠ 0 ∧
      (∀ k, j < k → k ≤ i → val (tokAt w k) = 0) ∧ lastv (w.take i) = val (tokAt w j)) := by
  intro i
  induction i with
  | zero =>
    intro _
    left
    refine ⟨fun j h1 h2 => by omega, ?_⟩
    simp [lastv]
  | succ i ih =>
    intro hi
    have hlt : i < w.length := by omega
    have ht : tokAt w (i + 1) = w[i] := by
      first
        | simp [tokAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        | simp [tokAt, hlt]
    have htake : w.take (i + 1) = w.take i ++ [tokAt w (i + 1)] := by
      first
        | (rw [List.take_succ, List.getElem?_eq_getElem hlt, ht]; done)
        | (rw [List.take_succ, List.getElem?_eq_getElem hlt, ht]; rfl)
        | simp [List.take_succ, List.getElem?_eq_getElem hlt, ht]
    have hlv : lastv (w.take (i + 1)) =
        if val (tokAt w (i + 1)) = 0 then lastv (w.take i) else val (tokAt w (i + 1)) := by
      rw [htake]; simp [lastv, List.foldl_append]
    rcases ih (by omega) with ⟨hn, hz⟩ | ⟨j, hj1, hji, hjv, hjm, hl⟩
    · by_cases hv : val (tokAt w (i + 1)) = 0
      · left
        refine ⟨fun j h1 h2 => ?_, ?_⟩
        · by_cases hj : j ≤ i
          · exact hn j h1 hj
          · have : j = i + 1 := by omega
            subst this
            exact hv
        · rw [hlv, if_pos hv, hz]
      · right
        refine ⟨i + 1, by omega, le_refl _, hv, fun k h1 h2 => by omega, ?_⟩
        rw [hlv, if_neg hv]
    · by_cases hv : val (tokAt w (i + 1)) = 0
      · right
        refine ⟨j, hj1, by omega, hjv, fun k h1 h2 => ?_, ?_⟩
        · by_cases hk : k ≤ i
          · exact hjm k h1 hk
          · have : k = i + 1 := by omega
            subst this
            exact hv
        · rw [hlv, if_pos hv, hl]
      · right
        refine ⟨i + 1, by omega, le_refl _, hv, fun k h1 h2 => by omega, ?_⟩
        rw [hlv, if_neg hv]

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

/-- The embedding row of a real token `t ≤ 5`. -/
theorem embed_row {t : ℕ} (h : t ≤ 5) :
    net.embed.getD t [] = [Fl t, ((val t : ℕ) : ℚ), 0] := by
  interval_cases t <;> first | rfl | simp [net, Fl, val] | norm_num [net, Fl, val]

theorem init_eq (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (j : ℕ) (h : tokAt w j ≤ 5) :
    net.init fl p w j = [asw fl (Fl (tokAt w j)) (p.E (tokAt w j) 0),
      asw fl ((val (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 1),
      asw fl 0 (p.E (tokAt w j) 2)] := by
  show aswRow fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0 = _
  rw [embed_row h]
  rfl

/-- The ideal state at `j`. -/
noncomputable def xhat (w : List ℕ) (j : ℕ) : List ℝ :=
  [((Fl (tokAt w j) : ℚ) : ℝ), ((val (tokAt w j) : ℕ) : ℝ), 0]

noncomputable def cs (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : List ℕ :=
  head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

noncomputable def sc (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : ℕ → ℝ :=
  fun j => head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i j

noncomputable def att (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (r : List ℚ) (k : ℕ) :
    ℝ :=
  savg fl ex (cs fl p w i) (sc fl p w i) (fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0)

theorem attn_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
      (net.init fl p w) i =
    [att fl ex p w i z3 0, att fl ex p w i z3 1, att fl ex p w i [0, 1, 0] 2] := rfl

theorem run_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    net.run fl ex p w i =
      Lane4.RSeq.radd fl (Lane4.RSeq.radd fl (net.init fl p w i)
        (head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
          (net.init fl p w) i))
        [fl (0 + asw fl 0 (p.b2 0 0)), fl (0 + asw fl 0 (p.b2 0 1)),
         fl (0 + asw fl 0 (p.b2 0 2))] := rfl

theorem run_vals (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (a b c : ℝ)
    (hx : net.init fl p w i = [a, b, c]) :
    net.run fl ex p w i =
      [fl (fl (a + att fl ex p w i z3 0) + fl (0 + asw fl 0 (p.b2 0 0))),
       fl (fl (b + att fl ex p w i z3 1) + fl (0 + asw fl 0 (p.b2 0 1))),
       fl (fl (c + att fl ex p w i [0, 1, 0] 2) + fl (0 + asw fl 0 (p.b2 0 2)))] := by
  rw [run_eq, hx, attn_eq]
  rfl

theorem dq0 (w : List ℕ) (j : ℕ) : dotQ z3 (xhat w j) = 0 := by
  simp [dotQ, z3, xhat]

theorem dq2 (w : List ℕ) (j : ℕ) : dotQ [0, 1, 0] (xhat w j) = ((val (tokAt w j) : ℕ) : ℝ) := by
  simp [dotQ, xhat]

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

theorem Ctx.u_small (ev : Ctx u η M fl ex p w) : u ≤ 1 / 1000000 := by
  have h := ev.hu1
  have : (1 : ℝ) / 2 ^ 24 ≤ 1 / 1000000 := by norm_num
  linarith

theorem Ctx.η_small (ev : Ctx u η M fl ex p w) : η ≤ 1 / 1000000 := by
  have h := eta_tiny ev.hη1
  have : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000000 := by norm_num
  linarith

/-- A stored weight with `|a| ≤ 3` is within 1/500 of `a`. -/
theorem asw_c (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149)
    (hM : 5 ≤ M) (a : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 1000) (ha : |(a : ℝ)| ≤ 3) :
    |asw fl a d - (a : ℝ)| ≤ 1 / 500 := by
  have h := asw_near hr hu0 a hd (by linarith)
  have h1 : u * (|(a : ℝ)| + 1 / 1000) ≤ 1 / 2 ^ 24 * 4 :=
    mul_le_mul hu (by linarith) (by positivity) (by positivity)
  have h2 := eta_tiny hη
  have h3 : (1 : ℝ) / 2 ^ 24 * 4 + 1 / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

/-- Width 3, written weights ≤ 1, ideal entries ≤ 3, entry error `e ≤ 1/20`. -/
theorem ardot3 (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 2 ^ 149) (hM : (2 : ℝ) ^ 30 ≤ M) (r : List ℚ) (hr3 : r.length = 3)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (x xh : List ℝ) (hx : x.length = 3) {e : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 20) (hC : Close x xh e 3) (d : ℕ → ℝ)
    (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r x d 0 0 - dotQ r xh| ≤ 3 * e + 1 / 100 ∧ |ardot fl r x d 0 0| ≤ 50 := by
  have h20 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
  have key := ardot_near u η M (1 / 1000) fl hr hu0 hu hη0 hη (by norm_num) (by norm_num)
    r x xh d 1 3 e (by omega) (by omega) hC hd hW (by norm_num) (by norm_num) he0
    (by rw [h20]; linarith) hM
  have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  have h16 : (2 : ℝ) ^ 16 = 65536 := by norm_num
  have h100 : (1 : ℝ) / 2 ^ 100 = 1 / 1267650600228229401496703205376 := by norm_num
  rw [hr3] at key
  obtain ⟨k1, k2⟩ := key
  simp only [h3, h16, h100] at k1
  simp only [h3] at k2
  constructor
  · linarith
  · linarith

theorem tk_pos (w : List ℕ) (j : ℕ) : True := trivial

theorem init_ent (ev : Ctx u η M fl ex p w) (j : ℕ) :
    ∃ a b c : ℝ, net.init fl p w j = [a, b, c] ∧
      |a - ((Fl (tokAt w j) : ℚ) : ℝ)| ≤ 1 / 500 ∧
      |b - ((val (tokAt w j) : ℕ) : ℝ)| ≤ 1 / 500 ∧ |c - 0| ≤ 1 / 500 := by
  have ht := tok_le w ev.hw j
  have hM5 : (5 : ℝ) ≤ M := ev.range 5 (by norm_num)
  refine ⟨_, _, _, init_eq fl p w j ht, ?_, ?_, ?_⟩
  · exact asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM5 (Fl (tokAt w j)) (ev.hp.E (tokAt w j) 0)
      (le_trans (Fl_abs _) (by norm_num))
  · have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM5 ((val (tokAt w j) : ℕ) : ℚ)
      (ev.hp.E (tokAt w j) 1) (val_cast_abs _)
    simpa using h
  · have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM5 (0 : ℚ) (ev.hp.E (tokAt w j) 2) (by simp)
    simpa using h

theorem init_close (ev : Ctx u η M fl ex p w) (j : ℕ) :
    (net.init fl p w j).length = 3 ∧ Close (net.init fl p w j) (xhat w j) (1 / 500) 3 := by
  obtain ⟨a, b, c, hx, ha, hb, hc⟩ := init_ent ev j
  rw [hx]
  refine ⟨rfl, ?_⟩
  unfold xhat
  exact close3 ha hb hc (le_trans (Fl_abs _) (by norm_num)) (val_abs _) (by norm_num)

/-- A stored-weight row applied to a stored state. -/
theorem val_near (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr3 : r.length = 3)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (j : ℕ) (d : ℕ → ℝ) (hd : ∀ c, |d c| ≤ 1 / 1000) :
    |ardot fl r (net.init fl p w j) d 0 0 - dotQ r (xhat w j)| ≤ 1 / 60 := by
  obtain ⟨hlen, hC⟩ := init_close ev j
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have h := ardot3 ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 r hr3 hW _ _ hlen (by norm_num)
    (by norm_num) hC d hd
  linarith [h.1]

/-! ### The gate -/

theorem gate_pre (ev : Ctx u η M fl ex p w) (j : ℕ) :
    |(ardot fl head1.g (net.init fl p w j) (p.g 0 0) 0 0 + asw fl head1.gb (p.gb 0 0)) -
      (((Fl (tokAt w j) : ℚ) : ℝ) - 1 / 2)| ≤ 1 / 50 := by
  have h := val_near ev head1.g rfl (by simp [head1]) j (p.g 0 0) (ev.hp.g 0 0)
  have hq : dotQ head1.g (xhat w j) = ((Fl (tokAt w j) : ℚ) : ℝ) := by
    simp [dotQ, head1, xhat]
  rw [hq] at h
  have hgb : ((head1.gb : ℚ) : ℝ) = -1 / 2 := by norm_num [head1]
  have hb := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 5 (by norm_num)) head1.gb
    (ev.hp.gb 0 0) (by rw [hgb]; norm_num)
  rw [hgb] at hb
  obtain ⟨h1a, h1b⟩ := abs_le.mp h
  obtain ⟨hba, hbb⟩ := abs_le.mp hb
  rw [abs_le]; constructor <;> linarith

theorem relu_core (ev : Ctx u η M fl ex p w) (S F : ℝ) (hF : F = 0 ∨ F = 1)
    (h : |S - (F - 1 / 2)| ≤ 1 / 50) : (Lane4.relu (fl S) = 0 ↔ F = 0) := by
  obtain ⟨hpa, hpb⟩ := abs_le.mp h
  have hM1 : (1 : ℝ) ≤ M := ev.range 1 (by norm_num)
  have hu := ev.u_small
  have hη := ev.η_small
  constructor
  · intro h0
    rcases hF with hF | hF
    · exact hF
    · exfalso
      rw [hF] at hpa hpb
      have hS : |S| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have hl := ev.hr.lower ev.hu0 hS hM1
      unfold Lane4.relu at h0
      have h2 : fl S ≤ 0 := le_trans (le_max_left _ _) (le_of_eq h0)
      linarith
  · intro hF0
    rw [hF0] at hpa hpb
    exact relu_fl_zero ev.hr (by linarith) (by linarith)

theorem gate_iff (ev : Ctx u η M fl ex p w) (j : ℕ) :
    head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) = 0 ↔ val (tokAt w j) ≠ 0 := by
  have hp := gate_pre ev j
  have hF : ((Fl (tokAt w j) : ℚ) : ℝ) = 0 ∨ ((Fl (tokAt w j) : ℚ) : ℝ) = 1 := by
    by_cases hv : val (tokAt w j) = 0
    · right; rw [Fl_pos hv]; simp
    · left; rw [Fl_neg hv]; simp
  unfold AHead.gate
  refine (relu_core ev _ _ hF hp).trans ?_
  constructor
  · intro h hv0
    rw [Fl_pos hv0] at h
    simp at h
  · intro hv
    rw [Fl_neg hv]
    simp

theorem mem_cs (ev : Ctx u η M fl ex p w) (i j : ℕ) :
    j ∈ cs fl p w i ↔ j ≤ i ∧ val (tokAt w j) ≠ 0 := by
  unfold cs
  rw [AHead.mem_cands]
  have hm : head1.mask = Mask.causal := rfl
  rw [hm, Lane4.Seq.mem_cand_causal, gate_iff ev j]

theorem cs_nodup (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : (cs fl p w i).Nodup :=
  AHead.cands_nodup head1 fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

theorem cs_len (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (hi : i ≤ w.length) :
    (cs fl p w i).length ≤ w.length + 1 := by
  have h1 : (cs fl p w i).length ≤ (cand Mask.causal (w.length + 1) i).length :=
    List.length_filter_le _ _
  have h2 : (cand Mask.causal (w.length + 1) i).length = i + 1 := by simp [cand]
  omega

/-! ### Scores -/

theorem content_small (ev : Ctx u η M fl ex p w) (i k : ℕ) :
    |Lane4.RSeq.pdot fl (net.init fl p w i)
        (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) 0| ≤ 1 / 4 := by
  obtain ⟨hli, hCi⟩ := init_close ev i
  obtain ⟨hlk, hCk⟩ := init_close ev k
  have hrow : ∀ r : ℕ, |ardot fl z3 (net.init fl p w k) (p.A 0 0 r) 0 0 - 0| ≤ 1 / 60 := by
    intro r
    have h := val_near ev z3 rfl (by simp [z3]) k (p.A 0 0 r) (ev.hp.A 0 0 r)
    rwa [dq0] at h
  have hy : armat fl head1.A (net.init fl p w k) (p.A 0 0) 0 =
      [ardot fl z3 (net.init fl p w k) (p.A 0 0 0) 0 0,
       ardot fl z3 (net.init fl p w k) (p.A 0 0 1) 0 0,
       ardot fl z3 (net.init fl p w k) (p.A 0 0 2) 0 0] := rfl
  have hCy : Close (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) [0, 0, 0] (1 / 60) 0 := by
    rw [hy]
    exact close3 (hrow 0) (hrow 1) (hrow 2) (by norm_num) (by norm_num) (by norm_num)
  have hlen_y : (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0).length = 3 := by
    simp [hy]
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  obtain ⟨p1, -⟩ := pdot_near u η M fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (net.init fl p w i)
    (xhat w i) (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) [0, 0, 0] 3 0 (1 / 500) (1 / 60)
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

/-! ### The head returns the value at the winner -/

theorem row_attn (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr3 : r.length = 3)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (hq : ∀ j, |dotQ r (xhat w j)| ≤ 3) (k : ℕ)
    (i : ℕ) (hi : i ≤ w.length) (j : ℕ) (hj : j ∈ cs fl p w i)
    (hmax : ∀ k' ∈ cs fl p w i, k' ≠ j → k' < j) :
    |att fl ex p w i r k - dotQ r (xhat w j)| ≤ 1 / 20 := by
  obtain ⟨hjle, hjv⟩ := (mem_cs ev i j).mp hj
  have hlen := cs_len fl p w i hi
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
  have hS : ∀ k' ∈ cs fl p w i, |sc fl p w i k'| ≤ 28 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k' hk'
    have := ((mem_cs ev i k').mp hk').1
    exact score_abs ev i k' (by omega) (by omega)
  have hSM : 2 * (28 * ((w.length + 1 : ℕ) : ℝ)) ≤ M := by
    have := ev.rangeN 56 (by norm_num) (by norm_num)
    linarith
  have hf : ∀ k' ∈ cs fl p w i,
      |ardot fl r (net.init fl p w k') (p.V 0 0 k) 0 0| ≤ (31 / 10 : ℝ) := by
    intro k' _
    have h1 := val_near ev r hr3 hW k' (p.V 0 0 k) (ev.hp.V 0 0 k)
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h2a, h2b⟩ := abs_le.mp (hq k')
    rw [abs_le]; constructor <;> linarith
  have hBM : 4 * (31 / 10 : ℝ) + 4 ≤ M := by
    have := ev.range 17 (by norm_num)
    linarith
  obtain ⟨hs1, -⟩ := soft_near (s := sc fl p w i)
    (f := fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0) ev.hr ev.he ev.hu0 ev.hu1
    ev.hη0 ev.hη1 (cs_nodup fl p w i) hlen ev.hn ev.hnη hj hgap hS hSM hf hBM
  have hs1' : |att fl ex p w i r k - ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0|
      ≤ (31 / 10 : ℝ) / 100 + 1 / 2 ^ 90 := hs1
  have hv := val_near ev r hr3 hW j (p.V 0 0 k) (ev.hp.V 0 0 k)
  have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 1000000 := by norm_num
  have h3 := abs_sub_le (att fl ex p w i r k)
    (ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0) (dotQ r (xhat w j))
  linarith

theorem att_empty (ev : Ctx u η M fl ex p w) (r : List ℚ) (k i : ℕ)
    (hnone : ∀ k', k' ∈ cs fl p w i → False) : att fl ex p w i r k = 0 := by
  unfold att
  exact soft_zeros ev.hr (fun k' hk' => (hnone k' hk').elim)

theorem head_close (ev : Ctx u η M fl ex p w) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    |att fl ex p w i z3 0 - 0| ≤ 1 / 20 ∧ |att fl ex p w i z3 1 - 0| ≤ 1 / 20 ∧
    |att fl ex p w i [0, 1, 0] 2 - ((target w i : ℕ) : ℝ)| ≤ 1 / 20 ∧
    |((target w i : ℕ) : ℝ)| ≤ 3 := by
  rcases last_marked w i hi with ⟨hn, hl⟩ | ⟨j, hj1, hji, hjv, hjm, hl⟩
  · have hT0 : target w i = 0 := hl
    have hnone : ∀ k', k' ∈ cs fl p w i → False := by
      intro k' hk'
      obtain ⟨hki, hkv⟩ := (mem_cs ev i k').mp hk'
      by_cases hk0 : k' = 0
      · subst hk0
        apply hkv
        rw [Lane4.Seq.tokAt_zero]
        simp [val]
      · exact hkv (hn k' (by omega) hki)
    have e0 : ∀ r k, att fl ex p w i r k = 0 := fun r k => att_empty ev r k i hnone
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e0]; norm_num
    · rw [e0]; norm_num
    · rw [e0, hT0]; norm_num
    · rw [hT0]; norm_num
  · have hjc : j ∈ cs fl p w i := (mem_cs ev i j).mpr ⟨hji, hjv⟩
    have hmax : ∀ k' ∈ cs fl p w i, k' ≠ j → k' < j := by
      intro k' hk' hne
      obtain ⟨hk'i, hk'v⟩ := (mem_cs ev i k').mp hk'
      by_contra hnl
      have hlt : j < k' := by omega
      exact hk'v (hjm k' hlt hk'i)
    have hT : target w i = val (tokAt w j) := hl
    have r0 := row_attn ev z3 rfl (by simp [z3]) (fun j => by rw [dq0]; norm_num) 0 i hi j hjc hmax
    have r1 := row_attn ev z3 rfl (by simp [z3]) (fun j => by rw [dq0]; norm_num) 1 i hi j hjc hmax
    have r2 := row_attn ev [0, 1, 0] rfl (by simp)
      (fun j => by rw [dq2]; exact val_abs _) 2 i hi j hjc hmax
    rw [dq0] at r0 r1
    rw [dq2] at r2
    refine ⟨r0, r1, ?_, ?_⟩
    · rw [hT]; exact r2
    · rw [hT]; exact val_abs _

/-! ### Residual add, MLP bias terms, read-out -/

theorem mlp_small (ev : Ctx u η M fl ex p w) (d : ℝ) (hd : |d| ≤ 1 / 1000) :
    |fl (0 + asw fl 0 d)| ≤ 1 / 100 := by
  have h1 := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 5 (by norm_num)) (0 : ℚ) hd (by simp)
  have h1' : |asw fl 0 d| ≤ 1 / 500 := by simpa using h1
  have h2 : |(0 : ℝ) + asw fl 0 d| ≤ 1 / 500 := by rw [zero_add]; exact h1'
  have h3 := ev.hr.bound ev.hu0 h2 (ev.range (1 / 500) (by norm_num))
  have hu := ev.u_small
  have hη := ev.η_small
  linarith

theorem add_step (ev : Ctx u η M fl ex p w) {x s m t s' y : ℝ} (hx : |x - t| ≤ 1 / 500)
    (hs : |s - s'| ≤ 1 / 20) (hy : t + s' = y) (hy2 : |y| ≤ 3) (hm : |m| ≤ 1 / 100) :
    |fl (fl (x + s) + m) - y| ≤ 1 / 10 := by
  have hM4 : (4 : ℝ) ≤ M := ev.range 4 (by norm_num)
  have hu4 : u * 4 ≤ 1 / 250000 := by
    have h := ev.u_small
    linarith
  have hη' := ev.η_small
  obtain ⟨hxa, hxb⟩ := abs_le.mp hx
  obtain ⟨hsa, hsb⟩ := abs_le.mp hs
  obtain ⟨hya, hyb⟩ := abs_le.mp hy2
  obtain ⟨hma, hmb⟩ := abs_le.mp hm
  have h1 : |x + s - y| ≤ 1 / 500 + 1 / 20 := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |x + s| ≤ 4 := by
    rw [abs_le]; constructor <;> linarith
  have h3 := ev.hr.near ev.hu0 h1 h2 hM4
  obtain ⟨h3a, h3b⟩ := abs_le.mp h3
  have h4 : |fl (x + s) + m - y| ≤ 1 / 500 + 1 / 20 + (u * 4 + η) + 1 / 100 := by
    rw [abs_le]; constructor <;> linarith
  have h5 : |fl (x + s) + m| ≤ 4 := by
    rw [abs_le]; constructor <;> linarith
  have h6 := ev.hr.near ev.hu0 h4 h5 hM4
  linarith

theorem final_round (ev : Ctx u η M fl ex p w) {A O t : ℝ} (hA : |A - t| ≤ 1 / 8)
    (hO : |O| ≤ 1 / 500) (ht : |t| ≤ 3) : |fl (A + O) - t| ≤ 1 / 4 := by
  have hM4 : (4 : ℝ) ≤ M := ev.range 4 (by norm_num)
  have hu4 : u * 4 ≤ 1 / 250000 := by
    have h := ev.u_small
    linarith
  have hη' := ev.η_small
  obtain ⟨hAa, hAb⟩ := abs_le.mp hA
  obtain ⟨hOa, hOb⟩ := abs_le.mp hO
  obtain ⟨hta, htb⟩ := abs_le.mp ht
  have h1 : |A + O - t| ≤ 1 / 8 + 1 / 500 := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |A + O| ≤ 4 := by
    rw [abs_le]; constructor <;> linarith
  have h3 := ev.hr.near ev.hu0 h1 h2 hM4
  linarith

theorem out_near (ev : Ctx u η M fl ex p w) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    |net.out fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  obtain ⟨a, b, c, hx, ha, hb, hc⟩ := init_ent ev i
  obtain ⟨r0, r1, r2, hT⟩ := head_close ev i hi1 hi
  have m0 := mlp_small ev (p.b2 0 0) (ev.hp.b2 0 0)
  have m1 := mlp_small ev (p.b2 0 1) (ev.hp.b2 0 1)
  have m2 := mlp_small ev (p.b2 0 2) (ev.hp.b2 0 2)
  have y0 := add_step ev ha r0 (add_zero _) (le_trans (Fl_abs _) (by norm_num)) m0
  have y1 := add_step ev hb r1 (add_zero _) (val_abs _) m1
  have y2 := add_step ev hc r2 (zero_add _) hT m2
  have hCy := close3 y0 y1 y2 (le_trans (Fl_abs _) (by norm_num)) (val_abs _) hT
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have ho := ardot_near_abs u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1
    (by norm_num) (by norm_num) net.outW _ _ p.oW 1 3 (1 / 10)
    (by simp [net]) (by simp [net]) hCy ev.hp.oW (by simp [net]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hM30
  have hq : ∀ x y z : ℝ, dotQ net.outW [x, y, z] = z := by
    intro x y z
    simp [dotQ, net]
  have hlen3 : net.outW.length = 3 := rfl
  have habs : absSum net.outW = 1 := by simp [absSum, net]
  have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  have h16 : (2 : ℝ) ^ 16 = 65536 := by norm_num
  have h100 : (1 : ℝ) / 2 ^ 100 = 1 / 1267650600228229401496703205376 := by norm_num
  rw [hq, hlen3, habs] at ho
  simp only [h3, h16, h100] at ho
  have hob : |asw fl net.outB p.oB| ≤ 1 / 500 := by
    have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 5 (by norm_num)) net.outB ev.hp.oB
      (by simp [net])
    have h0 : ((net.outB : ℚ) : ℝ) = 0 := by simp [net]
    rwa [h0, sub_zero] at h
  unfold ANet.out
  rw [run_vals fl ex p w i a b c hx]
  exact final_round ev (le_trans ho (by norm_num)) hob hT

end Steps

theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη1 p hp w hw hn hnη hM i hi1 hi
  have ctx : Ctx u η M fl ex p w := ⟨hr, he, hu0, hu1, hη0, hη1, hp, hw, hn, hnη, hM⟩
  exact out_near ctx i hi1 hi

end Lane4.Case
