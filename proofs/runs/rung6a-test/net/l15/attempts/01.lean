/-
Gated softmax transformer for "value of the last marked token up to and including i".

State width 3, rows `[val, flag, res]`:
  BOS and tokens 3,4,5: `[0,1,0]`; token 1: `[1,0,0]`; token 2: `[3,0,0]`.
One block, one head, no MLP:
  * mask causal, slope 24 (nearest key to the left wins),
  * gate `relu (flag - 1/2)`: exactly 0 iff the key is marked (flag 0),
  * score matrix 0, value matrix: row 2 copies `val` into `res`,
  * read-out reads `res`.
No candidate: head output 0, which is the target 0.
-/
namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

/-! ### The network -/

def z3 : List ℚ := [0, 0, 0]

def head1 : AHead :=
  { A := [z3, z3, z3], V := [z3, z3, [1, 0, 0]], mask := Mask.causal, m := 24,
    g := [0, 1, 0], gb := -1 / 2 }

def blk : ABlock :=
  { heads := [head1], W1 := [], b1 := [], W2 := [[], [], []], b2 := z3 }

def net : ANet :=
  { embed := [[0, 1, 0], [1, 0, 0], [3, 0, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]],
    blocks := [blk], outW := [0, 0, 1], outB := 0 }

/-! ### Ideal values -/

def cvQ (t : ℕ) : ℚ := ((val t : ℕ) : ℚ)
def cgQ (t : ℕ) : ℚ := if val t = 0 then 1 else 0

noncomputable def cv (t : ℕ) : ℝ := (cvQ t : ℝ)
noncomputable def cg (t : ℕ) : ℝ := (cgQ t : ℝ)

/-- The ideal state at position `j`: `[val, flag, 0]`. -/
noncomputable def xhat (w : List ℕ) (j : ℕ) : List ℝ := [cv (tokAt w j), cg (tokAt w j), 0]

noncomputable def cs (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : List ℕ :=
  head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

noncomputable def sc (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : ℕ → ℝ :=
  fun j => head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i j

noncomputable def att (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (r : List ℚ) (k : ℕ) :
    ℝ :=
  savg fl ex (cs fl p w i) (sc fl p w i) (fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0)

theorem val_cases (t : ℕ) : val t = 0 ∨ val t = 1 ∨ val t = 3 := by
  unfold val
  split_ifs <;> simp

theorem cv_eq (t : ℕ) : cv t = ((val t : ℕ) : ℝ) := by simp [cv, cvQ]

theorem cv_bd (t : ℕ) : 0 ≤ cv t ∧ cv t ≤ 3 := by
  rw [cv_eq]
  rcases val_cases t with h | h | h <;> rw [h] <;> norm_num

theorem cv_abs (t : ℕ) : |cv t| ≤ 3 := by
  obtain ⟨h0, h1⟩ := cv_bd t
  rw [abs_of_nonneg h0]
  exact h1

theorem cg_zero {t : ℕ} (h : val t = 0) : cg t = 1 := by simp [cg, cgQ, h]

theorem cg_one {t : ℕ} (h : val t ≠ 0) : cg t = 0 := by simp [cg, cgQ, h]

theorem cg_abs (t : ℕ) : |cg t| ≤ 3 := by
  by_cases h : val t = 0
  · rw [cg_zero h]; norm_num
  · rw [cg_one h]; norm_num

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem embed_row {t : ℕ} (h : t ≤ 5) : net.embed.getD t [] = [cvQ t, cgQ t, 0] := by
  interval_cases t <;> first | rfl | simp [net, cvQ, cgQ, val] | decide

theorem init_eq (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (j : ℕ) (h : tokAt w j ≤ 5) :
    net.init fl p w j = [asw fl (cvQ (tokAt w j)) (p.E (tokAt w j) 0),
      asw fl (cgQ (tokAt w j)) (p.E (tokAt w j) 1), asw fl 0 (p.E (tokAt w j) 2)] := by
  show aswRow fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0 = _
  rw [embed_row h]
  rfl

theorem attn_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
      (net.init fl p w) i =
    [att fl ex p w i z3 0, att fl ex p w i z3 1, att fl ex p w i [1, 0, 0] 2] := rfl

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
       fl (fl (c + att fl ex p w i [1, 0, 0] 2) + fl (0 + asw fl 0 (p.b2 0 2)))] := by
  rw [run_eq, hx, attn_eq]
  rfl

theorem dq0 (w : List ℕ) (j : ℕ) : dotQ z3 (xhat w j) = 0 := by
  simp [dotQ, z3, xhat]

theorem dq1 (w : List ℕ) (j : ℕ) : dotQ [1, 0, 0] (xhat w j) = cv (tokAt w j) := by
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

/-! ### Combinatorics of the target -/

theorem lastv_append (q : List ℕ) (t : ℕ) :
    lastv (q ++ [t]) = if val t = 0 then lastv q else val t := by
  simp [lastv, List.foldl_append]

theorem target_succ (w : List ℕ) (i : ℕ) (hi : i < w.length) :
    target w (i + 1) = if val w[i] = 0 then target w i else val w[i] := by
  unfold target
  rw [List.take_succ, List.getElem?_eq_getElem hi]
  simp [lastv_append]

theorem last_ex (w : List ℕ) : ∀ i, i ≤ w.length →
    ∃ j, j ≤ i ∧ (∀ k, j < k → k ≤ i → val (tokAt w k) = 0) ∧
      (val (tokAt w j) ≠ 0 ∨ ∀ k, k ≤ i → val (tokAt w k) = 0) ∧
      target w i = val (tokAt w j) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨0, le_refl _, fun k h1 h2 => by omega, Or.inr ?_, ?_⟩
    · intro k hk
      have : k = 0 := by omega
      subst this
      simp [Lane4.Seq.tokAt_zero, val]
    · simp [target, lastv, Lane4.Seq.tokAt_zero, val]
  | succ i ih =>
    intro hi
    obtain ⟨j, hji, hafter, hmark, htgt⟩ := ih (by omega)
    have hlt : i < w.length := by omega
    have ht := Lane4.Seq.tokAt_succ w i hlt
    have hts := target_succ w i hlt
    by_cases hv : val w[i] = 0
    · refine ⟨j, by omega, ?_, ?_, ?_⟩
      · intro k hk1 hk2
        by_cases hk : k = i + 1
        · subst hk
          rw [ht]
          exact hv
        · exact hafter k hk1 (by omega)
      · rcases hmark with h | h
        · exact Or.inl h
        · right
          intro k hk
          by_cases hk' : k = i + 1
          · subst hk'
            rw [ht]
            exact hv
          · exact h k (by omega)
      · rw [hts, if_pos hv]
        exact htgt
    · refine ⟨i + 1, le_refl _, fun k h1 h2 => by omega, Or.inl ?_, ?_⟩
      · rw [ht]
        exact hv
      · rw [hts, if_neg hv, ht]

theorem target_bd (w : List ℕ) (i : ℕ) (hi : i ≤ w.length) :
    0 ≤ ((target w i : ℕ) : ℝ) ∧ ((target w i : ℕ) : ℝ) ≤ 3 := by
  obtain ⟨j, -, -, -, ht⟩ := last_ex w i hi
  rw [ht]
  rcases val_cases (tokAt w j) with h | h | h <;> rw [h] <;> norm_num

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

/-! ### Stored weights -/

theorem asw_c (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149)
    (hM : 5 ≤ M) (a : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 1000) (ha : |(a : ℝ)| ≤ 3) :
    |asw fl a d - (a : ℝ)| ≤ 1 / 500 := by
  have h := asw_near hr hu0 a hd (by linarith)
  have h1 : u * (|(a : ℝ)| + 1 / 1000) ≤ 1 / 2 ^ 24 * 4 :=
    mul_le_mul hu (by linarith) (by positivity) (by positivity)
  have h2 := eta_tiny hη
  have h3 : (1 : ℝ) / 2 ^ 24 * 4 + 1 / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

theorem ardot3 (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 2 ^ 149) (hM : (2 : ℝ) ^ 30 ≤ M) (r : List ℚ) (hr3 : r.length = 3)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (x xh : List ℝ) (hx : x.length = 3) {e : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 16) (hC : Close x xh e 3) (d : ℕ → ℝ)
    (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r x d 0 0 - dotQ r xh| ≤ absSum r * e + 1 / 100 ∧ |ardot fl r x d 0 0| ≤ 50 := by
  have h20 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
  have hT : ((1 : ℝ) + 1) * (3 + e + 1) ≤ 2 ^ 20 := by rw [h20]; nlinarith
  have k1 := ardot_near_abs u η M (1 / 1000) fl hr hu0 hu hη0 hη (by norm_num) (by norm_num)
    r x xh d 1 3 e (by omega) (by omega) hC hd hW (by norm_num) (by norm_num) he0 hT hM
  have k2 := ardot_near u η M (1 / 1000) fl hr hu0 hu hη0 hη (by norm_num) (by norm_num)
    r x xh d 1 3 e (by omega) (by omega) hC hd hW (by norm_num) (by norm_num) he0 hT hM
  have h3 : (r.length : ℝ) = 3 := by rw [hr3]; norm_num
  have h16 : (2 : ℝ) ^ 16 = 65536 := by norm_num
  have h100 : (1 : ℝ) / 2 ^ 100 = 1 / 1267650600228229401496703205376 := by norm_num
  rw [h3, h16, h100] at k1
  obtain ⟨_, k2b⟩ := k2
  rw [h3] at k2b
  constructor
  · linarith [k1]
  · linarith [k2b]

/-! ### Step 1: the starting state -/

theorem init_ent (ev : Ctx u η M fl ex p w) (j : ℕ) :
    ∃ a b c : ℝ, net.init fl p w j = [a, b, c] ∧
      |a - cv (tokAt w j)| ≤ 1 / 500 ∧ |b - cg (tokAt w j)| ≤ 1 / 500 ∧ |c - 0| ≤ 1 / 500 := by
  have ht := tok_le w ev.hw j
  have hM5 : (5 : ℝ) ≤ M := ev.range 5 (by norm_num)
  refine ⟨_, _, _, init_eq fl p w j ht, ?_, ?_, ?_⟩
  · exact asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM5 (cvQ (tokAt w j)) (ev.hp.E (tokAt w j) 0)
      (cv_abs (tokAt w j))
  · exact asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM5 (cgQ (tokAt w j)) (ev.hp.E (tokAt w j) 1)
      (cg_abs (tokAt w j))
  · have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM5 (0 : ℚ) (ev.hp.E (tokAt w j) 2) (by simp)
    simpa using h

theorem init_close (ev : Ctx u η M fl ex p w) (j : ℕ) :
    (net.init fl p w j).length = 3 ∧ Close (net.init fl p w j) (xhat w j) (1 / 500) 3 := by
  obtain ⟨a, b, c, hx, ha, hb, hc⟩ := init_ent ev j
  rw [hx]
  refine ⟨rfl, ?_⟩
  unfold xhat
  exact close3 ha hb hc (cv_abs _) (cg_abs _) (by norm_num)

/-! ### Step 2: the gate -/

theorem relu_pos_ne (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 2 ^ 149) {x : ℝ} (hx1 : 1 / 4 ≤ x) (hx2 : x ≤ 1) (hM : 1 ≤ M) :
    Lane4.relu (fl x) ≠ 0 := by
  have hl := hr.lower hu0 (x := x) (B := 1) (by rw [abs_of_nonneg (by linarith)]; exact hx2) hM
  have h2 := eta_tiny hη
  have h3 : (1 : ℝ) / 2 ^ 24 ≤ 1 / 1000 := by norm_num
  have h4 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have hpos : 0 < fl x := by linarith
  intro h
  unfold Lane4.relu at h
  have := le_max_left (fl x) 0
  rw [h] at this
  linarith

theorem gate_pre (ev : Ctx u η M fl ex p w) (j : ℕ) :
    |ardot fl head1.g (net.init fl p w j) (p.g 0 0) 0 0 + asw fl head1.gb (p.gb 0 0)
      - (cg (tokAt w j) - 1 / 2)| ≤ 1 / 50 := by
  obtain ⟨hlen, hC⟩ := init_close ev j
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have h := ardot3 ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 head1.g rfl (by simp [head1])
    _ _ hlen (by norm_num) (by norm_num) hC (p.g 0 0) (ev.hp.g 0 0)
  have hq : dotQ head1.g (xhat w j) = cg (tokAt w j) := by simp [dotQ, head1, xhat]
  have habs : absSum head1.g = 1 := by simp [absSum, head1]
  obtain ⟨h1, -⟩ := h
  rw [hq, habs] at h1
  have hgb : ((head1.gb : ℚ) : ℝ) = -1 / 2 := by norm_num [head1]
  have hb := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 5 (by norm_num)) head1.gb
    (ev.hp.gb 0 0) (by rw [hgb]; norm_num)
  rw [hgb] at hb
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨hba, hbb⟩ := abs_le.mp hb
  rw [abs_le]
  constructor <;> linarith

theorem gate_iff (ev : Ctx u η M fl ex p w) (j : ℕ) :
    head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) = 0 ↔ val (tokAt w j) ≠ 0 := by
  have hp := gate_pre ev j
  unfold AHead.gate
  generalize ardot fl head1.g (net.init fl p w j) (p.g 0 0) 0 0 + asw fl head1.gb (p.gb 0 0) = P
    at hp ⊢
  obtain ⟨hpa, hpb⟩ := abs_le.mp hp
  have hM1 : (1 : ℝ) ≤ M := ev.range 1 (by norm_num)
  by_cases hv : val (tokAt w j) = 0
  · have hc := cg_zero hv
    rw [hc] at hpa hpb
    constructor
    · intro h
      exfalso
      exact relu_pos_ne ev.hr ev.hu0 ev.hu1 ev.hη1 (by linarith) (by linarith) hM1 h
    · intro h
      exact absurd hv h
  · have hc := cg_one hv
    rw [hc] at hpa hpb
    refine ⟨fun _ => hv, fun _ => ?_⟩
    exact relu_fl_zero ev.hr (by linarith) (by linarith)

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

/-! ### Step 3: scores -/

theorem val_near (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr3 : r.length = 3)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (j : ℕ) (d : ℕ → ℝ) (hd : ∀ c, |d c| ≤ 1 / 1000) :
    |ardot fl r (net.init fl p w j) d 0 0 - dotQ r (xhat w j)| ≤ 1 / 60 ∧
      |ardot fl r (net.init fl p w j) d 0 0| ≤ 50 := by
  obtain ⟨hlen, hC⟩ := init_close ev j
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have h := ardot3 ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 r hr3 hW _ _ hlen (by norm_num)
    (by norm_num) hC d hd
  have hs := absSum_le r 1 hW
  have h3 : (r.length : ℝ) = 3 := by rw [hr3]; norm_num
  rw [h3] at hs
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2⟩
  have := (abs_le.mp h1)
  rw [abs_le]
  constructor <;> linarith [this.1, this.2]

theorem content_small (ev : Ctx u η M fl ex p w) (i k : ℕ) :
    |Lane4.RSeq.pdot fl (net.init fl p w i)
        (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) 0| ≤ 1 / 5 := by
  obtain ⟨hli, hCi⟩ := init_close ev i
  obtain ⟨hlk, hCk⟩ := init_close ev k
  have hrow : ∀ r : ℕ, |ardot fl z3 (net.init fl p w k) (p.A 0 0 r) 0 0 - 0| ≤ 1 / 60 := by
    intro r
    have h := (val_near ev z3 rfl (by simp [z3]) k (p.A 0 0 r) (ev.hp.A 0 0 r)).1
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

/-! ### Step 4: the head -/

theorem row_attn (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr3 : r.length = 3)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (hq : ∀ j, |dotQ r (xhat w j)| ≤ 3) (k : ℕ)
    (i j : ℕ) (hi : i ≤ w.length) (hj : j ∈ cs fl p w i)
    (hmax : ∀ k' ∈ cs fl p w i, k' ≤ j) :
    |att fl ex p w i r k - dotQ r (xhat w j)| ≤ 1 / 20 := by
  have hlen := cs_len fl p w i hi
  have hji := ((mem_cs ev i j).mp hj).1
  have hgap : ∀ k' ∈ cs fl p w i, k' ≠ j →
      sc fl p w i k' ≤ sc fl p w i j - 16 * ((ndist j k' : ℕ) : ℝ) := by
    intro k' hk' hne
    have hk'j : k' < j := lt_of_le_of_ne (hmax k' hk') hne
    rw [ndist_cast]
    have hg := score_gap ev i j k' (by omega) (by omega) hk'j
    have h1 : (k' : ℝ) + 1 ≤ (j : ℝ) := by
      have h : k' + 1 ≤ j := hk'j
      exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    exact hg
  have hS : ∀ k' ∈ cs fl p w i, |sc fl p w i k'| ≤ 28 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k' hk'
    have := (mem_cs ev i k').mp hk'
    exact score_abs ev i k' (by omega) (by omega)
  have hSM : 2 * (28 * ((w.length + 1 : ℕ) : ℝ)) ≤ M := by
    have := ev.rangeN 56 (by norm_num) (by norm_num)
    linarith
  have hf : ∀ k' ∈ cs fl p w i,
      |ardot fl r (net.init fl p w k') (p.V 0 0 k) 0 0| ≤ (151 / 50 : ℝ) := by
    intro k' _
    have h1 := (val_near ev r hr3 hW k' (p.V 0 0 k) (ev.hp.V 0 0 k)).1
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h2a, h2b⟩ := abs_le.mp (hq k')
    rw [abs_le]; constructor <;> linarith
  have hBM : 4 * (151 / 50 : ℝ) + 4 ≤ M := by
    have := ev.range 17 (by norm_num)
    linarith
  obtain ⟨hs1, -⟩ := soft_near (s := sc fl p w i)
    (f := fun j' => ardot fl r (net.init fl p w j') (p.V 0 0 k) 0 0) ev.hr ev.he ev.hu0 ev.hu1
    ev.hη0 ev.hη1 (cs_nodup fl p w i) hlen ev.hn ev.hnη hj hgap hS hSM hf hBM
  have hs1' : |att fl ex p w i r k - ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0|
      ≤ (151 / 50 : ℝ) / 100 + 1 / 2 ^ 90 := hs1
  have hv := (val_near ev r hr3 hW j (p.V 0 0 k) (ev.hp.V 0 0 k)).1
  have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 1000000 := by norm_num
  have h3 := abs_sub_le (att fl ex p w i r k)
    (ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0) (dotQ r (xhat w j))
  linarith

theorem row_empty (ev : Ctx u η M fl ex p w) (r : List ℚ) (k i : ℕ) (h : cs fl p w i = []) :
    att fl ex p w i r k = 0 := by
  unfold att
  rw [h]
  exact soft_zeros ev.hr (by intro k hk; simp at hk)

theorem att_facts (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    |att fl ex p w i z3 0 - 0| ≤ 1 / 20 ∧ |att fl ex p w i z3 1 - 0| ≤ 1 / 20 ∧
    |att fl ex p w i [1, 0, 0] 2 - ((target w i : ℕ) : ℝ)| ≤ 1 / 20 := by
  obtain ⟨j, hji, hafter, hmark, htgt⟩ := last_ex w i hi
  have hz3 : z3.length = 3 := rfl
  have hWz : ∀ a ∈ z3, |(a : ℝ)| ≤ 1 := by simp [z3]
  have hWe : ∀ a ∈ ([1, 0, 0] : List ℚ), |(a : ℝ)| ≤ 1 := by simp
  have hqz : ∀ j', |dotQ z3 (xhat w j')| ≤ 3 := fun j' => by rw [dq0]; norm_num
  have hqe : ∀ j', |dotQ [1, 0, 0] (xhat w j')| ≤ 3 := fun j' => by
    rw [dq1]; exact cv_abs _
  rcases hmark with hne | hall
  · have hj : j ∈ cs fl p w i := (mem_cs ev i j).mpr ⟨hji, hne⟩
    have hmax : ∀ k' ∈ cs fl p w i, k' ≤ j := by
      intro k' hk'
      obtain ⟨h1, h2⟩ := (mem_cs ev i k').mp hk'
      by_contra hlt
      exact h2 (hafter k' (by omega) h1)
    have r0 := row_attn ev z3 hz3 hWz hqz 0 i j hi hj hmax
    have r1 := row_attn ev z3 hz3 hWz hqz 1 i j hi hj hmax
    have r2 := row_attn ev [1, 0, 0] rfl hWe hqe 2 i j hi hj hmax
    rw [dq0] at r0 r1
    rw [dq1] at r2
    refine ⟨r0, r1, ?_⟩
    have ht : ((target w i : ℕ) : ℝ) = cv (tokAt w j) := by rw [htgt, cv_eq]
    rw [ht]
    exact r2
  · have hcs : cs fl p w i = [] := by
      by_contra hne
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨h1, h2⟩ := (mem_cs ev i a).mp ha
      exact h2 (hall a h1)
    have ht : ((target w i : ℕ) : ℝ) = 0 := by simp [htgt, hall j hji]
    refine ⟨?_, ?_, ?_⟩
    · rw [row_empty ev z3 0 i hcs]; norm_num
    · rw [row_empty ev z3 1 i hcs]; norm_num
    · rw [row_empty ev [1, 0, 0] 2 i hcs, ht]; norm_num

/-! ### Step 5: residual, MLP bias, read-out -/

theorem mlp_small (ev : Ctx u η M fl ex p w) (d : ℝ) (hd : |d| ≤ 1 / 1000) :
    |fl (0 + asw fl 0 d)| ≤ 1 / 100 := by
  have h1 := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 5 (by norm_num)) (0 : ℚ) hd (by simp)
  have h1' : |asw fl 0 d| ≤ 1 / 500 := by simpa using h1
  have h2 : |(0 : ℝ) + asw fl 0 d| ≤ 1 / 500 := by rw [zero_add]; exact h1'
  have h3 := ev.hr.bound ev.hu0 h2 (ev.range (1 / 500) (by norm_num))
  have hu' : (1 : ℝ) / 2 ^ 24 ≤ 1 / 1000 := by norm_num
  have hη' := eta_tiny ev.hη1
  have hη'' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have := ev.hu1
  linarith

theorem add_step (ev : Ctx u η M fl ex p w) {x s m t s' y : ℝ} (hx : |x - t| ≤ 1 / 500)
    (hs : |s - s'| ≤ 1 / 20) (hy : t + s' = y) (hy2 : |y| ≤ 3) (hm : |m| ≤ 1 / 100) :
    |fl (fl (x + s) + m) - y| ≤ 1 / 16 := by
  have hM4 : (4 : ℝ) ≤ M := ev.range 4 (by norm_num)
  have hu3 : u * 4 ≤ 1 / 1000000 := by
    have h := ev.hu1
    have : (1 : ℝ) / 2 ^ 24 ≤ 1 / 4000000 := by norm_num
    linarith
  have hη' : η ≤ 1 / 1000000 := by
    have h := eta_tiny ev.hη1
    have : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000000 := by norm_num
    linarith
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

theorem final_round (ev : Ctx u η M fl ex p w) {A O t : ℝ} (hA : |A - t| ≤ 1 / 16 + 1 / 100)
    (hA2 : |A| ≤ 50) (hO : |O| ≤ 1 / 500) : |fl (A + O) - t| ≤ 1 / 4 := by
  have hM51 : (51 : ℝ) ≤ M := ev.range 51 (by norm_num)
  have hu51 : u * 51 ≤ 1 / 1000 := by
    have h := ev.hu1
    have : (1 : ℝ) / 2 ^ 24 ≤ 1 / 51000 := by norm_num
    linarith
  have hη' : η ≤ 1 / 1000 := by
    have h := eta_tiny ev.hη1
    have : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
    linarith
  obtain ⟨hAa, hAb⟩ := abs_le.mp hA
  obtain ⟨hAa2, hAb2⟩ := abs_le.mp hA2
  obtain ⟨hOa, hOb⟩ := abs_le.mp hO
  have h1 : |A + O - t| ≤ 1 / 16 + 1 / 100 + 1 / 500 := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |A + O| ≤ 51 := by
    rw [abs_le]; constructor <;> linarith
  have h3 := ev.hr.near ev.hu0 h1 h2 hM51
  linarith

theorem out_near (ev : Ctx u η M fl ex p w) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    |net.out fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  obtain ⟨a, b, c, hx, ha, hb, hc⟩ := init_ent ev i
  obtain ⟨f0, f1, f2⟩ := att_facts ev i hi
  obtain ⟨tb0, tb1⟩ := target_bd w i hi
  have m0 := mlp_small ev (p.b2 0 0) (ev.hp.b2 0 0)
  have m1 := mlp_small ev (p.b2 0 1) (ev.hp.b2 0 1)
  have m2 := mlp_small ev (p.b2 0 2) (ev.hp.b2 0 2)
  have tabs : |((target w i : ℕ) : ℝ)| ≤ 3 := by
    rw [abs_of_nonneg tb0]; exact tb1
  have y0 := add_step ev ha f0 (add_zero _) (cv_abs _) m0
  have y1 := add_step ev hb f1 (add_zero _) (cg_abs _) m1
  have y2 := add_step ev hc f2 (zero_add _) tabs m2
  have hCy := close3 y0 y1 y2 (cv_abs _) (cg_abs _) tabs
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  obtain ⟨ho1, ho2⟩ := ardot3 ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 net.outW rfl
    (by simp [net]) _ _ (by simp) (by norm_num) (by norm_num) hCy p.oW ev.hp.oW
  have hq : ∀ x y z : ℝ, dotQ net.outW [x, y, z] = z := by
    intro x y z
    simp [dotQ, net]
  have habs : absSum net.outW = 1 := by simp [absSum, net]
  rw [hq] at ho1
  have ho1' : |ardot fl net.outW
      [fl (fl (a + att fl ex p w i z3 0) + fl (0 + asw fl 0 (p.b2 0 0))),
       fl (fl (b + att fl ex p w i z3 1) + fl (0 + asw fl 0 (p.b2 0 1))),
       fl (fl (c + att fl ex p w i [1, 0, 0] 2) + fl (0 + asw fl 0 (p.b2 0 2)))] p.oW 0 0
      - ((target w i : ℕ) : ℝ)| ≤ 1 / 16 + 1 / 100 := by
    rw [habs] at ho1
    linarith [ho1]
  have hob : |asw fl net.outB p.oB| ≤ 1 / 500 := by
    have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 5 (by norm_num)) net.outB ev.hp.oB
      (by simp [net])
    have h0 : ((net.outB : ℚ) : ℝ) = 0 := by simp [net]
    rwa [h0, sub_zero] at h
  unfold ANet.out
  rw [run_vals fl ex p w i a b c hx]
  exact final_round ev ho1' ho2 hob

end Steps

theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη1 p hp w hw hn hnη hM i hi1 hi
  have ctx : Ctx u η M fl ex p w := ⟨hr, he, hu0, hu1, hη0, hη1, hp, hw, hn, hnη, hM⟩
  exact out_near ctx i hi1 hi

end Lane4.Case
