/-
Gated softmax transformer for "value of the last marked token among positions 1..i".

State width 3, embedding rows `[flag, val, res]`:
  BOS [0,0,0], tok1 [1,0,0], tok2/3/4 [0,1,0], tok5 [0,3,0].
One block, one head, no MLP: causal mask, slope 24, A = 0, gate g = [1,0,0], gb = -1/2
(a key is a candidate iff flag = 0, i.e. BOS or a marked token), V row 2 = [0,1,0]
(copy val into res), read-out = res.  BOS is always a candidate, so the candidate list is
never empty.
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
def vrow : List ℚ := [0, 1, 0]

def head1 : AHead :=
  { A := [z3, z3, z3], V := [z3, z3, vrow], mask := Mask.causal, m := 24, g := [1, 0, 0],
    gb := -1 / 2 }

def blk : ABlock :=
  { heads := [head1], W1 := [], b1 := [], W2 := [[], [], []], b2 := z3 }

def net : ANet :=
  { embed := [[0, 0, 0], [1, 0, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 3, 0]],
    blocks := [blk], outW := [0, 0, 1], outB := 0 }

/-! ### Ideal embedding -/

def fq (t : ℕ) : ℚ := if t = 1 then 1 else 0
def vq (t : ℕ) : ℚ := (val t : ℚ)

theorem vq_cast (t : ℕ) : ((vq t : ℚ) : ℝ) = ((val t : ℕ) : ℝ) := by simp [vq]

theorem val_le (t : ℕ) : val t ≤ 3 := by
  unfold val
  split_ifs <;> omega

theorem vq_abs (t : ℕ) : |((vq t : ℚ) : ℝ)| ≤ 3 := by
  rw [vq_cast, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast val_le t

theorem fq_abs (t : ℕ) : |((fq t : ℚ) : ℝ)| ≤ 3 := by
  unfold fq
  split_ifs <;> norm_num

theorem embed_row {t : ℕ} (h : t ≤ 5) : net.embed.getD t [] = [fq t, vq t, 0] := by
  interval_cases t <;>
    first
    | rfl
    | (simp [net, fq, vq, val]; done)
    | (norm_num [net, fq, vq, val]; done)

/-! ### The winner: the last position `j0 ≤ i` that is BOS or marked -/

theorem take_succ' : ∀ (w : List ℕ) (i : ℕ) (h : i < w.length),
    w.take (i + 1) = w.take i ++ [w[i]]
  | [], i, h => by simp at h
  | a :: t, 0, h => by first | rfl | simp
  | a :: t, i + 1, h => by
      have h' : i < t.length := by simpa using h
      have := take_succ' t i h'
      show a :: t.take (i + 1) = a :: (t.take i ++ [t[i]])
      rw [this]

theorem exists_win (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) :
    ∀ i, i ≤ w.length → ∃ j0, j0 ≤ i ∧ tokAt w j0 ≠ 1 ∧
      (∀ k, j0 < k → k ≤ i → tokAt w k = 1) ∧ lastv (w.take i) = val (tokAt w j0) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨0, le_refl _, ?_, ?_, ?_⟩
    · rw [Lane4.Seq.tokAt_zero]; omega
    · intro k h1 h2; omega
    · rw [Lane4.Seq.tokAt_zero]; simp [lastv, val]
  | succ i ih =>
    intro hi
    have hi' : i < w.length := by omega
    obtain ⟨j0, hj0, hne, hall, hl⟩ := ih (by omega)
    have hti : tokAt w (i + 1) = w[i] := Lane4.Seq.tokAt_succ w i hi'
    have hmem : w[i] ∈ w := List.getElem_mem hi'
    obtain ⟨h1, h5⟩ := hw _ hmem
    have hlast : lastv (w.take (i + 1)) =
        if val w[i] = 0 then lastv (w.take i) else val w[i] := by
      unfold lastv
      rw [take_succ' w i hi', List.foldl_append]
      first | rfl | simp
    by_cases h : w[i] = 1
    · refine ⟨j0, by omega, hne, ?_, ?_⟩
      · intro k hk1 hk2
        by_cases hk : k = i + 1
        · rw [hk, hti, h]
        · exact hall k hk1 (by omega)
      · rw [hlast, h, hl]
        simp [val]
    · refine ⟨i + 1, le_refl _, ?_, ?_, ?_⟩
      · rw [hti]; exact h
      · intro k hk1 hk2; omega
      · have hv : val w[i] ≠ 0 := by
          have h25 : w[i] = 2 ∨ w[i] = 3 ∨ w[i] = 4 ∨ w[i] = 5 := by omega
          rcases h25 with hh | hh | hh | hh <;> simp [val, hh]
        rw [hlast, hti, if_neg hv]

/-! ### Definitions used to state the proof -/

noncomputable def xhat (w : List ℕ) (j : ℕ) : List ℝ :=
  [((fq (tokAt w j) : ℚ) : ℝ), ((vq (tokAt w j) : ℚ) : ℝ), 0]

noncomputable def cs (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : List ℕ :=
  head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

noncomputable def sc (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : ℕ → ℝ :=
  fun j => head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i j

noncomputable def att (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (r : List ℚ) (k : ℕ) :
    ℝ :=
  savg fl ex (cs fl p w i) (sc fl p w i) (fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0)

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (j : ℕ) (h : tokAt w j ≤ 5) :
    net.init fl p w j = [asw fl (fq (tokAt w j)) (p.E (tokAt w j) 0),
      asw fl (vq (tokAt w j)) (p.E (tokAt w j) 1), asw fl 0 (p.E (tokAt w j) 2)] := by
  show aswRow fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0 = _
  rw [embed_row h]
  rfl

theorem attn_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
      (net.init fl p w) i =
    [att fl ex p w i z3 0, att fl ex p w i z3 1, att fl ex p w i vrow 2] := rfl

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
       fl (fl (c + att fl ex p w i vrow 2) + fl (0 + asw fl 0 (p.b2 0 2)))] := by
  rw [run_eq, hx, attn_eq]
  rfl

/-! ### Ideal dot products -/

theorem dq0 (w : List ℕ) (j : ℕ) : dotQ z3 (xhat w j) = 0 := by
  simp [dotQ, z3, xhat]

theorem dqv (w : List ℕ) (j : ℕ) : dotQ vrow (xhat w j) = ((vq (tokAt w j) : ℚ) : ℝ) := by
  simp [dotQ, vrow, xhat]

theorem dqg (w : List ℕ) (j : ℕ) : dotQ head1.g (xhat w j) = ((fq (tokAt w j) : ℚ) : ℝ) := by
  simp [dotQ, head1, xhat]

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

theorem absSum_z3 : absSum z3 = 0 := by simp [absSum, z3]

theorem relu_fl_pos {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) {X : ℝ} (hM : 2 ≤ M)
    (hX : 1 / 4 ≤ X) (hX2 : X ≤ 2) : Lane4.relu (fl X) ≠ 0 := by
  have hXabs : |X| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hl := hr.lower hu0 hXabs hM
  have hu2 : u * 2 ≤ 1 / 2 ^ 24 * 2 := mul_le_mul_of_nonneg_right hu (by norm_num)
  have hη' := eta_tiny hη
  have hc : (1 : ℝ) / 2 ^ 24 * 2 + 1 / 10 ^ 40 ≤ 1 / 8 := by norm_num
  have hpos : 0 < fl X := by linarith
  have hr' : 0 < Lane4.relu (fl X) := by
    unfold Lane4.relu
    exact lt_max_of_lt_left hpos
  exact hr'.ne'

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

/-! ### Step 0: stored weights and dot products -/

theorem asw_c (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149)
    (hM : 5 ≤ M) (a : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 1000) (ha : |(a : ℝ)| ≤ 3) :
    |asw fl a d - (a : ℝ)| ≤ 1 / 500 := by
  have h := asw_near hr hu0 a hd (by linarith)
  have h1 : u * (|(a : ℝ)| + 1 / 1000) ≤ 1 / 2 ^ 24 * 4 :=
    mul_le_mul hu (by linarith) (by positivity) (by positivity)
  have h2 := eta_tiny hη
  have h3 : (1 : ℝ) / 2 ^ 24 * 4 + 1 / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

theorem ardotA (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 2 ^ 149) (hM : (2 : ℝ) ^ 30 ≤ M) (r : List ℚ) (hr3 : r.length = 3)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (x xh : List ℝ) (hx : x.length = 3) {e : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 10) (hC : Close x xh e 3) (d : ℕ → ℝ)
    (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r x d 0 0 - dotQ r xh| ≤ absSum r * e + 1 / 90 := by
  have h20 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
  have key := ardot_near_abs u η M (1 / 1000) fl hr hu0 hu hη0 hη (by norm_num) (by norm_num)
    r x xh d 1 3 e (by omega) (by omega) hC hd hW (by norm_num) (by norm_num) he0
    (by rw [h20]; linarith) hM
  have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  have h16 : (2 : ℝ) ^ 16 = 65536 := by norm_num
  have h100 : (1 : ℝ) / 2 ^ 100 = 1 / 1267650600228229401496703205376 := by norm_num
  rw [hr3] at key
  simp only [h3, h16, h100] at key
  linarith

/-! ### Step 1: the starting state -/

theorem init_ent (ev : Ctx u η M fl ex p w) (j : ℕ) :
    ∃ a b c : ℝ, net.init fl p w j = [a, b, c] ∧
      |a - ((fq (tokAt w j) : ℚ) : ℝ)| ≤ 1 / 500 ∧
      |b - ((vq (tokAt w j) : ℚ) : ℝ)| ≤ 1 / 500 ∧ |c - 0| ≤ 1 / 500 := by
  have ht := tok_le w ev.hw j
  have hM5 : (5 : ℝ) ≤ M := ev.range 5 (by norm_num)
  refine ⟨_, _, _, init_eq fl p w j ht, ?_, ?_, ?_⟩
  · exact asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM5 _ (ev.hp.E (tokAt w j) 0) (fq_abs _)
  · exact asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM5 _ (ev.hp.E (tokAt w j) 1) (vq_abs _)
  · have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM5 (0 : ℚ) (ev.hp.E (tokAt w j) 2) (by simp)
    simpa using h

theorem init_close (ev : Ctx u η M fl ex p w) (j : ℕ) :
    (net.init fl p w j).length = 3 ∧ Close (net.init fl p w j) (xhat w j) (1 / 500) 3 := by
  obtain ⟨a, b, c, hx, ha, hb, hc⟩ := init_ent ev j
  rw [hx]
  refine ⟨rfl, ?_⟩
  unfold xhat
  exact close3 ha hb hc (fq_abs _) (vq_abs _) (by norm_num)

/-! ### Step 2: the gate -/

theorem gate_pre (ev : Ctx u η M fl ex p w) (j : ℕ) :
    |(ardot fl head1.g (net.init fl p w j) (p.g 0 0) 0 0 + asw fl head1.gb (p.gb 0 0))
        - (((fq (tokAt w j) : ℚ) : ℝ) - 1 / 2)| ≤ 1 / 50 := by
  obtain ⟨hlen, hC⟩ := init_close ev j
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have h := ardotA ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 head1.g rfl (by simp [head1])
    _ _ hlen (by norm_num) (by norm_num) hC (p.g 0 0) (ev.hp.g 0 0)
  have habs : absSum head1.g = 1 := by simp [absSum, head1]
  rw [dqg, habs] at h
  have hgb : ((head1.gb : ℚ) : ℝ) = -1 / 2 := by
    first | norm_num [head1] | simp [head1]
  have hb := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 5 (by norm_num)) head1.gb
    (ev.hp.gb 0 0) (by rw [hgb, abs_le]; constructor <;> norm_num)
  rw [hgb] at hb
  obtain ⟨h1a, h1b⟩ := abs_le.mp h
  obtain ⟨hba, hbb⟩ := abs_le.mp hb
  rw [abs_le]
  constructor <;> linarith

theorem gate_zero (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : tokAt w j ≠ 1) :
    head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) = 0 := by
  have h := gate_pre ev j
  have hf : ((fq (tokAt w j) : ℚ) : ℝ) = 0 := by simp [fq, hj]
  rw [hf] at h
  obtain ⟨h1, h2⟩ := abs_le.mp h
  have hM3 : (3 : ℝ) ≤ M := ev.range 3 (by norm_num)
  unfold AHead.gate
  exact relu_fl_zero ev.hr (by linarith) (by linarith)

theorem gate_pos (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : tokAt w j = 1) :
    head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) ≠ 0 := by
  have h := gate_pre ev j
  have hf : ((fq (tokAt w j) : ℚ) : ℝ) = 1 := by simp [fq, hj]
  rw [hf] at h
  obtain ⟨h1, h2⟩ := abs_le.mp h
  have hM3 : (3 : ℝ) ≤ M := ev.range 3 (by norm_num)
  unfold AHead.gate
  exact relu_fl_pos ev.hr ev.hu0 ev.hu1 ev.hη1 (by linarith) (by linarith) (by linarith)

theorem mem_cs (ev : Ctx u η M fl ex p w) (i j : ℕ) :
    j ∈ cs fl p w i ↔ j ≤ i ∧ tokAt w j ≠ 1 := by
  unfold cs
  rw [AHead.mem_cands]
  have hm : head1.mask = Mask.causal := rfl
  rw [hm, Lane4.Seq.mem_cand_causal]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => gate_pos ev j h h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, gate_zero ev j h2⟩

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
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (hA : absSum r ≤ 1) (j : ℕ) (d : ℕ → ℝ)
    (hd : ∀ c, |d c| ≤ 1 / 1000) :
    |ardot fl r (net.init fl p w j) d 0 0 - dotQ r (xhat w j)| ≤ 1 / 60 := by
  obtain ⟨hlen, hC⟩ := init_close ev j
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have h := ardotA ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 r hr3 hW _ _ hlen (by norm_num)
    (by norm_num) hC d hd
  have h2 : absSum r * (1 / 500) ≤ 1 / 500 := by linarith
  linarith

theorem content_small (ev : Ctx u η M fl ex p w) (i k : ℕ) :
    |Lane4.RSeq.pdot fl (net.init fl p w i)
        (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) 0| ≤ 1 / 5 := by
  obtain ⟨hli, hCi⟩ := init_close ev i
  obtain ⟨hlk, hCk⟩ := init_close ev k
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have hrow : ∀ r : ℕ, |ardot fl z3 (net.init fl p w k) (p.A 0 0 r) 0 0 - 0| ≤ 1 / 90 := by
    intro r
    have h := ardotA ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 z3 rfl (by simp [z3]) _ _ hlk
      (by norm_num) (by norm_num) hCk (p.A 0 0 r) (ev.hp.A 0 0 r)
    rw [dq0, absSum_z3] at h
    linarith
  have hy : armat fl head1.A (net.init fl p w k) (p.A 0 0) 0 =
      [ardot fl z3 (net.init fl p w k) (p.A 0 0 0) 0 0,
       ardot fl z3 (net.init fl p w k) (p.A 0 0 1) 0 0,
       ardot fl z3 (net.init fl p w k) (p.A 0 0 2) 0 0] := rfl
  have hCy : Close (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) [0, 0, 0] (1 / 90) 0 := by
    rw [hy]
    exact close3 (hrow 0) (hrow 1) (hrow 2) (by norm_num) (by norm_num) (by norm_num)
  have hlen_y : (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0).length = 3 := by
    simp [hy]
  obtain ⟨p1, -⟩ := pdot_near u η M fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (net.init fl p w i)
    (xhat w i) (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) [0, 0, 0] 3 0 (1 / 500) (1 / 90)
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

/-! ### Step 4-5: the head returns the value at the winner -/

theorem row_attn (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr3 : r.length = 3)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (hA : absSum r ≤ 1)
    (hq : ∀ j, |dotQ r (xhat w j)| ≤ 3) (k : ℕ)
    (i j0 : ℕ) (hi : i ≤ w.length) (hj0 : j0 ≤ i) (hne : tokAt w j0 ≠ 1)
    (hall : ∀ k', j0 < k' → k' ≤ i → tokAt w k' = 1) :
    |att fl ex p w i r k - dotQ r (xhat w j0)| ≤ 1 / 20 := by
  have hj : j0 ∈ cs fl p w i := (mem_cs ev i j0).mpr ⟨hj0, hne⟩
  have hlen := cs_len fl p w i hi
  have hgap : ∀ k' ∈ cs fl p w i, k' ≠ j0 →
      sc fl p w i k' ≤ sc fl p w i j0 - 16 * ((ndist j0 k' : ℕ) : ℝ) := by
    intro k' hk' hne'
    obtain ⟨hk'i, hk'm⟩ := (mem_cs ev i k').mp hk'
    have hlt : k' < j0 := by
      by_contra hcon
      have h1 : j0 < k' := by omega
      exact hk'm (hall k' h1 hk'i)
    rw [ndist_cast]
    have hg := score_gap ev i j0 k' (by omega) (by omega) hlt
    have h1 : (k' : ℝ) + 1 ≤ (j0 : ℝ) := by
      have h : k' + 1 ≤ j0 := hlt
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
      |ardot fl r (net.init fl p w k') (p.V 0 0 k) 0 0| ≤ (31 / 10 : ℝ) := by
    intro k' _
    have h1 := val_near ev r hr3 hW hA k' (p.V 0 0 k) (ev.hp.V 0 0 k)
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h2a, h2b⟩ := abs_le.mp (hq k')
    rw [abs_le]; constructor <;> linarith
  have hBM : 4 * (31 / 10 : ℝ) + 4 ≤ M := by
    have := ev.range 17 (by norm_num)
    linarith
  obtain ⟨hs1, -⟩ := soft_near (s := sc fl p w i)
    (f := fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0) ev.hr ev.he ev.hu0 ev.hu1
    ev.hη0 ev.hη1 (cs_nodup fl p w i) hlen ev.hn ev.hnη hj hgap hS hSM hf hBM
  have hs1' : |att fl ex p w i r k - ardot fl r (net.init fl p w j0) (p.V 0 0 k) 0 0|
      ≤ (31 / 10 : ℝ) / 100 + 1 / 2 ^ 90 := hs1
  have hv := val_near ev r hr3 hW hA j0 (p.V 0 0 k) (ev.hp.V 0 0 k)
  have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 1000000 := by norm_num
  have h3 := abs_sub_le (att fl ex p w i r k)
    (ardot fl r (net.init fl p w j0) (p.V 0 0 k) 0 0) (dotQ r (xhat w j0))
  linarith

/-! ### Step 6 -/

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
    |fl (fl (x + s) + m) - y| ≤ 1 / 10 := by
  have hM4 : (4 : ℝ) ≤ M := ev.range 4 (by norm_num)
  have hu4 : u * 4 ≤ 1 / 1000000 := by
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

theorem final_round (ev : Ctx u η M fl ex p w) {A O t : ℝ} (hA : |A - t| ≤ 1 / 8)
    (hT : |t| ≤ 3) (hO : |O| ≤ 1 / 500) : |fl (A + O) - t| ≤ 1 / 4 := by
  have hM4 : (4 : ℝ) ≤ M := ev.range 4 (by norm_num)
  have hu4 : u * 4 ≤ 1 / 1000000 := by
    have h := ev.hu1
    have : (1 : ℝ) / 2 ^ 24 ≤ 1 / 4000000 := by norm_num
    linarith
  have hη' : η ≤ 1 / 1000000 := by
    have h := eta_tiny ev.hη1
    have : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000000 := by norm_num
    linarith
  obtain ⟨hAa, hAb⟩ := abs_le.mp hA
  obtain ⟨hTa, hTb⟩ := abs_le.mp hT
  obtain ⟨hOa, hOb⟩ := abs_le.mp hO
  have h1 : |A + O - t| ≤ 1 / 8 + 1 / 500 := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |A + O| ≤ 4 := by
    rw [abs_le]; constructor <;> linarith
  have h3 := ev.hr.near ev.hu0 h1 h2 hM4
  linarith

/-! ### The theorem -/

theorem out_near (ev : Ctx u η M fl ex p w) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    |net.out fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  obtain ⟨j0, hj0, hne, hall, hl⟩ := exists_win w ev.hw i hi
  obtain ⟨a, b, c, hx, ha, hb, hc⟩ := init_ent ev i
  have r0 := row_attn ev z3 rfl (by simp [z3]) (by simp [absSum, z3])
    (fun j => by rw [dq0]; norm_num) 0 i j0 hi hj0 hne hall
  have r1 := row_attn ev z3 rfl (by simp [z3]) (by simp [absSum, z3])
    (fun j => by rw [dq0]; norm_num) 1 i j0 hi hj0 hne hall
  have r2 := row_attn ev vrow rfl (by simp [vrow]) (by simp [absSum, vrow])
    (fun j => by rw [dqv]; exact vq_abs _) 2 i j0 hi hj0 hne hall
  rw [dq0] at r0 r1
  rw [dqv] at r2
  have m0 := mlp_small ev (p.b2 0 0) (ev.hp.b2 0 0)
  have m1 := mlp_small ev (p.b2 0 1) (ev.hp.b2 0 1)
  have m2 := mlp_small ev (p.b2 0 2) (ev.hp.b2 0 2)
  have y0 := add_step ev ha r0 (add_zero _) (fq_abs _) m0
  have y1 := add_step ev hb r1 (add_zero _) (vq_abs _) m1
  have y2 := add_step ev hc r2 (zero_add _) (vq_abs _) m2
  have hCy := close3 y0 y1 y2 (fq_abs _) (vq_abs _) (vq_abs _)
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have ho1 := ardotA ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 net.outW rfl (by simp [net]) _ _
    (by simp) (by norm_num) (by norm_num) hCy p.oW ev.hp.oW
  have habs : absSum net.outW = 1 := by simp [absSum, net]
  have hq : ∀ x y z : ℝ, dotQ net.outW [x, y, z] = z := by
    intro x y z
    simp [dotQ, net]
  rw [hq, habs] at ho1
  have hob : |asw fl net.outB p.oB| ≤ 1 / 500 := by
    have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 5 (by norm_num)) net.outB ev.hp.oB
      (by simp [net])
    have h0 : ((net.outB : ℚ) : ℝ) = 0 := by simp [net]
    rwa [h0, sub_zero] at h
  have ht : ((target w i : ℕ) : ℝ) = ((vq (tokAt w j0) : ℚ) : ℝ) := by
    rw [vq_cast]
    have h' : target w i = val (tokAt w j0) := hl
    rw [h']
  rw [ht]
  unfold ANet.out
  rw [run_vals fl ex p w i a b c hx]
  exact final_round ev (le_trans ho1 (by norm_num)) (vq_abs _) hob

end Steps

theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη1 p hp w hw hn hnη hM i hi1 hi
  have ctx : Ctx u η M fl ex p w := ⟨hr, he, hu0, hu1, hη0, hη1, hp, hw, hn, hnη, hM⟩
  exact out_near ctx i hi1 hi

end Lane4.Case
