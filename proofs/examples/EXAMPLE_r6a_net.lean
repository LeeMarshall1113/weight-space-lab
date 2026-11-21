/-
WORKED EXAMPLE on a task outside the four task families: output the previous token
(2 real tokens; the token before position 1 is BOS = 0), in the GATED architecture of
AGate.lean under ADDITIVE perturbation of every weight. It was checked by the same checker
and passed, including the two corollaries of Final.lean. It shows the parts the checker
joins: the lane's Spec.lean, a Solution.lean, and (not shown) Final.lean. Only the part
after the SOLUTION START marker is what you write. (It was proved at radius 1/1000; your
task's radius is in your Spec.lean.)

Method: nothing is exactly zero here, so there are no closed forms by `simp`. Every
quantity is an IDEAL value plus an error bound (`Close`, `ardot_near_abs`, `ardot_near`,
`pdot_near`), the gate is shown to be exactly 0 on the wanted keys (`relu_fl_zero`), the
winner's score gap comes from `bias_gap` minus the content noise, `soft_near` returns the
winner's value, and a final chain of absolute errors closes the 1/4 budget.
This example has one head, all keys gated in, and no MLP; your task will need more.
-/

-- ===== Spec.lean (given) =====
namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

/-- Target at position `i`: the token one position earlier (BOS counts as 0). -/
def target (w : List ℕ) (i : ℕ) : ℕ := tokAt w (i - 1)

def Statement (N : ANet) : Prop :=
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Rnd u η M fl → ExpM u η ex →
  0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  ∀ p : APert, p.Within (1 / 1000) →
  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) →
  u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 → η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100 →
  2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M →
  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → |N.out fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4

end Lane4.Case

-- ===== Solution.lean (SOLUTION START) =====
/-
WORKED EXAMPLE for the additive-perturbation framework (`AGate.lean`): a gated softmax
transformer that outputs the PREVIOUS token (tokens 1, 2; BOS = 0).

THE NETWORK.  State width 3, embedding rows `[val, res, one]`:
  BOS `[0,0,1]`, token 1 `[1,0,1]`, token 2 `[2,0,1]`.
One block, one head, no MLP:
  * mask `strict` (query `i` sees keys `j < i`), slope `m = 24` (the only thing that
    distinguishes positions: the bias `24 * (j - i)` makes the NEAREST earlier key win),
  * score matrix `A = 0`, gate weights `g = 0`, gate bias `gb = -1` (every key is a candidate),
  * value matrix `V` with row 1 = `[1,0,0]` (copy `val` into `res`), other rows 0,
  * read-out `outW = [0,1,0]` (read `res`), `outB = 0`.

THE METHOD (IDEAL VALUE + ERROR BOUND).  Every weight, also those written 0, is `fl (w + d)`
with `|d| ≤ 1/1000`, so nothing is exactly zero and nothing can be computed in closed form.
Instead each quantity gets an IDEAL value (what the network would compute with the written
weights and exact arithmetic) and a bound on its distance from the ideal.  The proof is a
chain of such statements, each built from the lemmas of the kit:

   1. `init_close`  : state at `j`  is within 1/500 of the ideal `[tok j, 0, 1]`.
   2. `gate_zero`   : the gate pre-activation is about -1, so the gate is exactly 0 and the
                      candidates are exactly the keys the mask allows (`mem_cs`).
   3. `content_small`, `score_gap` : the content part of a score is tiny (≤ 1/10), so the
                      bias wins: the previous position beats an earlier key by ≥ 16 per
                      unit of distance (what `soft_near` needs).
   4. `val_near`    : a value `V_r · x_j` is within 1/75 of its ideal `dotQ V_r [tok j,0,1]`.
   5. `row_attn`    : `soft_near` for any value row: the head output is within 1/28 of the
                      ideal value at position `i - 1`.
   6. `add_step`, `final_round`, `out_near` : residual add, (almost) empty MLP, read-out.

The constants are generous: the final error is about 0.16 against the budget 1/4.
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
  { A := [z3, z3, z3], V := [z3, [1, 0, 0], z3], mask := Mask.strict, m := 24, g := z3, gb := -1 }

def blk : ABlock :=
  { heads := [head1], W1 := [], b1 := [], W2 := [[], [], []], b2 := z3 }

def net : ANet :=
  { embed := [[0, 0, 1], [1, 0, 1], [2, 0, 1]], blocks := [blk], outW := [0, 1, 0], outB := 0 }

/-! ### Definitions used to state the proof (no new behaviour) -/

/-- The ideal state at position `j`: `[tok j, 0, 1]`. -/
noncomputable def xhat (w : List ℕ) (j : ℕ) : List ℝ := [((tokAt w j : ℕ) : ℝ), 0, 1]

/-- The candidate keys of the head for query `i` (as the network computes them). -/
noncomputable def cs (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : List ℕ :=
  head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

/-- The scores of the head for query `i`. -/
noncomputable def sc (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : ℕ → ℝ :=
  fun j => head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i j

/-- Output entry `k` of the head, whose value row is `r` (the softmax average). -/
noncomputable def att (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (r : List ℚ) (k : ℕ) :
    ℝ :=
  savg fl ex (cs fl p w i) (sc fl p w i) (fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0)

/-! ### Unfolding the forward pass (definitional) -/

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (j : ℕ) : tokAt w j ≤ 2 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem tk_bound (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (j : ℕ) :
    0 ≤ ((tokAt w j : ℕ) : ℝ) ∧ ((tokAt w j : ℕ) : ℝ) ≤ 2 :=
  ⟨Nat.cast_nonneg _, by exact_mod_cast tok_le w hw j⟩

theorem tk_abs (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (j : ℕ) :
    |((tokAt w j : ℕ) : ℝ)| ≤ 2 := by
  obtain ⟨h0, h1⟩ := tk_bound w hw j
  rw [abs_of_nonneg h0]
  exact h1

/-- The embedding row of a real token `t ≤ 2` is `[t, 0, 1]`. -/
theorem embed_row {t : ℕ} (h : t ≤ 2) : net.embed.getD t [] = [(t : ℚ), 0, 1] := by
  interval_cases t <;> first | rfl | simp [net]

/-- The starting state at `j`, as an explicit list of stored weights. -/
theorem init_eq (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (j : ℕ) (h : tokAt w j ≤ 2) :
    net.init fl p w j = [asw fl ((tokAt w j : ℕ) : ℚ) (p.E (tokAt w j) 0),
      asw fl 0 (p.E (tokAt w j) 1), asw fl 1 (p.E (tokAt w j) 2)] := by
  show aswRow fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0 = _
  rw [embed_row h]
  rfl

/-- The head's output, row by row (rows 0 and 2 of `V` are zero, row 1 copies `val`). -/
theorem attn_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
      (net.init fl p w) i =
    [att fl ex p w i z3 0, att fl ex p w i [1, 0, 0] 1, att fl ex p w i z3 2] := rfl

/-- The whole forward pass at position `i`: state + head output + (empty MLP) bias terms. -/
theorem run_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    net.run fl ex p w i =
      Lane4.RSeq.radd fl (Lane4.RSeq.radd fl (net.init fl p w i)
        (head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
          (net.init fl p w) i))
        [fl (0 + asw fl 0 (p.b2 0 0)), fl (0 + asw fl 0 (p.b2 0 1)),
         fl (0 + asw fl 0 (p.b2 0 2))] := rfl

/-- The final state as three explicit entries, given the starting state `[a, b, c]`. -/
theorem run_vals (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (a b c : ℝ)
    (hx : net.init fl p w i = [a, b, c]) :
    net.run fl ex p w i =
      [fl (fl (a + att fl ex p w i z3 0) + fl (0 + asw fl 0 (p.b2 0 0))),
       fl (fl (b + att fl ex p w i [1, 0, 0] 1) + fl (0 + asw fl 0 (p.b2 0 1))),
       fl (fl (c + att fl ex p w i z3 2) + fl (0 + asw fl 0 (p.b2 0 2)))] := by
  rw [run_eq, hx, attn_eq]
  rfl

/-! ### Ideal dot products of the written weights (computed once) -/

theorem dq0 (w : List ℕ) (j : ℕ) : dotQ z3 (xhat w j) = 0 := by
  simp [dotQ, z3, xhat]

theorem dq1 (w : List ℕ) (j : ℕ) : dotQ [1, 0, 0] (xhat w j) = ((tokAt w j : ℕ) : ℝ) := by
  simp [dotQ, xhat]

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

/-! ### The context: all hypotheses of `Statement`, bundled -/

structure Ctx (u η M : ℝ) (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) : Prop where
  hr : Rnd u η M fl
  he : ExpM u η ex
  hu0 : 0 ≤ u
  hu1 : u ≤ 1 / 2 ^ 24
  hη0 : 0 ≤ η
  hη1 : η ≤ 1 / 2 ^ 149
  hp : p.Within (1 / 1000)
  hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2
  hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256
  hnη : η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100
  hM : 2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M

section Steps

variable {u η M : ℝ} {fl ex : ℝ → ℝ} {p : APert} {w : List ℕ}

/-- Range: any constant up to `2^40` fits in `M`. -/
theorem Ctx.range (ev : Ctx u η M fl ex p w) (c : ℝ) (hc : c ≤ 2 ^ 40) : c ≤ M :=
  range_const ev.hM (by omega) hc

/-- Range: `c * n ≤ M` for `0 ≤ c ≤ 2^40` (`n` = number of positions). -/
theorem Ctx.rangeN (ev : Ctx u η M fl ex p w) (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 2 ^ 40) :
    c * ((w.length + 1 : ℕ) : ℝ) ≤ M :=
  range_lin ev.hM (by omega) hc0 hc

/-- `u * (c * n) ≤ c / 256`. -/
theorem u_mul (ev : Ctx u η M fl ex p w) (c : ℝ) (hc : 0 ≤ c) :
    u * (c * ((w.length + 1 : ℕ) : ℝ)) ≤ c / 256 := by
  have h : u * (c * ((w.length + 1 : ℕ) : ℝ)) = c * (u * ((w.length + 1 : ℕ) : ℝ)) := by ring
  rw [h]
  have := mul_le_mul_of_nonneg_left ev.hn hc
  linarith

/-! ### Step 0: a stored weight is close to its written value -/

/-- A stored weight `fl (a + d)` with `|d| ≤ 1/1000` and `|a| ≤ 2` is within 1/500 of `a`. -/
theorem asw_c (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149)
    (hM : 4 ≤ M) (a : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 1000) (ha : |(a : ℝ)| ≤ 2) :
    |asw fl a d - (a : ℝ)| ≤ 1 / 500 := by
  have h := asw_near hr hu0 a hd (by linarith)
  have h1 : u * (|(a : ℝ)| + 1 / 1000) ≤ 1 / 2 ^ 24 * 3 :=
    mul_le_mul hu (by linarith) (by positivity) (by positivity)
  have h2 := eta_tiny hη
  have h3 : (1 : ℝ) / 2 ^ 24 * 3 + 1 / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

/-- The kit's `ardot_near` specialised to width 3, written weights of size ≤ 1, entry error
`e ≤ 1/20`, ideal entries ≤ 2: error `3e + 1/150`, magnitude ≤ 40. -/
theorem ardot3 (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 2 ^ 149) (hM : (2 : ℝ) ^ 30 ≤ M) (r : List ℚ) (hr3 : r.length = 3)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (x xh : List ℝ) (hx : x.length = 3) {e : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 20) (hC : Close x xh e 2) (d : ℕ → ℝ)
    (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r x d 0 0 - dotQ r xh| ≤ 3 * e + 1 / 150 ∧ |ardot fl r x d 0 0| ≤ 40 := by
  have h20 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
  have key := ardot_near u η M (1 / 1000) fl hr hu0 hu hη0 hη (by norm_num) (by norm_num)
    r x xh d 1 2 e (by omega) (by omega) hC hd hW (by norm_num) (by norm_num) he0
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

/-! ### Step 1: the starting state is close to the ideal state -/

theorem init_ent (ev : Ctx u η M fl ex p w) (j : ℕ) :
    ∃ a b c : ℝ, net.init fl p w j = [a, b, c] ∧
      |a - ((tokAt w j : ℕ) : ℝ)| ≤ 1 / 500 ∧ |b - 0| ≤ 1 / 500 ∧ |c - 1| ≤ 1 / 500 := by
  have ht := tok_le w ev.hw j
  have hM4 : (4 : ℝ) ≤ M := ev.range 4 (by norm_num)
  obtain ⟨ht0, htR⟩ := tk_bound w ev.hw j
  have hc : ((((tokAt w j : ℕ) : ℚ)) : ℝ) = ((tokAt w j : ℕ) : ℝ) := by simp
  refine ⟨_, _, _, init_eq fl p w j ht, ?_, ?_, ?_⟩
  · have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM4 ((tokAt w j : ℕ) : ℚ)
      (ev.hp.E (tokAt w j) 0) (by rw [hc, abs_of_nonneg ht0]; exact htR)
    rwa [hc] at h
  · have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM4 (0 : ℚ) (ev.hp.E (tokAt w j) 1) (by simp)
    simpa using h
  · have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM4 (1 : ℚ) (ev.hp.E (tokAt w j) 2) (by simp)
    simpa using h

theorem init_close (ev : Ctx u η M fl ex p w) (j : ℕ) :
    (net.init fl p w j).length = 3 ∧ Close (net.init fl p w j) (xhat w j) (1 / 500) 2 := by
  obtain ⟨a, b, c, hx, ha, hb, hc⟩ := init_ent ev j
  rw [hx]
  refine ⟨rfl, ?_⟩
  unfold xhat
  exact close3 ha hb hc (tk_abs w ev.hw j) (by norm_num) (by norm_num)

/-! ### Step 2: the gate is exactly 0, so the candidates are the mask's positions -/

theorem gate_zero (ev : Ctx u η M fl ex p w) (j : ℕ) :
    head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) = 0 := by
  obtain ⟨hlen, hC⟩ := init_close ev j
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have h := ardot3 ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 head1.g rfl (by simp [head1, z3])
    _ _ hlen (by norm_num) (by norm_num) hC (p.g 0 0) (ev.hp.g 0 0)
  have hq : dotQ head1.g (xhat w j) = 0 := by simp [dotQ, head1, z3, xhat]
  rw [hq] at h
  obtain ⟨h1, -⟩ := h
  have hgb : ((head1.gb : ℚ) : ℝ) = -1 := by simp [head1]
  have hb := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) head1.gb
    (ev.hp.gb 0 0) (by rw [hgb]; norm_num)
  rw [hgb] at hb
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨hba, hbb⟩ := abs_le.mp hb
  have hM3 : (3 : ℝ) ≤ M := ev.range 3 (by norm_num)
  unfold AHead.gate
  exact relu_fl_zero ev.hr (by linarith) (by linarith)

theorem mem_cs (ev : Ctx u η M fl ex p w) (i j : ℕ) : j ∈ cs fl p w i ↔ j < i := by
  unfold cs
  rw [AHead.mem_cands]
  have hm : head1.mask = Mask.strict := rfl
  rw [hm, Lane4.Seq.mem_cand_strict]
  exact ⟨fun h => h.1, fun h => ⟨h, gate_zero ev j⟩⟩

theorem cs_nodup (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : (cs fl p w i).Nodup :=
  AHead.cands_nodup head1 fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

theorem cs_len (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (hi : i ≤ w.length) :
    (cs fl p w i).length ≤ w.length + 1 := by
  have h1 : (cs fl p w i).length ≤ (cand Mask.strict (w.length + 1) i).length :=
    List.length_filter_le _ _
  have h2 : (cand Mask.strict (w.length + 1) i).length = i := by simp [cand]
  omega

/-! ### Step 3: scores.  Content is tiny, so the position bias decides -/

/-- The ideal dot products of the written weights are 0 for the zero rows, so a value or a
score row applied to a stored state is within 1/75 of 0 (or of its ideal value). -/
theorem val_near (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr3 : r.length = 3)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (j : ℕ) (d : ℕ → ℝ) (hd : ∀ c, |d c| ≤ 1 / 1000) :
    |ardot fl r (net.init fl p w j) d 0 0 - dotQ r (xhat w j)| ≤ 1 / 75 := by
  obtain ⟨hlen, hC⟩ := init_close ev j
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have h := ardot3 ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 r hr3 hW _ _ hlen (by norm_num)
    (by norm_num) hC d hd
  linarith [h.1]

/-- The content part of a score: `x_i · (A x_k)` is at most 1/10 in absolute value. -/
theorem content_small (ev : Ctx u η M fl ex p w) (i k : ℕ) :
    |Lane4.RSeq.pdot fl (net.init fl p w i)
        (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) 0| ≤ 1 / 10 := by
  obtain ⟨hli, hCi⟩ := init_close ev i
  obtain ⟨hlk, hCk⟩ := init_close ev k
  have hrow : ∀ r : ℕ, |ardot fl z3 (net.init fl p w k) (p.A 0 0 r) 0 0 - 0| ≤ 1 / 75 := by
    intro r
    have h := val_near ev z3 rfl (by simp [z3]) k (p.A 0 0 r) (ev.hp.A 0 0 r)
    rwa [dq0] at h
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

/-- Every position bias is at most `26 n`. -/
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

/-- A score is at most `28 n` in absolute value. -/
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

/-- THE SCORE GAP: an earlier key `k < j` scores at least `16 (j - k)` below key `j`. -/
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

/-! ### Step 4-5: the head returns the value of the previous position -/

/-- For ANY value row `r` (written weights of size ≤ 1, ideal values ≤ 2) the head's output
entry is within 1/28 of the ideal value at position `i - 1`. -/
theorem row_attn (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr3 : r.length = 3)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (hq : ∀ j, |dotQ r (xhat w j)| ≤ 2) (k : ℕ)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    |att fl ex p w i r k - dotQ r (xhat w (i - 1))| ≤ 1 / 28 := by
  -- the winner: the previous position
  have hj : i - 1 ∈ cs fl p w i := (mem_cs ev i (i - 1)).mpr (by omega)
  have hlen := cs_len fl p w i hi
  -- the winner beats every other candidate by 16 per unit of distance
  have hgap : ∀ k' ∈ cs fl p w i, k' ≠ i - 1 →
      sc fl p w i k' ≤ sc fl p w i (i - 1) - 16 * ((ndist (i - 1) k' : ℕ) : ℝ) := by
    intro k' hk' hne
    have hk'i : k' < i := (mem_cs ev i k').mp hk'
    have hlt : k' < i - 1 := by omega
    rw [ndist_cast]
    have hg := score_gap ev i (i - 1) k' (by omega) (by omega) hlt
    have h1 : (k' : ℝ) + 1 ≤ ((i - 1 : ℕ) : ℝ) := by
      have h : k' + 1 ≤ i - 1 := hlt
      exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    exact hg
  -- scores and values are bounded
  have hS : ∀ k' ∈ cs fl p w i, |sc fl p w i k'| ≤ 28 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k' hk'
    have := (mem_cs ev i k').mp hk'
    exact score_abs ev i k' (by omega) (by omega)
  have hSM : 2 * (28 * ((w.length + 1 : ℕ) : ℝ)) ≤ M := by
    have := ev.rangeN 56 (by norm_num) (by norm_num)
    linarith
  have hf : ∀ k' ∈ cs fl p w i,
      |ardot fl r (net.init fl p w k') (p.V 0 0 k) 0 0| ≤ (21 / 10 : ℝ) := by
    intro k' _
    have h1 := val_near ev r hr3 hW k' (p.V 0 0 k) (ev.hp.V 0 0 k)
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h2a, h2b⟩ := abs_le.mp (hq k')
    rw [abs_le]; constructor <;> linarith
  have hBM : 4 * (21 / 10 : ℝ) + 4 ≤ M := by
    have := ev.range 13 (by norm_num)
    linarith
  obtain ⟨hs1, -⟩ := soft_near (s := sc fl p w i)
    (f := fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0) ev.hr ev.he ev.hu0 ev.hu1
    ev.hη0 ev.hη1 (cs_nodup fl p w i) hlen ev.hn ev.hnη hj hgap hS hSM hf hBM
  have hs1' : |att fl ex p w i r k - ardot fl r (net.init fl p w (i - 1)) (p.V 0 0 k) 0 0|
      ≤ (21 / 10 : ℝ) / 100 + 1 / 2 ^ 90 := hs1
  have hv := val_near ev r hr3 hW (i - 1) (p.V 0 0 k) (ev.hp.V 0 0 k)
  have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 1000000 := by norm_num
  have h3 := abs_sub_le (att fl ex p w i r k)
    (ardot fl r (net.init fl p w (i - 1)) (p.V 0 0 k) 0 0) (dotQ r (xhat w (i - 1)))
  linarith

/-! ### Step 6: residual add, the MLP's bias terms, the read-out -/

/-- The MLP is empty: its output entries are `fl (0 + asw 0 d)`, a number of size ≤ 1/100. -/
theorem mlp_small (ev : Ctx u η M fl ex p w) (d : ℝ) (hd : |d| ≤ 1 / 1000) :
    |fl (0 + asw fl 0 d)| ≤ 1 / 100 := by
  have h1 := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) (0 : ℚ) hd (by simp)
  have h1' : |asw fl 0 d| ≤ 1 / 500 := by simpa using h1
  have h2 : |(0 : ℝ) + asw fl 0 d| ≤ 1 / 500 := by rw [zero_add]; exact h1'
  have h3 := ev.hr.bound ev.hu0 h2 (ev.range (1 / 500) (by norm_num))
  have hu' : (1 : ℝ) / 2 ^ 24 ≤ 1 / 1000 := by norm_num
  have hη' := eta_tiny ev.hη1
  have hη'' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have := ev.hu1
  linarith

/-- One entry of the final state: `fl (fl (x + s) + m)` against its ideal `y = t + s'`. -/
theorem add_step (ev : Ctx u η M fl ex p w) {x s m t s' y : ℝ} (hx : |x - t| ≤ 1 / 500)
    (hs : |s - s'| ≤ 1 / 28) (hy : t + s' = y) (hy2 : |y| ≤ 2) (hm : |m| ≤ 1 / 100) :
    |fl (fl (x + s) + m) - y| ≤ 1 / 20 := by
  have hM3 : (3 : ℝ) ≤ M := ev.range 3 (by norm_num)
  have hu3 : u * 3 ≤ 1 / 1000000 := by
    have h := ev.hu1
    have : (1 : ℝ) / 2 ^ 24 ≤ 1 / 3000000 := by norm_num
    linarith
  have hη' : η ≤ 1 / 1000000 := by
    have h := eta_tiny ev.hη1
    have : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000000 := by norm_num
    linarith
  obtain ⟨hxa, hxb⟩ := abs_le.mp hx
  obtain ⟨hsa, hsb⟩ := abs_le.mp hs
  obtain ⟨hya, hyb⟩ := abs_le.mp hy2
  obtain ⟨hma, hmb⟩ := abs_le.mp hm
  have h1 : |x + s - y| ≤ 1 / 500 + 1 / 28 := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |x + s| ≤ 3 := by
    rw [abs_le]; constructor <;> linarith
  have h3 := ev.hr.near ev.hu0 h1 h2 hM3
  obtain ⟨h3a, h3b⟩ := abs_le.mp h3
  have h4 : |fl (x + s) + m - y| ≤ 1 / 500 + 1 / 28 + (u * 3 + η) + 1 / 100 := by
    rw [abs_le]; constructor <;> linarith
  have h5 : |fl (x + s) + m| ≤ 3 := by
    rw [abs_le]; constructor <;> linarith
  have h6 := ev.hr.near ev.hu0 h4 h5 hM3
  linarith

/-- The read-out and its bias: from the dot product's error to the final error. -/
theorem final_round (ev : Ctx u η M fl ex p w) {A O t : ℝ} (hA : |A - t| ≤ 3 * (1 / 20) + 1 / 150)
    (hA2 : |A| ≤ 40) (hO : |O| ≤ 1 / 500) : |fl (A + O) - t| ≤ 1 / 4 := by
  have hM41 : (41 : ℝ) ≤ M := ev.range 41 (by norm_num)
  have hu41 : u * 41 ≤ 1 / 1000 := by
    have h := ev.hu1
    have : (1 : ℝ) / 2 ^ 24 ≤ 1 / 41000 := by norm_num
    linarith
  have hη' : η ≤ 1 / 1000 := by
    have h := eta_tiny ev.hη1
    have : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
    linarith
  obtain ⟨hAa, hAb⟩ := abs_le.mp hA
  obtain ⟨hAa2, hAb2⟩ := abs_le.mp hA2
  obtain ⟨hOa, hOb⟩ := abs_le.mp hO
  have h1 : |A + O - t| ≤ 3 * (1 / 20) + 1 / 150 + 1 / 500 := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |A + O| ≤ 41 := by
    rw [abs_le]; constructor <;> linarith
  have h3 := ev.hr.near ev.hu0 h1 h2 hM41
  linarith

/-! ### The theorem -/

theorem out_near (ev : Ctx u η M fl ex p w) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    |net.out fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  obtain ⟨a, b, c, hx, ha, hb, hc⟩ := init_ent ev i
  -- the head's three output entries against their ideal values 0, tok(i-1), 0
  have r0 := row_attn ev z3 rfl (by simp [z3]) (fun j => by rw [dq0]; norm_num) 0 i hi1 hi
  have r1 := row_attn ev [1, 0, 0] rfl (by simp)
    (fun j => by rw [dq1]; exact tk_abs w ev.hw j) 1 i hi1 hi
  have r2 := row_attn ev z3 rfl (by simp [z3]) (fun j => by rw [dq0]; norm_num) 2 i hi1 hi
  rw [dq0] at r0 r2
  rw [dq1] at r1
  -- the empty MLP leaves tiny bias terms
  have m0 := mlp_small ev (p.b2 0 0) (ev.hp.b2 0 0)
  have m1 := mlp_small ev (p.b2 0 1) (ev.hp.b2 0 1)
  have m2 := mlp_small ev (p.b2 0 2) (ev.hp.b2 0 2)
  -- the final state is within 1/20 of the ideal [tok i, tok (i-1), 1]
  have y0 := add_step ev ha r0 (add_zero _) (tk_abs w ev.hw i) m0
  have y1 := add_step ev hb r1 (zero_add _) (tk_abs w ev.hw (i - 1)) m1
  have y2 := add_step ev hc r2 (add_zero _) (by norm_num) m2
  have hCy := close3 y0 y1 y2 (tk_abs w ev.hw i) (tk_abs w ev.hw (i - 1)) (by norm_num)
  -- the read-out reads entry 1
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  obtain ⟨ho1, ho2⟩ := ardot3 ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 net.outW rfl
    (by simp [net]) _ _ (by simp) (by norm_num) (by norm_num) hCy p.oW ev.hp.oW
  have hq : ∀ x y : ℝ, dotQ net.outW [x, y, 1] = y := by
    intro x y
    simp [dotQ, net]
  rw [hq] at ho1
  have hob : |asw fl net.outB p.oB| ≤ 1 / 500 := by
    have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) net.outB ev.hp.oB
      (by simp [net])
    have h0 : ((net.outB : ℚ) : ℝ) = 0 := by simp [net]
    rwa [h0, sub_zero] at h
  have ht : ((target w i : ℕ) : ℝ) = ((tokAt w (i - 1) : ℕ) : ℝ) := rfl
  rw [ht]
  unfold ANet.out
  rw [run_vals fl ex p w i a b c hx]
  exact final_round ev ho1 ho2 hob

end Steps

theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη1 p hp w hw hn hnη hM i hi1 hi
  have ctx : Ctx u η M fl ex p w := ⟨hr, he, hu0, hu1, hη0, hη1, hp, hw, hn, hnη, hM⟩
  exact out_near ctx i hi1 hi

end Lane4.Case
-- ===== SOLUTION END =====
