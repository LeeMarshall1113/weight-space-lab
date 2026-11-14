/-
WORKED EXAMPLE on a task outside the four task families: output the previous token
(2 real tokens; the token before position 1 is BOS = 0). It was checked by the same
checker and passed. It shows the parts the checker joins: the lane's Spec.lean, a
Solution.lean, and (not shown) Final.lean. Only the part between the SOLUTION markers is
what you write.

How this proof is organised (a pattern, not the only way):
  1. `init_eq`: the starting state at any position as an explicit list. Cases on the token.
     Embedding entries are stored weights `sw fl w d`; a written 0 is exactly 0 (`sw_zero`).
  2. `score_eq`: the head's score in closed form. Zero weights drop out exactly, so only
     the products with non-zero written weights are left.
  3. `sel_eq`: the head selects exactly one position, for EVERY allowed perturbation and
     rounding (`Head.sel_unique`, `Rounding.lt_of_gap`, `Rounding.pos_gap`, `Rounding.pos_le`).
  4. `out_eq`: the output in closed form given the selected set (`ravg_singleton`).
  5. `net_ok`: bound the remaining rounded products with relative-error lemmas
     (`sw_rel`, `rel_mul`, `rel_fl`) and finish with linear arithmetic.
This example has one head and no MLP; your task will need more than this.
-/

-- ===== Spec.lean (given) =====
namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

/-- Target at position `i`: the token one position earlier (BOS counts as 0). -/
def target (w : List ℕ) (i : ℕ) : ℕ := tokAt w (i - 1)

def Statement (N : TNet) : Prop :=
  ∀ (u : ℝ) (fl : ℝ → ℝ), Rounding u fl → 0 ≤ u → u ≤ 1 / 16777216 →
  ∀ p : Pert, p.Within (1 / 200) →
  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) → u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 →
  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → |N.out fl p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4

end Lane4.Case

-- ===== Solution.lean (SOLUTION START) =====
namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

/-- State: [val, res, 1, fl i, fl n] (width 5). -/
def z5 : List ℚ := [0, 0, 0, 0, 0]

/-- Score of key j = (stored weight near 1) * position of j, strictly earlier keys only:
the winner is the previous position. Value: write the key's `val` into slot `res`. -/
def hd : Head :=
  { A := [z5, z5, [0, 0, 0, 1, 0], z5, z5],
    V := [z5, [1, 0, 0, 0, 0], z5, z5, z5],
    mask := Mask.strict }

def blk : Block :=
  { heads := [hd], W1 := [], b1 := [], W2 := [[], [], [], [], []], b2 := z5 }

def net : TNet :=
  { embed := [[0, 0], [1, 0], [2, 0]],
    blocks := [blk],
    outW := [0, 1, 0, 0, 0],
    outB := 0 }

/-- The stored `val` entry at position `j`. -/
noncomputable def ev (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl ((tokAt w j : ℕ) : ℚ) (p.E (tokAt w j) 0)

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (j : ℕ) : tokAt w j ≤ 2 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (j : ℕ) :
    net.init fl p w j = [ev fl p w j, 0] ++ pos fl j (w.length + 1) := by
  have h3 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 := by
    have := tok_le w hw j
    omega
  rcases h3 with h | h | h <;> simp [TNet.init, net, ev, swRow, h, sw_zero hr]

/-- The score in closed form: every zero weight stays exactly zero, so one product is left. -/
theorem score_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (a b qi qk qn qn' : ℝ) :
    hd.score fl dA [a, 0, 1, qi, qn] [b, 0, 1, qk, qn'] = fl (sw fl 1 (dA 2 3) * qk) := by
  simp [Head.score, hd, z5, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem]

/-- The head selects exactly the previous position, for every allowed weight setting and
rounding. The gap between neighbouring scores is about 1; the rounding error is at most
`2 * u * B` with `B` a bound on the scores, and `u * n ≤ 1/256` makes that small. -/
theorem sel_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = [i - 1] := by
  apply Head.sel_unique
  · rw [show hd.mask = Mask.strict from rfl, Lane4.Seq.mem_cand_strict]
    omega
  · intro k hk hne
    rw [show hd.mask = Mask.strict from rfl, Lane4.Seq.mem_cand_strict] at hk
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    rw [score_eq hr, score_eq hr]
    have hS := sw_rel hr hu0 1 (hp.A 0 0 2 3) (ε := 3 / 250) (by linarith)
    simp only [Rat.cast_one, abs_one, mul_one] at hS
    obtain ⟨hS1, hS2⟩ := abs_le.mp hS
    have hS0 : 0 ≤ sw fl 1 (p.A 0 0 2 3) := by linarith
    have hg := hr.pos_gap hu0 (show k < i - 1 by omega) (show i - 1 ≤ w.length + 1 by omega) hn
    have hk' := hr.pos_le hu0 (show k ≤ w.length + 1 by omega) hn
    have hj' := hr.pos_le hu0 (show i - 1 ≤ w.length + 1 by omega) hn
    apply hr.lt_of_gap hu0 (B := 2 * (((w.length + 1 : ℕ) : ℝ) + 1 / 256))
    · rw [abs_of_nonneg (mul_nonneg hS0 hk'.1)]
      exact mul_le_mul (by linarith) hk'.2 hk'.1 (by norm_num)
    · rw [abs_of_nonneg (mul_nonneg hS0 hj'.1)]
      exact mul_le_mul (by linarith) hj'.2 hj'.1 (by norm_num)
    · have h1 := mul_le_mul_of_nonneg_left hg hS0
      nlinarith [h1, hn, hu0, hu1, hS1]

/-- The output in closed form, given the selected set. -/
theorem out_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (i : ℕ)
    (hsel : hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = [i - 1]) :
    net.out fl p w i
      = fl (sw fl 1 (p.oW 1) * fl (sw fl 1 (p.V 0 0 1 0) * ev fl p w (i - 1))) := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  have hV : hd.V = [z5, [1, 0, 0, 0, 0], z5, z5, z5] := rfl
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [runFrom, Block.apply, blk, headsApply, Head.attn, hsel, hV, attnRows,
    ravg_singleton hr]
  simp only [init_eq hr p w hw]
  simp [ev, z5, pos, rdot, radd, raffine, sw_zero hr, hr.zero, hr.idem, hr.one, fl_sw hr]

theorem net_ok : Statement net := by
  intro u fl hr hu0 hu1 p hp w hw hn i hi1 hi
  have hsel := sel_eq hr hu0 hu1 p hp w hw hn i hi1 hi
  rw [out_eq hr p w hw i hsel]
  unfold target ev
  have ht : tokAt w (i - 1) ≤ 2 := tok_le w hw (i - 1)
  generalize tokAt w (i - 1) = t at ht ⊢
  -- every stored weight is within 3/250 (relative) of the written one
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 3 / 250 := by linarith
  have hE := sw_rel hr hu0 (t : ℚ) (hp.E t 0) hε
  have hT := sw_rel hr hu0 1 (hp.V 0 0 1 0) hε
  have hO := sw_rel hr hu0 1 (hp.oW 1) hε
  -- two rounded products
  have h1 := rel_fl hr hu0 (rel_mul hT hE (c := 1 / 40) (by norm_num)) (c := 13 / 500)
    (by linarith)
  have h2 := rel_fl hr hu0 (rel_mul hO h1 (c := 1 / 25) (by norm_num)) (c := 21 / 500)
    (by linarith)
  simp only [Rat.cast_one, Rat.cast_natCast, one_mul] at h2
  have htr : |(t : ℝ)| ≤ 2 := by
    rw [abs_of_nonneg (Nat.cast_nonneg t)]
    exact_mod_cast ht
  have := mul_le_mul_of_nonneg_left htr (show (0 : ℝ) ≤ 21 / 500 by norm_num)
  linarith

end Lane4.Case
-- ===== SOLUTION END =====
