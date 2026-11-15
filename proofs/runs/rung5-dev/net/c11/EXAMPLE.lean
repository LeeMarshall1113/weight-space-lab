/-
WORKED EXAMPLE on a task outside the four task families: output the previous token
(2 real tokens; the token before position 1 is BOS = 0), with SOFTMAX attention. It was
checked by the same checker and passed, including the two corollaries of Final.lean.
It shows the parts the checker joins: the lane's Spec.lean, a Solution.lean, and (not
shown) Final.lean. Only the part between the SOLUTION markers is what you write.

How this proof is organised (a pattern, not the only way):
  1. `init_eq`: the starting state at any position as an explicit list. Cases on the token.
     Embedding entries are stored weights `sw fl w d`; a written 0 is exactly 0 (`sw_zero`).
  2. `score_eq`, `val_eq`, `zrow_eq`: scores and values in closed form. Zero weights drop
     out exactly. Rounding a rounded value again is the identity only inside the range,
     so each closed form takes ONE hypothesis `hI : fl (fl x) = fl x` for its base
     product `x`; you get it from `Rnd.idem` and a bound `|x| ≤ M`. Simp then collapses
     the whole tower of `fl`s.
  3. `attn_eq`: the head's output row by row; rows of `V` that are zero give exactly 0
     (`soft_zeros`), the others stay as `savg ...`.
  4. `out_eq`: the output in closed form from the head's output.
  5. `net_ok`: range facts from `2^40 * n^2 ≤ M` (`range_lin`, `range_const`); bounds on
     the stored weights (`sw_near`); the score gap of at least `16 * |j - k|` between the
     winner and every other candidate (`Rnd.pos_gap`, `Rnd.gap`); `soft_near`; then a
     chain of absolute errors (`mul_near`, `Rnd.near`) closed by `linarith`.
This example has one head and no MLP; your task will need more than this.
-/

-- ===== Spec.lean (given) =====
namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

/-- Target at position `i`: the token one position earlier (BOS counts as 0). -/
def target (w : List ℕ) (i : ℕ) : ℕ := tokAt w (i - 1)

def Statement (N : TNet) : Prop :=
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Rnd u η M fl → ExpM u η ex →
  0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  ∀ p : Pert, p.Within (1 / 200) →
  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) →
  u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 → η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100 →
  2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M →
  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → |sout N fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4

end Lane4.Case

-- ===== Solution.lean (SOLUTION START) =====
namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

/-- State: [val, res, 1, fl i, fl n] (width 5). -/
def z5 : List ℚ := [0, 0, 0, 0, 0]

/-- Score of key j = (stored weight near 17) * position of j, strictly earlier keys only.
The previous position wins by a gap of at least 16 per unit of distance, which is what
`soft_near` needs. Value: write the key's `val` into slot `res`. -/
def hd : Head :=
  { A := [z5, z5, [0, 0, 0, 17, 0], z5, z5],
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

theorem init_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (j : ℕ) :
    net.init fl p w j = [ev fl p w j, 0] ++ pos fl j (w.length + 1) := by
  have h3 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 := by
    have := tok_le w hw j
    omega
  rcases h3 with h | h | h <;> simp [TNet.init, net, ev, swRow, h, sw_zero hr]

/-- The score in closed form. Zero weights drop out exactly. What is left is a tower
`fl (fl (... (S * qk)))`; the hypothesis `hI` (from `Rnd.idem`, which needs `|S * qk| ≤ M`)
collapses it. -/
theorem score_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (a b qi qk qn qn' : ℝ)
    (hI : fl (fl (sw fl 17 (dA 2 3) * qk)) = fl (sw fl 17 (dA 2 3) * qk)) :
    hd.score fl dA [a, 0, 1, qi, qn] [b, 0, 1, qk, qn'] = fl (sw fl 17 (dA 2 3) * qk) := by
  simp [Head.score, hd, z5, pdot, rmat, rdot, sw_zero hr, hr.zero, hI]

/-- The value of key `k` in closed form (row 1 of `V`). -/
theorem val_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ) (b qk qn : ℝ)
    (hI : fl (fl (sw fl 1 (dV 0) * b)) = fl (sw fl 1 (dV 0) * b)) :
    rdot fl [1, 0, 0, 0, 0] [b, 0, 1, qk, qn] dV 0 0 = fl (sw fl 1 (dV 0) * b) := by
  simp [rdot, sw_zero hr, hr.zero, hI]

/-- A zero row of `V` gives the value 0. -/
theorem zrow_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ) (a b c d e : ℝ) :
    rdot fl z5 [a, b, c, d, e] dV 0 0 = 0 := by
  simp [z5, rdot, sw_zero hr, hr.zero]

/-- The head's output: only slot `res` is written. -/
theorem attn_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (i : ℕ) :
    sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, savg fl ex (cand Mask.strict (w.length + 1) i)
              (hscore hd fl (p.A 0 0) (net.init fl p w) i)
              (fun j => rdot fl [1, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 1) 0 0),
         0, 0, 0] := by
  have hV : hd.V = [z5, [1, 0, 0, 0, 0], z5, z5, z5] := rfl
  have hm : hd.mask = Mask.strict := rfl
  have hz : ∀ d : ℕ → ℝ,
      savg fl ex (cand Mask.strict (w.length + 1) i)
        (hscore hd fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl z5 (net.init fl p w j) d 0 0) = 0 := by
    intro d
    apply soft_zeros hr
    intro k _
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact zrow_eq hr d _ _ _ _ _
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz]

/-- The output in closed form, given the head's output `[0, A, 0, 0, 0]`. `hA` says `A` is
unchanged by rounding (second part of `soft_near`); `hI` collapses the tower around the
read-out product. -/
theorem out_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (i : ℕ) (A : ℝ)
    (hattn : sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, A, 0, 0, 0])
    (hA : fl A = A)
    (hI : fl (fl (sw fl 1 (p.oW 1) * A)) = fl (sw fl 1 (p.oW 1) * A)) :
    sout net fl ex p w i = fl (sw fl 1 (p.oW 1) * A) := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  unfold sout srun
  rw [hb, ho, hc]
  simp only [srunFrom, sblock, blk, sheadsApply, hattn]
  simp only [init_eq hr p w hw]
  simp [z5, pos, rdot, radd, raffine, sw_zero hr, hr.zero, hA, hI]

set_option maxHeartbeats 1600000 in
theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη p hp w hw hn hnη hM i hi1 hi
  -- range facts: `M` is at least `2^40 * n^2`
  have hn1 : 1 ≤ w.length + 1 := by omega
  have hnR : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hn1
  have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
    have := range_lin hM hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have h18 : 18 * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  have h38 : 38 * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  have h40 : (40 : ℝ) ≤ M := range_const hM hn1 (by norm_num)
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by linarith
  -- the three stored weights that matter: S ≈ 17, T ≈ 1, O ≈ 1
  have c17 : ((17 : ℚ) : ℝ) = 17 := by norm_num
  have c1 : ((1 : ℚ) : ℝ) = 1 := by norm_num
  have hS := sw_near hr hu0 17 (hp.A 0 0 2 3) (by norm_num)
    (by rw [c17, abs_of_nonneg (by norm_num)]; linarith) hε
  rw [c17, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 17)] at hS
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  have hT := sw_near hr hu0 1 (hp.V 0 0 1 0) (by norm_num)
    (by rw [c1, abs_of_nonneg (by norm_num)]; linarith) hε
  rw [c1, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)] at hT
  have hO := sw_near hr hu0 1 (hp.oW 1) (by norm_num)
    (by rw [c1, abs_of_nonneg (by norm_num)]; linarith) hε
  rw [c1, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)] at hO
  -- stored embedding values: within 2/199 + η of the token
  have hE : ∀ k : ℕ, |ev fl p w k - ((tokAt w k : ℕ) : ℝ)| ≤ 2 / 199 + η := by
    intro k
    have ht : tokAt w k ≤ 2 := tok_le w hw k
    have htr : ((tokAt w k : ℕ) : ℝ) ≤ 2 := by exact_mod_cast ht
    have ht0 : (0 : ℝ) ≤ ((tokAt w k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hc : (((tokAt w k : ℕ) : ℚ) : ℝ) = ((tokAt w k : ℕ) : ℝ) := by norm_num
    have h := sw_near hr hu0 ((tokAt w k : ℕ) : ℚ) (hp.E (tokAt w k) 0) (by norm_num)
      (by rw [hc, abs_of_nonneg ht0]; linarith) hε
    rw [hc, abs_of_nonneg ht0] at h
    unfold ev
    linarith
  -- scores: s k = fl (S * fl k), with |S * fl k| ≤ 18 n
  have hPb : ∀ k : ℕ, k ≤ w.length + 1 →
      |sw fl 17 (p.A 0 0 2 3) * fl (k : ℝ)| ≤ 18 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    obtain ⟨hk0, hk1⟩ := hr.pos_le hu0 hη hk hn hnM
    have hS0 : 0 ≤ sw fl 17 (p.A 0 0 2 3) := by linarith
    rw [abs_of_nonneg (mul_nonneg hS0 hk0)]
    have := mul_le_mul (show sw fl 17 (p.A 0 0 2 3) ≤ 171 / 10 by linarith) hk1 hk0 (by norm_num)
    linarith
  have hsk : ∀ k : ℕ, k ≤ w.length + 1 →
      hscore hd fl (p.A 0 0) (net.init fl p w) i k = fl (sw fl 17 (p.A 0 0 2 3) * fl (k : ℝ)) := by
    intro k hk
    simp only [hscore, init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact score_eq hr _ _ _ _ _ _ _ (hr.idem _ (le_trans (hPb k hk) h18))
  -- values: f k = fl (T * ev k), with |T * ev k| ≤ 3
  have hTEb : ∀ k : ℕ, |sw fl 1 (p.V 0 0 1 0) * ev fl p w k| ≤ 3 := by
    intro k
    have ht : tokAt w k ≤ 2 := tok_le w hw k
    have htr : ((tokAt w k : ℕ) : ℝ) ≤ 2 := by exact_mod_cast ht
    have ht0 : (0 : ℝ) ≤ ((tokAt w k : ℕ) : ℝ) := Nat.cast_nonneg _
    obtain ⟨hT1, hT2⟩ := abs_le.mp hT
    obtain ⟨hE1, hE2⟩ := abs_le.mp (hE k)
    rw [abs_mul]
    have h1 : |sw fl 1 (p.V 0 0 1 0)| ≤ 11 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |ev fl p w k| ≤ 21 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
    have := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    linarith
  have hfk : ∀ k : ℕ, rdot fl [1, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 1) 0 0
      = fl (sw fl 1 (p.V 0 0 1 0) * ev fl p w k) := by
    intro k
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact val_eq hr _ _ _ _ (hr.idem _ (le_trans (hTEb k) (by linarith)))
  -- soft_near: the head returns the value of the previous position
  have hj : i - 1 ∈ cand Mask.strict (w.length + 1) i := by
    rw [Lane4.Seq.mem_cand_strict]; omega
  have hlen : (cand Mask.strict (w.length + 1) i).length ≤ w.length + 1 := by
    simp [cand]; omega
  have hgap : ∀ k ∈ cand Mask.strict (w.length + 1) i, k ≠ i - 1 →
      hscore hd fl (p.A 0 0) (net.init fl p w) i k
        ≤ hscore hd fl (p.A 0 0) (net.init fl p w) i (i - 1) - 16 * (ndist (i - 1) k : ℝ) := by
    intro k hk hne
    rw [Lane4.Seq.mem_cand_strict] at hk
    have hkj : k < i - 1 := by omega
    rw [hsk k (by omega), hsk (i - 1) (by omega), ndist_cast]
    have hg := hr.pos_gap hu0 hη (le_of_lt hkj) (show i - 1 ≤ w.length + 1 by omega) hn hnM
    have hgp := hr.gap hu0 (hPb k (by omega)) (hPb (i - 1) (by omega)) h18
    have hd1 : ((k : ℝ)) + 1 ≤ ((i - 1 : ℕ) : ℝ) := by exact_mod_cast hkj
    rw [abs_of_nonneg (by linarith)]
    have hD0 : 0 ≤ fl ((i - 1 : ℕ) : ℝ) - fl (k : ℝ) := by linarith
    have hSD := mul_le_mul_of_nonneg_right (show (169 : ℝ) / 10 ≤ sw fl 17 (p.A 0 0 2 3) by linarith) hD0
    have hun : u * (18 * ((w.length + 1 : ℕ) : ℝ)) = 18 * (u * ((w.length + 1 : ℕ) : ℝ)) := by ring
    linarith [hgp, hSD, hg, hd1, hn, hηs, hηs', hun]
  have hSb : ∀ k ∈ cand Mask.strict (w.length + 1) i,
      |hscore hd fl (p.A 0 0) (net.init fl p w) i k| ≤ 18 * ((w.length + 1 : ℕ) : ℝ) + 1 := by
    intro k hk
    rw [Lane4.Seq.mem_cand_strict] at hk
    rw [hsk k (by omega)]
    have := hr.bound hu0 (hPb k (by omega)) h18
    have hun : u * (18 * ((w.length + 1 : ℕ) : ℝ)) = 18 * (u * ((w.length + 1 : ℕ) : ℝ)) := by ring
    linarith
  have hfB : ∀ k ∈ cand Mask.strict (w.length + 1) i,
      |(fun j => rdot fl [1, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 1) 0 0) k| ≤ 4 := by
    intro k _
    show |rdot fl [1, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 1) 0 0| ≤ 4
    rw [hfk k]
    have := hr.bound hu0 (hTEb k) (by linarith)
    linarith
  obtain ⟨hA1, hA2⟩ := soft_near hr he hu0 hu1 hη0 hη (Lane4.Seq.cand_nodup _ _ _) hlen hn hnη
    hj hgap hSb (by linarith) hfB (by linarith)
  -- the output
  have hat := attn_eq (ex := ex) hr p w hw i
  have hAb : |savg fl ex (cand Mask.strict (w.length + 1) i)
      (hscore hd fl (p.A 0 0) (net.init fl p w) i)
      (fun j => rdot fl [1, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 1) 0 0)| ≤ 5 := by
    have h1 := hfB (i - 1) hj
    have h2 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 100 := by norm_num
    have h3 := abs_sub_abs_le_abs_sub
      (savg fl ex (cand Mask.strict (w.length + 1) i)
        (hscore hd fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl [1, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 1) 0 0))
      ((fun j => rdot fl [1, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 1) 0 0) (i - 1))
    linarith
  have hOAb : |sw fl 1 (p.oW 1) * savg fl ex (cand Mask.strict (w.length + 1) i)
      (hscore hd fl (p.A 0 0) (net.init fl p w) i)
      (fun j => rdot fl [1, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 1) 0 0)| ≤ 6 := by
    obtain ⟨hO1, hO2⟩ := abs_le.mp hO
    rw [abs_mul]
    have h1 : |sw fl 1 (p.oW 1)| ≤ 11 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
    have := mul_le_mul h1 hAb (abs_nonneg _) (by norm_num)
    linarith
  rw [out_eq hr p w hw i _ hat hA2 (hr.idem _ (le_trans hOAb (by linarith)))]
  -- error chain: A ≈ f (i-1) = fl (T * ev (i-1)) ≈ T * ev (i-1) ≈ token; then O * A; then fl
  unfold target
  have ht : tokAt w (i - 1) ≤ 2 := tok_le w hw (i - 1)
  have htr : ((tokAt w (i - 1) : ℕ) : ℝ) ≤ 2 := by exact_mod_cast ht
  have ht0 : (0 : ℝ) ≤ ((tokAt w (i - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hta : |((tokAt w (i - 1) : ℕ) : ℝ)| ≤ 2 := by rw [abs_of_nonneg ht0]; exact htr
  have ha : (1 : ℝ) / 199 * 1 + η ≤ 1 / 190 := by linarith
  have hb : (2 : ℝ) / 199 + η ≤ 1 / 90 := by linarith
  have hb0 : (0 : ℝ) ≤ 2 / 199 + η := by linarith
  have m1 := mul_le_mul ha hta (abs_nonneg _) (by norm_num)
  have m2 := mul_le_mul ha hb hb0 (by norm_num)
  have e1 := mul_near hT (hE (i - 1))
  rw [one_mul, abs_one] at e1
  have e1' : |sw fl 1 (p.V 0 0 1 0) * ev fl p w (i - 1) - ((tokAt w (i - 1) : ℕ) : ℝ)|
      ≤ 1 / 40 := by linarith
  have e2 := hr.near hu0 e1' (hTEb (i - 1)) (by linarith)
  have hA1' : |savg fl ex (cand Mask.strict (w.length + 1) i)
      (hscore hd fl (p.A 0 0) (net.init fl p w) i)
      (fun j => rdot fl [1, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 1) 0 0)
      - fl (sw fl 1 (p.V 0 0 1 0) * ev fl p w (i - 1))| ≤ 4 / 100 + 1 / 2 ^ 90 := by
    have := hA1
    simp only [hfk (i - 1)] at this
    exact this
  have e3 := abs_sub_le
    (savg fl ex (cand Mask.strict (w.length + 1) i)
      (hscore hd fl (p.A 0 0) (net.init fl p w) i)
      (fun j => rdot fl [1, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 1) 0 0))
    (fl (sw fl 1 (p.V 0 0 1 0) * ev fl p w (i - 1)))
    ((tokAt w (i - 1) : ℕ) : ℝ)
  have h2 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 100000 := by norm_num
  have hX : |savg fl ex (cand Mask.strict (w.length + 1) i)
      (hscore hd fl (p.A 0 0) (net.init fl p w) i)
      (fun j => rdot fl [1, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 1) 0 0)
      - ((tokAt w (i - 1) : ℕ) : ℝ)| ≤ 7 / 100 := by linarith
  have e4 := mul_near hO hX
  rw [one_mul, abs_one] at e4
  have e5 := hr.near hu0 e4 hOAb (by linarith)
  linarith

end Lane4.Case
-- ===== SOLUTION END =====
