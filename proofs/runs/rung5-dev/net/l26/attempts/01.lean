namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.style.longLine false

def z6 : List ℚ := [0, 0, 0, 0, 0, 0]

def hd : Head :=
  { A := [z6, z6, z6, [0, 0, 0, 0, 20, 0], z6, [0, -100, 0, 0, 0, 0]],
    V := [z6, z6, [1, 0, 0, 0, 0, 0], z6, z6, z6],
    mask := Mask.causal }

def blk : Block :=
  { heads := [hd], W1 := [], b1 := [], W2 := [[], [], [], [], [], []], b2 := z6 }

def net : TNet :=
  { embed := [[0, 1, 0], [2, 0, 0], [3, 0, 0], [0, 1, 0], [1, 0, 0]],
    blocks := [blk],
    outW := [0, 0, 1, 0, 0, 0],
    outB := 0 }

def vq (t : ℕ) : ℚ := ((Lane4.Case.val t : ℕ) : ℚ)
def uq (t : ℕ) : ℚ := if Lane4.Case.val t = 0 then 1 else 0

noncomputable def ev (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (vq (tokAt w j)) (p.E (tokAt w j) 0)

noncomputable def eu (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (uq (tokAt w j)) (p.E (tokAt w j) 1)

theorem val_le (t : ℕ) : Lane4.Case.val t ≤ 3 := by
  unfold Lane4.Case.val
  split_ifs <;> omega

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) : tokAt w j ≤ 4 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) :
    net.init fl p w j = [ev fl p w j, eu fl p w j, 0] ++ pos fl j (w.length + 1) := by
  have h3 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 := by
    have := tok_le w hw j
    omega
  rcases h3 with h | h | h | h | h <;>
    simp [TNet.init, net, ev, eu, vq, uq, Lane4.Case.val, swRow, h, sw_zero hr]

theorem score_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (a b c qi qn a' b' c' qk qn' : ℝ)
    (hI1 : fl (fl (sw fl 20 (dA 3 4) * qk)) = fl (sw fl 20 (dA 3 4) * qk))
    (hI2 : fl (fl (sw fl (-100) (dA 5 1) * b')) = fl (sw fl (-100) (dA 5 1) * b')) :
    hd.score fl dA [a, b, c, 1, qi, qn] [a', b', c', 1, qk, qn'] =
      fl (fl (sw fl 20 (dA 3 4) * qk) + fl (qn * fl (sw fl (-100) (dA 5 1) * b'))) := by
  simp [Head.score, hd, z6, pdot, rmat, rdot, sw_zero hr, hr.zero, hI1, hI2]

theorem val_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ) (b0 b1 b2 qk qn : ℝ)
    (hI : fl (fl (sw fl 1 (dV 0) * b0)) = fl (sw fl 1 (dV 0) * b0)) :
    rdot fl [1, 0, 0, 0, 0, 0] [b0, b1, b2, 1, qk, qn] dV 0 0 = fl (sw fl 1 (dV 0) * b0) := by
  simp [rdot, sw_zero hr, hr.zero, hI]

theorem zrow_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ) (a b c d e g : ℝ) :
    rdot fl z6 [a, b, c, d, e, g] dV 0 0 = 0 := by
  simp [z6, rdot, sw_zero hr, hr.zero]

theorem attn_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) (s f : ℕ → ℝ)
    (hs : s = hscore hd fl (p.A 0 0) (net.init fl p w) i)
    (hf : f = fun j => rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 2) 0 0) :
    sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, savg fl ex (cand Mask.causal (w.length + 1) i) s f, 0, 0, 0] := by
  subst hs
  subst hf
  have hV : hd.V = [z6, z6, [1, 0, 0, 0, 0, 0], z6, z6, z6] := rfl
  have hm : hd.mask = Mask.causal := rfl
  have hz : ∀ d : ℕ → ℝ,
      savg fl ex (cand Mask.causal (w.length + 1) i)
        (hscore hd fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl z6 (net.init fl p w j) d 0 0) = 0 := by
    intro d
    apply soft_zeros hr
    intro k _
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact zrow_eq hr d _ _ _ _ _ _
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz]

theorem out_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) (A : ℝ)
    (hattn : sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, A, 0, 0, 0])
    (hA : fl A = A)
    (hI : fl (fl (sw fl 1 (p.oW 2) * A)) = fl (sw fl 1 (p.oW 2) * A)) :
    sout net fl ex p w i = fl (sw fl 1 (p.oW 2) * A) := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 0, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  unfold sout srun
  rw [hb, ho, hc]
  simp only [srunFrom, sblock, blk, sheadsApply, hattn]
  simp only [init_eq hr p w hw]
  simp [z6, pos, rdot, radd, raffine, sw_zero hr, hr.zero, hA, hI]

/-! ### Real-number lemmas about the scores -/

theorem sx_parts {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) {N S T eu fk fn : ℝ} (hN1 : 1 ≤ N)
    (hun : u * N ≤ 1 / 256) (hMs : 258 * N ≤ M) (hS1 : 198 / 10 ≤ S) (hS2 : S ≤ 202 / 10)
    (hT1 : -1006 / 10 ≤ T) (hT2 : T ≤ -994 / 10) (he0 : 0 ≤ eu) (he1 : eu ≤ 101 / 100)
    (hk0 : 0 ≤ fk) (hk1 : fk ≤ N + 1 / 100) (hn0 : 0 ≤ fn) (hn1 : fn ≤ N + 1 / 100) :
    |fl (S * fk)| ≤ 22 * N ∧ |fl (fn * fl (T * eu))| ≤ 106 * N ∧
    fl (fn * fl (T * eu)) ≤ 0 ∧ |fl (T * eu)| ≤ 103 ∧ fl (T * eu) ≤ 0 ∧
    |fn * fl (T * eu)| ≤ 105 * N := by
  have h4 := eta_tiny hη
  have h5 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have hSk : |S * fk| ≤ 21 * N := by
    rw [abs_of_nonneg (mul_nonneg (by linarith) hk0)]
    have := mul_le_mul hS2 hk1 hk0 (by norm_num)
    linarith
  have hTe : |T * eu| ≤ 102 := by
    rw [abs_mul]
    have h1 : |T| ≤ 1006 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |eu| ≤ 101 / 100 := abs_le.mpr ⟨by linarith, by linarith⟩
    have := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    linarith
  have hTen : T * eu ≤ 0 := by
    have := mul_nonneg (show (0 : ℝ) ≤ -T by linarith) he0
    linarith
  have hTeabs := abs_le.mp hTe
  have hQ0 : fl (T * eu) ≤ 0 := hr.nonpos hTen (by linarith [hTeabs.1])
  have hQb : |fl (T * eu)| ≤ 103 := by
    have := hr.bound hu0 hTe (show (102 : ℝ) ≤ M by linarith)
    linarith
  have hnQ : |fn * fl (T * eu)| ≤ 105 * N := by
    rw [abs_mul, abs_of_nonneg hn0]
    have := mul_le_mul hn1 hQb (abs_nonneg _) (by linarith)
    linarith
  have hRn : fn * fl (T * eu) ≤ 0 := by
    have := mul_nonneg hn0 (show (0 : ℝ) ≤ -fl (T * eu) by linarith)
    linarith
  have hRnabs := abs_le.mp hnQ
  have hR0 : fl (fn * fl (T * eu)) ≤ 0 := hr.nonpos hRn (by linarith [hRnabs.1])
  have hRb : |fl (fn * fl (T * eu))| ≤ 106 * N := by
    have := hr.bound hu0 hnQ (show 105 * N ≤ M by linarith)
    have hun' : u * (105 * N) = 105 * (u * N) := by ring
    linarith
  have hPb : |fl (S * fk)| ≤ 22 * N := by
    have := hr.bound hu0 hSk (show 21 * N ≤ M by linarith)
    have hun' : u * (21 * N) = 21 * (u * N) := by ring
    linarith
  exact ⟨hPb, hRb, hR0, hQb, hQ0, hnQ⟩

theorem sx_le {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) {N S T eu fk fn : ℝ} (hN1 : 1 ≤ N)
    (hun : u * N ≤ 1 / 256) (hMs : 258 * N ≤ M) (hS1 : 198 / 10 ≤ S) (hS2 : S ≤ 202 / 10)
    (hT1 : -1006 / 10 ≤ T) (hT2 : T ≤ -994 / 10) (he0 : 0 ≤ eu) (he1 : eu ≤ 101 / 100)
    (hk0 : 0 ≤ fk) (hk1 : fk ≤ N + 1 / 100) (hn0 : 0 ≤ fn) (hn1 : fn ≤ N + 1 / 100) :
    fl (fl (S * fk) + fl (fn * fl (T * eu))) ≤ fl (S * fk) := by
  obtain ⟨hP, hR, hR0, -, -, -⟩ := sx_parts hr hu0 hu1 hη hN1 hun hMs hS1 hS2 hT1 hT2 he0 he1
    hk0 hk1 hn0 hn1
  have hSk : |S * fk| ≤ 21 * N := by
    rw [abs_of_nonneg (mul_nonneg (by linarith) hk0)]
    have := mul_le_mul hS2 hk1 hk0 (by norm_num)
    linarith
  have hidem : fl (fl (S * fk)) = fl (S * fk) := hr.idem _ (le_trans hSk (by linarith))
  have h1 : |fl (S * fk) + fl (fn * fl (T * eu))| ≤ M := by
    have := abs_add_le (fl (S * fk)) (fl (fn * fl (T * eu)))
    linarith
  have h2 : |fl (S * fk)| ≤ M := by linarith
  have := hr.mono _ _ h1 h2
    (show fl (S * fk) + fl (fn * fl (T * eu)) ≤ fl (S * fk) by linarith)
  rw [hidem] at this
  exact this

theorem sx_abs {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) {N S T eu fk fn : ℝ} (hN1 : 1 ≤ N)
    (hun : u * N ≤ 1 / 256) (hMs : 258 * N ≤ M) (hS1 : 198 / 10 ≤ S) (hS2 : S ≤ 202 / 10)
    (hT1 : -1006 / 10 ≤ T) (hT2 : T ≤ -994 / 10) (he0 : 0 ≤ eu) (he1 : eu ≤ 101 / 100)
    (hk0 : 0 ≤ fk) (hk1 : fk ≤ N + 1 / 100) (hn0 : 0 ≤ fn) (hn1 : fn ≤ N + 1 / 100) :
    |fl (fl (S * fk) + fl (fn * fl (T * eu)))| ≤ 129 * N := by
  have h4 := eta_tiny hη
  have h5 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  obtain ⟨hP, hR, hR0, -, -, -⟩ := sx_parts hr hu0 hu1 hη hN1 hun hMs hS1 hS2 hT1 hT2 he0 he1
    hk0 hk1 hn0 hn1
  have h1 : |fl (S * fk) + fl (fn * fl (T * eu))| ≤ 128 * N := by
    have := abs_add_le (fl (S * fk)) (fl (fn * fl (T * eu)))
    linarith
  have := hr.bound hu0 h1 (show 128 * N ≤ M by linarith)
  have hun' : u * (128 * N) = 128 * (u * N) := by ring
  linarith

theorem gap_early {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hη : η ≤ 1 / 2 ^ 149) {N S fk fj d : ℝ} (hN1 : 1 ≤ N) (hun : u * N ≤ 1 / 256)
    (hM : 21 * N ≤ M) (hS1 : 198 / 10 ≤ S) (hS2 : S ≤ 202 / 10)
    (hk0 : 0 ≤ fk) (hj0 : 0 ≤ fj) (hk1 : fk ≤ N + 1 / 100) (hj1 : fj ≤ N + 1 / 100)
    (hd1 : 1 ≤ d) (hdd : fk + d - 1 / 100 ≤ fj) :
    fl (S * fk) ≤ fl (S * fj) - 16 * d := by
  have hak : |S * fk| ≤ 21 * N := by
    rw [abs_of_nonneg (mul_nonneg (by linarith) hk0)]
    have := mul_le_mul hS2 hk1 hk0 (by norm_num)
    linarith
  have hbj : |S * fj| ≤ 21 * N := by
    rw [abs_of_nonneg (mul_nonneg (by linarith) hj0)]
    have := mul_le_mul hS2 hj1 hj0 (by norm_num)
    linarith
  have hgp := hr.gap hu0 hak hbj hM
  have hD0 : 0 ≤ fj - fk := by linarith
  have hSD := mul_le_mul_of_nonneg_right hS1 hD0
  have hun' : u * (21 * N) = 21 * (u * N) := by ring
  have h4 := eta_tiny hη
  have h5 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

theorem gap_late {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) {N S T eu fk fn : ℝ} (hN1 : 1 ≤ N)
    (hun : u * N ≤ 1 / 256) (hMs : 258 * N ≤ M) (hS1 : 198 / 10 ≤ S) (hS2 : S ≤ 202 / 10)
    (hT1 : -1006 / 10 ≤ T) (hT2 : T ≤ -994 / 10) (he0 : 0 ≤ eu) (he1 : eu ≤ 101 / 100)
    (hk0 : 0 ≤ fk) (hk1 : fk ≤ N + 1 / 100) (hn0 : 0 ≤ fn) (hn1 : fn ≤ N + 1 / 100)
    {kk jj fj : ℝ} (hkk : kk ≤ N) (hj0 : 0 ≤ jj) (hfk : fk ≤ kk + 1 / 200)
    (hfj : jj - 1 / 200 ≤ fj) (hfj0 : 0 ≤ fj) (hfj1 : fj ≤ N + 1 / 100)
    (hn2 : N - 1 / 200 ≤ fn) (he2 : 99 / 100 ≤ eu) :
    fl (fl (S * fk) + fl (fn * fl (T * eu))) ≤ fl (S * fj) - 16 * (kk - jj) := by
  have h4 := eta_tiny hη
  have h5 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  obtain ⟨hP, hR, hR0, hQb, hQ0, hnQ⟩ := sx_parts hr hu0 hu1 hη hN1 hun hMs hS1 hS2 hT1 hT2
    he0 he1 hk0 hk1 hn0 hn1
  have hSk : |S * fk| ≤ 21 * N := by
    rw [abs_of_nonneg (mul_nonneg (by linarith) hk0)]
    have := mul_le_mul hS2 hk1 hk0 (by norm_num)
    linarith
  have hSj : |S * fj| ≤ 21 * N := by
    rw [abs_of_nonneg (mul_nonneg (by linarith) hfj0)]
    have := mul_le_mul hS2 hfj1 hfj0 (by norm_num)
    linarith
  have hTe : |T * eu| ≤ 102 := by
    rw [abs_mul]
    have h1 : |T| ≤ 1006 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |eu| ≤ 101 / 100 := abs_le.mpr ⟨by linarith, by linarith⟩
    have := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    linarith
  have hTeq : T * eu ≤ -984 / 10 := by
    have := mul_nonneg (show (0 : ℝ) ≤ -T by linarith) (show (0 : ℝ) ≤ eu - 99 / 100 by linarith)
    linarith
  have hQup : fl (T * eu) ≤ -98 := by
    have := hr.upper hu0 hTe (show (102 : ℝ) ≤ M by linarith)
    linarith
  have hnQle : fn * fl (T * eu) ≤ -98 * fn := by
    have := mul_nonneg hn0 (show (0 : ℝ) ≤ -(fl (T * eu) + 98) by linarith)
    linarith
  have hRup := hr.upper hu0 hnQ (show 105 * N ≤ M by linarith)
  have hPup := hr.upper hu0 hSk (show 21 * N ≤ M by linarith)
  have hsum : |fl (S * fk) + fl (fn * fl (T * eu))| ≤ 128 * N := by
    have := abs_add_le (fl (S * fk)) (fl (fn * fl (T * eu)))
    linarith
  have hsup := hr.upper hu0 hsum (show 128 * N ≤ M by linarith)
  have hPj := hr.lower hu0 hSj (show 21 * N ≤ M by linarith)
  have hSfk : S * fk ≤ 202 / 10 * fk := mul_le_mul_of_nonneg_right hS2 hk0
  have hSfj : 198 / 10 * fj ≤ S * fj := mul_le_mul_of_nonneg_right hS1 hfj0
  have u1 : u * (21 * N) = 21 * (u * N) := by ring
  have u2 : u * (105 * N) = 105 * (u * N) := by ring
  have u3 : u * (128 * N) = 128 * (u * N) := by ring
  linarith

/-! ### The combinatorial part: the last marked token -/

theorem last_marked (w : List ℕ) : ∀ i : ℕ, i ≤ w.length →
    ((∀ k, 1 ≤ k → k ≤ i → Lane4.Case.val (tokAt w k) = 0) ∧ lastv (w.take i) = 0) ∨
    (∃ j, 1 ≤ j ∧ j ≤ i ∧ Lane4.Case.val (tokAt w j) ≠ 0 ∧
      (∀ k, j < k → k ≤ i → Lane4.Case.val (tokAt w k) = 0) ∧
      lastv (w.take i) = Lane4.Case.val (tokAt w j)) := by
  intro i
  induction i with
  | zero =>
    intro _
    left
    refine ⟨fun k h1 h2 => by omega, ?_⟩
    simp [lastv]
  | succ i ih =>
    intro hi
    have hlt : i < w.length := by omega
    have hsnoc : w.take (i + 1) = w.take i ++ [tokAt w (i + 1)] := by
      rw [Lane4.Seq.tokAt_succ w i hlt]
      first
        | exact List.take_succ_eq_append_getElem hlt
        | simp [List.take_succ, hlt]
    have hl : lastv (w.take (i + 1)) =
        if Lane4.Case.val (tokAt w (i + 1)) = 0 then lastv (w.take i)
        else Lane4.Case.val (tokAt w (i + 1)) := by
      rw [hsnoc]
      simp [lastv, List.foldl_append]
    by_cases hv : Lane4.Case.val (tokAt w (i + 1)) = 0
    · rw [if_pos hv] at hl
      rcases ih (by omega) with ⟨h1, h2⟩ | ⟨j, hj1, hji, hjm, hafter, hlast⟩
      · left
        refine ⟨fun k hk1 hk2 => ?_, by rw [hl, h2]⟩
        by_cases hk : k = i + 1
        · subst hk
          exact hv
        · exact h1 k hk1 (by omega)
      · right
        refine ⟨j, hj1, by omega, hjm, fun k hjk hk2 => ?_, by rw [hl, hlast]⟩
        by_cases hk : k = i + 1
        · subst hk
          exact hv
        · exact hafter k hjk (by omega)
    · rw [if_neg hv] at hl
      right
      exact ⟨i + 1, by omega, le_refl _, hv, fun k hk1 hk2 => by omega, hl⟩

/-! ### The main theorem -/

set_option maxHeartbeats 4000000 in
theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη p hp w hw hn hnη hM i hi1 hi
  have hn1 : 1 ≤ w.length + 1 := by omega
  have hnR : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hn1
  have hrg : ∀ c : ℝ, 0 ≤ c → c ≤ 2 ^ 40 → c * ((w.length + 1 : ℕ) : ℝ) ≤ M :=
    fun c h0 h1 => range_lin hM hn1 h0 h1
  have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
    have := hrg 1 (by norm_num) (by norm_num)
    linarith
  have h258 : 258 * ((w.length + 1 : ℕ) : ℝ) ≤ M := hrg 258 (by norm_num) (by norm_num)
  have h300 : (300 : ℝ) ≤ M := range_const hM hn1 (by norm_num)
  have hηs := eta_tiny hη
  have hη5 : η ≤ 1 / 100000 := le_trans hηs (by norm_num)
  have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 100000 := by norm_num
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by linarith
  have c20 : ((20 : ℚ) : ℝ) = 20 := by norm_num
  have c1 : ((1 : ℚ) : ℝ) = 1 := by norm_num
  have c100 : ((-100 : ℚ) : ℝ) = -100 := by norm_num
  have a100 : |((-100 : ℚ) : ℝ)| = 100 := by
    rw [c100, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 100)]
  obtain ⟨S, hSd⟩ : ∃ S : ℝ, S = sw fl 20 (p.A 0 0 3 4) := ⟨_, rfl⟩
  obtain ⟨T, hTd⟩ : ∃ T : ℝ, T = sw fl (-100) (p.A 0 0 5 1) := ⟨_, rfl⟩
  obtain ⟨T1, hT1d⟩ : ∃ T1 : ℝ, T1 = sw fl 1 (p.V 0 0 2 0) := ⟨_, rfl⟩
  obtain ⟨O, hOd⟩ : ∃ O : ℝ, O = sw fl 1 (p.oW 2) := ⟨_, rfl⟩
  have hS := sw_near hr hu0 20 (hp.A 0 0 3 4) (by norm_num)
    (by rw [c20, abs_of_nonneg (by norm_num)]; linarith) hε
  rw [c20, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 20), ← hSd] at hS
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  have hSl : (198 : ℝ) / 10 ≤ S := by linarith
  have hSu : S ≤ (202 : ℝ) / 10 := by linarith
  have hT := sw_near hr hu0 (-100) (hp.A 0 0 5 1) (by norm_num)
    (by rw [a100]; linarith) hε
  rw [a100, c100, ← hTd] at hT
  obtain ⟨hT1', hT2'⟩ := abs_le.mp hT
  have hTl : (-1006 : ℝ) / 10 ≤ T := by linarith
  have hTu : T ≤ (-994 : ℝ) / 10 := by linarith
  have hT1w := sw_near hr hu0 1 (hp.V 0 0 2 0) (by norm_num)
    (by rw [c1, abs_one]; linarith) hε
  rw [c1, abs_one, ← hT1d] at hT1w
  obtain ⟨hT1a, hT1b⟩ := abs_le.mp hT1w
  have hT1l : (99 : ℝ) / 100 ≤ T1 := by linarith
  have hT1u : T1 ≤ (101 : ℝ) / 100 := by linarith
  have hOw := sw_near hr hu0 1 (hp.oW 2) (by norm_num)
    (by rw [c1, abs_one]; linarith) hε
  rw [c1, abs_one, ← hOd] at hOw
  obtain ⟨hOa, hOb⟩ := abs_le.mp hOw
  have hOl : (99 : ℝ) / 100 ≤ O := by linarith
  have hOu : O ≤ (101 : ℝ) / 100 := by linarith
  -- embedding values
  have hvb : ∀ k : ℕ, (0 : ℝ) ≤ ((Lane4.Case.val (tokAt w k) : ℕ) : ℝ) ∧
      ((Lane4.Case.val (tokAt w k) : ℕ) : ℝ) ≤ 3 := by
    intro k
    refine ⟨Nat.cast_nonneg _, ?_⟩
    exact_mod_cast val_le (tokAt w k)
  have hval : ∀ k : ℕ, |ev fl p w k - ((Lane4.Case.val (tokAt w k) : ℕ) : ℝ)| ≤ 3 / 199 + η := by
    intro k
    have hc : ((vq (tokAt w k) : ℚ) : ℝ) = ((Lane4.Case.val (tokAt w k) : ℕ) : ℝ) := by
      simp [vq]
    have h := sw_near hr hu0 (vq (tokAt w k)) (hp.E (tokAt w k) 0) (by norm_num)
      (by rw [hc, abs_of_nonneg (hvb k).1]; linarith [(hvb k).2]) hε
    rw [hc, abs_of_nonneg (hvb k).1] at h
    unfold ev
    refine le_trans h ?_
    linarith [(hvb k).2]
  have hev0 : ∀ k : ℕ, Lane4.Case.val (tokAt w k) = 0 → ev fl p w k = 0 := by
    intro k h
    unfold ev
    simp [vq, h, sw_zero hr]
  have heu0 : ∀ k : ℕ, Lane4.Case.val (tokAt w k) ≠ 0 → eu fl p w k = 0 := by
    intro k h
    unfold eu
    simp [uq, h, sw_zero hr]
  have heu1 : ∀ k : ℕ, Lane4.Case.val (tokAt w k) = 0 →
      99 / 100 ≤ eu fl p w k ∧ eu fl p w k ≤ 101 / 100 := by
    intro k h
    have hc : ((uq (tokAt w k) : ℚ) : ℝ) = 1 := by simp [uq, h]
    have h2 := sw_near hr hu0 (uq (tokAt w k)) (hp.E (tokAt w k) 1) (by norm_num)
      (by rw [hc, abs_one]; linarith) hε
    rw [hc, abs_one] at h2
    unfold eu
    obtain ⟨a, b⟩ := abs_le.mp h2
    constructor <;> linarith
  have heub : ∀ k : ℕ, 0 ≤ eu fl p w k ∧ eu fl p w k ≤ 101 / 100 := by
    intro k
    by_cases h : Lane4.Case.val (tokAt w k) = 0
    · have := heu1 k h
      constructor <;> linarith [this.1, this.2]
    · rw [heu0 k h]
      norm_num
  have hTeb : ∀ k : ℕ, |T * eu fl p w k| ≤ 102 := by
    intro k
    rw [abs_mul]
    have h1 : |T| ≤ 1006 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |eu fl p w k| ≤ 101 / 100 :=
      abs_le.mpr ⟨by linarith [(heub k).1], (heub k).2⟩
    have := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    linarith
  have hTEb : ∀ k : ℕ, |T1 * ev fl p w k| ≤ 31 / 10 := by
    intro k
    rw [abs_mul]
    obtain ⟨e1, e2⟩ := abs_le.mp (hval k)
    have h1 : |T1| ≤ 101 / 100 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |ev fl p w k| ≤ 302 / 100 :=
      abs_le.mpr ⟨by linarith [(hvb k).1], by linarith [(hvb k).2]⟩
    have := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    linarith
  -- positions and scores
  have hPb : ∀ k : ℕ, k ≤ w.length + 1 → |S * fl (k : ℝ)| ≤ 21 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    obtain ⟨hk0, hk1⟩ := hr.pos_le hu0 hη hk hn hnM
    rw [abs_of_nonneg (mul_nonneg (by linarith) hk0)]
    have := mul_le_mul (show S ≤ 202 / 10 by linarith) hk1 hk0 (by norm_num)
    linarith
  have h21 : 21 * ((w.length + 1 : ℕ) : ℝ) ≤ M := hrg 21 (by norm_num) (by norm_num)
  have hsk : ∀ k : ℕ, k ≤ w.length + 1 →
      hscore hd fl (p.A 0 0) (net.init fl p w) i k =
        fl (fl (S * fl (k : ℝ)) +
          fl (fl ((w.length + 1 : ℕ) : ℝ) * fl (T * eu fl p w k))) := by
    intro k hk
    have hb1 := hPb k hk
    have hb2 := hTeb k
    subst hSd
    subst hTd
    simp only [hscore, init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact score_eq hr _ _ _ _ _ _ _ _ _ _ _ (hr.idem _ (le_trans hb1 h21))
      (hr.idem _ (le_trans hb2 (by linarith)))
  have hfn := hr.pos_le hu0 hη (le_refl (w.length + 1)) hn hnM
  have hfn2 := abs_le.mp (hr.pos_near hu0 hη (le_refl (w.length + 1)) hn hnM)
  -- the head's inputs
  have hat0 := attn_eq (ex := ex) hr p w hw i
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, s = hscore hd fl (p.A 0 0) (net.init fl p w) i := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ,
      f = fun j => rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 2) 0 0 := ⟨_, rfl⟩
  have hat := hat0 s f hs hf
  obtain ⟨A, hAd⟩ : ∃ A : ℝ,
      A = savg fl ex (cand Mask.causal (w.length + 1) i) s f := ⟨_, rfl⟩
  rw [← hAd] at hat
  have hfk : ∀ k : ℕ, f k = fl (T1 * ev fl p w k) := by
    intro k
    have hb := hTEb k
    rw [hf]
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    subst hT1d
    exact val_eq hr _ _ _ _ _ _ (hr.idem _ (le_trans hb (by linarith)))
  have hfB : ∀ k ∈ cand Mask.causal (w.length + 1) i, |f k| ≤ 33 / 10 := by
    intro k _
    rw [hfk k]
    have := hr.bound hu0 (hTEb k) (show (31 / 10 : ℝ) ≤ M by linarith)
    linarith
  have hlen : (cand Mask.causal (w.length + 1) i).length ≤ w.length + 1 := by
    simp only [cand, List.length_range]
    omega
  rcases last_marked w i hi with ⟨hnone, htarget⟩ | ⟨j, hj1, hji, hjm, hafter, htarget⟩
  · -- no marked token up to i
    have hz : A = 0 := by
      rw [hAd]
      apply soft_zeros hr
      intro k hk
      rw [Lane4.Seq.mem_cand_causal] at hk
      have hk0 : Lane4.Case.val (tokAt w k) = 0 := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0
          simp [Lane4.Seq.tokAt_zero, Lane4.Case.val]
        · exact hnone k (by omega) hk
      rw [hfk k, hev0 k hk0]
      simp [hr.zero]
    have hA0 : fl A = A := by
      rw [hz]
      exact hr.zero
    rw [out_eq hr p w hw i A hat hA0 (by rw [hz]; simp [hr.zero])]
    rw [hz]
    unfold target
    rw [htarget]
    norm_num [hr.zero]
  · -- the last marked token is at j
    have hj : j ∈ cand Mask.causal (w.length + 1) i := Lane4.Seq.mem_cand_causal.mpr hji
    have hjn : j ≤ w.length + 1 := by omega
    have hsc : ∀ k : ℕ, k ≤ w.length + 1 →
        s k = fl (fl (S * fl (k : ℝ)) +
          fl (fl ((w.length + 1 : ℕ) : ℝ) * fl (T * eu fl p w k))) := by
      intro k hk
      rw [hs]
      exact hsk k hk
    have hsj : s j = fl (S * fl (j : ℝ)) := by
      rw [hsc j hjn, heu0 j hjm]
      have hI := hr.idem _ (le_trans (hPb j hjn) h21)
      simp [hr.zero, hI]
    have hgap : ∀ k ∈ cand Mask.causal (w.length + 1) i, k ≠ j →
        s k ≤ s j - 16 * (ndist j k : ℝ) := by
      intro k hk hne
      rw [Lane4.Seq.mem_cand_causal] at hk
      have hkn : k ≤ w.length + 1 := by omega
      obtain ⟨hk0, hk1⟩ := hr.pos_le hu0 hη hkn hn hnM
      obtain ⟨hj0, hj1'⟩ := hr.pos_le hu0 hη hjn hn hnM
      have hjk0 := abs_le.mp (hr.pos_near hu0 hη hkn hn hnM)
      have hjj0 := abs_le.mp (hr.pos_near hu0 hη hjn hn hnM)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hg := hr.pos_gap hu0 hη (le_of_lt hlt) hjn hn hnM
        have hd1 : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hlt
        have hE := gap_early hr hu0 hη hnR hn h21 hSl hSu hk0 hj0 hk1 hj1'
          (d := (j : ℝ) - k) (by linarith) hg
        have hle := sx_le hr hu0 hu1 hη hnR hn h258 hSl hSu hTl hTu (heub k).1 (heub k).2
          hk0 hk1 hfn.1 hfn.2
        rw [ndist_cast, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (j : ℝ) - (k : ℝ))]
        rw [hsc k hkn, hsj]
        linarith
      · have hkm := hafter k hgt hk
        have heu := heu1 k hkm
        have hjlt : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hgt
        have hkN : (k : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hkn
        have hj00 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
        have hlate := gap_late hr hu0 hu1 hη hnR hn h258 hSl hSu hTl hTu (heub k).1 (heub k).2
          hk0 hk1 hfn.1 hfn.2 hkN hj00 (by linarith [hjk0.2]) (by linarith [hjj0.1]) hj0 hj1'
          (by linarith [hfn2.1]) heu.1
        rw [ndist_cast, abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - (j : ℝ))]
        rw [hsc k hkn, hsj]
        linarith
    have hSb : ∀ k ∈ cand Mask.causal (w.length + 1) i,
        |s k| ≤ 129 * ((w.length + 1 : ℕ) : ℝ) := by
      intro k hk
      rw [Lane4.Seq.mem_cand_causal] at hk
      have hkn : k ≤ w.length + 1 := by omega
      obtain ⟨hk0, hk1⟩ := hr.pos_le hu0 hη hkn hn hnM
      rw [hsc k hkn]
      exact sx_abs hr hu0 hu1 hη hnR hn h258 hSl hSu hTl hTu (heub k).1 (heub k).2
        hk0 hk1 hfn.1 hfn.2
    have hnear := soft_near hr he hu0 hu1 hη0 hη (Lane4.Seq.cand_nodup _ _ _) hlen hn hnη
      hj hgap hSb (by linarith) hfB (by linarith)
    rw [← hAd] at hnear
    obtain ⟨hA1, hA2⟩ := hnear
    rw [hfk j] at hA1
    obtain ⟨v, hvd⟩ : ∃ v : ℝ, v = ((Lane4.Case.val (tokAt w j) : ℕ) : ℝ) := ⟨_, rfl⟩
    have hvb' := hvb j
    rw [← hvd] at hvb'
    have hE := hval j
    rw [← hvd] at hE
    unfold target
    rw [htarget, ← hvd]
    have hta : |v| ≤ 3 := by
      rw [abs_of_nonneg hvb'.1]
      exact hvb'.2
    have ha : (1 : ℝ) / 199 * 1 + η ≤ 1 / 190 := by linarith
    have hb : (3 : ℝ) / 199 + η ≤ 1 / 60 := by linarith
    have hb0 : (0 : ℝ) ≤ 3 / 199 + η := by linarith
    have m1 := mul_le_mul ha hta (abs_nonneg _) (by norm_num)
    have m2 := mul_le_mul ha hb hb0 (by norm_num)
    have e1 := mul_near hT1w hE
    rw [one_mul, abs_one] at e1
    have e1' : |T1 * ev fl p w j - v| ≤ 1 / 25 := by linarith
    have e2 := hr.near hu0 e1' (hTEb j) (show (31 / 10 : ℝ) ≤ M by linarith)
    have e3 := abs_sub_le A (fl (T1 * ev fl p w j)) v
    have hX : |A - v| ≤ 1 / 10 := by linarith
    have hAb' : |A| ≤ 31 / 10 := by
      have := abs_sub_abs_le_abs_sub A v
      linarith
    have hOAb : |O * A| ≤ 4 := by
      rw [abs_mul]
      have h1 : |O| ≤ 101 / 100 := abs_le.mpr ⟨by linarith, by linarith⟩
      have := mul_le_mul h1 hAb' (abs_nonneg _) (by norm_num)
      linarith
    have hIout : fl (fl (sw fl 1 (p.oW 2) * A)) = fl (sw fl 1 (p.oW 2) * A) := by
      rw [← hOd]
      exact hr.idem _ (le_trans hOAb (by linarith))
    rw [out_eq hr p w hw i A hat hA2 hIout, ← hOd]
    have e4 := mul_near hOw hX
    rw [one_mul, abs_one] at e4
    have e4' : |O * A - v| ≤ 1 / 8 := by linarith
    have e5 := hr.near hu0 e4' hOAb (show (4 : ℝ) ≤ M by linarith)
    linarith

end Lane4.Case
