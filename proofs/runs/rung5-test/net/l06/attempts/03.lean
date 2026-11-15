set_option linter.unusedVariables false

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

/-- State: [val, ub, res, 1, fl i, fl n] (width 6). -/
def z6 : List ℚ := [0, 0, 0, 0, 0, 0]

/-- Score of key k = S * pos k + (fl n) * g * ub k, where `ub` is -40 on unmarked tokens
and exactly 0 on marked tokens. Causal mask. Value: copy `val` into slot `res`. -/
def hd : Head :=
  { A := [z6, z6, z6, [0, 0, 0, 0, 17, 0], z6, [0, 1, 0, 0, 0, 0]],
    V := [z6, z6, [1, 0, 0, 0, 0, 0], z6, z6, z6],
    mask := Mask.causal }

def blk : Block :=
  { heads := [hd], W1 := [], b1 := [], W2 := [[], [], [], [], [], []], b2 := z6 }

def net : TNet :=
  { embed := [[0, -40, 0], [1, 0, 0], [0, -40, 0], [3, 0, 0], [1, 0, 0], [3, 0, 0]],
    blocks := [blk],
    outW := [0, 0, 1, 0, 0, 0],
    outB := 0 }

noncomputable def ev (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl ((val (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 0)

noncomputable def ub (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (if val (tokAt w j) = 0 then (-40 : ℚ) else 0) (p.E (tokAt w j) 1)

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem val_le (t : ℕ) : val t ≤ 3 := by
  unfold val
  split_ifs <;> omega

theorem init_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [ev fl p w j, ub fl p w j, 0] ++ pos fl j (w.length + 1) := by
  have h6 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 ∨
      tokAt w j = 5 := by
    have := tok_le w hw j
    omega
  rcases h6 with h | h | h | h | h | h <;>
    simp [TNet.init, net, ev, ub, swRow, h, val, sw_zero hr]

theorem ev_zero {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ) (j : ℕ)
    (h : val (tokAt w j) = 0) : ev fl p w j = 0 := by
  unfold ev
  rw [h, Nat.cast_zero]
  exact sw_zero hr _

theorem ub_zero {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ) (j : ℕ)
    (h : val (tokAt w j) ≠ 0) : ub fl p w j = 0 := by
  unfold ub
  rw [if_neg h]
  exact sw_zero hr _

theorem score_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (a0 a1 qi qn b0 b1 qk qn' : ℝ)
    (hI1 : fl (fl (sw fl 17 (dA 3 4) * qk)) = fl (sw fl 17 (dA 3 4) * qk))
    (hI2 : fl (fl (sw fl 1 (dA 5 1) * b1)) = fl (sw fl 1 (dA 5 1) * b1)) :
    hd.score fl dA [a0, a1, 0, 1, qi, qn] [b0, b1, 0, 1, qk, qn'] =
      fl (fl (sw fl 17 (dA 3 4) * qk) + fl (qn * fl (sw fl 1 (dA 5 1) * b1))) := by
  simp [Head.score, hd, z6, pdot, rmat, rdot, sw_zero hr, hr.zero, hI1, hI2]

theorem val_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ) (b0 b1 qk qn : ℝ)
    (hI : fl (fl (sw fl 1 (dV 0) * b0)) = fl (sw fl 1 (dV 0) * b0)) :
    rdot fl [1, 0, 0, 0, 0, 0] [b0, b1, 0, 1, qk, qn] dV 0 0 = fl (sw fl 1 (dV 0) * b0) := by
  simp [rdot, sw_zero hr, hr.zero, hI]

theorem zrow_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ)
    (a b c d e f : ℝ) :
    rdot fl z6 [a, b, c, d, e, f] dV 0 0 = 0 := by
  simp [z6, rdot, sw_zero hr, hr.zero]

theorem attn_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) :
    sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, savg fl ex (cand Mask.causal (w.length + 1) i)
              (hscore hd fl (p.A 0 0) (net.init fl p w) i)
              (fun j => rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 2) 0 0),
         0, 0, 0] := by
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
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) (A : ℝ)
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

/-! ### last marked token -/

theorem lastv_succ (w : List ℕ) (i : ℕ) (h : i < w.length) :
    lastv (w.take (i + 1)) =
      if val (tokAt w (i + 1)) = 0 then lastv (w.take i) else val (tokAt w (i + 1)) := by
  rw [Lane4.Seq.tokAt_succ w i h]
  have ht : w.take (i + 1) = w.take i ++ [w[i]] := by
    first
    | exact List.take_succ_eq_append_getElem h
    | simp [List.take_add_one, h]
    | simp [List.take_succ, h]
  rw [ht]
  unfold lastv
  rw [List.foldl_append]
  rfl

theorem last_lemma (w : List ℕ) : ∀ i, i ≤ w.length →
    ((∀ j, j ≤ i → val (tokAt w j) = 0) ∧ lastv (w.take i) = 0) ∨
    (∃ J, J ≤ i ∧ val (tokAt w J) ≠ 0 ∧ (∀ k, J < k → k ≤ i → val (tokAt w k) = 0) ∧
      lastv (w.take i) = val (tokAt w J)) := by
  intro i
  induction i with
  | zero =>
    intro _
    left
    refine ⟨?_, ?_⟩
    · intro j hj
      have : j = 0 := by omega
      subst this
      rw [Lane4.Seq.tokAt_zero]
      simp [val]
    · simp [lastv]
  | succ i ih =>
    intro hi1
    have hi : i ≤ w.length := by omega
    have hlt : i < w.length := by omega
    have hs := lastv_succ w i hlt
    by_cases hm : val (tokAt w (i + 1)) = 0
    · rcases ih hi with ⟨h1, h2⟩ | ⟨J, hJ, hJm, hJl, hJt⟩
      · left
        refine ⟨?_, ?_⟩
        · intro j hj
          rcases Nat.lt_or_ge j (i + 1) with h | h
          · exact h1 j (by omega)
          · have : j = i + 1 := by omega
            subst this
            exact hm
        · rw [hs, if_pos hm]
          exact h2
      · right
        refine ⟨J, by omega, hJm, ?_, ?_⟩
        · intro k hk1 hk2
          rcases Nat.lt_or_ge k (i + 1) with h | h
          · exact hJl k hk1 (by omega)
          · have : k = i + 1 := by omega
            subst this
            exact hm
        · rw [hs, if_pos hm]
          exact hJt
    · right
      refine ⟨i + 1, le_refl _, hm, ?_, ?_⟩
      · intro k hk1 hk2
        omega
      · rw [hs, if_neg hm]

/-! ### numeric lemmas -/

theorem bnd18 {n S P : ℝ} (hn1 : 1 ≤ n) (hS0 : 0 ≤ S) (hS2 : S ≤ 171 / 10) (hP0 : 0 ≤ P)
    (hP1 : P ≤ n + 1 / 100) : |S * P| ≤ 18 * n := by
  rw [abs_of_nonneg (mul_nonneg hS0 hP0)]
  have := mul_le_mul hS2 hP1 hP0 (by norm_num)
  linarith

theorem gub_range {g ub : ℝ} (hg1 : 99 / 100 ≤ g) (hg2 : g ≤ 101 / 100)
    (hub1 : -161 / 4 ≤ ub) (hub2 : ub ≤ -159 / 4) : -41 ≤ g * ub ∧ g * ub ≤ -39 := by
  have hg0 : 0 ≤ g := by linarith
  have a := mul_le_mul_of_nonneg_left hub2 hg0
  have b := mul_le_mul_of_nonneg_left hub1 hg0
  constructor <;> linarith

theorem unm_core {u η M n : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 1000) (hu : u ≤ 1 / 1000) (hn : u * n ≤ 1 / 256) (hn1 : 1 ≤ n)
    (hM : 130 * n ≤ M)
    {S g ub Pk Pn : ℝ} (hS1 : 169 / 10 ≤ S) (hS2 : S ≤ 171 / 10)
    (hg1 : 99 / 100 ≤ g) (hg2 : g ≤ 101 / 100)
    (hub1 : -161 / 4 ≤ ub) (hub2 : ub ≤ -159 / 4) (hPk0 : 0 ≤ Pk) (hPk1 : Pk ≤ n + 1 / 100)
    (hPn1 : n - 1 / 200 ≤ Pn) (hPn2 : Pn ≤ n + 1 / 100) :
    |fl (S * Pk) + fl (Pn * fl (g * ub))| ≤ 62 * n ∧
    fl (S * Pk) + fl (Pn * fl (g * ub))
      ≤ 171 / 10 * (n + 1 / 100) - 38 * (n - 1 / 200) + 61 / 256 + 2 / 1000 := by
  have hS0 : 0 ≤ S := by linarith
  have hPn0 : 0 ≤ Pn := by linarith
  obtain ⟨e2, e1⟩ := gub_range hg1 hg2 hub1 hub2
  have e3 : |g * ub| ≤ 41 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hv5 := abs_le.mp (hr.abs hu0 e3 (by linarith : (41 : ℝ) ≤ M))
  have h5u : fl (g * ub) ≤ -38 := by linarith [hv5.2]
  have h5l : -42 ≤ fl (g * ub) := by linarith [hv5.1]
  have p1 : Pn * fl (g * ub) ≤ Pn * (-38) := mul_le_mul_of_nonneg_left h5u hPn0
  have p2 : Pn * (-42) ≤ Pn * fl (g * ub) := mul_le_mul_of_nonneg_left h5l hPn0
  have hB2 : |Pn * fl (g * ub)| ≤ 43 * n := abs_le.mpr ⟨by linarith, by linarith⟩
  have hq2 := abs_le.mp (hr.abs hu0 hB2 (by linarith : 43 * n ≤ M))
  have hB1 := bnd18 hn1 hS0 hS2 hPk0 hPk1
  have hq1 := abs_le.mp (hr.abs hu0 hB1 (by linarith : 18 * n ≤ M))
  have hSP : S * Pk ≤ 171 / 10 * (n + 1 / 100) := mul_le_mul hS2 hPk1 hPk0 (by norm_num)
  have hSP0 : 0 ≤ S * Pk := mul_nonneg hS0 hPk0
  have hun1 : u * (18 * n) = 18 * (u * n) := by ring
  have hun2 : u * (43 * n) = 43 * (u * n) := by ring
  constructor
  · rw [abs_le]
    constructor <;> linarith [hq1.1, hq1.2, hq2.1, hq2.2]
  · linarith [hq1.1, hq1.2, hq2.1, hq2.2]

theorem bnd_unm {u η M n : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 1000) (hu : u ≤ 1 / 1000) (hn : u * n ≤ 1 / 256) (hn1 : 1 ≤ n)
    (hM : 130 * n ≤ M)
    {S g ub Pk Pn : ℝ} (hS1 : 169 / 10 ≤ S) (hS2 : S ≤ 171 / 10)
    (hg1 : 99 / 100 ≤ g) (hg2 : g ≤ 101 / 100)
    (hub1 : -161 / 4 ≤ ub) (hub2 : ub ≤ -159 / 4) (hPk0 : 0 ≤ Pk) (hPk1 : Pk ≤ n + 1 / 100)
    (hPn1 : n - 1 / 200 ≤ Pn) (hPn2 : Pn ≤ n + 1 / 100) :
    |fl (fl (S * Pk) + fl (Pn * fl (g * ub)))| ≤ 62 * n + 1 := by
  obtain ⟨hx1, _⟩ := unm_core hr hu0 hη0 hη hu hn hn1 hM hS1 hS2 hg1 hg2 hub1 hub2 hPk0 hPk1
    hPn1 hPn2
  have h := hr.bound hu0 hx1 (by linarith : 62 * n ≤ M)
  have hun : u * (62 * n) = 62 * (u * n) := by ring
  linarith

theorem bnd_mar {u η M n : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hη : η ≤ 1 / 1000) (hn : u * n ≤ 1 / 256) (hn1 : 1 ≤ n) (hM : 130 * n ≤ M)
    {S Pk : ℝ} (hS1 : 169 / 10 ≤ S) (hS2 : S ≤ 171 / 10)
    (hPk0 : 0 ≤ Pk) (hPk1 : Pk ≤ n + 1 / 100) :
    |fl (S * Pk)| ≤ 62 * n + 1 := by
  have hS0 : 0 ≤ S := by linarith
  have hB1 := bnd18 hn1 hS0 hS2 hPk0 hPk1
  have h := hr.bound hu0 hB1 (by linarith : 18 * n ≤ M)
  have hun1 : u * (18 * n) = 18 * (u * n) := by ring
  linarith

theorem gap_unm {u η M n : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 1000) (hu : u ≤ 1 / 1000) (hn : u * n ≤ 1 / 256) (hn1 : 1 ≤ n)
    (hM : 130 * n ≤ M)
    {S g ub Pk PJ Pn d : ℝ} (hS1 : 169 / 10 ≤ S) (hS2 : S ≤ 171 / 10)
    (hg1 : 99 / 100 ≤ g) (hg2 : g ≤ 101 / 100)
    (hub1 : -161 / 4 ≤ ub) (hub2 : ub ≤ -159 / 4) (hPk0 : 0 ≤ Pk) (hPk1 : Pk ≤ n + 1 / 100)
    (hPJ0 : 0 ≤ PJ) (hPJ1 : PJ ≤ n + 1 / 100)
    (hPn1 : n - 1 / 200 ≤ Pn) (hPn2 : Pn ≤ n + 1 / 100) (hd0 : 0 ≤ d) (hd1 : d ≤ n) :
    fl (fl (S * Pk) + fl (Pn * fl (g * ub))) ≤ fl (S * PJ) - 16 * d := by
  obtain ⟨hx1, hx2⟩ := unm_core hr hu0 hη0 hη hu hn hn1 hM hS1 hS2 hg1 hg2 hub1 hub2 hPk0 hPk1
    hPn1 hPn2
  have hS0 : 0 ≤ S := by linarith
  have hB1J := bnd18 hn1 hS0 hS2 hPJ0 hPJ1
  have hJl := Rnd.lower hr hu0 hB1J (by linarith : 18 * n ≤ M)
  have hku := Rnd.upper hr hu0 hx1 (by linarith : 62 * n ≤ M)
  have hSJ0 : 0 ≤ S * PJ := mul_nonneg hS0 hPJ0
  have hun1 : u * (18 * n) = 18 * (u * n) := by ring
  have hun3 : u * (62 * n) = 62 * (u * n) := by ring
  linarith

theorem gap_mar {u η M n : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hη : η ≤ 1 / 1000) (hn : u * n ≤ 1 / 256) (hn1 : 1 ≤ n) (hM : 130 * n ≤ M)
    {S Pk PJ d : ℝ} (hS1 : 169 / 10 ≤ S) (hS2 : S ≤ 171 / 10)
    (hPk0 : 0 ≤ Pk) (hPk1 : Pk ≤ n + 1 / 100)
    (hPJ0 : 0 ≤ PJ) (hPJ1 : PJ ≤ n + 1 / 100) (hd1 : 1 ≤ d) (hgap : Pk + d - 1 / 100 ≤ PJ) :
    fl (S * Pk) ≤ fl (S * PJ) - 16 * d := by
  have hS0 : 0 ≤ S := by linarith
  have hBk := bnd18 hn1 hS0 hS2 hPk0 hPk1
  have hBJ := bnd18 hn1 hS0 hS2 hPJ0 hPJ1
  have hgp := Rnd.gap hr hu0 hBk hBJ (by linarith : 18 * n ≤ M)
  have hD0 : 0 ≤ PJ - Pk := by linarith
  have hSD := mul_le_mul_of_nonneg_right hS1 hD0
  have hun1 : u * (18 * n) = 18 * (u * n) := by ring
  linarith

theorem chain {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hη0 : 0 ≤ η)
    (hu : u ≤ 1 / 1000) (hη : η ≤ 1 / 100000) (hM : 4 ≤ M)
    {T E O A v : ℝ} (hv0 : 0 ≤ v) (hv3 : v ≤ 3)
    (hT : |T - 1| ≤ 1 / 199 + η) (hE : |E - v| ≤ 3 / 199 + η) (hO : |O - 1| ≤ 1 / 199 + η)
    (hA : |A - fl (T * E)| ≤ 4 / 100 + 1 / 2 ^ 90) :
    |fl (O * A) - v| ≤ 1 / 4 ∧ |O * A| ≤ 4 := by
  have h2 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 100000 := by norm_num
  have hTE : |T * E - v| ≤ 1 / 30 := by
    have e1 := mul_near hT hE
    simp only [one_mul, abs_one, abs_of_nonneg hv0] at e1
    have a1 : (1 / 199 + η) * v ≤ 1 / 190 * 3 := mul_le_mul (by linarith) hv3 hv0 (by norm_num)
    have a2 : (1 / 199 + η) * (3 / 199 + η) ≤ 1 / 190 * (1 / 60) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    linarith
  have hTEb : |T * E| ≤ 4 := by
    have := abs_le.mp hTE
    exact abs_le.mpr ⟨by linarith [this.1], by linarith [this.2]⟩
  have e2 := hr.near hu0 hTE hTEb hM
  have hAv : |A - v| ≤ 8 / 100 := by
    have := abs_sub_le A (fl (T * E)) v
    linarith
  have hOb : |O| ≤ 101 / 100 := by
    have := abs_le.mp hO
    exact abs_le.mpr ⟨by linarith [this.1], by linarith [this.2]⟩
  have hAb : |A| ≤ 31 / 10 := by
    have := abs_le.mp hAv
    exact abs_le.mpr ⟨by linarith [this.1], by linarith [this.2]⟩
  have hOA : |O * A| ≤ 4 := by
    rw [abs_mul]
    have := mul_le_mul hOb hAb (abs_nonneg _) (by norm_num)
    linarith
  have e4 := mul_near hO hAv
  simp only [one_mul, abs_one, abs_of_nonneg hv0] at e4
  have b1 : (1 / 199 + η) * v ≤ 1 / 190 * 3 := mul_le_mul (by linarith) hv3 hv0 (by norm_num)
  have b2 : (1 / 199 + η) * (8 / 100) ≤ 1 / 190 * (8 / 100) :=
    mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
  have e4' : |O * A - v| ≤ 1 / 5 := by linarith
  have e5 := hr.near hu0 e4' hOA hM
  exact ⟨by linarith, hOA⟩

set_option maxHeartbeats 1600000 in
theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη p hp w hw hn hnη hM i hi1 hi
  have hn1 : 1 ≤ w.length + 1 := by omega
  have hnR : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hn1
  have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
    have := range_lin hM hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have h130 : 130 * ((w.length + 1 : ℕ) : ℝ) ≤ M :=
    range_lin hM hn1 (by norm_num) (by norm_num)
  have h18 : 18 * ((w.length + 1 : ℕ) : ℝ) ≤ M := by linarith
  have h41 : (41 : ℝ) ≤ M := by linarith
  have hM4 : (4 : ℝ) ≤ M := by linarith
  have hηs := eta_tiny hη
  have hη' : η ≤ 1 / 1000 := le_trans hηs (by norm_num)
  have hηs' : η ≤ 1 / 100000 := le_trans hηs (by norm_num)
  have hu' : u ≤ 1 / 1000 := le_trans hu1 (by norm_num)
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by linarith
  have c17 : ((17 : ℚ) : ℝ) = 17 := by norm_num
  have c1 : ((1 : ℚ) : ℝ) = 1 := by norm_num
  have c40 : ((-40 : ℚ) : ℝ) = -40 := by norm_num
  -- stored weights: S ~ 17, g ~ 1, T ~ 1, O ~ 1
  have hS := sw_near hr hu0 17 (hp.A 0 0 3 4) (by norm_num)
    (by rw [c17, abs_of_nonneg (by norm_num)]; linarith) hε
  rw [c17, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 17)] at hS
  obtain ⟨hS1', hS2'⟩ := abs_le.mp hS
  have hSlo : 169 / 10 ≤ sw fl 17 (p.A 0 0 3 4) := by linarith
  have hShi : sw fl 17 (p.A 0 0 3 4) ≤ 171 / 10 := by linarith
  have hS0 : 0 ≤ sw fl 17 (p.A 0 0 3 4) := by linarith
  have hgw := sw_near hr hu0 1 (hp.A 0 0 5 1) (by norm_num)
    (by rw [c1, abs_of_nonneg (by norm_num)]; linarith) hε
  rw [c1, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)] at hgw
  obtain ⟨hg1', hg2'⟩ := abs_le.mp hgw
  have hg1 : 99 / 100 ≤ sw fl 1 (p.A 0 0 5 1) := by linarith
  have hg2 : sw fl 1 (p.A 0 0 5 1) ≤ 101 / 100 := by linarith
  have hT := sw_near hr hu0 1 (hp.V 0 0 2 0) (by norm_num)
    (by rw [c1, abs_of_nonneg (by norm_num)]; linarith) hε
  rw [c1, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)] at hT
  have hT' : |sw fl 1 (p.V 0 0 2 0) - 1| ≤ 1 / 199 + η := le_trans hT (by linarith)
  obtain ⟨hT1', hT2'⟩ := abs_le.mp hT'
  have hO := sw_near hr hu0 1 (hp.oW 2) (by norm_num)
    (by rw [c1, abs_of_nonneg (by norm_num)]; linarith) hε
  rw [c1, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)] at hO
  have hO' : |sw fl 1 (p.oW 2) - 1| ≤ 1 / 199 + η := le_trans hO (by linarith)
  -- stored embedding entries
  have hevn : ∀ j : ℕ, |ev fl p w j - ((val (tokAt w j) : ℕ) : ℝ)| ≤ 3 / 199 + η := by
    intro j
    have h3 : ((val (tokAt w j) : ℕ) : ℝ) ≤ 3 := by exact_mod_cast val_le _
    have h0 : (0 : ℝ) ≤ ((val (tokAt w j) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hc : (((val (tokAt w j) : ℕ) : ℚ) : ℝ) = ((val (tokAt w j) : ℕ) : ℝ) := by norm_num
    have h := sw_near hr hu0 ((val (tokAt w j) : ℕ) : ℚ) (hp.E (tokAt w j) 0) (by norm_num)
      (by rw [hc, abs_of_nonneg h0]; linarith) hε
    rw [hc, abs_of_nonneg h0] at h
    unfold ev
    linarith
  have hubn : ∀ j : ℕ, val (tokAt w j) = 0 → |ub fl p w j + 40| ≤ 1 / 4 := by
    intro j hj
    have e40 : |(-40 : ℝ)| = 40 := by norm_num
    have h := sw_near hr hu0 (-40 : ℚ) (hp.E (tokAt w j) 1) (by norm_num)
      (by rw [c40, e40]; linarith) hε
    rw [c40, e40] at h
    obtain ⟨h1, h2⟩ := abs_le.mp h
    unfold ub
    rw [if_pos hj]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hubb : ∀ j : ℕ, ub fl p w j = 0 ∨
      (-161 / 4 ≤ ub fl p w j ∧ ub fl p w j ≤ -159 / 4) := by
    intro j
    by_cases h : val (tokAt w j) = 0
    · right
      have := abs_le.mp (hubn j h)
      constructor <;> linarith [this.1, this.2]
    · left
      exact ub_zero hr p w j h
  have hgub : ∀ k : ℕ, |sw fl 1 (p.A 0 0 5 1) * ub fl p w k| ≤ 41 := by
    intro k
    rcases hubb k with h | ⟨h1, h2⟩
    · rw [h, mul_zero, abs_zero]; norm_num
    · obtain ⟨e2, e1⟩ := gub_range hg1 hg2 h1 h2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- positions
  have hPn := hr.pos_le hu0 hη (le_refl (w.length + 1)) hn hnM
  have hPn' := abs_le.mp (hr.pos_near hu0 hη (le_refl (w.length + 1)) hn hnM)
  have hPn1 : ((w.length + 1 : ℕ) : ℝ) - 1 / 200 ≤ fl ((w.length + 1 : ℕ) : ℝ) := by
    linarith [hPn'.1]
  have hPb : ∀ k : ℕ, k ≤ w.length + 1 →
      |sw fl 17 (p.A 0 0 3 4) * fl (k : ℝ)| ≤ 18 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    obtain ⟨hk0, hk1⟩ := hr.pos_le hu0 hη hk hn hnM
    exact bnd18 hnR hS0 hShi hk0 hk1
  -- scores in closed form
  have hsk : ∀ k : ℕ, k ≤ w.length + 1 →
      hscore hd fl (p.A 0 0) (net.init fl p w) i k =
        fl (fl (sw fl 17 (p.A 0 0 3 4) * fl (k : ℝ)) +
          fl (fl ((w.length + 1 : ℕ) : ℝ) * fl (sw fl 1 (p.A 0 0 5 1) * ub fl p w k))) := by
    intro k hk
    simp only [hscore, init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact score_eq hr _ _ _ _ _ _ _ _ _
      (hr.idem _ (le_trans (hPb k hk) h18))
      (hr.idem _ (le_trans (hgub k) h41))
  have hskm : ∀ k : ℕ, k ≤ w.length + 1 → val (tokAt w k) ≠ 0 →
      hscore hd fl (p.A 0 0) (net.init fl p w) i k =
        fl (sw fl 17 (p.A 0 0 3 4) * fl (k : ℝ)) := by
    intro k hk hm
    rw [hsk k hk, ub_zero hr p w k hm]
    have hI := hr.idem _ (le_trans (hPb k hk) h18)
    simp [hr.zero, hI]
  -- values
  have hTEb : ∀ k : ℕ, |sw fl 1 (p.V 0 0 2 0) * ev fl p w k| ≤ 7 / 2 := by
    intro k
    have h3 : ((val (tokAt w k) : ℕ) : ℝ) ≤ 3 := by exact_mod_cast val_le _
    have h0 : (0 : ℝ) ≤ ((val (tokAt w k) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hE := abs_le.mp (hevn k)
    have hT1 : |sw fl 1 (p.V 0 0 2 0)| ≤ 101 / 100 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hE1 : |ev fl p w k| ≤ 31 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [abs_mul]
    have := mul_le_mul hT1 hE1 (abs_nonneg _) (by norm_num)
    linarith
  have hfk : ∀ k : ℕ, rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 2) 0 0
      = fl (sw fl 1 (p.V 0 0 2 0) * ev fl p w k) := by
    intro k
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact val_eq hr _ _ _ _ _ (hr.idem _ (le_trans (hTEb k) (by linarith)))
  have hfB : ∀ k ∈ cand Mask.causal (w.length + 1) i,
      |(fun j => rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 2) 0 0) k| ≤ 4 := by
    intro k _
    show |rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 2) 0 0| ≤ 4
    rw [hfk k]
    have := hr.bound hu0 (hTEb k) (by linarith : (7 / 2 : ℝ) ≤ M)
    linarith
  -- score bounds
  have hSb : ∀ k ∈ cand Mask.causal (w.length + 1) i,
      |hscore hd fl (p.A 0 0) (net.init fl p w) i k| ≤ 62 * ((w.length + 1 : ℕ) : ℝ) + 1 := by
    intro k hk
    rw [Lane4.Seq.mem_cand_causal] at hk
    have hkn : k ≤ w.length + 1 := by omega
    obtain ⟨hk0, hk1⟩ := hr.pos_le hu0 hη hkn hn hnM
    by_cases hm : val (tokAt w k) = 0
    · rw [hsk k hkn]
      have hub := abs_le.mp (hubn k hm)
      exact bnd_unm hr hu0 hη0 hη' hu' hn hnR h130 (hS1 := hSlo) (hS2 := hShi) (hg1 := hg1)
        (hg2 := hg2) (hub1 := by linarith [hub.1]) (hub2 := by linarith [hub.2])
        (hPk0 := hk0) (hPk1 := hk1) (hPn1 := hPn1) (hPn2 := hPn.2)
    · rw [hskm k hkn hm]
      exact bnd_mar hr hu0 hη' hn hnR h130 (hS1 := hSlo) (hS2 := hShi) (hPk0 := hk0)
        (hPk1 := hk1)
  have hlen : (cand Mask.causal (w.length + 1) i).length ≤ w.length + 1 := by
    simp only [cand, List.length_range]
    omega
  have hat := attn_eq (ex := ex) hr p w hw i
  rcases last_lemma w i hi with ⟨hz, hl0⟩ | ⟨J, hJ, hJm, hJlast, hJt⟩
  · -- no marked token yet: all values are exactly 0
    have hA0 : savg fl ex (cand Mask.causal (w.length + 1) i)
        (hscore hd fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 2) 0 0) = 0 := by
      apply soft_zeros hr
      intro k hk
      rw [Lane4.Seq.mem_cand_causal] at hk
      show rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 2) 0 0 = 0
      rw [hfk k, ev_zero hr p w k (hz k hk)]
      simp [hr.zero]
    rw [hA0] at hat
    rw [out_eq hr p w hw i 0 hat hr.zero (by simp [hr.zero])]
    have ht0 : target w i = 0 := by
      unfold target
      exact hl0
    rw [ht0]
    norm_num [hr.zero]
  · have hj : J ∈ cand Mask.causal (w.length + 1) i := by
      rw [Lane4.Seq.mem_cand_causal]
      exact hJ
    have hgap : ∀ k ∈ cand Mask.causal (w.length + 1) i, k ≠ J →
        hscore hd fl (p.A 0 0) (net.init fl p w) i k
          ≤ hscore hd fl (p.A 0 0) (net.init fl p w) i J - 16 * (ndist J k : ℝ) := by
      intro k hk hne
      rw [Lane4.Seq.mem_cand_causal] at hk
      have hkn : k ≤ w.length + 1 := by omega
      have hJn : J ≤ w.length + 1 := by omega
      have hkR : (k : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hkn
      have hJR : (J : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hJn
      have hk0R : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      have hJ0R : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg _
      rw [ndist_cast, hskm J hJn hJm]
      obtain ⟨hk0, hk1⟩ := hr.pos_le hu0 hη hkn hn hnM
      obtain ⟨hJ0, hJ1⟩ := hr.pos_le hu0 hη hJn hn hnM
      by_cases hm : val (tokAt w k) = 0
      · rw [hsk k hkn]
        have hub := abs_le.mp (hubn k hm)
        exact gap_unm hr hu0 hη0 hη' hu' hn hnR h130 (hS1 := hSlo) (hS2 := hShi) (hg1 := hg1)
          (hg2 := hg2) (hub1 := by linarith [hub.1]) (hub2 := by linarith [hub.2])
          (hPk0 := hk0) (hPk1 := hk1) (hPJ0 := hJ0) (hPJ1 := hJ1) (hPn1 := hPn1)
          (hPn2 := hPn.2) (hd0 := abs_nonneg _)
          (hd1 := by rw [abs_le]; constructor <;> linarith)
      · rw [hskm k hkn hm]
        have hkJ : k < J := by
          by_contra hcon
          have hJk : J < k := by omega
          exact hm (hJlast k hJk hk)
        have hkJR : (k : ℝ) + 1 ≤ (J : ℝ) := by exact_mod_cast hkJ
        have habs : |(J : ℝ) - (k : ℝ)| = (J : ℝ) - (k : ℝ) := abs_of_nonneg (by linarith)
        have hg := hr.pos_gap hu0 hη (le_of_lt hkJ) hJn hn hnM
        rw [habs]
        exact gap_mar hr hu0 hη' hn hnR h130 (hS1 := hSlo) (hS2 := hShi) (hPk0 := hk0)
          (hPk1 := hk1) (hPJ0 := hJ0) (hPJ1 := hJ1) (hd1 := by linarith)
          (hgap := by linarith)
    obtain ⟨hA1, hA2⟩ := soft_near hr he hu0 hu1 hη0 hη (Lane4.Seq.cand_nodup _ _ _) hlen hn hnη
      hj hgap hSb (by linarith) hfB (by linarith)
    have hAJ : |savg fl ex (cand Mask.causal (w.length + 1) i)
        (hscore hd fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 2) 0 0)
        - fl (sw fl 1 (p.V 0 0 2 0) * ev fl p w J)| ≤ 4 / 100 + 1 / 2 ^ 90 := by
      have := hA1
      simp only [hfk J] at this
      exact this
    have hv3 : ((val (tokAt w J) : ℕ) : ℝ) ≤ 3 := by exact_mod_cast val_le _
    have hv0 : (0 : ℝ) ≤ ((val (tokAt w J) : ℕ) : ℝ) := Nat.cast_nonneg _
    obtain ⟨hch1, hch2⟩ := chain hr hu0 hη0 hu' hηs' hM4 hv0 hv3 hT' (hevn J) hO' hAJ
    rw [out_eq hr p w hw i _ hat hA2 (hr.idem _ (le_trans hch2 hM4))]
    unfold target
    rw [hJt]
    exact hch1

end Lane4.Case
