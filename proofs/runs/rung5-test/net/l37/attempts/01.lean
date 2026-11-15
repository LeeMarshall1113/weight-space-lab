set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

def z6 : List ℚ := [0, 0, 0, 0, 0, 0]

def hd : Head :=
  { A := [z6, z6, z6, [0, 0, 0, 0, 17, 0], z6, [0, -40, 0, 0, 0, 0]],
    V := [z6, z6, [1, 0, 0, 0, 0, 0], z6, z6, z6],
    mask := Mask.causal }

def blk : Block :=
  { heads := [hd], W1 := [], b1 := [], W2 := [[], [], [], [], [], []], b2 := z6 }

def net : TNet :=
  { embed := [[0, 1, 0], [3, 0, 0], [0, 1, 0], [1, 0, 0], [0, 1, 0], [2, 0, 0]],
    blocks := [blk],
    outW := [0, 0, 1, 0, 0, 0],
    outB := 0 }

def euq (t : ℕ) : ℚ := if val t = 0 then 1 else 0

noncomputable def ev (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl ((val (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 0)

noncomputable def eu (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (euq (tokAt w j)) (p.E (tokAt w j) 1)

noncomputable def Sw (fl : ℝ → ℝ) (p : Pert) : ℝ := sw fl 17 (p.A 0 0 3 4)
noncomputable def Cw (fl : ℝ → ℝ) (p : Pert) : ℝ := sw fl (-40) (p.A 0 0 5 1)
noncomputable def Tw (fl : ℝ → ℝ) (p : Pert) : ℝ := sw fl 1 (p.V 0 0 2 0)
noncomputable def Ow (fl : ℝ → ℝ) (p : Pert) : ℝ := sw fl 1 (p.oW 2)
noncomputable def Fn (fl : ℝ → ℝ) (w : List ℕ) : ℝ := fl ((w.length + 1 : ℕ) : ℝ)

theorem val_le (t : ℕ) : val t ≤ 3 := by
  unfold val
  split_ifs <;> omega

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem target_succ (w : List ℕ) (m : ℕ) (hm : m < w.length) :
    target w (m + 1) = if val (tokAt w (m + 1)) = 0 then target w m else val (tokAt w (m + 1)) := by
  unfold target lastv
  simp [List.take_succ, List.foldl_append, Lane4.Seq.tokAt_succ w m hm, List.getElem?_eq_getElem hm]

theorem last_struct (w : List ℕ) : ∀ i, i ≤ w.length →
    ((∀ k, k ≤ i → val (tokAt w k) = 0) ∧ target w i = 0) ∨
    (∃ j, j ≤ i ∧ val (tokAt w j) ≠ 0 ∧ (∀ k, j < k → k ≤ i → val (tokAt w k) = 0) ∧
      target w i = val (tokAt w j)) := by
  intro i
  induction i with
  | zero =>
    intro _
    left
    refine ⟨fun k hk => ?_, ?_⟩
    · have : k = 0 := by omega
      subst this
      simp [Lane4.Seq.tokAt_zero, val]
    · simp [target, lastv]
  | succ m ih =>
    intro hm
    have ih' := ih (by omega)
    have hts := target_succ w m (by omega)
    by_cases hv : val (tokAt w (m + 1)) = 0
    · rw [if_pos hv] at hts
      rcases ih' with ⟨h1, h2⟩ | ⟨j, hj, hjm, hj2, hj3⟩
      · left
        refine ⟨fun k hk => ?_, by rw [hts, h2]⟩
        by_cases hkm : k ≤ m
        · exact h1 k hkm
        · have : k = m + 1 := by omega
          subst this
          exact hv
      · right
        refine ⟨j, by omega, hjm, fun k hjk hk => ?_, by rw [hts, hj3]⟩
        by_cases hkm : k ≤ m
        · exact hj2 k hjk hkm
        · have : k = m + 1 := by omega
          subst this
          exact hv
    · rw [if_neg hv] at hts
      right
      exact ⟨m + 1, le_rfl, hv, fun k hk hk2 => by omega, hts⟩

theorem init_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [ev fl p w j, eu fl p w j, 0] ++ pos fl j (w.length + 1) := by
  have h6 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 ∨
      tokAt w j = 5 := by
    have := tok_le w hw j
    omega
  rcases h6 with h | h | h | h | h | h <;>
    simp [TNet.init, net, ev, eu, euq, val, swRow, h, sw_zero hr]

theorem ev_zero {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ) (k : ℕ)
    (h : val (tokAt w k) = 0) : ev fl p w k = 0 := by
  unfold ev
  have : ((val (tokAt w k) : ℕ) : ℚ) = 0 := by rw [h]; simp
  rw [this]
  exact sw_zero hr _

theorem ev_near {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (p : Pert)
    (hp : p.Within (1 / 200)) (hM : 6 ≤ M) (hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199)
    (w : List ℕ) (k : ℕ) :
    |ev fl p w k - ((val (tokAt w k) : ℕ) : ℝ)| ≤ 3 / 199 + η := by
  have hv : val (tokAt w k) ≤ 3 := val_le _
  have hvr : ((val (tokAt w k) : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hv
  have hv0 : (0 : ℝ) ≤ ((val (tokAt w k) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hc : (((val (tokAt w k) : ℕ) : ℚ) : ℝ) = ((val (tokAt w k) : ℕ) : ℝ) := by norm_num
  have h := sw_near hr hu0 ((val (tokAt w k) : ℕ) : ℚ) (hp.E (tokAt w k) 0) (by norm_num)
    (by rw [hc, abs_of_nonneg hv0]; linarith) hε
  rw [hc, abs_of_nonneg hv0] at h
  unfold ev
  have : (1 : ℝ) / 199 * ((val (tokAt w k) : ℕ) : ℝ) ≤ 3 / 199 := by linarith
  linarith

theorem eu_prop {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (p : Pert)
    (hp : p.Within (1 / 200)) (hM : 6 ≤ M) (hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199)
    (w : List ℕ) (k : ℕ) :
    (val (tokAt w k) ≠ 0 → eu fl p w k = 0) ∧
    (val (tokAt w k) = 0 → |eu fl p w k - 1| ≤ 1 / 199 + η) := by
  constructor
  · intro h
    unfold eu
    have : euq (tokAt w k) = 0 := by simp [euq, h]
    rw [this]
    exact sw_zero hr _
  · intro h
    unfold eu
    have h1 : euq (tokAt w k) = 1 := by simp [euq, h]
    rw [h1]
    have c1 : ((1 : ℚ) : ℝ) = 1 := by norm_num
    have hh := sw_near hr hu0 1 (hp.E (tokAt w k) 1) (by norm_num)
      (by rw [c1, abs_one]; linarith) hε
    rw [c1, abs_one] at hh
    linarith

theorem score_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    {a1 b1 c1 qi qn a2 b2 c2 qk qn2 : ℝ}
    (hI1 : fl (fl (sw fl 17 (dA 3 4) * qk)) = fl (sw fl 17 (dA 3 4) * qk))
    (hI2 : fl (fl (sw fl (-40) (dA 5 1) * b2)) = fl (sw fl (-40) (dA 5 1) * b2)) :
    hd.score fl dA [a1, b1, c1, 1, qi, qn] [a2, b2, c2, 1, qk, qn2]
      = fl (fl (sw fl 17 (dA 3 4) * qk) + fl (qn * fl (sw fl (-40) (dA 5 1) * b2))) := by
  simp [Head.score, hd, z6, pdot, rmat, rdot, sw_zero hr, hr.zero, hI1, hI2]

theorem val_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ) (a b c qk qn : ℝ)
    (hI : fl (fl (sw fl 1 (dV 0) * a)) = fl (sw fl 1 (dV 0) * a)) :
    rdot fl [1, 0, 0, 0, 0, 0] [a, b, c, 1, qk, qn] dV 0 0 = fl (sw fl 1 (dV 0) * a) := by
  simp [rdot, sw_zero hr, hr.zero, hI]

theorem zrow_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ) (a b c d e f : ℝ) :
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

theorem chain {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 10 ^ 40) (hM : 100 ≤ M) (T O e v A : ℝ)
    (hT : |T - 1| ≤ 1 / 199 + η) (hO : |O - 1| ≤ 1 / 199 + η) (hE : |e - v| ≤ 3 / 199 + η)
    (hv0 : 0 ≤ v) (hv3 : v ≤ 3) (hTE : |T * e| ≤ 4)
    (hA : |A - fl (T * e)| ≤ 5 / 100 + 1 / 2 ^ 90) : |fl (O * A) - v| ≤ 1 / 4 := by
  have h2 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 100000 := by norm_num
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hu2 : u ≤ 1 / 100000 := le_trans hu1 (by norm_num)
  have ha : 1 / 199 + η ≤ 1 / 190 := by linarith
  have hb : 3 / 199 + η ≤ 1 / 60 := by linarith
  have hb0 : 0 ≤ 3 / 199 + η := le_trans (abs_nonneg _) hE
  have hvabs : |v| ≤ 3 := by rw [abs_of_nonneg hv0]; exact hv3
  have e1 := mul_near hT hE
  rw [one_mul, abs_one] at e1
  have m1 : (1 / 199 + η) * |v| ≤ 1 / 190 * 3 := mul_le_mul ha hvabs (abs_nonneg _) (by norm_num)
  have m2 : (1 / 199 + η) * (3 / 199 + η) ≤ 1 / 190 * (1 / 60) :=
    mul_le_mul ha hb hb0 (by norm_num)
  have e1' : |T * e - v| ≤ 1 / 20 := by linarith
  have e2 := hr.near hu0 e1' hTE (by linarith : (4 : ℝ) ≤ M)
  have e3 := abs_sub_le A (fl (T * e)) v
  have hX : |A - v| ≤ 12 / 100 := by linarith
  have hFb := hr.bound hu0 hTE (by linarith : (4 : ℝ) ≤ M)
  have hAb : |A| ≤ 6 := by
    have := abs_sub_abs_le_abs_sub A (fl (T * e))
    linarith
  have hO1 : |O| ≤ 11 / 10 := by
    obtain ⟨hO1, hO2⟩ := abs_le.mp hO
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hOA : |O * A| ≤ 7 := by
    rw [abs_mul]
    have := mul_le_mul hO1 hAb (abs_nonneg _) (by norm_num)
    linarith
  have e4 := mul_near hO hX
  rw [one_mul, abs_one] at e4
  have m3 : (1 / 199 + η) * (12 / 100) ≤ 1 / 190 * (12 / 100) :=
    mul_le_mul_of_nonneg_right ha (by norm_num)
  have e4' : |O * A - v| ≤ 1 / 5 := by linarith
  have e5 := hr.near hu0 e4' hOA (by linarith : (7 : ℝ) ≤ M)
  linarith

set_option maxHeartbeats 3200000 in
theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη p hp w hw hn hnη hM i hi1 hi
  have hn1 : 1 ≤ w.length + 1 := by omega
  have hnR : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hn1
  have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
    have := range_lin hM hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have h18 : 18 * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  have h43 : 43 * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  have h63 : 63 * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  have h128 : 128 * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  have h100 : (100 : ℝ) ≤ M := range_const hM hn1 (by norm_num)
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by linarith
  have hM6 : (6 : ℝ) ≤ M := by linarith
  have hun18 : u * (18 * ((w.length + 1 : ℕ) : ℝ)) = 18 * (u * ((w.length + 1 : ℕ) : ℝ)) := by ring
  have hun43 : u * (43 * ((w.length + 1 : ℕ) : ℝ)) = 43 * (u * ((w.length + 1 : ℕ) : ℝ)) := by ring
  have hun63 : u * (63 * ((w.length + 1 : ℕ) : ℝ)) = 63 * (u * ((w.length + 1 : ℕ) : ℝ)) := by ring
  -- stored weights
  have c17 : ((17 : ℚ) : ℝ) = 17 := by norm_num
  have c1 : ((1 : ℚ) : ℝ) = 1 := by norm_num
  have c40 : (((-40 : ℚ)) : ℝ) = -40 := by norm_num
  have hab40 : |(-40 : ℝ)| = 40 := by norm_num
  have hS : |Sw fl p - 17| ≤ 1 / 199 * 17 + η := by
    have h := sw_near hr hu0 17 (hp.A 0 0 3 4) (by norm_num)
      (by rw [c17, abs_of_nonneg (by norm_num)]; linarith) hε
    rw [c17, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 17)] at h
    exact h
  have hC : |Cw fl p - (-40)| ≤ 1 / 199 * 40 + η := by
    have h := sw_near hr hu0 (-40) (hp.A 0 0 5 1) (by norm_num)
      (by rw [c40, hab40]; linarith) hε
    rw [c40, hab40] at h
    exact h
  have hT : |Tw fl p - 1| ≤ 1 / 199 * 1 + η := by
    have h := sw_near hr hu0 1 (hp.V 0 0 2 0) (by norm_num)
      (by rw [c1, abs_of_nonneg (by norm_num)]; linarith) hε
    rw [c1, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)] at h
    exact h
  have hO : |Ow fl p - 1| ≤ 1 / 199 * 1 + η := by
    have h := sw_near hr hu0 1 (hp.oW 2) (by norm_num)
      (by rw [c1, abs_of_nonneg (by norm_num)]; linarith) hε
    rw [c1, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)] at h
    exact h
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  obtain ⟨hC1, hC2⟩ := abs_le.mp hC
  have hSlo : (169 : ℝ) / 10 ≤ Sw fl p := by linarith
  have hShi : Sw fl p ≤ 171 / 10 := by linarith
  have hClo : (-4021 : ℝ) / 100 ≤ Cw fl p := by linarith
  have hChi : Cw fl p ≤ -3979 / 100 := by linarith
  -- embedding values
  have hE : ∀ k : ℕ, |ev fl p w k - ((val (tokAt w k) : ℕ) : ℝ)| ≤ 3 / 199 + η :=
    fun k => ev_near hr hu0 p hp hM6 hε w k
  have hEuB : ∀ k : ℕ, 0 ≤ eu fl p w k ∧ eu fl p w k ≤ 1006 / 1000 := by
    intro k
    by_cases hm : val (tokAt w k) = 0
    · have h := ((eu_prop hr hu0 p hp hM6 hε w k).2 hm)
      obtain ⟨h1, h2⟩ := abs_le.mp h
      constructor <;> linarith
    · rw [(eu_prop hr hu0 p hp hM6 hε w k).1 hm]
      constructor <;> norm_num
  have hEuL : ∀ k : ℕ, val (tokAt w k) = 0 → 99 / 100 ≤ eu fl p w k := by
    intro k hm
    have h := ((eu_prop hr hu0 p hp hM6 hε w k).2 hm)
    obtain ⟨h1, h2⟩ := abs_le.mp h
    linarith
  have hCe : ∀ k : ℕ, |Cw fl p * eu fl p w k| ≤ 41 := by
    intro k
    obtain ⟨h0, h1⟩ := hEuB k
    have m1 := mul_le_mul_of_nonneg_right hClo h0
    have m2 := mul_le_mul_of_nonneg_right hChi h0
    rw [abs_le]
    constructor <;> linarith
  have h41 : (41 : ℝ) ≤ M := by linarith
  -- positions
  have hfn := hr.pos_near hu0 hη (le_refl (w.length + 1)) hn hnM
  have hfn0 := hr.pos_le hu0 hη (le_refl (w.length + 1)) hn hnM
  have hFnE : Fn fl w = fl ((w.length + 1 : ℕ) : ℝ) := rfl
  obtain ⟨hfn1, hfn2⟩ := abs_le.mp hfn
  have hFn0 : 0 ≤ Fn fl w := hfn0.1
  have hFnlo : ((w.length + 1 : ℕ) : ℝ) - 1 / 200 ≤ Fn fl w := by linarith
  have hFnhi : Fn fl w ≤ ((w.length + 1 : ℕ) : ℝ) + 1 / 100 := hfn0.2
  -- scores
  have hPb : ∀ k : ℕ, k ≤ w.length + 1 →
      |Sw fl p * fl (k : ℝ)| ≤ 18 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    obtain ⟨hk0, hk1⟩ := hr.pos_le hu0 hη hk hn hnM
    have hS0 : 0 ≤ Sw fl p := by linarith
    rw [abs_of_nonneg (mul_nonneg hS0 hk0)]
    have := mul_le_mul hShi hk1 hk0 (by norm_num)
    linarith
  have hsk : ∀ k : ℕ, k ≤ w.length + 1 →
      hscore hd fl (p.A 0 0) (net.init fl p w) i k
        = fl (fl (Sw fl p * fl (k : ℝ)) + fl (Fn fl w * fl (Cw fl p * eu fl p w k))) := by
    intro k hk
    simp only [hscore, init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact score_eq hr (p.A 0 0) (hr.idem _ (le_trans (hPb k hk) h18))
      (hr.idem _ (le_trans (hCe k) h41))
  have hsk_m : ∀ k : ℕ, k ≤ w.length + 1 → val (tokAt w k) ≠ 0 →
      hscore hd fl (p.A 0 0) (net.init fl p w) i k = fl (Sw fl p * fl (k : ℝ)) := by
    intro k hk hm
    have hI := hr.idem _ (le_trans (hPb k hk) h18)
    rw [hsk k hk, (eu_prop hr hu0 p hp hM6 hε w k).1 hm]
    simp [hr.zero, hI]
  have hP19 : ∀ k : ℕ, k ≤ w.length + 1 →
      |fl (Sw fl p * fl (k : ℝ))| ≤ 19 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    have := hr.bound hu0 (hPb k hk) h18
    linarith
  have hR : ∀ k : ℕ, |fl (Cw fl p * eu fl p w k)| ≤ 42 := by
    intro k
    have := hr.bound hu0 (hCe k) h41
    linarith
  have hx43 : ∀ k : ℕ, |Fn fl w * fl (Cw fl p * eu fl p w k)|
      ≤ 43 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k
    rw [abs_mul, abs_of_nonneg hFn0]
    have := mul_le_mul hFnhi (hR k) (abs_nonneg _) (by linarith)
    linarith
  have hQ44 : ∀ k : ℕ, |fl (Fn fl w * fl (Cw fl p * eu fl p w k))|
      ≤ 44 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k
    have := hr.bound hu0 (hx43 k) h43
    linarith
  have hsum : ∀ k : ℕ, k ≤ w.length + 1 →
      |fl (Sw fl p * fl (k : ℝ)) + fl (Fn fl w * fl (Cw fl p * eu fl p w k))|
        ≤ 63 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    have h1 := abs_add_le (fl (Sw fl p * fl (k : ℝ))) (fl (Fn fl w * fl (Cw fl p * eu fl p w k)))
    have := hP19 k hk
    have := hQ44 k
    linarith
  have hQu : ∀ k : ℕ, val (tokAt w k) = 0 →
      fl (Fn fl w * fl (Cw fl p * eu fl p w k)) ≤ -392 / 10 * ((w.length + 1 : ℕ) : ℝ) + 4 / 10 := by
    intro k hm
    have heL := hEuL k hm
    obtain ⟨h0, h1⟩ := hEuB k
    have m2 := mul_le_mul_of_nonneg_right hChi h0
    have hCE : Cw fl p * eu fl p w k ≤ -393 / 10 := by linarith
    have hRu := hr.upper hu0 (hCe k) h41
    have hR2 : fl (Cw fl p * eu fl p w k) ≤ -392 / 10 := by linarith
    have hx := mul_le_mul_of_nonneg_left hR2 hFn0
    have hQup := hr.upper hu0 (hx43 k) h43
    linarith
  -- values
  have hTEb : ∀ k : ℕ, |Tw fl p * ev fl p w k| ≤ 4 := by
    intro k
    have hv : val (tokAt w k) ≤ 3 := val_le _
    have hvr : ((val (tokAt w k) : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hv
    have hv0 : (0 : ℝ) ≤ ((val (tokAt w k) : ℕ) : ℝ) := Nat.cast_nonneg _
    obtain ⟨hT1, hT2⟩ := abs_le.mp hT
    obtain ⟨hE1, hE2⟩ := abs_le.mp (hE k)
    rw [abs_mul]
    have h1 : |Tw fl p| ≤ 11 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |ev fl p w k| ≤ 31 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
    have := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    linarith
  have hfk : ∀ k : ℕ, rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 2) 0 0
      = fl (Tw fl p * ev fl p w k) := by
    intro k
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact val_eq hr _ _ _ _ _ _ (hr.idem _ (le_trans (hTEb k) (by linarith)))
  have hfB : ∀ k ∈ cand Mask.causal (w.length + 1) i,
      |(fun j => rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 2) 0 0) k| ≤ 5 := by
    intro k _
    show |rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 2) 0 0| ≤ 5
    rw [hfk k]
    have := hr.bound hu0 (hTEb k) (by linarith : (4 : ℝ) ≤ M)
    linarith
  have hat := attn_eq (ex := ex) hr p w hw i
  rcases last_struct w i hi with ⟨hz, htg⟩ | ⟨j, hji, hjm, hjafter, htg⟩
  · -- no marked token
    have hf0 : ∀ k ∈ cand Mask.causal (w.length + 1) i,
        (fun j => rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 2) 0 0) k = 0 := by
      intro k hk
      rw [Lane4.Seq.mem_cand_causal] at hk
      show rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 2) 0 0 = 0
      rw [hfk k, ev_zero hr p w k (hz k hk)]
      simp [hr.zero]
    have hsav := soft_zeros (ex := ex) hr
      (s := hscore hd fl (p.A 0 0) (net.init fl p w) i) hf0
    rw [hsav] at hat
    have hout := out_eq hr p w hw i 0 hat hr.zero (by simp [hr.zero])
    rw [hout, htg]
    norm_num [hr.zero]
  · -- last marked token j
    have hjn : j ≤ w.length + 1 := by omega
    have hj : j ∈ cand Mask.causal (w.length + 1) i := by
      rw [Lane4.Seq.mem_cand_causal]; omega
    have hlen : (cand Mask.causal (w.length + 1) i).length ≤ w.length + 1 := by
      simp [cand]; omega
    have hgap : ∀ k ∈ cand Mask.causal (w.length + 1) i, k ≠ j →
        hscore hd fl (p.A 0 0) (net.init fl p w) i k
          ≤ hscore hd fl (p.A 0 0) (net.init fl p w) i j - 16 * (ndist j k : ℝ) := by
      intro k hk hne
      rw [Lane4.Seq.mem_cand_causal] at hk
      have hkn : k ≤ w.length + 1 := by omega
      rw [hsk_m j hjn hjm, ndist_cast]
      have hgp := hr.gap hu0 (hPb k hkn) (hPb j hjn) h18
      have hSnn : 0 ≤ Sw fl p := by linarith
      by_cases hmk : val (tokAt w k) = 0
      · -- unmarked competitor
        have hsum' := hsum k hkn
        have hup := hr.upper hu0 hsum' h63
        have hQk := hQu k hmk
        rw [hsk k hkn]
        have hjk : (j : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hjn
        have hkk : (k : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hkn
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · -- k < j
          have hkjR : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hlt
          have hg := hr.pos_gap hu0 hη (le_of_lt hlt) hjn hn hnM
          have hD0 : 0 ≤ fl (j : ℝ) - fl (k : ℝ) := by linarith
          have hSD := mul_nonneg hSnn hD0
          rw [abs_of_nonneg (by linarith)]
          linarith [hgp, hSD, hup, hQk, hun18, hun63, hn, hηs, hηs']
        · -- j < k
          have hkjR : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hgt
          have hg := hr.pos_gap hu0 hη (le_of_lt hgt) hkn hn hnM
          have hnj := hr.pos_near hu0 hη hjn hn hnM
          have hnk := hr.pos_near hu0 hη hkn hn hnM
          obtain ⟨hnj1, hnj2⟩ := abs_le.mp hnj
          obtain ⟨hnk1, hnk2⟩ := abs_le.mp hnk
          have hD0 : 0 ≤ fl (k : ℝ) - fl (j : ℝ) := by linarith
          have hSD := mul_le_mul_of_nonneg_right hShi hD0
          rw [abs_of_nonpos (by linarith)]
          linarith [hgp, hSD, hup, hQk, hun18, hun63, hn, hηs, hηs']
      · -- marked competitor: k < j
        have hkj : k < j := by
          rcases lt_trichotomy k j with h | h | h
          · exact h
          · exact absurd h hne
          · exact absurd (hjafter k h (by omega)) hmk
        rw [hsk_m k hkn hmk]
        have hkjR : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hkj
        have hg := hr.pos_gap hu0 hη (le_of_lt hkj) hjn hn hnM
        have hD0 : 0 ≤ fl (j : ℝ) - fl (k : ℝ) := by linarith
        have hSD := mul_le_mul_of_nonneg_right hSlo hD0
        rw [abs_of_nonneg (by linarith)]
        linarith [hgp, hSD, hg, hkjR, hun18, hn, hηs, hηs']
    have hSb : ∀ k ∈ cand Mask.causal (w.length + 1) i,
        |hscore hd fl (p.A 0 0) (net.init fl p w) i k| ≤ 64 * ((w.length + 1 : ℕ) : ℝ) := by
      intro k hk
      rw [Lane4.Seq.mem_cand_causal] at hk
      rw [hsk k (by omega)]
      have := hr.bound hu0 (hsum k (by omega)) h63
      linarith
    obtain ⟨hA1, hA2⟩ := soft_near hr he hu0 hu1 hη0 hη (Lane4.Seq.cand_nodup _ _ _) hlen hn hnη
      hj hgap hSb (by linarith) hfB (by linarith)
    have hA1' : |savg fl ex (cand Mask.causal (w.length + 1) i)
        (hscore hd fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 2) 0 0)
        - fl (Tw fl p * ev fl p w j)| ≤ 5 / 100 + 1 / 2 ^ 90 := by
      have := hA1
      simp only [hfk j] at this
      exact this
    have hAb : |savg fl ex (cand Mask.causal (w.length + 1) i)
        (hscore hd fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 2) 0 0)| ≤ 6 := by
      have h1 := hr.bound hu0 (hTEb j) (by linarith : (4 : ℝ) ≤ M)
      have h2 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 100 := by norm_num
      have h3 := abs_sub_abs_le_abs_sub
        (savg fl ex (cand Mask.causal (w.length + 1) i)
          (hscore hd fl (p.A 0 0) (net.init fl p w) i)
          (fun j => rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 2) 0 0))
        (fl (Tw fl p * ev fl p w j))
      linarith
    have hOAb : |sw fl 1 (p.oW 2) * savg fl ex (cand Mask.causal (w.length + 1) i)
        (hscore hd fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 2) 0 0)| ≤ 7 := by
      obtain ⟨hO1, hO2⟩ := abs_le.mp hO
      rw [abs_mul]
      have h1 : |Ow fl p| ≤ 11 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
      have := mul_le_mul h1 hAb (abs_nonneg _) (by norm_num)
      have h2 : |sw fl 1 (p.oW 2)| = |Ow fl p| := rfl
      linarith
    rw [out_eq hr p w hw i _ hat hA2 (hr.idem _ (le_trans hOAb (by linarith)))]
    rw [htg]
    have hv : val (tokAt w j) ≤ 3 := val_le _
    have hvr : ((val (tokAt w j) : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hv
    have hv0 : (0 : ℝ) ≤ ((val (tokAt w j) : ℕ) : ℝ) := Nat.cast_nonneg _
    exact chain hr hu0 hu1 hηs h100 (Tw fl p) (Ow fl p) (ev fl p w j)
      ((val (tokAt w j) : ℕ) : ℝ) _ (by linarith) (by linarith) (hE j) hv0 hvr (hTEb j) hA1'

end Lane4.Case
