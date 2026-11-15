set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option maxHeartbeats 1600000

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

def z8 : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0]

/-- State: [c, p, dg, res, prod, 1, fl i, fl n].  Score = 20 * pos(key) - 50 * n * p(key). -/
def hd : Head :=
  { A := [z8, z8, z8, z8, z8, [0, 0, 0, 0, 0, 0, 20, 0], z8, [0, -50, 0, 0, 0, 0, 0, 0]],
    V := [z8, z8, z8, [1, 0, 0, 0, 0, 0, 0, 0], z8, z8, z8, z8],
    mask := Mask.strict }

def blk : Block :=
  { heads := [hd],
    W1 := [[0, -15 / 4, 0, 15 / 4, 0, 0, 0, 0]],
    b1 := [-3 / 4],
    W2 := [[0], [0], [0], [0], [1], [0], [0], [0]],
    b2 := z8 }

def net : TNet :=
  { embed := [[0, 0, 0, 0, 0], [0, 1, 1, 0, 0], [0, 1, 1, 0, 0], [0, 0, 2, 0, 0],
              [0, 1, 0, 0, 0], [1, 0, 2, 0, 0]],
    blocks := [blk],
    outW := [0, 0, 1, 1, -1, 0, 0, 0],
    outB := 0 }

noncomputable def ec (fl : ℝ → ℝ) (p : Pert) (t : ℕ) : ℝ :=
  sw fl (if t = 5 then 1 else 0) (p.E t 0)
noncomputable def ep (fl : ℝ → ℝ) (p : Pert) (t : ℕ) : ℝ :=
  sw fl (if t = 1 ∨ t = 2 ∨ t = 4 then 1 else 0) (p.E t 1)
noncomputable def eg (fl : ℝ → ℝ) (p : Pert) (t : ℕ) : ℝ :=
  sw fl ((dg t : ℕ) : ℚ) (p.E t 2)

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [ec fl p (tokAt w j), ep fl p (tokAt w j), eg fl p (tokAt w j), 0, 0]
      ++ pos fl j (w.length + 1) := by
  have h6 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4
      ∨ tokAt w j = 5 := by
    have := tok_le w hw j
    omega
  rcases h6 with h | h | h | h | h | h <;>
    simp [TNet.init, net, ec, ep, eg, swRow, h, sw_zero hr, dg]

theorem score_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (a0 a1 a2 a3 a4 qi qn c0 p0 g0 r0 q0 qk qn' : ℝ)
    (hI1 : fl (fl (sw fl 20 (dA 5 6) * qk)) = fl (sw fl 20 (dA 5 6) * qk))
    (hI2 : fl (fl (sw fl (-50) (dA 7 1) * p0)) = fl (sw fl (-50) (dA 7 1) * p0)) :
    hd.score fl dA [a0, a1, a2, a3, a4, 1, qi, qn] [c0, p0, g0, r0, q0, 1, qk, qn']
      = fl (fl (sw fl 20 (dA 5 6) * qk) + fl (qn * fl (sw fl (-50) (dA 7 1) * p0))) := by
  simp [Head.score, hd, z8, pdot, rmat, rdot, sw_zero hr, hr.zero, hI1, hI2]

theorem val_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ)
    (c0 p0 g0 r0 q0 qk qn : ℝ)
    (hI : fl (fl (sw fl 1 (dV 0) * c0)) = fl (sw fl 1 (dV 0) * c0)) :
    rdot fl [1, 0, 0, 0, 0, 0, 0, 0] [c0, p0, g0, r0, q0, 1, qk, qn] dV 0 0
      = fl (sw fl 1 (dV 0) * c0) := by
  simp [rdot, sw_zero hr, hr.zero, hI]

theorem zrow_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ)
    (a b c d e f g h : ℝ) :
    rdot fl z8 [a, b, c, d, e, f, g, h] dV 0 0 = 0 := by
  simp [z8, rdot, sw_zero hr, hr.zero]

theorem attn_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) :
    sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, 0, savg fl ex (cand Mask.strict (w.length + 1) i)
              (hscore hd fl (p.A 0 0) (net.init fl p w) i)
              (fun j => rdot fl [1, 0, 0, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 3) 0 0),
         0, 0, 0, 0] := by
  have hV : hd.V = [z8, z8, z8, [1, 0, 0, 0, 0, 0, 0, 0], z8, z8, z8, z8] := rfl
  have hm : hd.mask = Mask.strict := rfl
  have hz : ∀ d : ℕ → ℝ,
      savg fl ex (cand Mask.strict (w.length + 1) i)
        (hscore hd fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl z8 (net.init fl p w j) d 0 0) = 0 := by
    intro d
    apply soft_zeros hr
    intro k _
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact zrow_eq hr d _ _ _ _ _ _ _ _
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz]

/-- The output in closed form. -/
theorem out_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) (A P R Bv W D C Q Zv pv g : ℝ)
    (hattn : sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, 0, A, 0, 0, 0, 0])
    (hA : fl A = A)
    (hpvd : pv = ep fl p (tokAt w i)) (hgd : g = eg fl p (tokAt w i))
    (hg : fl g = g) (hpv : fl pv = pv)
    (hP : P = sw fl (-15 / 4) (p.W1 0 0 1)) (hR : R = sw fl (15 / 4) (p.W1 0 0 3))
    (hB : Bv = sw fl (-3 / 4) (p.b1 0 0)) (hW : W = sw fl 1 (p.W2 0 4 0))
    (hD : D = sw fl 1 (p.oW 2)) (hC : C = sw fl 1 (p.oW 3)) (hQ : Q = sw fl (-1) (p.oW 4))
    (hZ : Zv = fl (fl (fl (P * pv) + fl (R * A)) + Bv))
    (hIP : fl (fl (P * pv)) = fl (P * pv))
    (hIS : fl (fl (fl (P * pv) + fl (R * A))) = fl (fl (P * pv) + fl (R * A)))
    (hIW : fl (fl (W * relu Zv)) = fl (W * relu Zv))
    (hID : fl (fl (D * g)) = fl (D * g))
    (hIO : fl (fl (fl (fl (D * g) + fl (C * A)) + fl (Q * fl (W * relu Zv))))
        = fl (fl (fl (D * g) + fl (C * A)) + fl (Q * fl (W * relu Zv)))) :
    sout net fl ex p w i
      = fl (fl (fl (D * g) + fl (C * A)) + fl (Q * fl (W * relu Zv))) := by
  subst hP hR hB hW hD hC hQ hZ hpvd hgd
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 0, 1, 1, -1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  unfold sout srun
  rw [hb, ho, hc]
  simp only [srunFrom, sblock, blk, sheadsApply, hattn]
  simp only [init_eq hr p w hw]
  simp [z8, pos, rdot, radd, raffine, sw_zero hr, hr.zero, hr.one, hA, hg, hpv, hIP, hIS, hIW,
    hID, hIO]

theorem fl_near {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 2 ^ 149) (hM : 10 ≤ M) {x t e B : ℝ} (hx : |x - t| ≤ e) (ht : |t| ≤ B)
    (hB : B + e ≤ 10) : |fl x - t| ≤ e + 1 / 100000 := by
  have h1 : |x| ≤ 10 := by
    have := abs_sub_abs_le_abs_sub x t
    linarith
  have h2 := hr.near hu0 hx h1 hM
  have h3 : u * 10 ≤ 10 / 2 ^ 24 := by
    have := mul_le_mul_of_nonneg_right hu (by norm_num : (0 : ℝ) ≤ 10)
    linarith
  have h4 : (10 : ℝ) / 2 ^ 24 ≤ 1 / 200000 := by norm_num
  have h5 := eta_tiny hη
  have h6 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 200000 := by norm_num
  linarith

theorem add_near {x y s t a b : ℝ} (hx : |x - s| ≤ a) (hy : |y - t| ≤ b) :
    |x + y - (s + t)| ≤ a + b := by
  have h1 := abs_add_le (x - s) (y - t)
  have h2 : x + y - (s + t) = (x - s) + (y - t) := by ring
  rw [h2]
  linarith

theorem swr {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 2 ^ 149) (q : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 200) (x b : ℝ) (hx : (q : ℝ) = x)
    (hq : x = 0 ∨ 3 / 4 ≤ |x|) (hxb : |x| ≤ 100) (hM : 200 ≤ M) (hb : |x| / 190 ≤ b) :
    |sw fl q d - x| ≤ b := by
  rcases hq with h0 | h1
  · have hq0 : q = 0 := by exact_mod_cast hx.trans h0
    subst hq0
    have hb0 : 0 ≤ b := le_trans (by positivity) hb
    rw [sw_zero hr, h0]
    simpa using hb0
  · have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by
      have h : (1 : ℝ) / 2 ^ 24 = 1 / 16777216 := by norm_num
      have : u ≤ 1 / 16777216 := by linarith
      linarith
    have hqM : 2 * |(q : ℝ)| ≤ M := by rw [hx]; linarith
    have h := sw_near hr hu0 q hd (by norm_num) hqM hε
    rw [hx] at h
    have hη' := eta_tiny hη
    have h1' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 10000 := by norm_num
    linarith

theorem dg_le (t : ℕ) : dg t ≤ 2 := by
  unfold dg
  split_ifs <;> omega

theorem ec_b {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 2 ^ 149) (hM : 200 ≤ M) (p : Pert) (hp : p.Within (1 / 200)) (t : ℕ) :
    (t = 5 → |ec fl p t - 1| ≤ 1 / 190) ∧ (t ≠ 5 → ec fl p t = 0) := by
  constructor
  · intro h
    subst h
    have := swr hr hu0 hu hη 1 (hp.E 5 0) 1 (1 / 190) (by norm_num) (Or.inr (by norm_num))
      (by norm_num) hM (by norm_num)
    simpa [ec] using this
  · intro h
    simp [ec, h, sw_zero hr]

theorem ep_b {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 2 ^ 149) (hM : 200 ≤ M) (p : Pert) (hp : p.Within (1 / 200)) (t : ℕ) :
    ((t = 1 ∨ t = 2 ∨ t = 4) → |ep fl p t - 1| ≤ 1 / 190) ∧
    (¬ (t = 1 ∨ t = 2 ∨ t = 4) → ep fl p t = 0) := by
  constructor
  · intro h
    have := swr hr hu0 hu hη 1 (hp.E t 1) 1 (1 / 190) (by norm_num) (Or.inr (by norm_num))
      (by norm_num) hM (by norm_num)
    simpa [ep, h] using this
  · intro h
    simp [ep, h, sw_zero hr]

theorem eg_b {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 2 ^ 149) (hM : 200 ≤ M) (p : Pert) (hp : p.Within (1 / 200)) (t : ℕ) :
    |eg fl p t - (dg t : ℝ)| ≤ 2 / 190 := by
  have h2 := dg_le t
  have h2r : (dg t : ℝ) ≤ 2 := by exact_mod_cast h2
  have h0r : (0 : ℝ) ≤ (dg t : ℝ) := Nat.cast_nonneg _
  have hx : (((dg t : ℕ) : ℚ) : ℝ) = (dg t : ℝ) := by simp
  have hq : (dg t : ℝ) = 0 ∨ 3 / 4 ≤ |(dg t : ℝ)| := by
    rcases Nat.eq_zero_or_pos (dg t) with h | h
    · left
      simp [h]
    · right
      rw [abs_of_nonneg h0r]
      have : (1 : ℝ) ≤ (dg t : ℝ) := by exact_mod_cast h
      linarith
  have := swr hr hu0 hu hη ((dg t : ℕ) : ℚ) (hp.E t 2) (dg t : ℝ) (2 / 190) hx hq
    (by rw [abs_of_nonneg h0r]; linarith) hM (by rw [abs_of_nonneg h0r]; linarith)
  exact this

theorem fpos {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hη : η ≤ 1 / 2 ^ 149)
    {n : ℕ} (hun : u * (n : ℝ) ≤ 1 / 256) (hnM : (n : ℝ) ≤ M) {k : ℕ} (hk : k ≤ n) :
    0 ≤ fl (k : ℝ) ∧ |fl (k : ℝ) - k| ≤ 1 / 200 :=
  ⟨(hr.pos_le hu0 hη hk hun hnM).1, hr.pos_near hu0 hη hk hun hnM⟩

theorem sc_b5 {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hη : η ≤ 1 / 2 ^ 149)
    {n : ℕ} (hn2 : 2 ≤ n) (hun : u * (n : ℝ) ≤ 1 / 256) (hM : 2 ^ 40 * (n : ℝ) ^ 2 ≤ M)
    {S : ℝ} (hS1 : 1989 / 100 ≤ S) (hS2 : S ≤ 2011 / 100) {k : ℕ} (hk : k ≤ n) :
    |S * fl (k : ℝ)| ≤ 202 / 10 * n ∧ |fl (S * fl (k : ℝ)) - S * fl (k : ℝ)| ≤ 8 / 100 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnM : (n : ℝ) ≤ M := by
    have := range_lin hM hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  obtain ⟨h0, h1⟩ := fpos hr hu0 hη hun hnM hk
  have h1' := (abs_le.mp h1).2
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hb : |S * fl (k : ℝ)| ≤ 202 / 10 * n := by
    rw [abs_of_nonneg (mul_nonneg (by linarith) h0)]
    have := mul_le_mul hS2 (show fl (k : ℝ) ≤ n + 1 / 200 by linarith) h0 (by norm_num)
    linarith
  refine ⟨hb, ?_⟩
  have hBM : 202 / 10 * (n : ℝ) ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  have h2 := hr.abs hu0 hb hBM
  have hη' := eta_tiny hη
  have hun' : u * (202 / 10 * (n : ℝ)) = 202 / 10 * (u * n) := by ring
  have : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

theorem sc_mark {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hη : η ≤ 1 / 2 ^ 149)
    {n : ℕ} (hn2 : 2 ≤ n) (hun : u * (n : ℝ) ≤ 1 / 256) (hM : 2 ^ 40 * (n : ℝ) ^ 2 ≤ M)
    {S : ℝ} (hS1 : 1989 / 100 ≤ S) (hS2 : S ≤ 2011 / 100) {j k : ℕ} (hj : j ≤ n) (hk : k < j) :
    fl (S * fl (k : ℝ)) ≤ fl (S * fl (j : ℝ)) - 16 * (ndist j k : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hBM : 202 / 10 * (n : ℝ) ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  have hnM : (n : ℝ) ≤ M := by
    have := range_lin hM hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have hkn : k ≤ n := le_of_lt (lt_of_lt_of_le hk hj)
  obtain ⟨hb1, -⟩ := sc_b5 hr hu0 hη hn2 hun hM hS1 hS2 hkn
  obtain ⟨hb2, -⟩ := sc_b5 hr hu0 hη hn2 hun hM hS1 hS2 hj
  have hg := hr.gap hu0 hb1 hb2 hBM
  obtain ⟨hf1, hf2⟩ := fpos hr hu0 hη hun hnM hkn
  obtain ⟨hf3, hf4⟩ := fpos hr hu0 hη hun hnM hj
  have hkj : (k : ℝ) + 1 ≤ j := by exact_mod_cast hk
  rw [ndist_cast, abs_of_nonneg (by linarith)]
  have hf2' := abs_le.mp hf2
  have hf4' := abs_le.mp hf4
  have hd : ((j : ℝ) - k) - 1 / 100 ≤ fl (j : ℝ) - fl (k : ℝ) := by linarith
  have hd0 : 0 ≤ ((j : ℝ) - k) - 1 / 100 := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hp1 := mul_le_mul_of_nonneg_left hd hS0
  have hp2 := mul_le_mul_of_nonneg_right hS1 hd0
  have hη' := eta_tiny hη
  have hun' : u * (202 / 10 * (n : ℝ)) = 202 / 10 * (u * n) := by ring
  have : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

theorem sc_unm {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 2 ^ 149)
    {n : ℕ} (hn2 : 2 ≤ n) (hun : u * (n : ℝ) ≤ 1 / 256) (hM : 2 ^ 40 * (n : ℝ) ^ 2 ≤ M)
    {S N' pk : ℝ} (hS1 : 1989 / 100 ≤ S) (hS2 : S ≤ 2011 / 100)
    (hN : |N' - (-50)| ≤ 50 / 190) (hpk : |pk - 1| ≤ 1 / 190)
    {j k : ℕ} (hj : j < n) (hk : k < n) :
    fl (fl (S * fl (k : ℝ)) + fl (fl (n : ℝ) * fl (N' * pk)))
        ≤ fl (S * fl (j : ℝ)) - 16 * (ndist j k : ℝ)
    ∧ |fl (fl (S * fl (k : ℝ)) + fl (fl (n : ℝ) * fl (N' * pk)))| ≤ 74 * n := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnM : (n : ℝ) ≤ M := by
    have := range_lin hM hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have hM10 : (10 : ℝ) ≤ M := range_const hM hn1 (by norm_num)
  have hη' := eta_tiny hη
  have hηs : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have hu6 : u ≤ 1 / 10 ^ 6 := le_trans hu1 (by norm_num)
  -- the product N' * pk
  have hm := mul_near hN hpk
  have hm2 : (50 / 190 : ℝ) * |(1 : ℝ)| + 1 / 190 * |(-50 : ℝ)| + 50 / 190 * (1 / 190) ≤ 53 / 100 := by
    norm_num
  have hm3 := le_trans hm hm2
  have hm4 := abs_le.mp hm3
  have hNp : |N' * pk| ≤ 5053 / 100 := abs_le.mpr ⟨by linarith [hm4.1, hm4.2], by linarith [hm4.1, hm4.2]⟩
  have hNpM : (5053 / 100 : ℝ) ≤ M := range_const hM hn1 (by norm_num)
  have hb7 := hr.abs hu0 hNp hNpM
  have hb7' := abs_le.mp hb7
  have hu50 : u * (5053 / 100) ≤ 1 / 10000 := by
    have := mul_le_mul_of_nonneg_right hu1 (by norm_num : (0 : ℝ) ≤ 5053 / 100)
    have h2 : (1 : ℝ) / 2 ^ 24 * (5053 / 100) ≤ 1 / 10000 := by norm_num
    linarith
  have hb7a : fl (N' * pk) ≤ -4946 / 100 := by linarith [hm4.1, hm4.2, hb7'.1, hb7'.2]
  have hb7b : -5054 / 100 ≤ fl (N' * pk) := by linarith [hm4.1, hm4.2, hb7'.1, hb7'.2]
  -- F = fl n
  obtain ⟨hF0, hF1⟩ := fpos hr hu0 hη hun hnM (le_refl n)
  have hF1' := abs_le.mp hF1
  have hFu := mul_le_mul_of_nonneg_left hb7a hF0
  have hFl := mul_le_mul_of_nonneg_left hb7b hF0
  have hFb : |fl (n : ℝ) * fl (N' * pk)| ≤ 509 / 10 * n := by
    rw [abs_le]
    constructor
    · linarith [hFl, hF1'.1, hF1'.2]
    · linarith [hFu, hF0]
  have hBM1 : (509 / 10 : ℝ) * n ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  have hE := hr.abs hu0 hFb hBM1
  have hE' := abs_le.mp hE
  have hun1 : u * (509 / 10 * (n : ℝ)) = 509 / 10 * (u * n) := by ring
  have hE1 : fl (fl (n : ℝ) * fl (N' * pk)) ≤ -49 * n := by
    linarith [hFu, hE'.2, hF1'.1, hF1'.2, hun1, hun, hη', hηs]
  have hE2 : |fl (fl (n : ℝ) * fl (N' * pk))| ≤ 52 * n := by
    rw [abs_le]
    constructor
    · linarith [hFl, hE'.1, hF1'.1, hF1'.2, hun1, hun, hη', hηs]
    · linarith [hE1]
  -- b5 for k and j
  have hkn : k ≤ n := le_of_lt hk
  have hjn : j ≤ n := le_of_lt hj
  obtain ⟨hk1, hk2⟩ := sc_b5 hr hu0 hη hn2 hun hM hS1 hS2 hkn
  obtain ⟨hj1, hj2⟩ := sc_b5 hr hu0 hη hn2 hun hM hS1 hS2 hjn
  have hk2' := abs_le.mp hk2
  have hj2' := abs_le.mp hj2
  have hk1' := abs_le.mp hk1
  have hbk : |fl (S * fl (k : ℝ))| ≤ 203 / 10 * n := by
    rw [abs_le]
    constructor <;> linarith [hk1'.1, hk1'.2, hk2'.1, hk2'.2]
  have hE2' := abs_le.mp hE2
  have hY : |fl (S * fl (k : ℝ)) + fl (fl (n : ℝ) * fl (N' * pk))| ≤ 73 * n := by
    rw [abs_le]
    constructor <;> linarith [(abs_le.mp hbk).1, (abs_le.mp hbk).2, hE2'.1, hE2'.2]
  have hBM2 : (73 : ℝ) * n ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  have hs := hr.abs hu0 hY hBM2
  have hs' := abs_le.mp hs
  have hun2 : u * (73 * (n : ℝ)) = 73 * (u * n) := by ring
  refine ⟨?_, ?_⟩
  · -- the gap
    obtain ⟨hfk0, hfk1⟩ := fpos hr hu0 hη hun hnM hkn
    obtain ⟨hfj0, hfj1⟩ := fpos hr hu0 hη hun hnM hjn
    have hfk1' := abs_le.mp hfk1
    have hfj1' := abs_le.mp hfj1
    rw [ndist_cast]
    have hneg := neg_le_abs ((j : ℝ) - k)
    have hpos := le_abs_self ((j : ℝ) - k)
    have hdiff : fl (k : ℝ) - fl (j : ℝ) ≤ |(j : ℝ) - k| + 1 / 100 := by linarith
    have hjR : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
    have hkR : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hdn : |(j : ℝ) - k| ≤ n - 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hd0 : 0 ≤ |(j : ℝ) - k| + 1 / 100 := by positivity
    have hS0 : 0 ≤ S := by linarith
    have hp1 := mul_le_mul_of_nonneg_left hdiff hS0
    have hp2 := mul_le_mul_of_nonneg_right hS2 hd0
    have hbd : |(j : ℝ) - k| ≥ 0 := abs_nonneg _
    linarith [hs'.1, hs'.2, hE1, hk2'.1, hk2'.2, hj2'.1, hj2'.2, hun2, hη']
  · have : |fl (fl (S * fl (k : ℝ)) + fl (fl (n : ℝ) * fl (N' * pk)))| ≤ 74 * n := by
      rw [abs_le]
      constructor <;> linarith [hs'.1, hs'.2, (abs_le.mp hY).1, (abs_le.mp hY).2, hun2, hη']
    exact this

/-- Last position `≤ k` holding a non-propagate token (BOS counts). -/
def lm (w : List ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    if tokAt w (k + 1) = 1 ∨ tokAt w (k + 1) = 2 ∨ tokAt w (k + 1) = 4 then lm w k else k + 1

theorem lm_zero (w : List ℕ) : lm w 0 = 0 := rfl

theorem lm_succ (w : List ℕ) (k : ℕ) :
    lm w (k + 1) =
      if tokAt w (k + 1) = 1 ∨ tokAt w (k + 1) = 2 ∨ tokAt w (k + 1) = 4 then lm w k
      else k + 1 := rfl

theorem lm_le (w : List ℕ) : ∀ k, lm w k ≤ k := by
  intro k
  induction k with
  | zero => exact le_refl _
  | succ k ih =>
    rw [lm_succ]
    split_ifs
    · omega
    · exact le_refl _

theorem lm_mark (w : List ℕ) : ∀ k,
    ¬ (tokAt w (lm w k) = 1 ∨ tokAt w (lm w k) = 2 ∨ tokAt w (lm w k) = 4) := by
  intro k
  induction k with
  | zero =>
    rw [lm_zero, Lane4.Seq.tokAt_zero]
    omega
  | succ k ih =>
    rw [lm_succ]
    split_ifs with h
    · exact ih
    · exact h

theorem lm_after (w : List ℕ) : ∀ k j, lm w k < j → j ≤ k →
    (tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 4) := by
  intro k
  induction k with
  | zero =>
    intro j h1 h2
    rw [lm_zero] at h1
    omega
  | succ k ih =>
    intro j h1 h2
    rw [lm_succ] at h1
    by_cases hc : tokAt w (k + 1) = 1 ∨ tokAt w (k + 1) = 2 ∨ tokAt w (k + 1) = 4
    · rw [if_pos hc] at h1
      by_cases hj : j = k + 1
      · rw [hj]
        exact hc
      · exact ih j h1 (by omega)
    · rw [if_neg hc] at h1
      omega

theorem step_eq (t c : ℕ) (ht : 1 ≤ t ∧ t ≤ 5) :
    (if cls t = 2 then c else cls t) =
      (if t = 1 ∨ t = 2 ∨ t = 4 then c else (if t = 5 then 1 else 0)) := by
  obtain ⟨h1, h2⟩ := ht
  have : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
  rcases this with h | h | h | h | h <;> subst h <;> simp [cls]

theorem carry_lm (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) :
    ∀ k, k ≤ w.length → carry (w.take k) = (if tokAt w (lm w k) = 5 then 1 else 0) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [carry, lm_zero, Lane4.Seq.tokAt_zero]
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    have hlt : k < w.length := by omega
    have ht := Lane4.Seq.tokAt_succ w k hlt
    have h5 := hw _ (List.getElem_mem hlt)
    have htake : w.take (k + 1) = w.take k ++ [w[k]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hlt]
      rfl
    have hc : carry (w.take (k + 1)) =
        (if cls w[k] = 2 then carry (w.take k) else cls w[k]) := by
      rw [htake]
      simp [carry, List.foldl_append]
    rw [hc, step_eq _ _ h5, ← ht, lm_succ]
    by_cases hcnd : tokAt w (k + 1) = 1 ∨ tokAt w (k + 1) = 2 ∨ tokAt w (k + 1) = 4
    · simp only [if_pos hcnd]
      exact ih'
    · simp only [if_neg hcnd]
      try rfl

theorem tgt_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) (h1 : 1 ≤ i)
    (h2 : i ≤ w.length) :
    target w i = (dg (tokAt w i) + (if tokAt w (lm w (i - 1)) = 5 then 1 else 0)) % 3 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hlt : k < w.length := by omega
  have hk : k + 1 - 1 = k := by omega
  have hg : w.getD k 0 = tokAt w (k + 1) := by
    rw [Lane4.Seq.tokAt_succ w k hlt]
    first
      | exact List.getD_eq_getElem w 0 hlt
      | simp [List.getD_eq_getElem?_getD, hlt]
  unfold target
  rw [hk, hg, carry_lm w hw k (by omega)]

theorem mul_near_n {x y s t a b c : ℝ} (hx : |x - s| ≤ a) (hy : |y - t| ≤ b)
    (hc : a * |t| + b * |s| + a * b ≤ c) : |x * y - s * t| ≤ c :=
  le_trans (mul_near hx hy) hc

theorem Zcalc {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 2 ^ 149) (hM : 10 ≤ M) {P' R' Bv sP sR eP eR : ℝ}
    (h1 : |P' - sP| ≤ eP) (h2 : |R' - sR| ≤ eR) (hBv : |Bv - (-3 / 4)| ≤ 1 / 200)
    (hs : |sP + sR| ≤ 5) (hb : eP + eR ≤ 1) :
    |fl (fl (P' + R') + Bv) - (sP + sR + (-3 / 4))| ≤ eP + eR + 1 / 200 + 2 / 100000 := by
  have a1 := add_near h1 h2
  have a2 := fl_near hr hu0 hu hη hM a1 hs (by linarith)
  have a3 := add_near a2 hBv
  have hs' := abs_le.mp hs
  have ht : |sP + sR + (-3 / 4)| ≤ 6 := abs_le.mpr ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
  have a4 := fl_near hr hu0 hu hη hM a3 ht (by linarith)
  linarith

theorem Y_zero {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (W Q Zv : ℝ) (h : relu Zv = 0) :
    fl (Q * fl (W * relu Zv)) = 0 := by
  rw [h, mul_zero, hr.zero, mul_zero, hr.zero]

theorem Y_pos {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 2 ^ 149) (hM : 10 ≤ M) (W Q Zv : ℝ) (hW : |W - 1| ≤ 1 / 190)
    (hQ : |Q - (-1)| ≤ 1 / 190) (hZ : |Zv - 3| ≤ 11 / 100) :
    |fl (Q * fl (W * relu Zv)) - (-3)| ≤ 15 / 100 := by
  have hZ' := abs_le.mp hZ
  have hZ0 : 0 ≤ Zv := by linarith [hZ'.1]
  rw [relu_of_nonneg hZ0]
  have h1 := mul_near_n hW hZ (c := 127 / 1000) (by norm_num)
  have h2 := fl_near hr hu0 hu hη hM h1 (t := 1 * 3) (B := 3) (by norm_num) (by norm_num)
  have h3 := mul_near_n hQ h2 (c := 145 / 1000) (by norm_num)
  have h4 := fl_near hr hu0 hu hη hM h3 (t := (-1) * (1 * 3)) (B := 3) (by norm_num) (by norm_num)
  rw [abs_le] at h4 ⊢
  constructor <;> linarith [h4.1, h4.2]

theorem fin_bound {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) (hM : 10 ≤ M)
    (P R Bv W D C Q g dgv pv A Cr pbit Zv : ℝ)
    (hP : |P - (-15 / 4)| ≤ 1 / 50) (hR : |R - 15 / 4| ≤ 1 / 50)
    (hBv : |Bv - (-3 / 4)| ≤ 1 / 200) (hW : |W - 1| ≤ 1 / 190) (hD : |D - 1| ≤ 1 / 190)
    (hC : |C - 1| ≤ 1 / 190) (hQ : |Q - (-1)| ≤ 1 / 190)
    (hg : |g - dgv| ≤ 2 / 190) (hdg0 : 0 ≤ dgv) (hdg2 : dgv ≤ 2)
    (hpb : (pbit = 0 ∧ pv = 0) ∨ (pbit = 1 ∧ |pv - 1| ≤ 1 / 190))
    (hCr : Cr = 0 ∨ Cr = 1) (hA : |A - Cr| ≤ 21 / 1000)
    (hZ : Zv = fl (fl (fl (P * pv) + fl (R * A)) + Bv)) :
    |fl (fl (fl (D * g) + fl (C * A)) + fl (Q * fl (W * relu Zv)))
        - (dgv + Cr * (3 * pbit - 2))| ≤ 1 / 4 := by
  have hCr1 : |Cr| ≤ 1 := by
    rcases hCr with h | h <;> rw [h] <;> norm_num
  obtain ⟨hc1, hc2⟩ := abs_le.mp hCr1
  have hX1 := mul_near_n hD hg (c := 22 / 1000) (by rw [abs_of_nonneg hdg0, abs_one]; linarith)
  have hX2 := fl_near hr hu0 hu hη hM hX1 (t := 1 * dgv) (B := 2)
    (by rw [one_mul, abs_of_nonneg hdg0]; exact hdg2) (by norm_num)
  have hX3 := mul_near_n hC hA (c := 27 / 1000) (by rw [abs_one]; linarith)
  have hX4 := fl_near hr hu0 hu hη hM hX3 (t := 1 * Cr) (B := 1)
    (by rw [one_mul]; exact hCr1) (by norm_num)
  have hX5 := add_near hX2 hX4
  have hX6 := fl_near hr hu0 hu hη hM hX5 (t := 1 * dgv + 1 * Cr) (B := 3)
    (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)
  have hX7 := fl_near hr hu0 hu hη hM hX6 (t := 1 * dgv + 1 * Cr) (B := 3)
    (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)
  rcases hpb with ⟨rfl, rfl⟩ | ⟨rfl, hpv1⟩ <;> rcases hCr with rfl | rfl
  · -- pbit = 0, Cr = 0
    have hP0 : |fl (P * 0) - 0| ≤ 0 := by rw [mul_zero, hr.zero]; simp
    have hRA := mul_near_n hR hA (c := 8 / 100) (by norm_num)
    have hRA' := fl_near hr hu0 hu hη hM hRA (t := 15 / 4 * 0) (B := 1) (by norm_num) (by norm_num)
    have hZc := Zcalc hr hu0 hu hη hM hP0 hRA' hBv (by norm_num) (by norm_num)
    have hZc' : |Zv - (0 + 15 / 4 * 0 + (-3 / 4))| ≤ 9 / 100 := by
      rw [hZ]
      linarith
    have hneg : Zv ≤ 0 := by
      have := (abs_le.mp hZc').2
      linarith
    have hY := Y_zero hr W Q Zv (relu_of_nonpos hneg)
    rw [hY, add_zero]
    rw [abs_le] at hX7 ⊢
    constructor <;> linarith [hX7.1, hX7.2]
  · -- pbit = 0, Cr = 1
    have hP0 : |fl (P * 0) - 0| ≤ 0 := by rw [mul_zero, hr.zero]; simp
    have hRA := mul_near_n hR hA (c := 1 / 10) (by norm_num)
    have hRA' := fl_near hr hu0 hu hη hM hRA (t := 15 / 4 * 1) (B := 4) (by norm_num) (by norm_num)
    have hZc := Zcalc hr hu0 hu hη hM hP0 hRA' hBv (by norm_num) (by norm_num)
    have hZ3 : |Zv - 3| ≤ 11 / 100 := by
      have : |Zv - (0 + 15 / 4 * 1 + (-3 / 4))| ≤ 11 / 100 := by
        rw [hZ]
        linarith
      rw [abs_le] at this ⊢
      constructor <;> linarith [this.1, this.2]
    have hY := Y_pos hr hu0 hu hη hM W Q Zv hW hQ hZ3
    have hS := add_near hX6 hY
    have hO := fl_near hr hu0 hu hη hM hS (t := (1 * dgv + 1 * 1) + (-3)) (B := 3)
      (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)
    rw [abs_le] at hO ⊢
    constructor <;> linarith [hO.1, hO.2]
  · -- pbit = 1, Cr = 0
    have hP1 := mul_near_n hP hpv1 (c := 4 / 100) (by norm_num)
    have hP1' := fl_near hr hu0 hu hη hM hP1 (t := -15 / 4 * 1) (B := 4) (by norm_num) (by norm_num)
    have hRA := mul_near_n hR hA (c := 8 / 100) (by norm_num)
    have hRA' := fl_near hr hu0 hu hη hM hRA (t := 15 / 4 * 0) (B := 1) (by norm_num) (by norm_num)
    have hZc := Zcalc hr hu0 hu hη hM hP1' hRA' hBv (by norm_num) (by norm_num)
    have hZc' : |Zv - (-15 / 4 * 1 + 15 / 4 * 0 + (-3 / 4))| ≤ 13 / 100 := by
      rw [hZ]
      linarith
    have hneg : Zv ≤ 0 := by
      have := (abs_le.mp hZc').2
      linarith
    have hY := Y_zero hr W Q Zv (relu_of_nonpos hneg)
    rw [hY, add_zero]
    rw [abs_le] at hX7 ⊢
    constructor <;> linarith [hX7.1, hX7.2]
  · -- pbit = 1, Cr = 1
    have hP1 := mul_near_n hP hpv1 (c := 4 / 100) (by norm_num)
    have hP1' := fl_near hr hu0 hu hη hM hP1 (t := -15 / 4 * 1) (B := 4) (by norm_num) (by norm_num)
    have hRA := mul_near_n hR hA (c := 1 / 10) (by norm_num)
    have hRA' := fl_near hr hu0 hu hη hM hRA (t := 15 / 4 * 1) (B := 4) (by norm_num) (by norm_num)
    have hZc := Zcalc hr hu0 hu hη hM hP1' hRA' hBv (by norm_num) (by norm_num)
    have hZc' : |Zv - (-15 / 4 * 1 + 15 / 4 * 1 + (-3 / 4))| ≤ 15 / 100 := by
      rw [hZ]
      linarith
    have hneg : Zv ≤ 0 := by
      have := (abs_le.mp hZc').2
      linarith
    have hY := Y_zero hr W Q Zv (relu_of_nonpos hneg)
    rw [hY, add_zero]
    rw [abs_le] at hX7 ⊢
    constructor <;> linarith [hX7.1, hX7.2]

theorem flb {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 2 ^ 149) (hM : 200 ≤ M) {x B : ℝ} (hx : |x| ≤ B) (hB : B ≤ 100) :
    |fl x| ≤ B + 1 / 100000 := by
  have h1 := hr.bound hu0 hx (by linarith)
  have h3 : u * B ≤ u * 100 := mul_le_mul_of_nonneg_left hB hu0
  have h4 : u * 100 ≤ 1 / 2 ^ 24 * 100 := mul_le_mul_of_nonneg_right hu (by norm_num)
  have h5 := eta_tiny hη
  have h6 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 200000 := by norm_num
  have h7 : (1 : ℝ) / 2 ^ 24 * 100 ≤ 1 / 200000 := by norm_num
  linarith

theorem Npk {N' pk : ℝ} (hN : |N' - (-50)| ≤ 50 / 190) (hpk : pk = 0 ∨ |pk - 1| ≤ 1 / 190) :
    |N' * pk| ≤ 51 := by
  rcases hpk with h | h
  · rw [h, mul_zero, abs_zero]
    norm_num
  · have hm := mul_near_n hN h (c := 53 / 100) (by norm_num)
    have := abs_le.mp hm
    exact abs_le.mpr ⟨by linarith [this.1, this.2], by linarith [this.1, this.2]⟩

theorem Te_bound {T e : ℝ} (hT : |T - 1| ≤ 1 / 190) (he : |e| ≤ 191 / 190) :
    |T * e| ≤ 1011 / 1000 := by
  rw [abs_mul]
  have h1 : |T| ≤ 191 / 190 := by
    have := abs_le.mp hT
    exact abs_le.mpr ⟨by linarith [this.1], by linarith [this.2]⟩
  have := mul_le_mul h1 he (abs_nonneg _) (by norm_num)
  linarith

theorem relu_abs_le {z B : ℝ} (h : |z| ≤ B) : |relu z| ≤ B := by
  rcases le_total 0 z with h0 | h0
  · rw [relu_of_nonneg h0]
    exact h
  · rw [relu_of_nonpos h0, abs_zero]
    exact le_trans (abs_nonneg _) h

theorem target_real (t c : ℕ) (ht : 1 ≤ t ∧ t ≤ 5) :
    ((((dg t + (if c = 5 then 1 else 0)) % 3 : ℕ)) : ℝ)
      = (dg t : ℝ) + (if c = 5 then (1 : ℝ) else 0)
          * (3 * (if t = 1 ∨ t = 2 ∨ t = 4 then (1 : ℝ) else 0) - 2) := by
  obtain ⟨h1, h2⟩ := ht
  have : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> by_cases hc : c = 5 <;> simp [hc, dg] <;> norm_num

theorem ec_abs {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 2 ^ 149) (hM : 200 ≤ M) (p : Pert) (hp : p.Within (1 / 200)) (t : ℕ) :
    |ec fl p t| ≤ 191 / 190 := by
  obtain ⟨h1, h2⟩ := ec_b hr hu0 hu hη hM p hp t
  by_cases h : t = 5
  · have := abs_le.mp (h1 h)
    exact abs_le.mpr ⟨by linarith [this.1], by linarith [this.2]⟩
  · rw [h2 h, abs_zero]
    norm_num

theorem ep_abs {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 2 ^ 149) (hM : 200 ≤ M) (p : Pert) (hp : p.Within (1 / 200)) (t : ℕ) :
    |ep fl p t| ≤ 191 / 190 := by
  obtain ⟨h1, h2⟩ := ep_b hr hu0 hu hη hM p hp t
  by_cases h : (t = 1 ∨ t = 2 ∨ t = 4)
  · have := abs_le.mp (h1 h)
    exact abs_le.mpr ⟨by linarith [this.1], by linarith [this.2]⟩
  · rw [h2 h, abs_zero]
    norm_num

theorem ep_or {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 2 ^ 149) (hM : 200 ≤ M) (p : Pert) (hp : p.Within (1 / 200)) (t : ℕ) :
    ep fl p t = 0 ∨ |ep fl p t - 1| ≤ 1 / 190 := by
  obtain ⟨h1, h2⟩ := ep_b hr hu0 hu hη hM p hp t
  by_cases h : (t = 1 ∨ t = 2 ∨ t = 4)
  · exact Or.inr (h1 h)
  · exact Or.inl (h2 h)

theorem fl_ep {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hM : 200 ≤ M) (p : Pert)
    (hp : p.Within (1 / 200)) (t : ℕ) : fl (ep fl p t) = ep fl p t := by
  unfold ep
  apply fl_sw hr _ (hp.E t 1) (by norm_num)
  split_ifs <;> norm_num <;> linarith

theorem fl_eg {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hM : 200 ≤ M) (p : Pert)
    (hp : p.Within (1 / 200)) (t : ℕ) : fl (eg fl p t) = eg fl p t := by
  unfold eg
  apply fl_sw hr _ (hp.E t 2) (by norm_num)
  have h := dg_le t
  have h2 : (((dg t : ℕ) : ℚ) : ℝ) ≤ 2 := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ (((dg t : ℕ) : ℚ) : ℝ) := by positivity
  rw [abs_of_nonneg h0]
  linarith

theorem near_abs {x t e B1 B : ℝ} (h : |x - t| ≤ e) (ht : |t| ≤ B1) (hB : B1 + e ≤ B) :
    |x| ≤ B := by
  have := abs_sub_abs_le_abs_sub x t
  linarith

theorem abs_add3 {a b : ℝ} {x y : ℝ} (hx : |a| ≤ x) (hy : |b| ≤ y) : |a + b| ≤ x + y :=
  le_trans (abs_add_le a b) (add_le_add hx hy)

theorem abs_mul3 {a b : ℝ} {x y : ℝ} (hx : |a| ≤ x) (hy : |b| ≤ y) (hx0 : 0 ≤ x) :
    |a * b| ≤ x * y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) hx0

set_option maxHeartbeats 6400000 in
theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη p hp w hw hn hnη hM i hi1 hi
  have hn2 : 2 ≤ w.length + 1 := by omega
  have hn1 : 1 ≤ w.length + 1 := by omega
  have hnR : (2 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hn2
  have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
    have := range_lin hM hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have hM10 : (10 : ℝ) ≤ M := range_const hM hn1 (by norm_num)
  have hM200 : (200 : ℝ) ≤ M := range_const hM hn1 (by norm_num)
  have h200 : 200 * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  -- stored weights
  obtain ⟨S, hSd⟩ : ∃ S : ℝ, S = sw fl 20 (p.A 0 0 5 6) := ⟨_, rfl⟩
  have hSb : |S - 20| ≤ 20 / 190 := by
    rw [hSd]
    exact swr hr hu0 hu1 hη 20 (hp.A 0 0 5 6) 20 (20 / 190) (by norm_num)
      (Or.inr (by norm_num)) (by norm_num) hM200 (by norm_num)
  obtain ⟨N', hNd⟩ : ∃ N' : ℝ, N' = sw fl (-50) (p.A 0 0 7 1) := ⟨_, rfl⟩
  have hNb : |N' - (-50)| ≤ 50 / 190 := by
    rw [hNd]
    exact swr hr hu0 hu1 hη (-50) (hp.A 0 0 7 1) (-50) (50 / 190) (by norm_num)
      (Or.inr (by norm_num)) (by norm_num) hM200 (by norm_num)
  obtain ⟨T, hTd⟩ : ∃ T : ℝ, T = sw fl 1 (p.V 0 0 3 0) := ⟨_, rfl⟩
  have hTb : |T - 1| ≤ 1 / 190 := by
    rw [hTd]
    exact swr hr hu0 hu1 hη 1 (hp.V 0 0 3 0) 1 (1 / 190) (by norm_num)
      (Or.inr (by norm_num)) (by norm_num) hM200 (by norm_num)
  obtain ⟨P, hPd⟩ : ∃ P : ℝ, P = sw fl (-15 / 4) (p.W1 0 0 1) := ⟨_, rfl⟩
  have hPb : |P - (-15 / 4)| ≤ 1 / 50 := by
    rw [hPd]
    exact swr hr hu0 hu1 hη (-15 / 4) (hp.W1 0 0 1) (-15 / 4) (1 / 50) (by norm_num)
      (Or.inr (by norm_num)) (by norm_num) hM200 (by norm_num)
  obtain ⟨R, hRd⟩ : ∃ R : ℝ, R = sw fl (15 / 4) (p.W1 0 0 3) := ⟨_, rfl⟩
  have hRb : |R - 15 / 4| ≤ 1 / 50 := by
    rw [hRd]
    exact swr hr hu0 hu1 hη (15 / 4) (hp.W1 0 0 3) (15 / 4) (1 / 50) (by norm_num)
      (Or.inr (by norm_num)) (by norm_num) hM200 (by norm_num)
  obtain ⟨Bv, hBd⟩ : ∃ Bv : ℝ, Bv = sw fl (-3 / 4) (p.b1 0 0) := ⟨_, rfl⟩
  have hBb : |Bv - (-3 / 4)| ≤ 1 / 200 := by
    rw [hBd]
    exact swr hr hu0 hu1 hη (-3 / 4) (hp.b1 0 0) (-3 / 4) (1 / 200) (by norm_num)
      (Or.inr (by norm_num)) (by norm_num) hM200 (by norm_num)
  obtain ⟨W, hWd⟩ : ∃ W : ℝ, W = sw fl 1 (p.W2 0 4 0) := ⟨_, rfl⟩
  have hWb : |W - 1| ≤ 1 / 190 := by
    rw [hWd]
    exact swr hr hu0 hu1 hη 1 (hp.W2 0 4 0) 1 (1 / 190) (by norm_num)
      (Or.inr (by norm_num)) (by norm_num) hM200 (by norm_num)
  obtain ⟨D, hDd⟩ : ∃ D : ℝ, D = sw fl 1 (p.oW 2) := ⟨_, rfl⟩
  have hDb : |D - 1| ≤ 1 / 190 := by
    rw [hDd]
    exact swr hr hu0 hu1 hη 1 (hp.oW 2) 1 (1 / 190) (by norm_num)
      (Or.inr (by norm_num)) (by norm_num) hM200 (by norm_num)
  obtain ⟨C, hCd⟩ : ∃ C : ℝ, C = sw fl 1 (p.oW 3) := ⟨_, rfl⟩
  have hCb : |C - 1| ≤ 1 / 190 := by
    rw [hCd]
    exact swr hr hu0 hu1 hη 1 (hp.oW 3) 1 (1 / 190) (by norm_num)
      (Or.inr (by norm_num)) (by norm_num) hM200 (by norm_num)
  obtain ⟨Q, hQd⟩ : ∃ Q : ℝ, Q = sw fl (-1) (p.oW 4) := ⟨_, rfl⟩
  have hQb : |Q - (-1)| ≤ 1 / 190 := by
    rw [hQd]
    exact swr hr hu0 hu1 hη (-1) (hp.oW 4) (-1) (1 / 190) (by norm_num)
      (Or.inr (by norm_num)) (by norm_num) hM200 (by norm_num)
  obtain ⟨hS1, hS2⟩ : 1989 / 100 ≤ S ∧ S ≤ 2011 / 100 := by
    have := abs_le.mp hSb
    constructor <;> linarith [this.1, this.2]
  -- scores
  have hI1 : ∀ k : ℕ, k ≤ w.length + 1 → fl (fl (S * fl (k : ℝ))) = fl (S * fl (k : ℝ)) := by
    intro k hk
    apply hr.idem
    have := (sc_b5 hr hu0 hη hn2 hn hM hS1 hS2 hk).1
    linarith
  have hepo : ∀ k : ℕ, ep fl p (tokAt w k) = 0 ∨ |ep fl p (tokAt w k) - 1| ≤ 1 / 190 :=
    fun k => ep_or hr hu0 hu1 hη hM200 p hp (tokAt w k)
  have hI2 : ∀ k : ℕ, fl (fl (N' * ep fl p (tokAt w k))) = fl (N' * ep fl p (tokAt w k)) := by
    intro k
    apply hr.idem
    have := Npk hNb (hepo k)
    linarith
  have hsk : ∀ k : ℕ, k ≤ w.length + 1 →
      hscore hd fl (p.A 0 0) (net.init fl p w) i k =
        fl (fl (S * fl (k : ℝ)) + fl (fl ((w.length + 1 : ℕ) : ℝ)
          * fl (N' * ep fl p (tokAt w k)))) := by
    intro k hk
    have hI1' := hI1 k hk
    have hI2' := hI2 k
    rw [hSd] at hI1' ⊢
    rw [hNd] at hI2' ⊢
    simp only [hscore, init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact score_eq hr (p.A 0 0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI1' hI2'
  have hjle : lm w (i - 1) ≤ i - 1 := lm_le w (i - 1)
  have hjn : lm w (i - 1) < w.length + 1 := by omega
  have hjmark := lm_mark w (i - 1)
  have hscm : ∀ k : ℕ, k ≤ w.length + 1 → ¬ (tokAt w k = 1 ∨ tokAt w k = 2 ∨ tokAt w k = 4) →
      hscore hd fl (p.A 0 0) (net.init fl p w) i k = fl (S * fl (k : ℝ)) := by
    intro k hk hnp
    rw [hsk k hk, (ep_b hr hu0 hu1 hη hM200 p hp _).2 hnp]
    simp [hr.zero, hI1 k hk]
  have hscj : hscore hd fl (p.A 0 0) (net.init fl p w) i (lm w (i - 1))
      = fl (S * fl ((lm w (i - 1) : ℕ) : ℝ)) := hscm _ (by omega) hjmark
  have hjc : lm w (i - 1) ∈ cand Mask.strict (w.length + 1) i := by
    rw [Lane4.Seq.mem_cand_strict]
    omega
  have hlen : (cand Mask.strict (w.length + 1) i).length ≤ w.length + 1 := by
    simp [cand]
    omega
  have hgap : ∀ k ∈ cand Mask.strict (w.length + 1) i, k ≠ lm w (i - 1) →
      hscore hd fl (p.A 0 0) (net.init fl p w) i k
        ≤ hscore hd fl (p.A 0 0) (net.init fl p w) i (lm w (i - 1))
          - 16 * (ndist (lm w (i - 1)) k : ℝ) := by
    intro k hk hne
    rw [Lane4.Seq.mem_cand_strict] at hk
    rw [hscj]
    by_cases hpr : tokAt w k = 1 ∨ tokAt w k = 2 ∨ tokAt w k = 4
    · rw [hsk k (by omega)]
      exact (sc_unm hr hu0 hu1 hη hn2 hn hM hS1 hS2 hNb
        ((ep_b hr hu0 hu1 hη hM200 p hp _).1 hpr) hjn (by omega)).1
    · rw [hscm k (by omega) hpr]
      have hkj : k < lm w (i - 1) := by
        by_contra hcon
        have hlt : lm w (i - 1) < k := by omega
        exact hpr (lm_after w (i - 1) k hlt (by omega))
      exact sc_mark hr hu0 hη hn2 hn hM hS1 hS2 (le_of_lt hjn) hkj
  have hSb' : ∀ k ∈ cand Mask.strict (w.length + 1) i,
      |hscore hd fl (p.A 0 0) (net.init fl p w) i k| ≤ 80 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    rw [Lane4.Seq.mem_cand_strict] at hk
    by_cases hpr : tokAt w k = 1 ∨ tokAt w k = 2 ∨ tokAt w k = 4
    · rw [hsk k (by omega)]
      have := (sc_unm hr hu0 hu1 hη hn2 hn hM hS1 hS2 hNb
        ((ep_b hr hu0 hu1 hη hM200 p hp _).1 hpr) (j := k) (by omega) (by omega)).2
      linarith
    · rw [hscm k (by omega) hpr]
      obtain ⟨h1, h2⟩ := sc_b5 hr hu0 hη hn2 hn hM hS1 hS2 (show k ≤ w.length + 1 by omega)
      have h1' := abs_le.mp h1
      have h2' := abs_le.mp h2
      rw [abs_le]
      constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]
  -- values
  have hfk : ∀ k : ℕ, rdot fl [1, 0, 0, 0, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 3) 0 0
      = fl (T * ec fl p (tokAt w k)) := by
    intro k
    have hb : |T * ec fl p (tokAt w k)| ≤ M := by
      have := Te_bound hTb (ec_abs hr hu0 hu1 hη hM200 p hp (tokAt w k))
      linarith
    rw [hTd] at hb ⊢
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact val_eq hr (p.V 0 0 3) _ _ _ _ _ _ _ (hr.idem _ hb)
  have hfB : ∀ k ∈ cand Mask.strict (w.length + 1) i,
      |(fun j => rdot fl [1, 0, 0, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 3) 0 0) k|
        ≤ 51 / 50 := by
    intro k _
    show |rdot fl [1, 0, 0, 0, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 3) 0 0| ≤ 51 / 50
    rw [hfk k]
    have := flb hr hu0 hu1 hη hM200 (Te_bound hTb (ec_abs hr hu0 hu1 hη hM200 p hp (tokAt w k)))
      (by norm_num)
    linarith
  obtain ⟨hA1, hA2⟩ := soft_near hr he hu0 hu1 hη0 hη (Lane4.Seq.cand_nodup _ _ _) hlen hn hnη
    hjc hgap hSb' (by linarith) hfB (by linarith)
  have hat := attn_eq (ex := ex) hr p w hw i
  have hA1' : |savg fl ex (cand Mask.strict (w.length + 1) i)
      (hscore hd fl (p.A 0 0) (net.init fl p w) i)
      (fun j => rdot fl [1, 0, 0, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 3) 0 0)
      - fl (T * ec fl p (tokAt w (lm w (i - 1))))| ≤ 51 / 50 / 100 + 1 / 2 ^ 90 := by
    have := hA1
    simp only [hfk (lm w (i - 1))] at this
    exact this
  generalize savg fl ex (cand Mask.strict (w.length + 1) i)
      (hscore hd fl (p.A 0 0) (net.init fl p w) i)
      (fun j => rdot fl [1, 0, 0, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 3) 0 0) = A
    at hat hA1' hA2
  have hfj : |fl (T * ec fl p (tokAt w (lm w (i - 1))))
      - (if tokAt w (lm w (i - 1)) = 5 then (1 : ℝ) else 0)| ≤ 106 / 10000 + 1 / 100000 := by
    by_cases hc5 : tokAt w (lm w (i - 1)) = 5
    · rw [if_pos hc5]
      have hec := (ec_b hr hu0 hu1 hη hM200 p hp _).1 hc5
      have h1 := mul_near_n hTb hec (c := 106 / 10000) (by norm_num)
      have h2 := fl_near hr hu0 hu1 hη hM10 h1 (t := 1 * 1) (B := 1) (by norm_num) (by norm_num)
      rw [abs_le] at h2 ⊢
      constructor <;> linarith [h2.1, h2.2]
    · rw [if_neg hc5, (ec_b hr hu0 hu1 hη hM200 p hp _).2 hc5, mul_zero, hr.zero]
      norm_num
  have hAb : |A - (if tokAt w (lm w (i - 1)) = 5 then (1 : ℝ) else 0)| ≤ 21 / 1000 := by
    have h1 := abs_sub_le A (fl (T * ec fl p (tokAt w (lm w (i - 1)))))
      (if tokAt w (lm w (i - 1)) = 5 then (1 : ℝ) else 0)
    have h2 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 100000 := by norm_num
    linarith [hA1', hfj]
  have hCr : (if tokAt w (lm w (i - 1)) = 5 then (1 : ℝ) else 0) = 0
      ∨ (if tokAt w (lm w (i - 1)) = 5 then (1 : ℝ) else 0) = 1 := by
    by_cases hc5 : tokAt w (lm w (i - 1)) = 5
    · right
      rw [if_pos hc5]
    · left
      rw [if_neg hc5]
  -- the readout
  obtain ⟨g, hgd⟩ : ∃ g : ℝ, g = eg fl p (tokAt w i) := ⟨_, rfl⟩
  obtain ⟨pv, hpvd⟩ : ∃ pv : ℝ, pv = ep fl p (tokAt w i) := ⟨_, rfl⟩
  have hg1 : fl g = g := by
    rw [hgd]
    exact fl_eg hr hM200 p hp _
  have hpv1 : fl pv = pv := by
    rw [hpvd]
    exact fl_ep hr hM200 p hp _
  have hgb : |g - (dg (tokAt w i) : ℝ)| ≤ 2 / 190 := by
    rw [hgd]
    exact eg_b hr hu0 hu1 hη hM200 p hp _
  have hdg0 : (0 : ℝ) ≤ (dg (tokAt w i) : ℝ) := Nat.cast_nonneg _
  have hdg2 : (dg (tokAt w i) : ℝ) ≤ 2 := by exact_mod_cast dg_le (tokAt w i)
  have hpva : |pv| ≤ 2 := by
    have := ep_abs hr hu0 hu1 hη hM200 p hp (tokAt w i)
    rw [hpvd]
    linarith
  have hga : |g| ≤ 3 := near_abs hgb (B1 := 2) (by rw [abs_of_nonneg hdg0]; exact hdg2) (by norm_num)
  have hCr1 : |(if tokAt w (lm w (i - 1)) = 5 then (1 : ℝ) else 0)| ≤ 1 := by
    rcases hCr with h | h <;> rw [h] <;> norm_num
  have hAa : |A| ≤ 2 := near_abs hAb (B1 := 1) hCr1 (by norm_num)
  have hPa : |P| ≤ 4 := near_abs hPb (B1 := 15 / 4) (by norm_num) (by norm_num)
  have hRa : |R| ≤ 4 := near_abs hRb (B1 := 15 / 4) (by norm_num) (by norm_num)
  have hBa : |Bv| ≤ 1 := near_abs hBb (B1 := 3 / 4) (by norm_num) (by norm_num)
  have hWa : |W| ≤ 2 := near_abs hWb (B1 := 1) (by norm_num) (by norm_num)
  have hDa : |D| ≤ 2 := near_abs hDb (B1 := 1) (by norm_num) (by norm_num)
  have hCa : |C| ≤ 2 := near_abs hCb (B1 := 1) (by norm_num) (by norm_num)
  have hQa : |Q| ≤ 2 := near_abs hQb (B1 := 1) (by norm_num) (by norm_num)
  -- idempotence of the towers
  have hPpv : |P * pv| ≤ 8 := by
    have := abs_mul3 hPa hpva (by norm_num)
    linarith
  have hIP : fl (fl (P * pv)) = fl (P * pv) := hr.idem _ (by linarith)
  have hfP := flb hr hu0 hu1 hη hM200 hPpv (by norm_num)
  have hRA : |R * A| ≤ 8 := by
    have := abs_mul3 hRa hAa (by norm_num)
    linarith
  have hfR := flb hr hu0 hu1 hη hM200 hRA (by norm_num)
  have hS1a : |fl (P * pv) + fl (R * A)| ≤ 17 := by
    have := abs_add3 (a := fl (P * pv)) (b := fl (R * A)) hfP hfR
    linarith
  have hIS : fl (fl (fl (P * pv) + fl (R * A))) = fl (fl (P * pv) + fl (R * A)) :=
    hr.idem _ (by linarith)
  have hfS := flb hr hu0 hu1 hη hM200 hS1a (by norm_num)
  obtain ⟨Zv, hZ⟩ : ∃ Zv : ℝ, Zv = fl (fl (fl (P * pv) + fl (R * A)) + Bv) := ⟨_, rfl⟩
  have hZin : |fl (fl (P * pv) + fl (R * A)) + Bv| ≤ 19 := by
    have := abs_add3 (a := fl (fl (P * pv) + fl (R * A))) (b := Bv) hfS hBa
    linarith
  have hZa : |Zv| ≤ 20 := by
    have := flb hr hu0 hu1 hη hM200 hZin (by norm_num)
    rw [hZ]
    linarith
  have hrz : |relu Zv| ≤ 20 := relu_abs_le hZa
  have hWr : |W * relu Zv| ≤ 40 := by
    have := abs_mul3 hWa hrz (by norm_num)
    linarith
  have hIW : fl (fl (W * relu Zv)) = fl (W * relu Zv) := hr.idem _ (by linarith)
  have hfW := flb hr hu0 hu1 hη hM200 hWr (by norm_num)
  have hQW : |Q * fl (W * relu Zv)| ≤ 82 := by
    have := abs_mul3 hQa (le_trans hfW (by norm_num : (40 : ℝ) + 1 / 100000 ≤ 41)) (by norm_num)
    linarith
  have hfQ := flb hr hu0 hu1 hη hM200 hQW (by norm_num)
  have hDg : |D * g| ≤ 6 := by
    have := abs_mul3 hDa hga (by norm_num)
    linarith
  have hID : fl (fl (D * g)) = fl (D * g) := hr.idem _ (by linarith)
  have hfD := flb hr hu0 hu1 hη hM200 hDg (by norm_num)
  have hCA : |C * A| ≤ 4 := by
    have := abs_mul3 hCa hAa (by norm_num)
    linarith
  have hfC := flb hr hu0 hu1 hη hM200 hCA (by norm_num)
  have hX0 : |fl (D * g) + fl (C * A)| ≤ 12 := by
    have := abs_add3 (a := fl (D * g)) (b := fl (C * A)) hfD hfC
    linarith
  have hfX := flb hr hu0 hu1 hη hM200 hX0 (by norm_num)
  have hO0 : |fl (fl (D * g) + fl (C * A)) + fl (Q * fl (W * relu Zv))| ≤ 100 := by
    have := abs_add3 (a := fl (fl (D * g) + fl (C * A))) (b := fl (Q * fl (W * relu Zv))) hfX hfQ
    linarith
  have hIO : fl (fl (fl (fl (D * g) + fl (C * A)) + fl (Q * fl (W * relu Zv))))
      = fl (fl (fl (D * g) + fl (C * A)) + fl (Q * fl (W * relu Zv))) :=
    hr.idem _ (by linarith)
  have hout := out_eq hr p w hw i A P R Bv W D C Q Zv pv g hat hA2 hpvd hgd hg1 hpv1 hPd hRd hBd
    hWd hDd hCd hQd hZ hIP hIS hIW hID hIO
  rw [hout]
  have htok : 1 ≤ tokAt w i ∧ tokAt w i ≤ 5 := by
    have hk : i - 1 < w.length := by omega
    have h1 : tokAt w i = w[i - 1] := by
      have := Lane4.Seq.tokAt_succ w (i - 1) hk
      rwa [show i - 1 + 1 = i by omega] at this
    rw [h1]
    exact hw _ (List.getElem_mem hk)
  rw [tgt_eq w hw i hi1 hi, target_real _ _ htok]
  have hpb : ((if tokAt w i = 1 ∨ tokAt w i = 2 ∨ tokAt w i = 4 then (1 : ℝ) else 0) = 0 ∧ pv = 0)
      ∨ ((if tokAt w i = 1 ∨ tokAt w i = 2 ∨ tokAt w i = 4 then (1 : ℝ) else 0) = 1
          ∧ |pv - 1| ≤ 1 / 190) := by
    by_cases hpr : tokAt w i = 1 ∨ tokAt w i = 2 ∨ tokAt w i = 4
    · right
      refine ⟨if_pos hpr, ?_⟩
      rw [hpvd]
      exact (ep_b hr hu0 hu1 hη hM200 p hp _).1 hpr
    · left
      refine ⟨if_neg hpr, ?_⟩
      rw [hpvd]
      exact (ep_b hr hu0 hu1 hη hM200 p hp _).2 hpr
  exact fin_bound hr hu0 hu1 hη hM10 P R Bv W D C Q g (dg (tokAt w i) : ℝ) pv A
    (if tokAt w (lm w (i - 1)) = 5 then (1 : ℝ) else 0)
    (if tokAt w i = 1 ∨ tokAt w i = 2 ∨ tokAt w i = 4 then (1 : ℝ) else 0) Zv
    hPb hRb hBb hWb hDb hCb hQb hgb hdg0 hdg2 hpb hCr hAb hZ

end Lane4.Case
