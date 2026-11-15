set_option linter.unusedVariables false
namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

/-- State: [u, a, c, att, mlp, 1, fl i, fl n] (width 8). -/
def z8 : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0]

def hh : Head :=
  { A := [z8, z8, z8, z8, z8, [0, 0, 0, 0, 0, 0, -20, 0], z8, [-48, 0, 0, 0, 0, 0, 0, 0]],
    V := [z8, z8, z8, [0, 1, 0, 0, 0, 0, 0, 0], z8, z8, z8, z8],
    mask := Mask.causal }

def blk : Block :=
  { heads := [hh],
    W1 := [[0, 0, -1, 1, 0, 0, 0, 0], [0, 0, 1, -1, 0, 0, 0, 0]],
    b1 := [0, 0],
    W2 := [[0, 0], [0, 0], [0, 0], [0, 0], [1, 1], [0, 0], [0, 0], [0, 0]],
    b2 := z8 }

def net : TNet :=
  { embed := [[1, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 0],
              [0, 1, 1, 0, 0], [1, 0, 0, 0, 0]],
    blocks := [blk],
    outW := [0, 0, 0, 0, 1, 0, 0, 0],
    outB := 0 }

def rU (t : ℕ) : ℚ := if t = 0 ∨ t = 5 then 1 else 0
def rA (t : ℕ) : ℚ := if t = 3 ∨ t = 4 then 1 else 0
def rC (t : ℕ) : ℚ := if t = 2 ∨ t = 3 ∨ t = 4 then 1 else 0

noncomputable def ue (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (rU (tokAt w j)) (p.E (tokAt w j) 0)
noncomputable def ae (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (rA (tokAt w j)) (p.E (tokAt w j) 1)
noncomputable def ce (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (rC (tokAt w j)) (p.E (tokAt w j) 2)

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [ue fl p w j, ae fl p w j, ce fl p w j, 0, 0] ++ pos fl j (w.length + 1) := by
  have h6 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4
      ∨ tokAt w j = 5 := by
    have := tok_le w hw j
    omega
  rcases h6 with h | h | h | h | h | h <;>
    simp [TNet.init, net, ue, ae, ce, swRow, rU, rA, rC, h, sw_zero hr]

/-- A stored weight is within 1/199 relative of a real value it is written as. -/
theorem sw_b {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2 ^ 24)
    (x : ℝ) (w : ℚ) (hx : (w : ℝ) = x) {d : ℝ} (hd : |d| ≤ 1 / 200) (hxM : 2 * |x| ≤ M) :
    |sw fl w d - x| ≤ 1 / 199 * |x| + η := by
  have h24 : (1 : ℝ) / 2 ^ 24 ≤ 1 / 10 ^ 6 := by norm_num
  have h := sw_near (ε := 1 / 199) hr hu0 w hd (by norm_num) (by rw [hx]; exact hxM)
    (by linarith)
  rw [hx] at h
  exact h

theorem sw_dich {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) (hM : 2 ≤ M) (P : Prop) [Decidable P]
    {d : ℝ} (hd : |d| ≤ 1 / 200) :
    (¬P ∧ sw fl (if P then 1 else 0) d = 0) ∨
      (P ∧ |sw fl (if P then 1 else 0) d - 1| ≤ 1 / 190) := by
  by_cases h : P
  · right
    refine ⟨h, ?_⟩
    rw [if_pos h]
    have h1 := sw_b hr hu0 hu1 (1 : ℝ) (1 : ℚ) (by norm_num) hd (by rw [abs_one]; linarith)
    rw [abs_one] at h1
    have h2 := eta_tiny hη
    have h3 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 10000 := by norm_num
    linarith
  · left
    refine ⟨h, ?_⟩
    rw [if_neg h]
    exact sw_zero hr d

theorem ue_prop {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) (hM : 2 ≤ M) (p : Pert)
    (hp : p.Within (1 / 200)) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    (ue fl p w j = 0 ∧ 1 ≤ tokAt w j ∧ tokAt w j ≤ 4) ∨
      ((tokAt w j = 0 ∨ tokAt w j = 5) ∧ |ue fl p w j - 1| ≤ 1 / 190) := by
  have h5 := tok_le w hw j
  have := sw_dich hr hu0 hu1 hη hM (tokAt w j = 0 ∨ tokAt w j = 5) (hp.E (tokAt w j) 0)
  unfold ue rU
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    exact ⟨h2, by omega, by omega⟩
  · right
    exact ⟨h1, h2⟩

theorem ae_prop {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) (hM : 2 ≤ M) (p : Pert)
    (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ) :
    (ae fl p w j = 0 ∧ ¬(tokAt w j = 3 ∨ tokAt w j = 4)) ∨
      ((tokAt w j = 3 ∨ tokAt w j = 4) ∧ |ae fl p w j - 1| ≤ 1 / 190) := by
  have := sw_dich hr hu0 hu1 hη hM (tokAt w j = 3 ∨ tokAt w j = 4) (hp.E (tokAt w j) 1)
  unfold ae rA
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    exact ⟨h2, h1⟩
  · right
    exact ⟨h1, h2⟩

theorem ce_prop {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) (hM : 2 ≤ M) (p : Pert)
    (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ) :
    (ce fl p w j = 0 ∧ ¬(tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4)) ∨
      ((tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4) ∧ |ce fl p w j - 1| ≤ 1 / 190) := by
  have := sw_dich hr hu0 hu1 hη hM (tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4)
    (hp.E (tokAt w j) 2)
  unfold ce rC
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    exact ⟨h2, h1⟩
  · right
    exact ⟨h1, h2⟩

/-- The score in closed form. -/
theorem score_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (Sw Pw : ℝ) (hSw : sw fl (-20) (dA 5 6) = Sw) (hPw : sw fl (-48) (dA 7 0) = Pw)
    (a0 a1 a2 a3 a4 qi qn b0 b1 b2 b3 b4 qk qn' : ℝ)
    (hI1 : fl (fl (Sw * qk)) = fl (Sw * qk))
    (hI2 : fl (fl (Pw * b0)) = fl (Pw * b0)) :
    hh.score fl dA [a0, a1, a2, a3, a4, 1, qi, qn] [b0, b1, b2, b3, b4, 1, qk, qn']
      = fl (fl (Sw * qk) + fl (qn * fl (Pw * b0))) := by
  subst hSw hPw
  simp [Head.score, hh, z8, pdot, rmat, rdot, sw_zero hr, hr.zero, hI1, hI2]

theorem val_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ) (Vw : ℝ)
    (hV : sw fl 1 (dV 1) = Vw) (b0 b1 b2 b3 b4 qk qn : ℝ)
    (hI : fl (fl (Vw * b1)) = fl (Vw * b1)) :
    rdot fl [0, 1, 0, 0, 0, 0, 0, 0] [b0, b1, b2, b3, b4, 1, qk, qn] dV 0 0 = fl (Vw * b1) := by
  subst hV
  simp [rdot, sw_zero hr, hr.zero, hI]

theorem zrow_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ)
    (a b c d e f g h : ℝ) :
    rdot fl z8 [a, b, c, d, e, f, g, h] dV 0 0 = 0 := by
  simp [z8, rdot, sw_zero hr, hr.zero]

noncomputable def Aest (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (i : ℕ) : ℝ :=
  savg fl ex (cand Mask.causal (w.length + 1) i)
    (hscore hh fl (p.A 0 0) (net.init fl p w) i)
    (fun j => rdot fl [0, 1, 0, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 3) 0 0)

theorem attn_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) :
    sattn hh fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, 0, Aest fl ex p w i, 0, 0, 0, 0] := by
  have hV : hh.V = [z8, z8, z8, [0, 1, 0, 0, 0, 0, 0, 0], z8, z8, z8, z8] := rfl
  have hm : hh.mask = Mask.causal := rfl
  have hz : ∀ d : ℕ → ℝ,
      savg fl ex (cand Mask.causal (w.length + 1) i)
        (hscore hh fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl z8 (net.init fl p w j) d 0 0) = 0 := by
    intro d
    apply soft_zeros hr
    intro k _
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact zrow_eq hr d _ _ _ _ _ _ _ _
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz, Aest]

theorem out_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) (A : ℝ)
    (hattn : sattn hh fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, 0, A, 0, 0, 0, 0])
    (Sa Sb Sa' Sb' Sc Sd So G1 G2 H : ℝ)
    (e1 : sw fl (-1) (p.W1 0 0 2) = Sa) (e2 : sw fl 1 (p.W1 0 0 3) = Sb)
    (e3 : sw fl 1 (p.W1 0 1 2) = Sa') (e4 : sw fl (-1) (p.W1 0 1 3) = Sb')
    (e5 : sw fl 1 (p.W2 0 4 0) = Sc) (e6 : sw fl 1 (p.W2 0 4 1) = Sd)
    (e7 : sw fl 1 (p.oW 4) = So)
    (hG1 : fl (fl (Sa * ce fl p w i) + fl (Sb * A)) = G1)
    (hG2 : fl (fl (Sa' * ce fl p w i) + fl (Sb' * A)) = G2)
    (hH : fl (fl (Sc * relu G1) + fl (Sd * relu G2)) = H)
    (hce : fl (ce fl p w i) = ce fl p w i) (hA : fl A = A)
    (i1 : fl (fl (Sa * ce fl p w i)) = fl (Sa * ce fl p w i))
    (i2 : fl G1 = G1)
    (i3 : fl (fl (Sa' * ce fl p w i)) = fl (Sa' * ce fl p w i))
    (i4 : fl G2 = G2)
    (i5 : fl (fl (Sc * relu G1)) = fl (Sc * relu G1))
    (i6 : fl H = H)
    (i7 : fl (fl (So * H)) = fl (So * H)) :
    sout net fl ex p w i = fl (So * H) := by
  subst e1 e2 e3 e4 e5 e6 e7 hG1 hG2 hH
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 0, 0, 0, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  unfold sout srun
  rw [hb, ho, hc]
  simp only [srunFrom, sblock, blk, sheadsApply, hattn]
  simp only [init_eq hr p w hw]
  simp [z8, pos, rdot, radd, raffine, sw_zero hr, hr.zero, hce, hA, i1, i2, i3, i4, i5, i6, i7]

theorem absb {x t e : ℝ} (h : |x - t| ≤ e) (ht : |t| ≤ 1) (he : e ≤ 2) : |x| ≤ 4 := by
  have := abs_sub_abs_le_abs_sub x t
  linarith

theorem fl_step {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hM4 : 4 ≤ M)
    (hε0 : u * 4 + η ≤ 1 / 1000) {x t e : ℝ} (h : |x - t| ≤ e) (ht : |t| ≤ 1) (he : e ≤ 2) :
    |fl x - t| ≤ e + 1 / 1000 := by
  have := hr.near hu0 h (absb h ht he) hM4
  linarith

theorem add_near {x y s t a b : ℝ} (hx : |x - s| ≤ a) (hy : |y - t| ≤ b) :
    |(x + y) - (s + t)| ≤ a + b := by
  have h := abs_add_le (x - s) (y - t)
  have e : x + y - (s + t) = (x - s) + (y - t) := by ring
  rw [e]
  linarith

theorem mul_step {x y s t a b : ℝ} (hx : |x - s| ≤ a) (hy : |y - t| ≤ b) (hs : |s| = 1)
    (ht : |t| ≤ 1) (ha0 : 0 ≤ a) : |x * y - s * t| ≤ a + b + a * b := by
  have h := mul_near hx hy
  rw [hs] at h
  have := mul_le_mul_of_nonneg_left ht ha0
  linarith

theorem relu_eq (x : ℝ) : relu x = max x 0 := rfl

theorem bits_facts (a c : ℝ) (ha : a = 0 ∨ a = 1) (hc : c = 0 ∨ c = 1) :
    |a| ≤ 1 ∧ |c| ≤ 1 ∧ |(-1) * c + 1 * a| ≤ 1 ∧ |1 * c + (-1) * a| ≤ 1 ∧
    (0 ≤ max ((-1) * c + 1 * a) 0 ∧ max ((-1) * c + 1 * a) 0 ≤ 1) ∧
    (0 ≤ max (1 * c + (-1) * a) 0 ∧ max (1 * c + (-1) * a) 0 ≤ 1) ∧
    max ((-1) * c + 1 * a) 0 + max (1 * c + (-1) * a) 0 = |a - c| := by
  rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num [max_def]

theorem fin_bound {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hM4 : 4 ≤ M)
    (hε0 : u * 4 + η ≤ 1 / 1000)
    (a c ce A Sa Sb Sa' Sb' Sc Sd So G1 G2 H : ℝ)
    (ha : a = 0 ∨ a = 1) (hc : c = 0 ∨ c = 1)
    (hce : |ce - c| ≤ 1 / 100) (hA : |A - a| ≤ 1 / 30)
    (hSa : |Sa - (-1)| ≤ 1 / 190) (hSb : |Sb - 1| ≤ 1 / 190)
    (hSa' : |Sa' - 1| ≤ 1 / 190) (hSb' : |Sb' - (-1)| ≤ 1 / 190)
    (hSc : |Sc - 1| ≤ 1 / 190) (hSd : |Sd - 1| ≤ 1 / 190) (hSo : |So - 1| ≤ 1 / 190)
    (hG1 : fl (fl (Sa * ce) + fl (Sb * A)) = G1)
    (hG2 : fl (fl (Sa' * ce) + fl (Sb' * A)) = G2)
    (hH : fl (fl (Sc * relu G1) + fl (Sd * relu G2)) = H) :
    |fl (So * H) - |a - c|| ≤ 1 / 4 ∧
      fl (fl (Sa * ce)) = fl (Sa * ce) ∧ fl G1 = G1 ∧
      fl (fl (Sa' * ce)) = fl (Sa' * ce) ∧ fl G2 = G2 ∧
      fl (fl (Sc * relu G1)) = fl (Sc * relu G1) ∧ fl H = H ∧
      fl (fl (So * H)) = fl (So * H) := by
  obtain ⟨ha1, hc1, hg1, hg2, ⟨hr1a, hr1b⟩, ⟨hr2a, hr2b⟩, hsum⟩ := bits_facts a c ha hc
  have n1 : |(-1 : ℝ)| = 1 := by norm_num
  have n2 : |(1 : ℝ)| = 1 := by norm_num
  have n1c : |(-1) * c| ≤ 1 := by rw [neg_mul, one_mul, abs_neg]; exact hc1
  have n1a : |(-1) * a| ≤ 1 := by rw [neg_mul, one_mul, abs_neg]; exact ha1
  have n2c : |1 * c| ≤ 1 := by rw [one_mul]; exact hc1
  have n2a : |1 * a| ≤ 1 := by rw [one_mul]; exact ha1
  have e0 : (0 : ℝ) ≤ 1 / 190 := by norm_num
  -- G1 ≈ a - c
  have m1 := mul_step hSa hce n1 hc1 e0
  have m2 := mul_step hSb hA n2 ha1 e0
  have f1 := fl_step hr hu0 hM4 hε0 m1 n1c (by norm_num)
  have f2 := fl_step hr hu0 hM4 hε0 m2 n2a (by norm_num)
  have f3 := fl_step hr hu0 hM4 hε0 (add_near f1 f2) hg1 (by norm_num)
  have i1 := hr.idem _ (le_trans (absb m1 n1c (by norm_num)) hM4)
  have i2 := hr.idem _ (le_trans (absb (add_near f1 f2) hg1 (by norm_num)) hM4)
  rw [hG1] at f3 i2
  -- G2 ≈ c - a
  have m3 := mul_step hSa' hce n2 hc1 e0
  have m4 := mul_step hSb' hA n1 ha1 e0
  have f4 := fl_step hr hu0 hM4 hε0 m3 n2c (by norm_num)
  have f5 := fl_step hr hu0 hM4 hε0 m4 n1a (by norm_num)
  have f6 := fl_step hr hu0 hM4 hε0 (add_near f4 f5) hg2 (by norm_num)
  have i3 := hr.idem _ (le_trans (absb m3 n2c (by norm_num)) hM4)
  have i4 := hr.idem _ (le_trans (absb (add_near f4 f5) hg2 (by norm_num)) hM4)
  rw [hG2] at f6 i4
  -- relu
  have r1 : |relu G1 - max ((-1) * c + 1 * a) 0| ≤ 1 / 10 := by
    rw [relu_eq]
    have := abs_max_sub_max_le_abs G1 ((-1) * c + 1 * a) 0
    have h2 : |G1 - ((-1) * c + 1 * a)| ≤ 1 / 10 := by
      refine le_trans f3 ?_
      norm_num
    linarith
  have r2 : |relu G2 - max (1 * c + (-1) * a) 0| ≤ 1 / 10 := by
    rw [relu_eq]
    have := abs_max_sub_max_le_abs G2 (1 * c + (-1) * a) 0
    have h2 : |G2 - (1 * c + (-1) * a)| ≤ 1 / 10 := by
      refine le_trans f6 ?_
      norm_num
    linarith
  have rt1 : |max ((-1) * c + 1 * a) 0| ≤ 1 := by
    rw [abs_of_nonneg hr1a]; exact hr1b
  have rt2 : |max (1 * c + (-1) * a) 0| ≤ 1 := by
    rw [abs_of_nonneg hr2a]; exact hr2b
  -- products with Sc, Sd
  have m5 := mul_step hSc r1 n2 rt1 e0
  have m6 := mul_step hSd r2 n2 rt2 e0
  have f7 := fl_step hr hu0 hM4 hε0 m5 (by rw [one_mul]; exact rt1) (by norm_num)
  have f8 := fl_step hr hu0 hM4 hε0 m6 (by rw [one_mul]; exact rt2) (by norm_num)
  have hT : 1 * max ((-1) * c + 1 * a) 0 + 1 * max (1 * c + (-1) * a) 0 = |a - c| := by
    rw [one_mul, one_mul]; exact hsum
  have hTb : |1 * max ((-1) * c + 1 * a) 0 + 1 * max (1 * c + (-1) * a) 0| ≤ 1 := by
    rw [hT]
    rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num
  have f9 := fl_step hr hu0 hM4 hε0 (add_near f7 f8) hTb (by norm_num)
  have i5 := hr.idem _ (le_trans (absb m5 (by rw [one_mul]; exact rt1) (by norm_num)) hM4)
  have i6 := hr.idem _ (le_trans (absb (add_near f7 f8) hTb (by norm_num)) hM4)
  rw [hH] at f9 i6
  rw [hT] at f9
  have hTb' : |(|a - c|)| ≤ 1 := by rw [← hT]; exact hTb
  have m7 := mul_step hSo f9 n2 hTb' e0
  have hTb2 : |1 * |a - c|| ≤ 1 := by rw [one_mul]; exact hTb'
  have f10 := fl_step hr hu0 hM4 hε0 m7 hTb2 (by norm_num)
  have e1 : (1 : ℝ) * |a - c| = |a - c| := one_mul _
  have i7 := hr.idem _ (le_trans (absb m7 hTb2 (by norm_num)) hM4)
  rw [e1] at f10
  exact ⟨le_trans f10 (by norm_num), i1, i2, i3, i4, i5, i6, i7⟩

theorem code_ne (t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ 4) : code t ≠ 0 := by
  interval_cases t <;> simp [code]

theorem code_five : code 5 = 0 := by simp [code]

theorem code_two (t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ 4) : code t = 2 ↔ (t = 3 ∨ t = 4) := by
  interval_cases t <;> simp [code]

theorem tok_pos (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ w.length) : 1 ≤ tokAt w j ∧ tokAt w j ≤ 5 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Lane4.Seq.tokAt_succ w k (by omega)]
  exact hw _ (List.getElem_mem (by omega))

theorem firstc_succ (w : List ℕ) (i : ℕ) (h : i < w.length) :
    firstc (w.take (i + 1)) = if firstc (w.take i) = 0 then code w[i] else firstc (w.take i) := by
  rw [List.take_succ, List.getElem?_eq_getElem h]
  simp [firstc, List.foldl_append]

theorem first_struct (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) :
    ∀ i, i ≤ w.length →
      (firstc (w.take i) = 0 ∧ ∀ k, 1 ≤ k → k ≤ i → tokAt w k = 5) ∨
      (∃ j, 1 ≤ j ∧ j ≤ i ∧ tokAt w j ≤ 4 ∧ (∀ k, 1 ≤ k → k < j → tokAt w k = 5) ∧
        firstc (w.take i) = code (tokAt w j)) := by
  intro i
  induction i with
  | zero =>
    intro _
    left
    exact ⟨by simp [firstc], fun k hk1 hk2 => by omega⟩
  | succ i ih =>
    intro hi
    have hlt : i < w.length := by omega
    have htk : tokAt w (i + 1) = w[i] := Lane4.Seq.tokAt_succ w i hlt
    have hmem : 1 ≤ w[i] ∧ w[i] ≤ 5 := hw _ (List.getElem_mem hlt)
    have hF := firstc_succ w i hlt
    rcases ih (by omega) with ⟨h0, hall⟩ | ⟨j, hj1, hj2, hj3, hj4, hj5⟩
    · rw [h0, if_pos rfl] at hF
      by_cases h5 : w[i] = 5
      · left
        refine ⟨by rw [hF, h5, code_five], ?_⟩
        intro k hk1 hk2
        by_cases hk : k ≤ i
        · exact hall k hk1 hk
        · have : k = i + 1 := by omega
          rw [this, htk, h5]
      · right
        refine ⟨i + 1, by omega, le_refl _, by rw [htk]; omega, ?_, by rw [hF, htk]⟩
        intro k hk1 hk2
        exact hall k hk1 (by omega)
    · right
      refine ⟨j, hj1, by omega, hj3, hj4, ?_⟩
      have hp := tok_pos w hw j hj1 (by omega)
      have hne := code_ne (tokAt w j) hp.1 hj3
      rw [hF, hj5, if_neg hne]

theorem getD_tok (w : List ℕ) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    w.getD (i - 1) 0 = tokAt w i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Lane4.Seq.tokAt_succ w k (by omega)]
  simp [List.getD_eq_getElem?_getD, show k < w.length by omega]

theorem xor_abs (a c : ℕ) (ha : a = 0 ∨ a = 1) (hc : c = 0 ∨ c = 1) :
    (((a + c) % 2 : ℕ) : ℝ) = |(a : ℝ) - (c : ℝ)| := by
  rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num

theorem target_abs (w : List ℕ) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    ((target w i : ℕ) : ℝ) =
      |(((if firstc (w.take i) = 2 then 1 else 0 : ℕ)) : ℝ) - ((cbit (tokAt w i) : ℕ) : ℝ)| := by
  have hc := getD_tok w i h1 h2
  unfold target
  rw [hc]
  exact xor_abs _ _ (by split_ifs <;> simp) (by unfold cbit; split_ifs <;> simp)

set_option maxHeartbeats 1600000 in
theorem Aest_near {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (he : ExpM u η ex)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2 ^ 149)
    (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5)
    (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (hnη : η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100)
    (hM : 2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    |Aest fl ex p w i - ((if firstc (w.take i) = 2 then 1 else 0 : ℕ) : ℝ)| ≤ 1 / 30 ∧
      fl (Aest fl ex p w i) = Aest fl ex p w i := by
  have hn1 : 1 ≤ w.length + 1 := by omega
  have hnR : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hn1
  have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
    have := range_lin hM hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have h300 : 300 * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ((w.length + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hnN : u * N ≤ 1 / 256 := by rw [hN]; exact hn
  have hNge : 1 ≤ N := by rw [hN]; exact hnR
  have hNM : 300 * N ≤ M := by rw [hN]; exact h300
  have h2M : (2 : ℝ) ≤ M := by linarith
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hu6 : u ≤ 1 / 10 ^ 6 := le_trans hu1 (by norm_num)
  -- stored weights
  have c20 : |(-20 : ℝ)| = 20 := by norm_num
  have c48 : |(-48 : ℝ)| = 48 := by norm_num
  have c1 : |(1 : ℝ)| = 1 := by norm_num
  obtain ⟨Sw, hSw⟩ : ∃ Sw : ℝ, sw fl (-20) (p.A 0 0 5 6) = Sw := ⟨_, rfl⟩
  obtain ⟨Pw, hPw⟩ : ∃ Pw : ℝ, sw fl (-48) (p.A 0 0 7 0) = Pw := ⟨_, rfl⟩
  obtain ⟨Vw, hVw⟩ : ∃ Vw : ℝ, sw fl 1 (p.V 0 0 3 1) = Vw := ⟨_, rfl⟩
  have hSw' := sw_b hr hu0 hu1 (-20) (-20) (by norm_num) (hp.A 0 0 5 6) (by rw [c20]; linarith)
  have hPw' := sw_b hr hu0 hu1 (-48) (-48) (by norm_num) (hp.A 0 0 7 0) (by rw [c48]; linarith)
  have hVw' := sw_b hr hu0 hu1 (1 : ℝ) (1 : ℚ) (by norm_num) (hp.V 0 0 3 1) (by rw [c1]; linarith)
  rw [hSw, c20] at hSw'
  rw [hPw, c48] at hPw'
  rw [hVw, c1] at hVw'
  obtain ⟨hSw1, hSw2⟩ := abs_le.mp hSw'
  obtain ⟨hPw1, hPw2⟩ := abs_le.mp hPw'
  obtain ⟨hVw1, hVw2⟩ := abs_le.mp hVw'
  have hSwA : -101 / 5 ≤ Sw := by linarith
  have hSwB : Sw ≤ -99 / 5 := by linarith
  have hPwA : -483 / 10 ≤ Pw := by linarith
  have hPwB : Pw ≤ -477 / 10 := by linarith
  have hVwA : 1 - 1 / 190 ≤ Vw := by linarith
  have hVwB : Vw ≤ 1 + 1 / 190 := by linarith
  -- positions
  have hpl : ∀ k : ℕ, k ≤ w.length + 1 → 0 ≤ fl (k : ℝ) ∧ fl (k : ℝ) ≤ N + 1 / 100 := by
    intro k hk
    have := hr.pos_le hu0 hη hk hn hnM
    refine ⟨this.1, ?_⟩
    rw [hN]
    exact this.2
  have hpn : ∀ k : ℕ, k ≤ w.length + 1 → |fl (k : ℝ) - k| ≤ 1 / 200 :=
    fun k hk => hr.pos_near hu0 hη hk hn hnM
  have hpg : ∀ a b : ℕ, a ≤ b → b ≤ w.length + 1 →
      fl (a : ℝ) + ((b : ℝ) - a) - 1 / 100 ≤ fl (b : ℝ) :=
    fun a b hab hb => hr.pos_gap hu0 hη hab hb hn hnM
  have hfN := hpl (w.length + 1) le_rfl
  have hfNn := hpn (w.length + 1) le_rfl
  obtain ⟨fN, hfNdef⟩ : ∃ fN : ℝ, fN = fl ((w.length + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hfN0 : 0 ≤ fN := by rw [hfNdef]; exact hfN.1
  have hfNhi : fN ≤ N + 1 / 100 := by rw [hfNdef]; exact hfN.2
  have hfNlo : N - 1 / 200 ≤ fN := by
    have := (abs_le.mp hfNn).1
    rw [hfNdef, hN]
    linarith
  -- features
  have hUb : ∀ k : ℕ, |ue fl p w k| ≤ 101 / 100 := by
    intro k
    rcases ue_prop hr hu0 hu1 hη h2M p hp w hw k with ⟨h1, _, _⟩ | ⟨_, h2⟩
    · rw [h1]; norm_num
    · have h3 := abs_le.mp h2
      rw [abs_le]
      constructor <;> linarith [h3.1, h3.2]
  have hXb : ∀ k : ℕ, k ≤ w.length + 1 → |Sw * fl (k : ℝ)| ≤ 21 * N := by
    intro k hk
    obtain ⟨h0, h1⟩ := hpl k hk
    rw [abs_mul, abs_of_nonneg h0]
    have hs : |Sw| ≤ 101 / 5 := by
      rw [abs_le]
      constructor <;> linarith
    have := mul_le_mul hs h1 h0 (by norm_num)
    linarith
  have hQb : ∀ k : ℕ, |Pw * ue fl p w k| ≤ 49 := by
    intro k
    have hs : |Pw| ≤ 483 / 10 := by
      rw [abs_le]
      constructor <;> linarith
    rw [abs_mul]
    have := mul_le_mul hs (hUb k) (abs_nonneg _) (by norm_num)
    linarith
  have hsk : ∀ k : ℕ, k ≤ w.length + 1 →
      hscore hh fl (p.A 0 0) (net.init fl p w) i k
        = fl (fl (Sw * fl (k : ℝ)) + fl (fN * fl (Pw * ue fl p w k))) := by
    intro k hk
    rw [hfNdef]
    simp only [hscore, init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact score_eq hr (p.A 0 0) Sw Pw hSw hPw _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (hr.idem _ (le_trans (hXb k hk) (by linarith)))
      (hr.idem _ (le_trans (hQb k) (by linarith)))
  have hsm : ∀ k : ℕ, k ≤ w.length + 1 → ue fl p w k = 0 →
      hscore hh fl (p.A 0 0) (net.init fl p w) i k = fl (Sw * fl (k : ℝ)) := by
    intro k hk hu
    rw [hsk k hk, hu]
    simp only [mul_zero, hr.zero, add_zero]
    exact hr.idem _ (le_trans (hXb k hk) (by linarith))
  have hQa : ∀ k : ℕ, |fl (Pw * ue fl p w k)| ≤ 50 := by
    intro k
    have := hr.bound hu0 (hQb k) (by linarith : (49 : ℝ) ≤ M)
    linarith
  have hFQ : ∀ k : ℕ, |fN * fl (Pw * ue fl p w k)| ≤ 51 * N := by
    intro k
    rw [abs_mul, abs_of_nonneg hfN0]
    have := mul_le_mul hfNhi (hQa k) (abs_nonneg _) (by linarith)
    linarith
  have hYa : ∀ k : ℕ, |fl (fN * fl (Pw * ue fl p w k))| ≤ 52 * N := by
    intro k
    have := hr.bound hu0 (hFQ k) (by linarith : 51 * N ≤ M)
    linarith
  have hXa : ∀ k : ℕ, k ≤ w.length + 1 → |fl (Sw * fl (k : ℝ))| ≤ 22 * N := by
    intro k hk
    have := hr.bound hu0 (hXb k hk) (by linarith : 21 * N ≤ M)
    linarith
  have hSsum : ∀ k : ℕ, k ≤ w.length + 1 →
      |fl (Sw * fl (k : ℝ)) + fl (fN * fl (Pw * ue fl p w k))| ≤ 74 * N := by
    intro k hk
    have := abs_add_le (fl (Sw * fl (k : ℝ))) (fl (fN * fl (Pw * ue fl p w k)))
    linarith [hXa k hk, hYa k]
  have hsa : ∀ k : ℕ, k ≤ w.length + 1 →
      |hscore hh fl (p.A 0 0) (net.init fl p w) i k| ≤ 80 * N := by
    intro k hk
    rw [hsk k hk]
    have := hr.bound hu0 (hSsum k hk) (by linarith : 74 * N ≤ M)
    linarith
  -- values
  have hVa : ∀ k : ℕ, |Vw * ae fl p w k| ≤ 21 / 20 := by
    intro k
    have hV : |Vw| ≤ 101 / 100 := by
      rw [abs_le]
      constructor <;> linarith
    have hA : |ae fl p w k| ≤ 101 / 100 := by
      rcases ae_prop hr hu0 hu1 hη h2M p hp w k with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [h1]; norm_num
      · have h3 := abs_le.mp h2
        rw [abs_le]
        constructor <;> linarith [h3.1, h3.2]
    rw [abs_mul]
    have := mul_le_mul hV hA (abs_nonneg _) (by norm_num)
    linarith
  have hfk : ∀ k : ℕ, rdot fl [0, 1, 0, 0, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 3) 0 0
      = fl (Vw * ae fl p w k) := by
    intro k
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact val_eq hr (p.V 0 0 3) Vw hVw _ _ _ _ _ _ _
      (hr.idem _ (le_trans (hVa k) (by linarith)))
  have hfBk : ∀ k : ℕ,
      |rdot fl [0, 1, 0, 0, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 3) 0 0| ≤ 11 / 10 := by
    intro k
    rw [hfk k]
    have := hr.bound hu0 (hVa k) (by linarith : (21 / 20 : ℝ) ≤ M)
    linarith
  have hlen : (cand Mask.causal (w.length + 1) i).length ≤ w.length + 1 := by
    simp [cand]
    omega
  have hAe : Aest fl ex p w i = savg fl ex (cand Mask.causal (w.length + 1) i)
      (hscore hh fl (p.A 0 0) (net.init fl p w) i)
      (fun j => rdot fl [0, 1, 0, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 3) 0 0) := rfl
  rcases first_struct w hw i hi with ⟨hF0, hall⟩ | ⟨j0, hj1, hj2, hj3, hj4, hF⟩
  · -- no marked token among 1..i
    have hz : Aest fl ex p w i = 0 := by
      rw [hAe]
      apply soft_zeros hr
      intro k hk
      rw [Lane4.Seq.mem_cand_causal] at hk
      show rdot fl [0, 1, 0, 0, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 3) 0 0 = 0
      have hk5 : tokAt w k = 0 ∨ tokAt w k = 5 := by
        by_cases h0 : k = 0
        · left
          rw [h0]
          exact Lane4.Seq.tokAt_zero w
        · right
          exact hall k (by omega) hk
      have hae0 : ae fl p w k = 0 := by
        rcases ae_prop hr hu0 hu1 hη h2M p hp w k with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact h1
        · omega
      rw [hfk k, hae0]
      simp [hr.zero]
    rw [hz, hF0]
    norm_num [hr.zero]
  · -- first marked token at j0
    have hjn : j0 ≤ w.length + 1 := by omega
    have hp0 := tok_pos w hw j0 hj1 (by omega)
    have hue0 : ue fl p w j0 = 0 := by
      rcases ue_prop hr hu0 hu1 hη h2M p hp w j0 with ⟨h1, _, _⟩ | ⟨h1, _⟩
      · exact h1
      · omega
    have hsj0 := hsm j0 hjn hue0
    have hj : j0 ∈ cand Mask.causal (w.length + 1) i := by
      rw [Lane4.Seq.mem_cand_causal]
      exact hj2
    have hjR : (j0 : ℝ) + 1 ≤ N := by
      rw [hN]
      exact_mod_cast (show j0 + 1 ≤ w.length + 1 by omega)
    have hgap : ∀ k ∈ cand Mask.causal (w.length + 1) i, k ≠ j0 →
        hscore hh fl (p.A 0 0) (net.init fl p w) i k
          ≤ hscore hh fl (p.A 0 0) (net.init fl p w) i j0 - 16 * (ndist j0 k : ℝ) := by
      intro k hk hne
      rw [Lane4.Seq.mem_cand_causal] at hk
      have hkn : k ≤ w.length + 1 := by omega
      rw [hsj0, ndist_cast]
      obtain ⟨hk0, hk1⟩ := hpl k hkn
      obtain ⟨hj0', hj1'⟩ := hpl j0 hjn
      have hXgap := hr.gap hu0 (hXb k hkn) (hXb j0 hjn) (by linarith : 21 * N ≤ M)
      have hpk := abs_le.mp (hpn k hkn)
      have hpj := abs_le.mp (hpn j0 hjn)
      have hkc : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hun : u * (21 * N) = 21 * (u * N) := by ring
      rcases ue_prop hr hu0 hu1 hη h2M p hp w hw k with ⟨hku0, hkt1, hkt2⟩ | ⟨hkt, hku1⟩
      · -- marked k: it must come after j0
        have hkpos : 1 ≤ k := by
          by_contra h0
          have h00 : k = 0 := by omega
          rw [h00, Lane4.Seq.tokAt_zero] at hkt1
          omega
        have hjk : j0 < k := by
          by_contra hcon
          have hlt : k < j0 := by omega
          have h5 := hj4 k hkpos hlt
          omega
        rw [hsm k hkn hku0]
        have hd1 : (j0 : ℝ) + 1 ≤ k := by exact_mod_cast hjk
        have hg := hpg j0 k (le_of_lt hjk) hkn
        have hD0 : 0 ≤ fl (k : ℝ) - fl (j0 : ℝ) := by linarith
        have hSD := mul_le_mul_of_nonneg_right (show (99 : ℝ) / 5 ≤ -Sw by linarith) hD0
        rw [abs_of_nonpos (by linarith : (j0 : ℝ) - k ≤ 0)]
        linarith
      · -- unmarked k
        have hue_lo := (abs_le.mp hku1).1
        have hq := mul_le_mul (show (477 : ℝ) / 10 ≤ -Pw by linarith)
          (show (99 : ℝ) / 100 ≤ ue fl p w k by linarith) (by norm_num) (by linarith)
        have hQerr := hr.abs hu0 (hQb k) (by linarith : (49 : ℝ) ≤ M)
        have hQ1 : fl (Pw * ue fl p w k) ≤ -47 := by
          have := (abs_le.mp hQerr).2
          linarith
        have hfQ := mul_le_mul_of_nonneg_left hQ1 hfN0
        have hYup := hr.upper hu0 (hFQ k) (by linarith : 51 * N ≤ M)
        have hSup := hr.upper hu0 (hSsum k hkn) (by linarith : 74 * N ≤ M)
        rw [hsk k hkn]
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hlt' : (k : ℝ) + 1 ≤ j0 := by exact_mod_cast hlt
          have hg := hpg k j0 (le_of_lt hlt) hjn
          have hE0 : 0 ≤ fl (j0 : ℝ) - fl (k : ℝ) := by linarith
          have hSE := mul_le_mul_of_nonneg_right (show (-101 : ℝ) / 5 ≤ Sw by linarith) hE0
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (j0 : ℝ) - k)]
          linarith
        · have hgt' : (j0 : ℝ) + 1 ≤ k := by exact_mod_cast hgt
          have hg := hpg j0 k (le_of_lt hgt) hkn
          have hD0 : 0 ≤ fl (k : ℝ) - fl (j0 : ℝ) := by linarith
          have hSD := mul_le_mul_of_nonneg_right (show (99 : ℝ) / 5 ≤ -Sw by linarith) hD0
          rw [abs_of_nonpos (by linarith : (j0 : ℝ) - k ≤ 0)]
          linarith
    have hSb : ∀ k ∈ cand Mask.causal (w.length + 1) i,
        |hscore hh fl (p.A 0 0) (net.init fl p w) i k| ≤ 80 * N := by
      intro k hk
      rw [Lane4.Seq.mem_cand_causal] at hk
      exact hsa k (by omega)
    have hfB : ∀ k ∈ cand Mask.causal (w.length + 1) i,
        |(fun j => rdot fl [0, 1, 0, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 3) 0 0) k|
          ≤ 11 / 10 := by
      intro k _
      exact hfBk k
    obtain ⟨hA1, hA2⟩ := soft_near hr he hu0 hu1 hη0 hη (Lane4.Seq.cand_nodup _ _ _) hlen hn hnη
      hj hgap hSb (by linarith) hfB (by linarith)
    have hA1' : |Aest fl ex p w i
        - rdot fl [0, 1, 0, 0, 0, 0, 0, 0] (net.init fl p w j0) (p.V 0 0 3) 0 0|
        ≤ 11 / 10 / 100 + 1 / 2 ^ 90 := hA1
    have hA2' : fl (Aest fl ex p w i) = Aest fl ex p w i := hA2
    have hfj0 := hfk j0
    rcases ae_prop hr hu0 hu1 hη h2M p hp w j0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hn2 : ¬ code (tokAt w j0) = 2 := by
        rw [code_two _ hp0.1 hj3]
        exact h2
      have hab : ((if firstc (w.take i) = 2 then 1 else 0 : ℕ) : ℝ) = 0 := by
        rw [hF, if_neg hn2]
        norm_num
      rw [hab]
      refine ⟨?_, hA2'⟩
      rw [hfj0, h1] at hA1'
      simp only [mul_zero, hr.zero, sub_zero] at hA1'
      have h3 : (11 / 10 : ℝ) / 100 + 1 / 2 ^ 90 ≤ 1 / 30 := by norm_num
      rw [sub_zero]
      linarith
    · have hp2 : code (tokAt w j0) = 2 := (code_two _ hp0.1 hj3).mpr h1
      have hab : ((if firstc (w.take i) = 2 then 1 else 0 : ℕ) : ℝ) = 1 := by
        rw [hF, if_pos hp2]
        norm_num
      rw [hab]
      refine ⟨?_, hA2'⟩
      have hm := mul_step (x := Vw) (y := ae fl p w j0) (s := 1) (t := 1) (a := 1 / 190)
        (b := 1 / 190) (by rw [abs_le]; constructor <;> linarith) h2 c1 (by norm_num)
        (by norm_num)
      have hnr := hr.near hu0 hm (hVa j0) (by linarith : (21 / 20 : ℝ) ≤ M)
      have e11 : (1 : ℝ) * 1 = 1 := by norm_num
      rw [e11] at hnr
      rw [hfj0] at hA1'
      have h5 := abs_sub_le (Aest fl ex p w i) (fl (Vw * ae fl p w j0)) 1
      have h3 : (11 / 10 : ℝ) / 100 + 1 / 2 ^ 90 ≤ 1 / 90 := by norm_num
      linarith

theorem sw_one {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) (hM : 2 ≤ M) (w : ℚ) (x : ℝ)
    (hx : (w : ℝ) = x) (hx1 : |x| = 1) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    |sw fl w d - x| ≤ 1 / 190 := by
  have h := sw_b hr hu0 hu1 x w hx hd (by rw [hx1]; linarith)
  rw [hx1] at h
  have h2 := eta_tiny hη
  have h3 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 10000 := by norm_num
  linarith

theorem cbit_eq (t : ℕ) : cbit t = if (t = 2 ∨ t = 3 ∨ t = 4) then 1 else 0 := by
  unfold cbit
  split_ifs <;> omega

theorem fl_ce {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hM : 2 ≤ M) (p : Pert)
    (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ) : fl (ce fl p w j) = ce fl p w j := by
  unfold ce
  exact fl_sw hr _ (hp.E _ 2) (by norm_num)
    (by unfold rC; split_ifs <;> norm_num <;> linarith)

set_option maxHeartbeats 1600000 in
theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη p hp w hw hn hnη hM i hi1 hi
  obtain ⟨hA1, hA2⟩ := Aest_near hr he hu0 hu1 hη0 hη p hp w hw hn hnη hM i hi1 hi
  have hattn := attn_eq (ex := ex) hr p w hw i
  have hn1 : 1 ≤ w.length + 1 := by omega
  have h300 : (300 : ℝ) ≤ M := range_const hM hn1 (by norm_num)
  have h2M : (2 : ℝ) ≤ M := by linarith
  have hM4 : (4 : ℝ) ≤ M := by linarith
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hu6 : u ≤ 1 / 10 ^ 6 := le_trans hu1 (by norm_num)
  have hε0 : u * 4 + η ≤ 1 / 1000 := by linarith
  obtain ⟨Sa, e1⟩ : ∃ Sa : ℝ, sw fl (-1) (p.W1 0 0 2) = Sa := ⟨_, rfl⟩
  obtain ⟨Sb, e2⟩ : ∃ Sb : ℝ, sw fl 1 (p.W1 0 0 3) = Sb := ⟨_, rfl⟩
  obtain ⟨Sa', e3⟩ : ∃ Sa' : ℝ, sw fl 1 (p.W1 0 1 2) = Sa' := ⟨_, rfl⟩
  obtain ⟨Sb', e4⟩ : ∃ Sb' : ℝ, sw fl (-1) (p.W1 0 1 3) = Sb' := ⟨_, rfl⟩
  obtain ⟨Sc, e5⟩ : ∃ Sc : ℝ, sw fl 1 (p.W2 0 4 0) = Sc := ⟨_, rfl⟩
  obtain ⟨Sd, e6⟩ : ∃ Sd : ℝ, sw fl 1 (p.W2 0 4 1) = Sd := ⟨_, rfl⟩
  obtain ⟨So, e7⟩ : ∃ So : ℝ, sw fl 1 (p.oW 4) = So := ⟨_, rfl⟩
  have hSa := sw_one hr hu0 hu1 hη h2M (-1 : ℚ) (-1 : ℝ) (by norm_num) (by norm_num)
    (hp.W1 0 0 2)
  have hSb := sw_one hr hu0 hu1 hη h2M (1 : ℚ) (1 : ℝ) (by norm_num) (by norm_num)
    (hp.W1 0 0 3)
  have hSa' := sw_one hr hu0 hu1 hη h2M (1 : ℚ) (1 : ℝ) (by norm_num) (by norm_num)
    (hp.W1 0 1 2)
  have hSb' := sw_one hr hu0 hu1 hη h2M (-1 : ℚ) (-1 : ℝ) (by norm_num) (by norm_num)
    (hp.W1 0 1 3)
  have hSc := sw_one hr hu0 hu1 hη h2M (1 : ℚ) (1 : ℝ) (by norm_num) (by norm_num)
    (hp.W2 0 4 0)
  have hSd := sw_one hr hu0 hu1 hη h2M (1 : ℚ) (1 : ℝ) (by norm_num) (by norm_num)
    (hp.W2 0 4 1)
  have hSo := sw_one hr hu0 hu1 hη h2M (1 : ℚ) (1 : ℝ) (by norm_num) (by norm_num)
    (hp.oW 4)
  rw [e1] at hSa
  rw [e2] at hSb
  rw [e3] at hSa'
  rw [e4] at hSb'
  rw [e5] at hSc
  rw [e6] at hSd
  rw [e7] at hSo
  have hab01 : ((if firstc (w.take i) = 2 then 1 else 0 : ℕ) : ℝ) = 0 ∨
      ((if firstc (w.take i) = 2 then 1 else 0 : ℕ) : ℝ) = 1 := by
    by_cases h : firstc (w.take i) = 2
    · rw [if_pos h]
      norm_num
    · rw [if_neg h]
      norm_num
  have hcb01 : ((cbit (tokAt w i) : ℕ) : ℝ) = 0 ∨ ((cbit (tokAt w i) : ℕ) : ℝ) = 1 := by
    rw [cbit_eq]
    by_cases h : (tokAt w i = 2 ∨ tokAt w i = 3 ∨ tokAt w i = 4)
    · rw [if_pos h]
      norm_num
    · rw [if_neg h]
      norm_num
  have hce : |ce fl p w i - ((cbit (tokAt w i) : ℕ) : ℝ)| ≤ 1 / 100 := by
    rw [cbit_eq]
    rcases ce_prop hr hu0 hu1 hη h2M p hp w i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_neg h2, h1]
      norm_num
    · rw [if_pos h1, Nat.cast_one]
      linarith
  obtain ⟨G1, hG1⟩ : ∃ G1 : ℝ, fl (fl (Sa * ce fl p w i) + fl (Sb * Aest fl ex p w i)) = G1 :=
    ⟨_, rfl⟩
  obtain ⟨G2, hG2⟩ : ∃ G2 : ℝ, fl (fl (Sa' * ce fl p w i) + fl (Sb' * Aest fl ex p w i)) = G2 :=
    ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℝ, fl (fl (Sc * relu G1) + fl (Sd * relu G2)) = H := ⟨_, rfl⟩
  obtain ⟨hFb, hF1, hF2, hF3, hF4, hF5, hF6, hF7⟩ :=
    fin_bound hr hu0 hM4 hε0 ((if firstc (w.take i) = 2 then 1 else 0 : ℕ) : ℝ)
      ((cbit (tokAt w i) : ℕ) : ℝ) (ce fl p w i) (Aest fl ex p w i) Sa Sb Sa' Sb' Sc Sd So
      G1 G2 H hab01 hcb01 hce hA1 hSa hSb hSa' hSb' hSc hSd hSo hG1 hG2 hH
  rw [out_eq hr p w hw i (Aest fl ex p w i) hattn Sa Sb Sa' Sb' Sc Sd So G1 G2 H e1 e2 e3 e4 e5
    e6 e7 hG1 hG2 hH (fl_ce hr h2M p hp w i) hA2 hF1 hF2 hF3 hF4 hF5 hF6 hF7,
    target_abs w i hi1 hi]
  exact hFb

end Lane4.Case
