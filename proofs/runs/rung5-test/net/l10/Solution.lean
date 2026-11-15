namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false

/-- State: [val, res, unm, 1, fl i, fl n] (width 6). -/
def z6 : List ℚ := [0, 0, 0, 0, 0, 0]

/-- Causal head. Score of key j = 17 * pos j - 40 * n * unm j (unm = 1 for unmarked keys).
Value: the key's `val` is written into slot `res`. -/
def hd : Head :=
  { A := [z6, z6, z6, [0, 0, 0, 0, 17, 0], z6, [0, 0, -40, 0, 0, 0]],
    V := [z6, [1, 0, 0, 0, 0, 0], z6, z6, z6, z6],
    mask := Mask.causal }

def blk : Block :=
  { heads := [hd], W1 := [], b1 := [], W2 := [[], [], [], [], [], []], b2 := z6 }

def net : TNet :=
  { embed := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [1, 0, 0], [3, 0, 0], [1, 0, 0]],
    blocks := [blk],
    outW := [0, 1, 0, 0, 0, 0],
    outB := 0 }

def vq (t : ℕ) : ℚ := ((val t : ℕ) : ℚ)
def uq (t : ℕ) : ℚ := if t ≤ 2 then 1 else 0

noncomputable def ev (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (vq (tokAt w j)) (p.E (tokAt w j) 0)

noncomputable def eu (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (uq (tokAt w j)) (p.E (tokAt w j) 2)

theorem val_small (t : ℕ) (h : t ≤ 2) : val t = 0 := by
  interval_cases t <;> simp [val]

theorem val_le (t : ℕ) (h : t ≤ 5) : val t ≤ 3 := by
  interval_cases t <;> simp [val]

theorem val_zero_iff (t : ℕ) (h : t ≤ 5) : val t = 0 ↔ t ≤ 2 := by
  interval_cases t <;> simp [val]

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem ev_small {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ) (j : ℕ)
    (h : tokAt w j ≤ 2) : ev fl p w j = 0 := by
  unfold ev vq
  rw [val_small _ h]
  simp [sw_zero hr]

theorem eu_small (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) (h : tokAt w j ≤ 2) :
    eu fl p w j = sw fl 1 (p.E (tokAt w j) 2) := by
  unfold eu uq
  rw [if_pos h]

theorem eu_big {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ) (j : ℕ)
    (h : 3 ≤ tokAt w j) : eu fl p w j = 0 := by
  have h' : ¬ (tokAt w j ≤ 2) := by omega
  unfold eu uq
  rw [if_neg h']
  exact sw_zero hr _

theorem init_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [ev fl p w j, 0, eu fl p w j] ++ pos fl j (w.length + 1) := by
  have h6 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 ∨
      tokAt w j = 5 := by
    have := tok_le w hw j
    omega
  rcases h6 with h | h | h | h | h | h <;>
    simp [TNet.init, net, ev, eu, vq, uq, val, swRow, h, sw_zero hr]

theorem ev_near {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hMc : (20 : ℝ) ≤ M)
    (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ)
    (hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199) :
    |ev fl p w j - ((val (tokAt w j) : ℕ) : ℝ)| ≤ 1 / 199 * ((val (tokAt w j) : ℕ) : ℝ) + η
      ∧ 0 ≤ ((val (tokAt w j) : ℕ) : ℝ) ∧ ((val (tokAt w j) : ℕ) : ℝ) ≤ 3 := by
  have hc : ((vq (tokAt w j) : ℚ) : ℝ) = ((val (tokAt w j) : ℕ) : ℝ) := by simp [vq]
  have hv3 : val (tokAt w j) ≤ 3 := val_le _ (tok_le w hw j)
  have hv3R : ((val (tokAt w j) : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hv3
  have hv0 : (0 : ℝ) ≤ ((val (tokAt w j) : ℕ) : ℝ) := Nat.cast_nonneg _
  have h := sw_near hr hu0 (vq (tokAt w j)) (hp.E (tokAt w j) 0) (by norm_num)
    (by rw [hc, abs_of_nonneg hv0]; linarith) hε
  rw [hc, abs_of_nonneg hv0] at h
  exact ⟨h, hv0, hv3R⟩

theorem eu_near {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hMc : (20 : ℝ) ≤ M)
    (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ) (hj : tokAt w j ≤ 2)
    (hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199) (hη : η ≤ 1 / 2 ^ 149) :
    99 / 100 ≤ eu fl p w j ∧ eu fl p w j ≤ 101 / 100 := by
  have c1 : ((1 : ℚ) : ℝ) = 1 := by norm_num
  have h := sw_near hr hu0 1 (hp.E (tokAt w j) 2) (by norm_num)
    (by rw [c1, abs_of_nonneg (by norm_num)]; linarith) hε
  rw [c1, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)] at h
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  rw [eu_small fl p w j hj]
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

/-- The score in closed form. -/
theorem score_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (a0 a1 a2 qi qn b0 b1 b2 qk qn' : ℝ)
    (hI1 : fl (fl (sw fl 17 (dA 3 4) * qk)) = fl (sw fl 17 (dA 3 4) * qk))
    (hI2 : fl (fl (sw fl (-40) (dA 5 2) * b2)) = fl (sw fl (-40) (dA 5 2) * b2)) :
    hd.score fl dA [a0, a1, a2, 1, qi, qn] [b0, b1, b2, 1, qk, qn'] =
      fl (fl (sw fl 17 (dA 3 4) * qk) + fl (qn * fl (sw fl (-40) (dA 5 2) * b2))) := by
  simp [Head.score, hd, z6, pdot, rmat, rdot, sw_zero hr, hr.zero, hI1, hI2]

theorem msc {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (S Q nf pj : ℝ)
    (hI : fl (fl (S * pj)) = fl (S * pj)) :
    fl (fl (S * pj) + fl (nf * fl (Q * 0))) = fl (S * pj) := by
  simp [hr.zero, hI]

theorem val_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ)
    (b0 b1 b2 qk qn : ℝ)
    (hI : fl (fl (sw fl 1 (dV 0) * b0)) = fl (sw fl 1 (dV 0) * b0)) :
    rdot fl [1, 0, 0, 0, 0, 0] [b0, b1, b2, 1, qk, qn] dV 0 0 = fl (sw fl 1 (dV 0) * b0) := by
  simp [rdot, sw_zero hr, hr.zero, hI]

theorem zrow_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ)
    (a b c d e f : ℝ) :
    rdot fl z6 [a, b, c, d, e, f] dV 0 0 = 0 := by
  simp [z6, rdot, sw_zero hr, hr.zero]

theorem attn_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) :
    sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, savg fl ex (cand Mask.causal (w.length + 1) i)
              (hscore hd fl (p.A 0 0) (net.init fl p w) i)
              (fun j => rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 1) 0 0),
         0, 0, 0, 0] := by
  have hV : hd.V = [z6, [1, 0, 0, 0, 0, 0], z6, z6, z6, z6] := rfl
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
      = [0, A, 0, 0, 0, 0])
    (hA : fl A = A)
    (hI : fl (fl (sw fl 1 (p.oW 1) * A)) = fl (sw fl 1 (p.oW 1) * A)) :
    sout net fl ex p w i = fl (sw fl 1 (p.oW 1) * A) := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 1, 0, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  unfold sout srun
  rw [hb, ho, hc]
  simp only [srunFrom, sblock, blk, sheadsApply, hattn]
  simp only [init_eq hr p w hw]
  simp [z6, pos, rdot, radd, raffine, sw_zero hr, hr.zero, hA, hI]

/-! ### Pure real-arithmetic lemmas -/

theorem u_small {u : ℝ} {N : ℕ} (hu0 : 0 ≤ u) (hn : u * (N : ℝ) ≤ 1 / 256) (hN1 : 1 ≤ N) :
    u ≤ 1 / 256 := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have := mul_le_mul_of_nonneg_left hNR hu0
  linarith

theorem posbd {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hη : η ≤ 1 / 2 ^ 149) {N : ℕ} (hn : u * (N : ℝ) ≤ 1 / 256) (hnM : (N : ℝ) ≤ M)
    (hN1 : 1 ≤ N) (S : ℝ) (hS1 : 169 / 10 ≤ S) (hS2 : S ≤ 171 / 10) (k : ℕ) (hk : k ≤ N) :
    |S * fl (k : ℝ)| ≤ 18 * (N : ℝ) := by
  obtain ⟨hk0, hk1⟩ := hr.pos_le hu0 hη hk hn hnM
  have hS0 : 0 ≤ S := by linarith
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  rw [abs_of_nonneg (mul_nonneg hS0 hk0)]
  have := mul_le_mul hS2 hk1 hk0 (by norm_num)
  linarith

theorem gap_mm {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hη : η ≤ 1 / 2 ^ 149) {N : ℕ} (hn : u * (N : ℝ) ≤ 1 / 256) (hnM : (N : ℝ) ≤ M)
    (hN1 : 1 ≤ N) (h18 : 18 * (N : ℝ) ≤ M)
    (S : ℝ) (hS1 : 169 / 10 ≤ S) (hS2 : S ≤ 171 / 10) {j k : ℕ} (hkj : k < j) (hj : j ≤ N) :
    fl (S * fl (k : ℝ)) ≤ fl (S * fl (j : ℝ)) - 16 * |(j : ℝ) - k| := by
  have hg := hr.pos_gap hu0 hη (le_of_lt hkj) hj hn hnM
  have hgp := hr.gap hu0 (posbd hr hu0 hη hn hnM hN1 S hS1 hS2 k (by omega))
    (posbd hr hu0 hη hn hnM hN1 S hS1 hS2 j hj) h18
  have hd1 : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hkj
  rw [abs_of_nonneg (by linarith)]
  have hD0 : 0 ≤ fl (j : ℝ) - fl (k : ℝ) := by linarith
  have hSD := mul_le_mul_of_nonneg_right hS1 hD0
  have hun : u * (18 * (N : ℝ)) = 18 * (u * (N : ℝ)) := by ring
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  linarith [hgp, hSD, hg, hd1, hn, hηs, hηs', hun]

theorem qe_bd (Q e : ℝ) (hQ1 : Q ≤ -397 / 10) (hQ2 : -403 / 10 ≤ Q) (he0 : 0 ≤ e)
    (he2 : e ≤ 101 / 100) : -408 / 10 ≤ Q * e ∧ Q * e ≤ 0 := by
  constructor
  · have := mul_le_mul_of_nonneg_right hQ2 he0
    linarith
  · have := mul_nonneg (show (0 : ℝ) ≤ -Q by linarith) he0
    linarith

theorem qe_up (Q e : ℝ) (hQ1 : Q ≤ -397 / 10) (he0 : 0 ≤ e) (he1 : 99 / 100 ≤ e) :
    Q * e ≤ -393 / 10 := by
  have := mul_le_mul_of_nonneg_right hQ1 he0
  linarith

set_option maxHeartbeats 800000 in
theorem tbd {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hη : η ≤ 1 / 2 ^ 149)
    {N : ℕ} (hn : u * (N : ℝ) ≤ 1 / 256) (hnM : (N : ℝ) ≤ M) (hN1 : 1 ≤ N)
    (h300 : 300 * (N : ℝ) ≤ M) (hMc : (300 : ℝ) ≤ M)
    (Q e : ℝ) (hQ1 : Q ≤ -397 / 10) (hQ2 : -403 / 10 ≤ Q) (he0 : 0 ≤ e) (he2 : e ≤ 101 / 100) :
    |fl (fl (N : ℝ) * fl (Q * e))| ≤ 43 * (N : ℝ) ∧
    (99 / 100 ≤ e → fl (fl (N : ℝ) * fl (Q * e)) ≤ -391 / 10 * (N : ℝ) + 37 / 100) := by
  have hus := u_small hu0 hn hN1
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  obtain ⟨hqe1, hqe2⟩ := qe_bd Q e hQ1 hQ2 he0 he2
  have hqa : |Q * e| ≤ 41 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hR := hr.abs hu0 hqa (by linarith : (41 : ℝ) ≤ M)
  obtain ⟨hR1, hR2⟩ := abs_le.mp hR
  have hR5lo : -41 ≤ fl (Q * e) := by linarith
  have hR5hi : fl (Q * e) ≤ 1 / 5 := by linarith
  obtain ⟨hnf0, hnf1⟩ := hr.pos_le hu0 hη (le_refl N) hn hnM
  obtain ⟨hnf2, hnf3⟩ := abs_le.mp (hr.pos_near hu0 hη (le_refl N) hn hnM)
  have hP1 : fl (N : ℝ) * (-41) ≤ fl (N : ℝ) * fl (Q * e) :=
    mul_le_mul_of_nonneg_left hR5lo hnf0
  have hP2 : fl (N : ℝ) * fl (Q * e) ≤ fl (N : ℝ) * (1 / 5) :=
    mul_le_mul_of_nonneg_left hR5hi hnf0
  have hPa : |fl (N : ℝ) * fl (Q * e)| ≤ 42 * (N : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hub : u * (42 * (N : ℝ)) = 42 * (u * (N : ℝ)) := by ring
  have hT := hr.bound hu0 hPa (by linarith : 42 * (N : ℝ) ≤ M)
  refine ⟨by linarith, ?_⟩
  intro he1
  have hqe3 := qe_up Q e hQ1 he0 he1
  have hR5up : fl (Q * e) ≤ -391 / 10 := by linarith
  have hP3 : fl (N : ℝ) * fl (Q * e) ≤ fl (N : ℝ) * (-391 / 10) :=
    mul_le_mul_of_nonneg_left hR5up hnf0
  have hTu := hr.upper hu0 hPa (by linarith : 42 * (N : ℝ) ≤ M)
  linarith

set_option maxHeartbeats 800000 in
theorem sbound {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hη : η ≤ 1 / 2 ^ 149)
    {N : ℕ} (hn : u * (N : ℝ) ≤ 1 / 256) (hnM : (N : ℝ) ≤ M) (hN1 : 1 ≤ N)
    (h300 : 300 * (N : ℝ) ≤ M) (hMc : (300 : ℝ) ≤ M)
    (S Q e : ℝ) (hS1 : 169 / 10 ≤ S) (hS2 : S ≤ 171 / 10)
    (hQ1 : Q ≤ -397 / 10) (hQ2 : -403 / 10 ≤ Q) (he0 : 0 ≤ e) (he2 : e ≤ 101 / 100)
    {k : ℕ} (hk : k ≤ N) :
    |fl (fl (S * fl (k : ℝ)) + fl (fl (N : ℝ) * fl (Q * e)))| ≤ 70 * (N : ℝ) := by
  have hus := u_small hu0 hn hN1
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hPb := posbd hr hu0 hη hn hnM hN1 S hS1 hS2 k hk
  have hT := (tbd hr hu0 hη hn hnM hN1 h300 hMc Q e hQ1 hQ2 he0 he2).1
  have hR3 := hr.bound hu0 hPb (by linarith : 18 * (N : ℝ) ≤ M)
  have hub : u * (18 * (N : ℝ)) = 18 * (u * (N : ℝ)) := by ring
  have hub2 : u * (62 * (N : ℝ)) = 62 * (u * (N : ℝ)) := by ring
  have hX : |fl (S * fl (k : ℝ)) + fl (fl (N : ℝ) * fl (Q * e))| ≤ 62 * (N : ℝ) := by
    have := abs_add_le (fl (S * fl (k : ℝ))) (fl (fl (N : ℝ) * fl (Q * e)))
    linarith
  have := hr.bound hu0 hX (by linarith : 62 * (N : ℝ) ≤ M)
  linarith

set_option maxHeartbeats 1600000 in
theorem gap_um {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hη : η ≤ 1 / 2 ^ 149)
    {N : ℕ} (hn : u * (N : ℝ) ≤ 1 / 256) (hnM : (N : ℝ) ≤ M) (hN1 : 1 ≤ N)
    (h300 : 300 * (N : ℝ) ≤ M) (hMc : (300 : ℝ) ≤ M)
    (S Q e : ℝ) (hS1 : 169 / 10 ≤ S) (hS2 : S ≤ 171 / 10)
    (hQ1 : Q ≤ -397 / 10) (hQ2 : -403 / 10 ≤ Q) (he1 : 99 / 100 ≤ e) (he2 : e ≤ 101 / 100)
    {j k : ℕ} (hj : j ≤ N) (hk : k ≤ N) :
    fl (fl (S * fl (k : ℝ)) + fl (fl (N : ℝ) * fl (Q * e)))
      ≤ fl (S * fl (j : ℝ)) - 16 * |(j : ℝ) - k| := by
  have hus := u_small hu0 hn hN1
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have he0 : 0 ≤ e := by linarith
  have hPk := posbd hr hu0 hη hn hnM hN1 S hS1 hS2 k hk
  have hPj := posbd hr hu0 hη hn hnM hN1 S hS1 hS2 j hj
  obtain ⟨hT1, hT2⟩ := tbd hr hu0 hη hn hnM hN1 h300 hMc Q e hQ1 hQ2 he0 he2
  have hT3 := hT2 he1
  have hR3 := hr.bound hu0 hPk (by linarith : 18 * (N : ℝ) ≤ M)
  have hub : u * (18 * (N : ℝ)) = 18 * (u * (N : ℝ)) := by ring
  have hub2 : u * (62 * (N : ℝ)) = 62 * (u * (N : ℝ)) := by ring
  have hX : |fl (S * fl (k : ℝ)) + fl (fl (N : ℝ) * fl (Q * e))| ≤ 62 * (N : ℝ) := by
    have := abs_add_le (fl (S * fl (k : ℝ))) (fl (fl (N : ℝ) * fl (Q * e)))
    linarith
  have hup := hr.upper hu0 hX (by linarith : 62 * (N : ℝ) ≤ M)
  have hgp := hr.gap hu0 hPk hPj (by linarith : 18 * (N : ℝ) ≤ M)
  obtain ⟨hpj1, hpj2⟩ := abs_le.mp (hr.pos_near hu0 hη hj hn hnM)
  obtain ⟨hpk1, hpk2⟩ := abs_le.mp (hr.pos_near hu0 hη hk hn hnM)
  have hjR : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hS0 : 0 ≤ S := by linarith
  rcases lt_or_ge k j with hkj | hjk
  · have hd1 : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hkj
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (j : ℝ) - k)]
    have hD0 : 0 ≤ fl (j : ℝ) - fl (k : ℝ) := by linarith
    have hSD := mul_le_mul_of_nonneg_right hS1 hD0
    linarith
  · have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
    rw [abs_of_nonpos (by linarith : (j : ℝ) - k ≤ 0)]
    rcases le_or_gt 0 (fl (j : ℝ) - fl (k : ℝ)) with hD | hD
    · have hSD := mul_nonneg hS0 hD
      linarith
    · have hSD := mul_le_mul_of_nonpos_right hS2 hD.le
      linarith

set_option maxHeartbeats 800000 in
theorem chain {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hus : u ≤ 1 / 256)
    (hη : η ≤ 1 / 2 ^ 149) (hη0 : 0 ≤ η) (hMc : (300 : ℝ) ≤ M) (T E O A tv : ℝ)
    (hT : |T - 1| ≤ 1 / 199 * 1 + η) (hO : |O - 1| ≤ 1 / 199 * 1 + η)
    (hE : |E - tv| ≤ 1 / 199 * tv + η) (htv0 : 0 ≤ tv) (htv3 : tv ≤ 3)
    (hTE : |T * E| ≤ 7 / 2)
    (hA1 : |A - fl (T * E)| ≤ 4 / 100 + 1 / 2 ^ 90) :
    |O * A| ≤ 6 ∧ |fl (O * A) - tv| ≤ 1 / 4 := by
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have h2 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 100000 := by norm_num
  have htv : |tv| ≤ 3 := by rw [abs_of_nonneg htv0]; exact htv3
  have ha : (1 : ℝ) / 199 * 1 + η ≤ 1 / 190 := by linarith
  have hb : (1 : ℝ) / 199 * tv + η ≤ 1 / 60 := by linarith
  have hb0 : (0 : ℝ) ≤ 1 / 199 * tv + η := by linarith
  have m1 := mul_le_mul ha htv (abs_nonneg _) (by norm_num)
  have m2 := mul_le_mul ha hb hb0 (by norm_num)
  have e1 := mul_near hT hE
  rw [one_mul, abs_one] at e1
  have e1' : |T * E - tv| ≤ 1 / 25 := by linarith
  have e2 := hr.near hu0 e1' hTE (by linarith : (7 / 2 : ℝ) ≤ M)
  have hFb := hr.bound hu0 hTE (by linarith : (7 / 2 : ℝ) ≤ M)
  have e3 := abs_sub_le A (fl (T * E)) tv
  have hX : |A - tv| ≤ 1 / 10 := by linarith
  have hAb : |A| ≤ 5 := by
    have := abs_sub_abs_le_abs_sub A (fl (T * E))
    linarith
  obtain ⟨hO1, hO2⟩ := abs_le.mp hO
  have hOb : |O| ≤ 11 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hOA : |O * A| ≤ 6 := by
    rw [abs_mul]
    have := mul_le_mul hOb hAb (abs_nonneg _) (by norm_num)
    linarith
  refine ⟨hOA, ?_⟩
  have e4 := mul_near hO hX
  rw [one_mul, abs_one] at e4
  have e5 := hr.near hu0 e4 hOA (by linarith : (6 : ℝ) ≤ M)
  linarith

/-! ### The target: last marked token -/

theorem lastv_snoc (l : List ℕ) (t : ℕ) :
    lastv (l ++ [t]) = if val t = 0 then lastv l else val t := by
  unfold lastv
  simp [List.foldl_append]

theorem take_succ_last (w : List ℕ) (i : ℕ) (hi : i < w.length) :
    w.take (i + 1) = w.take i ++ [tokAt w (i + 1)] := by
  rw [Lane4.Seq.tokAt_succ w i hi, List.take_add_one, List.getElem?_eq_getElem hi]
  rfl

theorem last_ex (w : List ℕ) : ∀ i, i ≤ w.length →
    (target w i = 0 ∧ ∀ k, 1 ≤ k → k ≤ i → val (tokAt w k) = 0) ∨
    (∃ j, 1 ≤ j ∧ j ≤ i ∧ val (tokAt w j) ≠ 0 ∧
      (∀ k, j < k → k ≤ i → val (tokAt w k) = 0) ∧ target w i = val (tokAt w j)) := by
  intro i
  induction i with
  | zero =>
    intro _
    left
    exact ⟨by simp [target, lastv], fun k hk hk' => by omega⟩
  | succ i ih =>
    intro hi
    have hi' : i < w.length := by omega
    have htk : target w (i + 1) =
        if val (tokAt w (i + 1)) = 0 then target w i else val (tokAt w (i + 1)) := by
      unfold target
      rw [take_succ_last w i hi', lastv_snoc]
    rcases ih (by omega) with ⟨h0, hall⟩ | ⟨j, hj1, hj2, hj3, hj4, hj5⟩
    · by_cases hv : val (tokAt w (i + 1)) = 0
      · left
        refine ⟨(by rw [htk, if_pos hv]; exact h0), ?_⟩
        intro k hk hk'
        by_cases hki : k ≤ i
        · exact hall k hk hki
        · have : k = i + 1 := by omega
          rw [this]; exact hv
      · right
        exact ⟨i + 1, by omega, le_refl _, hv, fun k hk hk' => by omega,
          (by rw [htk, if_neg hv])⟩
    · by_cases hv : val (tokAt w (i + 1)) = 0
      · right
        refine ⟨j, hj1, by omega, hj3, ?_, (by rw [htk, if_pos hv]; exact hj5)⟩
        intro k hk hk'
        by_cases hki : k ≤ i
        · exact hj4 k hk hki
        · have : k = i + 1 := by omega
          rw [this]; exact hv
      · right
        exact ⟨i + 1, by omega, le_refl _, hv, fun k hk hk' => by omega,
          (by rw [htk, if_neg hv])⟩

/-! ### Main theorem -/

set_option maxHeartbeats 1600000 in
theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη p hp w hw hn hnη hM i hi1 hi
  have hn1 : 1 ≤ w.length + 1 := by omega
  have hnR : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hn1
  have hMn : 300 * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  have hMc : (300 : ℝ) ≤ M := range_const hM hn1 (by norm_num)
  have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by linarith
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hus := u_small hu0 hn hn1
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by linarith
  have hMc20 : (20 : ℝ) ≤ M := by linarith
  -- stored weights
  have c17 : ((17 : ℚ) : ℝ) = 17 := by norm_num
  have c40 : ((-40 : ℚ) : ℝ) = -40 := by norm_num
  have c1 : ((1 : ℚ) : ℝ) = 1 := by norm_num
  have hS := sw_near hr hu0 17 (hp.A 0 0 3 4) (by norm_num)
    (by rw [c17, abs_of_nonneg (by norm_num)]; linarith) hε
  rw [c17, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 17)] at hS
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  have hQ := sw_near hr hu0 (-40) (hp.A 0 0 5 2) (by norm_num)
    (by rw [c40, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 40)]; linarith) hε
  rw [c40, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 40)] at hQ
  obtain ⟨hQ1, hQ2⟩ := abs_le.mp hQ
  have hT := sw_near hr hu0 1 (hp.V 0 0 1 0) (by norm_num)
    (by rw [c1, abs_of_nonneg (by norm_num)]; linarith) hε
  rw [c1, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)] at hT
  have hO := sw_near hr hu0 1 (hp.oW 1) (by norm_num)
    (by rw [c1, abs_of_nonneg (by norm_num)]; linarith) hε
  rw [c1, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)] at hO
  -- the unmarked indicator
  have heu : ∀ k : ℕ, 0 ≤ eu fl p w k ∧ eu fl p w k ≤ 101 / 100 := by
    intro k
    by_cases hk : tokAt w k ≤ 2
    · obtain ⟨h1, h2⟩ := eu_near hr hu0 hMc20 p hp w k hk hε hη
      exact ⟨by linarith, h2⟩
    · rw [eu_big hr p w k (by omega)]
      norm_num
  have hQE : ∀ k : ℕ, |sw fl (-40) (p.A 0 0 5 2) * eu fl p w k| ≤ 41 := by
    intro k
    obtain ⟨a, b⟩ := heu k
    obtain ⟨c, d⟩ := qe_bd (sw fl (-40) (p.A 0 0 5 2)) (eu fl p w k) (by linarith)
      (by linarith) a b
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- scores
  have hPb : ∀ k : ℕ, k ≤ w.length + 1 →
      |sw fl 17 (p.A 0 0 3 4) * fl (k : ℝ)| ≤ 18 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    exact posbd hr hu0 hη hn hnM hn1 _ (by linarith) (by linarith) k hk
  have hsk : ∀ k : ℕ, k ≤ w.length + 1 →
      hscore hd fl (p.A 0 0) (net.init fl p w) i k
        = fl (fl (sw fl 17 (p.A 0 0 3 4) * fl (k : ℝ)) +
            fl (fl ((w.length + 1 : ℕ) : ℝ) *
              fl (sw fl (-40) (p.A 0 0 5 2) * eu fl p w k))) := by
    intro k hk
    simp only [hscore, init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact score_eq hr _ _ _ _ _ _ _ _ _ _ _
      (hr.idem _ (le_trans (hPb k hk) (by linarith)))
      (hr.idem _ (le_trans (hQE k) (by linarith)))
  have hsm : ∀ k : ℕ, k ≤ w.length + 1 → 3 ≤ tokAt w k →
      hscore hd fl (p.A 0 0) (net.init fl p w) i k
        = fl (sw fl 17 (p.A 0 0 3 4) * fl (k : ℝ)) := by
    intro k hk hk3
    rw [hsk k hk, eu_big hr p w k hk3]
    exact msc hr _ _ _ _ (hr.idem _ (le_trans (hPb k hk) (by linarith)))
  -- values
  have hTEb : ∀ k : ℕ, |sw fl 1 (p.V 0 0 1 0) * ev fl p w k| ≤ 7 / 2 := by
    intro k
    obtain ⟨hk1, hk2, hk3⟩ := ev_near hr hu0 hMc20 p hp w hw k hε
    obtain ⟨hT1, hT2⟩ := abs_le.mp hT
    obtain ⟨hE1, hE2⟩ := abs_le.mp hk1
    rw [abs_mul]
    have h1 : |sw fl 1 (p.V 0 0 1 0)| ≤ 11 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |ev fl p w k| ≤ 31 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
    have := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    linarith
  have hfk : ∀ k : ℕ, rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 1) 0 0
      = fl (sw fl 1 (p.V 0 0 1 0) * ev fl p w k) := by
    intro k
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact val_eq hr _ _ _ _ _ _ (hr.idem _ (le_trans (hTEb k) (by linarith)))
  have hlen0 : (cand Mask.causal (w.length + 1) i).length = i + 1 := by
    simp [cand]
  have hlen : (cand Mask.causal (w.length + 1) i).length ≤ w.length + 1 := by
    rw [hlen0]; omega
  have hat := attn_eq (ex := ex) hr p w hw i
  rcases last_ex w i hi with ⟨htg, hall⟩ | ⟨j, hj1, hji, hjv, hjlast, htg⟩
  · -- no marked token: every candidate value is exactly 0
    have hz : ∀ k ∈ cand Mask.causal (w.length + 1) i,
        (fun j => rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 1) 0 0) k = 0 := by
      intro k hk
      rw [Lane4.Seq.mem_cand_causal] at hk
      show rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 1) 0 0 = 0
      rw [hfk k]
      have hk0 : tokAt w k ≤ 2 := by
        by_cases hk' : k = 0
        · rw [hk']
          simp [Lane4.Seq.tokAt_zero]
        · have h1 := hall k (by omega) hk
          have h5 := tok_le w hw k
          exact (val_zero_iff _ h5).mp h1
      rw [ev_small hr p w k hk0, mul_zero, hr.zero]
    have hA0 := soft_zeros (ex := ex) hr
      (s := hscore hd fl (p.A 0 0) (net.init fl p w) i)
      (f := fun j => rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 1) 0 0) hz
    rw [hA0] at hat
    rw [out_eq hr p w hw i 0 hat hr.zero (by simp [hr.zero])]
    rw [htg]
    simp [hr.zero]
  · -- the last marked token is at position j
    have hj5 : tokAt w j ≤ 5 := tok_le w hw j
    have hjm : 3 ≤ tokAt w j := by
      by_contra hcon
      exact hjv ((val_zero_iff _ hj5).mpr (by omega))
    have hjc : j ∈ cand Mask.causal (w.length + 1) i := by
      rw [Lane4.Seq.mem_cand_causal]; exact hji
    have hsj := hsm j (by omega) hjm
    have hgap : ∀ k ∈ cand Mask.causal (w.length + 1) i, k ≠ j →
        hscore hd fl (p.A 0 0) (net.init fl p w) i k
          ≤ hscore hd fl (p.A 0 0) (net.init fl p w) i j - 16 * (ndist j k : ℝ) := by
      intro k hk hne
      rw [Lane4.Seq.mem_cand_causal] at hk
      rw [ndist_cast, hsj]
      by_cases hk2 : tokAt w k ≤ 2
      · rw [hsk k (by omega)]
        obtain ⟨he1, he2⟩ := eu_near hr hu0 hMc20 p hp w k hk2 hε hη
        exact gap_um hr hu0 hη hn hnM hn1 hMn hMc _ _ _ (by linarith) (by linarith)
          (by linarith) (by linarith) he1 he2 (by omega) (by omega)
      · have hk3 : 3 ≤ tokAt w k := by omega
        have hkj : k < j := by
          by_contra hcon
          have hjk : j < k := by omega
          have h1 := hjlast k hjk hk
          have h5 := tok_le w hw k
          exact hk2 ((val_zero_iff _ h5).mp h1)
        rw [hsm k (by omega) hk3]
        exact gap_mm hr hu0 hη hn hnM hn1 (by linarith) _ (by linarith) (by linarith) hkj
          (by omega)
    have hSb : ∀ k ∈ cand Mask.causal (w.length + 1) i,
        |hscore hd fl (p.A 0 0) (net.init fl p w) i k| ≤ 70 * ((w.length + 1 : ℕ) : ℝ) := by
      intro k hk
      rw [Lane4.Seq.mem_cand_causal] at hk
      rw [hsk k (by omega)]
      obtain ⟨he0, he2⟩ := heu k
      exact sbound hr hu0 hη hn hnM hn1 hMn hMc _ _ _ (by linarith) (by linarith)
        (by linarith) (by linarith) he0 he2 (by omega)
    have hfB : ∀ k ∈ cand Mask.causal (w.length + 1) i,
        |(fun j => rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 1) 0 0) k| ≤ 4 := by
      intro k _
      show |rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 1) 0 0| ≤ 4
      rw [hfk k]
      have := hr.bound hu0 (hTEb k) (by linarith)
      linarith
    obtain ⟨hA1, hA2⟩ := soft_near hr he hu0 hu1 hη0 hη (Lane4.Seq.cand_nodup _ _ _) hlen hn hnη
      hjc hgap hSb (by linarith) hfB (by linarith)
    have hA1' : |savg fl ex (cand Mask.causal (w.length + 1) i)
        (hscore hd fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl [1, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 1) 0 0)
        - fl (sw fl 1 (p.V 0 0 1 0) * ev fl p w j)| ≤ 4 / 100 + 1 / 2 ^ 90 := by
      have := hA1
      simp only [hfk j] at this
      exact this
    obtain ⟨hE, htv0, htv3⟩ := ev_near hr hu0 hMc20 p hp w hw j hε
    obtain ⟨hOAb, hfin⟩ := chain hr hu0 hus hη hη0 hMc _ _ _ _ _ hT hO hE htv0 htv3
      (hTEb j) hA1'
    rw [out_eq hr p w hw i _ hat hA2 (hr.idem _ (le_trans hOAb (by linarith)))]
    rw [htg]
    exact hfin

end Lane4.Case
