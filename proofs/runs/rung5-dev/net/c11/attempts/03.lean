set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.unnecessarySimpa false

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

def Vn (t : ℕ) : ℕ := if t = 2 ∨ t = 4 ∨ t = 5 then 1 else 0
def Gn (t : ℕ) : ℕ := if t = 2 ∨ t = 4 then 1 else 0
def Pn (t : ℕ) : ℕ := if t = 1 then 1 else 0
def Dn (t : ℕ) : ℕ :=
  if t = 1 then 1 else if t = 2 then 2 else if t = 3 then 0 else if t = 4 then 2
  else if t = 5 then 1 else 0

theorem Vn_le (t : ℕ) : Vn t ≤ 1 := by unfold Vn; split_ifs <;> omega
theorem Gn_le (t : ℕ) : Gn t ≤ 1 := by unfold Gn; split_ifs <;> omega
theorem Pn_le (t : ℕ) : Pn t ≤ 1 := by unfold Pn; split_ifs <;> omega
theorem Dn_le (t : ℕ) : Dn t ≤ 2 := by unfold Dn; split_ifs <;> omega

def z9 : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0, 0]
def rowS : List ℚ := [0, 0, 0, 0, 0, 0, 0, 17, 0]
def rowP : List ℚ := [0, -40, 0, 0, 0, 0, 0, 0, 0]
def rowV : List ℚ := [1, 0, 0, 0, 0, 0, 0, 0, 0]

def hdA : Head :=
  { A := [z9, z9, z9, z9, z9, z9, rowS, z9, rowP],
    V := [z9, z9, z9, z9, rowV, z9, z9, z9, z9],
    mask := Mask.strict }

def blk : Block :=
  { heads := [hdA], W1 := [[0, 0, 1, 0, 1, 0, 0, 0, 0]], b1 := [-1],
    W2 := [[0], [0], [0], [0], [0], [-3], [0], [0], [0]], b2 := z9 }

def net : TNet :=
  { embed := [[0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0], [1, 0, 1, 2, 0, 0],
              [0, 0, 0, 0, 0, 0], [1, 0, 1, 2, 0, 0], [1, 0, 0, 1, 0, 0]],
    blocks := [blk],
    outW := [0, 0, 0, 1, 1, 1, 0, 0, 0],
    outB := 0 }

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

noncomputable abbrev cS (fl : ℝ → ℝ) (p : Pert) : ℝ := sw fl 17 (p.A 0 0 6 7)
noncomputable abbrev cQ (fl : ℝ → ℝ) (p : Pert) : ℝ := sw fl (-40) (p.A 0 0 8 1)
noncomputable abbrev cT (fl : ℝ → ℝ) (p : Pert) : ℝ := sw fl 1 (p.V 0 0 4 0)
noncomputable abbrev eV (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl ((Vn (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 0)
noncomputable abbrev eP (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl ((Pn (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 1)
noncomputable abbrev eG (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl ((Gn (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 2)
noncomputable abbrev eD (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl ((Dn (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 3)

theorem init9 {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [eV fl p w j, eP fl p w j, eG fl p w j, eD fl p w j, 0, 0, 1,
      fl (j : ℝ), fl (((w.length + 1 : ℕ)) : ℝ)] := by
  have h6 : tokAt w j ≤ 5 := tok_le w hw j
  have h : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 ∨
      tokAt w j = 5 := by omega
  rcases h with h | h | h | h | h | h <;>
    simp [TNet.init, net, swRow, pos, h, Vn, Gn, Pn, Dn, eV, eP, eG, eD, sw_zero hr]

theorem score_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (a0 a1 a2 a3 qi qn b0 b1 b2 b3 qk qn' : ℝ)
    (hI1 : fl (fl (sw fl 17 (dA 6 7) * qk)) = fl (sw fl 17 (dA 6 7) * qk))
    (hI2 : fl (fl (sw fl (-40) (dA 8 1) * b1)) = fl (sw fl (-40) (dA 8 1) * b1)) :
    hdA.score fl dA [a0, a1, a2, a3, 0, 0, 1, qi, qn] [b0, b1, b2, b3, 0, 0, 1, qk, qn'] =
      fl (fl (sw fl 17 (dA 6 7) * qk) + fl (qn * fl (sw fl (-40) (dA 8 1) * b1))) := by
  simp [Head.score, hdA, z9, rowS, rowP, pdot, rmat, rdot, sw_zero hr, hr.zero, hI1, hI2]

theorem val_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ)
    (b0 b1 b2 b3 qk qn : ℝ)
    (hI : fl (fl (sw fl 1 (dV 0) * b0)) = fl (sw fl 1 (dV 0) * b0)) :
    rdot fl rowV [b0, b1, b2, b3, 0, 0, 1, qk, qn] dV 0 0 = fl (sw fl 1 (dV 0) * b0) := by
  simp [rowV, rdot, sw_zero hr, hr.zero, hI]

theorem zrow_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ)
    (a b c d e f g h i : ℝ) :
    rdot fl z9 [a, b, c, d, e, f, g, h, i] dV 0 0 = 0 := by
  simp [z9, rdot, sw_zero hr, hr.zero]

noncomputable abbrev HA (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (i : ℕ) : ℝ :=
  savg fl ex (cand Mask.strict (w.length + 1) i)
    (hscore hdA fl (p.A 0 0) (net.init fl p w) i)
    (fun j => rdot fl rowV (net.init fl p w j) (p.V 0 0 4) 0 0)

theorem attn_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) :
    sattn hdA fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, 0, 0, HA fl ex p w i, 0, 0, 0, 0] := by
  have hV : hdA.V = [z9, z9, z9, z9, rowV, z9, z9, z9, z9] := rfl
  have hm : hdA.mask = Mask.strict := rfl
  have hz : ∀ d : ℕ → ℝ,
      savg fl ex (cand Mask.strict (w.length + 1) i)
        (hscore hdA fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl z9 (net.init fl p w j) d 0 0) = 0 := by
    intro d
    apply soft_zeros hr
    intro k _
    show rdot fl z9 (net.init fl p w k) d 0 0 = 0
    rw [init9 hr p w hw k]
    exact zrow_eq hr d _ _ _ _ _ _ _ _ _
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz, HA]

theorem out_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) (A V P G D qi qn : ℝ)
    (sg sc sb sh sd sa sx : ℝ)
    (hxi : net.init fl p w i = [V, P, G, D, 0, 0, 1, qi, qn])
    (hattn : sattn hdA fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, 0, 0, A, 0, 0, 0, 0])
    (hV : fl V = V) (hP : fl P = P) (hG : fl G = G) (hD : fl D = D) (hA : fl A = A)
    (hqi : fl qi = qi) (hqn : fl qn = qn)
    (hsg : sw fl 1 (p.W1 0 0 2) = sg) (hsc : sw fl 1 (p.W1 0 0 4) = sc)
    (hsb : sw fl (-1) (p.b1 0 0) = sb) (hsh : sw fl (-3) (p.W2 0 5 0) = sh)
    (hsd : sw fl 1 (p.oW 3) = sd) (hsa : sw fl 1 (p.oW 4) = sa) (hsx : sw fl 1 (p.oW 5) = sx)
    (hI1 : fl (fl (sg * G)) = fl (sg * G))
    (hI2 : fl (fl (fl (sg * G) + fl (sc * A))) = fl (fl (sg * G) + fl (sc * A)))
    (hI3 : fl (fl (sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb))))
      = fl (sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb))))
    (hI4 : fl (fl (sd * D)) = fl (sd * D))
    (hI5 : fl (fl (fl (fl (sd * D) + fl (sa * A)) +
        fl (sx * fl (sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb))))))
      = fl (fl (fl (sd * D) + fl (sa * A)) +
        fl (sx * fl (sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb)))))) :
    sout net fl ex p w i
      = fl (fl (fl (sd * D) + fl (sa * A)) +
        fl (sx * fl (sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb))))) := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 0, 0, 1, 1, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  have hy : radd fl [V, P, G, D, 0, 0, 1, qi, qn] [0, 0, 0, 0, A, 0, 0, 0, 0]
      = [V, P, G, D, A, 0, 1, qi, qn] := by
    simp [radd, hr.zero, hr.one, hV, hP, hG, hD, hA, hqi, hqn]
  unfold sout srun
  rw [hb, ho, hc]
  simp only [srunFrom, sblock, blk, sheadsApply, hattn, hxi, hy]
  simp [raffine, radd, rdot, z9, sw_zero hr, hr.zero, hr.one, hV, hP, hG, hD, hA, hqi, hqn,
    hsg, hsc, hsb, hsh, hsd, hsa, hsx, hI1, hI2, hI3, hI4, hI5]

end Lane4.Case

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

theorem swn {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 2 ^ 149) (q : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 200) (hq : 2 * |(q : ℝ)| ≤ M) :
    |sw fl q d - (q : ℝ)| ≤ 1 / 199 * |(q : ℝ)| + 1 / 100000 := by
  have h24 : (1 : ℝ) / 2 ^ 24 ≤ 1 / 100000 := by norm_num
  have h1 := eta_tiny hη
  have h2 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have h := sw_near hr hu0 q hd (by norm_num) hq (by linarith : (1:ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199)
  linarith

theorem swr {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 2 ^ 149) (q : ℚ) (r : ℝ) (hqr : (q : ℝ) = r) {d : ℝ} (hd : |d| ≤ 1 / 200)
    (hq : 2 * |r| ≤ M) :
    |sw fl q d - r| ≤ 1 / 199 * |r| + 1 / 100000 := by
  subst hqr
  exact swn hr hu0 hu1 hη q hd hq

theorem swq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 2 ^ 149) (hM : 8 ≤ M) (m : ℕ) (hm : m ≤ 2) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    |sw fl ((m : ℕ) : ℚ) d - (m : ℝ)| ≤ 1 / 199 * (m : ℝ) + 1 / 100000
      ∧ 0 ≤ sw fl ((m : ℕ) : ℚ) d := by
  have hc : (((m : ℕ) : ℚ) : ℝ) = (m : ℝ) := by norm_cast
  have hm2 : (m : ℝ) ≤ 2 := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  constructor
  · have h := swr hr hu0 hu1 hη ((m : ℕ) : ℚ) (m : ℝ) hc hd
      (by rw [abs_of_nonneg hm0]; linarith)
    rwa [abs_of_nonneg hm0] at h
  · unfold sw
    have hd2 := abs_le.mp hd
    apply hr.nonneg
    · rw [hc]; exact mul_nonneg hm0 (by linarith)
    · rw [hc]
      have : (m : ℝ) * (1 + d) ≤ (m : ℝ) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) hm0
      linarith

theorem rn {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 2 ^ 149) (hM : 10 ≤ M) {x t e : ℝ} (hx : |x - t| ≤ e) (hB : |x| ≤ 10) :
    |fl x - t| ≤ e + 1 / 100000 := by
  have h := hr.near hu0 hx hB hM
  have h1 := eta_tiny hη
  have h2 : (1 : ℝ) / 2 ^ 24 ≤ 1 / 10000000 := by norm_num
  have h3 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000000 := by norm_num
  linarith

theorem absb {x t e B0 B : ℝ} (hx : |x - t| ≤ e) (ht : |t| ≤ B0) (he : e + B0 ≤ B) :
    |x| ≤ B := by
  have := abs_sub_abs_le_abs_sub x t
  linarith

theorem relu_lip (a b : ℝ) : |relu a - relu b| ≤ |a - b| := by
  unfold relu
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [max_eq_right ha, max_eq_right hb]; simp
  · rw [max_eq_right ha, max_eq_left hb]
    rw [abs_of_nonpos (by linarith : (0 : ℝ) - b ≤ 0), abs_of_nonpos (by linarith : a - b ≤ 0)]
    linarith
  · rw [max_eq_left ha, max_eq_right hb]
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - 0), abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - b)]
    linarith
  · rw [max_eq_left ha, max_eq_left hb]

theorem final_num {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) (hM : 10 ≤ M)
    (g0 c0 d0 G D A sg sc sb sh sd sa sx : ℝ)
    (hg0 : g0 = 0 ∨ g0 = 1) (hc0 : c0 = 0 ∨ c0 = 1) (hd0 : 0 ≤ d0 ∧ d0 ≤ 2)
    (hG : |G - g0| ≤ 1 / 198) (hD : |D - d0| ≤ 2 / 198) (hA : |A - c0| ≤ 9 / 400)
    (hsg : |sg - 1| ≤ 1 / 198) (hsc : |sc - 1| ≤ 1 / 198) (hsb : |sb - (-1)| ≤ 1 / 198)
    (hsh : |sh - (-3)| ≤ 3 / 198) (hsd : |sd - 1| ≤ 1 / 198) (hsa : |sa - 1| ≤ 1 / 198)
    (hsx : |sx - 1| ≤ 1 / 198) :
    fl (fl (sg * G)) = fl (sg * G) ∧
    fl (fl (fl (sg * G) + fl (sc * A))) = fl (fl (sg * G) + fl (sc * A)) ∧
    fl (fl (sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb))))
      = fl (sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb))) ∧
    fl (fl (sd * D)) = fl (sd * D) ∧
    fl (fl (fl (fl (sd * D) + fl (sa * A)) +
        fl (sx * fl (sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb))))))
      = fl (fl (fl (sd * D) + fl (sa * A)) +
        fl (sx * fl (sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb))))) ∧
    |fl (fl (fl (sd * D) + fl (sa * A)) +
        fl (sx * fl (sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb)))))
      - (d0 + c0 - 3 * max (g0 + c0 - 1) 0)| ≤ 1 / 4 := by
  have hg1 : |g0| ≤ 1 := by rcases hg0 with h | h <;> rw [h] <;> norm_num
  have hc1 : |c0| ≤ 1 := by rcases hc0 with h | h <;> rw [h] <;> norm_num
  have hd1 : |d0| ≤ 2 := by rw [abs_of_nonneg hd0.1]; exact hd0.2
  have hg01 : 0 ≤ g0 ∧ g0 ≤ 1 := by rcases hg0 with h | h <;> rw [h] <;> norm_num
  have hc01 : 0 ≤ c0 ∧ c0 ≤ 1 := by rcases hc0 with h | h <;> rw [h] <;> norm_num
  have hh0 : 0 ≤ max (g0 + c0 - 1) 0 ∧ max (g0 + c0 - 1) 0 ≤ 1 := by
    constructor
    · exact le_max_right _ _
    · apply max_le <;> linarith [hg01.2, hc01.2, hg01.1, hc01.1]
  generalize hh : max (g0 + c0 - 1) 0 = h0 at hh0 ⊢
  -- sg * G
  have m1 := mul_near hsg hG
  rw [one_mul, abs_one] at m1
  have e1 : |sg * G - g0| ≤ 1 / 98 := by
    have : 1 / 198 * |g0| ≤ (1 : ℝ) / 198 := by linarith
    linarith
  have r1 := rn hr hu0 hu1 hη hM e1 (absb e1 hg1 (by norm_num))
  -- sc * A
  have m2 := mul_near hsc hA
  rw [one_mul, abs_one] at m2
  have e2 : |sc * A - c0| ≤ 277 / 10000 := by
    have : 1 / 198 * |c0| ≤ (1 : ℝ) / 198 := by linarith
    linarith
  have r2 := rn hr hu0 hu1 hη hM e2 (absb e2 hc1 (by norm_num))
  -- sum
  have s12 : |fl (sg * G) + fl (sc * A) - (g0 + c0)| ≤ 1 / 98 + 277 / 10000 + 2 / 100000 := by
    have h := abs_add_le (fl (sg * G) - g0) (fl (sc * A) - c0)
    have : fl (sg * G) + fl (sc * A) - (g0 + c0) = (fl (sg * G) - g0) + (fl (sc * A) - c0) := by
      ring
    rw [this]
    linarith
  have hg0c : |g0 + c0| ≤ 2 := by rw [abs_le]; constructor <;> linarith [hg01.1, hc01.1, hg01.2, hc01.2]
  have r3 := rn hr hu0 hu1 hη hM s12 (absb s12 hg0c (by norm_num))
  -- plus bias
  have s4 : |fl (fl (sg * G) + fl (sc * A)) + sb - (g0 + c0 - 1)| ≤ 43 / 1000 - 1 / 100000 := by
    have h := abs_add_le (fl (fl (sg * G) + fl (sc * A)) - (g0 + c0)) (sb - (-1))
    have : fl (fl (sg * G) + fl (sc * A)) + sb - (g0 + c0 - 1)
        = (fl (fl (sg * G) + fl (sc * A)) - (g0 + c0)) + (sb - (-1)) := by ring
    rw [this]
    linarith
  have hg0c1 : |g0 + c0 - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hg01.1, hc01.1, hg01.2, hc01.2]
  have r4 := rn hr hu0 hu1 hη hM s4 (absb s4 hg0c1 (by norm_num))
  -- relu
  have r5 : |relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb)) - h0| ≤ 43 / 1000 := by
    have h := relu_lip (fl (fl (fl (sg * G) + fl (sc * A)) + sb)) (g0 + c0 - 1)
    have h' : relu (g0 + c0 - 1) = h0 := by rw [← hh]; rfl
    rw [h'] at h
    linarith
  -- sh * relu
  have m3 := mul_near hsh r5
  have e3 : |sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb)) - (-3) * h0| ≤ 1449 / 10000 := by
    have : 3 / 198 * |h0| ≤ (3 : ℝ) / 198 := by rw [abs_of_nonneg hh0.1]; linarith
    have h3 : |(-3 : ℝ)| = 3 := by norm_num
    rw [h3] at m3
    linarith
  have hh3 : |(-3) * h0| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  have r6 := rn hr hu0 hu1 hη hM e3 (absb e3 hh3 (by norm_num))
  -- sx * z
  have m4 := mul_near hsx r6
  rw [one_mul, abs_one] at m4
  have e4 : |sx * fl (sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb))) - (-3) * h0|
      ≤ 1608 / 10000 := by
    have : 1 / 198 * |(-3) * h0| ≤ (3 : ℝ) / 198 := by linarith
    linarith
  have r7 := rn hr hu0 hu1 hη hM e4 (absb e4 hh3 (by norm_num))
  -- sd * D
  have m5 := mul_near hsd hD
  rw [one_mul, abs_one] at m5
  have e5 : |sd * D - d0| ≤ 203 / 10000 := by
    have : 1 / 198 * |d0| ≤ (2 : ℝ) / 198 := by linarith
    linarith
  have r8 := rn hr hu0 hu1 hη hM e5 (absb e5 hd1 (by norm_num))
  -- sa * A
  have m6 := mul_near hsa hA
  rw [one_mul, abs_one] at m6
  have e6 : |sa * A - c0| ≤ 277 / 10000 := by
    have : 1 / 198 * |c0| ≤ (1 : ℝ) / 198 := by linarith
    linarith
  have r9 := rn hr hu0 hu1 hη hM e6 (absb e6 hc1 (by norm_num))
  have s10 : |fl (sd * D) + fl (sa * A) - (d0 + c0)| ≤ 203 / 10000 + 277 / 10000 + 2 / 100000 := by
    have h := abs_add_le (fl (sd * D) - d0) (fl (sa * A) - c0)
    have : fl (sd * D) + fl (sa * A) - (d0 + c0) = (fl (sd * D) - d0) + (fl (sa * A) - c0) := by
      ring
    rw [this]
    linarith
  have hdc : |d0 + c0| ≤ 3 := by rw [abs_le]; constructor <;> linarith [hd0.1, hc01.1, hd0.2, hc01.2]
  have r10 := rn hr hu0 hu1 hη hM s10 (absb s10 hdc (by norm_num))
  have s11 : |fl (fl (sd * D) + fl (sa * A)) +
      fl (sx * fl (sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb))))
      - (d0 + c0 - 3 * h0)| ≤ 2100 / 10000 := by
    have h := abs_add_le (fl (fl (sd * D) + fl (sa * A)) - (d0 + c0))
      (fl (sx * fl (sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb)))) - (-3) * h0)
    have : fl (fl (sd * D) + fl (sa * A)) +
        fl (sx * fl (sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb))))
        - (d0 + c0 - 3 * h0)
        = (fl (fl (sd * D) + fl (sa * A)) - (d0 + c0)) +
          (fl (sx * fl (sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb)))) - (-3) * h0) := by
      ring
    rw [this]
    linarith
  have hfin : |d0 + c0 - 3 * h0| ≤ 3 := by
    rw [abs_le]; constructor <;> linarith [hd0.1, hc01.1, hd0.2, hc01.2, hh0.1, hh0.2]
  have r11 := rn hr hu0 hu1 hη hM s11 (absb s11 hfin (by norm_num))
  have i1 : |sg * G| ≤ 10 := absb e1 hg1 (by norm_num)
  have i2 : |fl (sg * G) + fl (sc * A)| ≤ 10 := absb s12 hg0c (by norm_num)
  have i3 : |sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb))| ≤ 10 :=
    absb e3 hh3 (by norm_num)
  have i4 : |sd * D| ≤ 10 := absb e5 hd1 (by norm_num)
  have i5 : |fl (fl (sd * D) + fl (sa * A)) +
      fl (sx * fl (sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb))))| ≤ 10 :=
    absb s11 hfin (by norm_num)
  have i6 : |fl (fl (fl (sd * D) + fl (sa * A)) +
      fl (sx * fl (sh * relu (fl (fl (fl (sg * G) + fl (sc * A)) + sb)))))| ≤ 10 :=
    absb r11 hfin (by norm_num)
  refine ⟨hr.idem _ (le_trans i1 hM), hr.idem _ (le_trans i2 hM), hr.idem _ (le_trans i3 hM),
    hr.idem _ (le_trans i4 hM), hr.idem _ (le_trans i5 hM), ?_⟩
  linarith

end Lane4.Case

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

theorem carry_snoc (l : List ℕ) (t : ℕ) :
    carry (l ++ [t]) = if cls t = 2 then carry l else cls t := by
  simp [carry, List.foldl_append]

theorem cls_step (c t : ℕ) (h1 : 1 ≤ t) (h5 : t ≤ 5) :
    (if cls t = 2 then c else cls t) = if t = 1 then c else Vn t := by
  interval_cases t <;> simp [cls, Vn]

theorem take_snoc (w : List ℕ) (m : ℕ) (h : m < w.length) :
    w.take (m + 1) = w.take m ++ [w[m]] := by
  first
    | exact List.take_succ_eq_append_getElem h
    | (rw [List.take_succ]; simp [h])

theorem carry_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) :
    ∀ m, m ≤ w.length →
      carry (w.take m) = Vn (tokAt w (Nat.findGreatest (fun j => tokAt w j ≠ 1) m)) := by
  intro m
  induction m with
  | zero =>
    intro _
    simp [carry, Vn, tokAt]
  | succ m ih =>
    intro hm
    have hlt : m < w.length := by omega
    have ih' := ih (by omega)
    have htok : tokAt w (m + 1) = w[m] := Lane4.Seq.tokAt_succ w m hlt
    have hwm := hw w[m] (List.getElem_mem hlt)
    rw [take_snoc w m hlt, carry_snoc, cls_step _ _ hwm.1 hwm.2]
    by_cases h1 : w[m] = 1
    · have hfg : Nat.findGreatest (fun j => tokAt w j ≠ 1) (m + 1)
          = Nat.findGreatest (fun j => tokAt w j ≠ 1) m := by
        rw [Nat.findGreatest_succ]; simp [htok, h1]
      rw [hfg, if_pos h1]
      exact ih'
    · have hfg : Nat.findGreatest (fun j => tokAt w j ≠ 1) (m + 1) = m + 1 := by
        rw [Nat.findGreatest_succ]; simp [htok, h1]
      rw [hfg, if_neg h1, htok]

theorem tgt (t v : ℕ) (ht : t ≤ 5) (hv : v ≤ 1) :
    (((Dn t + v) % 3 : ℕ) : ℝ)
      = (Dn t : ℝ) + (v : ℝ) - 3 * max ((Gn t : ℝ) + (v : ℝ) - 1) 0 := by
  interval_cases t <;> interval_cases v <;> norm_num [Dn, Gn, max_def]

theorem nat01 (m : ℕ) (hm : m ≤ 1) : (m : ℝ) = 0 ∨ (m : ℝ) = 1 := by
  interval_cases m <;> simp

theorem target_eq (w : List ℕ) (i : ℕ) (hi1 : 1 ≤ i) :
    target w i = (Dn (tokAt w i) + carry (w.take (i - 1))) % 3 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  unfold target
  have h : tokAt w (k + 1) = w.getD (k + 1 - 1) 0 := by simp [tokAt]
  rw [h]
  rfl

end Lane4.Case

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

set_option maxHeartbeats 4000000 in
theorem head_ok {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (he : ExpM u η ex)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2 ^ 149)
    (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5)
    (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256) (hnη : η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100)
    (hM : 2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) (jw : ℕ) (hjle : jw ≤ i - 1)
    (hjP : tokAt w jw ≠ 1) (hjK : ∀ k, jw < k → k ≤ i - 1 → tokAt w k = 1) :
    |HA fl ex p w i - ((Vn (tokAt w jw) : ℕ) : ℝ)| ≤ 9 / 400
      ∧ fl (HA fl ex p w i) = HA fl ex p w i := by
  have hn1 : 1 ≤ w.length + 1 := by omega
  have hnR : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hn1
  have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
    have := range_lin hM hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have h18 : 18 * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  have h42 : 42 * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  have h62 : 62 * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  have h140 : 140 * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  have h100 : (100 : ℝ) ≤ M := range_const hM hn1 (by norm_num)
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hu7 : u ≤ 1 / 10000000 := by
    have : (1 : ℝ) / 2 ^ 24 ≤ 1 / 10000000 := by norm_num
    linarith
  have hunN : ∀ c : ℝ, u * (c * ((w.length + 1 : ℕ) : ℝ)) = c * (u * ((w.length + 1 : ℕ) : ℝ)) := fun c => by ring
  -- stored weights
  have hS : |cS fl p - 17| ≤ 1 / 199 * |(17 : ℝ)| + 1 / 100000 :=
    swr hr hu0 hu1 hη 17 17 (by norm_num) (hp.A 0 0 6 7) (by norm_num; linarith)
  have h17 : |(17 : ℝ)| = 17 := by norm_num
  rw [h17] at hS
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  have hSlo : (169 : ℝ) / 10 ≤ cS fl p := by linarith
  have hShi : cS fl p ≤ 171 / 10 := by linarith
  have hQ : |cQ fl p - (-40)| ≤ 1 / 199 * |(-40 : ℝ)| + 1 / 100000 :=
    swr hr hu0 hu1 hη (-40) (-40) (by norm_num) (hp.A 0 0 8 1) (by norm_num; linarith)
  have h40 : |(-40 : ℝ)| = 40 := by norm_num
  rw [h40] at hQ
  obtain ⟨hQ1, hQ2⟩ := abs_le.mp hQ
  have hQlo : -4021 / 100 ≤ cQ fl p := by linarith
  have hQhi : cQ fl p ≤ -3979 / 100 := by linarith
  have hT : |cT fl p - 1| ≤ 1 / 199 * |(1 : ℝ)| + 1 / 100000 :=
    swr hr hu0 hu1 hη 1 1 (by norm_num) (hp.V 0 0 4 0) (by norm_num; linarith)
  rw [abs_one] at hT
  have hT' : |cT fl p - 1| ≤ 1 / 198 := by linarith
  obtain ⟨hT1, hT2⟩ := abs_le.mp hT'
  -- token-dependent stored weights
  have hPk : ∀ k, |eP fl p w k - (Pn (tokAt w k) : ℝ)| ≤ 1 / 199 * (Pn (tokAt w k) : ℝ) + 1 / 100000
      ∧ 0 ≤ eP fl p w k := fun k =>
    swq hr hu0 hu1 hη (by linarith) _ (by have := Pn_le (tokAt w k); omega) (hp.E _ 1)
  have hVk : ∀ k, |eV fl p w k - (Vn (tokAt w k) : ℝ)| ≤ 1 / 199 * (Vn (tokAt w k) : ℝ) + 1 / 100000
      ∧ 0 ≤ eV fl p w k := fun k =>
    swq hr hu0 hu1 hη (by linarith) _ (by have := Vn_le (tokAt w k); omega) (hp.E _ 0)
  have hPn1 : ∀ k, (Pn (tokAt w k) : ℝ) ≤ 1 := fun k => by exact_mod_cast Pn_le (tokAt w k)
  have hVn1 : ∀ k, (Vn (tokAt w k) : ℝ) ≤ 1 := fun k => by exact_mod_cast Vn_le (tokAt w k)
  have hVn0 : ∀ k, (0 : ℝ) ≤ (Vn (tokAt w k) : ℝ) := fun k => Nat.cast_nonneg _
  have hPn0 : ∀ k, (0 : ℝ) ≤ (Pn (tokAt w k) : ℝ) := fun k => Nat.cast_nonneg _
  have hP101 : ∀ k, eP fl p w k ≤ 101 / 100 := by
    intro k
    have := (abs_le.mp (hPk k).1).2
    linarith [hPn1 k, hPn0 k]
  have hV101 : ∀ k, eV fl p w k ≤ 101 / 100 := by
    intro k
    have := (abs_le.mp (hVk k).1).2
    linarith [hVn1 k, hVn0 k]
  -- positions
  have hpos : ∀ k : ℕ, k ≤ w.length + 1 → 0 ≤ fl (k : ℝ) ∧ fl (k : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) + 1 / 100 :=
    fun k hk => hr.pos_le hu0 hη hk hn hnM
  have hpn : ∀ k : ℕ, k ≤ w.length + 1 → |fl (k : ℝ) - k| ≤ 1 / 200 :=
    fun k hk => hr.pos_near hu0 hη hk hn hnM
  have hfln := hpos (w.length + 1) le_rfl
  have hflnn := hpn (w.length + 1) le_rfl
  have hflnn' := abs_le.mp hflnn
  have hPb : ∀ k : ℕ, k ≤ w.length + 1 → |cS fl p * fl (k : ℝ)| ≤ 18 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    obtain ⟨hk0, hk1⟩ := hpos k hk
    have hS0 : 0 ≤ cS fl p := by linarith
    rw [abs_of_nonneg (mul_nonneg hS0 hk0)]
    have := mul_le_mul hShi hk1 hk0 (by norm_num)
    linarith
  have hQabs : |cQ fl p| ≤ 4021 / 100 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hQP : ∀ k, |cQ fl p * eP fl p w k| ≤ 41 := by
    intro k
    have hPa : |eP fl p w k| ≤ 101 / 100 := abs_le.mpr ⟨by linarith [(hPk k).2], hP101 k⟩
    rw [abs_mul]
    have := mul_le_mul hQabs hPa (abs_nonneg _) (by norm_num)
    linarith
  have hbabs : ∀ k, |fl (cQ fl p * eP fl p w k)| ≤ 411 / 10 := by
    intro k
    have := hr.bound hu0 (hQP k) (by linarith : (41 : ℝ) ≤ M)
    linarith
  have hfb : ∀ k, |fl (((w.length + 1 : ℕ) : ℝ)) * fl (cQ fl p * eP fl p w k)| ≤ 42 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k
    rw [abs_mul, abs_of_nonneg hfln.1]
    have := mul_le_mul hfln.2 (hbabs k) (abs_nonneg _) (by linarith)
    linarith
  have hI1 : ∀ k : ℕ, k ≤ w.length + 1 → fl (fl (cS fl p * fl (k : ℝ))) = fl (cS fl p * fl (k : ℝ)) :=
    fun k hk => hr.idem _ (le_trans (hPb k hk) h18)
  have hI2 : ∀ k, fl (fl (cQ fl p * eP fl p w k)) = fl (cQ fl p * eP fl p w k) :=
    fun k => hr.idem _ (le_trans (hQP k) (by linarith))
  have hsk : ∀ k : ℕ, k ≤ w.length + 1 →
      hscore hdA fl (p.A 0 0) (net.init fl p w) i k =
        fl (fl (cS fl p * fl (k : ℝ)) + fl (fl ((w.length + 1 : ℕ) : ℝ) * fl (cQ fl p * eP fl p w k))) := by
    intro k hk
    simp only [hscore]
    rw [init9 hr p w hw i, init9 hr p w hw k]
    exact score_eq hr (p.A 0 0) _ _ _ _ _ _ _ _ _ _ _ _ (hI1 k hk) (hI2 k)
  -- sign facts
  have hb_le : ∀ k, fl (cQ fl p * eP fl p w k) ≤ 0 := by
    intro k
    apply hr.nonpos
    · have := mul_le_mul_of_nonneg_right (show cQ fl p ≤ 0 by linarith) (hPk k).2
      linarith
    · have := (abs_le.mp (hQP k)).1
      linarith
  have ht_le : ∀ k, fl (fl ((w.length + 1 : ℕ) : ℝ) * fl (cQ fl p * eP fl p w k)) ≤ 0 := by
    intro k
    apply hr.nonpos
    · have := mul_le_mul_of_nonneg_left (hb_le k) hfln.1
      linarith
    · have := (abs_le.mp (hfb k)).1
      linarith
  have hat : ∀ k : ℕ, k ≤ w.length + 1 → |fl (cS fl p * fl (k : ℝ))| ≤ 18 * ((w.length + 1 : ℕ) : ℝ) + 1 := by
    intro k hk
    have := hr.bound hu0 (hPb k hk) h18
    have := hunN 18
    linarith
  have htabs : ∀ k, |fl (fl ((w.length + 1 : ℕ) : ℝ) * fl (cQ fl p * eP fl p w k))| ≤ 42 * ((w.length + 1 : ℕ) : ℝ) + 1 := by
    intro k
    have := hr.bound hu0 (hfb k) h42
    have := hunN 42
    linarith
  have hsum : ∀ k : ℕ, k ≤ w.length + 1 →
      |fl (cS fl p * fl (k : ℝ)) + fl (fl ((w.length + 1 : ℕ) : ℝ) * fl (cQ fl p * eP fl p w k))| ≤ 62 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    have h1 := hat k hk
    have h2 := htabs k
    have := abs_add_le (fl (cS fl p * fl (k : ℝ))) (fl (fl ((w.length + 1 : ℕ) : ℝ) * fl (cQ fl p * eP fl p w k)))
    linarith
  have hsbd : ∀ k : ℕ, k ≤ w.length + 1 →
      |hscore hdA fl (p.A 0 0) (net.init fl p w) i k| ≤ 70 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    rw [hsk k hk]
    have := hr.bound hu0 (hsum k hk) h62
    have := hunN 62
    linarith
  have hs_le : ∀ k : ℕ, k ≤ w.length + 1 →
      hscore hdA fl (p.A 0 0) (net.init fl p w) i k ≤ fl (cS fl p * fl (k : ℝ)) := by
    intro k hk
    rw [hsk k hk]
    have hm := hr.mono (fl (cS fl p * fl (k : ℝ)) + fl (fl ((w.length + 1 : ℕ) : ℝ) * fl (cQ fl p * eP fl p w k)))
      (fl (cS fl p * fl (k : ℝ))) (le_trans (hsum k hk) h62)
      (show |fl (cS fl p * fl (k : ℝ))| ≤ M by have := hat k hk; linarith)
      (by linarith [ht_le k])
    rw [hI1 k hk] at hm
    exact hm
  have hjn : jw ≤ w.length + 1 := by omega
  have hPj : eP fl p w jw = 0 := by
    have : Pn (tokAt w jw) = 0 := by simp [Pn, hjP]
    simp [eP, this, sw_zero hr]
  have hsjw : hscore hdA fl (p.A 0 0) (net.init fl p w) i jw = fl (cS fl p * fl (jw : ℝ)) := by
    rw [hsk jw hjn, hPj]
    simp [hr.zero, hI1 jw hjn]
  have hAgap : ∀ a b : ℕ, a < b → b ≤ w.length + 1 →
      fl (cS fl p * fl (a : ℝ)) ≤ fl (cS fl p * fl (b : ℝ)) - 16 * ((b : ℝ) - a) := by
    intro a b hab hbn
    have hg := hr.pos_gap hu0 hη (le_of_lt hab) hbn hn hnM
    have hgp := hr.gap hu0 (hPb a (by omega)) (hPb b hbn) h18
    have hd1 : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
    have hD0 : 0 ≤ fl (b : ℝ) - fl (a : ℝ) := by linarith
    have hSD := mul_le_mul_of_nonneg_right (show (169 : ℝ) / 10 ≤ cS fl p by linarith) hD0
    have hun := hunN 18
    linarith [hgp, hSD, hg, hd1, hn, hηs, hηs', hun]
  have hj : jw ∈ cand Mask.strict (w.length + 1) i := by
    rw [Lane4.Seq.mem_cand_strict]; omega
  have hlen : (cand Mask.strict (w.length + 1) i).length ≤ w.length + 1 := by
    simp [cand]; omega
  have hgap : ∀ k ∈ cand Mask.strict (w.length + 1) i, k ≠ jw →
      hscore hdA fl (p.A 0 0) (net.init fl p w) i k
        ≤ hscore hdA fl (p.A 0 0) (net.init fl p w) i jw - 16 * (ndist jw k : ℝ) := by
    intro k hk hne
    rw [Lane4.Seq.mem_cand_strict] at hk
    rw [ndist_cast, hsjw]
    have hkn : k ≤ w.length + 1 := by omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 := hs_le k hkn
      have h2 := hAgap k jw hlt hjn
      have hkj : (k : ℝ) ≤ (jw : ℝ) := by exact_mod_cast hlt.le
      rw [abs_of_nonneg (show (0 : ℝ) ≤ (jw : ℝ) - (k : ℝ) by linarith)]
      linarith
    · have hkP : tokAt w k = 1 := hjK k hgt (by omega)
      have hPn : Pn (tokAt w k) = 1 := by simp [Pn, hkP]
      have hc1 : ((Pn (tokAt w k) : ℕ) : ℝ) = 1 := by rw [hPn]; simp
      have hP99 : (99 : ℝ) / 100 ≤ eP fl p w k := by
        have := (abs_le.mp (hPk k).1).1
        rw [hc1] at this
        linarith
      have hQPk : cQ fl p * eP fl p w k ≤ -(3939 / 100) := by
        have := mul_le_mul (show (3979 : ℝ) / 100 ≤ -cQ fl p by linarith) hP99 (by norm_num)
          (by linarith)
        linarith
      have hbk : fl (cQ fl p * eP fl p w k) ≤ -(393 / 10) := by
        have := hr.upper hu0 (hQP k) (by linarith : (41 : ℝ) ≤ M)
        linarith
      have hfbk : fl ((w.length + 1 : ℕ) : ℝ) * fl (cQ fl p * eP fl p w k) ≤ fl ((w.length + 1 : ℕ) : ℝ) * (-(393 / 10)) :=
        mul_le_mul_of_nonneg_left hbk hfln.1
      have htk := hr.upper hu0 (hfb k) h42
      have hak := hr.upper hu0 (hPb k hkn) h18
      have hsk' := hr.upper hu0 (hsum k hkn) h62
      have hSk : cS fl p * fl (k : ℝ) ≤ 171 / 10 * fl (k : ℝ) :=
        mul_le_mul_of_nonneg_right hShi (hpos k hkn).1
      have hSj : 169 / 10 * fl (jw : ℝ) ≤ cS fl p * fl (jw : ℝ) :=
        mul_le_mul_of_nonneg_right hSlo (hpos jw hjn).1
      have hajl := hr.lower hu0 (hPb jw hjn) h18
      have hpk := abs_le.mp (hpn k hkn)
      have hpj := abs_le.mp (hpn jw hjn)
      have hkN : (k : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hkn
      have hj0 : (0 : ℝ) ≤ (jw : ℝ) := Nat.cast_nonneg _
      have hjk : (jw : ℝ) ≤ (k : ℝ) := by exact_mod_cast hgt.le
      rw [hsk k hkn, abs_of_nonpos (show (jw : ℝ) - (k : ℝ) ≤ 0 by linarith)]
      linarith [hfln.1, hflnn'.1, hflnn'.2, hpk.1, hpk.2, hpj.1, hpj.2, hunN 18, hunN 42,
        hunN 62]
  have hTV : ∀ k, |cT fl p * eV fl p w k| ≤ 102 / 100 := by
    intro k
    have hTa : |cT fl p| ≤ 101 / 100 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hVa : |eV fl p w k| ≤ 101 / 100 := abs_le.mpr ⟨by linarith [(hVk k).2], hV101 k⟩
    rw [abs_mul]
    have := mul_le_mul hTa hVa (abs_nonneg _) (by norm_num)
    linarith
  have hfk : ∀ k, rdot fl rowV (net.init fl p w k) (p.V 0 0 4) 0 0
      = fl (cT fl p * eV fl p w k) := by
    intro k
    rw [init9 hr p w hw k]
    exact val_eq hr (p.V 0 0 4) _ _ _ _ _ _ (hr.idem _ (le_trans (hTV k) (by linarith)))
  have hfB : ∀ k ∈ cand Mask.strict (w.length + 1) i,
      |(fun j => rdot fl rowV (net.init fl p w j) (p.V 0 0 4) 0 0) k| ≤ 103 / 100 := by
    intro k _
    show |rdot fl rowV (net.init fl p w k) (p.V 0 0 4) 0 0| ≤ 103 / 100
    rw [hfk k]
    have := hr.bound hu0 (hTV k) (by linarith : (102 : ℝ) / 100 ≤ M)
    linarith
  obtain ⟨hA1, hA2⟩ := soft_near hr he hu0 hu1 hη0 hη (Lane4.Seq.cand_nodup _ _ _) hlen hn hnη
    hj hgap (fun k hk => hsbd k (by rw [Lane4.Seq.mem_cand_strict] at hk; omega))
    (by linarith) hfB (by linarith)
  refine ⟨?_, hA2⟩
  have hA1' : |HA fl ex p w i - fl (cT fl p * eV fl p w jw)| ≤ 103 / 100 / 100 + 1 / 2 ^ 90 := by
    have := hA1
    simp only [hfk jw] at this
    exact this
  have hv := hVk jw
  have m := mul_near hT' hv.1
  rw [one_mul, abs_one] at m
  have h1 := hVn1 jw
  have h0 := hVn0 jw
  have e1 : |cT fl p * eV fl p w jw - (Vn (tokAt w jw) : ℝ)| ≤ 11 / 1000 := by
    have : (1 : ℝ) / 198 * |(Vn (tokAt w jw) : ℝ)| ≤ 1 / 198 := by
      rw [abs_of_nonneg h0]; linarith
    linarith
  have hva : |(Vn (tokAt w jw) : ℝ)| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
  have r1 := rn hr hu0 hu1 hη (by linarith) e1 (absb e1 hva (by norm_num))
  have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 100000 := by norm_num
  have e3 := abs_sub_le (HA fl ex p w i) (fl (cT fl p * eV fl p w jw)) ((Vn (tokAt w jw) : ℕ) : ℝ)
  linarith

end Lane4.Case

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

theorem flswq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hM : 8 ≤ M) (m : ℕ) (hm : m ≤ 2)
    {d : ℝ} (hd : |d| ≤ 1 / 200) :
    fl (sw fl ((m : ℕ) : ℚ) d) = sw fl ((m : ℕ) : ℚ) d := by
  have hc : (((m : ℕ) : ℚ) : ℝ) = (m : ℝ) := by norm_cast
  have hm2 : (m : ℝ) ≤ 2 := by exact_mod_cast hm
  exact fl_sw hr _ hd (by norm_num) (by rw [hc, abs_of_nonneg (Nat.cast_nonneg m)]; linarith)

set_option maxHeartbeats 1600000 in
theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη p hp w hw hn hnη hM i hi1 hi
  have hn1 : 1 ≤ w.length + 1 := by omega
  have hh100 : (100 : ℝ) ≤ M := range_const hM hn1 (by norm_num)
  have hNM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
    have := range_lin hM hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have hiN : i ≤ w.length + 1 := by omega
  have hiR : (i : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hiN
  have hqi : fl (fl (i : ℝ)) = fl (i : ℝ) :=
    hr.idem _ (by rw [abs_of_nonneg (Nat.cast_nonneg i)]; linarith)
  have hqn : fl (fl ((w.length + 1 : ℕ) : ℝ)) = fl ((w.length + 1 : ℕ) : ℝ) :=
    hr.idem _ (by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact hNM)
  -- the last non-propagate position before i
  obtain ⟨jw, hjwdef⟩ : ∃ jw, jw = Nat.findGreatest (fun j => tokAt w j ≠ 1) (i - 1) :=
    ⟨_, rfl⟩
  have hjle : jw ≤ i - 1 := by rw [hjwdef]; exact Nat.findGreatest_le _
  have hjP : tokAt w jw ≠ 1 := by
    rw [hjwdef]
    exact Nat.findGreatest_spec (P := fun j => tokAt w j ≠ 1) (Nat.zero_le _)
      (by simp [Lane4.Seq.tokAt_zero])
  have hjK : ∀ k, jw < k → k ≤ i - 1 → tokAt w k = 1 := by
    intro k h1 h2
    rw [hjwdef] at h1
    have := Nat.findGreatest_is_greatest h1 h2
    simpa using this
  have hcar : carry (w.take (i - 1)) = Vn (tokAt w jw) := by
    rw [hjwdef]; exact carry_eq w hw (i - 1) (by omega)
  obtain ⟨hA1, hA2⟩ := head_ok hr he hu0 hu1 hη0 hη p hp w hw hn hnη hM i hi1 hi jw hjle hjP hjK
  -- stored weights
  have hsg : |sw fl 1 (p.W1 0 0 2) - 1| ≤ 1 / 198 := by
    have := swr hr hu0 hu1 hη 1 1 (by norm_num) (hp.W1 0 0 2) (by norm_num; linarith)
    rw [abs_one] at this
    linarith
  have hsc : |sw fl 1 (p.W1 0 0 4) - 1| ≤ 1 / 198 := by
    have := swr hr hu0 hu1 hη 1 1 (by norm_num) (hp.W1 0 0 4) (by norm_num; linarith)
    rw [abs_one] at this
    linarith
  have hsb : |sw fl (-1) (p.b1 0 0) - (-1)| ≤ 1 / 198 := by
    have := swr hr hu0 hu1 hη (-1) (-1) (by norm_num) (hp.b1 0 0) (by norm_num; linarith)
    have h1 : |(-1 : ℝ)| = 1 := by norm_num
    rw [h1] at this
    linarith
  have hsh : |sw fl (-3) (p.W2 0 5 0) - (-3)| ≤ 3 / 198 := by
    have := swr hr hu0 hu1 hη (-3) (-3) (by norm_num) (hp.W2 0 5 0) (by norm_num; linarith)
    have h1 : |(-3 : ℝ)| = 3 := by norm_num
    rw [h1] at this
    linarith
  have hsd : |sw fl 1 (p.oW 3) - 1| ≤ 1 / 198 := by
    have := swr hr hu0 hu1 hη 1 1 (by norm_num) (hp.oW 3) (by norm_num; linarith)
    rw [abs_one] at this
    linarith
  have hsa : |sw fl 1 (p.oW 4) - 1| ≤ 1 / 198 := by
    have := swr hr hu0 hu1 hη 1 1 (by norm_num) (hp.oW 4) (by norm_num; linarith)
    rw [abs_one] at this
    linarith
  have hsx : |sw fl 1 (p.oW 5) - 1| ≤ 1 / 198 := by
    have := swr hr hu0 hu1 hη 1 1 (by norm_num) (hp.oW 5) (by norm_num; linarith)
    rw [abs_one] at this
    linarith
  -- stored token features at position i
  have hGn1 : (Gn (tokAt w i) : ℝ) ≤ 1 := by exact_mod_cast Gn_le (tokAt w i)
  have hGn0 : (0 : ℝ) ≤ (Gn (tokAt w i) : ℝ) := Nat.cast_nonneg _
  have hDn2 : (Dn (tokAt w i) : ℝ) ≤ 2 := by exact_mod_cast Dn_le (tokAt w i)
  have hDn0 : (0 : ℝ) ≤ (Dn (tokAt w i) : ℝ) := Nat.cast_nonneg _
  have hG : |eG fl p w i - (Gn (tokAt w i) : ℝ)| ≤ 1 / 198 := by
    have := (swq hr hu0 hu1 hη (by linarith) (Gn (tokAt w i))
      (by have := Gn_le (tokAt w i); omega) (hp.E (tokAt w i) 2)).1
    linarith
  have hD : |eD fl p w i - (Dn (tokAt w i) : ℝ)| ≤ 2 / 198 := by
    have := (swq hr hu0 hu1 hη (by linarith) (Dn (tokAt w i))
      (Dn_le (tokAt w i)) (hp.E (tokAt w i) 3)).1
    linarith
  have hflV : fl (eV fl p w i) = eV fl p w i :=
    flswq hr (by linarith) _ (by have := Vn_le (tokAt w i); omega) (hp.E _ 0)
  have hflP : fl (eP fl p w i) = eP fl p w i :=
    flswq hr (by linarith) _ (by have := Pn_le (tokAt w i); omega) (hp.E _ 1)
  have hflG : fl (eG fl p w i) = eG fl p w i :=
    flswq hr (by linarith) _ (by have := Gn_le (tokAt w i); omega) (hp.E _ 2)
  have hflD : fl (eD fl p w i) = eD fl p w i :=
    flswq hr (by linarith) _ (Dn_le (tokAt w i)) (hp.E _ 3)
  have hg0 := nat01 (Gn (tokAt w i)) (Gn_le (tokAt w i))
  have hc0 := nat01 (Vn (tokAt w jw)) (Vn_le (tokAt w jw))
  obtain ⟨hI1, hI2, hI3, hI4, hI5, hfin⟩ := final_num hr hu0 hu1 hη (by linarith)
    (Gn (tokAt w i) : ℝ) (Vn (tokAt w jw) : ℝ) (Dn (tokAt w i) : ℝ)
    (eG fl p w i) (eD fl p w i) (HA fl ex p w i)
    (sw fl 1 (p.W1 0 0 2)) (sw fl 1 (p.W1 0 0 4)) (sw fl (-1) (p.b1 0 0))
    (sw fl (-3) (p.W2 0 5 0)) (sw fl 1 (p.oW 3)) (sw fl 1 (p.oW 4)) (sw fl 1 (p.oW 5))
    hg0 hc0 ⟨hDn0, hDn2⟩ hG hD hA1 hsg hsc hsb hsh hsd hsa hsx
  have hout := out_eq hr p w hw i (HA fl ex p w i) (eV fl p w i) (eP fl p w i) (eG fl p w i)
    (eD fl p w i) (fl (i : ℝ)) (fl ((w.length + 1 : ℕ) : ℝ))
    (sw fl 1 (p.W1 0 0 2)) (sw fl 1 (p.W1 0 0 4)) (sw fl (-1) (p.b1 0 0))
    (sw fl (-3) (p.W2 0 5 0)) (sw fl 1 (p.oW 3)) (sw fl 1 (p.oW 4)) (sw fl 1 (p.oW 5))
    (init9 hr p w hw i) (attn_eq hr p w hw i) hflV hflP hflG hflD hA2 hqi hqn
    rfl rfl rfl rfl rfl rfl rfl hI1 hI2 hI3 hI4 hI5
  rw [hout, target_eq w i hi1, hcar, tgt _ _ (tok_le w hw i) (Vn_le _)]
  exact hfin

end Lane4.Case
