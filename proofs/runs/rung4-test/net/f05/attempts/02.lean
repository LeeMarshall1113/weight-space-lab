namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

def z10 : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def hd0 : Head :=
  { A := [z10, z10, z10, z10, z10, z10, z10, [0, 0, 0, 0, 0, 0, 0, 0, -1, 0], z10,
          [0, 4, 0, 0, 0, 0, 0, 0, 0, 0]],
    V := [z10, z10, z10, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], z10, z10, z10, z10, z10, z10],
    mask := Mask.causal }

def hd1 : Head :=
  { A := [z10, z10, z10, z10, z10, z10, z10, [0, 0, 0, 0, 0, 0, 0, 0, -1, 0], z10,
          [0, 0, 0, 0, 4, 0, 0, 0, 0, 0]],
    V := [z10, z10, z10, z10, z10, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], z10, z10, z10, z10],
    mask := Mask.causal }

def blk0 : Block :=
  { heads := [hd0],
    W1 := [[1, 0, 0, -10, 0, 0, 0, 0, 0, 0]],
    b1 := [0],
    W2 := [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
    b2 := z10 }

def blk1 : Block :=
  { heads := [hd1],
    W1 := [[0, 0, 1, 0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0, 0, 0, 0]],
    b1 := [0, -1],
    W2 := [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, -2], [0, 0], [0, 0], [0, 0]],
    b2 := z10 }

def net : TNet :=
  { embed := [[0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0],
              [0, 1, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0]],
    blocks := [blk0, blk1],
    outW := [0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    outB := 0 }

/-! ### numeric helpers -/

theorem mul_iv {x y a b c d : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hx : a ≤ x ∧ x ≤ b)
    (hy : c ≤ y ∧ y ≤ d) : a * c ≤ x * y ∧ x * y ≤ b * d := by
  constructor
  · exact mul_le_mul hx.1 hy.1 hc (le_trans ha hx.1)
  · exact mul_le_mul hx.2 hy.2 (le_trans hc hy.1) (le_trans ha (le_trans hx.1 hx.2))

theorem sw_pos {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (w : ℚ) (hw : 0 ≤ w) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    (w : ℝ) * (188 / 189) ≤ sw fl w d ∧ sw fl w d ≤ (w : ℝ) * (190 / 189) := by
  have h := sw_rel hr hu0 w hd (ε := 1 / 189) (by linarith)
  have hw' : (0 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  rw [abs_of_nonneg hw'] at h
  have h2 := abs_le.mp h
  constructor <;> linarith [h2.1, h2.2]

theorem sw_neg {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (w : ℚ) (d : ℝ) :
    sw fl (-w) d = - sw fl w d := by
  unfold sw
  have : ((-w : ℚ) : ℝ) * (1 + d) = -((w : ℝ) * (1 + d)) := by push_cast; ring
  rw [this, hr.neg]

theorem flb {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {x : ℝ} (hx : |x| ≤ 8) :
    x - 1 / 1000000 ≤ fl x ∧ fl x ≤ x + 1 / 1000000 := by
  have h := hr.err hu0 hx
  have h2 : u * 8 ≤ 1 / 1000000 := by linarith
  have h3 := abs_le.mp (le_trans h h2)
  constructor <;> linarith [h3.1, h3.2]

/-! ### selection core -/

theorem sel_core {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216)
    (L i : ℕ) (hL : u * (L : ℝ) ≤ 1 / 256) (hi : i < L) (hL2 : 2 ≤ L)
    (sa sb V0 : ℝ) (hsa : 39 / 10 ≤ sa ∧ sa ≤ 41 / 10) (hsb : -51 / 50 ≤ sb ∧ sb ≤ -49 / 50)
    (hV : 9 / 10 ≤ V0 ∧ V0 ≤ 11 / 10)
    (f : ℕ → ℝ) (hf : ∀ k ≤ i, f k = 0 ∨ f k = V0) (j0 : ℕ) (hj0 : j0 ≤ i)
    (hfirst : (f j0 = V0 ∧ ∀ k < j0, f k = 0) ∨ (j0 = 0 ∧ ∀ k ≤ i, f k = 0))
    (sc : ℕ → ℝ)
    (hsc : ∀ k ≤ i, sc k = fl (fl (sb * fl (k : ℝ)) + fl (fl (L : ℝ) * fl (sa * f k)))) :
    ∀ k ≤ i, k ≠ j0 → sc k < sc j0 := by
  have hLr : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL2
  have hpos : ∀ k ≤ i, 0 ≤ fl (k : ℝ) ∧ fl (k : ℝ) ≤ (L : ℝ) + 1 / 256 := by
    intro k hk
    exact hr.pos_le hu0 (show k ≤ L by omega) hL
  have hsbk : ∀ k ≤ i, -(51 / 50) * fl (k : ℝ) ≤ sb * fl (k : ℝ) ∧
      sb * fl (k : ℝ) ≤ -(49 / 50) * fl (k : ℝ) := by
    intro k hk
    have h := (hpos k hk).1
    constructor <;>
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ sb + 51 / 50) h,
        mul_nonneg (by linarith : (0 : ℝ) ≤ -49 / 50 - sb) h]
  have hY : ∀ k ≤ i, |fl (sb * fl (k : ℝ)) - sb * fl (k : ℝ)| ≤ 11 / 2560 := by
    intro k hk
    obtain ⟨h1, h2⟩ := hpos k hk
    obtain ⟨h3, h4⟩ := hsbk k hk
    have hb : |sb * fl (k : ℝ)| ≤ 11 / 10 * (L : ℝ) := by
      rw [abs_le]; constructor <;> linarith
    have := hr.err hu0 hb
    calc _ ≤ u * (11 / 10 * (L : ℝ)) := this
      _ = 11 / 10 * (u * (L : ℝ)) := by ring
      _ ≤ 11 / 2560 := by linarith
  have hy0 : ∀ k ≤ i, fl (sb * fl (k : ℝ)) ≤ 0 := by
    intro k hk
    have h := hr.mono (sb * fl (k : ℝ)) 0 (by linarith [hsbk k hk, (hpos k hk).1])
    rwa [hr.zero] at h
  -- the N term
  obtain ⟨hq1, hq2⟩ := mul_iv (a := 39 / 10) (b := 41 / 10) (c := 9 / 10) (d := 11 / 10)
    (by norm_num) (by norm_num) hsa hV
  have hq : |sa * V0| ≤ 8 := by rw [abs_le]; constructor <;> linarith
  have hq3 := flb hr hu0 hu1 hq
  have hFL : |fl (L : ℝ) - L| ≤ 1 / 256 := le_trans (hr.natCast_near L) hL
  obtain ⟨hf1, hf2⟩ := abs_le.mp hFL
  have hprod := mul_iv (a := (L : ℝ) - 1 / 256) (b := (L : ℝ) + 1 / 256) (c := 35 / 10)
    (d := 452 / 100) (x := fl (L : ℝ)) (y := fl (sa * V0)) (by linarith) (by norm_num)
    ⟨by linarith, by linarith⟩ ⟨by linarith [hq3.1], by linarith [hq3.2]⟩
  have hpb : |fl (L : ℝ) * fl (sa * V0)| ≤ 46 / 10 * (L : ℝ) := by
    rw [abs_le]; constructor <;> linarith [hprod.1, hprod.2]
  have hNe := hr.err hu0 hpb
  have hNu : u * (46 / 10 * (L : ℝ)) ≤ 46 / 2560 := by
    calc u * (46 / 10 * (L : ℝ)) = 46 / 10 * (u * (L : ℝ)) := by ring
      _ ≤ 46 / 2560 := by linarith
  have hNe2 := abs_le.mp (le_trans hNe hNu)
  have hN1 : 7 / 2 * (L : ℝ) - 1 / 25 ≤ fl (fl (L : ℝ) * fl (sa * V0)) := by
    linarith [hprod.1, hNe2.1, hNe2.2]
  have hN2 : fl (fl (L : ℝ) * fl (sa * V0)) ≤ 23 / 5 * (L : ℝ) + 1 / 25 := by
    linarith [hprod.2, hNe2.1, hNe2.2]
  have e0 : fl (fl (L : ℝ) * fl (sa * 0)) = 0 := by simp [hr.zero]
  intro k hk hne
  rw [hsc k hk, hsc j0 hj0]
  rcases hfirst with ⟨hfj0, hbefore⟩ | ⟨hj00, hall⟩
  · rw [hfj0]
    rcases hf k hk with hk0 | hkV
    · rw [hk0, e0, add_zero, hr.idem]
      have hl := hy0 k hk
      have hy := abs_le.mp (hY j0 hj0)
      have hs := hsbk j0 hj0
      have hp := hpos j0 hj0
      have hyj := hy0 j0 hj0
      have hB : |fl (sb * fl (j0 : ℝ)) + fl (fl (L : ℝ) * fl (sa * V0))| ≤ 6 * (L : ℝ) := by
        rw [abs_le]; constructor <;> linarith
      have hlow := hr.lower hu0 hB
      have h6 : u * (6 * (L : ℝ)) ≤ 6 / 256 := by
        calc u * (6 * (L : ℝ)) = 6 * (u * (L : ℝ)) := by ring
          _ ≤ 6 / 256 := by linarith
      have hsum : 0 < fl (sb * fl (j0 : ℝ)) + fl (fl (L : ℝ) * fl (sa * V0)) - u * (6 * (L : ℝ)) := by
        linarith
      exact lt_of_le_of_lt hl (lt_of_lt_of_le hsum hlow)
    · rw [hkV]
      have hkj : j0 < k := by
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · have := hbefore k h
          rw [hkV] at this
          linarith [hV.1]
        · exact h
      have hg := hr.pos_gap hu0 hkj (show k ≤ L by omega) hL
      have hyk := abs_le.mp (hY k hk)
      have hyj := abs_le.mp (hY j0 hj0)
      have hsk := hsbk k hk
      have hsj := hsbk j0 hj0
      have hpk := hpos k hk
      have hpj := hpos j0 hj0
      have hy0k := hy0 k hk
      have hy0j := hy0 j0 hj0
      have hmul := mul_le_mul_of_nonpos_left hg (by linarith : sb ≤ 0)
      have h7 : u * (7 * (L : ℝ)) ≤ 7 / 256 := by
        calc u * (7 * (L : ℝ)) = 7 * (u * (L : ℝ)) := by ring
          _ ≤ 7 / 256 := by linarith
      apply hr.lt_of_gap hu0 (B := 7 * (L : ℝ))
      · rw [abs_le]; constructor <;> linarith
      · rw [abs_le]; constructor <;> linarith
      · linarith
  · subst hj00
    rw [hall k hk, hall 0 hj0]
    have e1 : fl (fl (sb * fl (((0 : ℕ) : ℝ))) + fl (fl (L : ℝ) * fl (sa * 0))) = 0 := by
      simp [hr.zero]
    have e2 : fl (fl (sb * fl (k : ℝ)) + fl (fl (L : ℝ) * fl (sa * 0))) = fl (sb * fl (k : ℝ)) := by
      simp [hr.zero, hr.idem]
    rw [e1, e2]
    have hg0 := hr.pos_gap hu0 (show 0 < k by omega) (show k ≤ L by omega) hL
    simp only [Nat.cast_zero, hr.zero, zero_add] at hg0
    have hyk := abs_le.mp (hY k hk)
    have hsk := hsbk k hk
    linarith

/-! ### closed forms -/

theorem score0_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (q0 q1 q2 q3 q4 q5 q6 qi qn k0 k1 k2 k3 k4 k5 k6 k7 kp kn : ℝ) :
    hd0.score fl dA [q0, q1, q2, q3, q4, q5, q6, 1, qi, qn]
      [k0, k1, k2, k3, k4, k5, k6, k7, kp, kn]
      = fl (fl (sw fl (-1) (dA 7 8) * kp) + fl (qn * fl (sw fl 4 (dA 9 1) * k1))) := by
  simp [Head.score, hd0, z10, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem]

theorem score1_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (q0 q1 q2 q3 q4 q5 q6 qi qn k0 k1 k2 k3 k4 k5 k6 k7 kp kn : ℝ) :
    hd1.score fl dA [q0, q1, q2, q3, q4, q5, q6, 1, qi, qn]
      [k0, k1, k2, k3, k4, k5, k6, k7, kp, kn]
      = fl (fl (sw fl (-1) (dA 7 8) * kp) + fl (qn * fl (sw fl 4 (dA 9 4) * k4))) := by
  simp [Head.score, hd1, z10, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem]

theorem blk0_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (n i j0 : ℕ)
    (x : ℕ → Vec) (a b c pj : ℕ → ℝ) (qn : ℝ) (a0 b0 c0 p0 q0 : ℝ)
    (hxi : x i = [a i, b i, c i, 0, 0, 0, 0, 1, pj i, qn])
    (hxj : x j0 = [a0, b0, c0, 0, 0, 0, 0, 1, p0, q0])
    (ha : fl (a i) = a i) (hb : fl (b i) = b i) (hc : fl (c i) = c i)
    (hp : fl (pj i) = pj i) (hq : fl qn = qn)
    (hsel : hd0.sel fl (p.A 0 0) n x i = [j0]) :
    blk0.apply fl p 0 n x i =
      [a i, b i, c i, fl (sw fl 1 (p.V 0 0 3 1) * b0),
       fl (sw fl 1 (p.W2 0 4 0) *
         relu (fl (fl (sw fl 1 (p.W1 0 0 0) * a i) +
           fl (sw fl (-10) (p.W1 0 0 3) * fl (sw fl 1 (p.V 0 0 3 1) * b0))))),
       0, 0, 1, pj i, qn] := by
  have hV : hd0.V = [z10, z10, z10, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], z10, z10, z10, z10, z10, z10] := rfl
  simp [Block.apply, blk0, headsApply, Head.attn, hsel, hV, attnRows, ravg_singleton hr, hxi, hxj,
    z10, radd, raffine, rdot, sw_zero hr, hr.zero, hr.idem, hr.one, ha, hb, hc, hp, hq]

theorem net_ok : Statement net := by
  intro u fl hr hu0 hu1 p hp w hw hn i hi1 hi
  skip

end Lane4.Case
