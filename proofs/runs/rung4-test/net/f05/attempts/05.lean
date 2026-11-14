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
    (hu1 : u ≤ 1 / 16777216) {x : ℝ} (hx : |x| ≤ 16) :
    x - 1 / 1000000 ≤ fl x ∧ fl x ≤ x + 1 / 1000000 := by
  have h := hr.err hu0 hx
  have h2 : u * 16 ≤ 1 / 1000000 := by linarith
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
  have hq : |sa * V0| ≤ 16 := by rw [abs_le]; constructor <;> linarith
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

noncomputable def preA (fl : ℝ → ℝ) (p : Pert) (c res : ℝ) : ℝ :=
  fl (fl (sw fl 1 (p.W1 1 0 2) * c) + fl (sw fl 1 (p.W1 1 0 5) * res))

noncomputable def preB (fl : ℝ → ℝ) (p : Pert) (c res : ℝ) : ℝ :=
  fl (fl (fl (sw fl 1 (p.W1 1 1 2) * c) + fl (sw fl 1 (p.W1 1 1 5) * res))
    + sw fl (-1) (p.b1 1 1))

noncomputable def outv (fl : ℝ → ℝ) (p : Pert) (c res : ℝ) : ℝ :=
  fl (fl (sw fl 1 (p.W2 1 6 0) * relu (preA fl p c res)) +
    fl (sw fl (-2) (p.W2 1 6 1) * relu (preB fl p c res)))

theorem blk1_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (n i j1 : ℕ)
    (x : ℕ → Vec) (a b c g F pj : ℕ → ℝ) (qn : ℝ) (a0 b0 c0 g0 F0 p0 q0 : ℝ)
    (hxi : x i = [a i, b i, c i, g i, F i, 0, 0, 1, pj i, qn])
    (hxj : x j1 = [a0, b0, c0, g0, F0, 0, 0, 1, p0, q0])
    (ha : fl (a i) = a i) (hb : fl (b i) = b i) (hc : fl (c i) = c i)
    (hg : fl (g i) = g i) (hF : fl (F i) = F i)
    (hp : fl (pj i) = pj i) (hq : fl qn = qn)
    (hsel : hd1.sel fl (p.A 1 0) n x i = [j1]) :
    blk1.apply fl p 1 n x i =
      [a i, b i, c i, g i, F i, fl (sw fl 1 (p.V 1 0 5 4) * F0),
       outv fl p (c i) (fl (sw fl 1 (p.V 1 0 5 4) * F0)), 1, pj i, qn] := by
  have hV : hd1.V = [z10, z10, z10, z10, z10, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], z10, z10, z10, z10] := rfl
  simp [Block.apply, blk1, headsApply, Head.attn, hsel, hV, attnRows, ravg_singleton hr, hxi, hxj,
    z10, radd, raffine, rdot, sw_zero hr, hr.zero, hr.idem, hr.one, ha, hb, hc, hg, hF, hp, hq,
    outv, preA, preB]

theorem run_eq (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) :
    net.run fl p w = blk1.apply fl p 1 (w.length + 1) (blk0.apply fl p 0 (w.length + 1) (net.init fl p w)) := by
  simp [TNet.run, net, runFrom]

theorem out_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (i : ℕ)
    (a b c g F res o pj qn : ℝ)
    (hrun : net.run fl p w i = [a, b, c, g, F, res, o, 1, pj, qn]) :
    net.out fl p w i = fl (sw fl 1 (p.oW 6) * o) := by
  unfold TNet.out
  rw [hrun]
  simp [net, rdot, sw_zero hr, hr.zero, hr.idem]

/-! ### initial state -/

noncomputable def fa (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  if tokAt w j = 2 then sw fl 1 (p.E 2 0) else 0

noncomputable def fb (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  if tokAt w j = 3 then sw fl 1 (p.E 3 1) else 0

noncomputable def fcc (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  if tokAt w j = 1 then sw fl 1 (p.E 1 2) else if tokAt w j = 3 then sw fl 1 (p.E 3 2)
  else if tokAt w j = 4 then sw fl 1 (p.E 4 2) else 0

theorem fa_fix {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ) :
    fl (fa fl p w j) = fa fl p w j := by
  unfold fa; split_ifs
  · exact fl_sw hr _ _
  · exact hr.zero

theorem fb_fix {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ) :
    fl (fb fl p w j) = fb fl p w j := by
  unfold fb; split_ifs
  · exact fl_sw hr _ _
  · exact hr.zero

theorem fcc_fix {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ) :
    fl (fcc fl p w j) = fcc fl p w j := by
  unfold fcc; split_ifs
  · exact fl_sw hr _ _
  · exact fl_sw hr _ _
  · exact fl_sw hr _ _
  · exact hr.zero

theorem tok_le4 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) : tokAt w j ≤ 4 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) :
    net.init fl p w j = [fa fl p w j, fb fl p w j, fcc fl p w j, 0, 0, 0, 0, 1,
      fl (j : ℝ), fl ((w.length + 1 : ℕ) : ℝ)] := by
  have h5 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 := by
    have := tok_le4 w hw j
    omega
  rcases h5 with h | h | h | h | h <;>
    simp [TNet.init, net, swRow, h, sw_zero hr, fa, fb, fcc, pos]

/-! ### first position and the reference semantics -/

theorem first_exists (P : ℕ → Prop) (i : ℕ) :
    ∃ j0, j0 ≤ i ∧ ((P j0 ∧ ∀ m, m < j0 → ¬ P m) ∨ (j0 = 0 ∧ ∀ m, m ≤ i → ¬ P m)) := by
  classical
  by_cases h : ∃ m, m ≤ i ∧ P m
  · refine ⟨Nat.find h, (Nat.find_spec h).1, Or.inl ⟨(Nat.find_spec h).2, ?_⟩⟩
    intro m hm hPm
    exact Nat.find_min h hm ⟨by have := (Nat.find_spec h).1; omega, hPm⟩
  · refine ⟨0, Nat.zero_le _, Or.inr ⟨rfl, ?_⟩⟩
    intro m hm hPm
    exact h ⟨m, hm, hPm⟩

theorem code_unmarked (t : ℕ) (h2 : t ≠ 2) (h3 : t ≠ 3) : code t = 0 := by
  unfold code
  split_ifs <;> omega

theorem firstc_succ (w : List ℕ) (i : ℕ) (h : i < w.length) :
    firstc (w.take (i + 1)) =
      (if firstc (w.take i) = 0 then code (tokAt w (i + 1)) else firstc (w.take i)) := by
  have ht : w.take (i + 1) = w.take i ++ [w[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h]
    first | rfl | simp
  unfold firstc
  rw [ht, List.foldl_append]
  simp [Lane4.Seq.tokAt_succ w i h]

theorem fc_inv (w : List ℕ) : ∀ i, i ≤ w.length →
    ((∀ m, 1 ≤ m → m ≤ i → tokAt w m ≠ 2 ∧ tokAt w m ≠ 3) → firstc (w.take i) = 0) ∧
    (∀ j, 1 ≤ j → j ≤ i → (tokAt w j = 2 ∨ tokAt w j = 3) →
      (∀ t, 1 ≤ t → t < j → tokAt w t ≠ 2 ∧ tokAt w t ≠ 3) →
      firstc (w.take i) = code (tokAt w j)) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨fun _ => rfl, ?_⟩
    intro j h1 h2
    omega
  | succ i ih =>
    intro hi
    obtain ⟨u1, u2⟩ := ih (by omega)
    rw [firstc_succ w i (by omega)]
    constructor
    · intro hall
      have h0 : firstc (w.take i) = 0 := u1 (fun m h1 h2 => hall m h1 (by omega))
      rw [if_pos h0]
      have h := hall (i + 1) (by omega) le_rfl
      exact code_unmarked _ h.1 h.2
    · intro j h1 h2 hm hb
      by_cases hji : j ≤ i
      · have hs := u2 j h1 hji hm hb
        have hne : firstc (w.take i) ≠ 0 := by
          rw [hs]; rcases hm with h | h <;> simp [code, h]
        rw [if_neg hne, hs]
      · have hj : j = i + 1 := by omega
        subst hj
        have h0 := u1 (fun m hm1 hm2 => hb m hm1 (by omega))
        rw [if_pos h0]

theorem fc_char (w : List ℕ) (i : ℕ) (hi : i ≤ w.length) :
    (firstc (w.take i) = 2 ∧ ∃ m, m ≤ i ∧ tokAt w m = 2 ∧ ∀ t, t ≤ m → tokAt w t ≠ 3) ∨
    (firstc (w.take i) ≠ 2 ∧ ¬ ∃ m, m ≤ i ∧ tokAt w m = 2 ∧ ∀ t, t ≤ m → tokAt w t ≠ 3) := by
  obtain ⟨j, hj, hcase⟩ :=
    first_exists (fun m => 1 ≤ m ∧ (tokAt w m = 2 ∨ tokAt w m = 3)) i
  obtain ⟨u1, u2⟩ := fc_inv w i hi
  rcases hcase with ⟨⟨h1, hm⟩, hbefore⟩ | ⟨hj0, hnone⟩
  · have hun : ∀ t, 1 ≤ t → t < j → tokAt w t ≠ 2 ∧ tokAt w t ≠ 3 := by
      intro t ht1 htj
      have := hbefore t htj
      exact ⟨fun h => this ⟨ht1, Or.inl h⟩, fun h => this ⟨ht1, Or.inr h⟩⟩
    have hfc := u2 j h1 hj hm hun
    rcases hm with h2 | h3
    · left
      refine ⟨by rw [hfc, h2]; rfl, j, hj, h2, ?_⟩
      intro t ht
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · subst h0; rw [Lane4.Seq.tokAt_zero]; omega
      · rcases Nat.lt_or_ge t j with hlt | hge
        · exact (hun t hpos hlt).2
        · have : t = j := by omega
          subst this; omega
    · right
      refine ⟨by rw [hfc, h3]; decide, ?_⟩
      rintro ⟨m, hm, hm2, hno3⟩
      rcases Nat.lt_or_ge m j with hlt | hge
      · rcases Nat.eq_zero_or_pos m with h0 | hpos
        · subst h0; rw [Lane4.Seq.tokAt_zero] at hm2; omega
        · exact (hun m hpos hlt).1 hm2
      · exact hno3 j hge h3
  · subst hj0
    have hun : ∀ m, 1 ≤ m → m ≤ i → tokAt w m ≠ 2 ∧ tokAt w m ≠ 3 := by
      intro m hm1 hm2
      have := hnone m hm2
      exact ⟨fun h => this ⟨hm1, Or.inl h⟩, fun h => this ⟨hm1, Or.inr h⟩⟩
    have hfc := u1 hun
    right
    refine ⟨by rw [hfc]; omega, ?_⟩
    rintro ⟨m, hm, hm2, _⟩
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; rw [Lane4.Seq.tokAt_zero] at hm2; omega
    · exact (hun m hpos hm).1 hm2

/-! ### numeric lemmas -/

theorem sw1_iv {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    188 / 189 ≤ sw fl 1 d ∧ sw fl 1 d ≤ 190 / 189 := by
  have h := sw_pos hr hu0 hu1 1 (by norm_num) hd
  norm_num at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem sw4_iv {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    752 / 189 ≤ sw fl 4 d ∧ sw fl 4 d ≤ 760 / 189 := by
  have h := sw_pos hr hu0 hu1 4 (by norm_num) hd
  norm_num at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem swn1_iv {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    -190 / 189 ≤ sw fl (-1) d ∧ sw fl (-1) d ≤ -188 / 189 := by
  rw [sw_neg hr 1 d]
  have h := sw1_iv hr hu0 hu1 hd
  constructor <;> linarith [h.1, h.2]

theorem swn2_iv {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    -380 / 189 ≤ sw fl (-2) d ∧ sw fl (-2) d ≤ -376 / 189 := by
  rw [sw_neg hr 2 d]
  have h := sw_pos hr hu0 hu1 2 (by norm_num) hd
  norm_num at h
  constructor <;> linarith [h.1, h.2]

theorem swn10_iv {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    -1900 / 189 ≤ sw fl (-10) d ∧ sw fl (-10) d ≤ -1880 / 189 := by
  rw [sw_neg hr 10 d]
  have h := sw_pos hr hu0 hu1 10 (by norm_num) hd
  norm_num at h
  constructor <;> linarith [h.1, h.2]

theorem fl_in {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {x lo hi : ℝ} (h1 : lo ≤ x) (h2 : x ≤ hi) (h3 : -16 ≤ lo)
    (h4 : hi ≤ 16) : lo - 1 / 1000000 ≤ fl x ∧ fl x ≤ hi + 1 / 1000000 := by
  have := flb hr hu0 hu1 (x := x) (by rw [abs_le]; constructor <;> linarith)
  constructor <;> linarith [this.1, this.2]

theorem flprod {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {x y a b c d : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : b ≤ 4)
    (hd : d ≤ 4) (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    a * c - 1 / 1000000 ≤ fl (x * y) ∧ fl (x * y) ≤ b * d + 1 / 1000000 := by
  obtain ⟨h1, h2⟩ := mul_iv ha hc hx hy
  have hb0 : 0 ≤ b := le_trans ha (le_trans hx.1 hx.2)
  have hd0 : 0 ≤ d := le_trans hc (le_trans hy.1 hy.2)
  have hbd : b * d ≤ 16 := by
    have := mul_le_mul hb hd hd0 (by norm_num : (0 : ℝ) ≤ 4)
    linarith
  have hac := mul_nonneg ha hc
  exact fl_in hr hu0 hu1 h1 h2 (by linarith) hbd

theorem pre_nog {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (s1 sn a : ℝ) (hs1 : 0 ≤ s1)
    (ha : 0 ≤ a) : relu (fl (fl (s1 * a) + fl (sn * 0))) = fl (s1 * a) := by
  have h0 : 0 ≤ fl (s1 * a) := hr.nonneg (mul_nonneg hs1 ha)
  have e : fl (fl (s1 * a) + fl (sn * 0)) = fl (s1 * a) := by simp [hr.zero, hr.idem]
  rw [e]
  exact Lane4.relu_of_nonneg h0

theorem pre_has3 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (s1 sn a g : ℝ) (hs1 : 0 ≤ s1 ∧ s1 ≤ 11 / 10)
    (hsn : -101 / 10 ≤ sn ∧ sn ≤ -9) (ha : 0 ≤ a ∧ a ≤ 11 / 10)
    (hg : 49 / 100 ≤ g ∧ g ≤ 11 / 10) :
    relu (fl (fl (s1 * a) + fl (sn * g))) = 0 := by
  apply Lane4.relu_of_nonpos
  have hp1 := mul_iv (a := 0) (b := 11 / 10) (c := 0) (d := 11 / 10) le_rfl le_rfl hs1 ha
  have f1 := fl_in hr hu0 hu1 (x := s1 * a) (lo := 0 * 0) (hi := 11 / 10 * (11 / 10))
    hp1.1 hp1.2 (by norm_num) (by norm_num)
  have h2 : sn * g ≤ -441 / 100 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ -9 - sn by linarith) (show (0 : ℝ) ≤ g by linarith)]
  have h3 : -1111 / 100 ≤ sn * g := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ sn + 101 / 10 by linarith) (show (0 : ℝ) ≤ g by linarith)]
  have f2 := fl_in hr hu0 hu1 (x := sn * g) h3 h2 (by norm_num) (by norm_num)
  have f3 := fl_in hr hu0 hu1 (x := fl (s1 * a) + fl (sn * g)) (lo := -12) (hi := -1)
    (by linarith [f1.1, f2.1]) (by linarith [f1.2, f2.2]) (by norm_num) (by norm_num)
  linarith [f3.2]

noncomputable def Fexp (fl : ℝ → ℝ) (p : Pert) (a g : ℝ) : ℝ :=
  fl (sw fl 1 (p.W2 0 4 0) *
    relu (fl (fl (sw fl 1 (p.W1 0 0 0) * a) + fl (sw fl (-10) (p.W1 0 0 3) * g))))

noncomputable def Fa (fl : ℝ → ℝ) (p : Pert) : ℝ :=
  fl (sw fl 1 (p.W2 0 4 0) * fl (sw fl 1 (p.W1 0 0 0) * sw fl 1 (p.E 2 0)))

noncomputable def Gc (fl : ℝ → ℝ) (p : Pert) : ℝ :=
  fl (sw fl 1 (p.V 0 0 3 1) * sw fl 1 (p.E 3 1))

theorem Fexp_fix {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (a g : ℝ) :
    fl (Fexp fl p a g) = Fexp fl p a g := by
  unfold Fexp; exact hr.idem _

theorem F_nog_zero {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) :
    Fexp fl p 0 0 = 0 := by
  simp [Fexp, hr.zero, relu]

theorem F_nog_two {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) :
    Fexp fl p (sw fl 1 (p.E 2 0)) 0 = Fa fl p := by
  have hs1 := sw1_iv hr hu0 hu1 (hp.W1 0 0 0)
  have hM := sw1_iv hr hu0 hu1 (hp.E 2 0)
  unfold Fexp Fa
  rw [pre_nog hr _ _ _ (by linarith [hs1.1]) (by linarith [hM.1])]

theorem F_has3 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (a g : ℝ)
    (ha : 0 ≤ a ∧ a ≤ 11 / 10) (hg : 49 / 100 ≤ g ∧ g ≤ 11 / 10) :
    Fexp fl p a g = 0 := by
  have hs1 := sw1_iv hr hu0 hu1 (hp.W1 0 0 0)
  have hsn := swn10_iv hr hu0 hu1 (hp.W1 0 0 3)
  unfold Fexp
  rw [pre_has3 hr hu0 hu1 _ _ a g ⟨by linarith [hs1.1], by linarith [hs1.2]⟩
    ⟨by linarith [hsn.1], by linarith [hsn.2]⟩ ha hg]
  simp [hr.zero]

theorem Fa_iv {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) :
    49 / 50 ≤ Fa fl p ∧ Fa fl p ≤ 51 / 50 := by
  have hs1 := sw1_iv hr hu0 hu1 (hp.W1 0 0 0)
  have hM := sw1_iv hr hu0 hu1 (hp.E 2 0)
  have hW := sw1_iv hr hu0 hu1 (hp.W2 0 4 0)
  have t := flprod hr hu0 hu1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hs1 hM
  have t2 := flprod hr hu0 hu1 (x := sw fl 1 (p.W2 0 4 0)) (y := fl (sw fl 1 (p.W1 0 0 0) * sw fl 1 (p.E 2 0)))
    (a := 188 / 189) (b := 190 / 189) (c := 989 / 1000) (d := 1011 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hW ⟨by linarith [t.1], by linarith [t.2]⟩
  unfold Fa
  constructor <;> linarith [t2.1, t2.2]

theorem Gc_iv {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) :
    49 / 50 ≤ Gc fl p ∧ Gc fl p ≤ 51 / 50 := by
  have hV := sw1_iv hr hu0 hu1 (hp.V 0 0 3 1)
  have hM := sw1_iv hr hu0 hu1 (hp.E 3 1)
  have t := flprod hr hu0 hu1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hV hM
  unfold Gc
  constructor <;> linarith [t.1, t.2]

/-! ### the second MLP -/

theorem outv_zero {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) :
    outv fl p 0 0 = 0 := by
  have hnb := swn1_iv hr hu0 hu1 (hp.b1 1 1)
  have eA : preA fl p 0 0 = 0 := by simp [preA, hr.zero]
  have eB : preB fl p 0 0 = sw fl (-1) (p.b1 1 1) := by
    simp [preB, hr.zero, fl_sw hr]
  have hB : relu (preB fl p 0 0) = 0 := by
    rw [eB]; exact Lane4.relu_of_nonpos (by linarith [hnb.2])
  have hA : relu (preA fl p 0 0) = 0 := by
    rw [eA]; simp [relu]
  unfold outv
  rw [hA, hB]
  simp [hr.zero]

theorem outv_one_c {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (c : ℝ)
    (hc : 994 / 1000 ≤ c ∧ c ≤ 1006 / 1000) :
    85 / 100 ≤ outv fl p c 0 ∧ outv fl p c 0 ≤ 11 / 10 := by
  have ha1 := sw1_iv hr hu0 hu1 (hp.W1 1 0 2)
  have hb1 := sw1_iv hr hu0 hu1 (hp.W1 1 1 2)
  have hnb := swn1_iv hr hu0 hu1 (hp.b1 1 1)
  have hw2 := sw1_iv hr hu0 hu1 (hp.W2 1 6 0)
  have hn2 := swn2_iv hr hu0 hu1 (hp.W2 1 6 1)
  have eA : preA fl p c 0 = fl (sw fl 1 (p.W1 1 0 2) * c) := by
    simp [preA, hr.zero, hr.idem]
  have eB : preB fl p c 0 = fl (fl (sw fl 1 (p.W1 1 1 2) * c) + sw fl (-1) (p.b1 1 1)) := by
    simp [preB, hr.zero, hr.idem]
  have t1 := flprod hr hu0 hu1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha1 hc
  have t1' := flprod hr hu0 hu1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hb1 hc
  have hB := fl_in hr hu0 hu1 (x := fl (sw fl 1 (p.W1 1 1 2) * c) + sw fl (-1) (p.b1 1 1))
    (lo := -2 / 100) (hi := 2 / 100) (by linarith [t1'.1, hnb.1]) (by linarith [t1'.2, hnb.2])
    (by norm_num) (by norm_num)
  have hrB0 : 0 ≤ relu (preB fl p c 0) := le_max_right _ _
  have hrB1 : relu (preB fl p c 0) ≤ 21 / 1000 := by
    unfold relu; rw [eB]; exact max_le (by linarith [hB.2]) (by norm_num)
  have hrA : relu (preA fl p c 0) = preA fl p c 0 := by
    apply Lane4.relu_of_nonneg; rw [eA]; linarith [t1.1]
  have hAb : 988 / 1000 ≤ preA fl p c 0 ∧ preA fl p c 0 ≤ 1012 / 1000 := by
    rw [eA]; constructor <;> linarith [t1.1, t1.2]
  have u1 := flprod hr hu0 hu1 (x := sw fl 1 (p.W2 1 6 0)) (y := relu (preA fl p c 0))
    (a := 188 / 189) (b := 190 / 189) (c := 988 / 1000) (d := 1012 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hw2
    ⟨by rw [hrA]; exact hAb.1, by rw [hrA]; exact hAb.2⟩
  have m := mul_iv (x := -sw fl (-2) (p.W2 1 6 1)) (y := relu (preB fl p c 0))
    (a := 376 / 189) (b := 380 / 189) (c := 0) (d := 21 / 1000) (by norm_num) le_rfl
    ⟨by linarith [hn2.2], by linarith [hn2.1]⟩ ⟨hrB0, hrB1⟩
  have u2 := fl_in hr hu0 hu1 (x := sw fl (-2) (p.W2 1 6 1) * relu (preB fl p c 0))
    (lo := -43 / 1000) (hi := 0) (by linarith [m.2]) (by linarith [m.1]) (by norm_num)
    (by norm_num)
  have hs := fl_in hr hu0 hu1
    (x := fl (sw fl 1 (p.W2 1 6 0) * relu (preA fl p c 0)) +
      fl (sw fl (-2) (p.W2 1 6 1) * relu (preB fl p c 0)))
    (lo := 93 / 100) (hi := 103 / 100) (by linarith [u1.1, u2.1]) (by linarith [u1.2, u2.2])
    (by norm_num) (by norm_num)
  unfold outv
  constructor <;> linarith [hs.1, hs.2]

theorem outv_one_r {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (res : ℝ)
    (hc : 97 / 100 ≤ res ∧ res ≤ 103 / 100) :
    85 / 100 ≤ outv fl p 0 res ∧ outv fl p 0 res ≤ 11 / 10 := by
  have ha2 := sw1_iv hr hu0 hu1 (hp.W1 1 0 5)
  have hb2 := sw1_iv hr hu0 hu1 (hp.W1 1 1 5)
  have hnb := swn1_iv hr hu0 hu1 (hp.b1 1 1)
  have hw2 := sw1_iv hr hu0 hu1 (hp.W2 1 6 0)
  have hn2 := swn2_iv hr hu0 hu1 (hp.W2 1 6 1)
  have eA : preA fl p 0 res = fl (sw fl 1 (p.W1 1 0 5) * res) := by
    simp [preA, hr.zero, hr.idem]
  have eB : preB fl p 0 res = fl (fl (sw fl 1 (p.W1 1 1 5) * res) + sw fl (-1) (p.b1 1 1)) := by
    simp [preB, hr.zero, hr.idem]
  have t1 := flprod hr hu0 hu1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha2 hc
  have t1' := flprod hr hu0 hu1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hb2 hc
  have hB := fl_in hr hu0 hu1 (x := fl (sw fl 1 (p.W1 1 1 5) * res) + sw fl (-1) (p.b1 1 1))
    (lo := -42 / 1000) (hi := 42 / 1000) (by linarith [t1'.1, hnb.1]) (by linarith [t1'.2, hnb.2])
    (by norm_num) (by norm_num)
  have hrB0 : 0 ≤ relu (preB fl p 0 res) := le_max_right _ _
  have hrB1 : relu (preB fl p 0 res) ≤ 43 / 1000 := by
    unfold relu; rw [eB]; exact max_le (by linarith [hB.2]) (by norm_num)
  have hrA : relu (preA fl p 0 res) = preA fl p 0 res := by
    apply Lane4.relu_of_nonneg; rw [eA]; linarith [t1.1]
  have hAb : 96 / 100 ≤ preA fl p 0 res ∧ preA fl p 0 res ≤ 1036 / 1000 := by
    rw [eA]; constructor <;> linarith [t1.1, t1.2]
  have u1 := flprod hr hu0 hu1 (x := sw fl 1 (p.W2 1 6 0)) (y := relu (preA fl p 0 res))
    (a := 188 / 189) (b := 190 / 189) (c := 96 / 100) (d := 1036 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hw2
    ⟨by rw [hrA]; exact hAb.1, by rw [hrA]; exact hAb.2⟩
  have m := mul_iv (x := -sw fl (-2) (p.W2 1 6 1)) (y := relu (preB fl p 0 res))
    (a := 376 / 189) (b := 380 / 189) (c := 0) (d := 43 / 1000) (by norm_num) le_rfl
    ⟨by linarith [hn2.2], by linarith [hn2.1]⟩ ⟨hrB0, hrB1⟩
  have u2 := fl_in hr hu0 hu1 (x := sw fl (-2) (p.W2 1 6 1) * relu (preB fl p 0 res))
    (lo := -87 / 1000) (hi := 0) (by linarith [m.2]) (by linarith [m.1]) (by norm_num)
    (by norm_num)
  have hs := fl_in hr hu0 hu1
    (x := fl (sw fl 1 (p.W2 1 6 0) * relu (preA fl p 0 res)) +
      fl (sw fl (-2) (p.W2 1 6 1) * relu (preB fl p 0 res)))
    (lo := 86 / 100) (hi := 105 / 100) (by linarith [u1.1, u2.1]) (by linarith [u1.2, u2.2])
    (by norm_num) (by norm_num)
  unfold outv
  constructor <;> linarith [hs.1, hs.2]

theorem outv_two {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (c res : ℝ)
    (hc : 994 / 1000 ≤ c ∧ c ≤ 1006 / 1000) (hres : 97 / 100 ≤ res ∧ res ≤ 103 / 100) :
    -1 / 5 ≤ outv fl p c res ∧ outv fl p c res ≤ 1 / 5 := by
  have ha1 := sw1_iv hr hu0 hu1 (hp.W1 1 0 2)
  have ha2 := sw1_iv hr hu0 hu1 (hp.W1 1 0 5)
  have hb1 := sw1_iv hr hu0 hu1 (hp.W1 1 1 2)
  have hb2 := sw1_iv hr hu0 hu1 (hp.W1 1 1 5)
  have hnb := swn1_iv hr hu0 hu1 (hp.b1 1 1)
  have hw2 := sw1_iv hr hu0 hu1 (hp.W2 1 6 0)
  have hn2 := swn2_iv hr hu0 hu1 (hp.W2 1 6 1)
  have t1 := flprod hr hu0 hu1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha1 hc
  have t2 := flprod hr hu0 hu1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha2 hres
  have t1' := flprod hr hu0 hu1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hb1 hc
  have t2' := flprod hr hu0 hu1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hb2 hres
  have hA := fl_in hr hu0 hu1
    (x := fl (sw fl 1 (p.W1 1 0 2) * c) + fl (sw fl 1 (p.W1 1 0 5) * res))
    (lo := 195 / 100) (hi := 205 / 100) (by linarith [t1.1, t2.1]) (by linarith [t1.2, t2.2])
    (by norm_num) (by norm_num)
  have hY := fl_in hr hu0 hu1
    (x := fl (sw fl 1 (p.W1 1 1 2) * c) + fl (sw fl 1 (p.W1 1 1 5) * res))
    (lo := 195 / 100) (hi := 205 / 100) (by linarith [t1'.1, t2'.1]) (by linarith [t1'.2, t2'.2])
    (by norm_num) (by norm_num)
  have hZ := fl_in hr hu0 hu1
    (x := fl (fl (sw fl 1 (p.W1 1 1 2) * c) + fl (sw fl 1 (p.W1 1 1 5) * res)) +
      sw fl (-1) (p.b1 1 1))
    (lo := 94 / 100) (hi := 106 / 100) (by linarith [hY.1, hnb.1]) (by linarith [hY.2, hnb.2])
    (by norm_num) (by norm_num)
  have hrA : relu (preA fl p c res) = preA fl p c res := by
    apply Lane4.relu_of_nonneg; unfold preA; linarith [hA.1]
  have hrB : relu (preB fl p c res) = preB fl p c res := by
    apply Lane4.relu_of_nonneg; unfold preB; linarith [hZ.1]
  have hAb : 1949 / 1000 ≤ preA fl p c res ∧ preA fl p c res ≤ 2051 / 1000 := by
    unfold preA; constructor <;> linarith [hA.1, hA.2]
  have hBb : 939 / 1000 ≤ preB fl p c res ∧ preB fl p c res ≤ 1061 / 1000 := by
    unfold preB; constructor <;> linarith [hZ.1, hZ.2]
  have u1 := flprod hr hu0 hu1 (x := sw fl 1 (p.W2 1 6 0)) (y := relu (preA fl p c res))
    (a := 188 / 189) (b := 190 / 189) (c := 1949 / 1000) (d := 2051 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hw2
    ⟨by rw [hrA]; exact hAb.1, by rw [hrA]; exact hAb.2⟩
  have m := mul_iv (x := -sw fl (-2) (p.W2 1 6 1)) (y := relu (preB fl p c res))
    (a := 376 / 189) (b := 380 / 189) (c := 939 / 1000) (d := 1061 / 1000)
    (by norm_num) (by norm_num)
    ⟨by linarith [hn2.2], by linarith [hn2.1]⟩
    ⟨by rw [hrB]; exact hBb.1, by rw [hrB]; exact hBb.2⟩
  have u2 := fl_in hr hu0 hu1 (x := sw fl (-2) (p.W2 1 6 1) * relu (preB fl p c res))
    (lo := -2134 / 1000) (hi := -1868 / 1000) (by linarith [m.2]) (by linarith [m.1])
    (by norm_num) (by norm_num)
  have hs := fl_in hr hu0 hu1
    (x := fl (sw fl 1 (p.W2 1 6 0) * relu (preA fl p c res)) +
      fl (sw fl (-2) (p.W2 1 6 1) * relu (preB fl p c res)))
    (lo := -197 / 1000) (hi := 197 / 1000) (by linarith [u1.1, u2.1]) (by linarith [u1.2, u2.2])
    (by norm_num) (by norm_num)
  unfold outv
  constructor <;> linarith [hs.1, hs.2]

/-! ### final read-out -/

theorem fin_one {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (s o : ℝ) (hs : 188 / 189 ≤ s ∧ s ≤ 190 / 189)
    (ho : 85 / 100 ≤ o ∧ o ≤ 11 / 10) : |fl (s * o) - 1| ≤ 1 / 4 := by
  have m := mul_iv (by norm_num) (by norm_num) hs ho
  have f := fl_in hr hu0 hu1 (x := s * o) m.1 m.2 (by norm_num) (by norm_num)
  rw [abs_le]; constructor <;> linarith [f.1, f.2]

theorem fin_zero {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (s o : ℝ) (hs : 188 / 189 ≤ s ∧ s ≤ 190 / 189)
    (ho : -1 / 5 ≤ o ∧ o ≤ 1 / 5) : |fl (s * o) - 0| ≤ 1 / 4 := by
  have h1 : s * o ≤ 1 / 5 * s := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ s by linarith [hs.1]) (show (0 : ℝ) ≤ 1 / 5 - o by linarith [ho.2])]
  have h2 : -(1 / 5) * s ≤ s * o := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ s by linarith [hs.1]) (show (0 : ℝ) ≤ o + 1 / 5 by linarith [ho.1])]
  have f := fl_in hr hu0 hu1 (x := s * o) (lo := -22 / 100) (hi := 22 / 100)
    (by linarith [hs.2]) (by linarith [hs.2]) (by norm_num) (by norm_num)
  rw [abs_le]; constructor <;> linarith [f.1, f.2]

theorem fin_exact {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (s : ℝ) :
    |fl (s * 0) - 0| ≤ 1 / 4 := by
  simp [hr.zero]

theorem fa_cases (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (k : ℕ) :
    (tokAt w k = 2 → fa fl p w k = sw fl 1 (p.E 2 0)) ∧ (tokAt w k ≠ 2 → fa fl p w k = 0) :=
  ⟨fun h => by simp [fa, h], fun h => by simp [fa, h]⟩

theorem tok_getD (w : List ℕ) (i : ℕ) (h1 : 1 ≤ i) : w.getD (i - 1) 0 = tokAt w i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  simp [tokAt]

theorem tok_real (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) (h1 : 1 ≤ i)
    (h2 : i ≤ w.length) : 1 ≤ tokAt w i ∧ tokAt w i ≤ 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Lane4.Seq.tokAt_succ w k (by omega)]
  exact hw _ (List.getElem_mem (by omega))

theorem stage0 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (hlen : 1 ≤ w.length) :
    ∀ k, ∃ g F : ℝ, k ≤ w.length →
      (blk0.apply fl p 0 (w.length + 1) (net.init fl p w) k =
        [fa fl p w k, fb fl p w k, fcc fl p w k, g, F, 0, 0, 1, fl (k : ℝ),
          fl ((w.length + 1 : ℕ) : ℝ)] ∧
      fl g = g ∧ fl F = F ∧
      ((∃ t, t ≤ k ∧ tokAt w t = 3) → g = Gc fl p) ∧
      ((¬∃ t, t ≤ k ∧ tokAt w t = 3) → g = 0) ∧
      ((tokAt w k = 2 ∧ ¬∃ t, t ≤ k ∧ tokAt w t = 3) → F = Fa fl p) ∧
      (¬(tokAt w k = 2 ∧ ¬∃ t, t ≤ k ∧ tokAt w t = 3) → F = 0)) := by
  intro k
  by_cases hk : k ≤ w.length
  swap
  · exact ⟨0, 0, fun h => absurd h hk⟩
  have hL : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 := hn
  have hLn : 2 ≤ w.length + 1 := by omega
  obtain ⟨j0, hj0, hcase⟩ := first_exists (fun m => tokAt w m = 3) k
  have hfb : ∀ m, m ≤ k → fb fl p w m = 0 ∨ fb fl p w m = sw fl 1 (p.E 3 1) := by
    intro m _
    by_cases h : tokAt w m = 3
    · right; simp [fb, h]
    · left; simp [fb, h]
  have hfirst : (fb fl p w j0 = sw fl 1 (p.E 3 1) ∧ ∀ m, m < j0 → fb fl p w m = 0) ∨
      (j0 = 0 ∧ ∀ m, m ≤ k → fb fl p w m = 0) := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨by simp [fb, h1], fun m hm => ?_⟩
      have hm3 : tokAt w m ≠ 3 := h2 m hm
      simp [fb, hm3]
    · right
      refine ⟨h1, fun m hm => ?_⟩
      have hm3 : tokAt w m ≠ 3 := h2 m hm
      simp [fb, hm3]
  have hsc : ∀ m, m ≤ k → hd0.score fl (p.A 0 0) (net.init fl p w k) (net.init fl p w m) =
      fl (fl (sw fl (-1) (p.A 0 0 7 8) * fl (m : ℝ)) +
        fl (fl ((w.length + 1 : ℕ) : ℝ) * fl (sw fl 4 (p.A 0 0 9 1) * fb fl p w m))) := by
    intro m _
    rw [init_eq hr p w hw k, init_eq hr p w hw m, score0_eq hr]
  have hsa := sw4_iv hr hu0 hu1 (hp.A 0 0 9 1)
  have hsb := swn1_iv hr hu0 hu1 (hp.A 0 0 7 8)
  have hM3 := sw1_iv hr hu0 hu1 (hp.E 3 1)
  have hsel : hd0.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) k = [j0] := by
    apply Head.sel_unique
    · rw [show hd0.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal]; exact hj0
    · intro m hm hne
      rw [show hd0.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal] at hm
      exact sel_core hr hu0 hu1 (w.length + 1) k hL (by omega) hLn
        (sw fl 4 (p.A 0 0 9 1)) (sw fl (-1) (p.A 0 0 7 8)) (sw fl 1 (p.E 3 1))
        ⟨by linarith [hsa.1], by linarith [hsa.2]⟩ ⟨by linarith [hsb.1], by linarith [hsb.2]⟩
        ⟨by linarith [hM3.1], by linarith [hM3.2]⟩ (fb fl p w) hfb j0 hj0 hfirst
        (fun m => hd0.score fl (p.A 0 0) (net.init fl p w k) (net.init fl p w m)) hsc m hm hne
  have hb := blk0_eq hr p (w.length + 1) k j0 (net.init fl p w) (fa fl p w) (fb fl p w)
    (fcc fl p w) (fun j => fl (j : ℝ)) (fl ((w.length + 1 : ℕ) : ℝ)) (fa fl p w j0)
    (fb fl p w j0) (fcc fl p w j0) (fl (j0 : ℝ)) (fl ((w.length + 1 : ℕ) : ℝ))
    (init_eq hr p w hw k) (init_eq hr p w hw j0) (fa_fix hr p w k) (fb_fix hr p w k)
    (fcc_fix hr p w k) (hr.idem _) (hr.idem _) hsel
  have hgG : (∃ t, t ≤ k ∧ tokAt w t = 3) →
      fl (sw fl 1 (p.V 0 0 3 1) * fb fl p w j0) = Gc fl p := by
    intro hex
    rcases hcase with ⟨h3, _⟩ | ⟨h0, hall⟩
    · have : fb fl p w j0 = sw fl 1 (p.E 3 1) := by simp [fb, h3]
      rw [this]; rfl
    · obtain ⟨t, ht, ht3⟩ := hex
      exact absurd ht3 (hall t ht)
  have hg0 : (¬∃ t, t ≤ k ∧ tokAt w t = 3) →
      fl (sw fl 1 (p.V 0 0 3 1) * fb fl p w j0) = 0 := by
    intro hnex
    rcases hcase with ⟨h3, _⟩ | ⟨h0, _⟩
    · exact absurd ⟨j0, hj0, h3⟩ hnex
    · rw [h0]; simp [fb, Lane4.Seq.tokAt_zero, hr.zero]
  have hfa := fa_cases fl p w k
  have hfab : 0 ≤ fa fl p w k ∧ fa fl p w k ≤ 11 / 10 := by
    by_cases h : tokAt w k = 2
    · rw [(hfa.1 h)]
      have := sw1_iv hr hu0 hu1 (hp.E 2 0)
      constructor <;> linarith [this.1, this.2]
    · rw [hfa.2 h]; norm_num
  have hGb := Gc_iv hr hu0 hu1 p hp
  refine ⟨fl (sw fl 1 (p.V 0 0 3 1) * fb fl p w j0),
    Fexp fl p (fa fl p w k) (fl (sw fl 1 (p.V 0 0 3 1) * fb fl p w j0)),
    fun _ => ⟨hb, hr.idem _, Fexp_fix hr p _ _, hgG, hg0, ?_, ?_⟩⟩
  · rintro ⟨h2, hnex⟩
    rw [hg0 hnex, hfa.1 h2]
    exact F_nog_two hr hu0 hu1 p hp
  · intro hnot
    by_cases hex : ∃ t, t ≤ k ∧ tokAt w t = 3
    · rw [hgG hex]
      exact F_has3 hr hu0 hu1 p hp _ _ hfab ⟨by linarith [hGb.1], by linarith [hGb.2]⟩
    · have h2 : tokAt w k ≠ 2 := fun h => hnot ⟨h, hex⟩
      rw [hg0 hex, hfa.2 h2]
      exact F_nog_zero hr p

theorem net_ok : Statement net := by
  intro u fl hr hu0 hu1 p hp w hw hn i hi1 hi
  have hlen : 1 ≤ w.length := by omega
  have hL : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 := hn
  have hLn : 2 ≤ w.length + 1 := by omega
  choose g F hgF using stage0 hr hu0 hu1 p hp w hw hn hlen
  have hx1 : ∀ k, k ≤ w.length →
      blk0.apply fl p 0 (w.length + 1) (net.init fl p w) k =
        [fa fl p w k, fb fl p w k, fcc fl p w k, g k, F k, 0, 0, 1, fl (k : ℝ),
          fl ((w.length + 1 : ℕ) : ℝ)] := fun k hk => (hgF k hk).1
  have hFa_b := Fa_iv hr hu0 hu1 p hp
  obtain ⟨j1, hj1, hcase⟩ :=
    first_exists (fun m => tokAt w m = 2 ∧ ¬∃ t, t ≤ m ∧ tokAt w t = 3) i
  have hFv : ∀ m, m ≤ w.length →
      ((tokAt w m = 2 ∧ ¬∃ t, t ≤ m ∧ tokAt w t = 3) → F m = Fa fl p) ∧
      (¬(tokAt w m = 2 ∧ ¬∃ t, t ≤ m ∧ tokAt w t = 3) → F m = 0) :=
    fun m hm => ⟨(hgF m hm).2.2.2.2.2.1, (hgF m hm).2.2.2.2.2.2⟩
  have hfF : ∀ m, m ≤ i → F m = 0 ∨ F m = Fa fl p := by
    intro m hm
    by_cases h : (tokAt w m = 2 ∧ ¬∃ t, t ≤ m ∧ tokAt w t = 3)
    · right; exact (hFv m (by omega)).1 h
    · left; exact (hFv m (by omega)).2 h
  have hfirst : (F j1 = Fa fl p ∧ ∀ m, m < j1 → F m = 0) ∨
      (j1 = 0 ∧ ∀ m, m ≤ i → F m = 0) := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨(hFv j1 (by omega)).1 h1, fun m hm => (hFv m (by omega)).2 (h2 m hm)⟩
    · right
      exact ⟨h1, fun m hm => (hFv m (by omega)).2 (h2 m hm)⟩
  have hsc : ∀ m, m ≤ i →
      hd1.score fl (p.A 1 0) (blk0.apply fl p 0 (w.length + 1) (net.init fl p w) i)
        (blk0.apply fl p 0 (w.length + 1) (net.init fl p w) m) =
      fl (fl (sw fl (-1) (p.A 1 0 7 8) * fl (m : ℝ)) +
        fl (fl ((w.length + 1 : ℕ) : ℝ) * fl (sw fl 4 (p.A 1 0 9 4) * F m))) := by
    intro m hm
    rw [hx1 i hi, hx1 m (by omega), score1_eq hr]
  have hsa := sw4_iv hr hu0 hu1 (hp.A 1 0 9 4)
  have hsb := swn1_iv hr hu0 hu1 (hp.A 1 0 7 8)
  have hsel1 : hd1.sel fl (p.A 1 0) (w.length + 1) (blk0.apply fl p 0 (w.length + 1) (net.init fl p w)) i = [j1] := by
    apply Head.sel_unique
    · rw [show hd1.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal]; exact hj1
    · intro m hm hne
      rw [show hd1.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal] at hm
      exact sel_core hr hu0 hu1 (w.length + 1) i hL (by omega) hLn
        (sw fl 4 (p.A 1 0 9 4)) (sw fl (-1) (p.A 1 0 7 8)) (Fa fl p)
        ⟨by linarith [hsa.1], by linarith [hsa.2]⟩ ⟨by linarith [hsb.1], by linarith [hsb.2]⟩
        ⟨by linarith [hFa_b.1], by linarith [hFa_b.2]⟩ F hfF j1 hj1 hfirst
        (fun m => hd1.score fl (p.A 1 0) (blk0.apply fl p 0 (w.length + 1) (net.init fl p w) i)
          (blk0.apply fl p 0 (w.length + 1) (net.init fl p w) m)) hsc m hm hne
  have hb1 := blk1_eq hr p (w.length + 1) i j1
    (blk0.apply fl p 0 (w.length + 1) (net.init fl p w)) (fa fl p w) (fb fl p w) (fcc fl p w)
    g F (fun j => fl (j : ℝ)) (fl ((w.length + 1 : ℕ) : ℝ)) (fa fl p w j1) (fb fl p w j1)
    (fcc fl p w j1) (g j1) (F j1) (fl (j1 : ℝ)) (fl ((w.length + 1 : ℕ) : ℝ))
    (hx1 i hi) (hx1 j1 (by omega)) (fa_fix hr p w i) (fb_fix hr p w i) (fcc_fix hr p w i)
    (hgF i hi).2.1 (hgF i hi).2.2.1 (hr.idem _) (hr.idem _) hsel1
  have hout := out_eq hr p w i _ _ _ _ _ _ _ _ _ (by rw [run_eq fl p w]; exact hb1)
  generalize hres : fl (sw fl 1 (p.V 1 0 5 4) * F j1) = res at hout
  have hsV := sw1_iv hr hu0 hu1 (hp.V 1 0 5 4)
  have hs := sw1_iv hr hu0 hu1 (hp.oW 6)
  have htokr := tok_real w hw i hi1 hi
  have hgd := tok_getD w i hi1
  have hc0 : tokAt w i = 2 → fcc fl p w i = 0 := by
    intro h; simp [fcc, h]
  have hc1 : tokAt w i ≠ 2 → 994 / 1000 ≤ fcc fl p w i ∧ fcc fl p w i ≤ 1006 / 1000 := by
    intro h
    rcases (by omega : tokAt w i = 1 ∨ tokAt w i = 3 ∨ tokAt w i = 4) with h' | h' | h'
    · have e : fcc fl p w i = sw fl 1 (p.E 1 2) := by simp [fcc, h']
      have := sw1_iv hr hu0 hu1 (hp.E 1 2)
      rw [e]; constructor <;> linarith [this.1, this.2]
    · have e : fcc fl p w i = sw fl 1 (p.E 3 2) := by simp [fcc, h']
      have := sw1_iv hr hu0 hu1 (hp.E 3 2)
      rw [e]; constructor <;> linarith [this.1, this.2]
    · have e : fcc fl p w i = sw fl 1 (p.E 4 2) := by simp [fcc, h']
      have := sw1_iv hr hu0 hu1 (hp.E 4 2)
      rw [e]; constructor <;> linarith [this.1, this.2]
  have hcb2 : tokAt w i = 2 → cbit (tokAt w i) = 0 := by
    intro h; simp [cbit, h]
  have hcb1 : tokAt w i ≠ 2 → cbit (tokAt w i) = 1 := by
    intro h
    rcases (by omega : tokAt w i = 1 ∨ tokAt w i = 3 ∨ tokAt w i = 4) with h' | h' | h' <;>
      simp [cbit, h']
  rw [hout]
  rcases fc_char w i hi with ⟨hfc, hex⟩ | ⟨hfc, hnex⟩
  · -- the first marked token is a 2
    have hPj : (tokAt w j1 = 2 ∧ ¬∃ t, t ≤ j1 ∧ tokAt w t = 3) := by
      rcases hcase with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · exfalso
        obtain ⟨m, hm, hm2, hm3⟩ := hex
        exact h2 m hm ⟨hm2, fun ⟨t, ht, h3⟩ => hm3 t ht h3⟩
    have hFj : F j1 = Fa fl p := (hFv j1 (by omega)).1 hPj
    have hr1 : 97 / 100 ≤ res ∧ res ≤ 103 / 100 := by
      have t := flprod hr hu0 hu1 (x := sw fl 1 (p.V 1 0 5 4)) (y := F j1)
        (a := 188 / 189) (b := 190 / 189) (c := 49 / 50) (d := 51 / 50)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) hsV
        (by rw [hFj]; exact hFa_b)
      rw [← hres]
      constructor <;> linarith [t.1, t.2]
    by_cases h2 : tokAt w i = 2
    · have htg : target w i = 1 := by
        unfold target; rw [hgd, hcb2 h2, if_pos hfc] <;> norm_num
      rw [htg, Nat.cast_one, hc0 h2]
      exact fin_one hr hu0 hu1 _ _ hs (outv_one_r hr hu0 hu1 p hp res hr1)
    · have htg : target w i = 0 := by
        unfold target; rw [hgd, hcb1 h2, if_pos hfc] <;> norm_num
      rw [htg, Nat.cast_zero]
      exact fin_zero hr hu0 hu1 _ _ hs (outv_two hr hu0 hu1 p hp _ res (hc1 h2) hr1)
  · -- the first marked token is not a 2
    have hF0 : F j1 = 0 := by
      rcases hcase with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exfalso
        exact hnex ⟨j1, hj1, h1.1, fun t ht h3 => h1.2 ⟨t, ht, h3⟩⟩
      · exact (hFv j1 (by omega)).2 (h2 j1 hj1)
    have hres0 : res = 0 := by
      rw [← hres, hF0]; simp [hr.zero]
    subst hres0
    by_cases h2 : tokAt w i = 2
    · have htg : target w i = 0 := by
        unfold target; rw [hgd, hcb2 h2, if_neg hfc] <;> norm_num
      rw [htg, Nat.cast_zero, hc0 h2, outv_zero hr hu0 hu1 p hp]
      exact fin_exact hr _
    · have htg : target w i = 1 := by
        unfold target; rw [hgd, hcb1 h2, if_neg hfc] <;> norm_num
      rw [htg, Nat.cast_one]
      exact fin_one hr hu0 hu1 _ _ hs (outv_one_c hr hu0 hu1 p hp _ (hc1 h2))

end Lane4.Case
