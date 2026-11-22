set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option linter.deprecated false
set_option maxHeartbeats 4000000

namespace Lane4.Case
open Lane4.RSeq (Vec pdot radd rsum)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.LNC Lane4.R7K2
open Lane4.LNKD

/-! ### the pieces of `lnOne` -/

def lo0 (R : FF) (dr : ℤ) (ns : ℕ) (c : FF) : FF :=
  ⟨c.c * R.c / SC, List.zipWith (fun x y => (R.c * x + c.c * y) / SC) c.t R.t,
   cdiv (R.c * c.r + iabs c.c * R.r + c.dev * dr) SC + ((ns : ℤ) + 1)⟩

def lo1 (R : FF) (dr : ℤ) (ns : ℕ) (c : FF) : FF := (lo0 R dr ns c).wide (chg (lo0 R dr ns c).mag)

def lo2b (dI : ℤ) (ns : ℕ) (o : FF) (g : ℤ) : FF :=
  ⟨g * o.c / SC, o.t.map (fun x => g * x / SC),
   cdiv (iabs g * o.r) SC + ((ns : ℤ) + 1) + cdiv (dI * o.dev) SC⟩

def lo2 (dI : ℤ) (ns : ℕ) (slot : Option ℕ) (o : FF) (g : ℤ) : FF :=
  (lo2b dI ns o g).bump slot (cdiv (dI * (iabs o.c + SC)) SC)

def lo4 (dI : ℤ) (ns : ℕ) (slot : Option ℕ) (o : FF) (g b : ℤ) : FF :=
  let o2 := lo2 dI ns slot o g
  let o3 := o2.wide (chg o2.mag + chg (iabs b + dI))
  ⟨o3.c + b, o3.t, o3.r⟩

theorem lnOne_eq (dI : ℤ) (rinv : FF) (dr : ℤ) (ns : ℕ) (slot0 slot : Option ℕ) (c : FF) (g b : ℤ) :
    lnOne dI rinv dr ns slot0 slot c g b =
      ((lo1 rinv dr ns c).small && freeOpt slot0 (lo2b dI ns (lo1 rinv dr ns c) g) &&
         ((lo4 dI ns slot (lo1 rinv dr ns c) g b).wide (chg (lo4 dI ns slot (lo1 rinv dr ns c) g b).mag)).small,
       (lo4 dI ns slot (lo1 rinv dr ns c) g b).wide (chg (lo4 dI ns slot (lo1 rinv dr ns c) g b).mag)) := rfl

/-! ### generic widening -/

theorem gw (e : ℕ → ℝ) (z f : ℝ) (s : FF) (m : ℤ) (hs : InFF e z s)
    (hf : |f - z| * 2 ^ 56 ≤ (m : ℝ)) : InFF e f (s.wide m) := by
  unfold InFF at hs ⊢
  simp only [FF.wide]
  push_cast
  have e1 : f * 2 ^ 56 - ((s.c : ℝ) + linValI s.t e 0)
      = (f - z) * 2 ^ 56 + (z * 2 ^ 56 - ((s.c : ℝ) + linValI s.t e 0)) := by ring
  rw [e1]
  have h2 : |(f - z) * 2 ^ 56| = |f - z| * 2 ^ 56 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 56)]
  have h4 := abs_add_le ((f - z) * 2 ^ 56) (z * 2 ^ 56 - ((s.c : ℝ) + linValI s.t e 0))
  linarith

/-! ### the product -/

theorem zip_floor (e : ℕ → ℝ) (he : Sym e) (a b : ℤ) : ∀ (t1 t2 : List ℤ) (k : ℕ),
    t1.length = t2.length →
    |((a : ℝ) * linValI t1 e k + (b : ℝ) * linValI t2 e k) / 2 ^ 56
      - linValI (List.zipWith (fun x y => (a * x + b * y) / SC) t1 t2) e k| ≤ (t1.length : ℝ) := by
  intro t1
  induction t1 with
  | nil =>
    intro t2 k h
    cases t2 with
    | nil => simp [linValI]
    | cons _ _ => simp at h
  | cons x l ih =>
    intro t2 k h
    cases t2 with
    | nil => simp at h
    | cons y m =>
      have hl : l.length = m.length := by simpa using h
      have hf := floor_facts (a * x + b * y) SC (by unfold SC; norm_num)
      have hSC : ((SC : ℤ) : ℝ) = 2 ^ 56 := by unfold SC; norm_num
      rw [hSC] at hf
      push_cast at hf
      have h1 : |((a : ℝ) * x + b * y) / 2 ^ 56 - (((a * x + b * y) / SC : ℤ) : ℝ)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hf.1, hf.2]
      have h2 : |(((a : ℝ) * x + b * y) / 2 ^ 56 - (((a * x + b * y) / SC : ℤ) : ℝ)) * e k| ≤ 1 := by
        rw [abs_mul]
        calc _ ≤ 1 * 1 := mul_le_mul h1 (he k) (abs_nonneg _) zero_le_one
          _ = 1 := by norm_num
      have h3 := ih m (k + 1) hl
      simp only [List.zipWith_cons_cons, linValI, List.length_cons]
      have e1 : ((a : ℝ) * ((x : ℝ) * e k + linValI l e (k + 1))
            + (b : ℝ) * ((y : ℝ) * e k + linValI m e (k + 1))) / 2 ^ 56
          - ((((a * x + b * y) / SC : ℤ) : ℝ) * e k
              + linValI (List.zipWith (fun x y => (a * x + b * y) / SC) l m) e (k + 1))
        = (((a : ℝ) * x + b * y) / 2 ^ 56 - (((a * x + b * y) / SC : ℤ) : ℝ)) * e k
          + (((a : ℝ) * linValI l e (k + 1) + (b : ℝ) * linValI m e (k + 1)) / 2 ^ 56
              - linValI (List.zipWith (fun x y => (a * x + b * y) / SC) l m) e (k + 1)) := by ring
      rw [e1]
      have h4 := abs_add_le
        ((((a : ℝ) * x + b * y) / 2 ^ 56 - (((a * x + b * y) / SC : ℤ) : ℝ)) * e k)
        (((a : ℝ) * linValI l e (k + 1) + (b : ℝ) * linValI m e (k + 1)) / 2 ^ 56
              - linValI (List.zipWith (fun x y => (a * x + b * y) / SC) l m) e (k + 1))
      push_cast
      linarith

theorem prod_sound (e : ℕ → ℝ) (he : Sym e) (c ri : ℝ) (C R : FF) (ns : ℕ) (dr : ℤ)
    (hdr : dr = R.dev) (hc : InFF e c C) (hr : InFF e ri R)
    (hCl : C.t.length = ns) (hRl : R.t.length = ns) (hR0 : 0 ≤ R.c) :
    InFF e (c * ri) (lo0 R dr ns C) := by
  subst hdr
  have hSC : ((SC : ℤ) : ℝ) = 2 ^ 56 := by unfold SC; norm_num
  have hP := inff_dev e c C he hc
  have hQ := inff_dev e ri R he hr
  have hzf := zip_floor e he R.c C.c C.t R.t 0 (by rw [hCl, hRl])
  have hF := floor_facts (C.c * R.c) SC (by unfold SC; norm_num)
  rw [hSC] at hF
  push_cast at hF
  have hN := cdiv_facts (R.c * C.r + iabs C.c * R.r + C.dev * R.dev) SC (by unfold SC; norm_num)
  rw [hSC] at hN
  push_cast at hN
  rw [iabs_cast] at hN
  have hR0R : (0 : ℝ) ≤ (R.c : ℝ) := by exact_mod_cast hR0
  have hSpos : (0 : ℝ) < 2 ^ 56 := by norm_num
  have hc' := hc
  have hr' := hr
  unfold InFF at hc' hr'
  have hCr : (0 : ℝ) ≤ (C.r : ℝ) := le_trans (abs_nonneg _) hc'
  have hRr : (0 : ℝ) ≤ (R.r : ℝ) := le_trans (abs_nonneg _) hr'
  have t1 : |(R.c : ℝ) * (c * 2 ^ 56 - ((C.c : ℝ) + linValI C.t e 0))| ≤ (R.c : ℝ) * (C.r : ℝ) := by
    rw [abs_mul, abs_of_nonneg hR0R]
    exact mul_le_mul_of_nonneg_left hc' hR0R
  have t2 : |(C.c : ℝ) * (ri * 2 ^ 56 - ((R.c : ℝ) + linValI R.t e 0))| ≤ |(C.c : ℝ)| * (R.r : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hr' (abs_nonneg _)
  have t3 : |(c * 2 ^ 56 - (C.c : ℝ)) * (ri * 2 ^ 56 - (R.c : ℝ))| ≤ (C.dev : ℝ) * (R.dev : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul hP hQ (abs_nonneg _) (by exact_mod_cast (show 0 ≤ C.dev by
      unfold FF.dev; have := linI_nonneg C.t; have h0 : 0 ≤ C.r := by exact_mod_cast hCr
      omega))
  have tT : |(R.c : ℝ) * (c * 2 ^ 56 - ((C.c : ℝ) + linValI C.t e 0))
      + (C.c : ℝ) * (ri * 2 ^ 56 - ((R.c : ℝ) + linValI R.t e 0))
      + (c * 2 ^ 56 - (C.c : ℝ)) * (ri * 2 ^ 56 - (R.c : ℝ))|
      ≤ (R.c : ℝ) * (C.r : ℝ) + |(C.c : ℝ)| * (R.r : ℝ) + (C.dev : ℝ) * (R.dev : ℝ) := by
    have a1 := abs_add_le ((R.c : ℝ) * (c * 2 ^ 56 - ((C.c : ℝ) + linValI C.t e 0)))
      ((C.c : ℝ) * (ri * 2 ^ 56 - ((R.c : ℝ) + linValI R.t e 0)))
    have a2 := abs_add_le ((R.c : ℝ) * (c * 2 ^ 56 - ((C.c : ℝ) + linValI C.t e 0))
      + (C.c : ℝ) * (ri * 2 ^ 56 - ((R.c : ℝ) + linValI R.t e 0)))
      ((c * 2 ^ 56 - (C.c : ℝ)) * (ri * 2 ^ 56 - (R.c : ℝ)))
    linarith
  have tT2 : |((R.c : ℝ) * (c * 2 ^ 56 - ((C.c : ℝ) + linValI C.t e 0))
      + (C.c : ℝ) * (ri * 2 ^ 56 - ((R.c : ℝ) + linValI R.t e 0))
      + (c * 2 ^ 56 - (C.c : ℝ)) * (ri * 2 ^ 56 - (R.c : ℝ))) / 2 ^ 56|
      ≤ ((R.c : ℝ) * (C.r : ℝ) + |(C.c : ℝ)| * (R.r : ℝ) + (C.dev : ℝ) * (R.dev : ℝ)) / 2 ^ 56 := by
    rw [abs_div, abs_of_pos hSpos]
    gcongr
  have key : c * ri * 2 ^ 56 - ((((C.c * R.c / SC : ℤ)) : ℝ)
        + linValI (List.zipWith (fun x y => (R.c * x + C.c * y) / SC) C.t R.t) e 0)
      = ((C.c : ℝ) * R.c / 2 ^ 56 - (((C.c * R.c / SC : ℤ)) : ℝ))
        + (((R.c : ℝ) * linValI C.t e 0 + (C.c : ℝ) * linValI R.t e 0) / 2 ^ 56
            - linValI (List.zipWith (fun x y => (R.c * x + C.c * y) / SC) C.t R.t) e 0)
        + ((R.c : ℝ) * (c * 2 ^ 56 - ((C.c : ℝ) + linValI C.t e 0))
      + (C.c : ℝ) * (ri * 2 ^ 56 - ((R.c : ℝ) + linValI R.t e 0))
      + (c * 2 ^ 56 - (C.c : ℝ)) * (ri * 2 ^ 56 - (R.c : ℝ))) / 2 ^ 56 := by
    ring
  have hzf' : |((R.c : ℝ) * linValI C.t e 0 + (C.c : ℝ) * linValI R.t e 0) / 2 ^ 56
      - linValI (List.zipWith (fun x y => (R.c * x + C.c * y) / SC) C.t R.t) e 0| ≤ (ns : ℝ) := by
    rw [hCl] at hzf; exact hzf
  have d1 : |(C.c : ℝ) * R.c / 2 ^ 56 - (((C.c * R.c / SC : ℤ)) : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hF.1, hF.2]
  unfold InFF
  simp only [lo0]
  push_cast
  rw [key]
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add (le_trans (abs_add_le _ _) (add_le_add d1 hzf')) tT2) ?_
  linarith [hN.1]

/-! ### the gain -/

theorem gain_sound (e : ℕ → ℝ) (he : Sym e) (o' gq dg δ : ℝ) (O : FF) (gI dI : ℤ) (ns : ℕ)
    (hg : (gI : ℝ) = gq * 2 ^ 56) (hd : (dI : ℝ) = δ * 2 ^ 56) (hδ : 0 ≤ δ) (hdg : |dg| ≤ δ)
    (hOl : O.t.length = ns) (ho : InFF e o' O) :
    InFF e (o' * (gq + dg) - dg * (O.c : ℝ) / 2 ^ 56) (lo2b dI ns O gI) := by
  have hSC : ((SC : ℤ) : ℝ) = 2 ^ 56 := by unfold SC; norm_num
  have hSpos : (0 : ℝ) < 2 ^ 56 := by norm_num
  obtain rfl : gq = (gI : ℝ) / 2 ^ 56 := by rw [hg]; field_simp
  obtain rfl : δ = (dI : ℝ) / 2 ^ 56 := by rw [hd]; field_simp
  have hOd := inff_dev e o' O he ho
  have hoo := ho
  unfold InFF at hoo
  have hmf := map_floor_err e he gI SC (by unfold SC; norm_num) O.t 0
  rw [hSC, hOl] at hmf
  have hF := floor_facts (gI * O.c) SC (by unfold SC; norm_num)
  rw [hSC] at hF
  push_cast at hF
  have hc1 := cdiv_facts (iabs gI * O.r) SC (by unfold SC; norm_num)
  rw [hSC] at hc1
  push_cast at hc1
  rw [iabs_cast] at hc1
  have hc2 := cdiv_facts (dI * O.dev) SC (by unfold SC; norm_num)
  rw [hSC] at hc2
  push_cast at hc2
  have d1 : |(gI : ℝ) * O.c / 2 ^ 56 - (((gI * O.c / SC : ℤ)) : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hF.1, hF.2]
  have d3 : |(gI : ℝ) / 2 ^ 56 * (o' * 2 ^ 56 - ((O.c : ℝ) + linValI O.t e 0))|
      ≤ (((cdiv (iabs gI * O.r) SC : ℤ)) : ℝ) := by
    have h : |(gI : ℝ) / 2 ^ 56 * (o' * 2 ^ 56 - ((O.c : ℝ) + linValI O.t e 0))|
        ≤ |(gI : ℝ)| * (O.r : ℝ) / 2 ^ 56 := by
      rw [abs_mul, abs_div, abs_of_pos hSpos]
      calc |(gI : ℝ)| / 2 ^ 56 * |o' * 2 ^ 56 - ((O.c : ℝ) + linValI O.t e 0)|
          ≤ |(gI : ℝ)| / 2 ^ 56 * (O.r : ℝ) := mul_le_mul_of_nonneg_left hoo (by positivity)
        _ = |(gI : ℝ)| * (O.r : ℝ) / 2 ^ 56 := by ring
    linarith [hc1.1]
  have hdI : (0 : ℝ) ≤ (dI : ℝ) / 2 ^ 56 := by
    have := le_trans (abs_nonneg dg) hdg; exact this
  have d4 : |dg * (o' * 2 ^ 56 - (O.c : ℝ))| ≤ (((cdiv (dI * O.dev) SC : ℤ)) : ℝ) := by
    have h : |dg * (o' * 2 ^ 56 - (O.c : ℝ))| ≤ (dI : ℝ) * (O.dev : ℝ) / 2 ^ 56 := by
      rw [abs_mul]
      calc |dg| * |o' * 2 ^ 56 - (O.c : ℝ)| ≤ (dI : ℝ) / 2 ^ 56 * (O.dev : ℝ) :=
            mul_le_mul hdg hOd (abs_nonneg _) hdI
        _ = (dI : ℝ) * (O.dev : ℝ) / 2 ^ 56 := by ring
    linarith [hc2.1]
  have key : (o' * ((gI : ℝ) / 2 ^ 56 + dg) - dg * (O.c : ℝ) / 2 ^ 56) * 2 ^ 56
        - ((((gI * O.c / SC : ℤ)) : ℝ) + linValI (O.t.map (fun x => gI * x / SC)) e 0)
      = ((gI : ℝ) * O.c / 2 ^ 56 - (((gI * O.c / SC : ℤ)) : ℝ))
        + ((gI : ℝ) / 2 ^ 56 * linValI O.t e 0 - linValI (O.t.map (fun x => gI * x / SC)) e 0)
        + (gI : ℝ) / 2 ^ 56 * (o' * 2 ^ 56 - ((O.c : ℝ) + linValI O.t e 0))
        + dg * (o' * 2 ^ 56 - (O.c : ℝ)) := by ring
  unfold InFF
  simp only [lo2b]
  push_cast
  rw [key]
  rw [abs_le] at d1 d3 d4 hmf ⊢
  constructor <;> linarith [d1.1, d1.2, d3.1, d3.2, d4.1, d4.2, hmf.1, hmf.2]

/-! ### the roundings of one coordinate -/

theorem wide_mag (a : FF) (x : ℤ) : (a.wide x).mag = a.mag + x := by
  unfold FF.mag FF.dev FF.wide
  simp only
  omega

theorem small_mag (a : FF) (h : a.small = true) : a.mag ≤ 15 * SC := by
  unfold FF.small at h
  exact of_decide_eq_true h

theorem q15 (g : ℚ) (h : qabs g ≤ 15) : |(g : ℝ)| ≤ 15 := by
  have h1 := zqabs_cast g
  have h2 : ((qabs g : ℚ) : ℝ) ≤ 15 := by exact_mod_cast h
  rw [h1] at h2; exact h2

theorem round_sound {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (ê : ℕ → ℝ) (hê : Sym ê)
    (o' dg db δ : ℝ) (g b : ℚ) (O : FF) (gI bI dI : ℤ) (ns : ℕ) (slot : Option ℕ)
    (hgb : qabs g ≤ 15) (hbb : qabs b ≤ 15) (hgI : (gI : ℝ) = (g : ℝ) * 2 ^ 56)
    (hbI : (bI : ℝ) = (b : ℝ) * 2 ^ 56) (hdI : (dI : ℝ) = δ * 2 ^ 56) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2) (hdg : |dg| ≤ δ) (hdb : |db| ≤ δ)
    (ho' : |o'| ≤ 15) (hmag : |o'| * 2 ^ 56 ≤ (O.mag : ℝ))
    (hlow : (|(g : ℝ)| + δ) * (O.mag : ℝ) ≤ ((lo2 dI ns slot O gI).mag : ℝ))
    (hV3 : InFF ê (o' * ((g : ℝ) + dg) + db) (lo2 dI ns slot O gI))
    (hsm : ((lo4 dI ns slot O gI bI).wide (chg (lo4 dI ns slot O gI bI).mag)).small = true) :
    InFF ê (fl (fl (o' * asw fl g dg) + asw fl b db))
      ((lo4 dI ns slot O gI bI).wide (chg (lo4 dI ns slot O gI bI).mag)) := by
  have hu0 := hC.u0
  have hu1 := hC.u1
  have hη0 := hC.h0
  have hη1 := hC.h1
  have hM1 := hC.M1
  have hSC : ((SC : ℤ) : ℝ) = 2 ^ 56 := by unfold SC; norm_num
  have hSpos : (0 : ℝ) < 2 ^ 56 := by norm_num
  have hu1' : u ≤ 1 := le_trans hu1 (by norm_num)
  have hη1' : η ≤ 1 := le_trans hη1 (by norm_num)
  have h16 : (16 : ℝ) ≤ 2 ^ 40 := by norm_num
  have hg15 := q15 g hgb
  have hb15 := q15 b hbb
  have hG0 : 0 ≤ |(g : ℝ)| + δ := by positivity
  have hGb : |(g : ℝ) + dg| ≤ |(g : ℝ)| + δ := le_trans (abs_add_le _ _) (by linarith)
  have hBb : |(b : ℝ) + db| ≤ |(b : ℝ)| + δ := le_trans (abs_add_le _ _) (by linarith)
  have hMg : |(g : ℝ) + dg| ≤ M := by linarith
  have hMb : |(b : ℝ) + db| ≤ M := by linarith
  have hρg : |asw fl g dg - ((g : ℝ) + dg)| ≤ u * |(g : ℝ) + dg| + η := by
    unfold asw; exact hC.rnd.err _ hMg
  have hρb : |asw fl b db - ((b : ℝ) + db)| ≤ u * |(b : ℝ) + db| + η := by
    unfold asw; exact hC.rnd.err _ hMb
  have hρg' : |asw fl g dg - ((g : ℝ) + dg)| ≤ u * (|(g : ℝ)| + δ) + η := by
    have := mul_le_mul_of_nonneg_left hGb hu0
    linarith
  have hĝ : |asw fl g dg| ≤ (|(g : ℝ)| + δ) + (u * (|(g : ℝ)| + δ) + η) := by
    have e1 : asw fl g dg = ((g : ℝ) + dg) + (asw fl g dg - ((g : ℝ) + dg)) := by ring
    calc |asw fl g dg| = |((g : ℝ) + dg) + (asw fl g dg - ((g : ℝ) + dg))| := by rw [← e1]
      _ ≤ |(g : ℝ) + dg| + |asw fl g dg - ((g : ℝ) + dg)| := abs_add_le _ _
      _ ≤ _ := by linarith
  have huG : u * (|(g : ℝ)| + δ) ≤ |(g : ℝ)| + δ := mul_le_of_le_one_left hG0 hu1'
  have hz1b : |o' * asw fl g dg| ≤ |o'| * ((|(g : ℝ)| + δ) + (u * (|(g : ℝ)| + δ) + η)) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hĝ (abs_nonneg _)
  have hz1b' : |o'| * ((|(g : ℝ)| + δ) + (u * (|(g : ℝ)| + δ) + η)) ≤ 15 * 40 := by
    have h0 : (0 : ℝ) ≤ (|(g : ℝ)| + δ) + (u * (|(g : ℝ)| + δ) + η) := by positivity
    calc _ ≤ 15 * ((|(g : ℝ)| + δ) + (u * (|(g : ℝ)| + δ) + η)) :=
          mul_le_mul_of_nonneg_right ho' h0
      _ ≤ 15 * 40 := by linarith
  have hz1M : |o' * asw fl g dg| ≤ M := by linarith
  have hph : |fl (o' * asw fl g dg) - o' * asw fl g dg| ≤ u * |o' * asw fl g dg| + η :=
    hC.rnd.err _ hz1M
  -- magnitude facts
  have hO0 : (0 : ℝ) ≤ (O.mag : ℝ) := le_trans (by positivity) hmag
  have hm2 : (0 : ℝ) ≤ ((lo2 dI ns slot O gI).mag : ℝ) := le_trans (by positivity) hlow
  have hm2i : 0 ≤ (lo2 dI ns slot O gI).mag := by exact_mod_cast hm2
  obtain ⟨hchg1, hchg2⟩ := chg_facts _ hm2i
  -- error of the product stage
  have hX1 : |o' * (asw fl g dg - ((g : ℝ) + dg))| + |fl (o' * asw fl g dg) - o' * asw fl g dg|
      ≤ |o'| * (u * (|(g : ℝ)| + δ) + η)
        + (u * (|o'| * ((|(g : ℝ)| + δ) + (u * (|(g : ℝ)| + δ) + η))) + η) := by
    have a1 : |o' * (asw fl g dg - ((g : ℝ) + dg))| ≤ |o'| * (u * (|(g : ℝ)| + δ) + η) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hρg' (abs_nonneg _)
    have a2 : u * |o' * asw fl g dg|
        ≤ u * (|o'| * ((|(g : ℝ)| + δ) + (u * (|(g : ℝ)| + δ) + η))) :=
      mul_le_mul_of_nonneg_left hz1b hu0
    linarith
  have hX2 : (2 : ℝ) ^ 56 * (|o'| * (u * (|(g : ℝ)| + δ) + η)
        + (u * (|o'| * ((|(g : ℝ)| + δ) + (u * (|(g : ℝ)| + δ) + η))) + η))
      = (u * (2 + u)) * (|o'| * (|(g : ℝ)| + δ) * 2 ^ 56)
        + 2 ^ 56 * η * (|o'| * (1 + u) + 1) := by ring
  have hT : |o'| * (|(g : ℝ)| + δ) * 2 ^ 56 ≤ ((lo2 dI ns slot O gI).mag : ℝ) := by
    have : |o'| * (|(g : ℝ)| + δ) * 2 ^ 56 = (|(g : ℝ)| + δ) * (|o'| * 2 ^ 56) := by ring
    rw [this]
    exact le_trans (mul_le_mul_of_nonneg_left hmag hG0) hlow
  have hT0 : 0 ≤ |o'| * (|(g : ℝ)| + δ) * 2 ^ 56 := by positivity
  have hu23 : u * (2 + u) ≤ 3 / 2 ^ 24 := by nlinarith
  have hηS : 2 ^ 56 * η ≤ 1 / 2 ^ 93 := by
    calc (2 : ℝ) ^ 56 * η ≤ 2 ^ 56 * (1 / 2 ^ 149) := mul_le_mul_of_nonneg_left hη1 (by norm_num)
      _ = 1 / 2 ^ 93 := by norm_num
  have hηS0 : 0 ≤ 2 ^ 56 * η := mul_nonneg (by norm_num) hη0
  have hAu : |o'| * (1 + u) + 1 ≤ 31 := by nlinarith [abs_nonneg o']
  have hAu0 : 0 ≤ |o'| * (1 + u) + 1 := by positivity
  have hprod : (2 : ℝ) ^ 56 * (|o'| * (u * (|(g : ℝ)| + δ) + η)
        + (u * (|o'| * ((|(g : ℝ)| + δ) + (u * (|(g : ℝ)| + δ) + η))) + η))
      ≤ ((lo2 dI ns slot O gI).mag : ℝ) / 2 ^ 22 * (3 / 4) + 31 / 2 ^ 93 := by
    rw [hX2]
    have b1 : (u * (2 + u)) * (|o'| * (|(g : ℝ)| + δ) * 2 ^ 56)
        ≤ (3 / 2 ^ 24) * ((lo2 dI ns slot O gI).mag : ℝ) := by
      calc _ ≤ (3 / 2 ^ 24) * (|o'| * (|(g : ℝ)| + δ) * 2 ^ 56) :=
            mul_le_mul_of_nonneg_right hu23 hT0
        _ ≤ _ := mul_le_mul_of_nonneg_left hT (by norm_num)
    have b2 : 2 ^ 56 * η * (|o'| * (1 + u) + 1) ≤ 1 / 2 ^ 93 * 31 := by
      calc _ ≤ (1 / 2 ^ 93) * (|o'| * (1 + u) + 1) := mul_le_mul_of_nonneg_right hηS hAu0
        _ ≤ (1 / 2 ^ 93) * 31 := mul_le_mul_of_nonneg_left hAu (by norm_num)
    have b3 : (3 / 2 ^ 24) * ((lo2 dI ns slot O gI).mag : ℝ)
        = ((lo2 dI ns slot O gI).mag : ℝ) / 2 ^ 22 * (3 / 4) := by ring
    linarith
  -- the gain/bias stage in the form
  have hρb2 : 2 ^ 56 * |asw fl b db - ((b : ℝ) + db)| ≤ ((chg (iabs bI + dI) : ℤ) : ℝ) := by
    have hm : |(b : ℝ) + db| * 2 ^ 56 ≤ (((iabs bI + dI : ℤ)) : ℝ) := by
      push_cast
      rw [iabs_cast, hbI, hdI]
      have h1 : |(b : ℝ) * 2 ^ 56| = |(b : ℝ)| * 2 ^ 56 := by
        rw [abs_mul, abs_of_pos hSpos]
      rw [h1]
      nlinarith
    have h1 := round_chg hu0 hu1 hη0 hη1 ((b : ℝ) + db) _ hm
    have h2 : 2 ^ 56 * |asw fl b db - ((b : ℝ) + db)|
        ≤ (u * |(b : ℝ) + db| + η) * 2 ^ 56 := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right hρb (by norm_num)
    linarith
  -- the value before the last rounding
  set E : ℤ := chg (lo2 dI ns slot O gI).mag + chg (iabs bI + dI) with hE
  have hshift : InFF ê (o' * ((g : ℝ) + dg) + db + (b : ℝ))
      ⟨(lo2 dI ns slot O gI).c + bI, (lo2 dI ns slot O gI).t, (lo2 dI ns slot O gI).r⟩ := by
    have h := hV3
    unfold InFF at h ⊢
    show |(o' * ((g : ℝ) + dg) + db + (b : ℝ)) * 2 ^ 56
      - ((((lo2 dI ns slot O gI).c + bI : ℤ) : ℝ) + linValI (lo2 dI ns slot O gI).t ê 0)|
        ≤ (((lo2 dI ns slot O gI).r : ℤ) : ℝ)
    have e1 : (o' * ((g : ℝ) + dg) + db + (b : ℝ)) * 2 ^ 56
      - ((((lo2 dI ns slot O gI).c + bI : ℤ) : ℝ) + linValI (lo2 dI ns slot O gI).t ê 0)
      = (o' * ((g : ℝ) + dg) + db) * 2 ^ 56
        - (((lo2 dI ns slot O gI).c : ℝ) + linValI (lo2 dI ns slot O gI).t ê 0) := by
      push_cast; rw [hbI]; ring
    rw [e1]; exact h
  have hz2 : InFF ê (fl (o' * asw fl g dg) + asw fl b db)
      ((⟨(lo2 dI ns slot O gI).c + bI, (lo2 dI ns slot O gI).t, (lo2 dI ns slot O gI).r⟩ : FF).wide E) := by
    apply gw ê (o' * ((g : ℝ) + dg) + db + (b : ℝ)) _ _ E hshift
    have e2 : fl (o' * asw fl g dg) + asw fl b db - (o' * ((g : ℝ) + dg) + db + (b : ℝ))
        = (o' * (asw fl g dg - ((g : ℝ) + dg))
            + (fl (o' * asw fl g dg) - o' * asw fl g dg))
          + (asw fl b db - ((b : ℝ) + db)) := by ring
    rw [e2]
    have f1 := abs_add_le (o' * (asw fl g dg - ((g : ℝ) + dg))
            + (fl (o' * asw fl g dg) - o' * asw fl g dg)) (asw fl b db - ((b : ℝ) + db))
    have f2 := abs_add_le (o' * (asw fl g dg - ((g : ℝ) + dg)))
            (fl (o' * asw fl g dg) - o' * asw fl g dg)
    rw [hE]
    push_cast
    nlinarith [hX1, hprod, hρb2, hchg1, hchg2, f1, f2]
  have hlo4 : lo4 dI ns slot O gI bI
      = (⟨(lo2 dI ns slot O gI).c + bI, (lo2 dI ns slot O gI).t, (lo2 dI ns slot O gI).r⟩ : FF).wide E := rfl
  rw [← hlo4] at hz2
  have hb4 := box_sound ê _ _ hê hz2
  have hsm' := small_mag _ hsm
  rw [wide_mag] at hsm'
  have hz2M : |fl (o' * asw fl g dg) + asw fl b db| ≤ M := by
    have h1 : (|fl (o' * asw fl g dg) + asw fl b db|) * 2 ^ 56 ≤ (15 : ℝ) * 2 ^ 56 := by
      have h2 : ((lo4 dI ns slot O gI bI).mag : ℝ) ≤ 15 * 2 ^ 56 := by
        have h3 : (lo4 dI ns slot O gI bI).mag ≤ 15 * SC := by
          have := chg_facts (lo4 dI ns slot O gI bI).mag
          have hm4 : (0 : ℝ) ≤ ((lo4 dI ns slot O gI bI).mag : ℝ) := le_trans (by positivity) hb4.2.2
          have hm4i : 0 ≤ (lo4 dI ns slot O gI bI).mag := by exact_mod_cast hm4
          have := (this hm4i).2
          have h5 : (1 : ℤ) ≤ chg (lo4 dI ns slot O gI bI).mag := by exact_mod_cast this
          omega
        have h4 : (((lo4 dI ns slot O gI bI).mag : ℤ) : ℝ) ≤ (((15 * SC : ℤ)) : ℝ) := by exact_mod_cast h3
        rw [Int.cast_mul, hSC] at h4
        simpa using h4
      linarith [hb4.2.2]
    have h2 : |fl (o' * asw fl g dg) + asw fl b db| ≤ 15 := by
      by_contra hcon
      have := not_le.mp hcon
      nlinarith
    linarith
  have hfin := hC.rnd.err _ hz2M
  exact wide_round hC ê hê _ _ _ hz2 hfin

/-! ### lower bound for the magnitude of the gain form -/

theorem abs_floor_le (y F : ℝ) (h1 : F ≤ y) (h2 : y < F + 1) : |y| ≤ |F| + 1 := by
  rw [abs_le]
  constructor
  · have := neg_abs_le F; linarith
  · have := le_abs_self F; linarith

theorem linI_map_floor (gI : ℤ) : ∀ t : List ℤ,
    (|(gI : ℝ)| / 2 ^ 56) * (linI t : ℝ) - (t.length : ℝ)
      ≤ (linI (t.map (fun x => gI * x / SC)) : ℝ) := by
  intro t
  induction t with
  | nil => simp [linI_nil']
  | cons x l ih =>
    have hSC : ((SC : ℤ) : ℝ) = 2 ^ 56 := by unfold SC; norm_num
    have hf := floor_facts (gI * x) SC (by unfold SC; norm_num)
    rw [hSC] at hf
    push_cast at hf
    have h1 := abs_floor_le _ _ hf.1 hf.2
    have h2 : |(gI : ℝ) * x / 2 ^ 56| = |(gI : ℝ)| / 2 ^ 56 * |(x : ℝ)| := by
      rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 56)]; ring
    rw [h2] at h1
    simp only [List.map_cons, linI_cons, List.length_cons]
    push_cast
    rw [iabs_cast, iabs_cast]
    linarith

theorem linI_addAt : ∀ (l : List ℤ) (k : ℕ) (v : ℤ), 0 ≤ v → l.getD k 0 = 0 → k < l.length →
    linI (addAt l k v) = linI l + v := by
  intro l
  induction l with
  | nil => intro k v _ _ h; simp at h
  | cons a l ih =>
    intro k v hv hz hk
    cases k with
    | zero =>
      simp only [List.getD_cons_zero] at hz
      subst hz
      simp only [addAt]
      rw [linI_cons, linI_cons]
      have : iabs (0 + v) = v := by rw [iabs_eq']; simp [abs_of_nonneg hv]
      have h0 : iabs (0 : ℤ) = 0 := by simp [iabs]
      rw [this, h0]; ring
    | succ k' =>
      simp only [List.getD_cons_succ] at hz
      simp only [addAt]
      rw [linI_cons, linI_cons, ih k' v hv hz (by simpa using hk)]
      ring

theorem low_sound (g δ : ℝ) (hδ : 0 ≤ δ) (O : FF) (gI dI : ℤ) (ns : ℕ) (slot : Option ℕ)
    (hg : (gI : ℝ) = g * 2 ^ 56) (hd : (dI : ℝ) = δ * 2 ^ 56) (hOl : O.t.length = ns)
    (hr0 : 0 ≤ O.r)
    (hz : ∀ sl, slot = some sl → (lo2b dI ns O gI).t.getD sl 0 = 0 ∧ sl < ns) :
    (|g| + δ) * (O.mag : ℝ) ≤ ((lo2 dI ns slot O gI).mag : ℝ) := by
  have hSC : ((SC : ℤ) : ℝ) = 2 ^ 56 := by unfold SC; norm_num
  have hSpos : (0 : ℝ) < 2 ^ 56 := by norm_num
  have hK := cdiv_facts (dI * (iabs O.c + SC)) SC (by unfold SC; norm_num)
  rw [hSC] at hK
  push_cast at hK
  rw [iabs_cast] at hK
  simp only [hSC] at hK
  have hKδ : δ * (|(O.c : ℝ)| + 2 ^ 56) ≤ ((cdiv (dI * (iabs O.c + SC)) SC : ℤ) : ℝ) := by
    have : (dI : ℝ) * (|(O.c : ℝ)| + 2 ^ 56) / 2 ^ 56 = δ * (|(O.c : ℝ)| + 2 ^ 56) := by
      rw [hd]; ring
    linarith [hK.1]
  have hK0 : 0 ≤ cdiv (dI * (iabs O.c + SC)) SC := by
    have : (0 : ℝ) ≤ ((cdiv (dI * (iabs O.c + SC)) SC : ℤ) : ℝ) :=
      le_trans (mul_nonneg hδ (by positivity)) hKδ
    exact_mod_cast this
  have hbump : (lo2 dI ns slot O gI).mag
      = (lo2b dI ns O gI).mag + cdiv (dI * (iabs O.c + SC)) SC := by
    cases slot with
    | none =>
      simp only [lo2, FF.bump, FF.mag, FF.dev]
      omega
    | some sl =>
      obtain ⟨hz1, hz2⟩ := hz sl rfl
      have hlen : sl < (lo2b dI ns O gI).t.length := by
        have : (lo2b dI ns O gI).t.length = ns := by simp [lo2b, hOl]
        omega
      have := linI_addAt (lo2b dI ns O gI).t sl _ hK0 hz1 hlen
      simp only [lo2, FF.bump, FF.mag, FF.dev]
      omega
  rw [hbump]
  have hmagb : (lo2b dI ns O gI).mag = iabs (gI * O.c / SC)
      + (linI (O.t.map (fun x => gI * x / SC))
        + (cdiv (iabs gI * O.r) SC + ((ns : ℤ) + 1) + cdiv (dI * O.dev) SC)) := rfl
  rw [hmagb]
  have hF := floor_facts (gI * O.c) SC (by unfold SC; norm_num)
  rw [hSC] at hF
  push_cast at hF
  have f1 := abs_floor_le _ _ hF.1 hF.2
  have e1 : (gI : ℝ) * O.c / 2 ^ 56 = g * O.c := by rw [hg]; ring
  rw [e1, abs_mul] at f1
  have f2 := linI_map_floor gI O.t
  have e2 : |(gI : ℝ)| / 2 ^ 56 = |g| := by
    rw [hg, abs_mul, abs_of_pos hSpos]; ring
  rw [e2, hOl] at f2
  have f3 := cdiv_facts (iabs gI * O.r) SC (by unfold SC; norm_num)
  rw [hSC] at f3
  push_cast at f3
  rw [iabs_cast] at f3
  have e3 : |(gI : ℝ)| * (O.r : ℝ) / 2 ^ 56 = |g| * (O.r : ℝ) := by
    rw [hg, abs_mul, abs_of_pos hSpos]; ring
  rw [e3] at f3
  have f4 := cdiv_facts (dI * O.dev) SC (by unfold SC; norm_num)
  rw [hSC] at f4
  push_cast at f4
  have e4 : (dI : ℝ) * (O.dev : ℝ) / 2 ^ 56 = δ * (O.dev : ℝ) := by
    rw [hd]; ring
  rw [e4] at f4
  have hdev : (O.dev : ℝ) = (linI O.t : ℝ) + (O.r : ℝ) := by simp [FF.dev]
  have hmg : (O.mag : ℝ) = |(O.c : ℝ)| + (O.dev : ℝ) := by
    unfold FF.mag; push_cast; rw [iabs_cast]
  push_cast
  rw [iabs_cast]
  rw [hmg, hdev]
  rw [hdev] at f4
  have hL0 : (0 : ℝ) ≤ (linI O.t : ℝ) := by exact_mod_cast linI_nonneg O.t
  have hr0R : (0 : ℝ) ≤ (O.r : ℝ) := by exact_mod_cast hr0
  nlinarith [f1, f2, f3.1, f4.1, hKδ, mul_nonneg hδ (abs_nonneg (O.c : ℝ)), mul_nonneg hδ hSpos.le]

end Lane4.Case
