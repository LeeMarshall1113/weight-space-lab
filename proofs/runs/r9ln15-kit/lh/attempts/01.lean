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

end Lane4.Case
