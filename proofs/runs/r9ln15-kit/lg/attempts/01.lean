set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Lane4.Case

open Lane4.RSeq (Vec pdot radd rsum)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.LNC Lane4.R7K2

lemma rs_abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases abs_cases x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases abs_cases y with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  rcases abs_cases (x + y) with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> linarith

lemma rs_SCr : ((SC : ℤ) : ℝ) = (2 : ℝ) ^ 56 := by
  first
    | (simp [SC]; done)
    | (unfold SC; norm_num)
    | (unfold SC; push_cast; rfl)

lemma rs_SC_pos : (0 : ℤ) < SC := by
  unfold SC; norm_num

def rs_lsum : List ℤ → ℤ
  | [] => 0
  | a :: l => iabs a + rs_lsum l

lemma rs_iabs_cast (a : ℤ) : ((iabs a : ℤ) : ℝ) = |(a : ℝ)| := by
  have h : iabs a = |a| := by
    unfold iabs
    first | exact Int.natCast_natAbs a | simp
  rw [h, Int.cast_abs]

lemma rs_iabs_nonneg (a : ℤ) : 0 ≤ iabs a := by
  unfold iabs; positivity

lemma rs_lsum_nonneg : ∀ l : List ℤ, 0 ≤ rs_lsum l
  | [] => le_refl _
  | a :: l => by
    simp only [rs_lsum]
    have h1 := rs_iabs_nonneg a
    have h2 := rs_lsum_nonneg l
    omega

lemma rs_foldl_lsum : ∀ (t : List ℤ) (s : ℤ),
    t.foldl (fun s v => s + iabs v) s = s + rs_lsum t
  | [], s => by simp [rs_lsum]
  | a :: l, s => by
    simp only [List.foldl_cons, rs_lsum]
    rw [rs_foldl_lsum l]
    ring

lemma rs_linI_eq (t : List ℤ) : linI t = rs_lsum t := by
  unfold linI
  rw [rs_foldl_lsum]
  simp

lemma rs_linVal_le (e : ℕ → ℝ) (he : ∀ k, |e k| ≤ 1) :
    ∀ (t : List ℤ) (k : ℕ), |linValI t e k| ≤ ((rs_lsum t : ℤ) : ℝ)
  | [], k => by simp [linValI, rs_lsum]
  | a :: l, k => by
    have ih := rs_linVal_le e he l (k + 1)
    simp only [linValI, rs_lsum]
    push_cast
    rw [rs_iabs_cast]
    have h1 : |(a : ℝ) * e k| ≤ |(a : ℝ)| := by
      rw [abs_mul]
      calc |(a : ℝ)| * |e k| ≤ |(a : ℝ)| * 1 :=
            mul_le_mul_of_nonneg_left (he k) (abs_nonneg _)
        _ = |(a : ℝ)| := mul_one _
    have h2 := rs_abs_add ((a : ℝ) * e k) (linValI l e (k + 1))
    linarith

lemma rs_fdiv_le (a b : ℤ) (hb : 0 < b) : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  have h1 := Int.ediv_add_emod a b
  have h2 := Int.emod_nonneg a hb.ne'
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [le_div_iff₀ hbR]
  have h3 : ((b * (a / b) + a % b : ℤ) : ℝ) = (a : ℝ) := by rw [h1]
  have h4 : (0 : ℝ) ≤ ((a % b : ℤ) : ℝ) := by exact_mod_cast h2
  push_cast at h3
  nlinarith

lemma rs_fdiv_gt (a b : ℤ) (hb : 0 < b) : (a : ℝ) / (b : ℝ) < ((a / b : ℤ) : ℝ) + 1 := by
  have h1 := Int.ediv_add_emod a b
  have h3 := Int.emod_lt_of_pos a hb
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_lt_iff₀ hbR]
  have e1 : ((b * (a / b) + a % b : ℤ) : ℝ) = (a : ℝ) := by rw [h1]
  have e2 : ((a % b : ℤ) : ℝ) < b := by exact_mod_cast h3
  push_cast at e1
  nlinarith

lemma rs_cdiv_ge (a b : ℤ) (hb : 0 < b) : (a : ℝ) / (b : ℝ) ≤ (cdiv a b : ℝ) := by
  have h := rs_fdiv_le (-a) b hb
  unfold cdiv
  push_cast at h ⊢
  have e1 : (a : ℝ) / b = -((-(a : ℝ)) / b) := by ring
  linarith

lemma rs_chg_gt (m : ℤ) : (m : ℝ) / 2 ^ 22 < (chg m : ℝ) := by
  have h := rs_fdiv_gt m (2 ^ 22) (by norm_num)
  unfold chg
  push_cast at h ⊢
  linarith

lemma rs_map_lin (k1 : ℤ) (e : ℕ → ℝ) (he : ∀ k, |e k| ≤ 1) :
    ∀ (l : List ℤ) (k : ℕ),
      |linValI (l.map (fun t => (-k1 * t) / SC)) e k + ((k1 : ℝ) / 2 ^ 56) * linValI l e k|
        ≤ (l.length : ℝ)
  | [], k => by simp [linValI]
  | a :: l, k => by
    have ih := rs_map_lin k1 e he l (k + 1)
    have h1 := rs_fdiv_le (-k1 * a) SC rs_SC_pos
    have h2 := rs_fdiv_gt (-k1 * a) SC rs_SC_pos
    rw [rs_SCr] at h1 h2
    simp only [List.map_cons, linValI, List.length_cons]
    push_cast at h1 h2 ih ⊢
    generalize ((-k1 * a / SC : ℤ) : ℝ) = F at h1 h2 ⊢
    generalize linValI (List.map (fun t => (-k1 * t) / SC) l) e (k + 1) = X at ih ⊢
    generalize linValI l e (k + 1) = Y at ih ⊢
    have hek := he k
    have hδ : |F - (-(k1 : ℝ) * a / 2 ^ 56)| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    have e1 : F * e k + X + (k1 : ℝ) / 2 ^ 56 * ((a : ℝ) * e k + Y)
        = (F - (-(k1 : ℝ) * a / 2 ^ 56)) * e k + (X + (k1 : ℝ) / 2 ^ 56 * Y) := by ring
    rw [e1]
    have h3 : |(F - (-(k1 : ℝ) * a / 2 ^ 56)) * e k| ≤ 1 := by
      rw [abs_mul]
      calc |F - (-(k1 : ℝ) * a / 2 ^ 56)| * |e k| ≤ 1 * 1 :=
            mul_le_mul hδ hek (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have h4 := rs_abs_add ((F - (-(k1 : ℝ) * a / 2 ^ 56)) * e k) (X + (k1 : ℝ) / 2 ^ 56 * Y)
    linarith

lemma rs_step4 (u η p s : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / 2 ^ 149) (hp : 1 / 2 ^ 56 ≤ p) (hs : |s - p| ≤ u * p + η) :
    0 < s ∧ |1 / s - 1 / p| ≤ (1 / p) / 2 ^ 22 := by
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have h1 : u * p ≤ p / 2 ^ 24 := by
    calc u * p ≤ (1 / 2 ^ 24) * p := mul_le_mul_of_nonneg_right hu1 hp0.le
      _ = p / 2 ^ 24 := by ring
  have h2 : η ≤ p / 2 ^ 24 := by
    calc η ≤ 1 / 2 ^ 149 := hη1
      _ ≤ (1 / 2 ^ 56) / 2 ^ 24 := by norm_num
      _ ≤ p / 2 ^ 24 := by gcongr
  have h3 : |s - p| ≤ p / 2 ^ 23 := by
    have : p / 2 ^ 24 + p / 2 ^ 24 = p / 2 ^ 23 := by ring
    linarith
  obtain ⟨h4, h5⟩ := abs_le.1 h3
  have hs0 : p / 2 ≤ s := by linarith
  have hspos : 0 < s := by linarith
  refine ⟨hspos, ?_⟩
  have key : 1 / s - 1 / p = (p - s) / (s * p) := by
    rw [div_sub_div _ _ hspos.ne' hp0.ne']
    ring
  rw [key, abs_div, abs_of_pos (mul_pos hspos hp0), div_le_iff₀ (mul_pos hspos hp0)]
  have e1 : (1 / p) / 2 ^ 22 * (s * p) = s / 2 ^ 22 := by
    have := hp0.ne'
    first | (field_simp; done) | (field_simp; ring)
  rw [e1, abs_sub_comm]
  linarith

lemma rs_taylor (p q r0 : ℝ) (hr0 : 0 < r0) (hp : r0 ≤ p) (hq : r0 ≤ q) :
    |1 / p - 1 / q + (p ^ 2 - q ^ 2) / (2 * q ^ 3)| ≤ 3 / 8 * (p ^ 2 - q ^ 2) ^ 2 / r0 ^ 5 := by
  have hp0 : 0 < p := lt_of_lt_of_le hr0 hp
  have hq0 : 0 < q := lt_of_lt_of_le hr0 hq
  have hpne := hp0.ne'
  have hqne := hq0.ne'
  have hrne := hr0.ne'
  have key : 1 / p - 1 / q + (p ^ 2 - q ^ 2) / (2 * q ^ 3)
      = (p - q) ^ 2 * (p + 2 * q) / (2 * p * q ^ 3) := by
    first | (field_simp; done) | (field_simp; ring)
  have hnn : 0 ≤ (p - q) ^ 2 * (p + 2 * q) / (2 * p * q ^ 3) := by positivity
  rw [key, abs_of_nonneg hnn]
  have hA1 : r0 ^ 2 * q ≤ q ^ 3 := by
    have : 0 ≤ q * ((q - r0) * (q + r0)) :=
      mul_nonneg hq0.le (mul_nonneg (by linarith) (by linarith))
    nlinarith
  have hA2 : 4 * r0 ^ 2 ≤ (p + q) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ p + q - 2 * r0) (by linarith : 0 ≤ p + q + 2 * r0)]
  have hA3 : p * (r0 ^ 2 * q) * (4 * r0 ^ 2) ≤ p * q ^ 3 * (p + q) ^ 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hA1 hp0.le) hA2 (by positivity) (by positivity)
  have hA4 : r0 * (p + 2 * q) ≤ 3 * (p * q) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hq) hp0.le, mul_nonneg (sub_nonneg.2 hp) hq0.le]
  have hpoly : 8 * r0 ^ 5 * (p + 2 * q) ≤ 6 * (p * q ^ 3 * (p + q) ^ 2) := by
    have h5 : 0 ≤ r0 ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hA4 h5, hA3]
  have h2 : (p ^ 2 - q ^ 2) ^ 2 = (p - q) ^ 2 * (p + q) ^ 2 := by ring
  have hfrac : (p + 2 * q) / (2 * p * q ^ 3) ≤ 3 * (p + q) ^ 2 / (8 * r0 ^ 5) := by
    rw [div_le_iff₀ (by positivity)]
    have : 3 * (p + q) ^ 2 / (8 * r0 ^ 5) * (2 * p * q ^ 3)
        = (6 * (p * q ^ 3 * (p + q) ^ 2)) / (8 * r0 ^ 5) := by
      first | (field_simp; done) | (field_simp; ring)
    rw [this, le_div_iff₀ (by positivity)]
    nlinarith [hpoly]
  calc (p - q) ^ 2 * (p + 2 * q) / (2 * p * q ^ 3)
      = (p - q) ^ 2 * ((p + 2 * q) / (2 * p * q ^ 3)) := by ring
    _ ≤ (p - q) ^ 2 * (3 * (p + q) ^ 2 / (8 * r0 ^ 5)) :=
        mul_le_mul_of_nonneg_left hfrac (sq_nonneg _)
    _ = 3 / 8 * (p ^ 2 - q ^ 2) ^ 2 / r0 ^ 5 := by
        rw [h2]
        first | (field_simp; done) | (field_simp; ring)

lemma rs_slope (S g0 G e k1 : ℝ) (hS : 0 < S) (hg0 : 0 < g0) (hG : 0 < G)
    (hGe : |g0 - G| ≤ e) (he : e ≤ g0 / 8)
    (hk1a : g0 ^ 3 / (2 * S ^ 2) ≤ k1) (hk1b : k1 ≤ g0 ^ 3 / (2 * S ^ 2) + 1) :
    |k1 - G ^ 3 / (2 * S ^ 2)| ≤ 1 + 4 * k1 * e / g0 := by
  have hSne := hS.ne'
  have hgne := hg0.ne'
  have he0 : 0 ≤ e := (abs_nonneg _).trans hGe
  have hGle : G ≤ 9 / 8 * g0 := by
    have := (abs_le.1 hGe).1
    linarith
  have hQ : g0 ^ 2 + g0 * G + G ^ 2 ≤ 4 * g0 ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hGle hg0.le, mul_le_mul hGle hGle hG.le (by positivity)]
  have hcub : |g0 ^ 3 - G ^ 3| ≤ 4 * e * g0 ^ 2 := by
    have h1 : g0 ^ 3 - G ^ 3 = (g0 - G) * (g0 ^ 2 + g0 * G + G ^ 2) := by ring
    rw [h1, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ g0 ^ 2 + g0 * G + G ^ 2)]
    calc |g0 - G| * (g0 ^ 2 + g0 * G + G ^ 2) ≤ e * (4 * g0 ^ 2) :=
          mul_le_mul hGe hQ (by positivity) he0
      _ = 4 * e * g0 ^ 2 := by ring
  have h5 : |(g0 ^ 3 - G ^ 3) / (2 * S ^ 2)| ≤ 4 * e * g0 ^ 2 / (2 * S ^ 2) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * S ^ 2)]
    gcongr
  have h6 : 4 * e * g0 ^ 2 / (2 * S ^ 2) ≤ 4 * k1 * e / g0 := by
    have e1 : 4 * e * g0 ^ 2 / (2 * S ^ 2) = 4 * e * (g0 ^ 3 / (2 * S ^ 2)) / g0 := by
      first | (field_simp; done) | (field_simp; ring)
    rw [e1]
    have : 4 * e * (g0 ^ 3 / (2 * S ^ 2)) ≤ 4 * k1 * e := by
      nlinarith [mul_le_mul_of_nonneg_left hk1a he0]
    gcongr
  have h7 : k1 - G ^ 3 / (2 * S ^ 2)
      = (k1 - g0 ^ 3 / (2 * S ^ 2)) + (g0 ^ 3 - G ^ 3) / (2 * S ^ 2) := by ring
  have h8 : |k1 - g0 ^ 3 / (2 * S ^ 2)| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  rw [h7]
  have := rs_abs_add (k1 - g0 ^ 3 / (2 * S ^ 2)) ((g0 ^ 3 - G ^ 3) / (2 * S ^ 2))
  linarith

lemma rs_centre (S c a glo ghi : ℝ) (hS : 0 < S) (ha : 1 ≤ a) (h1 : a * a ≤ c * S)
    (h2 : c * S < (a + 1) * (a + 1)) (hglo : glo ≤ S * S / (a + 1)) (hghi : S * S / a ≤ ghi) :
    glo ≤ S ^ 2 / Real.sqrt (c * S) ∧ S ^ 2 / Real.sqrt (c * S) ≤ ghi := by
  have hcS : 0 ≤ c * S := le_trans (mul_self_nonneg a) h1
  have hRsq : Real.sqrt (c * S) * Real.sqrt (c * S) = c * S := Real.mul_self_sqrt hcS
  have hR0 : 0 ≤ Real.sqrt (c * S) := Real.sqrt_nonneg _
  generalize Real.sqrt (c * S) = R at hRsq hR0 ⊢
  have haR : a ≤ R := by
    by_contra h
    push_neg at h
    nlinarith [mul_pos (sub_pos.2 h) (by linarith : 0 < a + R)]
  have hRa : R < a + 1 := by
    by_contra h
    push_neg at h
    nlinarith [mul_nonneg (sub_nonneg.2 h) (by linarith : 0 ≤ R + (a + 1))]
  have hRpos : 0 < R := by linarith
  constructor
  · calc glo ≤ S * S / (a + 1) := hglo
      _ ≤ S ^ 2 / R := by
        rw [sq]
        have := one_div_lt_one_div_of_lt hRpos hRa
        calc S * S / (a + 1) = (S * S) * (1 / (a + 1)) := by ring
          _ ≤ (S * S) * (1 / R) := mul_le_mul_of_nonneg_left this.le (by positivity)
          _ = S * S / R := by ring
  · calc S ^ 2 / R ≤ S * S / a := by
        rw [sq]
        have := one_div_le_one_div_of_le (by linarith : 0 < a) haR
        calc S * S / R = (S * S) * (1 / R) := by ring
          _ ≤ (S * S) * (1 / a) := mul_le_mul_of_nonneg_left this (by positivity)
          _ = S * S / a := by ring
      _ ≤ ghi := hghi

lemma rs_rcore (u η S c L r ℓ D vh b glo ghi g0 eg k1 chgM Mb Q1 Q3 Q4 Q5 N lin s : ℝ)
    (hS : S = 2 ^ 56)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2 ^ 149)
    (hs : 0 ≤ vh → |s - Real.sqrt vh| ≤ u * Real.sqrt vh + η)
    (hvh : |vh * S - (c + L)| ≤ r) (hL : |L| ≤ ℓ) (hD : D = ℓ + r) (hpos : 0 < c - D)
    (hb1 : 1 ≤ b) (hb2 : b * b ≤ (c - D) * S)
    (hbr : glo ≤ S ^ 2 / Real.sqrt (c * S) ∧ S ^ 2 / Real.sqrt (c * S) ≤ ghi)
    (hg0 : glo ≤ g0 ∧ g0 ≤ ghi)
    (hMb : S * S / b ≤ Mb) (hchg : Mb / 2 ^ 22 < chgM)
    (heg : eg = ghi - glo + 1 + chgM) (hguard : 8 * eg ≤ g0)
    (hk1 : g0 ^ 3 / (2 * S * S) ≤ k1 ∧ k1 ≤ g0 ^ 3 / (2 * S * S) + 1)
    (hQ1 : k1 * r / S ≤ Q1) (hQ3 : 4 * k1 * eg * D / (g0 * S) ≤ Q3) (hQ4 : D / S ≤ Q4)
    (hQ5 : 3 * D * D * S ^ 4 / (8 * b ^ 5) ≤ Q5)
    (hlin : |lin + (k1 / S) * L| ≤ N) :
    0 < s ∧ |1 / s * S - (g0 + lin)| ≤ Q1 + eg + Q3 + Q4 + Q5 + (N + 2) := by
  have hSpos : 0 < S := by rw [hS]; positivity
  have hSne := hSpos.ne'
  have hr0 : 0 ≤ r := (abs_nonneg _).trans hvh
  have hℓ0 : 0 ≤ ℓ := (abs_nonneg _).trans hL
  have hD0 : 0 ≤ D := by linarith
  have hc0 : 0 < c := by linarith
  have hvhl := abs_le.1 hvh
  have hLl := abs_le.1 hL
  have hW1 : -D ≤ vh * S - c := by linarith [hvhl.1, hvhl.2, hLl.1, hLl.2]
  have hW2 : vh * S - c ≤ D := by linarith [hvhl.1, hvhl.2, hLl.1, hLl.2]
  have hXge : c - D ≤ vh * S := by linarith
  have hvh0 : 0 < vh := by
    by_contra h
    push_neg at h
    nlinarith [mul_nonneg (neg_nonneg.2 h) hSpos.le]
  have hbpos : 0 < b := by linarith
  have hbne := hbpos.ne'
  have hr0pos : 0 < b / S := div_pos hbpos hSpos
  have hp0 : 0 < Real.sqrt vh := Real.sqrt_pos.2 hvh0
  have hp2 : Real.sqrt vh ^ 2 = vh := Real.sq_sqrt hvh0.le
  have hrp : b / S ≤ Real.sqrt vh := by
    have h1 : (b / S) ^ 2 ≤ vh := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hXge hSpos.le]
    exact le_trans (le_abs_self _) (Real.abs_le_sqrt h1)
  have hs' := hs hvh0.le
  generalize Real.sqrt vh = p at hp0 hp2 hrp hs'
  have hcS : 0 < c * S := mul_pos hc0 hSpos
  have hR0 : 0 < Real.sqrt (c * S) := Real.sqrt_pos.2 hcS
  have hR2 : Real.sqrt (c * S) ^ 2 = c * S := Real.sq_sqrt hcS.le
  have hbR : b ≤ Real.sqrt (c * S) := by
    have h1 : b ^ 2 ≤ c * S := by nlinarith [mul_nonneg hD0 hSpos.le]
    exact le_trans (le_abs_self _) (Real.abs_le_sqrt h1)
  generalize Real.sqrt (c * S) = R at hR0 hR2 hbR hbr
  have hq0 : 0 < R / S := div_pos hR0 hSpos
  have hq2 : (R / S) ^ 2 = c / S := by
    rw [div_pow, hR2]
    first | (field_simp; done) | (field_simp; ring)
  have hrq : b / S ≤ R / S := by gcongr
  generalize hqdef : R / S = q at hq0 hq2 hrq
  have hpne := hp0.ne'
  have hqne := hq0.ne'
  have ht := rs_taylor p q (b / S) hr0pos hrp hrq
  rw [hp2, hq2] at ht
  have hW : (vh * S - c) ^ 2 ≤ D * D := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ D + (vh * S - c)) (by linarith : 0 ≤ D - (vh * S - c))]
  have ht3 : |S / p - S / q + (1 / (2 * q ^ 3)) * (vh * S - c)|
      ≤ 3 * D * D * S ^ 4 / (8 * b ^ 5) := by
    have e1 : S / p - S / q + (1 / (2 * q ^ 3)) * (vh * S - c)
        = S * (1 / p - 1 / q + (vh - c / S) / (2 * q ^ 3)) := by
      first | (field_simp; done) | (field_simp; ring)
    rw [e1, abs_mul, abs_of_pos hSpos]
    calc S * |1 / p - 1 / q + (vh - c / S) / (2 * q ^ 3)|
        ≤ S * (3 / 8 * (vh - c / S) ^ 2 / (b / S) ^ 5) :=
          mul_le_mul_of_nonneg_left ht hSpos.le
      _ = 3 / 8 * (vh * S - c) ^ 2 * S ^ 4 / b ^ 5 := by
          first | (field_simp; done) | (field_simp; ring)
      _ ≤ 3 * D * D * S ^ 4 / (8 * b ^ 5) := by
          have e2 : 3 * D * D * S ^ 4 / (8 * b ^ 5) = 3 / 8 * (D * D) * S ^ 4 / b ^ 5 := by
            first | (field_simp; done) | (field_simp; ring)
          rw [e2]
          gcongr
  have hG0 : 0 < S / q := div_pos hSpos hq0
  have hGeq : S / q = S ^ 2 / R := by
    rw [← hqdef]
    first | (field_simp; done) | (field_simp; ring)
  have hGbr : glo ≤ S / q ∧ S / q ≤ ghi := by rw [hGeq]; exact hbr
  have hchgpos : 0 < chgM := by
    have : 0 < S * S / b := by positivity
    linarith
  have hge : ghi - glo ≤ eg := by linarith
  have hgg : 0 ≤ ghi - glo := by linarith [hGbr.1, hGbr.2]
  have hegpos : 1 < eg := by linarith
  have hegpos' : 0 < eg := by linarith
  have hg0pos : 0 < g0 := by linarith
  have hgne := hg0pos.ne'
  have hGe : |g0 - S / q| ≤ ghi - glo :=
    abs_le.2 ⟨by linarith [hg0.1, hg0.2, hGbr.1, hGbr.2], by linarith [hg0.1, hg0.2, hGbr.1, hGbr.2]⟩
  have hk1' : g0 ^ 3 / (2 * S ^ 2) ≤ k1 ∧ k1 ≤ g0 ^ 3 / (2 * S ^ 2) + 1 := by
    have : 2 * S ^ 2 = 2 * S * S := by ring
    rw [this]; exact hk1
  have hslope := rs_slope S g0 (S / q) eg k1 hSpos hg0pos hG0 (hGe.trans hge) (by linarith)
    hk1'.1 hk1'.2
  have hk1pos : 0 < k1 := by
    have : 0 < g0 ^ 3 / (2 * S * S) := by positivity
    linarith [hk1.1]
  have hκ : k1 / S - 1 / (2 * q ^ 3) = (1 / S) * (k1 - (S / q) ^ 3 / (2 * S ^ 2)) := by
    first | (field_simp; done) | (field_simp; ring)
  have e3 : (1 / S) * (1 + 4 * k1 * eg / g0) * D = D / S + 4 * k1 * eg * D / (g0 * S) := by
    first | (field_simp; done) | (field_simp; ring)
  have hWabs : |vh * S - c| ≤ D := abs_le.2 ⟨hW1, hW2⟩
  have hA1 : |(k1 / S - 1 / (2 * q ^ 3)) * (vh * S - c)| ≤ D / S + 4 * k1 * eg * D / (g0 * S) := by
    rw [abs_mul, hκ, abs_mul, abs_of_pos (one_div_pos.2 hSpos)]
    have hnn : 0 ≤ 1 / S * (1 + 4 * k1 * eg / g0) := by positivity
    calc 1 / S * |k1 - (S / q) ^ 3 / (2 * S ^ 2)| * |vh * S - c|
        ≤ 1 / S * (1 + 4 * k1 * eg / g0) * D :=
          mul_le_mul (mul_le_mul_of_nonneg_left hslope (by positivity)) hWabs (abs_nonneg _) hnn
      _ = D / S + 4 * k1 * eg * D / (g0 * S) := e3
  have hA2 : |(k1 / S) * (vh * S - (c + L))| ≤ k1 * r / S := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ k1 / S)]
    calc k1 / S * |vh * S - (c + L)| ≤ k1 / S * r :=
          mul_le_mul_of_nonneg_left hvh (by positivity)
      _ = k1 * r / S := by ring
  have ht4 : |-(1 / (2 * q ^ 3)) * (vh * S - c) - lin| ≤ Q1 + Q3 + Q4 + N := by
    have e2 : -(1 / (2 * q ^ 3)) * (vh * S - c) - lin
        = -(lin + (k1 / S) * L) + (k1 / S - 1 / (2 * q ^ 3)) * (vh * S - c)
          + -((k1 / S) * (vh * S - (c + L))) := by ring
    rw [e2]
    have h1 := rs_abs_add (-(lin + (k1 / S) * L) + (k1 / S - 1 / (2 * q ^ 3)) * (vh * S - c))
      (-((k1 / S) * (vh * S - (c + L))))
    have h2 := rs_abs_add (-(lin + (k1 / S) * L)) ((k1 / S - 1 / (2 * q ^ 3)) * (vh * S - c))
    have h3 : |-(lin + (k1 / S) * L)| = |lin + (k1 / S) * L| := abs_neg _
    have h4 : |-((k1 / S) * (vh * S - (c + L)))| = |(k1 / S) * (vh * S - (c + L))| := abs_neg _
    linarith
  have hp1 : 1 / 2 ^ 56 ≤ p := by
    have h0 : (1 : ℝ) / 2 ^ 56 ≤ b / 2 ^ 56 := by gcongr
    rw [hS] at hrp
    linarith
  obtain ⟨hs0, hs1⟩ := rs_step4 u η p s hu0 hu1 hη0 hη1 hp1 hs'
  have ht1 : |S / s - S / p| ≤ chgM := by
    have e1 : S / s - S / p = S * (1 / s - 1 / p) := by ring
    rw [e1, abs_mul, abs_of_pos hSpos]
    have h1 : 1 / p ≤ S / b := by
      have := one_div_le_one_div_of_le hr0pos hrp
      rwa [one_div_div] at this
    have hSp : S / p ≤ Mb := by
      calc S / p = S * (1 / p) := by ring
        _ ≤ S * (S / b) := mul_le_mul_of_nonneg_left h1 hSpos.le
        _ = S * S / b := by ring
        _ ≤ Mb := hMb
    calc S * |1 / s - 1 / p| ≤ S * ((1 / p) / 2 ^ 22) := mul_le_mul_of_nonneg_left hs1 hSpos.le
      _ = (S / p) / 2 ^ 22 := by ring
      _ ≤ Mb / 2 ^ 22 := by linarith
      _ ≤ chgM := hchg.le
  have hfin : 1 / s * S - (g0 + lin)
      = (S / s - S / p) + (S / p - S / q + (1 / (2 * q ^ 3)) * (vh * S - c)) + (S / q - g0)
        + (-(1 / (2 * q ^ 3)) * (vh * S - c) - lin) := by ring
  refine ⟨hs0, ?_⟩
  rw [hfin]
  have a1 := rs_abs_add ((S / s - S / p) + (S / p - S / q + (1 / (2 * q ^ 3)) * (vh * S - c))
    + (S / q - g0)) (-(1 / (2 * q ^ 3)) * (vh * S - c) - lin)
  have a2 := rs_abs_add ((S / s - S / p) + (S / p - S / q + (1 / (2 * q ^ 3)) * (vh * S - c)))
    (S / q - g0)
  have a3 := rs_abs_add (S / s - S / p) (S / p - S / q + (1 / (2 * q ^ 3)) * (vh * S - c))
  have a4 : |S / q - g0| ≤ ghi - glo := by rw [abs_sub_comm]; exact hGe
  linarith

theorem rinv_sound : RinvSound := by
  unfold RinvSound
  intro u η M fl sq hC hSq ns vh v a b rinv e he hin hlen hpos hA hB hb hr
  have he' : ∀ k, |e k| ≤ 1 := he
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = 2 ^ 56 := ⟨_, rfl⟩
  have hSC : ((SC : ℤ) : ℝ) = S := by rw [hS]; exact rs_SCr
  have hSpos : 0 < S := by rw [hS]; positivity
  have hSCpos : (0 : ℤ) < SC := rs_SC_pos
  have hin' : |vh * S - ((v.c : ℝ) + linValI v.t e 0)| ≤ (v.r : ℝ) := by
    have h := hin
    unfold InFF at h
    rw [hS]
    exact h
  have hLb := rs_linVal_le e he' v.t 0
  have hdvdef : ((v.dev : ℤ) : ℝ) = ((rs_lsum v.t : ℤ) : ℝ) + (v.r : ℝ) := by
    unfold FF.dev
    rw [rs_linI_eq, Int.cast_add]
  have hr0R : (0 : ℝ) ≤ (v.r : ℝ) := (abs_nonneg _).trans hin'
  have hr0 : 0 ≤ v.r := by exact_mod_cast hr0R
  have hdv0 : 0 ≤ v.dev := by
    unfold FF.dev
    rw [rs_linI_eq]
    have := rs_lsum_nonneg v.t
    omega
  have hA' := hA
  unfold sqrtOK at hA'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hA'
  obtain ⟨⟨hA0, hA1⟩, hA2⟩ := hA'
  have hB' := hB
  unfold sqrtOK at hB'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hB'
  obtain ⟨⟨hB0, hB1⟩, hB2⟩ := hB'
  have hbpos : 0 < b := by omega
  have hbb : 1 ≤ b * b := by nlinarith
  have hcS1 : (v.c - v.dev) * SC ≤ v.c * SC := by nlinarith [mul_nonneg hdv0 hSCpos.le]
  have ha1 : 1 ≤ a := by
    by_contra h
    have : a = 0 := by omega
    subst this
    nlinarith
  have ha1r : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have ha2r : (a : ℝ) * a ≤ (v.c : ℝ) * S := by
    have h : ((a * a : ℤ) : ℝ) ≤ ((v.c * SC : ℤ) : ℝ) := by exact_mod_cast hA1
    push_cast [hSC] at h
    exact h
  have ha3r : (v.c : ℝ) * S < ((a : ℝ) + 1) * ((a : ℝ) + 1) := by
    have h : ((v.c * SC : ℤ) : ℝ) < (((a + 1) * (a + 1) : ℤ) : ℝ) := by exact_mod_cast hA2
    push_cast [hSC] at h
    exact h
  have hb1r : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbposR : (0 : ℝ) < b := by linarith
  have hb2r : (b : ℝ) * b ≤ ((v.c : ℝ) - (v.dev : ℝ)) * S := by
    have h : ((b * b : ℤ) : ℝ) ≤ (((v.c - v.dev) * SC : ℤ) : ℝ) := by exact_mod_cast hB1
    push_cast [hSC] at h
    exact h
  have hpos' : (0 : ℝ) < (v.c : ℝ) - (v.dev : ℝ) := by exact_mod_cast hpos
  unfold rinvF at hr
  try dsimp only at hr
  split at hr
  · rename_i hg
    obtain rfl := Option.some.inj hr
    generalize hglo : SC * SC / (a + 1) = glo at hg ⊢
    generalize hghi : cdiv (SC * SC) a = ghi at hg ⊢
    generalize hg0 : (glo + ghi) / 2 = g0 at hg ⊢
    generalize heg : ghi - glo + 1 + chg (cdiv (SC * SC) b) = eg at hg ⊢
    generalize hk1 : g0 ^ 3 / (2 * SC * SC) + 1 = k1
    have hglo_r : (glo : ℝ) ≤ S * S / ((a : ℝ) + 1) := by
      have h := rs_fdiv_le (SC * SC) (a + 1) (by omega)
      rw [hglo] at h
      push_cast [hSC] at h
      exact h
    have hghi_r : S * S / (a : ℝ) ≤ ghi := by
      have h := rs_cdiv_ge (SC * SC) a (by omega)
      rw [hghi] at h
      push_cast [hSC] at h
      exact h
    have hcb := rs_centre S (v.c : ℝ) (a : ℝ) (glo : ℝ) (ghi : ℝ) hSpos ha1r ha2r ha3r hglo_r hghi_r
    have hgg : glo ≤ ghi := by
      have := le_trans hcb.1 hcb.2
      exact_mod_cast this
    have hg0b : glo ≤ g0 ∧ g0 ≤ ghi := by omega
    have hg0r : (glo : ℝ) ≤ g0 ∧ (g0 : ℝ) ≤ ghi :=
      ⟨by exact_mod_cast hg0b.1, by exact_mod_cast hg0b.2⟩
    have hMb : S * S / (b : ℝ) ≤ ((cdiv (SC * SC) b : ℤ) : ℝ) := by
      have h := rs_cdiv_ge (SC * SC) b hbpos
      push_cast [hSC] at h
      exact h
    have hMpos : (0 : ℤ) < cdiv (SC * SC) b := by
      have : (0 : ℝ) < ((cdiv (SC * SC) b : ℤ) : ℝ) := lt_of_lt_of_le (by positivity) hMb
      exact_mod_cast this
    have hchg1 : 1 ≤ chg (cdiv (SC * SC) b) := by
      have := Int.ediv_nonneg hMpos.le (by norm_num : (0 : ℤ) ≤ 2 ^ 22)
      unfold chg
      linarith
    have hegpos : 1 ≤ eg := by linarith
    have hg0pos : 0 < g0 := by linarith
    have hchgR := rs_chg_gt (cdiv (SC * SC) b)
    have hegR : (eg : ℝ) = (ghi : ℝ) - glo + 1 + ((chg (cdiv (SC * SC) b) : ℤ) : ℝ) := by
      have h : ((ghi - glo + 1 + chg (cdiv (SC * SC) b) : ℤ) : ℝ) = (eg : ℝ) := by rw [heg]
      push_cast at h
      linarith
    have hguardR : (8 : ℝ) * eg ≤ g0 := by exact_mod_cast hg
    have hk1R : (g0 : ℝ) ^ 3 / (2 * S * S) ≤ k1 ∧ (k1 : ℝ) ≤ (g0 : ℝ) ^ 3 / (2 * S * S) + 1 := by
      have h1 := rs_fdiv_gt (g0 ^ 3) (2 * SC * SC) (by positivity)
      have h2 := rs_fdiv_le (g0 ^ 3) (2 * SC * SC) (by positivity)
      have hkc : (k1 : ℝ) = ((g0 ^ 3 / (2 * SC * SC) : ℤ) : ℝ) + 1 := by
        rw [← hk1, Int.cast_add, Int.cast_one]
      push_cast [hSC] at h1 h2
      constructor <;> linarith
    have hQ1 : (k1 : ℝ) * (v.r : ℝ) / S ≤ ((cdiv (k1 * v.r) SC : ℤ) : ℝ) := by
      have h := rs_cdiv_ge (k1 * v.r) SC hSCpos
      push_cast [hSC] at h
      exact h
    have hQ3 : 4 * (k1 : ℝ) * eg * (v.dev : ℝ) / ((g0 : ℝ) * S)
        ≤ ((cdiv (4 * k1 * eg * v.dev) (g0 * SC) : ℤ) : ℝ) := by
      have h := rs_cdiv_ge (4 * k1 * eg * v.dev) (g0 * SC) (mul_pos hg0pos hSCpos)
      push_cast [hSC] at h
      exact h
    have hQ4 : (v.dev : ℝ) / S ≤ ((cdiv v.dev SC : ℤ) : ℝ) := by
      have h := rs_cdiv_ge v.dev SC hSCpos
      push_cast [hSC] at h
      exact h
    have hQ5 : 3 * (v.dev : ℝ) * (v.dev : ℝ) * S ^ 4 / (8 * (b : ℝ) ^ 5)
        ≤ ((cdiv (3 * v.dev * v.dev * SC ^ 4) (8 * b ^ 5) : ℤ) : ℝ) := by
      have h5 : 0 < 8 * b ^ 5 := by have := pow_pos hbpos 5; linarith
      have h := rs_cdiv_ge (3 * v.dev * v.dev * SC ^ 4) (8 * b ^ 5) h5
      push_cast [hSC] at h
      exact h
    have hlin := rs_map_lin k1 e he' v.t 0
    rw [← hS, hlen] at hlin
    have hmain := rs_rcore u η S (v.c : ℝ) (linValI v.t e 0) (v.r : ℝ)
      ((rs_lsum v.t : ℤ) : ℝ) ((v.dev : ℤ) : ℝ) vh (b : ℝ) (glo : ℝ) (ghi : ℝ) (g0 : ℝ) (eg : ℝ)
      (k1 : ℝ) ((chg (cdiv (SC * SC) b) : ℤ) : ℝ) ((cdiv (SC * SC) b : ℤ) : ℝ)
      ((cdiv (k1 * v.r) SC : ℤ) : ℝ)
      ((cdiv (4 * k1 * eg * v.dev) (g0 * SC) : ℤ) : ℝ) ((cdiv v.dev SC : ℤ) : ℝ)
      ((cdiv (3 * v.dev * v.dev * SC ^ 4) (8 * b ^ 5) : ℤ) : ℝ) (ns : ℝ)
      (linValI (v.t.map (fun t => (-k1 * t) / SC)) e 0) (sq vh)
      hS hC.u0 hC.u1 hC.h0 hC.h1 (fun h => hSq.err vh h) hin' hLb hdvdef hpos' hb1r hb2r hcb
      hg0r hMb hchgR hegR hguardR hk1R hQ1 hQ3 hQ4 hQ5 hlin
    refine ⟨hmain.1, ?_, ?_⟩
    · unfold InFF
      dsimp only
      rw [← hS]
      refine le_trans hmain.2 (le_of_eq ?_)
      push_cast <;> ring
    · simp [hlen]
  · exact absurd hr (by simp)

end Lane4.Case
