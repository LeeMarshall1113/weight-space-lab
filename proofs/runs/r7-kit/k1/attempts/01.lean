set_option linter.unusedVariables false
set_option linter.style.longLine false
namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft

theorem exp_neg11_le : Real.exp (-11) ≤ 17 / 10 ^ 6 := by
  have h1 := Real.exp_one_gt_d9
  have h2 : (2.7182818283 : ℝ) ^ 11 ≤ Real.exp 1 ^ 11 := by gcongr
  have h3 : Real.exp 11 = Real.exp 1 ^ 11 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h4 : (10 : ℝ) ^ 6 / 17 ≤ Real.exp 11 := by
    rw [h3]; refine le_trans ?_ h2; norm_num
  rw [Real.exp_neg, inv_eq_one_div]
  rw [div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  rw [div_le_iff₀ (by norm_num)] at h4
  linarith

theorem savg_near12 : SavgNear12 := by
  have hR := rsum_err
  have hG := geom_dist
  unfold SavgNear12
  intro u η M fl ex hfl hex hu hu2 hη hη2 c hnd n hcn hun hηn s f j hj hgap Sb hSb hSbM B hB hBM
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, w = swt fl ex c s := ⟨_, rfl⟩
  obtain ⟨t, htfun⟩ : ∃ t : ℕ → ℝ, t = fun k => fl (w k * f k) := ⟨_, rfl⟩
  have ht : ∀ k, t k = fl (w k * f k) := fun k => by rw [htfun]
  have hgoal : savg fl ex c s f = fl (rsum fl (c.map t) 0 / rsum fl (c.map w) 0) := by
    unfold savg
    rw [htfun, hw]
  rw [hgoal]
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = 1 / 2 ^ 100 := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hEdef]; positivity
  have hE6 : E ≤ 1 / 10 ^ 6 := by rw [hEdef]; norm_num
  have hE90 : 12 * E ≤ 1 / 2 ^ 90 := by rw [hEdef]; norm_num
  rw [← hEdef] at hηn
  have hη1 : η ≤ E := by
    have h0 : η ≤ 1 / 2 ^ 149 := hη2
    rw [hEdef]
    refine le_trans h0 ?_
    norm_num
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB j hj)
  have hBM' : B ≤ M := by linarith
  have hu6 : u ≤ 1 / 10 ^ 6 := le_trans hu2 (by norm_num)
  have hmn : (c.length : ℝ) ≤ n := by exact_mod_cast hcn
  have hum : u * (c.length : ℝ) ≤ 1 / 256 :=
    le_trans (mul_le_mul_of_nonneg_left hmn hu) hun
  have hmη : (c.length : ℝ) * η ≤ E :=
    le_trans (mul_le_mul_of_nonneg_right hmn hη) (by linarith)
  -- weights
  have hmax : ∀ k ∈ c, s k ≤ s j := by
    intro k hk
    by_cases hkj : k = j
    · rw [hkj]
    · have h1 := hgap k hk hkj
      have h0 : (0 : ℝ) ≤ (ndist j k : ℝ) := Nat.cast_nonneg _
      linarith
  have hwj : w j = 1 := by
    subst hw
    exact swt_winner hfl hex s c j hj hmax
  have hsm : smax s c = s j := smax_eq s c j hj hmax
  have hwdef : ∀ k, w k = ex (fl (s k - smax s c)) := fun k => by
    subst hw
    rfl
  have hw0 : ∀ k, 0 ≤ w k := fun k => by
    rw [hwdef k]
    exact hex.nonneg _
  have hq := exp_neg11_le
  have hq0 : 0 ≤ Real.exp (-11) := (Real.exp_pos _).le
  have hqh : Real.exp (-11) ≤ 1 / 2 := le_trans hq (by norm_num)
  have hnd1 : ∀ k, k ≠ j → 1 ≤ ndist j k := by
    intro k hk
    unfold ndist
    omega
  have hwk : ∀ k ∈ c, k ≠ j → w k ≤ (1 + 4 * u) * Real.exp (-11) ^ (ndist j k) + η := by
    intro k hk hkj
    have hd := hnd1 k hkj
    have hdR : (1 : ℝ) ≤ (ndist j k : ℝ) := by exact_mod_cast hd
    have hg := hgap k hk hkj
    have h1 := abs_le.mp (hSb k hk)
    have h2 := abs_le.mp (hSb j hj)
    have habs : |s k - s j| ≤ M := by
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have herr := hfl.err _ habs
    have hxa : |s k - s j| = -(s k - s j) := abs_of_nonpos (by linarith)
    rw [hxa] at herr
    have hup := (abs_le.mp herr).2
    have hy : 12 * (ndist j k : ℝ) ≤ -(s k - s j) := by linarith
    have hprod := mul_nonneg (sub_nonneg.mpr hy) (by linarith : (0 : ℝ) ≤ 1 - u)
    have hud := mul_le_mul_of_nonneg_right hu6 (show (0 : ℝ) ≤ (ndist j k : ℝ) by linarith)
    have hflx : fl (s k - s j) ≤ -11 * (ndist j k : ℝ) := by
      linarith [hup, hprod, hud, hη1, hE6]
    have hexp : Real.exp (fl (s k - s j)) ≤ Real.exp (-11) ^ (ndist j k) := by
      have h3 : Real.exp (fl (s k - s j)) ≤ Real.exp (((ndist j k : ℕ) : ℝ) * (-11)) :=
        Real.exp_le_exp.mpr (by linarith)
      rwa [Real.exp_nat_mul] at h3
    have hee := hex.err (fl (s k - s j)) (by linarith)
    have hee' := (abs_le.mp hee).2
    have hm := mul_le_mul_of_nonneg_left hexp (by linarith : (0 : ℝ) ≤ 1 + 4 * u)
    rw [hwdef k, hsm]
    linarith [hee', hm]
  have hw1 : ∀ k ∈ c, w k ≤ 1 := by
    intro k hk
    by_cases hkj : k = j
    · rw [hkj, hwj]
    · have h1 := hwk k hk hkj
      have h2 := pow_small hq0 (by linarith : Real.exp (-11) ≤ 1) (ndist j k) (hnd1 k hkj)
      have h3 : (1 + 4 * u) * Real.exp (-11) ^ (ndist j k) ≤ (1 + 4 * u) * Real.exp (-11) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      have h4 : (1 + 4 * u) * Real.exp (-11) ≤ 2 * (17 / 10 ^ 6) :=
        mul_le_mul (by linarith) hq hq0 (by norm_num)
      linarith
  -- the tail sum
  obtain ⟨F, hFdef⟩ : ∃ F : List ℕ, F = c.filter (fun k => decide (k ≠ j)) := ⟨_, rfl⟩
  have hF : ∀ k ∈ F, k ∈ c ∧ k ≠ j := by
    intro k hk
    rw [hFdef] at hk
    rcases List.mem_filter.mp hk with ⟨h1, h2⟩
    exact ⟨h1, by simpa using h2⟩
  have hFlen : (F.length : ℝ) ≤ c.length := by
    rw [hFdef]
    exact_mod_cast List.length_filter_le _ _
  have hFη : (F.length : ℝ) * η ≤ E :=
    le_trans (mul_le_mul_of_nonneg_right hFlen hη) hmη
  have hS1 : (c.map w).sum = 1 + (F.map w).sum := by
    rw [hFdef, sum_split w j c hnd hj, hwj]
  have hGeom : (F.map (fun k => Real.exp (-11) ^ ndist j k)).sum ≤ 4 * Real.exp (-11) := by
    rw [hFdef]
    exact hG c hnd j _ hq0 hqh
  have hL : (F.map w).sum ≤ (1 + 4 * u) * (4 * Real.exp (-11)) + E := by
    have h1 := sum_le_aff F w (fun k => Real.exp (-11) ^ ndist j k) (1 + 4 * u) η
      (fun k hk => hwk k (hF k hk).1 (hF k hk).2)
    have h2 := mul_le_mul_of_nonneg_left hGeom (by linarith : (0 : ℝ) ≤ 1 + 4 * u)
    linarith
  have hL1 : (F.map w).sum ≤ 8 / 10 ^ 5 := by
    have h1 : (1 + 4 * u) * (4 * Real.exp (-11)) ≤ 11 / 10 * (4 * (17 / 10 ^ 6)) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
    linarith
  have hL0 : 0 ≤ (F.map w).sum := by
    apply lsum_nonneg
    intro k _
    exact hw0 k
  have hwB : ∀ k ∈ c, |t k| ≤ (1 + u) * B * w k + η := by
    intro k hk
    rw [ht k]
    have hx : |w k * f k| ≤ w k * B := by
      rw [abs_mul, abs_of_nonneg (hw0 k)]
      exact mul_le_mul_of_nonneg_left (hB k hk) (hw0 k)
    have hwB1 := mul_le_mul_of_nonneg_right (hw1 k hk) hB0
    have h1 := hfl.bound hu hx (by linarith : w k * B ≤ M)
    linarith [h1, hwB1]
  have hsplit_t : (c.map t).sum = t j + (F.map t).sum := by
    rw [hFdef]
    exact sum_split t j c hnd hj
  have htj : |t j - f j| ≤ u * B + η := by
    rw [ht j, hwj, one_mul]
    exact hfl.abs hu (hB j hj) hBM'
  have htF : |(F.map t).sum| ≤ (1 + u) * B * (F.map w).sum + (F.length : ℝ) * η :=
    abs_sum_le_aff F t w ((1 + u) * B) η (fun k hk => hwB k (hF k hk).1)
  generalize hLg : (F.map w).sum = L at hS1 hL1 hL0 htF
  -- denominator
  have hAbs1 : ((c.map w).map (fun a => |a|)).sum = (c.map w).sum :=
    abs_sum_eq _ (fun a ha => by
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha
      exact hw0 k)
  have hZe := hR u η M fl hfl hu hη (c.map w) 0
    (by rw [List.length_map]; exact hum)
    (by
      rw [List.length_map, hAbs1, hS1]
      simp only [abs_zero]
      linarith)
  rw [List.length_map, hAbs1, hS1] at hZe
  simp only [abs_zero, zero_add] at hZe
  have hZ1 : |rsum fl (c.map w) 0 - 1| ≤ 4 / 1000 := by
    have h1 := mul_le_mul_of_nonneg_right hum (show (0 : ℝ) ≤ 1 + L by linarith)
    have h2 := abs_le.mp hZe
    rw [abs_le]
    constructor <;> linarith [h1, h2.1, h2.2]
  -- numerator
  have hP : (1 + u) * (1 + L) ≤ 10001 / 10000 := by
    have huL : u * L ≤ 1 / 10 ^ 6 * (8 / 10 ^ 5) := mul_le_mul hu6 hL1 hL0 (by norm_num)
    linarith [huL]
  have hTabs : ((c.map t).map (fun a => |a|)).sum ≤ 10001 / 10000 * B + E := by
    have e1 : (c.map t).map (fun a => |a|) = c.map (fun k => |t k|) := by
      rw [List.map_map]; rfl
    rw [e1]
    have h1 := sum_le_aff c (fun k => |t k|) w ((1 + u) * B) η hwB
    rw [hS1] at h1
    have h2 := mul_le_mul_of_nonneg_left hP hB0
    linarith [h1, h2, hmη]
  have hA0 : 0 ≤ ((c.map t).map (fun a => |a|)).sum :=
    lsum_nonneg _ _ (fun k _ => abs_nonneg k)
  have hNe := hR u η M fl hfl hu hη (c.map t) 0
    (by rw [List.length_map]; exact hum)
    (by
      rw [List.length_map]
      simp only [abs_zero]
      linarith)
  rw [List.length_map] at hNe
  simp only [abs_zero, zero_add] at hNe
  have hs : |(c.map t).sum - f j| ≤ (u * B + η) + ((1 + u) * B * L + E) := by
    have e : (c.map t).sum - f j = (t j - f j) + (F.map t).sum := by
      rw [hsplit_t]; ring
    rw [e]
    have h3 := abs_add_le (t j - f j) ((F.map t).sum)
    linarith
  have hAL : (1 + u) * B * L ≤ 9 / 10 ^ 5 * B := by
    have huL : u * L ≤ 1 / 10 ^ 6 * (8 / 10 ^ 5) := mul_le_mul hu6 hL1 hL0 (by norm_num)
    have h : (1 + u) * L ≤ 9 / 10 ^ 5 := by linarith [huL]
    have := mul_le_mul_of_nonneg_right h hB0
    linarith [this]
  have huB : u * B ≤ 1 / 10 ^ 6 * B := mul_le_mul_of_nonneg_right hu6 hB0
  have h4 := mul_le_mul_of_nonneg_right hum hA0
  have h3 := abs_sub_le (rsum fl (c.map t) 0) ((c.map t).sum) (f j)
  have hNf : |rsum fl (c.map t) 0 - f j| ≤ 4 / 1000 * B + 5 * E := by
    linarith [h3, hNe, h4, hTabs, hs, hmη, hAL, huB, hη1]
  have hdiv := div_step (rsum fl (c.map t) 0) (rsum fl (c.map w) 0) (f j) B (5 * E)
    hZ1 hNf (hB j hj) hB0 (by linarith)
  have hd1 := abs_le.mp hdiv
  have hf1 := abs_le.mp (hB j hj)
  have hxB : |rsum fl (c.map t) 0 / rsum fl (c.map w) 0| ≤ 11 / 10 * B + 10 * E := by
    rw [abs_le]
    constructor <;> linarith [hd1.1, hd1.2, hf1.1, hf1.2]
  have hnear := hfl.near hu hdiv hxB (by linarith)
  have hu1 := mul_le_mul_of_nonneg_right hu6 hE0.le
  refine ⟨by linarith [hnear, huB, hu1, hη1, hE90], hfl.idem _ (by linarith)⟩

end Lane4.Case
