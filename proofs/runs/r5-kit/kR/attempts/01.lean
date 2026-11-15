set_option linter.unusedVariables false

namespace Lane4.Case
open Lane4.RSeq

theorem mem_of_le (m e : ℤ) (hm : |m| ≤ 2 ^ 24) : (m : ℝ) * (2 : ℝ) ^ e ∈ FLX := by
  rcases lt_or_eq_of_le hm with h | h
  · exact ⟨m, e, h, rfl⟩
  · rcases abs_choice m with h1 | h1
    · rw [h1] at h
      refine ⟨2 ^ 23, e + 1, abs_lt.mpr ⟨by norm_num, by norm_num⟩, ?_⟩
      rw [h]
      push_cast
      rw [zpow_add_one₀ (by norm_num)]
      ring
    · have h' : m = -2 ^ 24 := by linarith
      refine ⟨-2 ^ 23, e + 1, abs_lt.mpr ⟨by norm_num, by norm_num⟩, ?_⟩
      rw [h']
      push_cast
      rw [zpow_add_one₀ (by norm_num)]
      ring

theorem zero_mem : (0 : ℝ) ∈ FLX := ⟨0, 0, by norm_num, by simp⟩

theorem neg_mem {g : ℝ} (hg : g ∈ FLX) : -g ∈ FLX := by
  obtain ⟨m, e, hm, rfl⟩ := hg
  refine ⟨-m, e, by rw [abs_neg]; exact hm, ?_⟩
  push_cast
  ring

theorem fl_fix {fl : ℝ → ℝ} (h : ∀ x, fl x ∈ FLX ∧ ∀ g ∈ FLX, |fl x - x| ≤ |g - x|)
    {g : ℝ} (hg : g ∈ FLX) : fl g = g := by
  have h0 : |fl g - g| ≤ 0 := by simpa using (h g).2 g hg
  have := abs_nonpos_iff.mp h0
  linarith

theorem nat_mem (k : ℕ) (hk : k ≤ 16777216) : ((k : ℕ) : ℝ) ∈ FLX := by
  have h' : (k : ℤ) ≤ 16777216 := by exact_mod_cast hk
  have := mem_of_le (k : ℤ) 0 (by rw [abs_of_nonneg (by positivity)]; linarith)
  simpa using this

theorem near (x : ℝ) : ∃ g ∈ FLX, |g - x| ≤ 1 / 2 ^ 24 * |x| := by
  by_cases hx : x = 0
  · exact ⟨0, zero_mem, by rw [hx]; simp⟩
  have hpos : 0 < |x| := abs_pos.mpr hx
  obtain ⟨L, hL1, hL2⟩ : ∃ L : ℤ, (2 : ℝ) ^ L ≤ |x| ∧ |x| < (2 : ℝ) ^ (L + 1) := by
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hpos (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, hn1, hn2⟩
  obtain ⟨e, he⟩ : ∃ e : ℤ, e = L - 23 := ⟨_, rfl⟩
  have hc : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) e
  have hlt : |x| < (2 : ℝ) ^ (e + 24) := by
    calc |x| < (2 : ℝ) ^ (L + 1) := hL2
      _ ≤ (2 : ℝ) ^ (e + 24) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hle : (2 : ℝ) ^ e / 2 ≤ 1 / 2 ^ 24 * |x| := by
    have e3 : (2 : ℝ) ^ e / 2 = 2 ^ L / 2 ^ 24 := by
      rw [he, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num <;> ring
    have e4 : (2 : ℝ) ^ L / 2 ^ 24 ≤ 1 / 2 ^ 24 * |x| := by
      calc (2 : ℝ) ^ L / 2 ^ 24 = 1 / 2 ^ 24 * 2 ^ L := by ring
        _ ≤ 1 / 2 ^ 24 * |x| := by gcongr
    rw [e3]
    exact e4
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = x / 2 ^ e := ⟨_, rfl⟩
  have hx' : x = t * 2 ^ e := by rw [ht]; field_simp
  have habs : |t| < 2 ^ 24 := by
    rw [ht, abs_div, abs_of_pos hc, div_lt_iff₀ hc]
    calc |x| < (2 : ℝ) ^ (e + 24) := hlt
      _ = 2 ^ 24 * 2 ^ e := by
        rw [zpow_add₀ (by norm_num), mul_comm]
        norm_num
  have hr : |t - round t| ≤ 1 / 2 := abs_sub_round t
  obtain ⟨hr1, hr2⟩ := abs_le.mp hr
  obtain ⟨ha1, ha2⟩ := abs_lt.mp habs
  have hm : |round t| ≤ 2 ^ 24 := by
    have h3 : ((round t : ℤ) : ℝ) < 2 ^ 24 + 1 := by linarith
    have h4 : -((2 : ℝ) ^ 24 + 1) < ((round t : ℤ) : ℝ) := by linarith
    have h5 : round t < 2 ^ 24 + 1 := by exact_mod_cast h3
    have h6 : -(2 ^ 24 + 1) < round t := by exact_mod_cast h4
    exact abs_le.mpr ⟨by omega, by omega⟩
  refine ⟨(round t : ℝ) * 2 ^ e, mem_of_le _ _ hm, ?_⟩
  have h7 : (round t : ℝ) * 2 ^ e - x = (round t - t) * 2 ^ e := by
    rw [sub_mul, ← hx']
  calc |(round t : ℝ) * 2 ^ e - x| = |(round t : ℝ) - t| * 2 ^ e := by
        rw [h7, abs_mul, abs_of_pos hc]
    _ ≤ 1 / 2 * 2 ^ e := by
        apply mul_le_mul_of_nonneg_right _ hc.le
        rw [abs_sub_comm]; exact hr
    _ = 2 ^ e / 2 := by ring
    _ ≤ _ := hle

theorem rnx_rounding : RnxRounding := by
  intro fl h
  unfold IsRNX at h
  obtain ⟨hnear, hneg⟩ := h
  refine ⟨?_, ?_, ?_, hneg, ?_⟩
  · intro x
    obtain ⟨g, hg, hgx⟩ := near x
    exact le_trans ((hnear x).2 g hg) hgx
  · intro x y hxy
    by_contra hlt
    push_neg at hlt
    have h1 := (hnear x).2 (fl y) (hnear y).1
    have h2 := (hnear y).2 (fl x) (hnear x).1
    rcases eq_or_lt_of_le hxy with rfl | hxy'
    · exact lt_irrefl _ hlt
    · rcases abs_cases (fl x - x) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      rcases abs_cases (fl y - x) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
      rcases abs_cases (fl y - y) with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
      rcases abs_cases (fl x - y) with ⟨d1, d2⟩ | ⟨d1, d2⟩ <;>
      linarith
  · intro x
    exact fl_fix hnear (hnear x).1
  · intro k hk
    exact fl_fix hnear (nat_mem k hk)

theorem nearest_pos (x : ℝ) (hx : 0 < x) :
    ∃ g ∈ FLX, ∀ g' ∈ FLX, |g - x| ≤ |g' - x| := by
  obtain ⟨L, hL1, hL2⟩ : ∃ L : ℤ, (2 : ℝ) ^ L ≤ x ∧ x < (2 : ℝ) ^ (L + 1) := by
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hx (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, hn1, hn2⟩
  obtain ⟨e, he⟩ : ∃ e : ℤ, e = L - 23 := ⟨_, rfl⟩
  have hc : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) e
  have hL23 : (2 : ℝ) ^ L = 2 ^ 23 * 2 ^ e := by
    have h1 : L = e + 23 := by omega
    have h23 : (2 : ℝ) ^ (23 : ℤ) = 2 ^ 23 := by norm_num
    rw [h1, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), h23]
    ring
  have hL24 : (2 : ℝ) ^ (L + 1) = 2 ^ 24 * 2 ^ e := by
    have h1 : L + 1 = e + 24 := by omega
    have h24 : (2 : ℝ) ^ (24 : ℤ) = 2 ^ 24 := by norm_num
    rw [h1, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), h24]
    ring
  have hhalf : (2 : ℝ) ^ e = 2 ^ (e - 1) * 2 := by
    have := zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0) (e - 1)
    rw [show e - 1 + 1 = e by ring] at this
    exact this
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = x / 2 ^ e := ⟨_, rfl⟩
  have ht1 : 2 ^ 23 ≤ t := by
    rw [ht, le_div_iff₀ hc]; linarith
  have ht2 : t < 2 ^ 24 := by
    rw [ht, div_lt_iff₀ hc]; linarith
  have hxt : x = t * 2 ^ e := by rw [ht]; field_simp
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = ⌊t⌋ := ⟨_, rfl⟩
  have hn1 : (n : ℝ) ≤ t := by rw [hn]; exact Int.floor_le t
  have hn2 : t < (n : ℝ) + 1 := by rw [hn]; exact Int.lt_floor_add_one t
  have hn3 : (2 : ℝ) ^ 23 ≤ n := by
    have : ((2 ^ 23 : ℤ) : ℝ) ≤ t := by push_cast; exact ht1
    have h' := Int.le_floor.mpr this
    rw [← hn] at h'
    have : ((2 ^ 23 : ℤ) : ℝ) ≤ n := Int.cast_le.mpr h'
    push_cast at this
    exact this
  have hn4 : (n : ℝ) < 2 ^ 24 := lt_of_le_of_lt hn1 ht2
  have hnz : (0 : ℤ) ≤ n := by
    have : (0 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hn5 : n < 2 ^ 24 := by exact_mod_cast hn4
  have ha : (n : ℝ) * 2 ^ e ∈ FLX :=
    mem_of_le n e (by rw [abs_of_nonneg hnz]; omega)
  have hb : ((n : ℝ) + 1) * 2 ^ e ∈ FLX := by
    have := mem_of_le (n + 1) e (by rw [abs_of_nonneg (by omega)]; omega)
    push_cast at this
    exact this
  have hax : (n : ℝ) * 2 ^ e ≤ x := by rw [hxt]; exact mul_le_mul_of_nonneg_right hn1 hc.le
  have hbx : x ≤ ((n : ℝ) + 1) * 2 ^ e := by
    rw [hxt]; exact mul_le_mul_of_nonneg_right hn2.le hc.le
  have hapos : (2 : ℝ) ^ 23 * 2 ^ e ≤ (n : ℝ) * 2 ^ e :=
    mul_le_mul_of_nonneg_right hn3 hc.le
  have key : ∀ g' ∈ FLX, g' ≤ (n : ℝ) * 2 ^ e ∨ ((n : ℝ) + 1) * 2 ^ e ≤ g' := by
    intro g' hg'
    by_contra hcon
    push_neg at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    obtain ⟨m, e', hm, rfl⟩ := hg'
    have hmr : (m : ℝ) < 2 ^ 24 := by
      have := (abs_lt.mp hm).2
      exact_mod_cast this
    have he' : e ≤ e' := by
      by_contra hlt
      push_neg at hlt
      have h1 : (2 : ℝ) ^ e' ≤ 2 ^ (e - 1) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h2 : (0 : ℝ) < 2 ^ e' := zpow_pos (by norm_num) e'
      have h3 : (m : ℝ) * 2 ^ e' < 2 ^ 24 * 2 ^ e' := mul_lt_mul_of_pos_right hmr h2
      have h4 : (2 : ℝ) ^ 24 * 2 ^ e' ≤ 2 ^ 24 * 2 ^ (e - 1) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h5 : (2 : ℝ) ^ 24 * 2 ^ (e - 1) = 2 ^ 23 * 2 ^ e := by
        rw [hhalf]; ring
      linarith
    obtain ⟨k, hk⟩ : ∃ k : ℕ, e' = e + k := ⟨(e' - e).toNat, by omega⟩
    have hmn : (m : ℝ) * 2 ^ e' = ((m * 2 ^ k : ℤ) : ℝ) * 2 ^ e := by
      rw [hk, zpow_add₀ (by norm_num), zpow_natCast]
      push_cast
      ring
    rw [hmn] at hc1 hc2
    have i1 : (n : ℝ) < ((m * 2 ^ k : ℤ) : ℝ) := lt_of_mul_lt_mul_right hc1 hc.le
    have i2 : ((m * 2 ^ k : ℤ) : ℝ) < (n : ℝ) + 1 := lt_of_mul_lt_mul_right hc2 hc.le
    have j1 : n < m * 2 ^ k := by exact_mod_cast i1
    have j2 : m * 2 ^ k < n + 1 := by exact_mod_cast (by push_cast at i2 ⊢; exact i2 : ((m * 2 ^ k : ℤ) : ℝ) < ((n + 1 : ℤ) : ℝ))
    omega
  rcases le_total (x - (n : ℝ) * 2 ^ e) (((n : ℝ) + 1) * 2 ^ e - x) with hh | hh
  · refine ⟨(n : ℝ) * 2 ^ e, ha, fun g' hg' => ?_⟩
    have e1 : |(n : ℝ) * 2 ^ e - x| = x - (n : ℝ) * 2 ^ e := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [e1]
    rcases key g' hg' with k1 | k1
    · have := le_abs_self (x - g')
      rw [abs_sub_comm] at this
      linarith
    · have := le_abs_self (g' - x)
      linarith
  · refine ⟨((n : ℝ) + 1) * 2 ^ e, hb, fun g' hg' => ?_⟩
    have e1 : |((n : ℝ) + 1) * 2 ^ e - x| = ((n : ℝ) + 1) * 2 ^ e - x := by
      rw [abs_of_nonneg (by linarith)]
    rw [e1]
    rcases key g' hg' with k1 | k1
    · have := le_abs_self (x - g')
      rw [abs_sub_comm] at this
      linarith
    · have := le_abs_self (g' - x)
      linarith

theorem nearest_all (x : ℝ) : ∃ g ∈ FLX, ∀ g' ∈ FLX, |g - x| ≤ |g' - x| := by
  rcases lt_trichotomy x 0 with h | h | h
  · obtain ⟨g, hg, hmin⟩ := nearest_pos (-x) (by linarith)
    refine ⟨-g, neg_mem hg, fun g' hg' => ?_⟩
    have a1 := hmin (-g') (neg_mem hg')
    have b1 : |-g - x| = |g - -x| := by rw [← abs_neg]; congr 1; ring
    have b2 : |g' - x| = |-g' - -x| := by rw [← abs_neg]; congr 1; ring
    rw [b1, b2]
    exact a1
  · exact ⟨0, zero_mem, fun g' hg' => by rw [h]; simp⟩
  · exact nearest_pos x h

theorem not_mem : ¬ ((16777217 : ℝ) ∈ FLX) := by
  rintro ⟨m, e, hm, h⟩
  have hm1 := abs_lt.mp hm
  have hm2 : m < 2 ^ 24 := hm1.2
  rcases le_or_gt 0 e with he | he
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, e = k := ⟨e.toNat, by omega⟩
    rw [hk, zpow_natCast] at h
    have h2 : (16777217 : ℤ) = m * 2 ^ k := by exact_mod_cast h
    rcases k with _ | j
    · simp at h2
      omega
    · have h3 : (16777217 : ℤ) = 2 * (m * 2 ^ j) := by rw [h2, pow_succ]; ring
      obtain ⟨q, hq⟩ : ∃ q : ℤ, q = m * 2 ^ j := ⟨_, rfl⟩
      rw [← hq] at h3
      omega
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, e = -(k : ℤ) := ⟨(-e).toNat, by omega⟩
    rw [hk, zpow_neg, zpow_natCast] at h
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    have hp1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have h4 : (m : ℝ) = 16777217 * 2 ^ k := by
      rw [h]; field_simp
    have h5 : (m : ℝ) < 2 ^ 24 := by exact_mod_cast hm2
    nlinarith

theorem rnx_exists : RnxExists := by
  choose c hc using nearest_all
  refine ⟨fun x => if 0 < x then c x else if x = 0 then 0 else -c (-x), ⟨?_, ?_⟩, ?_⟩
  · intro x
    by_cases h1 : 0 < x
    · simp only [h1, if_true]
      exact hc x
    · by_cases h2 : x = 0
      · simp only [h1, h2, if_false, if_true]
        exact ⟨zero_mem, fun g hg => by rw [h2]; simp⟩
      · simp only [h1, h2, if_false]
        refine ⟨neg_mem (hc (-x)).1, fun g hg => ?_⟩
        have a1 := (hc (-x)).2 (-g) (neg_mem hg)
        have b1 : |-c (-x) - x| = |c (-x) - -x| := by rw [← abs_neg]; congr 1; ring
        have b2 : |g - x| = |-g - -x| := by rw [← abs_neg]; congr 1; ring
        rw [b1, b2]
        exact a1
  · intro x
    by_cases h1 : 0 < x
    · have h2 : ¬ (0 < -x) := by linarith
      have h3 : ¬ (-x = 0) := by linarith
      simp only [h1, h2, h3, if_true, if_false, neg_neg]
    · by_cases h2 : x = 0
      · simp [h2]
      · have h3 : 0 < -x := by
          rcases lt_or_gt_of_ne h2 with h | h
          · linarith
          · exact absurd h h1
        simp only [h1, h2, h3, if_true, if_false]
  · have hpos : (0 : ℝ) < 16777217 := by norm_num
    simp only [hpos, if_true]
    intro heq
    exact not_mem (heq ▸ (hc 16777217).1)

end Lane4.Case
