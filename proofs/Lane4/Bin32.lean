/-
Lane 4, rung 5: binary32 arithmetic satisfies the rounding model of RSoft.lean.

Assembled by tools/r5_assemble.py from kit case runs/r5-kit/kC2 (proved by a Sonnet doctor,
checked by the lane's checker). Not needed by doctors.

`F32U` is the binary32 grid with subnormals (`m * 2^e`, `|m| < 2^24`, `e ≥ -149`); the
finite binary32 numbers are its members of magnitude at most `maxF`. `IsRN rn` says `rn`
rounds every real to a nearest grid point (any tie rule; round-to-nearest-even is one).
`bin32_rnd`: any `fl` that agrees with such an `rn` on `|x| ≤ maxF` satisfies
`Rnd (1/2^24) (1/2^150) maxF fl`. That is IEEE 754 binary32 addition, subtraction,
multiplication and division of finite values with finite results (each returns the
rounding of the exact result); signed zeros are identified and the bit-level encoding is
not modelled. The model assumes nothing outside `|x| ≤ maxF`, so a theorem proved from
`Rnd` also shows that no exact result exceeds `maxF` (no overflow).
-/
import Lane4.RSoft

namespace Lane4.Bin32
open Lane4.RSoft


/-- The binary32 grid with subnormals and with exponents unbounded above:
`m * 2^e` with an integer significand `|m| < 2^24` and an integer exponent `e ≥ -149`.
(Finite binary32 numbers are exactly the members of absolute value at most
`(2^24 - 1) * 2^104`.) -/
def F32U : Set ℝ := {x | ∃ m e : ℤ, |m| < 2 ^ 24 ∧ -149 ≤ e ∧ x = (m : ℝ) * (2 : ℝ) ^ e}

/-- `fl` rounds every real to a nearest grid point (any tie rule). -/
def IsRN (fl : ℝ → ℝ) : Prop := ∀ x, fl x ∈ F32U ∧ ∀ g ∈ F32U, |fl x - x| ≤ |g - x|

/-- The largest finite binary32 number. -/
noncomputable def maxF : ℝ := (2 ^ 24 - 1) * 2 ^ 104

/-- Binary32 arithmetic satisfies the rounding model of RSoft.lean on the finite range:
any `fl` that agrees, for `|x| ≤ maxF`, with a round-to-nearest `rn` onto the grid.
(Nothing is assumed about `fl` outside the range.) -/
def RnRnd : Prop :=
  ∀ rn, IsRN rn → ∀ fl : ℝ → ℝ, (∀ x, |x| ≤ maxF → fl x = rn x) →
    Rnd (1 / 2 ^ 24) (1 / 2 ^ 150) maxF fl

/-- Such a rounding function exists. -/
def RnExists : Prop := ∃ fl, IsRN fl

set_option linter.unusedVariables false


theorem mem_of_le (m e : ℤ) (hm : |m| ≤ 2 ^ 24) (he : -149 ≤ e) :
    (m : ℝ) * (2 : ℝ) ^ e ∈ F32U := by
  rcases lt_or_eq_of_le hm with h | h
  · exact ⟨m, e, h, he, rfl⟩
  · rcases abs_choice m with h1 | h1
    · rw [h1] at h
      refine ⟨2 ^ 23, e + 1, abs_lt.mpr ⟨by norm_num, by norm_num⟩, by omega, ?_⟩
      rw [h]
      push_cast
      rw [zpow_add_one₀ (by norm_num)]
      ring
    · have h' : m = -2 ^ 24 := by linarith
      refine ⟨-2 ^ 23, e + 1, abs_lt.mpr ⟨by norm_num, by norm_num⟩, by omega, ?_⟩
      rw [h']
      push_cast
      rw [zpow_add_one₀ (by norm_num)]
      ring

theorem fl_fix {fl : ℝ → ℝ} (h : IsRN fl) {g : ℝ} (hg : g ∈ F32U) : fl g = g := by
  have h0 : |fl g - g| ≤ 0 := by simpa using (h g).2 g hg
  have := abs_nonpos_iff.mp h0
  linarith

theorem nat_mem (k : ℕ) (hk : k ≤ 16777216) : ((k : ℕ) : ℝ) ∈ F32U := by
  have h' : (k : ℤ) ≤ 16777216 := by exact_mod_cast hk
  have := mem_of_le (k : ℤ) 0 (by rw [abs_of_nonneg (by positivity)]; linarith) (by norm_num)
  simpa using this

theorem near (x : ℝ) : ∃ g ∈ F32U, |g - x| ≤ 1 / 2 ^ 24 * |x| + 1 / 2 ^ 150 := by
  have key : ∃ e : ℤ, -149 ≤ e ∧ |x| < (2 : ℝ) ^ (e + 24) ∧
      (2 : ℝ) ^ e / 2 ≤ 1 / 2 ^ 24 * |x| + 1 / 2 ^ 150 := by
    by_cases hx : x = 0
    · refine ⟨-149, le_refl _, ?_, ?_⟩
      · rw [hx, abs_zero]; positivity
      · rw [hx, abs_zero]; norm_num
    · have hpos : 0 < |x| := abs_pos.mpr hx
      obtain ⟨L, hL1, hL2⟩ : ∃ L : ℤ, (2 : ℝ) ^ L ≤ |x| ∧ |x| < (2 : ℝ) ^ (L + 1) :=
        by
          obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hpos (by norm_num : (1 : ℝ) < 2)
          exact ⟨n, hn1, hn2⟩
      refine ⟨max (L - 23) (-149), le_max_right _ _, ?_, ?_⟩
      · calc |x| < (2 : ℝ) ^ (L + 1) := hL2
          _ ≤ (2 : ℝ) ^ (max (L - 23) (-149) + 24) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
      · rcases le_total (L - 23) (-149) with h | h
        · rw [max_eq_right h]
          have : (0 : ℝ) ≤ 1 / 2 ^ 24 * |x| := by positivity
          have e2 : (2 : ℝ) ^ (-149 : ℤ) / 2 = 1 / 2 ^ 150 := by norm_num
          linarith
        · rw [max_eq_left h]
          have e3 : (2 : ℝ) ^ (L - 23) / 2 = 2 ^ L / 2 ^ 24 := by
            rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
            norm_num <;> ring
          have e4 : (2 : ℝ) ^ L / 2 ^ 24 ≤ 1 / 2 ^ 24 * |x| := by
            calc (2 : ℝ) ^ L / 2 ^ 24 = 1 / 2 ^ 24 * 2 ^ L := by ring
              _ ≤ 1 / 2 ^ 24 * |x| := by gcongr
          have : (0 : ℝ) < 1 / 2 ^ 150 := by positivity
          rw [e3]
          linarith
  obtain ⟨e, he, hlt, hle⟩ := key
  have hc : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) e
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = x / 2 ^ e := ⟨_, rfl⟩
  have hx : x = t * 2 ^ e := by rw [ht]; field_simp
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
  refine ⟨(round t : ℝ) * 2 ^ e, mem_of_le _ _ hm he, ?_⟩
  have h7 : (round t : ℝ) * 2 ^ e - x = (round t - t) * 2 ^ e := by
    rw [sub_mul, ← hx]
  calc |(round t : ℝ) * 2 ^ e - x| = |(round t : ℝ) - t| * 2 ^ e := by
        rw [h7, abs_mul, abs_of_pos hc]
    _ ≤ 1 / 2 * 2 ^ e := by
        apply mul_le_mul_of_nonneg_right _ hc.le
        rw [abs_sub_comm]; exact hr
    _ = 2 ^ e / 2 := by ring
    _ ≤ _ := hle

theorem rn_props (fl : ℝ → ℝ) (h : IsRN fl) :
    (∀ x, |fl x - x| ≤ 1 / 2 ^ 24 * |x| + 1 / 2 ^ 150) ∧
    (∀ x y, x ≤ y → fl x ≤ fl y) ∧ (∀ x, fl (fl x) = fl x) ∧
    (∀ k : ℕ, k ≤ 16777216 → fl (k : ℝ) = (k : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨g, hg, hgx⟩ := near x
    exact le_trans ((h x).2 g hg) hgx
  · intro x y hxy
    by_contra hlt
    push_neg at hlt
    have h1 := (h x).2 (fl y) (h y).1
    have h2 := (h y).2 (fl x) (h x).1
    rcases eq_or_lt_of_le hxy with rfl | hxy'
    · exact lt_irrefl _ hlt
    · rcases abs_cases (fl x - x) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      rcases abs_cases (fl y - x) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
      rcases abs_cases (fl y - y) with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
      rcases abs_cases (fl x - y) with ⟨d1, d2⟩ | ⟨d1, d2⟩ <;>
      linarith
  · intro x
    exact fl_fix h (h x).1
  · intro k hk
    exact fl_fix h (nat_mem k hk)

theorem rn_range (fl : ℝ → ℝ) (h : IsRN fl) (x : ℝ) (hx : |x| ≤ maxF) : |fl x| ≤ maxF := by
  have hM : maxF ∈ F32U :=
    ⟨2 ^ 24 - 1, 104, abs_lt.mpr ⟨by norm_num, by norm_num⟩, by norm_num, by
      unfold maxF; norm_num⟩
  have hM' : -maxF ∈ F32U :=
    ⟨-(2 ^ 24 - 1), 104, abs_lt.mpr ⟨by norm_num, by norm_num⟩, by norm_num, by
      unfold maxF; norm_num⟩
  have hr := (rn_props fl h).2.1
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  have a := hr (-maxF) x hx1
  have b := hr x maxF hx2
  rw [fl_fix h hM'] at a
  rw [fl_fix h hM] at b
  exact abs_le.mpr ⟨a, b⟩

theorem nearest (x : ℝ) : ∃ g ∈ F32U, ∀ g' ∈ F32U, |g - x| ≤ |g' - x| := by
  obtain ⟨g0, hg0, hb0⟩ := near x
  obtain ⟨d0, hd0⟩ : ∃ d : ℝ, d = |g0 - x| := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (2 : ℝ) ^ (-149 : ℤ) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; exact zpow_pos (by norm_num) _
  have hfin : {g : ℝ | g ∈ F32U ∧ |g - x| ≤ d0}.Finite := by
    apply Set.Finite.subset (Set.Finite.image (fun n : ℤ => (n : ℝ) * c)
      (Set.finite_Icc ⌊(x - d0) / c⌋ ⌈(x + d0) / c⌉))
    rintro g ⟨⟨m, e, hm, he, rfl⟩, hd⟩
    obtain ⟨k, hk⟩ : ∃ k : ℕ, e = -149 + k := ⟨(e + 149).toNat, by omega⟩
    have hn : (m : ℝ) * 2 ^ e = ((m * 2 ^ k : ℤ) : ℝ) * c := by
      rw [hk, zpow_add₀ (by norm_num), zpow_natCast, hcdef]
      push_cast
      ring
    have hd' : |((m * 2 ^ k : ℤ) : ℝ) * c - x| ≤ d0 := by rw [← hn]; exact hd
    obtain ⟨hd1, hd2⟩ := abs_le.mp hd'
    refine ⟨m * 2 ^ k, ⟨?_, ?_⟩, hn.symm⟩
    · have : (x - d0) / c ≤ ((m * 2 ^ k : ℤ) : ℝ) := by
        rw [div_le_iff₀ hc]; linarith
      exact Int.cast_le.mp ((Int.floor_le _).trans this)
    · have : ((m * 2 ^ k : ℤ) : ℝ) ≤ (x + d0) / c := by
        rw [le_div_iff₀ hc]; linarith
      exact Int.cast_le.mp (this.trans (Int.le_ceil _))
  obtain ⟨g1, ⟨hg1, hg1d⟩, hmin⟩ :=
    Set.exists_min_image {g : ℝ | g ∈ F32U ∧ |g - x| ≤ d0} (fun g => |g - x|) hfin
      ⟨g0, hg0, by rw [hd0]⟩
  refine ⟨g1, hg1, fun g' hg' => ?_⟩
  by_cases hh : |g' - x| ≤ d0
  · exact hmin g' ⟨hg', hh⟩
  · push_neg at hh
    exact hg1d.trans hh.le

theorem rn_rnd : RnRnd := by
  intro rn h fl hfl
  obtain ⟨p1, p2, p3, p4⟩ := rn_props rn h
  have hM0 : (0 : ℝ) ≤ maxF := by unfold maxF; norm_num
  refine ⟨hM0, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hfl x hx]; exact p1 x
  · intro x y hx hy hxy
    rw [hfl x hx, hfl y hy]; exact p2 x y hxy
  · intro x hx
    have h1 := rn_range rn h x hx
    rw [hfl x hx, hfl (rn x) h1]; exact p3 x
  · intro k hk
    have hk' : |((k : ℕ) : ℝ)| ≤ maxF := by
      rw [abs_of_nonneg (by positivity)]
      have : (k : ℝ) ≤ 16777216 := by exact_mod_cast hk
      unfold maxF; linarith
    rw [hfl _ hk']; exact p4 k hk

theorem rn_exists : RnExists := by
  refine ⟨fun x => Classical.choose (nearest x), fun x => ?_⟩
  exact Classical.choose_spec (nearest x)

/-- Binary32 satisfies the rounding model on the finite range. -/
theorem bin32_rnd {rn fl : ℝ → ℝ} (h : IsRN rn) (hfl : ∀ x, |x| ≤ maxF → fl x = rn x) :
    Rnd (1 / 2 ^ 24) (1 / 2 ^ 150) maxF fl := rn_rnd rn h fl hfl

/-- The range of the model covers the statement's range condition for up to 2^16
positions: `2^40 * n^2 ≤ maxF` whenever `n ≤ 65536`. -/
theorem range_ok {n : ℕ} (hn : n ≤ 65536) : (2 : ℝ) ^ 40 * (n : ℝ) ^ 2 ≤ maxF := by
  have h1 : (n : ℝ) ≤ 65536 := by exact_mod_cast hn
  have h2 : (n : ℝ) ^ 2 ≤ 65536 ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg n) h1 2
  unfold maxF
  nlinarith [h2]

end Lane4.Bin32
