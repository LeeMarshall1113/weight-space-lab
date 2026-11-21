set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace Lane4.Case
open Lane4.Cert Lane4.Cert8

theorem dn_le (b : ℕ) (x : ℚ) : dnB b x ≤ x := by
  unfold dnB
  have hd : (0:ℤ) < (x.den : ℤ) := by exact_mod_cast x.den_pos
  have h1 := Int.ediv_mul_le (x.num * 2 ^ b) hd.ne'
  generalize hq : (x.num * 2 ^ b / (x.den : ℤ) : ℤ) = q at h1 ⊢
  have h2 : ((q * (x.den : ℤ) : ℤ) : ℚ) ≤ ((x.num * 2 ^ b : ℤ) : ℚ) := by exact_mod_cast h1
  push_cast at h2
  have hx : x * (x.den : ℚ) = (x.num : ℚ) := by exact_mod_cast Rat.mul_den_eq_num x
  have hdq : (0:ℚ) < (x.den : ℚ) := by exact_mod_cast x.den_pos
  rw [← hx] at h2
  rw [div_le_iff₀ (by positivity)]
  apply le_of_mul_le_mul_right _ hdq
  linarith [h2]

theorem round_sound : RoundSound := by
  intro b x
  refine ⟨dn_le b x, ?_⟩
  unfold upB
  have := dn_le b (-x)
  linarith

theorem dn_nonneg (b : ℕ) (x : ℚ) (hx : 0 ≤ x) : 0 ≤ dnB b x := by
  unfold dnB
  have h1 : 0 ≤ x.num := Rat.num_nonneg.mpr hx
  have h2 : (0:ℤ) ≤ x.num * 2 ^ b := by positivity
  have h3 : (0:ℤ) ≤ x.num * 2 ^ b / (x.den : ℤ) := Int.ediv_nonneg h2 (by positivity)
  have h4 : (0:ℚ) ≤ ((x.num * 2 ^ b / (x.den : ℤ) : ℤ) : ℚ) := by exact_mod_cast h3
  positivity

theorem key_list (L : List ℕ) :
    (do let a ← L; pure (a : ℚ) : List ℚ) = L.map (fun k => (k : ℚ)) := by
  first
  | simp
  | (induction L with
     | nil => simp
     | cons a L ih => simp_all [List.flatMap_cons, pure, bind])

theorem fold_eq0 (y : ℚ) (n : ℕ) :
    ((List.range n).map (fun k => (k : ℚ))).foldl
      (fun p (k : ℚ) => (p.1 + p.2, p.2 * y / (k + 1))) ((0:ℚ), (1:ℚ))
      = (∑ k ∈ Finset.range n, y ^ k / (Nat.factorial k : ℚ), y ^ n / (Nat.factorial n : ℚ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [Finset.sum_range_succ]
    refine Prod.ext (by simp) ?_
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem fold_eq (y : ℚ) :
    expSeries y = (∑ k ∈ Finset.range 14, y ^ k / (Nat.factorial k : ℚ),
      y ^ 14 / (Nat.factorial 14 : ℚ)) := by
  unfold expSeries
  first
  | (rw [key_list]; exact fold_eq0 y 14)
  | (simp only [key_list]; exact fold_eq0 y 14)

theorem qabs_cast (T : ℚ) : ((qabs T : ℚ) : ℝ) = |(T : ℝ)| := by
  unfold qabs
  split_ifs with h
  · push_cast
    rw [abs_of_neg (by exact_mod_cast h)]
  · push_cast
    rw [abs_of_nonneg (by exact_mod_cast not_lt.mp h)]

theorem series_encl (y : ℚ) (h1 : -(15/16) ≤ y) (h2 : y ≤ 1) :
    ((expSeries y).1 : ℝ) - 3 * |((expSeries y).2 : ℝ)| ≤ Real.exp (y : ℝ) ∧
    Real.exp (y : ℝ) ≤ ((expSeries y).1 : ℝ) + 3 * |((expSeries y).2 : ℝ)| ∧
    |((expSeries y).2 : ℝ)| ≤ 1 / 87178291200 := by
  have e : expSeries y = (∑ k ∈ Finset.range 14, y ^ k / (Nat.factorial k : ℚ),
      y ^ 14 / (Nat.factorial 14 : ℚ)) := by
    exact fold_eq y
  have hS : ((∑ k ∈ Finset.range 14, y ^ k / (Nat.factorial k : ℚ) : ℚ) : ℝ)
      = ∑ k ∈ Finset.range 14, (y : ℝ) ^ k / (Nat.factorial k : ℝ) := by
    push_cast <;> rfl
  have hT : ((y ^ 14 / (Nat.factorial 14 : ℚ) : ℚ) : ℝ)
      = (y : ℝ) ^ 14 / (Nat.factorial 14 : ℝ) := by
    push_cast <;> rfl
  have a1 : (-(15/16) : ℝ) ≤ (y : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr h1
    push_cast at this
    linarith
  have a2 : (y : ℝ) ≤ 1 := by exact_mod_cast h2
  have hyr : |(y : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hb := Real.exp_bound hyr (n := 14) (by norm_num)
  have hc : (Nat.factorial 14 : ℝ) = 87178291200 := by norm_num [Nat.factorial]
  have hcpos : (0:ℝ) < (Nat.factorial 14 : ℝ) := by positivity
  have hp : 0 ≤ |(y : ℝ)| ^ 14 := by positivity
  have hp1 : |(y : ℝ)| ^ 14 ≤ 1 := pow_le_one₀ (abs_nonneg _) hyr
  have hTabs : |(y : ℝ) ^ 14 / (Nat.factorial 14 : ℝ)| = |(y : ℝ)| ^ 14 / (Nat.factorial 14 : ℝ) := by
    rw [abs_div, abs_pow, abs_of_pos hcpos]
  have hb2 : |Real.exp (y : ℝ) - ∑ m ∈ Finset.range 14, (y : ℝ) ^ m / (Nat.factorial m : ℝ)|
      ≤ 3 * (|(y : ℝ)| ^ 14 / (Nat.factorial 14 : ℝ)) := by
    refine hb.trans ?_
    rw [hc]
    norm_num <;> nlinarith [hp]
  rw [e]
  dsimp only
  rw [hS, hT, hTabs]
  rw [abs_le] at hb2
  rw [hc] at hb2 ⊢
  refine ⟨?_, ?_, ?_⟩
  · linarith [hb2.1, hb2.2]
  · linarith [hb2.1, hb2.2]
  · have : |(y : ℝ)| ^ 14 / 87178291200 ≤ 1 / 87178291200 := by
      apply div_le_div_of_nonneg_right hp1 (by norm_num)
    exact this

theorem sq_lo (n : ℕ) : ∀ (a : ℚ) (z : ℝ), 0 ≤ a → (a : ℝ) ≤ Real.exp z →
    ((sqN (dnB 70) n a : ℚ) : ℝ) ≤ Real.exp (2 ^ n * z) := by
  induction n with
  | zero => intro a z _ h; simpa [sqN] using h
  | succ n ih =>
    intro a z ha h
    rw [sqN]
    have ha' : (0:ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have h2 : ((dnB 70 (a * a) : ℚ) : ℝ) ≤ Real.exp (2 * z) := by
      calc ((dnB 70 (a * a) : ℚ) : ℝ) ≤ ((a * a : ℚ) : ℝ) := by exact_mod_cast dn_le 70 (a * a)
        _ = (a : ℝ) * a := by push_cast; ring
        _ ≤ Real.exp z * Real.exp z := mul_self_le_mul_self ha' h
        _ = Real.exp (2 * z) := by rw [← Real.exp_add]; congr 1; ring
    have := ih (dnB 70 (a * a)) (2 * z) (dn_nonneg 70 _ (mul_self_nonneg a)) h2
    have e : (2:ℝ) ^ (n + 1) * z = 2 ^ n * (2 * z) := by ring
    rw [e]
    exact this

theorem sq_hi (n : ℕ) : ∀ (a : ℚ) (z : ℝ), Real.exp z ≤ (a : ℝ) →
    Real.exp (2 ^ n * z) ≤ ((sqN (upB 70) n a : ℚ) : ℝ) := by
  induction n with
  | zero => intro a z h; simpa [sqN] using h
  | succ n ih =>
    intro a z h
    rw [sqN]
    have h2 : Real.exp (2 * z) ≤ ((upB 70 (a * a) : ℚ) : ℝ) := by
      calc Real.exp (2 * z) = Real.exp z * Real.exp z := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ (a : ℝ) * a := mul_self_le_mul_self (Real.exp_pos z).le h
        _ = ((a * a : ℚ) : ℝ) := by push_cast; ring
        _ ≤ ((upB 70 (a * a) : ℚ) : ℝ) := by exact_mod_cast (round_sound 70 (a * a)).2
    have := ih (upB 70 (a * a)) (2 * z) h2
    have e : (2:ℝ) ^ (n + 1) * z = 2 ^ n * (2 * z) := by ring
    rw [e]
    exact this

theorem lo_final (S T x : ℚ) (y : ℝ) (hy : (2:ℝ) ^ 6 * y = (x : ℝ))
    (hy1 : -(15/16) ≤ y)
    (hhi : Real.exp y ≤ (S : ℝ) + 3 * |(T : ℝ)|) (hT : |(T : ℝ)| ≤ 1 / 87178291200) :
    ((max (sqN (dnB 70) 6 (dnB 70 (S - 3 * qabs T))) 0 : ℚ) : ℝ) ≤ Real.exp (x : ℝ) := by
  have hqa := qabs_cast T
  have hpos : (0:ℝ) < ((S - 3 * qabs T : ℚ) : ℝ) := by
    push_cast
    rw [hqa]
    have := Real.add_one_le_exp y
    linarith
  have hpos' : 0 < S - 3 * qabs T := by exact_mod_cast hpos
  have h0 : 0 ≤ dnB 70 (S - 3 * qabs T) := dn_nonneg 70 _ hpos'.le
  have h1 : ((dnB 70 (S - 3 * qabs T) : ℚ) : ℝ) ≤ Real.exp y := by
    have := dn_le 70 (S - 3 * qabs T)
    have h' : ((dnB 70 (S - 3 * qabs T) : ℚ) : ℝ) ≤ ((S - 3 * qabs T : ℚ) : ℝ) := by
      exact_mod_cast this
    push_cast at h'
    rw [hqa] at h'
    linarith
  have := sq_lo 6 _ y h0 h1
  rw [hy] at this
  rw [Rat.cast_max]
  refine max_le this ?_
  simpa using (Real.exp_pos _).le

theorem hi_final (S T x : ℚ) (y : ℝ) (hy : (2:ℝ) ^ 6 * y = (x : ℝ))
    (hhi : Real.exp y ≤ (S : ℝ) + 3 * |(T : ℝ)|) :
    Real.exp (x : ℝ) ≤ ((sqN (upB 70) 6 (upB 70 (S + 3 * qabs T)) : ℚ) : ℝ) := by
  have hqa := qabs_cast T
  have h1 : Real.exp y ≤ ((upB 70 (S + 3 * qabs T) : ℚ) : ℝ) := by
    have h' : ((S + 3 * qabs T : ℚ) : ℝ) ≤ ((upB 70 (S + 3 * qabs T) : ℚ) : ℝ) := by
      exact_mod_cast (round_sound 70 _).2
    push_cast at h'
    rw [hqa] at h'
    linarith
  have := sq_hi 6 _ y h1
  rw [hy] at this
  exact this

theorem far_left (x : ℝ) (h : x < -60) : Real.exp x ≤ 1 / 2 ^ 80 := by
  have e3 : (16:ℝ) ≤ Real.exp 3 := by
    have e : Real.exp 3 = Real.exp (3/32) ^ 32 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    have := pow_le_pow_left₀ (by norm_num) (Real.add_one_le_exp (3/32 : ℝ)) 32
    refine le_trans ?_ this
    norm_num
  have e60 : Real.exp 60 = Real.exp 3 ^ 20 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h60 : (2:ℝ) ^ 80 ≤ Real.exp 60 := by
    rw [e60]
    have := pow_le_pow_left₀ (by norm_num) e3 20
    have e : (2:ℝ) ^ 80 = 16 ^ 20 := by norm_num
    rw [e]
    exact this
  have hx : Real.exp x ≤ Real.exp (-60) := Real.exp_le_exp.mpr h.le
  have hn : Real.exp (-60) = (Real.exp 60)⁻¹ := Real.exp_neg 60
  rw [hn] at hx
  refine hx.trans ?_
  rw [one_div]
  exact inv_anti₀ (by positivity) h60

theorem exp_encl : ExpEncl := by
  intro x hx
  by_cases h : x < -60
  · unfold expLo expHi
    rw [if_pos h, if_pos h]
    refine ⟨le_refl _, ?_, ?_⟩
    · simpa using (Real.exp_pos _).le
    · have := far_left (x : ℝ) (by exact_mod_cast h)
      push_cast
      exact this
  · have hx1 : -60 ≤ x := not_lt.mp h
    unfold expLo expHi
    rw [if_neg h, if_neg h]
    have h1 : -(15/16) ≤ x / 64 := by linarith
    have h2 : x / 64 ≤ 1 := by linarith
    obtain ⟨hlo, hhi, hT⟩ := series_encl (x / 64) h1 h2
    have hy : (2:ℝ) ^ 6 * (((x / 64 : ℚ)) : ℝ) = (x : ℝ) := by push_cast; ring
    have hy1 : -(15/16) ≤ (((x / 64 : ℚ)) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr h1
      push_cast at this ⊢
      linarith
    refine ⟨le_max_right _ _, ?_, ?_⟩
    · exact lo_final _ _ x _ hy hy1 hhi hT
    · exact hi_final _ _ x _ hy hhi

end Lane4.Case
