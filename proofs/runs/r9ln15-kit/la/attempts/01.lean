set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Lane4.Case
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd rsum)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.LNC Lane4.R7K2

/-! ### basic equations -/

theorem la_sumL_cons (a : ℝ) (l : List ℝ) : sumL (a :: l) = a + sumL l := rfl
theorem la_sumAbsL_cons (a : ℝ) (l : List ℝ) : sumAbsL (a :: l) = |a| + sumAbsL l := rfl

theorem la_sumAbsL_nonneg : ∀ l : List ℝ, 0 ≤ sumAbsL l
  | [] => by simp [sumAbsL]
  | a :: l => by
    rw [la_sumAbsL_cons]
    exact add_nonneg (abs_nonneg a) (la_sumAbsL_nonneg l)

theorem la_sumAbsL_le (c : ℝ) : ∀ l : List ℝ, (∀ v ∈ l, |v| ≤ c) → sumAbsL l ≤ c * (l.length : ℝ)
  | [], _ => by simp [sumAbsL]
  | a :: l, h => by
    rw [la_sumAbsL_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have h1 := h a (List.mem_cons.mpr (Or.inl rfl))
    have h2 := la_sumAbsL_le c l (fun v hv => h v (List.mem_cons_of_mem _ hv))
    linarith

theorem la_one_le_pow {u : ℝ} (hu : 0 ≤ u) : ∀ k : ℕ, 1 ≤ (1 + u) ^ k
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ]
    have := la_one_le_pow hu k
    nlinarith

theorem la_pow_le {u : ℝ} (hu : 0 ≤ u) :
    ∀ k : ℕ, 2 * (k : ℝ) * u ≤ 1 → (1 + u) ^ k ≤ 1 + 2 * (k : ℝ) * u := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro h
    push_cast at h
    have hk : 2 * (k : ℝ) * u ≤ 1 := by
      have : 0 ≤ u := hu
      linarith
    have h1 := ih hk
    have h2 : (1 + u) ^ (k + 1) = (1 + u) ^ k * (1 + u) := pow_succ _ _
    rw [h2]
    push_cast
    have h3 : (1 + u) ^ k * (1 + u) ≤ (1 + 2 * (k : ℝ) * u) * (1 + u) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have h4 : 2 * (k : ℝ) * u * u ≤ 1 * u := mul_le_mul_of_nonneg_right hk hu
    have h5 : (1 + 2 * (k : ℝ) * u) * (1 + u) = 1 + u + 2 * (k : ℝ) * u + 2 * (k : ℝ) * u * u := by
      ring
    linarith

/-! ### the generalised chain -/

theorem la_chain {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) :
    ∀ (l : List ℝ) (acc : ℝ),
      (|acc| + sumAbsL l) * (1 + u) ^ l.length + (l.length : ℝ) * (1 + u) ^ l.length * η ≤ M →
      |rsum fl l acc - (acc + sumL l)| ≤
        ((1 + u) ^ l.length - 1) * (|acc| + sumAbsL l) + (l.length : ℝ) * (1 + u) ^ l.length * η := by
  intro l
  induction l with
  | nil =>
    intro acc _
    simp [rsum, sumL, sumAbsL]
  | cons a l ih =>
    intro acc hM
    have hu0 := hC.u0
    have hη0 := hC.h0
    have hS0 := la_sumAbsL_nonneg l
    have hq1 := la_one_le_pow hu0 l.length
    have hk0 : (0 : ℝ) ≤ (l.length : ℝ) := Nat.cast_nonneg _
    have e : rsum fl (a :: l) acc = rsum fl l (fl (acc + a)) := rfl
    rw [e, la_sumL_cons, la_sumAbsL_cons]
    simp only [List.length_cons, pow_succ, Nat.cast_add, Nat.cast_one] at hM ⊢
    rw [la_sumAbsL_cons] at hM
    have hQ : 1 ≤ (1 + u) ^ l.length * (1 + u) := by nlinarith
    have hMt : |acc + a| ≤ M := by
      have h1 := abs_add_le acc a
      have h2 : |acc| + (|a| + sumAbsL l) ≤
          (|acc| + (|a| + sumAbsL l)) * ((1 + u) ^ l.length * (1 + u)) :=
        le_mul_of_one_le_right (by have := abs_nonneg acc; have := abs_nonneg a; linarith) hQ
      have h3 : 0 ≤ ((l.length : ℝ) + 1) * ((1 + u) ^ l.length * (1 + u)) * η :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) hη0
      linarith
    have herr := hC.rnd.err (acc + a) hMt
    have hP : |acc + a| ≤ |acc| + |a| := abs_add_le acc a
    have hut : u * |acc + a| ≤ u * (|acc| + |a|) := mul_le_mul_of_nonneg_left hP hu0
    have hF : |fl (acc + a)| ≤ (1 + u) * (|acc| + |a|) + η := by
      have := abs_sub_abs_le_abs_sub (fl (acc + a)) (acc + a)
      linarith
    have hS5 : 0 ≤ sumAbsL l * (1 + u) ^ l.length * u :=
      mul_nonneg (mul_nonneg hS0 (by linarith)) hu0
    have hS6 : 0 ≤ ((l.length : ℝ) + 1) * (1 + u) ^ l.length * η * u :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hη0) hu0
    have hM' : (|fl (acc + a)| + sumAbsL l) * (1 + u) ^ l.length
        + (l.length : ℝ) * (1 + u) ^ l.length * η ≤ M := by
      have h4 : (|fl (acc + a)| + sumAbsL l) * (1 + u) ^ l.length ≤
          ((1 + u) * (|acc| + |a|) + η + sumAbsL l) * (1 + u) ^ l.length :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      first
        | linarith [h4, hS5, hS6, hM]
        | nlinarith [h4, hS5, hS6, hM]
    have IH := ih (fl (acc + a)) hM'
    have hq0 : 0 ≤ (1 + u) ^ l.length - 1 := by linarith
    have h7 : ((1 + u) ^ l.length - 1) * |fl (acc + a)| ≤
        ((1 + u) ^ l.length - 1) * ((1 + u) * (|acc| + |a|) + η) :=
      mul_le_mul_of_nonneg_left hF hq0
    obtain ⟨c1, c2⟩ := abs_le.mp IH
    obtain ⟨d1, d2⟩ := abs_le.mp herr
    rw [abs_le]
    constructor
    · first
        | linarith [c1, d1, h7, hut, hS5, hS6]
        | nlinarith [c1, d1, h7, hut, hS5, hS6]
    · first
        | linarith [c2, d2, h7, hut, hS5, hS6]
        | nlinarith [c2, d2, h7, hut, hS5, hS6]

theorem la_rsum_gen {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (l : List ℝ)
    (hl : l.length ≤ 32) (hS : sumAbsL l ≤ 2 ^ 36) :
    |rsum fl l 0 - sumL l| ≤ 2 * (l.length : ℝ) * u * sumAbsL l + 2 * (l.length : ℝ) * η := by
  have hu0 := hC.u0
  have hη0 := hC.h0
  have hu1 : u ≤ 1 / 16777216 := le_trans hC.u1 (by norm_num)
  have hη1 : η ≤ 1 / 2 ^ 149 := hC.h1
  have hk0 : (0 : ℝ) ≤ (l.length : ℝ) := Nat.cast_nonneg _
  have hk32 : (l.length : ℝ) ≤ 32 := by exact_mod_cast hl
  have hS0 := la_sumAbsL_nonneg l
  have hku : 2 * (l.length : ℝ) * u ≤ 1 := by
    have h := mul_le_mul hk32 hu1 hu0 (by norm_num : (0 : ℝ) ≤ 32)
    have h' : (32 : ℝ) * (1 / 16777216) ≤ 1 / 2 := by norm_num
    linarith
  have hp := la_pow_le hu0 l.length hku
  have hq1 := la_one_le_pow hu0 l.length
  have hq2 : (1 + u) ^ l.length ≤ 2 := by linarith
  have hΦ : (|(0 : ℝ)| + sumAbsL l) * (1 + u) ^ l.length
      + (l.length : ℝ) * (1 + u) ^ l.length * η ≤ M := by
    rw [abs_zero, zero_add]
    have h1 : sumAbsL l * (1 + u) ^ l.length ≤ 2 ^ 36 * 2 :=
      mul_le_mul hS hq2 (by linarith) (by positivity)
    have h2 : (l.length : ℝ) * (1 + u) ^ l.length ≤ 32 * 2 :=
      mul_le_mul hk32 hq2 (by linarith) (by norm_num)
    have h3 : (l.length : ℝ) * (1 + u) ^ l.length * η ≤ 32 * 2 * η :=
      mul_le_mul_of_nonneg_right h2 hη0
    have h4 : (2 : ℝ) ^ 36 * 2 + 32 * 2 * (1 / 2 ^ 149) ≤ 2 ^ 40 := by norm_num
    have h5 := hC.M1
    linarith
  have key := la_chain hC l 0 hΦ
  simp only [abs_zero, zero_add] at key
  have hq3 : (1 + u) ^ l.length - 1 ≤ 2 * (l.length : ℝ) * u := by linarith
  have h5 : ((1 + u) ^ l.length - 1) * sumAbsL l ≤ 2 * (l.length : ℝ) * u * sumAbsL l :=
    mul_le_mul_of_nonneg_right hq3 hS0
  have h6 : (l.length : ℝ) * (1 + u) ^ l.length * η ≤ 2 * (l.length : ℝ) * η := by
    have := mul_le_mul_of_nonneg_left hq2 (mul_nonneg hk0 hη0)
    linarith
  linarith

theorem la_combine {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (l : List ℝ) (n : ℕ)
    (hn : l.length = n) (s W : ℝ) (hW : 0 ≤ W) (hl : n ≤ 32)
    (hS : sumAbsL l ≤ (1 + 3 * u) * W + 20 * (n : ℝ) * η) (hS2 : sumAbsL l ≤ 2 ^ 36)
    (herr : |sumL l - s| ≤ (2 * u + u ^ 2) * W + 19 * (n : ℝ) * η) :
    |rsum fl l 0 - s| ≤ 2 * ((n : ℝ) + 2) * u * W + 200 * (n : ℝ) * η := by
  have hu0 := hC.u0
  have hη0 := hC.h0
  have hu1 : u ≤ 1 / 16777216 := le_trans hC.u1 (by norm_num)
  have h1 := la_rsum_gen hC l (by rw [hn]; exact hl) hS2
  rw [hn] at h1
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hn32 : (n : ℝ) ≤ 32 := by exact_mod_cast hl
  have hnu : (n : ℝ) * u ≤ 1 / 524288 := by
    have h := mul_le_mul hn32 hu1 hu0 (by norm_num : (0 : ℝ) ≤ 32)
    have h' : (32 : ℝ) * (1 / 16777216) ≤ 1 / 524288 := by norm_num
    linarith
  have h6 : (6 * (n : ℝ) + 1) * u ≤ 2 := by
    have h' : (6 : ℝ) * (1 / 524288) + 1 / 16777216 ≤ 2 := by norm_num
    linarith
  have hnu0 : 0 ≤ 2 * (n : ℝ) * u := by
    have := mul_nonneg hn0 hu0
    linarith
  have hA : 2 * (n : ℝ) * u * sumAbsL l ≤ 2 * (n : ℝ) * u * ((1 + 3 * u) * W + 20 * (n : ℝ) * η) :=
    mul_le_mul_of_nonneg_left hS hnu0
  have hW1 : 0 ≤ u * W := mul_nonneg hu0 hW
  have hB : ((6 * (n : ℝ) + 1) * u) * (u * W) ≤ 2 * (u * W) :=
    mul_le_mul_of_nonneg_right h6 hW1
  have hnη : 0 ≤ (n : ℝ) * η := mul_nonneg hn0 hη0
  have hD : ((n : ℝ) * u) * ((n : ℝ) * η) ≤ 1 * ((n : ℝ) * η) :=
    mul_le_mul_of_nonneg_right (by linarith) hnη
  obtain ⟨a1, a2⟩ := abs_le.mp h1
  obtain ⟨b1, b2⟩ := abs_le.mp herr
  rw [abs_le]
  constructor
  · first
      | linarith [hA, hB, hD, hnη, hW1, a1, a2, b1, b2]
      | nlinarith [hA, hB, hD, hnη, hW1, a1, a2, b1, b2]
  · first
      | linarith [hA, hB, hD, hnη, hW1, a1, a2, b1, b2]
      | nlinarith [hA, hB, hD, hnη, hW1, a1, a2, b1, b2]

theorem rsum_rel : RsumRel := by
  intro u η M fl hC l hl hv
  have h := la_sumAbsL_le (2 ^ 30) l hv
  have hk32 : (l.length : ℝ) ≤ 32 := by exact_mod_cast hl
  have h2 : (2 : ℝ) ^ 30 * (l.length : ℝ) ≤ 2 ^ 30 * 32 :=
    mul_le_mul_of_nonneg_left hk32 (by norm_num)
  have h3 : (2 : ℝ) ^ 30 * 32 ≤ 2 ^ 36 := by norm_num
  exact la_rsum_gen hC l hl (by linarith)

/-! ### terms -/

theorem la_term_core {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) {y v w : ℝ}
    (hw0 : 0 ≤ w) (hw : w ≤ 16) (hy : |y| ≤ w) (hv : |v| ≤ 17) :
    |fl (fl y * v) - y * v| ≤ (2 * u + u ^ 2) * (w * |v|) + 19 * η ∧
    |fl (fl y * v)| ≤ (1 + 3 * u) * (w * |v|) + 20 * η ∧ |fl (fl y * v)| ≤ 300 := by
  have hu0 := hC.u0
  have hη0 := hC.h0
  have hu : u ≤ 1 / 16777216 := le_trans hC.u1 (by norm_num)
  have hη : η ≤ 1 / 1000000000 := le_trans hC.h1 (by norm_num)
  have hM : (1000000 : ℝ) ≤ M := le_trans (by norm_num) hC.M1
  have hv0 : 0 ≤ |v| := abs_nonneg v
  have huw : u * w ≤ 1 := by
    have h1 : u * w ≤ 1 / 16777216 * 16 := mul_le_mul hu hw hw0 (by norm_num)
    have h2 : (1 : ℝ) / 16777216 * 16 ≤ 1 := by norm_num
    linarith
  have hwM : w ≤ M := by linarith
  have e1 := hC.rnd.abs hu0 hy hwM
  have e2 := hC.rnd.bound hu0 hy hwM
  have hz : |fl y * v| ≤ (w + (u * w + η)) * |v| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right e2 hv0
  have hBM : (w + (u * w + η)) * |v| ≤ M := by
    have h1 : w + (u * w + η) ≤ 18 := by linarith
    have h2 : (w + (u * w + η)) * |v| ≤ 18 * 17 := mul_le_mul h1 hv hv0 (by norm_num)
    linarith
  have e3 := hC.rnd.abs hu0 hz hBM
  have e4 := hC.rnd.bound hu0 hz hBM
  have e5 : |fl y * v - y * v| ≤ (u * w + η) * |v| := by
    rw [← sub_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right e1 hv0
  have hwv : 0 ≤ w * |v| := mul_nonneg hw0 hv0
  have huu : u * u ≤ u := by nlinarith
  have hU1 : (u * u) * (w * |v|) ≤ u * (w * |v|) := mul_le_mul_of_nonneg_right huu hwv
  have hve : (η + u * η) * |v| ≤ (η + u * η) * 17 :=
    mul_le_mul_of_nonneg_left hv (add_nonneg hη0 (mul_nonneg hu0 hη0))
  have hUe : u * η ≤ 1 / 16777216 * η := mul_le_mul_of_nonneg_right hu hη0
  have h6 := abs_sub_le (fl (fl y * v)) (fl y * v) (y * v)
  have h2 : |fl (fl y * v)| ≤ (1 + 3 * u) * (w * |v|) + 20 * η := by
    first
      | linarith [e4, hU1, hve, hUe, hη0]
      | nlinarith [e4, hU1, hve, hUe, hη0]
  refine ⟨?_, h2, ?_⟩
  · first
      | linarith [h6, e3, e5, hve, hUe, hη0]
      | nlinarith [h6, e3, e5, hve, hUe, hη0]
  · have hwv2 : w * |v| ≤ 272 := by
      have := mul_le_mul hw hv hv0 (by norm_num : (0 : ℝ) ≤ 16)
      linarith
    have h3 : u * (w * |v|) ≤ u * 272 := mul_le_mul_of_nonneg_left hwv2 hu0
    first
      | linarith [h2, hwv2, h3, hu, hη]
      | nlinarith [h2, hwv2, h3, hu, hη]

theorem la_term_p {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) {z : ℝ} (hz : |z| ≤ 1048576) :
    |fl z - z| ≤ (2 * u + u ^ 2) * |z| + 19 * η ∧ |fl z| ≤ (1 + 3 * u) * |z| + 20 * η ∧
    |fl z| ≤ 2097152 := by
  have hu0 := hC.u0
  have hη0 := hC.h0
  have hu : u ≤ 1 / 16777216 := le_trans hC.u1 (by norm_num)
  have hη : η ≤ 1 / 1000000000 := le_trans hC.h1 (by norm_num)
  have hM : (1048576 : ℝ) ≤ M := le_trans (by norm_num) hC.M1
  have e := hC.rnd.err z (le_trans hz hM)
  have hz0 : 0 ≤ |z| := abs_nonneg z
  have hu2 : 0 ≤ u ^ 2 * |z| := mul_nonneg (sq_nonneg u) hz0
  have huz : 0 ≤ u * |z| := mul_nonneg hu0 hz0
  have hfz : |fl z| ≤ |z| + (u * |z| + η) := by
    have := abs_sub_abs_le_abs_sub (fl z) z
    linarith
  refine ⟨?_, ?_, ?_⟩
  · first
      | linarith [e, hu2, huz, hη0]
      | nlinarith [e, hu2, huz, hη0]
  · first
      | linarith [hfz, hu2, huz, hη0]
      | nlinarith [hfz, hu2, huz, hη0]
  · have h1 : u * |z| ≤ u * 1048576 := mul_le_mul_of_nonneg_left hz hu0
    linarith

/-! ### the lists of rounded products -/

noncomputable def la_prods (fl : ℝ → ℝ) : List ℚ → List ℝ → (ℕ → ℝ) → ℕ → List ℝ
  | a :: w, v :: x, d, j => fl (asw fl a (d j) * v) :: la_prods fl w x d (j + 1)
  | _, _, _, _ => []

noncomputable def la_pprods (fl : ℝ → ℝ) : List ℝ → List ℝ → List ℝ
  | a :: x, b :: y => fl (a * b) :: la_pprods fl x y
  | _, _ => []

theorem la_ardot_eq (fl : ℝ → ℝ) : ∀ (r : List ℚ) (x : List ℝ) (d : ℕ → ℝ) (j : ℕ) (acc : ℝ),
    ardot fl r x d j acc = rsum fl (la_prods fl r x d j) acc := by
  intro r
  induction r with
  | nil => intro x d j acc; cases x <;> rfl
  | cons a w ih =>
    intro x d j acc
    cases x with
    | nil => rfl
    | cons v x' => exact ih x' d (j + 1) (fl (acc + fl (asw fl a (d j) * v)))

theorem la_pdot_eq (fl : ℝ → ℝ) : ∀ (x y : List ℝ) (acc : ℝ),
    pdot fl x y acc = rsum fl (la_pprods fl x y) acc := by
  intro x
  induction x with
  | nil => intro y acc; cases y <;> rfl
  | cons a x' ih =>
    intro y acc
    cases y with
    | nil => rfl
    | cons b y' => exact ih y' (fl (acc + fl (a * b)))

theorem la_prods_length (fl : ℝ → ℝ) (d : ℕ → ℝ) :
    ∀ (r : List ℚ) (x : List ℝ) (j : ℕ), r.length = x.length →
      (la_prods fl r x d j).length = r.length := by
  intro r
  induction r with
  | nil =>
    intro x j hl
    cases x with
    | nil => rfl
    | cons v x => simp at hl
  | cons a w ih =>
    intro x j hl
    cases x with
    | nil => simp at hl
    | cons v x' =>
      have hl' : w.length = x'.length := by simpa using hl
      show (fl (asw fl a (d j) * v) :: la_prods fl w x' d (j + 1)).length = (a :: w).length
      rw [List.length_cons, List.length_cons, ih x' (j + 1) hl']

theorem la_pprods_length (fl : ℝ → ℝ) :
    ∀ (x y : List ℝ), x.length = y.length → (la_pprods fl x y).length = x.length := by
  intro x
  induction x with
  | nil =>
    intro y hl
    cases y with
    | nil => rfl
    | cons v y => simp at hl
  | cons a x' ih =>
    intro y hl
    cases y with
    | nil => simp at hl
    | cons b y' =>
      have hl' : x'.length = y'.length := by simpa using hl
      show (fl (a * b) :: la_pprods fl x' y').length = (a :: x').length
      rw [List.length_cons, List.length_cons, ih y' hl']

/-! ### nil equations -/

theorem la_dotT_nil_l (δ : ℝ) (x : List ℝ) : dotT δ [] x = 0 := by cases x <;> rfl
theorem la_dotT_nil_r (δ : ℝ) (r : List ℚ) : dotT δ r [] = 0 := by cases r <;> rfl
theorem la_dotP_nil_l (x : List ℝ) (d : ℕ → ℝ) (j : ℕ) : dotP [] x d j = 0 := by cases x <;> rfl
theorem la_dotP_nil_r (r : List ℚ) (d : ℕ → ℝ) (j : ℕ) : dotP r [] d j = 0 := by cases r <;> rfl
theorem la_dotR_nil_l (y : List ℝ) : Lane4.LNC.dotR [] y = 0 := by cases y <;> rfl
theorem la_dotR_nil_r (x : List ℝ) : Lane4.LNC.dotR x [] = 0 := by cases x <;> rfl
theorem la_dotRA_nil_l (y : List ℝ) : dotRA [] y = 0 := by cases y <;> rfl
theorem la_dotRA_nil_r (x : List ℝ) : dotRA x [] = 0 := by cases x <;> rfl
theorem la_totQ_nil_l (δ : ℚ) (xv : List IV) : totQ δ [] xv = 0 := by cases xv <;> rfl
theorem la_totQ_nil_r (δ : ℚ) (r : List ℚ) : totQ δ r [] = 0 := by cases r <;> rfl
theorem la_pErr_nil_l (yv : List IV) : pErrQ [] yv = 0 := by cases yv <;> rfl
theorem la_pErr_nil_r (xv : List IV) : pErrQ xv [] = 0 := by cases xv <;> rfl
theorem la_ptot_nil_l (yv : List IV) : ptotQ [] yv = 0 := by cases yv <;> rfl
theorem la_ptot_nil_r (xv : List IV) : ptotQ xv [] = 0 := by cases xv <;> rfl

theorem la_dotT_nonneg {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ (r : List ℚ) (x : List ℝ), 0 ≤ dotT δ r x := by
  intro r
  induction r with
  | nil => intro x; rw [la_dotT_nil_l]
  | cons a w ih =>
    intro x
    cases x with
    | nil => rw [la_dotT_nil_r]
    | cons v x' =>
      have e1 : dotT δ (a :: w) (v :: x') = (|(a : ℝ)| + δ) * |v| + dotT δ w x' := rfl
      rw [e1]
      have := mul_nonneg (add_nonneg (abs_nonneg (a : ℝ)) hδ) (abs_nonneg v)
      have := ih x'
      linarith

theorem la_dotRA_nonneg : ∀ (x y : List ℝ), 0 ≤ dotRA x y := by
  intro x
  induction x with
  | nil => intro y; rw [la_dotRA_nil_l]
  | cons a x' ih =>
    intro y
    cases y with
    | nil => rw [la_dotRA_nil_r]
    | cons b y' =>
      have e1 : dotRA (a :: x') (b :: y') = |a * b| + dotRA x' y' := rfl
      rw [e1]
      have := abs_nonneg (a * b)
      have := ih y'
      linarith

/-! ### sums of rounded products: ardot -/

theorem la_prods_facts {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ δ) :
    ∀ (r : List ℚ) (x : List ℝ) (j : ℕ), r.length = x.length → (∀ a ∈ r, |(a : ℝ)| ≤ 15) →
      (∀ v ∈ x, |v| ≤ 17) →
      sumAbsL (la_prods fl r x d j) ≤ (1 + 3 * u) * dotT δ r x + 20 * (r.length : ℝ) * η ∧
      |sumL (la_prods fl r x d j) - dotP r x d j| ≤
        (2 * u + u ^ 2) * dotT δ r x + 19 * (r.length : ℝ) * η ∧
      sumAbsL (la_prods fl r x d j) ≤ 300 * (r.length : ℝ) := by
  intro r
  induction r with
  | nil =>
    intro x j hl _ _
    cases x with
    | nil =>
      have e1 : la_prods fl [] [] d j = [] := rfl
      rw [e1, la_dotT_nil_l, la_dotP_nil_l]
      simp [sumAbsL, sumL]
    | cons v x => simp at hl
  | cons a w ih =>
    intro x j hl hr hx
    cases x with
    | nil => simp at hl
    | cons v x' =>
      have hl' : w.length = x'.length := by simpa using hl
      obtain ⟨i1, i2, i3⟩ := ih x' (j + 1) hl' (fun b hb => hr b (List.mem_cons_of_mem _ hb))
        (fun b hb => hx b (List.mem_cons_of_mem _ hb))
      have ha := hr a (List.mem_cons.mpr (Or.inl rfl))
      have hv := hx v (List.mem_cons.mpr (Or.inl rfl))
      have hw0 : 0 ≤ |(a : ℝ)| + δ := add_nonneg (abs_nonneg _) hδ0
      have hy : |(a : ℝ) + d j| ≤ |(a : ℝ)| + δ :=
        le_trans (abs_add_le _ _) (by linarith [hd j])
      obtain ⟨t1, t2, t3⟩ := la_term_core hC hw0 (by linarith) hy hv
      have e1 : la_prods fl (a :: w) (v :: x') d j
          = fl (fl ((a : ℝ) + d j) * v) :: la_prods fl w x' d (j + 1) := rfl
      have e2 : dotT δ (a :: w) (v :: x') = (|(a : ℝ)| + δ) * |v| + dotT δ w x' := rfl
      have e3 : dotP (a :: w) (v :: x') d j = ((a : ℝ) + d j) * v + dotP w x' d (j + 1) := rfl
      rw [e1, e2, e3, la_sumAbsL_cons, la_sumL_cons]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      obtain ⟨b1, b2⟩ := abs_le.mp t1
      obtain ⟨c1, c2⟩ := abs_le.mp i2
      refine ⟨?_, ?_, ?_⟩
      · first
          | linarith [t2, i1]
          | nlinarith [t2, i1]
      · rw [abs_le]
        constructor
        · first
            | linarith [b1, b2, c1, c2]
            | nlinarith [b1, b2, c1, c2]
        · first
            | linarith [b1, b2, c1, c2]
            | nlinarith [b1, b2, c1, c2]
      · linarith [t3, i3]

/-! ### sums of rounded products: pdot -/

theorem la_pprods_facts {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (A B : ℝ) (hA0 : 0 ≤ A)
    (hB0 : 0 ≤ B) (hAB : A * B ≤ 1048576) :
    ∀ (x y : List ℝ), x.length = y.length → (∀ v ∈ x, |v| ≤ A) → (∀ v ∈ y, |v| ≤ B) →
      sumAbsL (la_pprods fl x y) ≤ (1 + 3 * u) * dotRA x y + 20 * (x.length : ℝ) * η ∧
      |sumL (la_pprods fl x y) - Lane4.LNC.dotR x y| ≤
        (2 * u + u ^ 2) * dotRA x y + 19 * (x.length : ℝ) * η ∧
      sumAbsL (la_pprods fl x y) ≤ 2097152 * (x.length : ℝ) := by
  intro x
  induction x with
  | nil =>
    intro y hl _ _
    cases y with
    | nil =>
      have e1 : la_pprods fl [] [] = [] := rfl
      rw [e1, la_dotRA_nil_l, la_dotR_nil_l]
      simp [sumAbsL, sumL]
    | cons v y => simp at hl
  | cons a x' ih =>
    intro y hl hx hy
    cases y with
    | nil => simp at hl
    | cons b y' =>
      have hl' : x'.length = y'.length := by simpa using hl
      obtain ⟨i1, i2, i3⟩ := ih y' hl' (fun v hv => hx v (List.mem_cons_of_mem _ hv))
        (fun v hv => hy v (List.mem_cons_of_mem _ hv))
      have ha := hx a (List.mem_cons.mpr (Or.inl rfl))
      have hb := hy b (List.mem_cons.mpr (Or.inl rfl))
      have hz : |a * b| ≤ 1048576 := by
        rw [abs_mul]
        exact le_trans (mul_le_mul ha hb (abs_nonneg _) hA0) hAB
      obtain ⟨t1, t2, t3⟩ := la_term_p hC hz
      have e1 : la_pprods fl (a :: x') (b :: y') = fl (a * b) :: la_pprods fl x' y' := rfl
      have e2 : dotRA (a :: x') (b :: y') = |a * b| + dotRA x' y' := rfl
      have e3 : Lane4.LNC.dotR (a :: x') (b :: y') = a * b + Lane4.LNC.dotR x' y' := rfl
      rw [e1, e2, e3, la_sumAbsL_cons, la_sumL_cons]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      obtain ⟨b1, b2⟩ := abs_le.mp t1
      obtain ⟨c1, c2⟩ := abs_le.mp i2
      refine ⟨?_, ?_, ?_⟩
      · first
          | linarith [t2, i1]
          | nlinarith [t2, i1]
      · rw [abs_le]
        constructor
        · first
            | linarith [b1, b2, c1, c2]
            | nlinarith [b1, b2, c1, c2]
        · first
            | linarith [b1, b2, c1, c2]
            | nlinarith [b1, b2, c1, c2]
      · linarith [t3, i3]

theorem la_small_abs {r : List ℚ} (hsm : smallQ r = true) : ∀ a ∈ r, |(a : ℝ)| ≤ 15 := by
  intro a ha
  have h := zsmallQ_mem hsm a ha
  have h2 : ((qabs a : ℚ) : ℝ) ≤ 15 := by exact_mod_cast h
  rwa [zqabs_cast] at h2

theorem ardot_rel : ArdotRel := by
  intro u η M fl hC δ hδ0 hδ1 r x d hd hrx hr32 hsm hx
  have hr : ∀ a ∈ r, |(a : ℝ)| ≤ 15 := la_small_abs hsm
  obtain ⟨f1, f2, f3⟩ := la_prods_facts hC hδ0 hδ1 d hd r x 0 hrx hr hx
  have hlen := la_prods_length fl d r x 0 hrx
  rw [la_ardot_eq]
  have hS2 : sumAbsL (la_prods fl r x d 0) ≤ 2 ^ 36 := by
    have hn32 : (r.length : ℝ) ≤ 32 := by exact_mod_cast hr32
    have h : (300 : ℝ) * 32 ≤ 2 ^ 36 := by norm_num
    linarith
  exact la_combine hC (la_prods fl r x d 0) r.length hlen (dotP r x d 0) (dotT δ r x)
    (la_dotT_nonneg hδ0 r x) hr32 f1 hS2 f2

theorem pdot_rel : PdotRel := by
  intro u η M fl hC x y A B hl hx32 hA hB hA0 hB0 hAB
  have hAB' : A * B ≤ 1048576 := le_trans hAB (by norm_num)
  obtain ⟨f1, f2, f3⟩ := la_pprods_facts hC A B hA0 hB0 hAB' x y hl hA hB
  have hlen := la_pprods_length fl x y hl
  rw [la_pdot_eq]
  have hS2 : sumAbsL (la_pprods fl x y) ≤ 2 ^ 36 := by
    have hn32 : (x.length : ℝ) ≤ 32 := by exact_mod_cast hx32
    have h : (2097152 : ℝ) * 32 ≤ 2 ^ 36 := by norm_num
    linarith
  exact la_combine hC (la_pprods fl x y) x.length hlen (Lane4.LNC.dotR x y) (dotRA x y)
    (la_dotRA_nonneg x y) hx32 f1 hS2 f2

/-! ### interval bookkeeping -/

theorem la_mem_iv : ∀ (x : List ℝ) (xv : List IV), InIVs x xv → ∀ v ∈ x, ∃ c ∈ xv, InIV v c := by
  intro x
  induction x with
  | nil => intro xv _ v hv; simp at hv
  | cons a x ih =>
    intro xv h v hv
    cases xv with
    | nil => exact absurd (zinIVs_len h) (by simp)
    | cons c xv' =>
      obtain ⟨h1, h2⟩ := zinIVs_cons_inv h
      rcases List.mem_cons.mp hv with hv1 | hv2
      · subst hv1
        exact ⟨c, List.mem_cons.mpr (Or.inl rfl), h1⟩
      · obtain ⟨c', hc', hi⟩ := ih xv' h2 v hv2
        exact ⟨c', List.mem_cons_of_mem _ hc', hi⟩

theorem la_bound_iv {x : List ℝ} {xv : List IV} (hx : InIVs x xv) (hnn : ∀ a ∈ xv, 0 ≤ a.2) :
    ∀ v ∈ x, |v| ≤ ((maxAbs (xv.map Prod.fst) : ℚ) : ℝ) + ((maxAbs (xv.map Prod.snd) : ℚ) : ℝ) := by
  intro v hv
  obtain ⟨c, hc, hi⟩ := la_mem_iv x xv hx v hv
  have hi' := zinIV_iff.mp hi
  have h1 : |v| ≤ |((c.1 : ℚ) : ℝ)| + ((c.2 : ℚ) : ℝ) := by
    have := abs_sub_abs_le_abs_sub v ((c.1 : ℚ) : ℝ)
    linarith
  have h2 := zle_maxAbs (List.mem_map.mpr ⟨c, hc, rfl⟩ : c.1 ∈ xv.map Prod.fst)
  have h3 : ((qabs c.1 : ℚ) : ℝ) ≤ ((maxAbs (xv.map Prod.fst) : ℚ) : ℝ) := by exact_mod_cast h2
  rw [zqabs_cast] at h3
  have h4 := zle_maxAbs (List.mem_map.mpr ⟨c, hc, rfl⟩ : c.2 ∈ xv.map Prod.snd)
  rw [zqabs_of_nonneg (hnn c hc)] at h4
  have h5 : ((c.2 : ℚ) : ℝ) ≤ ((maxAbs (xv.map Prod.snd) : ℚ) : ℝ) := by exact_mod_cast h4
  linarith

theorem la_totQ_nonneg {δ : ℚ} (hδ : 0 ≤ δ) :
    ∀ (r : List ℚ) (xv : List IV), (∀ a ∈ xv, 0 ≤ a.2) → 0 ≤ totQ δ r xv := by
  intro r
  induction r with
  | nil => intro xv _; exact le_of_eq (la_totQ_nil_l δ xv).symm
  | cons a w ih =>
    intro xv hx
    cases xv with
    | nil => exact le_of_eq (la_totQ_nil_r δ (a :: w)).symm
    | cons c xv' =>
      have e3 : totQ δ (a :: w) (c :: xv') = (qabs a + δ) * (qabs c.1 + c.2) + totQ δ w xv' := rfl
      rw [e3]
      have hc := hx c (List.mem_cons.mpr (Or.inl rfl))
      have ih' := ih xv' (fun b hb => hx b (List.mem_cons_of_mem _ hb))
      have q1 := zqabs_nonneg a
      have q2 := zqabs_nonneg c.1
      have p1 : 0 ≤ (qabs a + δ) * (qabs c.1 + c.2) := mul_nonneg (by linarith) (by linarith)
      linarith

theorem la_pErr_nonneg : ∀ (xv yv : List IV), (∀ a ∈ xv, 0 ≤ a.2) → (∀ a ∈ yv, 0 ≤ a.2) →
    0 ≤ pErrQ xv yv := by
  intro xv
  induction xv with
  | nil => intro yv _ _; exact le_of_eq (la_pErr_nil_l yv).symm
  | cons c xv' ih =>
    intro yv hx hy
    cases yv with
    | nil => exact le_of_eq (la_pErr_nil_r (c :: xv')).symm
    | cons e yv' =>
      have e3 : pErrQ (c :: xv') (e :: yv') =
          c.2 * (qabs e.1 + e.2) + qabs c.1 * e.2 + pErrQ xv' yv' := rfl
      rw [e3]
      have hc := hx c (List.mem_cons.mpr (Or.inl rfl))
      have he := hy e (List.mem_cons.mpr (Or.inl rfl))
      have ih' := ih yv' (fun a ha => hx a (List.mem_cons_of_mem _ ha))
        (fun a ha => hy a (List.mem_cons_of_mem _ ha))
      have q1 := zqabs_nonneg e.1
      have q2 := zqabs_nonneg c.1
      have p1 : 0 ≤ c.2 * (qabs e.1 + e.2) := mul_nonneg hc (by linarith)
      have p2 : 0 ≤ qabs c.1 * e.2 := mul_nonneg q2 he
      linarith

theorem la_ptot_nonneg : ∀ (xv yv : List IV), (∀ a ∈ xv, 0 ≤ a.2) → (∀ a ∈ yv, 0 ≤ a.2) →
    0 ≤ ptotQ xv yv := by
  intro xv
  induction xv with
  | nil => intro yv _ _; exact le_of_eq (la_ptot_nil_l yv).symm
  | cons c xv' ih =>
    intro yv hx hy
    cases yv with
    | nil => exact le_of_eq (la_ptot_nil_r (c :: xv')).symm
    | cons e yv' =>
      have e3 : ptotQ (c :: xv') (e :: yv') =
          (qabs c.1 + c.2) * (qabs e.1 + e.2) + ptotQ xv' yv' := rfl
      rw [e3]
      have hc := hx c (List.mem_cons.mpr (Or.inl rfl))
      have he := hy e (List.mem_cons.mpr (Or.inl rfl))
      have ih' := ih yv' (fun a ha => hx a (List.mem_cons_of_mem _ ha))
        (fun a ha => hy a (List.mem_cons_of_mem _ ha))
      have q1 := zqabs_nonneg e.1
      have q2 := zqabs_nonneg c.1
      have p1 : 0 ≤ (qabs c.1 + c.2) * (qabs e.1 + e.2) := mul_nonneg (by linarith) (by linarith)
      linarith

/-! ### dot: closeness of the ideal sums -/

theorem la_dotP_close {δ : ℚ} (hδ0 : 0 ≤ δ) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ (δ : ℝ)) :
    ∀ (r : List ℚ) (x : List ℝ) (xv : List IV) (j : ℕ), InIVs x xv →
      |dotP r x d j - ((dotC r xv : ℚ) : ℝ)| ≤ ((wErrQ δ r xv : ℚ) : ℝ) := by
  have hδR0 : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ0
  intro r
  induction r with
  | nil =>
    intro x xv j hx
    rw [la_dotP_nil_l, zdotC_nl, zwErrQ_nl]
    simp
  | cons a w ih =>
    intro x xv j hx
    cases x with
    | nil =>
      have hxv := zinIVs_nil_left hx
      subst hxv
      rw [la_dotP_nil_r, zdotC_nr, zwErrQ_nr]
      simp
    | cons v x' =>
      cases xv with
      | nil => exact absurd (zinIVs_len hx) (by simp)
      | cons c xv' =>
        obtain ⟨h1, h2⟩ := zinIVs_cons_inv hx
        have IH := ih x' xv' (j + 1) h2
        have h1' := zinIV_iff.mp h1
        have e1 : dotP (a :: w) (v :: x') d j = ((a : ℝ) + d j) * v + dotP w x' d (j + 1) := rfl
        have e2 : dotC (a :: w) (c :: xv') = a * c.1 + dotC w xv' := rfl
        have e3 : wErrQ δ (a :: w) (c :: xv') =
            qabs a * c.2 + δ * (qabs c.1 + c.2) + wErrQ δ w xv' := rfl
        rw [e1, e2, e3]
        push_cast
        simp only [zqabs_cast]
        have hvv : |v| ≤ |((c.1 : ℚ) : ℝ)| + ((c.2 : ℚ) : ℝ) := by
          have := abs_sub_abs_le_abs_sub v ((c.1 : ℚ) : ℝ)
          linarith
        have t1 : |(a : ℝ) * (v - ((c.1 : ℚ) : ℝ))| ≤ |(a : ℝ)| * ((c.2 : ℚ) : ℝ) := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left h1' (abs_nonneg _)
        have t2 : |d j * v| ≤ (δ : ℝ) * (|((c.1 : ℚ) : ℝ)| + ((c.2 : ℚ) : ℝ)) := by
          rw [abs_mul]
          exact mul_le_mul (hd j) hvv (abs_nonneg _) hδR0
        obtain ⟨p1, p2⟩ := abs_le.mp t1
        obtain ⟨q1, q2⟩ := abs_le.mp t2
        obtain ⟨r1, r2⟩ := abs_le.mp IH
        rw [abs_le]
        constructor
        · first
            | linarith [p1, p2, q1, q2, r1, r2]
            | nlinarith [p1, p2, q1, q2, r1, r2]
        · first
            | linarith [p1, p2, q1, q2, r1, r2]
            | nlinarith [p1, p2, q1, q2, r1, r2]

theorem la_dotT_le_totQ {δ : ℚ} (hδ0 : 0 ≤ δ) :
    ∀ (r : List ℚ) (x : List ℝ) (xv : List IV), InIVs x xv →
      dotT (δ : ℝ) r x ≤ ((totQ δ r xv : ℚ) : ℝ) := by
  have hδR0 : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ0
  intro r
  induction r with
  | nil =>
    intro x xv hx
    rw [la_dotT_nil_l, la_totQ_nil_l]
    simp
  | cons a w ih =>
    intro x xv hx
    cases x with
    | nil =>
      have hxv := zinIVs_nil_left hx
      subst hxv
      rw [la_dotT_nil_r, la_totQ_nil_r]
      simp
    | cons v x' =>
      cases xv with
      | nil => exact absurd (zinIVs_len hx) (by simp)
      | cons c xv' =>
        obtain ⟨h1, h2⟩ := zinIVs_cons_inv hx
        have IH := ih x' xv' h2
        have h1' := zinIV_iff.mp h1
        have hvv : |v| ≤ |((c.1 : ℚ) : ℝ)| + ((c.2 : ℚ) : ℝ) := by
          have := abs_sub_abs_le_abs_sub v ((c.1 : ℚ) : ℝ)
          linarith
        have e1 : dotT (δ : ℝ) (a :: w) (v :: x') = (|(a : ℝ)| + (δ : ℝ)) * |v| + dotT (δ : ℝ) w x' :=
          rfl
        have e3 : totQ δ (a :: w) (c :: xv') =
            (qabs a + δ) * (qabs c.1 + c.2) + totQ δ w xv' := rfl
        rw [e1, e3]
        push_cast
        simp only [zqabs_cast]
        have t : (|(a : ℝ)| + (δ : ℝ)) * |v| ≤
            (|(a : ℝ)| + (δ : ℝ)) * (|((c.1 : ℚ) : ℝ)| + ((c.2 : ℚ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hvv (add_nonneg (abs_nonneg _) hδR0)
        linarith

theorem dot_rel_sound : DotRelSound := by
  intro u η M fl hC δ hδ0 hδ1 r x xv d hd hrx hr32 hsm hx hB
  have hδR0 : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ0
  have hδR1 : (δ : ℝ) ≤ 1 / 2 := zhalf δ hδ1
  have hxabs : ∀ v ∈ x, |v| ≤ 17 := by
    intro v hv
    obtain ⟨c, hc, hi⟩ := la_mem_iv x xv hx v hv
    have hb := hB c hc
    have hi' := zinIV_iff.mp hi
    have hq : ((qabs c.1 : ℚ) : ℝ) + ((c.2 : ℚ) : ℝ) ≤ 16 := by exact_mod_cast hb.2
    rw [zqabs_cast] at hq
    have := abs_sub_abs_le_abs_sub v ((c.1 : ℚ) : ℝ)
    linarith
  have key := ardot_rel u η M fl hC (δ : ℝ) hδR0 hδR1 r x d hd hrx hr32 hsm hxabs
  have hcl := la_dotP_close hδ0 d hd r x xv 0 hx
  have hTq := la_dotT_le_totQ hδ0 r x xv hx
  have hT0 := la_dotT_nonneg hδR0 r x
  have hnn : ∀ a ∈ xv, 0 ≤ a.2 := fun a ha => (hB a ha).1
  have hw0 := zwErrQ_nonneg hδ0 r xv hnn
  have ht0 := la_totQ_nonneg hδ0 r xv hnn
  have ht0R : (0 : ℝ) ≤ ((totQ δ r xv : ℚ) : ℝ) := by exact_mod_cast ht0
  have e1 : (dotRel δ r xv).1 = dotC r xv := rfl
  have e2 : (dotRel δ r xv).2 =
      wErrQ δ r xv + ((r.length : ℚ) + 2) * totQ δ r xv / 2 ^ 21 + 1 / 2 ^ 60 := rfl
  have hrad0 : 0 ≤ wErrQ δ r xv + ((r.length : ℚ) + 2) * totQ δ r xv / 2 ^ 21 + 1 / 2 ^ 60 := by
    have h1 : 0 ≤ ((r.length : ℚ) + 2) * totQ δ r xv / 2 ^ 21 :=
      div_nonneg (mul_nonneg (by positivity) ht0) (by norm_num)
    have h2 : (0 : ℚ) ≤ 1 / 2 ^ 60 := by norm_num
    linarith
  refine ⟨?_, by rw [e2]; exact hrad0⟩
  rw [zinIV_iff, e1, e2]
  push_cast
  have hu0 := hC.u0
  have hη0 := hC.h0
  have hu : u ≤ 1 / 16777216 := le_trans hC.u1 (by norm_num)
  have hn0 : (0 : ℝ) ≤ (r.length : ℝ) := Nat.cast_nonneg _
  have hn32 : (r.length : ℝ) ≤ 32 := by exact_mod_cast hr32
  have h1 : u * (((r.length : ℝ) + 2) * dotT (δ : ℝ) r x) ≤
      1 / 16777216 * (((r.length : ℝ) + 2) * dotT (δ : ℝ) r x) :=
    mul_le_mul_of_nonneg_right hu (mul_nonneg (by linarith) hT0)
  have h2 : ((r.length : ℝ) + 2) * dotT (δ : ℝ) r x ≤
      ((r.length : ℝ) + 2) * ((totQ δ r xv : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left hTq (by linarith)
  have h4 : 0 ≤ ((r.length : ℝ) + 2) * ((totQ δ r xv : ℚ) : ℝ) :=
    mul_nonneg (by linarith) ht0R
  have h3 : 200 * (r.length : ℝ) * η ≤ 1 / 2 ^ 60 := by
    have h := mul_le_mul_of_nonneg_right hn32 hη0
    have h5 : (6400 : ℝ) * (1 / 2 ^ 149) ≤ 1 / 2 ^ 60 := by norm_num
    have h6 := hC.h1
    linarith
  obtain ⟨a1, a2⟩ := abs_le.mp key
  obtain ⟨b1, b2⟩ := abs_le.mp hcl
  rw [abs_le]
  constructor
  · first
      | linarith [a1, b1, h1, h2, h3, h4]
      | nlinarith [a1, b1, h1, h2, h3, h4]
  · first
      | linarith [a2, b2, h1, h2, h3, h4]
      | nlinarith [a2, b2, h1, h2, h3, h4]

/-! ### score -/

theorem la_mat_aux {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) {δ : ℚ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2) {x : List ℝ} {xv : List IV} (hx32 : x.length ≤ 32) (hx : InIVs x xv)
    (hB : Bdd 16 xv) (d : ℕ → ℕ → ℝ) (hd : ∀ i k, |d i k| ≤ (δ : ℝ)) :
    ∀ (A : List (List ℚ)) (i : ℕ), (∀ r ∈ A, r.length = x.length) →
      (∀ r ∈ A, smallQ r = true) →
      InIVs (armat fl A x d i) (matRel δ A xv) ∧ ∀ a ∈ matRel δ A xv, 0 ≤ a.2 := by
  intro A
  induction A with
  | nil =>
    intro i _ _
    exact ⟨zinIVs_nil, fun a ha => by simp [matRel] at ha⟩
  | cons r A ih =>
    intro i hr hs
    have hr0 := hr r (List.mem_cons.mpr (Or.inl rfl))
    have h1 := dot_rel_sound u η M fl hC δ hδ0 hδ1 r x xv (d i) (hd i) hr0
      (by rw [hr0]; exact hx32) (hs r (List.mem_cons.mpr (Or.inl rfl))) hx hB
    obtain ⟨ih1, ih2⟩ := ih (i + 1) (fun r' h => hr r' (List.mem_cons_of_mem _ h))
      (fun r' h => hs r' (List.mem_cons_of_mem _ h))
    have e1 : armat fl (r :: A) x d i = ardot fl r x (d i) 0 0 :: armat fl A x d (i + 1) := rfl
    have e2 : matRel δ (r :: A) xv = dotRel δ r xv :: matRel δ A xv := rfl
    rw [e1, e2]
    refine ⟨zinIVs_cons h1.1 ih1, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with h | h
    · rw [h]; exact h1.2
    · exact ih2 a h

theorem la_dotR_close : ∀ (x y : List ℝ) (xv yv : List IV), InIVs x xv → InIVs y yv →
    |Lane4.LNC.dotR x y - ((dotC (xv.map Prod.fst) yv : ℚ) : ℝ)| ≤ ((pErrQ xv yv : ℚ) : ℝ) := by
  intro x
  induction x with
  | nil =>
    intro y xv yv hx hy
    have hxv := zinIVs_nil_left hx
    subst hxv
    rw [la_dotR_nil_l, List.map_nil, zdotC_nl, la_pErr_nil_l]
    simp
  | cons a x' ih =>
    intro y xv yv hx hy
    cases y with
    | nil =>
      have hyv := zinIVs_nil_left hy
      subst hyv
      rw [la_dotR_nil_r, zdotC_nr, la_pErr_nil_r]
      simp
    | cons b y' =>
      cases xv with
      | nil => exact absurd (zinIVs_len hx) (by simp)
      | cons c xv' =>
        cases yv with
        | nil => exact absurd (zinIVs_len hy) (by simp)
        | cons e yv' =>
          obtain ⟨h1, h2⟩ := zinIVs_cons_inv hx
          obtain ⟨g1, g2⟩ := zinIVs_cons_inv hy
          have IH := ih y' xv' yv' h2 g2
          have h1' := zinIV_iff.mp h1
          have g1' := zinIV_iff.mp g1
          have e1 : Lane4.LNC.dotR (a :: x') (b :: y') = a * b + Lane4.LNC.dotR x' y' := rfl
          have e2 : dotC ((c :: xv').map Prod.fst) (e :: yv') =
              c.1 * e.1 + dotC (xv'.map Prod.fst) yv' := rfl
          have e3 : pErrQ (c :: xv') (e :: yv') =
              c.2 * (qabs e.1 + e.2) + qabs c.1 * e.2 + pErrQ xv' yv' := rfl
          rw [e1, e2, e3]
          push_cast
          simp only [zqabs_cast]
          have hbb : |b| ≤ |((e.1 : ℚ) : ℝ)| + ((e.2 : ℚ) : ℝ) := by
            have := abs_sub_abs_le_abs_sub b ((e.1 : ℚ) : ℝ)
            linarith
          have t1 : |(a - ((c.1 : ℚ) : ℝ)) * b| ≤
              ((c.2 : ℚ) : ℝ) * (|((e.1 : ℚ) : ℝ)| + ((e.2 : ℚ) : ℝ)) := by
            rw [abs_mul]
            exact mul_le_mul h1' hbb (abs_nonneg _) (le_trans (abs_nonneg _) h1')
          have t2 : |((c.1 : ℚ) : ℝ) * (b - ((e.1 : ℚ) : ℝ))| ≤
              |((c.1 : ℚ) : ℝ)| * ((e.2 : ℚ) : ℝ) := by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left g1' (abs_nonneg _)
          obtain ⟨p1, p2⟩ := abs_le.mp t1
          obtain ⟨q1, q2⟩ := abs_le.mp t2
          obtain ⟨r1, r2⟩ := abs_le.mp IH
          rw [abs_le]
          constructor
          · first
              | linarith [p1, p2, q1, q2, r1, r2]
              | nlinarith [p1, p2, q1, q2, r1, r2]
          · first
              | linarith [p1, p2, q1, q2, r1, r2]
              | nlinarith [p1, p2, q1, q2, r1, r2]

theorem la_dotRA_le : ∀ (x y : List ℝ) (xv yv : List IV), InIVs x xv → InIVs y yv →
    dotRA x y ≤ ((ptotQ xv yv : ℚ) : ℝ) := by
  intro x
  induction x with
  | nil =>
    intro y xv yv hx hy
    have hxv := zinIVs_nil_left hx
    subst hxv
    rw [la_dotRA_nil_l, la_ptot_nil_l]
    simp
  | cons a x' ih =>
    intro y xv yv hx hy
    cases y with
    | nil =>
      have hyv := zinIVs_nil_left hy
      subst hyv
      rw [la_dotRA_nil_r, la_ptot_nil_r]
      simp
    | cons b y' =>
      cases xv with
      | nil => exact absurd (zinIVs_len hx) (by simp)
      | cons c xv' =>
        cases yv with
        | nil => exact absurd (zinIVs_len hy) (by simp)
        | cons e yv' =>
          obtain ⟨h1, h2⟩ := zinIVs_cons_inv hx
          obtain ⟨g1, g2⟩ := zinIVs_cons_inv hy
          have IH := ih y' xv' yv' h2 g2
          have h1' := zinIV_iff.mp h1
          have g1' := zinIV_iff.mp g1
          have e1 : dotRA (a :: x') (b :: y') = |a * b| + dotRA x' y' := rfl
          have e3 : ptotQ (c :: xv') (e :: yv') =
              (qabs c.1 + c.2) * (qabs e.1 + e.2) + ptotQ xv' yv' := rfl
          rw [e1, e3]
          push_cast
          simp only [zqabs_cast]
          have haa : |a| ≤ |((c.1 : ℚ) : ℝ)| + ((c.2 : ℚ) : ℝ) := by
            have := abs_sub_abs_le_abs_sub a ((c.1 : ℚ) : ℝ)
            linarith
          have hbb : |b| ≤ |((e.1 : ℚ) : ℝ)| + ((e.2 : ℚ) : ℝ) := by
            have := abs_sub_abs_le_abs_sub b ((e.1 : ℚ) : ℝ)
            linarith
          have t : |a * b| ≤ (|((c.1 : ℚ) : ℝ)| + ((c.2 : ℚ) : ℝ)) *
              (|((e.1 : ℚ) : ℝ)| + ((e.2 : ℚ) : ℝ)) := by
            rw [abs_mul]
            exact mul_le_mul haa hbb (abs_nonneg _) (le_trans (abs_nonneg _) haa)
          linarith

theorem la_score_core {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) {xq y : List ℝ}
    {xqv yv : List IV} (hxq : InIVs xq xqv) (hy : InIVs y yv) (hn1 : ∀ a ∈ xqv, 0 ≤ a.2)
    (hn2 : ∀ a ∈ yv, 0 ≤ a.2) (hlen : xq.length = y.length) (h32 : xq.length ≤ 32)
    (hT : (maxAbs (xqv.map Prod.fst) + maxAbs (xqv.map Prod.snd) + 1) *
          (maxAbs (yv.map Prod.fst) + maxAbs (yv.map Prod.snd) + 1) ≤ 2 ^ 20) :
    |pdot fl xq y 0 - ((dotC (xqv.map Prod.fst) yv : ℚ) : ℝ)| ≤
      ((pErrQ xqv yv + ((xqv.length : ℚ) + 2) * ptotQ xqv yv / 2 ^ 21 + 1 / 2 ^ 60 : ℚ) : ℝ)
    ∧ 0 ≤ pErrQ xqv yv + ((xqv.length : ℚ) + 2) * ptotQ xqv yv / 2 ^ 21 + 1 / 2 ^ 60 := by
  have hbx := la_bound_iv hxq hn1
  have hby := la_bound_iv hy hn2
  have hX0 : (0 : ℝ) ≤ ((maxAbs (xqv.map Prod.fst) : ℚ) : ℝ) := by
    exact_mod_cast zmaxAbs_nonneg (xqv.map Prod.fst)
  have he10 : (0 : ℝ) ≤ ((maxAbs (xqv.map Prod.snd) : ℚ) : ℝ) := by
    exact_mod_cast zmaxAbs_nonneg (xqv.map Prod.snd)
  have hY0 : (0 : ℝ) ≤ ((maxAbs (yv.map Prod.fst) : ℚ) : ℝ) := by
    exact_mod_cast zmaxAbs_nonneg (yv.map Prod.fst)
  have he20 : (0 : ℝ) ≤ ((maxAbs (yv.map Prod.snd) : ℚ) : ℝ) := by
    exact_mod_cast zmaxAbs_nonneg (yv.map Prod.snd)
  have hT' : (((maxAbs (xqv.map Prod.fst) : ℚ) : ℝ) + ((maxAbs (xqv.map Prod.snd) : ℚ) : ℝ) + 1) *
      (((maxAbs (yv.map Prod.fst) : ℚ) : ℝ) + ((maxAbs (yv.map Prod.snd) : ℚ) : ℝ) + 1)
      ≤ 2 ^ 20 := by exact_mod_cast hT
  have key := pdot_rel u η M fl hC xq y
    (((maxAbs (xqv.map Prod.fst) : ℚ) : ℝ) + ((maxAbs (xqv.map Prod.snd) : ℚ) : ℝ) + 1)
    (((maxAbs (yv.map Prod.fst) : ℚ) : ℝ) + ((maxAbs (yv.map Prod.snd) : ℚ) : ℝ) + 1)
    hlen h32 (fun v hv => by have := hbx v hv; linarith)
    (fun v hv => by have := hby v hv; linarith) (by linarith) (by linarith) hT'
  have hdr := la_dotR_close xq y xqv yv hxq hy
  have hra := la_dotRA_le xq y xqv yv hxq hy
  have hR0 := la_dotRA_nonneg xq y
  have hxl : xq.length = xqv.length := zinIVs_len hxq
  have hp0 := la_pErr_nonneg xqv yv hn1 hn2
  have ht0 := la_ptot_nonneg xqv yv hn1 hn2
  have ht0R : (0 : ℝ) ≤ ((ptotQ xqv yv : ℚ) : ℝ) := by exact_mod_cast ht0
  have hrad0 : 0 ≤ pErrQ xqv yv + ((xqv.length : ℚ) + 2) * ptotQ xqv yv / 2 ^ 21 + 1 / 2 ^ 60 := by
    have h1 : 0 ≤ ((xqv.length : ℚ) + 2) * ptotQ xqv yv / 2 ^ 21 :=
      div_nonneg (mul_nonneg (by positivity) ht0) (by norm_num)
    have h2 : (0 : ℚ) ≤ 1 / 2 ^ 60 := by norm_num
    linarith
  refine ⟨?_, hrad0⟩
  push_cast
  rw [← hxl]
  have hu0 := hC.u0
  have hη0 := hC.h0
  have hu : u ≤ 1 / 16777216 := le_trans hC.u1 (by norm_num)
  have hn0 : (0 : ℝ) ≤ (xq.length : ℝ) := Nat.cast_nonneg _
  have hn32 : (xq.length : ℝ) ≤ 32 := by exact_mod_cast h32
  have h1 : u * (((xq.length : ℝ) + 2) * dotRA xq y) ≤
      1 / 16777216 * (((xq.length : ℝ) + 2) * dotRA xq y) :=
    mul_le_mul_of_nonneg_right hu (mul_nonneg (by linarith) hR0)
  have h2 : ((xq.length : ℝ) + 2) * dotRA xq y ≤
      ((xq.length : ℝ) + 2) * ((ptotQ xqv yv : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left hra (by linarith)
  have h4 : 0 ≤ ((xq.length : ℝ) + 2) * ((ptotQ xqv yv : ℚ) : ℝ) :=
    mul_nonneg (by linarith) ht0R
  have h3 : 200 * (xq.length : ℝ) * η ≤ 1 / 2 ^ 60 := by
    have h := mul_le_mul_of_nonneg_right hn32 hη0
    have h5 : (6400 : ℝ) * (1 / 2 ^ 149) ≤ 1 / 2 ^ 60 := by norm_num
    have h6 := hC.h1
    linarith
  obtain ⟨a1, a2⟩ := abs_le.mp key
  obtain ⟨b1, b2⟩ := abs_le.mp hdr
  rw [abs_le]
  constructor
  · first
      | linarith [a1, b1, h1, h2, h3, h4]
      | nlinarith [a1, b1, h1, h2, h3, h4]
  · first
      | linarith [a2, b2, h1, h2, h3, h4]
      | nlinarith [a2, b2, h1, h2, h3, h4]

theorem score_rel_sound : ScoreRelSound := by
  intro u η M fl hC δ hδ0 hδ1 h xq xt xqv xtv dA hdA hr hxt32 hAq hxq32 hsA hxq hBq hxt hBt hsc
  obtain ⟨hmat, hmnn⟩ := la_mat_aux hC hδ0 hδ1 hxt32 hxt hBt dA hdA h.A 0 hr (zsmallM_mem hsA)
  have hlenA := zarmat_length fl xt dA h.A 0
  have hlen : xq.length = (armat fl h.A xt dA 0).length := by rw [hlenA, hAq]
  have hxqn : ∀ a ∈ xqv, 0 ≤ a.2 := fun a ha => (hBq a ha).1
  have hsc' := hsc
  simp only [scoreOKR, Bool.and_eq_true, decide_eq_true_eq] at hsc'
  obtain ⟨hsc1, hsc2⟩ := hsc'
  have core := la_score_core hC hxq hmat hxqn hmnn hlen hxq32 hsc1
  have hmain : |pdot fl xq (armat fl h.A xt dA 0) 0 - (((scoreRel δ h xqv xtv).1 : ℚ) : ℝ)| ≤
      (((scoreRel δ h xqv xtv).2 : ℚ) : ℝ) := core.1
  have hrad : 0 ≤ (scoreRel δ h xqv xtv).2 := core.2
  refine ⟨zinIV_iff.mpr hmain, hrad, ?_⟩
  have hs2 : ((qabs (scoreRel δ h xqv xtv).1 : ℚ) : ℝ) + (((scoreRel δ h xqv xtv).2 : ℚ) : ℝ)
      ≤ 1024 := by
    exact_mod_cast hsc2
  rw [zqabs_cast] at hs2
  have h3 := abs_sub_abs_le_abs_sub (pdot fl xq (armat fl h.A xt dA 0) 0)
    (((scoreRel δ h xqv xtv).1 : ℚ) : ℝ)
  linarith [hmain]

end Lane4.Case
