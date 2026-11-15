/-
Lane 4, rung 5 lemma kit, part 2: rounded sums and the softmax lemmas.

Assembled by tools/r5_assemble.py from kit cases proved by Sonnet doctors and checked by
the same checker as every other case (runs/r5-kit/kA2, kB). Fixed by the lane; doctors do
not edit this file. What you need from it is at the END of the file: `soft_near` and
`soft_zeros` (and `rsum_err`, `geom_dist` if you sum things yourself).
-/
import Lane4.RSoft

namespace Lane4.RSoft
open Lane4.RSeq

-- ===== statements (kit case specs) =====
open Lane4.RSeq Lane4.RSoft

/-- Left-to-right rounded summation is close to the exact sum. Range condition: twice the
total magnitude (plus the underflow terms) stays within `M`. -/
def RsumErr : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Rnd u η M fl → 0 ≤ u → 0 ≤ η →
  ∀ (l : List ℝ) (acc : ℝ), u * (l.length : ℝ) ≤ 1 / 256 →
    2 * (|acc| + (l.map (fun a => |a|)).sum) + 2 * (l.length : ℝ) * η ≤ M →
    |rsum fl l acc - (acc + l.sum)|
      ≤ 101 / 100 * u * (l.length : ℝ) * (|acc| + (l.map (fun a => |a|)).sum)
        + 2 * (l.length : ℝ) * η

/-- A geometric sum over the distances to `j` in a duplicate-free list of naturals. -/
def GeomDist : Prop :=
  ∀ (c : List ℕ), c.Nodup → ∀ (j : ℕ) (q : ℝ), 0 ≤ q → q ≤ 1 / 2 →
    ((c.filter (fun k => decide (k ≠ j))).map (fun k => q ^ ndist j k)).sum ≤ 4 * q

/-- Softmax attention with a clear winner returns the winner's value, up to a small error.
Key `j` beats every other candidate `k` by a score gap of at least 16 per unit of
distance `|j - k|`. `B` bounds the values, `Sb` the scores, `n` the number of candidates.
Range conditions: `2 * Sb ≤ M` and `4 * B + 4 ≤ M`. -/
def SavgNear : Prop :=
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Rnd u η M fl → ExpM u η ex →
  0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  ∀ (c : List ℕ), c.Nodup → ∀ n : ℕ, c.length ≤ n →
  u * (n : ℝ) ≤ 1 / 256 → η * (n : ℝ) ≤ 1 / 2 ^ 100 →
  ∀ (s f : ℕ → ℝ) (j : ℕ), j ∈ c →
  (∀ k ∈ c, k ≠ j → s k ≤ s j - 16 * (ndist j k : ℝ)) →
  ∀ Sb : ℝ, (∀ k ∈ c, |s k| ≤ Sb) → 2 * Sb ≤ M →
  ∀ B : ℝ, (∀ k ∈ c, |f k| ≤ B) → 4 * B + 4 ≤ M →
    |savg fl ex c s f - f j| ≤ B / 100 + 1 / 2 ^ 90
      ∧ fl (savg fl ex c s f) = savg fl ex c s f

/-- If every candidate's value is exactly 0, the attention output is exactly 0. -/
def SavgZeros : Prop :=
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Rnd u η M fl →
  ∀ (c : List ℕ) (s f : ℕ → ℝ), (∀ k ∈ c, f k = 0) → savg fl ex c s f = 0

-- ===== kA2: rounded sums, geometric distance sum =====
set_option linter.unusedVariables false
set_option linter.style.longLine false

open Lane4.RSeq Lane4.RSoft

theorem rsum_err_aux (u η M : ℝ) (fl : ℝ → ℝ) (h : Rnd u η M fl) (hu : 0 ≤ u) (hη : 0 ≤ η)
    (l : List ℝ) :
    ∀ (acc : ℝ), u * (l.length : ℝ) ≤ 1 / 256 →
    (1 + 2 * u * (l.length : ℝ)) * (|acc| + (l.map (fun a => |a|)).sum)
      + 2 * (l.length : ℝ) * η ≤ M →
    |rsum fl l acc - (acc + l.sum)|
      ≤ 101 / 100 * u * (l.length : ℝ) * (|acc| + (l.map (fun a => |a|)).sum)
        + 2 * (l.length : ℝ) * η := by
  induction l with
  | nil =>
    intro acc _ _
    simp [rsum]
  | cons a l ih =>
    intro acc hlen hM
    simp only [rsum, List.length_cons, Nat.cast_add, Nat.cast_one, List.sum_cons,
      List.map_cons] at hlen hM ⊢
    set n' : ℝ := (l.length : ℝ) with hn'
    have hn'0 : 0 ≤ n' := Nat.cast_nonneg _
    have hun' : u * n' ≤ 1 / 256 := by nlinarith
    set S' : ℝ := (l.map (fun a => |a|)).sum with hS'
    have hS0 : 0 ≤ S' := by
      rw [hS']
      apply List.sum_nonneg
      intro x hx
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      exact abs_nonneg _
    set A : ℝ := |acc| + |a| with hA
    have hA0 : 0 ≤ A := by positivity
    have hacc : |acc + a| ≤ A := abs_add_le _ _
    have hg1 : 0 ≤ u * n' := mul_nonneg hu hn'0
    have hnη : 0 ≤ n' * η := mul_nonneg hn'0 hη
    have hAM : A ≤ M := by
      have e : |acc| + (|a| + S') = A + S' := by rw [hA]; ring
      rw [e] at hM
      nlinarith [mul_nonneg hg1 hA0, mul_nonneg hg1 hS0]
    have h1 : |fl (acc + a) - (acc + a)| ≤ u * A + η := h.abs hu hacc hAM
    have h2 : |fl (acc + a)| ≤ (1 + u) * A + η := by
      have h3 := abs_add_le (fl (acc + a) - (acc + a)) (acc + a)
      have h4 : fl (acc + a) - (acc + a) + (acc + a) = fl (acc + a) := by ring
      rw [h4] at h3
      nlinarith [mul_nonneg hu hA0]
    set k : ℝ := 101 / 100 * u * n' with hk
    have hk0 : 0 ≤ k := by positivity
    have hk1 : k ≤ 1 / 100 := by rw [hk]; nlinarith
    have h5 : k * |fl (acc + a)| ≤ k * ((1 + u) * A + η) :=
      mul_le_mul_of_nonneg_left h2 hk0
    -- range hypothesis for the induction hypothesis
    have hMi : (1 + 2 * u * n') * (|fl (acc + a)| + S') + 2 * n' * η ≤ M := by
      have e : |acc| + (|a| + S') = A + S' := by rw [hA]; ring
      rw [e] at hM
      have g2 : 0 ≤ 2 - (1 + 2 * u * n') := by linarith
      have p1 := mul_nonneg (mul_nonneg hu hA0) g2
      have p2 := mul_nonneg hη g2
      have p3 := mul_nonneg hu hS0
      have p4 : (1 + 2 * u * n') * |fl (acc + a)|
          ≤ (1 + 2 * u * n') * ((1 + u) * A + η) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      nlinarith [p1, p2, p3, p4]
    have ih' := ih (fl (acc + a)) hun' hMi
    have h6 : |rsum fl l (fl (acc + a)) - (acc + (a + l.sum))| ≤
        |rsum fl l (fl (acc + a)) - (fl (acc + a) + l.sum)| + |fl (acc + a) - (acc + a)| := by
      have := abs_add_le (rsum fl l (fl (acc + a)) - (fl (acc + a) + l.sum))
        (fl (acc + a) - (acc + a))
      have e : rsum fl l (fl (acc + a)) - (fl (acc + a) + l.sum) + (fl (acc + a) - (acc + a))
          = rsum fl l (fl (acc + a)) - (acc + (a + l.sum)) := by ring
      rw [e] at this
      exact this
    have h7 := mul_nonneg (mul_nonneg hu hA0) (by linarith : (0:ℝ) ≤ 101 / 100 - 1 - k)
    have h8 := mul_nonneg hη (by linarith : (0:ℝ) ≤ 1 - k)
    have h9 := mul_nonneg (mul_nonneg hu hS0) (by norm_num : (0:ℝ) ≤ 101 / 100)
    have e2 : |acc| + (|a| + S') = A + S' := by rw [hA]; ring
    rw [e2]
    have e3 : 101 / 100 * u * (n' + 1) * (A + S') = k * (A + S') + 101 / 100 * u * (A + S') := by
      rw [hk]; ring
    rw [e3]
    nlinarith [h1, h5, h6, ih', h7, h8, h9, mul_nonneg hk0 hS0]

theorem rsum_err : RsumErr := by
  intro u η M fl h hu hη l acc hlen hM
  apply rsum_err_aux u η M fl h hu hη l acc hlen
  have hS0 : 0 ≤ (l.map (fun a => |a|)).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg _
  have hT : 0 ≤ |acc| + (l.map (fun a => |a|)).sum := by positivity
  have hg : 1 + 2 * u * (l.length : ℝ) ≤ 2 := by nlinarith
  nlinarith [mul_nonneg hT (by linarith : (0:ℝ) ≤ 2 - (1 + 2 * u * (l.length : ℝ)))]


theorem geom_Icc (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1 / 2) (M : ℕ) :
    ∑ d ∈ Finset.Icc 1 M, q ^ d ≤ 2 * q := by
  have key : ∀ M : ℕ, (1 - q) * ∑ d ∈ Finset.Icc 1 M, q ^ d = q - q ^ (M + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
      ring
  have hS : 0 ≤ ∑ d ∈ Finset.Icc 1 M, q ^ d :=
    Finset.sum_nonneg (fun d _ => pow_nonneg h0 d)
  have := key M
  have hp : 0 ≤ q ^ (M + 1) := pow_nonneg h0 _
  nlinarith [mul_nonneg hS (by linarith : (0:ℝ) ≤ 1 / 2 - q)]

theorem geom_side (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1 / 2) (s : Finset ℕ) (g : ℕ → ℕ)
    (inj : ∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y) (pos : ∀ x ∈ s, 1 ≤ g x) :
    ∑ k ∈ s, q ^ (g k) ≤ 2 * q := by
  rw [← Finset.sum_image inj]
  calc ∑ d ∈ s.image g, q ^ d
      ≤ ∑ d ∈ Finset.Icc 1 ((s.image g).sup id), q ^ d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [Finset.mem_Icc]
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
          exact ⟨pos x hx, Finset.le_sup (f := id) hd⟩
        · intro d _ _
          exact pow_nonneg h0 d
    _ ≤ 2 * q := geom_Icc q h0 h1 _

theorem geom_dist : GeomDist := by
  intro c hc j q h0 h1
  have hnd : (c.filter (fun k => decide (k ≠ j))).Nodup := hc.filter _
  rw [← List.sum_toFinset _ hnd]
  set s := (c.filter (fun k => decide (k ≠ j))).toFinset with hs
  have hsj : ∀ k ∈ s, k ≠ j := by
    intro k hk
    rw [hs, List.mem_toFinset, List.mem_filter] at hk
    simpa using hk.2
  rw [← Finset.sum_filter_add_sum_filter_not s (fun k => k < j)]
  have e1 : ∑ k ∈ s.filter (fun k => k < j), q ^ ndist j k
      = ∑ k ∈ s.filter (fun k => k < j), q ^ (j - k) := by
    apply Finset.sum_congr rfl
    intro k hk
    have : k < j := (Finset.mem_filter.mp hk).2
    have : ndist j k = j - k := by unfold ndist; omega
    rw [this]
  have e2 : ∑ k ∈ s.filter (fun k => ¬ k < j), q ^ ndist j k
      = ∑ k ∈ s.filter (fun k => ¬ k < j), q ^ (k - j) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    have := hsj k hk'.1
    have : ndist j k = k - j := by unfold ndist; omega
    rw [this]
  rw [e1, e2]
  have a1 := geom_side q h0 h1 (s.filter (fun k => k < j)) (fun k => j - k)
    (by
      intro x hx y hy hxy
      have := (Finset.mem_filter.mp hx).2
      have := (Finset.mem_filter.mp hy).2
      beta_reduce at hxy
      omega)
    (by
      intro x hx
      have := (Finset.mem_filter.mp hx).2
      beta_reduce
      omega)
  have a2 := geom_side q h0 h1 (s.filter (fun k => ¬ k < j)) (fun k => k - j)
    (by
      intro x hx y hy hxy
      have hx' := Finset.mem_filter.mp hx
      have hy' := Finset.mem_filter.mp hy
      have := hsj x hx'.1
      have := hsj y hy'.1
      beta_reduce at hxy
      omega)
    (by
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      have := hsj x hx'.1
      beta_reduce
      omega)
  linarith

-- ===== kB: softmax =====
open Lane4.RSeq Lane4.RSoft

theorem rsum_zero_of {u η M : ℝ} {fl : ℝ → ℝ} (h : Rnd u η M fl) (l : List ℝ)
    (hl : ∀ a ∈ l, a = 0) : rsum fl l 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ha : a = 0 := hl a (by simp)
    subst ha
    simp only [rsum, add_zero, h.zero]
    exact ih (fun b hb => hl b (List.mem_cons_of_mem _ hb))

theorem savg_zeros : SavgZeros := by
  unfold SavgZeros
  intro u η M fl ex h c s f hf
  unfold savg
  have h1 : rsum fl (c.map (fun j => fl (swt fl ex c s j * f j))) 0 = 0 := by
    apply rsum_zero_of h
    intro a ha
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
    rw [hf k hk, mul_zero, h.zero]
  rw [h1, zero_div, h.zero]

theorem sum_split (g : ℕ → ℝ) (j : ℕ) (c : List ℕ) (hnd : c.Nodup) (hj : j ∈ c) :
    (c.map g).sum = g j + ((c.filter (fun k => decide (k ≠ j))).map g).sum := by
  induction c with
  | nil => simp at hj
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    by_cases ha : a = j
    · have hf : t.filter (fun k => decide (k ≠ j)) = t := by
        rw [List.filter_eq_self]
        intro x hx
        have hxj : x ≠ j := fun hxj => hnd.1 (by rw [ha, ← hxj]; exact hx)
        simpa using hxj
      have hc : ¬ (decide (a ≠ j) = true) := by simp [ha]
      rw [List.filter_cons, if_neg hc, hf, ha]
      simp
    · have hjt : j ∈ t := by
        rcases List.mem_cons.mp hj with h | h
        · exact absurd h.symm ha
        · exact h
      have h1 := ih hnd.2 hjt
      have hc : decide (a ≠ j) = true := by simp [ha]
      rw [List.filter_cons, if_pos hc]
      simp only [List.map_cons, List.sum_cons]
      rw [h1]
      ring

theorem sum_le_aff {α : Type*} (l : List α) (f g : α → ℝ) (A η : ℝ)
    (h : ∀ k ∈ l, f k ≤ A * g k + η) :
    (l.map f).sum ≤ A * (l.map g).sum + (l.length : ℝ) * η := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun k hk => h k (List.mem_cons_of_mem _ hk))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem abs_sum_le_aff {α : Type*} (l : List α) (f g : α → ℝ) (A η : ℝ)
    (h : ∀ k ∈ l, |f k| ≤ A * g k + η) :
    |(l.map f).sum| ≤ A * (l.map g).sum + (l.length : ℝ) * η := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun k hk => h k (List.mem_cons_of_mem _ hk))
    have h3 := abs_add_le (f a) ((t.map f).sum)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem lsum_nonneg {α : Type*} (l : List α) (g : α → ℝ) (h : ∀ k ∈ l, 0 ≤ g k) :
    0 ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun k hk => h k (List.mem_cons_of_mem _ hk))
    linarith

theorem abs_sum_eq (l : List ℝ) (h : ∀ a ∈ l, 0 ≤ a) :
    (l.map (fun a => |a|)).sum = l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [abs_of_nonneg (h a (by simp)), ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem pow_small {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ∀ d : ℕ, 1 ≤ d → q ^ d ≤ q := by
  intro d hd
  induction d with
  | zero => omega
  | succ e ih =>
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he; simp
    · have h2 := ih (by omega)
      rw [pow_succ]
      have h3 := mul_le_mul_of_nonneg_right (le_trans h2 h1) h0
      linarith

theorem exp_neg15_le : Real.exp (-15) ≤ 1 / 10 ^ 6 := by
  have h1 : (1 : ℝ) + 15 / 100 ≤ Real.exp (15 / 100) := by
    have := Real.add_one_le_exp (15 / 100 : ℝ)
    linarith
  have h2 : ((1 : ℝ) + 15 / 100) ^ 100 ≤ Real.exp (15 / 100) ^ 100 := by gcongr
  have h3 : Real.exp 15 = Real.exp (15 / 100) ^ 100 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h4 : (10 : ℝ) ^ 6 ≤ Real.exp 15 := by
    rw [h3]; refine le_trans ?_ h2; norm_num
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by positivity) h4

theorem div_step (N Z fj B e : ℝ) (hZ : |Z - 1| ≤ 4 / 1000)
    (hN : |N - fj| ≤ 4 / 1000 * B + e)
    (hfj : |fj| ≤ B) (hB : 0 ≤ B) (he : 0 ≤ e) :
    |N / Z - fj| ≤ 81 / 10000 * B + 2 * e := by
  have hZ' := abs_le.mp hZ
  have hZpos : 996 / 1000 ≤ Z := by linarith [hZ'.1]
  have hZp : 0 < Z := by linarith
  have hZne : Z ≠ 0 := ne_of_gt hZp
  have h1 : |N - fj * Z| ≤ 8 / 1000 * B + e := by
    have e1 : N - fj * Z = (N - fj) + fj * (1 - Z) := by ring
    have e2 : |fj * (1 - Z)| ≤ B * (4 / 1000) := by
      rw [abs_mul]
      have : |1 - Z| ≤ 4 / 1000 := by rw [abs_sub_comm]; exact hZ
      exact mul_le_mul hfj this (abs_nonneg _) hB
    have e3 := abs_add_le (N - fj) (fj * (1 - Z))
    rw [← e1] at e3
    linarith
  have h2 : N / Z - fj = (N - fj * Z) / Z := by field_simp
  rw [h2, abs_div, abs_of_pos hZp, div_le_iff₀ hZp]
  have h3 := mul_le_mul_of_nonneg_left hZpos
    (by linarith : (0 : ℝ) ≤ 81 / 10000 * B + 2 * e)
  linarith

theorem savg_near : RsumErr → GeomDist → SavgNear := by
  intro hR hG
  unfold SavgNear
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
  have hq := exp_neg15_le
  have hq0 : 0 ≤ Real.exp (-15) := (Real.exp_pos _).le
  have hqh : Real.exp (-15) ≤ 1 / 2 := le_trans hq (by norm_num)
  have hnd1 : ∀ k, k ≠ j → 1 ≤ ndist j k := by
    intro k hk
    unfold ndist
    omega
  have hwk : ∀ k ∈ c, k ≠ j → w k ≤ (1 + 4 * u) * Real.exp (-15) ^ (ndist j k) + η := by
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
    have hy : 16 * (ndist j k : ℝ) ≤ -(s k - s j) := by linarith
    have hprod := mul_nonneg (sub_nonneg.mpr hy) (by linarith : (0 : ℝ) ≤ 1 - u)
    have hud := mul_le_mul_of_nonneg_right hu6 (show (0 : ℝ) ≤ (ndist j k : ℝ) by linarith)
    have hflx : fl (s k - s j) ≤ -15 * (ndist j k : ℝ) := by
      linarith [hup, hprod, hud, hη1, hE6]
    have hexp : Real.exp (fl (s k - s j)) ≤ Real.exp (-15) ^ (ndist j k) := by
      have h3 : Real.exp (fl (s k - s j)) ≤ Real.exp (((ndist j k : ℕ) : ℝ) * (-15)) :=
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
      have h2 := pow_small hq0 (by linarith : Real.exp (-15) ≤ 1) (ndist j k) (hnd1 k hkj)
      have h3 : (1 + 4 * u) * Real.exp (-15) ^ (ndist j k) ≤ (1 + 4 * u) * Real.exp (-15) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      have h4 : (1 + 4 * u) * Real.exp (-15) ≤ 2 * (1 / 10 ^ 6) :=
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
  have hGeom : (F.map (fun k => Real.exp (-15) ^ ndist j k)).sum ≤ 4 * Real.exp (-15) := by
    rw [hFdef]
    exact hG c hnd j _ hq0 hqh
  have hL : (F.map w).sum ≤ (1 + 4 * u) * (4 * Real.exp (-15)) + E := by
    have h1 := sum_le_aff F w (fun k => Real.exp (-15) ^ ndist j k) (1 + 4 * u) η
      (fun k hk => hwk k (hF k hk).1 (hF k hk).2)
    have h2 := mul_le_mul_of_nonneg_left hGeom (by linarith : (0 : ℝ) ≤ 1 + 4 * u)
    linarith
  have hL1 : (F.map w).sum ≤ 1 / 10 ^ 5 := by
    have h1 : (1 + 4 * u) * (4 * Real.exp (-15)) ≤ 2 * (4 * (1 / 10 ^ 6)) :=
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
    have huL : u * L ≤ 1 / 10 ^ 6 * (1 / 10 ^ 5) := mul_le_mul hu6 hL1 hL0 (by norm_num)
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
  have hAL : (1 + u) * B * L ≤ 2 / 10 ^ 5 * B := by
    have huL : u * L ≤ 1 / 10 ^ 6 * (1 / 10 ^ 5) := mul_le_mul hu6 hL1 hL0 (by norm_num)
    have h : (1 + u) * L ≤ 2 / 10 ^ 5 := by linarith [huL]
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

-- ===== what doctors use =====

/-- SOFTMAX WITH A CLEAR WINNER. Candidates `c` (no duplicates, at most `n` of them), scores
`s`, values `f`. If key `j ∈ c` beats every other candidate `k` by at least
`16 * |j - k|` in score, then the head's output is within `B / 100 + 1 / 2^90` of the
winner's value `f j`, and it is unchanged by rounding it again.
`Sb` bounds the scores (`2 * Sb ≤ M`), `B` bounds the values (`4 * B + 4 ≤ M`). -/
theorem soft_near {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (he : ExpM u η ex)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2 ^ 149)
    {c : List ℕ} (hc : c.Nodup) {n : ℕ} (hlen : c.length ≤ n)
    (hn : u * (n : ℝ) ≤ 1 / 256) (hnη : η * (n : ℝ) ≤ 1 / 2 ^ 100)
    {s f : ℕ → ℝ} {j : ℕ} (hj : j ∈ c)
    (hgap : ∀ k ∈ c, k ≠ j → s k ≤ s j - 16 * (ndist j k : ℝ))
    {Sb : ℝ} (hS : ∀ k ∈ c, |s k| ≤ Sb) (hSM : 2 * Sb ≤ M)
    {B : ℝ} (hB : ∀ k ∈ c, |f k| ≤ B) (hBM : 4 * B + 4 ≤ M) :
    |savg fl ex c s f - f j| ≤ B / 100 + 1 / 2 ^ 90
      ∧ fl (savg fl ex c s f) = savg fl ex c s f :=
  savg_near rsum_err geom_dist u η M fl ex hr he hu0 hu hη0 hη c hc n hlen hn hnη s f j hj hgap
    Sb hS hSM B hB hBM

/-- SOFTMAX OVER ZERO VALUES. If every candidate's value is exactly 0, the head's output is
exactly 0, whatever the scores are. -/
theorem soft_zeros {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) {c : List ℕ}
    {s f : ℕ → ℝ} (h : ∀ k ∈ c, f k = 0) : savg fl ex c s f = 0 :=
  savg_zeros u η M fl ex hr c s f h

end Lane4.RSoft
