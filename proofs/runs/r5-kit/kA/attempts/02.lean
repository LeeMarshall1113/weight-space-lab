set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft

theorem rsum_err : RsumErr := by
  intro u η fl h hu hη l
  induction l with
  | nil =>
    intro acc _
    simp [rsum]
  | cons a l ih =>
    intro acc hlen
    simp only [rsum, List.length_cons, Nat.cast_add, Nat.cast_one, List.sum_cons,
      List.map_cons] at hlen ⊢
    set n' : ℝ := (l.length : ℝ) with hn'
    have hn'0 : 0 ≤ n' := Nat.cast_nonneg _
    have hun' : u * n' ≤ 1 / 256 := by nlinarith
    have ih' := ih (fl (acc + a)) hun'
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
    have h1 : |fl (acc + a) - (acc + a)| ≤ u * A + η := h.abs hu hacc
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

end Lane4.Case
