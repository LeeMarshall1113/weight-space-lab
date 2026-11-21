set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedTactic false
set_option linter.flexible false
set_option linter.style.multiGoal false

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft

theorem kb_rsum_append (fl : ℝ → ℝ) : ∀ (l1 l2 : List ℝ) (acc : ℝ),
    rsum fl (l1 ++ l2) acc = rsum fl l2 (rsum fl l1 acc) := by
  intro l1
  induction l1 with
  | nil => intro l2 acc; simp [rsum]
  | cons a t ih =>
    intro l2 acc
    simp only [List.cons_append, rsum]
    exact ih l2 _

theorem kb_abs_sum_le (l : List ℝ) : |l.sum| ≤ (l.map (fun a => |a|)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.sum_cons, List.map_cons]
    have := abs_add_le a t.sum
    linarith

theorem kb_sum_const_len {α : Type*} (l : List α) (c : ℝ) :
    (l.map (fun _ => c)).sum = (l.length : ℝ) * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [ih]
    ring

theorem kb_sum_map_sub {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map f).sum - (l.map g).sum = (l.map (fun k => f k - g k)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    linarith

/-- Two-part rounded sum: a long prefix and at most three more terms. -/
theorem kb_rsum_PQ {u η M E : ℝ} {fl : ℝ → ℝ} (h : Rnd u η M fl) (hu : 0 ≤ u)
    (hu2 : u ≤ 1 / 2 ^ 24) (hη : 0 ≤ η) (hE0 : 0 ≤ E) (hE1 : E ≤ 1 / 1000) (hηE : 6 * η ≤ E)
    (P Q : List ℝ) (hQ : Q.length ≤ 3) (hP : u * (P.length : ℝ) ≤ 1 / 256)
    (hmη : (P.length : ℝ) * η ≤ E) (SPb SQb : ℝ)
    (hSP : (P.map (fun a => |a|)).sum ≤ SPb) (hSQ : (Q.map (fun a => |a|)).sum ≤ SQb)
    (hM : 101 / 100 * (2 * SPb + SQb + 2 * E) + 1 / 100 ≤ M) :
    |rsum fl (P ++ Q) 0 - (P.sum + Q.sum)| ≤ SPb * (1 / 200) + SQb * (1 / 10 ^ 6) + 4 * E := by
  have hu7 : u ≤ 1 / 10 ^ 7 := le_trans hu2 (by norm_num)
  have hm0 : (0 : ℝ) ≤ (P.length : ℝ) := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ (Q.length : ℝ) := Nat.cast_nonneg _
  have hq3 : (Q.length : ℝ) ≤ 3 := by exact_mod_cast hQ
  obtain ⟨SP, hSPd⟩ : ∃ SP : ℝ, SP = (P.map (fun a => |a|)).sum := ⟨_, rfl⟩
  obtain ⟨SQ, hSQd⟩ : ∃ SQ : ℝ, SQ = (Q.map (fun a => |a|)).sum := ⟨_, rfl⟩
  have hSP0 : 0 ≤ SP := by
    rw [hSPd]; exact lsum_nonneg P (fun a => |a|) (fun k _ => abs_nonneg k)
  have hSQ0 : 0 ≤ SQ := by
    rw [hSQd]; exact lsum_nonneg Q (fun a => |a|) (fun k _ => abs_nonneg k)
  rw [← hSPd] at hSP
  rw [← hSQd] at hSQ
  have hPs : |P.sum| ≤ SP := by rw [hSPd]; exact kb_abs_sum_le P
  have hum : u * (P.length : ℝ) * SP ≤ 1 / 256 * SP := mul_le_mul_of_nonneg_right hP hSP0
  have hQu : u * (Q.length : ℝ) ≤ 3 / 10 ^ 7 := by
    have := mul_le_mul_of_nonneg_left hq3 hu
    linarith
  have e1 := rsum_err_aux u η M fl h hu hη P 0 hP (by
    rw [← hSPd]
    simp only [abs_zero, zero_add]
    have h1 : 1 + 2 * u * (P.length : ℝ) ≤ 101 / 100 := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hSP0
    linarith)
  rw [← hSPd] at e1
  simp only [abs_zero, zero_add] at e1
  obtain ⟨a, had⟩ : ∃ a : ℝ, a = rsum fl P 0 := ⟨_, rfl⟩
  rw [← had] at e1
  have hA : |a| ≤ 2 * SP + 2 * E := by
    have h1 := abs_le.mp e1
    have h2 := abs_le.mp hPs
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hum, hmη, hSP0, hE0]
  have e2 := rsum_err_aux u η M fl h hu hη Q a (by linarith) (by
    rw [← hSQd]
    have h1 : 1 + 2 * u * (Q.length : ℝ) ≤ 101 / 100 := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (add_nonneg (abs_nonneg a) hSQ0)
    have h3 := mul_le_mul_of_nonneg_right hq3 hη
    linarith)
  rw [← hSQd] at e2
  rw [kb_rsum_append, ← had]
  have h3 := mul_le_mul_of_nonneg_right hQu (add_nonneg (abs_nonneg a) hSQ0)
  have h4 := mul_le_mul_of_nonneg_right hq3 hη
  have h5 := abs_le.mp e1
  have h6 := abs_le.mp e2
  rw [abs_le]
  constructor <;> linarith

/-- The generic comparison: old part with geometric decay, then at most three terms. -/
theorem kb_sum_cmp {u η M E : ℝ} {fl : ℝ → ℝ} (h : Rnd u η M fl) (hu : 0 ≤ u)
    (hu2 : u ≤ 1 / 2 ^ 24) (hη : 0 ≤ η) (hE0 : 0 ≤ E) (hE1 : E ≤ 1 / 1000) (hηE : 6 * η ≤ E)
    (P Q : List ℕ) (hQ : Q.length ≤ 3) (hP : u * (P.length : ℝ) ≤ 1 / 256)
    (hmη : (P.length : ℝ) * η ≤ E)
    (τ X g : ℕ → ℝ) (a b d e Ee : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hme : (P.length : ℝ) * e ≤ Ee) (hgs : (P.map g).sum ≤ 4)
    (hτP : ∀ k ∈ P, |τ k| ≤ a * g k + e) (hXP : ∀ k ∈ P, |X k| ≤ a * g k)
    (hτQ : ∀ k ∈ Q, |τ k| ≤ b) (hdQ : ∀ k ∈ Q, |τ k - X k| ≤ d)
    (hM : 101 / 100 * (2 * (4 * a + Ee) + 3 * b + 2 * E) + 1 / 100 ≤ M) :
    |rsum fl ((P ++ Q).map τ) 0 - ((P ++ Q).map X).sum|
      ≤ 9 * a + 3 * d + 4 * b * (1 / 10 ^ 6) + 2 * Ee + 4 * E := by
  have hEe : 0 ≤ Ee := le_trans (mul_nonneg (Nat.cast_nonneg _) he) hme
  have hq3 : (Q.length : ℝ) ≤ 3 := by exact_mod_cast hQ
  rw [List.map_append, List.map_append, List.sum_append]
  have hSP : ((P.map τ).map (fun a => |a|)).sum ≤ 4 * a + Ee := by
    have e1 : (P.map τ).map (fun a => |a|) = P.map (fun k => |τ k|) := by
      rw [List.map_map]; rfl
    rw [e1]
    have h1 := sum_le_aff P (fun k => |τ k|) g a e hτP
    have h2 : a * (P.map g).sum ≤ a * 4 := mul_le_mul_of_nonneg_left hgs ha
    linarith
  have hSQ : ((Q.map τ).map (fun a => |a|)).sum ≤ 3 * b := by
    have e1 : (Q.map τ).map (fun a => |a|) = Q.map (fun k => |τ k|) := by
      rw [List.map_map]; rfl
    rw [e1]
    have h1 := sum_le_aff Q (fun k => |τ k|) (fun _ => (1 : ℝ)) b 0
      (fun k hk => by
        have := hτQ k hk
        show |τ k| ≤ b * 1 + 0
        linarith)
    rw [kb_sum_const_len] at h1
    have h2 := mul_le_mul_of_nonneg_left hq3 hb
    linarith
  have hB := kb_rsum_PQ h hu hu2 hη hE0 hE1 hηE (P.map τ) (Q.map τ)
    (by rw [List.length_map]; exact hQ) (by rw [List.length_map]; exact hP)
    (by rw [List.length_map]; exact hmη) (4 * a + Ee) (3 * b) hSP hSQ hM
  have hPτ : |(P.map τ).sum| ≤ 4 * a + Ee := by
    have h1 := abs_sum_le_aff P τ g a e hτP
    have h2 : a * (P.map g).sum ≤ a * 4 := mul_le_mul_of_nonneg_left hgs ha
    linarith
  have hPX : |(P.map X).sum| ≤ 4 * a := by
    have h1 := abs_sum_le_aff P X g a 0 (fun k hk => by have := hXP k hk; linarith)
    have h2 : a * (P.map g).sum ≤ a * 4 := mul_le_mul_of_nonneg_left hgs ha
    linarith
  have hQd : |(Q.map τ).sum - (Q.map X).sum| ≤ 3 * d := by
    rw [kb_sum_map_sub]
    have h1 := abs_sum_le_aff Q (fun k => τ k - X k) (fun _ => (1 : ℝ)) d 0
      (fun k hk => by
        have := hdQ k hk
        show |τ k - X k| ≤ d * 1 + 0
        linarith)
    rw [kb_sum_const_len] at h1
    have h2 := mul_le_mul_of_nonneg_left hq3 hd
    linarith
  have hb1 := abs_le.mp hB
  have hb2 := abs_le.mp hPτ
  have hb3 := abs_le.mp hPX
  have hb4 := abs_le.mp hQd
  rw [abs_le]
  constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2, hb4.1, hb4.2, hEe, ha, hb, hd, hE0]

/-! geometric sums -/

theorem kb_geomR (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 3 / 4) (N : ℕ) :
    ∑ d ∈ Finset.range N, q ^ d ≤ 4 := by
  have key : ∀ N : ℕ, (1 - q) * ∑ d ∈ Finset.range N, q ^ d = 1 - q ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      ring
  have hS : 0 ≤ ∑ d ∈ Finset.range N, q ^ d := Finset.sum_nonneg (fun d _ => pow_nonneg h0 d)
  have := key N
  have hp : 0 ≤ q ^ N := pow_nonneg h0 N
  nlinarith [mul_nonneg hS (by linarith : (0 : ℝ) ≤ 3 / 4 - q)]

theorem kb_geom_inj (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 3 / 4) (s : Finset ℕ) (g : ℕ → ℕ)
    (inj : ∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y) :
    ∑ k ∈ s, q ^ (g k) ≤ 4 := by
  rw [← Finset.sum_image inj]
  calc ∑ d ∈ s.image g, q ^ d
      ≤ ∑ d ∈ Finset.range ((s.image g).sup id + 1), q ^ d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [Finset.mem_range]
          have : d ≤ (s.image g).sup id := Finset.le_sup (f := id) hd
          omega
        · intro d _ _
          exact pow_nonneg h0 d
    _ ≤ 4 := kb_geomR q h0 h1 _

theorem kb_geom_list (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 3 / 4) (P : List ℕ) (hnd : P.Nodup)
    (g : ℕ → ℕ) (inj : ∀ x ∈ P, ∀ y ∈ P, g x = g y → x = y) :
    (P.map (fun k => q ^ (g k))).sum ≤ 4 := by
  rw [← List.sum_toFinset _ hnd]
  apply kb_geom_inj q h0 h1
  intro x hx y hy hxy
  exact inj x (List.mem_toFinset.mp hx) y (List.mem_toFinset.mp hy) hxy

/-! splitting the sorted list -/

theorem kb_split_exists (p : ℕ) : ∀ (c : List ℕ), c.Pairwise (fun a b => a < b) →
    ∃ P Q : List ℕ, c = P ++ Q ∧ (∀ k ∈ P, k + 3 ≤ p) ∧ (∀ k ∈ Q, p < k + 3) := by
  intro c
  induction c with
  | nil => intro _; exact ⟨[], [], rfl, by simp, by simp⟩
  | cons a t ih =>
    intro hc
    rw [List.pairwise_cons] at hc
    by_cases ha : a + 3 ≤ p
    · obtain ⟨P, Q, h1, h2, h3⟩ := ih hc.2
      refine ⟨a :: P, Q, by rw [h1]; rfl, ?_, h3⟩
      intro k hk
      rcases List.mem_cons.mp hk with hk | hk
      · rw [hk]; exact ha
      · exact h2 k hk
    · refine ⟨[], a :: t, rfl, by simp, ?_⟩
      intro k hk
      rcases List.mem_cons.mp hk with hk | hk
      · rw [hk]; omega
      · have := hc.1 k hk
        omega

theorem kb_len_le_three (p : ℕ) (Q : List ℕ) (hnd : Q.Nodup) (h1 : ∀ k ∈ Q, p < k + 3)
    (h2 : ∀ k ∈ Q, k ≤ p) : Q.length ≤ 3 := by
  have hsub : Q.toFinset ⊆ Finset.Icc (p - 2) p := by
    intro k hk
    rw [List.mem_toFinset] at hk
    rw [Finset.mem_Icc]
    have := h1 k hk
    have := h2 k hk
    omega
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Nat.card_Icc] at this
  omega

/-! exponentials -/

theorem kb_exp_decay (z : ℝ) (D : ℕ) (hz : z ≤ -15 - 2 / 5 * (D : ℝ)) :
    Real.exp z ≤ 1 / 10 ^ 6 * Real.exp (-2 / 5) ^ D := by
  have h1 : Real.exp z ≤ Real.exp (-15 + (D : ℝ) * (-2 / 5)) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_add, Real.exp_nat_mul] at h1
  have h2 := exp_neg15_le
  have h3 : 0 ≤ Real.exp (-2 / 5) ^ D := pow_nonneg (Real.exp_pos _).le D
  calc Real.exp z ≤ Real.exp (-15) * Real.exp (-2 / 5) ^ D := h1
    _ ≤ 1 / 10 ^ 6 * Real.exp (-2 / 5) ^ D := mul_le_mul_of_nonneg_right h2 h3

theorem kb_q_le : Real.exp (-2 / 5) ≤ 3 / 4 := by
  have h1 := Real.add_one_le_exp (2 / 5 : ℝ)
  have h2 : Real.exp (-2 / 5) * Real.exp (2 / 5) = 1 := by
    rw [← Real.exp_add]; norm_num
  have h3 := (Real.exp_pos (-2 / 5 : ℝ)).le
  nlinarith [mul_le_mul_of_nonneg_left h1 h3]

theorem kb_wt_facts {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (he : ExpM u η ex)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2 ^ 24) (hη : 0 ≤ η) (hη2 : η ≤ 1 / 2 ^ 149)
    (x : ℝ) (hx0 : x ≤ 0) (hxM : |x| ≤ M) :
    0 ≤ ex (fl x) ∧ ex (fl x) ≤ 11 / 10 ∧ |ex (fl x) - Real.exp x| ≤ 4 / 10 ^ 6 := by
  have hu8 : u ≤ 6 / 10 ^ 8 := le_trans hu2 (by norm_num)
  have hη7 : η ≤ 1 / 10 ^ 40 := eta_tiny hη2
  have hMx := abs_le.mp hxM
  have hy0 : fl x ≤ 0 := hr.nonpos hx0 (by linarith [hMx.1])
  have herr := hr.err x hxM
  rw [abs_of_nonpos hx0] at herr
  have herr' := abs_le.mp herr
  have hey := he.err (fl x) hy0
  have hey1 : Real.exp (fl x) ≤ 1 := by
    have := Real.exp_le_exp.mpr hy0
    rwa [Real.exp_zero] at this
  have hey0 : 0 ≤ Real.exp (fl x) := (Real.exp_pos _).le
  have hey' := abs_le.mp hey
  have h4u : 4 * u * Real.exp (fl x) ≤ 4 * u * 1 :=
    mul_le_mul_of_nonneg_left hey1 (by linarith)
  have hex1 : Real.exp x ≤ 1 := by
    have := Real.exp_le_exp.mpr hx0
    rwa [Real.exp_zero] at this
  have hb2 : |Real.exp (fl x) - Real.exp x| ≤ 3 / 10 ^ 6 := by
    by_cases hx20 : -x ≤ 20
    · have hδ' : |fl x - x| ≤ u * 20 + η := by
        refine le_trans herr ?_
        have := mul_le_mul_of_nonneg_left hx20 hu
        linarith
      have hδ1 : |fl x - x| ≤ 1 := by linarith
      have h3 := Real.abs_exp_sub_one_le hδ1
      have h4 : Real.exp (fl x) = Real.exp x * Real.exp (fl x - x) := by
        rw [← Real.exp_add]; congr 1; ring
      have h5 : Real.exp (fl x) - Real.exp x = Real.exp x * (Real.exp (fl x - x) - 1) := by
        rw [h4]; ring
      rw [h5, abs_mul, abs_of_pos (Real.exp_pos x)]
      have h6 := mul_le_mul hex1 h3 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      linarith
    · have hx20' : x ≤ -20 := by linarith
      have hfx : fl x ≤ -15 := by
        have h1 := mul_le_mul_of_nonneg_left hx20' (by linarith : (0 : ℝ) ≤ 1 - u)
        have h2 := herr'.2
        linarith
      have h1 := exp_neg15_le
      have h2 : Real.exp (fl x) ≤ Real.exp (-15) := Real.exp_le_exp.mpr hfx
      have h3 : Real.exp x ≤ Real.exp (-15) := Real.exp_le_exp.mpr (by linarith)
      have h4 := (Real.exp_pos x).le
      rw [abs_le]; constructor <;> linarith
  refine ⟨he.nonneg _, ?_, ?_⟩
  · linarith [hey'.2, hey1, h4u, hu8, hη7]
  · have hb2' := abs_le.mp hb2
    rw [abs_le]
    constructor <;> linarith [hey'.1, hey'.2, hb2'.1, hb2'.2, h4u, hu8, hη7]

theorem kb_wt_decay {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (he : ExpM u η ex)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2 ^ 24) (hη : 0 ≤ η) (hη2 : η ≤ 1 / 2 ^ 149)
    (x : ℝ) (D : ℕ) (hxD : x ≤ -16 - (D : ℝ) / 2) (hxM : |x| ≤ M) :
    ex (fl x) ≤ 11 / 10 * (1 / 10 ^ 6 * Real.exp (-2 / 5) ^ D) + η ∧
    Real.exp x ≤ 1 / 10 ^ 6 * Real.exp (-2 / 5) ^ D := by
  have hu7 : u ≤ 1 / 10 ^ 7 := le_trans hu2 (by norm_num)
  have hη7 : η ≤ 1 / 10 ^ 40 := eta_tiny hη2
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hx0 : x ≤ 0 := by linarith
  have herr := hr.err x hxM
  rw [abs_of_nonpos hx0] at herr
  have herr' := (abs_le.mp herr).2
  have hp1 := mul_le_mul_of_nonneg_left hxD (by linarith : (0 : ℝ) ≤ 1 - u)
  have hp2 := mul_le_mul_of_nonneg_right (by linarith : u ≤ 1 / 5) hD0
  have hy : fl x ≤ -15 - 2 / 5 * (D : ℝ) := by linarith
  have hy0 : fl x ≤ 0 := by linarith
  have hE := kb_exp_decay (fl x) D hy
  have hey := (abs_le.mp (he.err (fl x) hy0)).2
  have hey0 : 0 ≤ Real.exp (fl x) := (Real.exp_pos _).le
  have hq : 0 ≤ Real.exp (-2 / 5) ^ D := pow_nonneg (Real.exp_pos _).le D
  have hT : 0 ≤ 1 / 10 ^ 6 * Real.exp (-2 / 5) ^ D := by positivity
  have h2 : 4 * u * Real.exp (fl x) ≤ 1 / 10 * Real.exp (fl x) :=
    mul_le_mul_of_nonneg_right (by linarith) hey0
  refine ⟨by linarith, kb_exp_decay x D (by linarith)⟩

theorem kb_quot {Nh Zh N Z dN dZ B : ℝ} (hZ : 1 ≤ Z) (hZh : 9 / 10 ≤ Zh) (hB : 0 ≤ B)
    (hN : |N| ≤ B * Z) (h1 : |Nh - N| ≤ dN) (h2 : |Zh - Z| ≤ dZ) :
    |Nh / Zh - N / Z| ≤ 10 / 9 * (dN + B * dZ) := by
  have hZ0 : 0 < Z := by linarith
  have hZh0 : 0 < Zh := by linarith
  have hZne : Z ≠ 0 := hZ0.ne'
  have hZhne : Zh ≠ 0 := hZh0.ne'
  have hdN : 0 ≤ dN := le_trans (abs_nonneg _) h1
  have hdZ : 0 ≤ dZ := le_trans (abs_nonneg _) h2
  have e : Nh / Zh - N / Z = ((Nh - N) * Z - N * (Zh - Z)) / (Zh * Z) := by
    rw [div_sub_div _ _ hZhne hZne]; ring
  have hpos : 0 < Zh * Z := mul_pos hZh0 hZ0
  rw [e, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have a1 : |(Nh - N) * Z| ≤ dN * Z := by
    rw [abs_mul, abs_of_pos hZ0]
    exact mul_le_mul_of_nonneg_right h1 hZ0.le
  have a2 : |N * (Zh - Z)| ≤ B * Z * dZ := by
    rw [abs_mul]
    exact mul_le_mul hN h2 (abs_nonneg _) (mul_nonneg hB hZ0.le)
  have a3 := abs_le.mp a1
  have a4 := abs_le.mp a2
  have a5 : |(Nh - N) * Z - N * (Zh - Z)| ≤ dN * Z + B * Z * dZ := by
    rw [abs_le]; constructor <;> linarith [a3.1, a3.2, a4.1, a4.2]
  have hT : 0 ≤ (dN + B * dZ) * Z := mul_nonneg (add_nonneg hdN (mul_nonneg hB hdZ)) hZ0.le
  have a6 := mul_nonneg hT (by linarith : (0 : ℝ) ≤ 10 / 9 * Zh - 1)
  nlinarith [a5, a6]

theorem kb_final {u η M B E : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu : 0 ≤ u)
    (hu7 : u ≤ 1 / 10 ^ 7) (hη : 0 ≤ η) (hηE : 6 * η ≤ E) (hE0 : 0 ≤ E)
    (hE9 : E ≤ 1 / 10 ^ 9) (hE90 : 40 * E ≤ 1 / 2 ^ 90) (hB0 : 0 ≤ B) (hM : 4 * B + 4 ≤ M)
    (Nh Zh N Z : ℝ) (hZ1 : 1 ≤ Z) (hNZ : |N| ≤ B * Z)
    (hZe : |Zh - Z| ≤ 9 * (11 / 10 * (1 / 10 ^ 6)) + 3 * (4 / 10 ^ 6)
      + 4 * (11 / 10) * (1 / 10 ^ 6) + 2 * E + 4 * E)
    (hNe : |Nh - N| ≤ 9 * (12 / 10 ^ 7 * B) + 3 * (5 / 10 ^ 6 * B + η)
      + 4 * (12 / 10 * B + η) * (1 / 10 ^ 6) + 2 * (2 * (B + 1) * E) + 4 * E) :
    |fl (Nh / Zh) - N / Z| ≤ B / 2 ^ 13 + 1 / 2 ^ 90 ∧ fl (fl (Nh / Zh)) = fl (Nh / Zh) := by
  have hBE : B * E ≤ B * (1 / 10 ^ 9) := mul_le_mul_of_nonneg_left hE9 hB0
  have hZe' : |Zh - Z| ≤ 3 / 10 ^ 5 := by linarith
  have hNe' : |Nh - N| ≤ 31 / 10 ^ 6 * B + 9 * E := by linarith
  have hZh : 9 / 10 ≤ Zh := by
    have := abs_le.mp hZe'
    linarith [this.1]
  have hq := kb_quot hZ1 hZh hB0 hNZ hNe' hZe'
  have hZ0 : 0 < Z := by linarith
  have hNZ' : |N / Z| ≤ B := by
    rw [abs_div, abs_of_pos hZ0, div_le_iff₀ hZ0]
    exact hNZ
  have hqB : |Nh / Zh| ≤ 11 / 10 * B + 10 * E := by
    have h1 := abs_le.mp hq
    have h2 := abs_le.mp hNZ'
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hxM : 11 / 10 * B + 10 * E ≤ M := by linarith
  have hfl := hr.abs hu hqB hxM
  have hu1 : u * (11 / 10 * B + 10 * E) ≤ 1 / 10 ^ 7 * (11 / 10 * B + 10 * E) :=
    mul_le_mul_of_nonneg_right hu7 (by linarith)
  refine ⟨?_, hr.idem _ (le_trans hqB hxM)⟩
  have h1 := abs_le.mp hfl
  have h2 := abs_le.mp hq
  rw [show (2 : ℝ) ^ 13 = 8192 by norm_num]
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hu1, hE90, hηE, hE0, hB0, hη]

set_option maxHeartbeats 4000000 in
theorem savg_arith : SavgArith := by
  unfold SavgArith
  intro u η M fl ex hr he hu hu2 hη hη2 c hsort n hcn hun hηn s f p hp hcp hdec Sb hSb hSbM B hB hBM
  obtain ⟨E, hEd⟩ : ∃ E : ℝ, E = 1 / 2 ^ 100 := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hEd]; positivity
  have hE9 : E ≤ 1 / 10 ^ 9 := by rw [hEd]; norm_num
  have hE90 : 40 * E ≤ 1 / 2 ^ 90 := by rw [hEd]; norm_num
  have hηE : 6 * η ≤ E := by
    have h1 : 6 * η ≤ 6 * (1 / 2 ^ 149) := by linarith
    have h2 : (6 : ℝ) * (1 / 2 ^ 149) ≤ E := by rw [hEd]; norm_num
    linarith
  rw [← hEd] at hηn
  have hu7 : u ≤ 1 / 10 ^ 7 := le_trans hu2 (by norm_num)
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB p hp)
  have hcne : c ≠ [] := List.ne_nil_of_mem hp
  obtain ⟨j0, hj0, hsm⟩ := smax_mem s c hcne
  have hsmge := smax_ge s c
  have hSm : |smax s c| ≤ Sb := by rw [hsm]; exact hSb j0 hj0
  have hxM : ∀ k ∈ c, |s k - smax s c| ≤ M := by
    intro k hk
    have h1 := abs_le.mp (hSb k hk)
    have h2 := abs_le.mp hSm
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- splitting
  obtain ⟨P, Q, hcPQ, hP3, hQ3⟩ := kb_split_exists p c hsort
  have hsort2 : (P ++ Q).Pairwise (fun a b => a < b) := by rw [← hcPQ]; exact hsort
  obtain ⟨hsP, hsQ, _⟩ := List.pairwise_append.mp hsort2
  have hndP : P.Nodup := by
    unfold List.Nodup
    exact hsP.imp (fun h => ne_of_lt h)
  have hndQ : Q.Nodup := by
    unfold List.Nodup
    exact hsQ.imp (fun h => ne_of_lt h)
  have hndc : c.Nodup := by
    unfold List.Nodup
    exact hsort.imp (fun h => ne_of_lt h)
  have hmemP : ∀ k ∈ P, k ∈ c := fun k hk => by
    rw [hcPQ]; exact List.mem_append_left _ hk
  have hmemQ : ∀ k ∈ Q, k ∈ c := fun k hk => by
    rw [hcPQ]; exact List.mem_append_right _ hk
  have hQlen : Q.length ≤ 3 := kb_len_le_three p Q hndQ hQ3 (fun k hk => hcp k (hmemQ k hk))
  have hlenPQ : P.length + Q.length ≤ n := by
    have := hcn
    rw [hcPQ, List.length_append] at this
    exact this
  have hmn : (P.length : ℝ) ≤ n := by
    exact_mod_cast (le_trans (Nat.le_add_right _ _) hlenPQ)
  have hP : u * (P.length : ℝ) ≤ 1 / 256 := le_trans (mul_le_mul_of_nonneg_left hmn hu) hun
  have hmη : (P.length : ℝ) * η ≤ E := by
    have := mul_le_mul_of_nonneg_right hmn hη
    linarith
  -- weights
  have hwf : ∀ k ∈ c, 0 ≤ swt fl ex c s k ∧ swt fl ex c s k ≤ 11 / 10 ∧
      |swt fl ex c s k - Real.exp (s k - smax s c)| ≤ 4 / 10 ^ 6 := by
    intro k hk
    exact kb_wt_facts hr he hu hu2 hη hη2 (s k - smax s c)
      (by linarith [hsmge k hk]) (hxM k hk)
  have hW0 : ∀ k, 0 ≤ Real.exp (s k - smax s c) := fun k => (Real.exp_pos _).le
  have hq0 : 0 ≤ Real.exp (-2 / 5) := (Real.exp_pos _).le
  have hqle := kb_q_le
  have hdecP : ∀ k ∈ P,
      swt fl ex c s k ≤ 11 / 10 * (1 / 10 ^ 6 * Real.exp (-2 / 5) ^ (p - (k + 3))) + η ∧
      Real.exp (s k - smax s c) ≤ 1 / 10 ^ 6 * Real.exp (-2 / 5) ^ (p - (k + 3)) := by
    intro k hk
    have hkc := hmemP k hk
    have hk3 := hP3 k hk
    have hD : ((p - (k + 3) : ℕ) : ℝ) = (p : ℝ) - k - 3 := by
      rw [Nat.cast_sub hk3]; push_cast; ring
    have h1 := hdec k hkc hk3
    have h2 := hsmge p hp
    have hx : s k - smax s c ≤ -16 - ((p - (k + 3) : ℕ) : ℝ) / 2 := by
      rw [hD]; linarith
    exact kb_wt_decay hr he hu hu2 hη hη2 (s k - smax s c) (p - (k + 3)) hx (hxM k hkc)
  have hgs : (P.map (fun k => Real.exp (-2 / 5) ^ (p - (k + 3)))).sum ≤ 4 :=
    kb_geom_list _ hq0 hqle P hndP (fun k => p - (k + 3)) (by
      intro x hx y hy hxy
      have h1 := hP3 x hx
      have h2 := hP3 y hy
      beta_reduce at hxy
      omega)
  -- denominator comparison
  have hZτP : ∀ k ∈ P, |swt fl ex c s k|
      ≤ 11 / 10 * (1 / 10 ^ 6) * Real.exp (-2 / 5) ^ (p - (k + 3)) + η := by
    intro k hk
    obtain ⟨hw0, _, _⟩ := hwf k (hmemP k hk)
    have := (hdecP k hk).1
    rw [abs_of_nonneg hw0]
    linarith
  have hZXP : ∀ k ∈ P, |Real.exp (s k - smax s c)|
      ≤ 11 / 10 * (1 / 10 ^ 6) * Real.exp (-2 / 5) ^ (p - (k + 3)) := by
    intro k hk
    have h1 := (hdecP k hk).2
    have hG0 : 0 ≤ Real.exp (-2 / 5) ^ (p - (k + 3)) := pow_nonneg hq0 _
    rw [abs_of_nonneg (hW0 k)]
    linarith
  have hZτQ : ∀ k ∈ Q, |swt fl ex c s k| ≤ 11 / 10 := by
    intro k hk
    obtain ⟨hw0, hw1, _⟩ := hwf k (hmemQ k hk)
    rw [abs_of_nonneg hw0]; exact hw1
  have hZdQ : ∀ k ∈ Q, |swt fl ex c s k - Real.exp (s k - smax s c)| ≤ 4 / 10 ^ 6 :=
    fun k hk => (hwf k (hmemQ k hk)).2.2
  have hMden : 101 / 100 * (2 * (4 * (11 / 10 * (1 / 10 ^ 6)) + E) + 3 * (11 / 10) + 2 * E)
      + 1 / 100 ≤ M := by
    linarith
  have hZc := kb_sum_cmp hr hu hu2 hη hE0.le (by linarith) hηE P Q hQlen hP hmη
    (swt fl ex c s) (fun k => Real.exp (s k - smax s c))
    (fun k => Real.exp (-2 / 5) ^ (p - (k + 3)))
    (11 / 10 * (1 / 10 ^ 6)) (11 / 10) (4 / 10 ^ 6) η E (by norm_num) (by norm_num)
    (by norm_num) hη hmη hgs hZτP hZXP hZτQ hZdQ hMden
  rw [← hcPQ] at hZc
  -- numerator comparison
  have hNτP : ∀ k ∈ P, |fl (swt fl ex c s k * f k)|
      ≤ 12 / 10 ^ 7 * B * Real.exp (-2 / 5) ^ (p - (k + 3)) + 2 * (B + 1) * η := by
    intro k hk
    have hkc := hmemP k hk
    obtain ⟨hw0, hw1, _⟩ := hwf k hkc
    have hwd := (hdecP k hk).1
    have hG0 : 0 ≤ Real.exp (-2 / 5) ^ (p - (k + 3)) := pow_nonneg hq0 _
    have hfB := hB k hkc
    have hx : |swt fl ex c s k * f k| ≤ swt fl ex c s k * B := by
      rw [abs_mul, abs_of_nonneg hw0]
      exact mul_le_mul_of_nonneg_left hfB hw0
    have hwB1 : swt fl ex c s k * B ≤ 11 / 10 * B := mul_le_mul_of_nonneg_right hw1 hB0
    have hbd := hr.bound hu hx (by linarith)
    have h1 : u * (swt fl ex c s k * B) ≤ 1 / 10 ^ 7 * (swt fl ex c s k * B) :=
      mul_le_mul_of_nonneg_right hu7 (mul_nonneg hw0 hB0)
    have h2 : swt fl ex c s k * B
        ≤ (11 / 10 * (1 / 10 ^ 6 * Real.exp (-2 / 5) ^ (p - (k + 3))) + η) * B :=
      mul_le_mul_of_nonneg_right hwd hB0
    have h3 : 0 ≤ Real.exp (-2 / 5) ^ (p - (k + 3)) * B := mul_nonneg hG0 hB0
    have h4 : 0 ≤ η * B := mul_nonneg hη hB0
    linarith
  have hNXP : ∀ k ∈ P, |Real.exp (s k - smax s c) * f k|
      ≤ 12 / 10 ^ 7 * B * Real.exp (-2 / 5) ^ (p - (k + 3)) := by
    intro k hk
    have hkc := hmemP k hk
    have h1 := (hdecP k hk).2
    have hG0 : 0 ≤ Real.exp (-2 / 5) ^ (p - (k + 3)) := pow_nonneg hq0 _
    have hfB := hB k hkc
    rw [abs_mul, abs_of_nonneg (hW0 k)]
    have h2 := mul_le_mul_of_nonneg_left hfB (hW0 k)
    have h3 := mul_le_mul_of_nonneg_right h1 hB0
    have h4 : 0 ≤ Real.exp (-2 / 5) ^ (p - (k + 3)) * B := mul_nonneg hG0 hB0
    linarith
  have hNτQ : ∀ k ∈ Q, |fl (swt fl ex c s k * f k)| ≤ 12 / 10 * B + η := by
    intro k hk
    have hkc := hmemQ k hk
    obtain ⟨hw0, hw1, _⟩ := hwf k hkc
    have hfB := hB k hkc
    have hx : |swt fl ex c s k * f k| ≤ swt fl ex c s k * B := by
      rw [abs_mul, abs_of_nonneg hw0]
      exact mul_le_mul_of_nonneg_left hfB hw0
    have hwB1 : swt fl ex c s k * B ≤ 11 / 10 * B := mul_le_mul_of_nonneg_right hw1 hB0
    have hbd := hr.bound hu hx (by linarith)
    have h1 : u * (swt fl ex c s k * B) ≤ 1 / 10 ^ 7 * (swt fl ex c s k * B) :=
      mul_le_mul_of_nonneg_right hu7 (mul_nonneg hw0 hB0)
    linarith
  have hNdQ : ∀ k ∈ Q, |fl (swt fl ex c s k * f k) - Real.exp (s k - smax s c) * f k|
      ≤ 5 / 10 ^ 6 * B + η := by
    intro k hk
    have hkc := hmemQ k hk
    obtain ⟨hw0, hw1, hwd⟩ := hwf k hkc
    have hfB := hB k hkc
    have hx : |swt fl ex c s k * f k| ≤ swt fl ex c s k * B := by
      rw [abs_mul, abs_of_nonneg hw0]
      exact mul_le_mul_of_nonneg_left hfB hw0
    have hwB1 : swt fl ex c s k * B ≤ 11 / 10 * B := mul_le_mul_of_nonneg_right hw1 hB0
    have h1 := hr.abs hu hx (by linarith)
    have h1' : u * (swt fl ex c s k * B) ≤ 1 / 10 ^ 7 * (swt fl ex c s k * B) :=
      mul_le_mul_of_nonneg_right hu7 (mul_nonneg hw0 hB0)
    have h2 : |swt fl ex c s k * f k - Real.exp (s k - smax s c) * f k| ≤ 4 / 10 ^ 6 * B := by
      have e : swt fl ex c s k * f k - Real.exp (s k - smax s c) * f k
          = (swt fl ex c s k - Real.exp (s k - smax s c)) * f k := by ring
      rw [e, abs_mul]
      exact mul_le_mul hwd hfB (abs_nonneg _) (by norm_num)
    have h3 := abs_le.mp h1
    have h4 := abs_le.mp h2
    rw [abs_le]
    constructor <;> linarith
  have hmeN : (P.length : ℝ) * (2 * (B + 1) * η) ≤ 2 * (B + 1) * E := by
    have := mul_le_mul_of_nonneg_left hmη (by linarith : (0 : ℝ) ≤ 2 * (B + 1))
    linarith
  have hMnum : 101 / 100 * (2 * (4 * (12 / 10 ^ 7 * B) + 2 * (B + 1) * E)
      + 3 * (12 / 10 * B + η) + 2 * E) + 1 / 100 ≤ M := by
    have hBE : B * E ≤ B * (1 / 10 ^ 9) := mul_le_mul_of_nonneg_left hE9 hB0
    linarith
  have hNc := kb_sum_cmp hr hu hu2 hη hE0.le (by linarith) hηE P Q hQlen hP hmη
    (fun j => fl (swt fl ex c s j * f j)) (fun k => Real.exp (s k - smax s c) * f k)
    (fun k => Real.exp (-2 / 5) ^ (p - (k + 3)))
    (12 / 10 ^ 7 * B) (12 / 10 * B + η) (5 / 10 ^ 6 * B + η) (2 * (B + 1) * η)
    (2 * (B + 1) * E) (mul_nonneg (by norm_num) hB0) (by linarith) (by linarith)
    (mul_nonneg (by linarith) hη) hmeN hgs hNτP hNXP hNτQ hNdQ hMnum
  rw [← hcPQ] at hNc
  -- the exact quotient
  have hZ1 : 1 ≤ (c.map (fun k => Real.exp (s k - smax s c))).sum := by
    have h0 := sum_split (fun k => Real.exp (s k - smax s c)) j0 c hndc hj0
    have h1 : Real.exp (s j0 - smax s c) = 1 := by rw [hsm, sub_self, Real.exp_zero]
    have h2 := lsum_nonneg (c.filter (fun k => decide (k ≠ j0)))
      (fun k => Real.exp (s k - smax s c)) (fun k _ => (Real.exp_pos _).le)
    linarith
  have hNZ : |(c.map (fun k => Real.exp (s k - smax s c) * f k)).sum|
      ≤ B * (c.map (fun k => Real.exp (s k - smax s c))).sum := by
    have := abs_sum_le_aff c (fun k => Real.exp (s k - smax s c) * f k)
      (fun k => Real.exp (s k - smax s c)) B 0 (fun k hk => by
        show |Real.exp (s k - smax s c) * f k| ≤ B * Real.exp (s k - smax s c) + 0
        rw [abs_mul, abs_of_nonneg (hW0 k)]
        have := mul_le_mul_of_nonneg_left (hB k hk) (hW0 k)
        linarith)
    linarith
  have hpt : ∀ k, Real.exp (s k) = Real.exp (smax s c) * Real.exp (s k - smax s c) := fun k => by
    rw [← Real.exp_add]; congr 1; ring
  have hEN : (c.map (fun k => Real.exp (s k) * f k)).sum
      = Real.exp (smax s c) * (c.map (fun k => Real.exp (s k - smax s c) * f k)).sum := by
    rw [← List.sum_map_mul_left]
    exact congrArg List.sum (List.map_congr_left (fun k _ => by
      show Real.exp (s k) * f k = Real.exp (smax s c) * (Real.exp (s k - smax s c) * f k)
      rw [hpt k]; ring))
  have hEZ : (c.map (fun k => Real.exp (s k))).sum
      = Real.exp (smax s c) * (c.map (fun k => Real.exp (s k - smax s c))).sum := by
    rw [← List.sum_map_mul_left]
    exact congrArg List.sum (List.map_congr_left (fun k _ => by
      show Real.exp (s k) = Real.exp (smax s c) * Real.exp (s k - smax s c)
      exact hpt k))
  have hAe : eavg c s f = (c.map (fun k => Real.exp (s k - smax s c) * f k)).sum
      / (c.map (fun k => Real.exp (s k - smax s c))).sum := by
    unfold eavg
    rw [hEN, hEZ, mul_div_mul_left _ _ (Real.exp_pos _).ne']
  have hsv : savg fl ex c s f = fl (rsum fl (c.map (fun j => fl (swt fl ex c s j * f j))) 0
      / rsum fl (c.map (swt fl ex c s)) 0) := rfl
  rw [hsv, hAe]
  exact kb_final hr hu hu7 hη hηE hE0.le hE9 hE90 hB0 hBM _ _ _ _ hZ1 hNZ hZc hNc

end Lane4.Case
