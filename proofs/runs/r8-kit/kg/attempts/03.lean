set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.multiGoal false
set_option linter.unusedTactic false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

namespace Lane4.Case
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.R7K2

/-! ### list helpers -/

theorem gd_range : ∀ (n k : ℕ), k < n → (List.range n).getD k 0 = k := by
  intro n
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    rw [List.range_succ_eq_map]
    cases k with
    | zero => simp
    | succ k =>
      rw [List.getD_cons_succ, Lane4.R8KA.k_getD_map Nat.succ 0 0 (List.range n) k (by simpa using hk)]
      rw [ih k (by omega)]

theorem gd_map_range {α : Type} (g : ℕ → α) (d : α) (n k : ℕ) (hk : k < n) :
    ((List.range n).map g).getD k d = g k := by
  rw [Lane4.R8KA.k_getD_map g 0 d (List.range n) k (by simpa using hk), gd_range n k hk]

theorem gd_zipWith {α β γ : Type} (f : α → β → γ) (da : α) (db : β) (dg : γ) :
    ∀ (a : List α) (b : List β) (j : ℕ), j < a.length → j < b.length →
      (List.zipWith f a b).getD j dg = f (a.getD j da) (b.getD j db)
  | [], b, j, h1, h2 => by simp at h1
  | x :: a, [], j, h1, h2 => by simp at h2
  | x :: a, y :: b, 0, h1, h2 => by simp
  | x :: a, y :: b, j + 1, h1, h2 => by
      simp only [List.zipWith_cons_cons, List.getD_cons_succ]
      exact gd_zipWith f da db dg a b j (by simpa using h1) (by simpa using h2)

theorem allSome_spec {α : Type} (d : α) : ∀ (l : List (Option α)) (r : List α),
    allSome l = some r →
    r.length = l.length ∧ ∀ i, i < l.length → l.getD i none = some (r.getD i d)
  | [], r, h => by
      simp [allSome] at h
      subst h
      exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | none :: l, r, h => by simp [allSome] at h
  | some a :: l, r, h => by
      cases hl : allSome l with
      | none => simp [allSome, hl] at h
      | some r' =>
        simp [allSome, hl] at h
        subst h
        obtain ⟨h1, h2⟩ := allSome_spec d l r' hl
        refine ⟨by simp [h1], ?_⟩
        intro i hi
        cases i with
        | zero => simp
        | succ i =>
          simp only [List.getD_cons_succ]
          exact h2 i (by simpa using hi)

theorem mem_otherRanks {n ref k : ℕ} : k ∈ otherRanks n ref ↔ k < n ∧ k ≠ ref := by
  unfold otherRanks
  rw [List.mem_filter, List.mem_range]
  simp

theorem otherRanks_nodup (n ref : ℕ) : (otherRanks n ref).Nodup := by
  unfold otherRanks
  exact List.Nodup.filter _ (by simp [List.nodup_range])

theorem otherRanks_len_le (n ref : ℕ) (h : ref < n) : (otherRanks n ref).length + 1 ≤ n := by
  have hnd := otherRanks_nodup n ref
  have hsub : (otherRanks n ref).toFinset ⊆ (Finset.range n).erase ref := by
    intro k hk
    rw [List.mem_toFinset, mem_otherRanks] at hk
    rw [Finset.mem_erase, Finset.mem_range]
    exact ⟨hk.2, hk.1⟩
  have h1 := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Finset.card_erase_of_mem (Finset.mem_range.mpr h),
    Finset.card_range] at h1
  omega

theorem fmax_aux : ∀ (L : List ℚ) (m0 : ℚ),
    m0 ≤ L.foldl max m0 ∧ ∀ a ∈ L, a ≤ L.foldl max m0
  | [], m0 => by simp
  | b :: L, m0 => by
      have ih := fmax_aux L (max m0 b)
      simp only [List.foldl_cons]
      refine ⟨le_trans (le_max_left _ _) ih.1, ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact le_trans (le_max_right _ _) ih.1
      · exact ih.2 a ha

/-! ### sums -/

theorem lsum_add {α : Type} (l : List α) (f g : α → ℝ) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem lsum_sub {α : Type} (l : List α) (f g : α → ℝ) :
    (l.map (fun x => f x - g x)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem lsum_mul_right {α : Type} (l : List α) (f : α → ℝ) (c : ℝ) :
    (l.map (fun x => f x * c)).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem lsum_congr {α : Type} (l : List α) (f g : α → ℝ) (h : ∀ x ∈ l, f x = g x) :
    (l.map f).sum = (l.map g).sum := by
  rw [List.map_congr_left h]

theorem coord_alg (N : ℕ) (a cW fW : ℕ → ℝ) (cref fref R : ℝ)
    (ha0 : ∀ j, 0 ≤ a j) (hA : ((List.range N).map a).sum ≤ 1)
    (hr : |fref - cref| ≤ R) (hj : ∀ j, j < N → |fW j - cW j| ≤ R) :
    |(fref + ((List.range N).map (fun j => a j * (fW j - fref))).sum)
      - (cref + ((List.range N).map (fun j => a j * (cW j - cref))).sum)| ≤ R := by
  have hA0 : 0 ≤ ((List.range N).map a).sum := by
    apply List.sum_nonneg
    intro y hy
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hy
    exact ha0 k
  have hS : |((List.range N).map (fun j => a j * (fW j - cW j))).sum|
      ≤ R * ((List.range N).map a).sum :=
    Lane4.R8KD.lc_abs_bound a (fun j => fW j - cW j) R ha0 (List.range N)
      (fun k hk => hj k (List.mem_range.mp hk))
  have e1 : ((List.range N).map (fun j => a j * (fW j - fref))).sum
      - ((List.range N).map (fun j => a j * (cW j - cref))).sum
      = ((List.range N).map (fun j => a j * (fW j - cW j))).sum
        - ((List.range N).map a).sum * (fref - cref) := by
    rw [← lsum_sub]
    have : ((List.range N).map (fun j => a j * (fW j - cW j))).sum
        - ((List.range N).map a).sum * (fref - cref)
        = ((List.range N).map (fun j => a j * (fW j - cW j) - a j * (fref - cref))).sum := by
      rw [lsum_sub, lsum_mul_right]
    rw [this]
    apply lsum_congr
    intro j _
    ring
  have e2 : (fref + ((List.range N).map (fun j => a j * (fW j - fref))).sum)
      - (cref + ((List.range N).map (fun j => a j * (cW j - cref))).sum)
      = (fref - cref) + (((List.range N).map (fun j => a j * (fW j - fref))).sum
      - ((List.range N).map (fun j => a j * (cW j - cref))).sum) := by ring
  rw [e2, e1]
  obtain ⟨h1, h2⟩ := abs_le.mp hr
  obtain ⟨h3, h4⟩ := abs_le.mp hS
  rw [abs_le]
  have p1 := mul_nonneg (sub_nonneg.mpr hA) (show 0 ≤ R - (fref - cref) by linarith)
  have p2 := mul_nonneg (sub_nonneg.mpr hA) (show 0 ≤ R + (fref - cref) by linarith)
  constructor <;> nlinarith [p1, p2]

theorem weights_symbols (N : ℕ) (mid rad a : ℕ → ℝ)
    (h : ∀ j, j < N → mid j - rad j ≤ a j ∧ a j ≤ mid j + rad j) :
    ∃ e' : ℕ → ℝ, (∀ k, |e' k| ≤ 1) ∧ ∀ j, j < N → a j = mid j + rad j * e' j := by
  refine ⟨fun j => if j < N then (a j - mid j) / rad j else 0, ?_, ?_⟩
  · intro k
    dsimp only
    by_cases hk : k < N
    · rw [if_pos hk]
      obtain ⟨h1, h2⟩ := h k hk
      have hr0 : 0 ≤ rad k := by linarith
      rcases hr0.lt_or_eq with hpos | hz
      · have ht : rad k * ((a k - mid k) / rad k) = a k - mid k := by
          field_simp
        rw [abs_le]
        constructor <;> nlinarith
      · rw [← hz]; simp
    · rw [if_neg hk]; simp
  · intro j hj
    dsimp only
    rw [if_pos hj]
    obtain ⟨h1, h2⟩ := h j hj
    have hr0 : 0 ≤ rad j := by linarith
    rcases hr0.lt_or_eq with hpos | hz
    · have ht : rad j * ((a j - mid j) / rad j) = a j - mid j := by
        field_simp
      linarith
    · have ha : a j = mid j := by linarith
      rw [← hz, ha]; ring

/-! ### affine forms -/

theorem linVal_replicate_append (pre : ℕ) (l : List ℚ) (e : ℕ → ℝ) :
    ∀ k, linVal (List.replicate pre 0 ++ l) e k = linVal l e (k + pre) := by
  induction pre with
  | zero => intro k; simp
  | succ p ih =>
    intro k
    have h1 := ih (k + 1)
    rw [List.replicate_succ, List.cons_append]
    calc linVal ((0 : ℚ) :: (List.replicate p 0 ++ l)) e k
        = ((0 : ℚ) : ℝ) * e k + linVal (List.replicate p 0 ++ l) e (k + 1) := rfl
      _ = linVal l e (k + (p + 1)) := by
        rw [h1, Rat.cast_zero, zero_mul, zero_add]
        rw [show k + 1 + p = k + (p + 1) by omega]

theorem linVal_sum (e e' : ℕ → ℝ) : ∀ (l : List ℚ) (k : ℕ),
    (∀ j, j < l.length → e (k + j) = e' j) →
    linVal l e k = ((List.range l.length).map (fun j => ((l.getD j 0 : ℚ) : ℝ) * e' j)).sum := by
  intro l
  induction l generalizing e' with
  | nil => intro k _; simp [linVal]
  | cons a l ih =>
    intro k hk
    have h0 : e k = e' 0 := by simpa using hk 0 (by simp)
    have h1 := ih (fun j => e' (j + 1)) (k + 1) (by
      intro j hj
      have := hk (j + 1) (by simpa using hj)
      rw [show k + 1 + j = k + (j + 1) by omega]
      exact this)
    calc linVal (a :: l) e k = ((a : ℚ) : ℝ) * e k + linVal l e (k + 1) := rfl
      _ = ((a : ℚ) : ℝ) * e' 0
          + ((List.range l.length).map (fun j => ((l.getD j 0 : ℚ) : ℝ) * e' (j + 1))).sum := by
        rw [h0, h1]
      _ = ((List.range (a :: l).length).map
            (fun j => (((a :: l).getD j 0 : ℚ) : ℝ) * e' j)).sum := by
        rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
        have hz : ((a : ℚ) : ℝ) * e' 0 = (((a :: l).getD 0 0 : ℚ) : ℝ) * e' 0 := by simp
        rw [hz]
        try (congr 1; apply lsum_congr; intro j _; simp [Function.comp, List.getD_cons_succ])

theorem foldr_add_cast : ∀ (l : List ℚ),
    ((l.foldr (fun a s => a + s) 0 : ℚ) : ℝ) = (l.map (fun a => ((a : ℚ) : ℝ))).sum
  | [] => by simp
  | a :: l => by
      simp only [List.foldr_cons, Rat.cast_add, List.map_cons, List.sum_cons, foldr_add_cast l]

theorem af_centre (ws : List (ℚ × ℚ)) (diffs : List ℚ) (hl : ws.length = diffs.length)
    (vref : ℚ) (pre : ℕ) (e a e' : ℕ → ℝ)
    (hmid : ∀ j, j < ws.length →
      a j = ((((ws.getD j (0, 0)).1 + (ws.getD j (0, 0)).2) / 2 : ℚ) : ℝ)
        + ((((ws.getD j (0, 0)).2 - (ws.getD j (0, 0)).1) / 2 : ℚ) : ℝ) * e' j)
    (he : ∀ j, j < ws.length → e (pre + j) = e' j) :
    ((vref + (List.zipWith (fun (w : ℚ × ℚ) (d : ℚ) => (w.1 + w.2) / 2 * d) ws diffs).foldr
        (fun a s => a + s) 0 : ℚ) : ℝ)
      + linVal (List.replicate pre 0 ++
          List.zipWith (fun (w : ℚ × ℚ) (d : ℚ) => (w.2 - w.1) / 2 * d) ws diffs) e 0
    = (vref : ℝ) + ((List.range ws.length).map
        (fun j => a j * ((diffs.getD j 0 : ℚ) : ℝ))).sum := by
  have hlen1 : (List.zipWith (fun (w : ℚ × ℚ) (d : ℚ) => (w.1 + w.2) / 2 * d) ws diffs).length
      = ws.length := by
    rw [List.length_zipWith]; omega
  have hlen2 : (List.zipWith (fun (w : ℚ × ℚ) (d : ℚ) => (w.2 - w.1) / 2 * d) ws diffs).length
      = ws.length := by
    rw [List.length_zipWith]; omega
  have hc1 : (((List.zipWith (fun (w : ℚ × ℚ) (d : ℚ) => (w.1 + w.2) / 2 * d) ws diffs).foldr
        (fun a s => a + s) 0 : ℚ) : ℝ)
      = ((List.range ws.length).map (fun j =>
          ((((ws.getD j (0, 0)).1 + (ws.getD j (0, 0)).2) / 2 : ℚ) : ℝ)
            * ((diffs.getD j 0 : ℚ) : ℝ))).sum := by
    rw [foldr_add_cast, ← Lane4.R8KD.lc_sum_getD (0 : ℚ) _ (fun q : ℚ => (q : ℝ)), hlen1]
    apply lsum_congr
    intro j hj
    have hj' := List.mem_range.mp hj
    rw [gd_zipWith (fun (w : ℚ × ℚ) (d : ℚ) => (w.1 + w.2) / 2 * d) (0, 0) 0 0 ws diffs j hj'
      (by omega)]
    push_cast
    try ring
  have hc2 : linVal (List.replicate pre 0 ++
          List.zipWith (fun (w : ℚ × ℚ) (d : ℚ) => (w.2 - w.1) / 2 * d) ws diffs) e 0
      = ((List.range ws.length).map (fun j =>
          ((((ws.getD j (0, 0)).2 - (ws.getD j (0, 0)).1) / 2 : ℚ) : ℝ)
            * ((diffs.getD j 0 : ℚ) : ℝ) * e' j)).sum := by
    rw [linVal_replicate_append, Nat.zero_add,
      linVal_sum e e' _ pre (by intro j hj; rw [hlen2] at hj; exact he j hj)]
    rw [hlen2]
    apply lsum_congr
    intro j hj
    have hj' := List.mem_range.mp hj
    rw [gd_zipWith (fun (w : ℚ × ℚ) (d : ℚ) => (w.2 - w.1) / 2 * d) (0, 0) 0 0 ws diffs j hj'
      (by omega)]
    push_cast
    try ring
  rw [Rat.cast_add, hc1, hc2, add_assoc, ← lsum_add]
  congr 1
  apply lsum_congr
  intro j hj
  have hj' := List.mem_range.mp hj
  try dsimp only
  rw [hmid j hj']
  ring

/-! ### positions in a window -/

theorem dec_idx : ∀ (P : List ℕ), P.Pairwise (fun a b => b < a) →
    ∀ a b : ℕ, a < b → b < P.length → P.getD b 0 < P.getD a 0
  | [], _, a, b, _, hb => by simp at hb
  | x :: P', hP, a, b, hab, hb => by
      obtain ⟨hx, hP'⟩ := List.pairwise_cons.mp hP
      cases a with
      | zero =>
        cases b with
        | zero => omega
        | succ b =>
          simp only [List.getD_cons_succ, List.getD_cons_zero]
          exact hx _ (zgetD_mem' 0 P' b (by simpa using hb))
      | succ a =>
        cases b with
        | zero => omega
        | succ b =>
          simp only [List.getD_cons_succ]
          exact dec_idx P' hP' a b (by omega) (by simpa using hb)

theorem dec_le {P : List ℕ} (hP : P.Pairwise (fun a b => b < a)) {a b : ℕ} (hab : a ≤ b)
    (hb : b < P.length) : P.getD b 0 ≤ P.getD a 0 := by
  rcases Nat.lt_or_ge a b with h | h
  · exact (dec_idx P hP a b h hb).le
  · have : a = b := by omega
    subst this
    exact le_refl _

theorem dec_sum {P : List ℕ} (hP : P.Pairwise (fun a b => b < a)) :
    ∀ a, a < P.length → P.getD a 0 + a ≤ P.getD 0 0 := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    have h1 := dec_idx P hP a (a + 1) (by omega) ha
    have h2 := ih (by omega)
    omega

theorem dec_inj {P : List ℕ} (hP : P.Pairwise (fun a b => b < a)) {a b : ℕ}
    (ha : a < P.length) (hb : b < P.length) (h : P.getD a 0 = P.getD b 0) : a = b := by
  rcases Nat.lt_trichotomy a b with h1 | h1 | h1
  · have := dec_idx P hP a b h1 hb
    omega
  · exact h1
  · have := dec_idx P hP b a h1 ha
    omega

theorem mem_getD_idx : ∀ (P : List ℕ) (k : ℕ), k ∈ P → ∃ a, a < P.length ∧ P.getD a 0 = k
  | [], k, h => by simp at h
  | x :: P', k, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨0, by simp, by simp⟩
      · obtain ⟨a, ha, hk⟩ := mem_getD_idx P' k h'
        exact ⟨a + 1, by simpa using ha, by simpa using hk⟩

theorem pos_top_max {m : Mask} {cd : List Bool} {tok : ℕ → ℕ} {n i : ℕ} {P : List ℕ} {c : List ℕ}
    (hW : WinPos m cd tok n i P) (hlen : 0 < P.length)
    (hc : ∀ k, k ∈ c → k ∈ cand m n i ∧ cd.getD (tok k) false = true) :
    ∀ k ∈ c, k ≤ P.getD 0 0 := by
  obtain ⟨hP1, hP2, hP3⟩ := hW
  intro k hk
  obtain ⟨hk1, hk2⟩ := hc k hk
  by_cases hkP : k ∈ P
  · obtain ⟨a, ha, rfl⟩ := mem_getD_idx P k hkP
    exact dec_le hP1 (Nat.zero_le a) ha
  · exact (hP3 k hk1 hk2 hkP (P.getD 0 0) (zgetD_mem' 0 P 0 hlen)).le

theorem pos_tail {m : Mask} {cd : List Bool} {tok : ℕ → ℕ} {n i : ℕ} {P : List ℕ} {c : List ℕ}
    (hW : WinPos m cd tok n i P) (hlen : 0 < P.length)
    (hc : ∀ k, k ∈ c → k ∈ cand m n i ∧ cd.getD (tok k) false = true) :
    ∀ k ∈ c, k ∉ P → k + P.length ≤ P.getD 0 0 := by
  obtain ⟨hP1, hP2, hP3⟩ := hW
  intro k hk hkP
  obtain ⟨hk1, hk2⟩ := hc k hk
  have h1 := hP3 k hk1 hk2 hkP (P.getD (P.length - 1) 0) (zgetD_mem' 0 P (P.length - 1) (by omega))
  have h2 := dec_sum hP1 (P.length - 1) (by omega)
  omega

theorem cand_iff (m : Mask) (hm : m ≠ Mask.all) (n i : ℕ) :
    ∃ bd, i ≤ bd ∧ bd ≤ i + 1 ∧ ∀ k, k ∈ cand m n i ↔ k < bd := by
  cases m with
  | all => exact absurd rfl hm
  | causal => exact ⟨i + 1, by omega, by omega, fun k => by simp [cand]⟩
  | strict => exact ⟨i, by omega, by omega, fun k => by simp [cand]⟩

theorem cand_le {m : Mask} (hm : m ≠ Mask.all) {n i k : ℕ} (hk : k ∈ cand m n i) : k ≤ i := by
  cases m with
  | all => exact absurd rfl hm
  | causal => simp [cand] at hk; omega
  | strict => simp [cand] at hk; omega

theorem pos_dense {m : Mask} {cd : List Bool} {tok : ℕ → ℕ} {n i : ℕ} {P : List ℕ} (bd : ℕ)
    (hbd : ∀ k, k ∈ cand m n i ↔ k < bd)
    (hd : ∀ k ∈ cand m n i, cd.getD (tok k) false = true)
    (hW : WinPos m cd tok n i P) (hlen : 0 < P.length) :
    (∀ a, a < P.length → P.getD a 0 + a = P.getD 0 0) ∧ bd ≤ P.getD 0 0 + 1 := by
  obtain ⟨hP1, hP2, hP3⟩ := hW
  have hmem : ∀ a, a < P.length → P.getD a 0 ∈ P := fun a ha => zgetD_mem' 0 P a ha
  have hlt : ∀ a, a < P.length → P.getD a 0 < bd :=
    fun a ha => (hbd _).mp (hP2 _ (hmem a ha)).1
  have key : ∀ k, k < bd → ∀ b, b < P.length → P.getD b 0 ≤ k → k ∈ P := by
    intro k hk b hb hbk
    by_contra hkP
    have := hP3 k ((hbd k).mpr hk) (hd k ((hbd k).mpr hk)) hkP (P.getD b 0) (hmem b hb)
    omega
  constructor
  · intro a
    induction a with
    | zero => intro _; simp
    | succ a ih =>
      intro ha
      have h1 := dec_idx P hP1 a (a + 1) (by omega) ha
      have h2 := ih (by omega)
      have h3 : P.getD a 0 ≤ P.getD (a + 1) 0 + 1 := by
        by_contra hcon
        have hk : P.getD (a + 1) 0 + 1 < bd := by
          have := hlt a (by omega)
          omega
        have hkP := key (P.getD (a + 1) 0 + 1) hk (a + 1) ha (by omega)
        obtain ⟨b, hb, hbk⟩ := mem_getD_idx P _ hkP
        rcases Nat.lt_or_ge a b with hab | hab
        · have := dec_le hP1 (show a + 1 ≤ b by omega) hb
          omega
        · have := dec_le hP1 hab (show a < P.length by omega)
          omega
      omega
  · by_contra hcon
    have hk : P.getD 0 0 + 1 < bd := by omega
    have hkP := key (P.getD 0 0 + 1) hk 0 hlen (by omega)
    obtain ⟨b, hb, hbk⟩ := mem_getD_idx P _ hkP
    have := dec_le hP1 (Nat.zero_le b) hb
    omega

theorem pw_range : ∀ n : ℕ, (List.range n).Pairwise (fun a b => a < b) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.pairwise_append]
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_range, List.mem_singleton] at ha hb
    omega

theorem pw_cand (m : Mask) (n i : ℕ) : (cand m n i).Pairwise (fun a b => a < b) := by
  cases m <;> simp only [cand] <;> exact pw_range _

theorem cands_pairwise (h : AHead) (fl : ℝ → ℝ) (dg : ℕ → ℝ) (dgb : ℝ) (n : ℕ) (x : ℕ → Vec)
    (i : ℕ) : (h.cands fl dg dgb n x i).Pairwise (fun a b => a < b) := by
  unfold AHead.cands
  exact List.Pairwise.sublist List.filter_sublist (pw_cand h.mask n i)

theorem cands_len (h : AHead) (fl : ℝ → ℝ) (dg : ℕ → ℝ) (dgb : ℝ) (n : ℕ) (x : ℕ → Vec)
    (i : ℕ) (hi : i < n) : (h.cands fl dg dgb n x i).length ≤ n := by
  unfold AHead.cands
  exact le_trans (List.length_filter_le _ _) (Lane4.R7K3.hs_cand_len h.mask n i hi)

theorem dense_getD {hc : HCert} (hd : hc.dense = true) {t : ℕ} (ht : t < hc.cands.length) :
    hc.cands.getD t false = true := by
  unfold HCert.dense at hd
  have := List.all_eq_true.mp hd _ (zgetD_mem' false hc.cands t ht)
  simpa using this

/-! ### exponentials -/

theorem exp_one_bounds : (27 / 10 : ℝ) ≤ Real.exp 1 ∧ Real.exp 1 ≤ 3 := by
  have h := Real.exp_bound (x := (1 : ℝ)) (by norm_num) (n := 8) (by norm_num)
  obtain ⟨h1, h2⟩ := abs_le.mp h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1 h2
  constructor <;> linarith

theorem exp_one_le_three : Real.exp 1 ≤ 3 := exp_one_bounds.2

theorem exp_five_ge : (143 : ℝ) ≤ Real.exp 5 := by
  have h1 : (27 / 10 : ℝ) ≤ Real.exp 1 := exp_one_bounds.1
  have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h5]
  have h6 : ((27 / 10 : ℝ)) ^ 5 ≤ Real.exp 1 ^ 5 := by gcongr
  norm_num at h6
  linarith

theorem exp_neg_small (a : ℝ) (ha : 16 / 3 ≤ a) : Real.exp (-a) ≤ 1 / 101 := by
  have h1 : Real.exp 5 ≤ Real.exp a := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
  have h3 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  have h4 := exp_five_ge
  nlinarith [mul_le_mul_of_nonneg_left (le_trans h4 h1) h3]

theorem geo_sum_le (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 101) (N : ℕ) :
    ∑ j ∈ Finset.range N, q ^ j ≤ 101 / 100 := by
  have h1 := mul_neg_geom_sum q N
  have hS0 : 0 ≤ ∑ j ∈ Finset.range N, q ^ j := Finset.sum_nonneg (fun j _ => pow_nonneg hq0 j)
  have hqN : 0 ≤ q ^ N := pow_nonneg hq0 N
  have h2 : q * (∑ j ∈ Finset.range N, q ^ j) ≤ (1 / 101) * (∑ j ∈ Finset.range N, q ^ j) :=
    mul_le_mul_of_nonneg_right hq hS0
  nlinarith [h1, hS0, hqN, h2]

theorem geo_tail (s : ℕ → ℝ) (sr : ℝ) (T : List ℕ) (hT : T.Nodup) (p0 L : ℕ) (a D : ℝ)
    (ha : 16 / 3 ≤ a)
    (hk : ∀ k ∈ T, k + L ≤ p0 ∧ s k - sr ≤ -(a * ((p0 : ℝ) - (k : ℝ))) + D) :
    (T.map (fun k => Real.exp (s k - sr))).sum ≤ Real.exp (D - a * (L : ℝ)) * (101 / 100) := by
  have hq0 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  have hq1 : Real.exp (-a) ≤ 1 / 101 := exp_neg_small a ha
  have hterm : ∀ k ∈ T, Real.exp (s k - sr)
      ≤ Real.exp (D - a * (L : ℝ)) * Real.exp (-a) ^ (p0 - k - L) := by
    intro k hkT
    obtain ⟨hk1, hk2⟩ := hk k hkT
    have hc : ((p0 - k - L : ℕ) : ℝ) = (p0 : ℝ) - k - L := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    rw [← Real.exp_nat_mul, ← Real.exp_add, hc]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsub : T.toFinset ⊆ Finset.range (p0 - L + 1) := by
    intro k hkT
    rw [List.mem_toFinset] at hkT
    rw [Finset.mem_range]
    have := (hk k hkT).1
    omega
  rw [← List.sum_toFinset _ hT]
  have hE0 : 0 ≤ Real.exp (D - a * (L : ℝ)) := (Real.exp_pos _).le
  calc ∑ k ∈ T.toFinset, Real.exp (s k - sr)
      ≤ ∑ k ∈ T.toFinset, Real.exp (D - a * (L : ℝ)) * Real.exp (-a) ^ (p0 - k - L) :=
        Finset.sum_le_sum (fun k hk => hterm k (List.mem_toFinset.mp hk))
    _ ≤ ∑ k ∈ Finset.range (p0 - L + 1), Real.exp (D - a * (L : ℝ)) * Real.exp (-a) ^ (p0 - k - L) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => mul_nonneg hE0 (pow_nonneg hq0 _))
    _ = Real.exp (D - a * (L : ℝ)) * ∑ k ∈ Finset.range (p0 - L + 1), Real.exp (-a) ^ (p0 - k - L) :=
        (Finset.mul_sum _ _ _).symm
    _ = Real.exp (D - a * (L : ℝ)) * ∑ j ∈ Finset.range (p0 - L + 1), Real.exp (-a) ^ j := by
        congr 1
        have hrefl : ∑ k ∈ Finset.range (p0 - L + 1), Real.exp (-a) ^ (p0 - L + 1 - 1 - k)
            = ∑ j ∈ Finset.range (p0 - L + 1), Real.exp (-a) ^ j :=
          Finset.sum_range_reflect (fun j => Real.exp (-a) ^ j) (p0 - L + 1)
        rw [← hrefl]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [show p0 - k - L = p0 - L + 1 - 1 - k by omega]
    _ ≤ Real.exp (D - a * (L : ℝ)) * (101 / 100) :=
        mul_le_mul_of_nonneg_left (geo_sum_le _ hq0 hq1 _) hE0

theorem sb_arith {M m : ℝ} {n : ℕ} (hn : 1 ≤ n) (hM : 2 ^ 40 * (n : ℝ) ^ 2 ≤ M)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1024) :
    2 * (m * ((n : ℝ) + 1) + 2 * ((n : ℝ) + 1) + 1025) ≤ M := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h40 : (2 : ℝ) ^ 40 = 1099511627776 := by norm_num
  rw [h40] at hM
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hmn : m * ((n : ℝ) + 1) ≤ 1024 * ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hm2 (by linarith)
  nlinarith


/-! ### the environment of one head -/

theorem mem_drop_range {len q : ℕ} (h1 : 1 ≤ q) (h2 : q < len) :
    q ∈ (List.range len).drop 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, len = m + 1 := ⟨len - 1, by omega⟩
  rw [List.range_succ_eq_map]
  simp only [List.drop_succ_cons, List.drop_zero, List.mem_map, List.mem_range]
  exact ⟨q - 1, by omega, by omega⟩

theorem mem_zip_range : ∀ (len : ℕ) (cd : List Bool), cd.length = len → ∀ t, t < len →
    (t, cd.getD t false) ∈ List.zip (List.range len) cd
  | 0, cd, _, t, ht => by omega
  | m + 1, [], hl, t, _ => by simp at hl
  | m + 1, c :: cs, hl, t, ht => by
      rw [List.range_succ_eq_map]
      cases t with
      | zero => simp
      | succ t =>
        have ih := mem_zip_range m cs (by simpa using hl) t (by omega)
        rw [List.zip_cons_cons]
        simp only [List.getD_cons_succ]
        apply List.mem_cons_of_mem
        rw [List.zip_map_left]
        exact List.mem_map.mpr ⟨(t, cs.getD t false), ih, rfl⟩

structure Env8 (u η M : ℝ) (fl : ℝ → ℝ) (δ : ℚ) (h : AHead) (E : List (List IV)) (hc : HCert)
    (dd : ℕ) (dA dV : ℕ → ℕ → ℝ) (dm : ℝ) (dg : ℕ → ℝ) (dgb : ℝ) (n : ℕ) (x : ℕ → Vec)
    (tok : ℕ → ℕ) : Prop where
  ctx : Ctx u η M fl
  d0 : 0 ≤ δ
  d1 : δ ≤ 1 / 2
  ok : headOK8 δ E h hc = true
  shape : h.shapeOK dd = true
  dd24 : dd ≤ 24
  sA : smallM h.A = true
  sV : smallM h.V = true
  sg : smallQ h.g = true
  sgb : smallQ [h.gb] = true
  rows : ∀ row ∈ E, row.length = dd ∧ Bdd 16 row
  hdA : ∀ a b, |dA a b| ≤ (δ : ℝ)
  hdV : ∀ a b, |dV a b| ≤ (δ : ℝ)
  hdm : |dm| ≤ (δ : ℝ)
  hdg : ∀ k, |dg k| ≤ (δ : ℝ)
  hdgb : |dgb| ≤ (δ : ℝ)
  hun : u * (n : ℝ) ≤ 1 / 256
  hηn : η * (n : ℝ) ≤ 1 / 2 ^ 100
  hM : 2 ^ 40 * (n : ℝ) ^ 2 ≤ M
  hx : ∀ j, j < n → tok j < E.length ∧ InIVs (x j) (E.getD (tok j) [])
  mne : h.mask ≠ Mask.all
  m1 : 1 ≤ h.m
  m2 : h.m ≤ 1024
  hlen : hc.cands.length = E.length
  gate : ∀ t, t < E.length → gateDec δ h (E.getD t []) = some (hc.cands.getD t false)
  hVE : hc.VE = E.map (fun xt => matIV δ h.V xt)
  hBv : hc.Bv = valBound δ E h hc.cands
  hBv20 : ∀ B ∈ hc.Bv, B ≤ 2 ^ 20
  sp0 : 0 ≤ hc.spread
  pair : ∀ tq, 1 ≤ tq → tq < E.length → ∀ ta, ta < E.length → ∀ tb, tb < E.length →
      hc.cands.getD ta false = true → hc.cands.getD tb false = true →
      (sAt hc tq tb).1 - (sAt hc tq ta).1 + (sAt hc tq ta).2 + (sAt hc tq tb).2 ≤ hc.spread
  L1 : 1 ≤ hc.L
  L3 : hc.L ≤ 3
  room : 16 ≤ tailRoom δ h hc

theorem open8 {δ : ℚ} {E : List (List IV)} {h : AHead} {hc : HCert}
    (hok : headOK8 δ E h hc = true) :
    h.mask ≠ Mask.all ∧ 1 ≤ h.m ∧ h.m ≤ 1024 ∧ hc.cands.length = E.length ∧
    (∀ t, t < E.length → gateDec δ h (E.getD t []) = some (hc.cands.getD t false)) ∧
    hc.VE = E.map (fun xt => matIV δ h.V xt) ∧ hc.Bv = valBound δ E h hc.cands ∧
    (∀ B ∈ hc.Bv, B ≤ 2 ^ 20) ∧ 0 ≤ hc.spread ∧
    (∀ tq, 1 ≤ tq → tq < E.length → ∀ ta, ta < E.length → ∀ tb, tb < E.length →
       hc.cands.getD ta false = true → hc.cands.getD tb false = true →
       (sAt hc tq tb).1 - (sAt hc tq ta).1 + (sAt hc tq ta).2 + (sAt hc tq tb).2 ≤ hc.spread) ∧
    1 ≤ hc.L ∧ hc.L ≤ 3 ∧ 16 ≤ tailRoom δ h hc := by
  unfold headOK8 at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hmask, hm1⟩, hm2⟩, hlen⟩, hg⟩, -⟩, hVE⟩, hBv⟩, hBv20⟩, -⟩, hsp⟩, hpair⟩,
    hL1⟩, hL3⟩, hroom⟩ := hok
  refine ⟨hmask, hm1, hm2, hlen, ?_, hVE, hBv, ?_, hsp, ?_, hL1, hL3, hroom⟩
  · intro t ht
    have := Lane4.R7K3.hs_zipWith_all (fun x b => gateDec δ h x == some b) E hc.cands hlen hg t ht
    simpa using this
  · intro B hB
    have := List.all_eq_true.mp hBv20 B hB
    simpa using this
  · intro tq h1 htq ta hta tb htb hca hcb
    have a1 := List.all_eq_true.mp hpair tq (mem_drop_range h1 htq)
    have a2 := List.all_eq_true.mp a1 (ta, hc.cands.getD ta false)
      (mem_zip_range E.length hc.cands hlen ta hta)
    have a3 := List.all_eq_true.mp a2 (tb, hc.cands.getD tb false)
      (mem_zip_range E.length hc.cands hlen tb htb)
    exact Lane4.R7K3.hs_or3 a3 hca hcb

section
variable {u η M : ℝ} {fl : ℝ → ℝ} {ex : ℝ → ℝ} {δ : ℚ} {h : AHead} {E : List (List IV)}
  {hc : HCert} {dd : ℕ} {dA dV : ℕ → ℕ → ℝ} {dm : ℝ} {dg : ℕ → ℝ} {dgb : ℝ} {n : ℕ}
  {x : ℕ → Vec} {tok : ℕ → ℕ}

theorem e_const (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) :
    (1 : ℝ) ≤ ((h.m : ℚ) : ℝ) ∧ ((h.m : ℚ) : ℝ) ≤ 1024 ∧ (0 : ℝ) ≤ (δ : ℝ) ∧ (δ : ℝ) ≤ 1 / 2 :=
  ⟨by exact_mod_cast env.m1, by exact_mod_cast env.m2, by exact_mod_cast env.d0, zhalf δ env.d1⟩

theorem e_Vlen (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) : h.V.length = dd :=
  (Lane4.R7K3.hs_shape env.shape).2.2.1

theorem e_gate (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {k : ℕ} (hk : k < n) :
    h.gate fl dg dgb (x k) = 0 ↔ hc.cands.getD (tok k) false = true := by
  obtain ⟨hqk, hxk⟩ := env.hx k hk
  have rk := env.rows _ (zgetD_mem' [] E _ hqk)
  obtain ⟨-, -, -, -, sg1⟩ := Lane4.R7K3.hs_shape env.shape
  have lk : (x k).length = dd := by rw [zinIVs_len hxk]; exact rk.1
  have hdd := env.dd24
  exact gate_sound u η M fl env.ctx δ env.d0 env.d1 h (x k) _ dg dgb env.hdg env.hdgb
    (by rw [sg1, lk]) (by omega) env.sg env.sgb hxk rk.2 _ (env.gate (tok k) hqk)

theorem e_mem_cands (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {i : ℕ}
    (hi : i < n) (k : ℕ) :
    k ∈ h.cands fl dg dgb n x i ↔ k ∈ cand h.mask n i ∧ hc.cands.getD (tok k) false = true := by
  rw [AHead.mem_cands]
  constructor
  · rintro ⟨hk, hg⟩
    exact ⟨hk, (e_gate env (Lane4.R7K3.hs_cand_lt hi hk)).mp hg⟩
  · rintro ⟨hk, hcd⟩
    exact ⟨hk, (e_gate env (Lane4.R7K3.hs_cand_lt hi hk)).mpr hcd⟩

theorem e_dot_key (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {r : List ℚ}
    (hr : r ∈ h.V) {k : ℕ} (hk : k < n) (i' : ℕ) :
    InIV (ardot fl r (x k) (dV i') 0 0) (dotIV δ r (E.getD (tok k) []))
    ∧ 0 ≤ (dotIV δ r (E.getD (tok k) [])).2 := by
  obtain ⟨hqk, hxk⟩ := env.hx k hk
  have rk := env.rows _ (zgetD_mem' [] E _ hqk)
  obtain ⟨-, -, -, sV2, -⟩ := Lane4.R7K3.hs_shape env.shape
  have lk : (x k).length = dd := by rw [zinIVs_len hxk]; exact rk.1
  have hdd := env.dd24
  have hr' := zsmallM_mem env.sV r hr
  have hrl := sV2 r hr
  exact dot_sound u η M fl env.ctx δ env.d0 env.d1 r (x k) _ (dV i') (env.hdV i')
    (by rw [hrl, lk]) (by omega) hr' hxk rk.2

theorem e_Bv (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {ρ : ℕ} (hρ : ρ < dd) :
    hc.Bv.getD ρ 0 = Lane4.R7K3.hs_Bf δ E hc.cands (h.V.getD ρ []) := by
  have e1 : hc.Bv = h.V.map (Lane4.R7K3.hs_Bf δ E hc.cands) := env.hBv.trans rfl
  rw [e1]
  exact Lane4.R8KA.k_getD_map (Lane4.R7K3.hs_Bf δ E hc.cands) [] 0 h.V ρ
    (by rw [e_Vlen env]; exact hρ)

theorem e_Bf20 (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {r : List ℚ}
    (hr : r ∈ h.V) : Lane4.R7K3.hs_Bf δ E hc.cands r ≤ 2 ^ 20 := by
  apply env.hBv20
  rw [env.hBv]
  unfold valBound
  exact List.mem_map.mpr ⟨r, hr, rfl⟩

theorem e_vAt (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {t ρ : ℕ}
    (ht : t < E.length) (hρ : ρ < dd) :
    vAt hc t ρ = dotIV δ (h.V.getD ρ []) (E.getD t []) := by
  have e1 : hc.VE.getD t [] = matIV δ h.V (E.getD t []) := by
    rw [env.hVE]
    exact Lane4.R8KA.k_getD_map (fun xt => matIV δ h.V xt) [] [] E t ht
  unfold vAt
  rw [e1]
  unfold matIV
  exact Lane4.R8KA.k_getD_map (fun r => dotIV δ r (E.getD t [])) [] (0, 0) h.V ρ
    (by rw [e_Vlen env]; exact hρ)

theorem e_key_val (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {ρ : ℕ} (hρ : ρ < dd)
    {k : ℕ} (hk : k < n) :
    |ardot fl (h.V.getD ρ []) (x k) (dV ρ) 0 0 - (((vAt hc (tok k) ρ).1 : ℚ) : ℝ)|
      ≤ (((vAt hc (tok k) ρ).2 : ℚ) : ℝ) := by
  have hr : h.V.getD ρ [] ∈ h.V := zgetD_mem' [] h.V ρ (by rw [e_Vlen env]; exact hρ)
  have := (e_dot_key env hr hk ρ).1
  rw [e_vAt env (env.hx k hk).1 hρ]
  exact this

theorem e_fk_bound (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {r : List ℚ}
    (hr : r ∈ h.V) {k : ℕ} (hk : k < n) (hcd : hc.cands.getD (tok k) false = true) (i' : ℕ) :
    |ardot fl r (x k) (dV i') 0 0| ≤ ((Lane4.R7K3.hs_Bf δ E hc.cands r : ℚ) : ℝ) := by
  obtain ⟨d1, d2⟩ := e_dot_key env hr hk i'
  have hqk := (env.hx k hk).1
  have hb := Lane4.R7K3.hs_Bf_ge δ E hc.cands env.hlen r hqk hcd
  have hbR : |(((dotIV δ r (E.getD (tok k) [])).1 : ℚ) : ℝ)|
      + (((dotIV δ r (E.getD (tok k) [])).2 : ℚ) : ℝ)
        ≤ ((Lane4.R7K3.hs_Bf δ E hc.cands r : ℚ) : ℝ) := by
    have : ((qabs (dotIV δ r (E.getD (tok k) [])).1 + (dotIV δ r (E.getD (tok k) [])).2 : ℚ) : ℝ)
        ≤ ((Lane4.R7K3.hs_Bf δ E hc.cands r : ℚ) : ℝ) := by exact_mod_cast hb
    rw [Rat.cast_add, zqabs_cast] at this
    exact this
  unfold InIV at d1
  obtain ⟨e1, e2⟩ := abs_le.mp d1
  have f1 := neg_abs_le (((dotIV δ r (E.getD (tok k) [])).1 : ℚ) : ℝ)
  have f2 := le_abs_self (((dotIV δ r (E.getD (tok k) [])).1 : ℚ) : ℝ)
  rw [abs_le]
  constructor <;> linarith

theorem e_size (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {i : ℕ} (hi : i < n)
    (hti : 1 ≤ tok i) {j : ℕ} (hj : j ≤ i) (hcj : hc.cands.getD (tok j) false = true) :
    |h.score fl dA dm x i j|
      ≤ ((h.m : ℚ) : ℝ) * ((n : ℝ) + 1) + 2 * ((n : ℝ) + 1) + 1025 :=
  (Lane4.R8KA.score_win u η M fl env.ctx δ env.d0 env.d1 h E hc dd env.ok env.shape env.dd24
    env.sA env.rows dA dm env.hdA env.hdm n x tok env.hun env.hηn env.hM env.hx i hi hti j j hj hj
    hcj hcj).1

theorem e_far (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {i : ℕ} (hi : i < n)
    (hti : 1 ≤ tok i) {j k : ℕ} (hj : j ≤ i) (hk : k ≤ i)
    (hcj : hc.cands.getD (tok j) false = true) (hck : hc.cands.getD (tok k) false = true)
    (hkj : k < j) :
    h.score fl dA dm x i k - h.score fl dA dm x i j ≤
      -((((h.m : ℚ) : ℝ) - (δ : ℝ)) * ((j : ℝ) - (k : ℝ))) + ((hc.spread + sigFar h : ℚ) : ℝ) := by
  have hF := (Lane4.R8KA.score_win u η M fl env.ctx δ env.d0 env.d1 h E hc dd env.ok env.shape
    env.dd24 env.sA env.rows dA dm env.hdA env.hdm n x tok env.hun env.hηn env.hM env.hx i hi hti
    j k hj hk hcj hck).2.1 hkj
  have hqi := (env.hx i hi).1
  have hjn : j < n := lt_of_le_of_lt hj hi
  have hkn : k < n := lt_trans hkj hjn
  have hqj := (env.hx j hjn).1
  have hqk := (env.hx k hkn).1
  have hp := env.pair (tok i) hti hqi (tok j) hqj (tok k) hqk hcj hck
  have hpR : ((((sAt hc (tok i) (tok k)).1 - (sAt hc (tok i) (tok j)).1
      + (sAt hc (tok i) (tok j)).2 + (sAt hc (tok i) (tok k)).2 : ℚ)) : ℝ)
      ≤ ((hc.spread : ℚ) : ℝ) := by exact_mod_cast hp
  push_cast at hF hpR ⊢
  linarith

theorem e_decay (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {i : ℕ} (hi : i < n)
    (hti : 1 ≤ tok i) {p k : ℕ} (hp : p ≤ i) (hk : k ≤ i)
    (hcp : hc.cands.getD (tok p) false = true) (hck : hc.cands.getD (tok k) false = true)
    (hpk : k + 3 ≤ p) :
    h.score fl dA dm x i k ≤ h.score fl dA dm x i p - 16 - ((p : ℝ) - (k : ℝ) - 3) / 2 := by
  have hF := e_far env hi hti hp hk hcp hck (by omega)
  obtain ⟨hm1, hm2, hd0, hd1⟩ := e_const env
  have hroom : (16 : ℝ) ≤ (((h.m - δ) * (hc.L : ℚ) - hc.spread - sigFar h : ℚ) : ℝ) := by
    have := env.room
    unfold tailRoom at this
    exact_mod_cast this
  have hL3 : (hc.L : ℝ) ≤ 3 := by exact_mod_cast env.L3
  push_cast at hroom hF
  have hpk' : (3 : ℝ) ≤ (p : ℝ) - (k : ℝ) := by
    have : (k : ℝ) + 3 ≤ (p : ℝ) := by exact_mod_cast hpk
    linarith
  have p1 := mul_nonneg (show (0 : ℝ) ≤ ((h.m : ℚ) : ℝ) - (δ : ℝ) - 1 / 2 by linarith)
    (show (0 : ℝ) ≤ (p : ℝ) - (k : ℝ) - 3 by linarith)
  have p2 := mul_nonneg (show (0 : ℝ) ≤ ((h.m : ℚ) : ℝ) - (δ : ℝ) by linarith)
    (show (0 : ℝ) ≤ 3 - (hc.L : ℝ) by linarith)
  nlinarith [p1, p2]

theorem row_savg (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) (hex : ExpM u η ex)
    {i : ℕ} (hi : i < n) (hti : 1 ≤ tok i) {r : List ℚ} (hr : r ∈ h.V) (i' : ℕ) {p : ℕ}
    (hp : p ∈ h.cands fl dg dgb n x i) (hmax : ∀ k ∈ h.cands fl dg dgb n x i, k ≤ p) :
    |savg fl ex (h.cands fl dg dgb n x i) (fun j => h.score fl dA dm x i j)
        (fun k => ardot fl r (x k) (dV i') 0 0)
      - eavg (h.cands fl dg dgb n x i) (fun j => h.score fl dA dm x i j)
        (fun k => ardot fl r (x k) (dV i') 0 0)|
      ≤ ((Lane4.R7K3.hs_Bf δ E hc.cands r : ℚ) : ℝ) / 2 ^ 13 + 1 / 2 ^ 90 := by
  have C := env.ctx
  have hmem := e_mem_cands env hi
  obtain ⟨hm1R, hm2R, hδ0R, hδ1R⟩ := e_const env
  have hn1 : 1 ≤ n := by omega
  have hSb := sb_arith hn1 env.hM hm1R hm2R
  have h4 := (Lane4.R7K3.hs_Sb hn1 env.hM hm1R hm2R).2.2.1
  have hB20 : Lane4.R7K3.hs_Bf δ E hc.cands r ≤ 2 ^ 20 := e_Bf20 env hr
  have hB20R : ((Lane4.R7K3.hs_Bf δ E hc.cands r : ℚ) : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hB20
  have hBM : 4 * ((Lane4.R7K3.hs_Bf δ E hc.cands r : ℚ) : ℝ) + 4 ≤ M := by linarith
  have hdec : ∀ k ∈ h.cands fl dg dgb n x i, k + 3 ≤ p →
      h.score fl dA dm x i k ≤ h.score fl dA dm x i p - 16 - ((p : ℝ) - (k : ℝ) - 3) / 2 := by
    intro k hk hkp
    obtain ⟨hk1, hk2⟩ := (hmem k).mp hk
    obtain ⟨hp1, hp2⟩ := (hmem p).mp hp
    exact e_decay env hi hti (cand_le env.mne hp1) (cand_le env.mne hk1) hp2 hk2 hkp
  have hSk : ∀ k ∈ h.cands fl dg dgb n x i, |h.score fl dA dm x i k|
      ≤ ((h.m : ℚ) : ℝ) * ((n : ℝ) + 1) + 2 * ((n : ℝ) + 1) + 1025 := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := (hmem k).mp hk
    exact e_size env hi hti (cand_le env.mne hk1) hk2
  have hBk : ∀ k ∈ h.cands fl dg dgb n x i, |ardot fl r (x k) (dV i') 0 0|
      ≤ ((Lane4.R7K3.hs_Bf δ E hc.cands r : ℚ) : ℝ) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := (hmem k).mp hk
    exact e_fk_bound env hr (Lane4.R7K3.hs_cand_lt hi hk1) hk2 i'
  have := Lane4.R8KB.savg_arith u η M fl ex C.rnd hex C.u0 C.u1 C.h0 C.h1 _
    (cands_pairwise h fl dg dgb n x i) n (cands_len h fl dg dgb n x i hi) env.hun env.hηn
    (fun j => h.score fl dA dm x i j) (fun k => ardot fl r (x k) (dV i') 0 0) p hp hmax hdec _ hSk
    hSb _ hBk hBM
  exact this.1

end

end Lane4.Case
