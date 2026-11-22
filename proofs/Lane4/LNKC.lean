/-
Lane 4, rung 9-LN15 kit module, assembled by tools/ln_assemble.py from kit case lc
(runs/r9ln15-kit/lc): statements by the lane (Lane4/LNDefs.lean), proofs checked by tools/check.py.
-/
import Lane4.LNB2

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.multiGoal false
set_option linter.unusedTactic false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

namespace Lane4.LNKC
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.LNC Lane4.R7K2

/-! ported from Lane4/R7K3.lean (`hs_Bf_nonneg`, `hs_Bf_ge`) for `bfRel` -/

theorem bfRel_nonneg (δ : ℚ) (E : List (List IV)) (cd : List Bool) (r : List ℚ) :
    0 ≤ bfRel δ E cd r :=
  (Lane4.R7K3.hs_foldl_max (fun a : List IV × Bool => qabs (dotRel δ r a.1).1 + (dotRel δ r a.1).2)
    ((List.zip E cd).filter (fun a => a.2)) 0).1

theorem bfRel_ge (δ : ℚ) (E : List (List IV)) (cd : List Bool) (hlen : cd.length = E.length)
    (r : List ℚ) {t : ℕ} (ht : t < E.length) (hcd : cd.getD t false = true) :
    qabs (dotRel δ r (E.getD t [])).1 + (dotRel δ r (E.getD t [])).2 ≤ bfRel δ E cd r := by
  have hmem : (E.getD t [], cd.getD t false) ∈ (List.zip E cd).filter (fun a => a.2) := by
    rw [List.mem_filter]
    exact ⟨Lane4.R7K3.hs_mem_zip E cd hlen t ht, by simpa using hcd⟩
  have key := (Lane4.R7K3.hs_foldl_max (fun a : List IV × Bool => qabs (dotRel δ r a.1).1 + (dotRel δ r a.1).2)
    ((List.zip E cd).filter (fun a => a.2)) 0).2 (E.getD t [], cd.getD t false) hmem
  unfold bfRel
  exact key

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
        have hmap : List.map (fun j => ((l.getD j 0 : ℚ) : ℝ) * e' (j + 1)) (List.range l.length)
            = List.map ((fun j => (((a :: l).getD j 0 : ℚ) : ℝ) * e' j) ∘ Nat.succ)
              (List.range l.length) := by
          apply List.map_congr_left
          intro j _
          simp [Function.comp, List.getD_cons_succ]
        rw [hmap]

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
  ok : headOKLN δ E h hc = true
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
  hVE : hc.VE = E.map (fun xt => matRel δ h.V xt)
  hBv : hc.Bv = valBoundR δ E h hc.cands
  hBv20 : ∀ B ∈ hc.Bv, B ≤ 2 ^ 20
  sp0 : 0 ≤ hc.spread
  pair : ∀ tq, 1 ≤ tq → tq < E.length → ∀ ta, ta < E.length → ∀ tb, tb < E.length →
      hc.cands.getD ta false = true → hc.cands.getD tb false = true →
      (sAt hc tq tb).1 - (sAt hc tq ta).1 + (sAt hc tq ta).2 + (sAt hc tq tb).2 ≤ hc.spread
  L1 : 1 ≤ hc.L
  L3 : hc.L ≤ 3
  room : 16 ≤ tailRoom δ h hc

theorem open8 {δ : ℚ} {E : List (List IV)} {h : AHead} {hc : HCert}
    (hok : headOKLN δ E h hc = true) :
    h.mask ≠ Mask.all ∧ 1 ≤ h.m ∧ h.m ≤ 1024 ∧ hc.cands.length = E.length ∧
    (∀ t, t < E.length → gateDec δ h (E.getD t []) = some (hc.cands.getD t false)) ∧
    hc.VE = E.map (fun xt => matRel δ h.V xt) ∧ hc.Bv = valBoundR δ E h hc.cands ∧
    (∀ B ∈ hc.Bv, B ≤ 2 ^ 20) ∧ 0 ≤ hc.spread ∧
    (∀ tq, 1 ≤ tq → tq < E.length → ∀ ta, ta < E.length → ∀ tb, tb < E.length →
       hc.cands.getD ta false = true → hc.cands.getD tb false = true →
       (sAt hc tq tb).1 - (sAt hc tq ta).1 + (sAt hc tq ta).2 + (sAt hc tq tb).2 ≤ hc.spread) ∧
    1 ≤ hc.L ∧ hc.L ≤ 3 ∧ 16 ≤ tailRoom δ h hc := by
  unfold headOKLN at hok
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
    InIV (ardot fl r (x k) (dV i') 0 0) (dotRel δ r (E.getD (tok k) []))
    ∧ 0 ≤ (dotRel δ r (E.getD (tok k) [])).2 := by
  obtain ⟨hqk, hxk⟩ := env.hx k hk
  have rk := env.rows _ (zgetD_mem' [] E _ hqk)
  obtain ⟨-, -, -, sV2, -⟩ := Lane4.R7K3.hs_shape env.shape
  have lk : (x k).length = dd := by rw [zinIVs_len hxk]; exact rk.1
  have hdd := env.dd24
  have hr' := zsmallM_mem env.sV r hr
  have hrl := sV2 r hr
  exact Lane4.LNKA.dot_rel_sound u η M fl env.ctx δ env.d0 env.d1 r (x k) _ (dV i') (env.hdV i')
    (by rw [hrl, lk]) (by omega) hr' hxk rk.2

theorem e_Bv (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {ρ : ℕ} (hρ : ρ < dd) :
    hc.Bv.getD ρ 0 = bfRel δ E hc.cands (h.V.getD ρ []) := by
  have e1 : hc.Bv = h.V.map (bfRel δ E hc.cands) := env.hBv.trans rfl
  rw [e1]
  exact Lane4.R8KA.k_getD_map (bfRel δ E hc.cands) [] 0 h.V ρ
    (by rw [e_Vlen env]; exact hρ)

theorem e_Bf20 (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {r : List ℚ}
    (hr : r ∈ h.V) : bfRel δ E hc.cands r ≤ 2 ^ 20 := by
  apply env.hBv20
  rw [env.hBv]
  unfold valBoundR
  exact List.mem_map.mpr ⟨r, hr, rfl⟩

theorem e_vAt (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {t ρ : ℕ}
    (ht : t < E.length) (hρ : ρ < dd) :
    vAt hc t ρ = dotRel δ (h.V.getD ρ []) (E.getD t []) := by
  have e1 : hc.VE.getD t [] = matRel δ h.V (E.getD t []) := by
    rw [env.hVE]
    exact Lane4.R8KA.k_getD_map (fun xt => matRel δ h.V xt) [] [] E t ht
  unfold vAt
  rw [e1]
  unfold matRel
  exact Lane4.R8KA.k_getD_map (fun r => dotRel δ r (E.getD t [])) [] (0, 0) h.V ρ
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
    |ardot fl r (x k) (dV i') 0 0| ≤ ((bfRel δ E hc.cands r : ℚ) : ℝ) := by
  obtain ⟨d1, d2⟩ := e_dot_key env hr hk i'
  have hqk := (env.hx k hk).1
  have hb := bfRel_ge δ E hc.cands env.hlen r hqk hcd
  have hbR : |(((dotRel δ r (E.getD (tok k) [])).1 : ℚ) : ℝ)|
      + (((dotRel δ r (E.getD (tok k) [])).2 : ℚ) : ℝ)
        ≤ ((bfRel δ E hc.cands r : ℚ) : ℝ) := by
    have : ((qabs (dotRel δ r (E.getD (tok k) [])).1 + (dotRel δ r (E.getD (tok k) [])).2 : ℚ) : ℝ)
        ≤ ((bfRel δ E hc.cands r : ℚ) : ℝ) := by exact_mod_cast hb
    rw [Rat.cast_add, zqabs_cast] at this
    exact this
  unfold InIV at d1
  obtain ⟨e1, e2⟩ := abs_le.mp d1
  have f1 := neg_abs_le (((dotRel δ r (E.getD (tok k) [])).1 : ℚ) : ℝ)
  have f2 := le_abs_self (((dotRel δ r (E.getD (tok k) [])).1 : ℚ) : ℝ)
  rw [abs_le]
  constructor <;> linarith

theorem e_size (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {i : ℕ} (hi : i < n)
    (hti : 1 ≤ tok i) {j : ℕ} (hj : j ≤ i) (hcj : hc.cands.getD (tok j) false = true) :
    |h.score fl dA dm x i j|
      ≤ ((h.m : ℚ) : ℝ) * ((n : ℝ) + 1) + 2 * ((n : ℝ) + 1) + 1025 :=
  (Lane4.LNKB.score_win_ln u η M fl env.ctx δ env.d0 env.d1 h E hc dd env.ok env.shape env.dd24
    env.sA env.rows dA dm env.hdA env.hdm n x tok env.hun env.hηn env.hM env.hx i hi hti j j hj hj
    hcj hcj).1

theorem e_far (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {i : ℕ} (hi : i < n)
    (hti : 1 ≤ tok i) {j k : ℕ} (hj : j ≤ i) (hk : k ≤ i)
    (hcj : hc.cands.getD (tok j) false = true) (hck : hc.cands.getD (tok k) false = true)
    (hkj : k < j) :
    h.score fl dA dm x i k - h.score fl dA dm x i j ≤
      -((((h.m : ℚ) : ℝ) - (δ : ℝ)) * ((j : ℝ) - (k : ℝ))) + ((hc.spread + sigFar h : ℚ) : ℝ) := by
  have hF := (Lane4.LNKB.score_win_ln u η M fl env.ctx δ env.d0 env.d1 h E hc dd env.ok env.shape
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
      ≤ ((bfRel δ E hc.cands r : ℚ) : ℝ) / 2 ^ 13 + 1 / 2 ^ 90 := by
  have C := env.ctx
  have hmem := e_mem_cands env hi
  obtain ⟨hm1R, hm2R, hδ0R, hδ1R⟩ := e_const env
  have hn1 : 1 ≤ n := by omega
  have hSb := sb_arith hn1 env.hM hm1R hm2R
  have h4 := (Lane4.R7K3.hs_Sb hn1 env.hM hm1R hm2R).2.2.1
  have hB20 : bfRel δ E hc.cands r ≤ 2 ^ 20 := e_Bf20 env hr
  have hB20R : ((bfRel δ E hc.cands r : ℚ) : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hB20
  have hBM : 4 * ((bfRel δ E hc.cands r : ℚ) : ℝ) + 4 ≤ M := by linarith
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
      ≤ ((bfRel δ E hc.cands r : ℚ) : ℝ) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := (hmem k).mp hk
    exact e_fk_bound env hr (Lane4.R7K3.hs_cand_lt hi hk1) hk2 i'
  have := Lane4.R8KB.savg_arith u η M fl ex C.rnd hex C.u0 C.u1 C.h0 C.h1 _
    (cands_pairwise h fl dg dgb n x i) n (cands_len h fl dg dgb n x i hi) env.hun env.hηn
    (fun j => h.score fl dA dm x i j) (fun k => ardot fl r (x k) (dV i') 0 0) p hp hmax hdec _ hSk
    hSb _ hBk hBM
  exact this.1

end


/-! ### the ratio table -/

def hiEq (δ : ℚ) (h : AHead) (hc : HCert) (q : ℕ) (keys : List ℕ) (ref rank : ℕ) : ℚ :=
  -(h.m * ((rank : ℚ) - (ref : ℚ))) + δ * qabs ((rank : ℚ) - (ref : ℚ))
    + ((sAt hc q (keys.getD rank 0)).1 - (sAt hc q (keys.getD ref 0)).1)
    + (sAt hc q (keys.getD rank 0)).2 + (sAt hc q (keys.getD ref 0)).2 + sigWin h hc

def loEq (δ : ℚ) (h : AHead) (hc : HCert) (q : ℕ) (keys : List ℕ) (ref rank : ℕ) : ℚ :=
  -(h.m * ((rank : ℚ) - (ref : ℚ))) - δ * qabs ((rank : ℚ) - (ref : ℚ))
    + ((sAt hc q (keys.getD rank 0)).1 - (sAt hc q (keys.getD ref 0)).1)
    - (sAt hc q (keys.getD rank 0)).2 - (sAt hc q (keys.getD ref 0)).2 - sigWin h hc

theorem ratioAt_eq (δ : ℚ) (h : AHead) (hc : HCert) (q : ℕ) (keys : List ℕ) (ref rank : ℕ) :
    ratioAt δ h hc q keys ref rank =
      if hiEq δ h hc q keys ref rank ≤ 6 then
        some (if hc.dense then expLo (loEq δ h hc q keys ref rank) else 0,
              expHi (hiEq δ h hc q keys ref rank))
      else none := rfl

theorem hiEq_cast (δ : ℚ) (h : AHead) (hc : HCert) (q : ℕ) (keys : List ℕ) (ref rank : ℕ) :
    ((hiEq δ h hc q keys ref rank : ℚ) : ℝ) =
      -(((h.m : ℚ) : ℝ) * ((rank : ℝ) - (ref : ℝ))) + (δ : ℝ) * |(rank : ℝ) - (ref : ℝ)|
      + ((((sAt hc q (keys.getD rank 0)).1 : ℚ) : ℝ) - (((sAt hc q (keys.getD ref 0)).1 : ℚ) : ℝ))
      + (((sAt hc q (keys.getD rank 0)).2 : ℚ) : ℝ) + (((sAt hc q (keys.getD ref 0)).2 : ℚ) : ℝ)
      + ((sigWin h hc : ℚ) : ℝ) := by
  unfold hiEq
  push_cast [zqabs_cast]
  try ring

theorem loEq_cast (δ : ℚ) (h : AHead) (hc : HCert) (q : ℕ) (keys : List ℕ) (ref rank : ℕ) :
    ((loEq δ h hc q keys ref rank : ℚ) : ℝ) =
      -(((h.m : ℚ) : ℝ) * ((rank : ℝ) - (ref : ℝ))) - (δ : ℝ) * |(rank : ℝ) - (ref : ℝ)|
      + ((((sAt hc q (keys.getD rank 0)).1 : ℚ) : ℝ) - (((sAt hc q (keys.getD ref 0)).1 : ℚ) : ℝ))
      - (((sAt hc q (keys.getD rank 0)).2 : ℚ) : ℝ) - (((sAt hc q (keys.getD ref 0)).2 : ℚ) : ℝ)
      - ((sigWin h hc : ℚ) : ℝ) := by
  unfold loEq
  push_cast [zqabs_cast]
  try ring

theorem ratioAt_enclose {δ : ℚ} {h : AHead} {hc : HCert} {q : ℕ} {keys : List ℕ} {ref rank : ℕ}
    {w : ℚ × ℚ} (hr : ratioAt δ h hc q keys ref rank = some w) (D : ℝ)
    (hhi : D ≤ ((hiEq δ h hc q keys ref rank : ℚ) : ℝ))
    (hlo : hc.dense = true → ((loEq δ h hc q keys ref rank : ℚ) : ℝ) ≤ D) :
    0 ≤ (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ Real.exp D ∧ Real.exp D ≤ (w.2 : ℝ) := by
  rw [ratioAt_eq] at hr
  by_cases h6 : hiEq δ h hc q keys ref rank ≤ 6
  · rw [if_pos h6] at hr
    have hw := Option.some.inj hr
    have hE := Lane4.R8KC.exp_encl (hiEq δ h hc q keys ref rank) h6
    have hhiR : Real.exp D ≤ Real.exp ((hiEq δ h hc q keys ref rank : ℚ) : ℝ) :=
      Real.exp_le_exp.mpr hhi
    by_cases hd : hc.dense = true
    · have hlo' := hlo hd
      have h6R : ((hiEq δ h hc q keys ref rank : ℚ) : ℝ) ≤ 6 := by exact_mod_cast h6
      have h6' : loEq δ h hc q keys ref rank ≤ 6 := by
        have : ((loEq δ h hc q keys ref rank : ℚ) : ℝ) ≤ 6 := by linarith
        exact_mod_cast this
      have hE2 := Lane4.R8KC.exp_encl (loEq δ h hc q keys ref rank) h6'
      rw [if_pos hd] at hw
      subst hw
      dsimp only
      refine ⟨by exact_mod_cast hE2.1, le_trans hE2.2.1 (Real.exp_le_exp.mpr hlo'), ?_⟩
      exact le_trans hhiR hE.2.2
    · rw [if_neg hd] at hw
      subst hw
      dsimp only
      refine ⟨by simp, by simpa using (Real.exp_pos D).le, ?_⟩
      exact le_trans hhiR hE.2.2
  · rw [if_neg h6] at hr
    exact absurd hr (by simp)

/-! ### opening `headAF` -/

def tlOf (δ : ℚ) (h : AHead) (hc : HCert) (q : ℕ) (keys : List ℕ) : ℚ :=
  if decide (hc.L + (if h.mask = Mask.causal ∧ hc.cands.getD q false = true then 1 else 0)
      ≤ keys.length) = true then 3 * tailB δ h hc else 0

theorem tlOf_full {δ : ℚ} {h : AHead} {hc : HCert} {q : ℕ} {keys : List ℕ}
    (hle : fullLen h hc q ≤ keys.length) : tlOf δ h hc q keys = 3 * tailB δ h hc := by
  unfold tlOf
  have hcond : decide (hc.L + (if h.mask = Mask.causal ∧ hc.cands.getD q false = true then 1 else 0)
      ≤ keys.length) = true := decide_eq_true hle
  rw [if_pos hcond]

theorem tlOf_notfull {δ : ℚ} {h : AHead} {hc : HCert} {q : ℕ} {keys : List ℕ}
    (hlt : keys.length < fullLen h hc q) : tlOf δ h hc q keys = 0 := by
  unfold tlOf
  have hcond : ¬ (decide (hc.L + (if h.mask = Mask.causal ∧ hc.cands.getD q false = true
      then 1 else 0) ≤ keys.length) = true) := by
    intro hc'
    have := of_decide_eq_true hc'
    unfold fullLen at hlt
    omega
  rw [if_neg hcond]

theorem headAF_open {δ : ℚ} {h : AHead} {hc : HCert} {d pre q : ℕ} {keys : List ℕ}
    {o : List AF} (hne : keys.length ≠ 0) (hh : headAF δ h hc d pre q keys = some o) :
    (hc.dense = true → (sAt hc q (keys.getD 0 0)).2
        + (sAt hc q (keys.getD (refRank h hc q keys) 0)).2
        + sigWin h hc + δ * ((refRank h hc q keys : ℕ) : ℚ) ≤ 1) ∧
    ∃ rs : List (ℚ × ℚ),
      allSome ((otherRanks keys.length (refRank h hc q keys)).map
        (fun k => ratioAt δ h hc q keys (refRank h hc q keys) k)) = some rs ∧
      o = (List.range d).map (fun r => coordAF hc keys (refRank h hc q keys)
        (otherRanks keys.length (refRank h hc q keys))
        (rs.map (fun w => weightIV w (sumFst rs) (sumSnd rs) (tlOf δ h hc q keys)))
        pre (tlOf δ h hc q keys) softDen r) := by
  unfold headAF at hh
  rw [if_neg hne] at hh
  dsimp only at hh
  by_cases hg : hc.dense = true ∧ ¬ ((sAt hc q (keys.getD 0 0)).2
        + (sAt hc q (keys.getD (refRank h hc q keys) 0)).2
        + sigWin h hc + δ * ((refRank h hc q keys : ℕ) : ℚ) ≤ 1)
  · rw [if_pos hg] at hh
    exact absurd hh (by simp)
  · rw [if_neg hg] at hh
    refine ⟨?_, ?_⟩
    · intro hd
      by_contra hn
      exact hg ⟨hd, hn⟩
    · generalize hR : allSome ((otherRanks keys.length (refRank h hc q keys)).map
          (fun k => ratioAt δ h hc q keys (refRank h hc q keys) k)) = R at hh ⊢
      cases R with
      | none => simp at hh
      | some rs =>
        refine ⟨rs, rfl, ?_⟩
        exact (Option.some.inj hh).symm

theorem tailB_nonneg {δ : ℚ} {h : AHead} {hc : HCert} (hroom : 16 ≤ tailRoom δ h hc) :
    0 ≤ tailB δ h hc := by
  have hx6 : (-(tailRoom δ h hc) : ℚ) ≤ 6 := by linarith
  obtain ⟨h0, h1, h2⟩ := Lane4.R8KC.exp_encl (-(tailRoom δ h hc)) hx6
  have hs := (Lane4.R8KC.round_sound 70 (expHi (-(tailRoom δ h hc)) * (101 / 100))).2
  have hpos : (0 : ℝ) < ((expHi (-(tailRoom δ h hc)) : ℚ) : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos _) h2
  have hq : (0 : ℚ) < expHi (-(tailRoom δ h hc)) := by exact_mod_cast hpos
  unfold tailB
  linarith

theorem argmax_le (h : AHead) (hc : HCert) (q : ℕ) (keys : List ℕ) :
    ∀ n, argmaxNom h hc q keys n ≤ n
  | 0 => by simp [argmaxNom]
  | n + 1 => by
      simp only [argmaxNom]
      split_ifs
      · exact le_refl _
      · have := argmax_le h hc q keys n
        omega

theorem argmax_max (h : AHead) (hc : HCert) (q : ℕ) (keys : List ℕ) :
    ∀ n j, j ≤ n → nomAt h hc q keys j ≤ nomAt h hc q keys (argmaxNom h hc q keys n)
  | 0, j, hj => by
      have : j = 0 := by omega
      subst this
      simp [argmaxNom]
  | n + 1, j, hj => by
      simp only [argmaxNom]
      split_ifs with hlt
      · rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
        · exact le_trans (argmax_max h hc q keys n j (by omega)) hlt.le
        · have : j = n + 1 := by omega
          subst this
          exact le_refl _
      · rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
        · exact argmax_max h hc q keys n j (by omega)
        · have : j = n + 1 := by omega
          subst this
          exact not_lt.mp hlt

theorem sumFst_cast : ∀ rs : List (ℚ × ℚ),
    ((sumFst rs : ℚ) : ℝ) = (rs.map (fun w => ((w.1 : ℚ) : ℝ))).sum
  | [] => by simp [sumFst]
  | a :: l => by
      have : sumFst (a :: l) = a.1 + sumFst l := rfl
      rw [this, Rat.cast_add, sumFst_cast l]
      simp

theorem sumSnd_cast : ∀ rs : List (ℚ × ℚ),
    ((sumSnd rs : ℚ) : ℝ) = (rs.map (fun w => ((w.2 : ℚ) : ℝ))).sum
  | [] => by simp [sumSnd]
  | a :: l => by
      have : sumSnd (a :: l) = a.2 + sumSnd l := rfl
      rw [this, Rat.cast_add, sumSnd_cast l]
      simp

theorem weightIV_enclose (w : ℚ × ℚ) (slo shi tl : ℚ) (a : ℝ)
    (h1 : (w.1 : ℝ) / (1 + (w.1 : ℝ) + ((shi : ℝ) - (w.2 : ℝ)) + (tl : ℝ)) ≤ a)
    (h2 : a ≤ (w.2 : ℝ) / (1 + (w.2 : ℝ) + ((slo : ℝ) - (w.1 : ℝ)))) :
    (((weightIV w slo shi tl).1 : ℚ) : ℝ) ≤ a ∧ a ≤ (((weightIV w slo shi tl).2 : ℚ) : ℝ) := by
  have hd := (Lane4.R8KC.round_sound 70 (w.1 / (1 + w.1 + (shi - w.2) + tl))).1
  have hu := (Lane4.R8KC.round_sound 70 (w.2 / (1 + w.2 + (slo - w.1)))).2
  have hdR : ((dnB 70 (w.1 / (1 + w.1 + (shi - w.2) + tl)) : ℚ) : ℝ)
      ≤ ((w.1 / (1 + w.1 + (shi - w.2) + tl) : ℚ) : ℝ) := by exact_mod_cast hd
  have huR : ((w.2 / (1 + w.2 + (slo - w.1)) : ℚ) : ℝ)
      ≤ ((upB 70 (w.2 / (1 + w.2 + (slo - w.1))) : ℚ) : ℝ) := by exact_mod_cast hu
  push_cast at hdR huR
  have e1 : (weightIV w slo shi tl).1 = dnB 70 (w.1 / (1 + w.1 + (shi - w.2) + tl)) := rfl
  have e2 : (weightIV w slo shi tl).2 = upB 70 (w.2 / (1 + w.2 + (slo - w.1))) := rfl
  rw [e1, e2]
  exact ⟨le_trans hdR h1, le_trans h2 huR⟩

theorem weights_real (c : List ℕ) (hc : c.Nodup) (s : ℕ → ℝ) (jr : ℕ) (hjr : jr ∈ c)
    (W : List ℕ) (rs : List (ℚ × ℚ)) (tl : ℚ) (hWn : W.Nodup) (hW : ∀ k ∈ W, k ∈ c ∧ k ≠ jr)
    (hl : rs.length = W.length)
    (hint : ∀ j, j < W.length → 0 ≤ ((rs.getD j (0, 0)).1 : ℝ) ∧
      ((rs.getD j (0, 0)).1 : ℝ) ≤ Real.exp (s (W.getD j 0) - s jr) ∧
      Real.exp (s (W.getD j 0) - s jr) ≤ ((rs.getD j (0, 0)).2 : ℝ))
    (htl : 0 ≤ (tl : ℝ))
    (hrest : ((c.filter (fun k => decide (k ≠ jr ∧ k ∉ W))).map
      (fun k => Real.exp (s k - s jr))).sum ≤ (tl : ℝ)) :
    ∃ a : ℕ → ℝ, (∀ j, j < W.length →
        (((weightIV (rs.getD j (0, 0)) (sumFst rs) (sumSnd rs) tl).1 : ℚ) : ℝ) ≤ a j ∧
        a j ≤ (((weightIV (rs.getD j (0, 0)) (sumFst rs) (sumSnd rs) tl).2 : ℚ) : ℝ)) ∧
      (∀ j, 0 ≤ a j) ∧ ((List.range W.length).map a).sum ≤ 1 ∧
      ∀ (f : ℕ → ℝ) (B : ℝ), (∀ k ∈ c, |f k| ≤ B) →
        |eavg c s f - (f jr + ((List.range W.length).map
            (fun j => a j * (f (W.getD j 0) - f jr))).sum)| ≤ 2 * (tl : ℝ) * B := by
  have hlo : ∀ j, j < W.length →
      (rs.map (fun w => ((w.1 : ℚ) : ℝ))).getD j 0 = (((rs.getD j (0, 0)).1 : ℚ) : ℝ) := by
    intro j hj
    exact Lane4.R8KA.k_getD_map (fun w : ℚ × ℚ => ((w.1 : ℚ) : ℝ)) (0, 0) 0 rs j
      (by rw [hl]; exact hj)
  have hhi : ∀ j, j < W.length →
      (rs.map (fun w => ((w.2 : ℚ) : ℝ))).getD j 0 = (((rs.getD j (0, 0)).2 : ℚ) : ℝ) := by
    intro j hj
    exact Lane4.R8KA.k_getD_map (fun w : ℚ × ℚ => ((w.2 : ℚ) : ℝ)) (0, 0) 0 rs j
      (by rw [hl]; exact hj)
  obtain ⟨a, ha1, ha0, haS, hmix⟩ := Lane4.R8KD.mix_bound c hc s jr hjr W
    (rs.map (fun w => ((w.1 : ℚ) : ℝ))) (rs.map (fun w => ((w.2 : ℚ) : ℝ))) hWn hW
    (by simp [hl]) (by simp [hl])
    (by intro j hj; rw [hlo j hj, hhi j hj]; exact hint j hj) (tl : ℝ) htl hrest
  refine ⟨a, ?_, ha0, haS, hmix⟩
  intro j hj
  obtain ⟨h1, h2⟩ := ha1 j hj
  rw [hlo j hj, hhi j hj, ← sumSnd_cast] at h1
  rw [hlo j hj, hhi j hj, ← sumFst_cast] at h2
  exact weightIV_enclose _ _ _ _ _ h1 h2

theorem row_core (c : List ℕ) (s f : ℕ → ℝ) (sv : ℝ) (jr : ℕ) (W : List ℕ) (a cW : ℕ → ℝ)
    (cref R B tl : ℝ)
    (hsav : |sv - eavg c s f| ≤ B / 2 ^ 13 + 1 / 2 ^ 90)
    (hmix : |eavg c s f - (f jr + ((List.range W.length).map
      (fun j => a j * (f (W.getD j 0) - f jr))).sum)| ≤ 2 * tl * B)
    (ha0 : ∀ j, 0 ≤ a j) (hA : ((List.range W.length).map a).sum ≤ 1)
    (hr : |f jr - cref| ≤ R) (hj : ∀ j, j < W.length → |f (W.getD j 0) - cW j| ≤ R) :
    |sv - (cref + ((List.range W.length).map (fun j => a j * (cW j - cref))).sum)|
      ≤ R + 2 * tl * B + (B / 2 ^ 13 + 1 / 2 ^ 90) := by
  have h3 : |(f jr + ((List.range W.length).map (fun j => a j * (f (W.getD j 0) - f jr))).sum)
      - (cref + ((List.range W.length).map (fun j => a j * (cW j - cref))).sum)| ≤ R :=
    coord_alg W.length a cW (fun j => f (W.getD j 0)) cref (f jr) R ha0 hA hr hj
  obtain ⟨a1, a2⟩ := abs_le.mp hsav
  obtain ⟨b1, b2⟩ := abs_le.mp hmix
  obtain ⟨c1, c2⟩ := abs_le.mp h3
  rw [abs_le]
  constructor <;> linarith

theorem coordAF_c (hc : HCert) (keys : List ℕ) (ref : ℕ) (others : List ℕ) (ws : List (ℚ × ℚ))
    (pre : ℕ) (tl sd : ℚ) (r : ℕ) :
    (coordAF hc keys ref others ws pre tl sd r).c =
      (vAt hc (keys.getD ref 0) r).1 +
      (List.zipWith (fun (w : ℚ × ℚ) (d : ℚ) => (w.1 + w.2) / 2 * d) ws
        (others.map (fun k => (vAt hc (keys.getD k 0) r).1 - (vAt hc (keys.getD ref 0) r).1))).foldr
        (fun a s => a + s) 0 := rfl

theorem coordAF_t (hc : HCert) (keys : List ℕ) (ref : ℕ) (others : List ℕ) (ws : List (ℚ × ℚ))
    (pre : ℕ) (tl sd : ℚ) (r : ℕ) :
    (coordAF hc keys ref others ws pre tl sd r).t =
      List.replicate pre 0 ++
      List.zipWith (fun (w : ℚ × ℚ) (d : ℚ) => (w.2 - w.1) / 2 * d) ws
        (others.map (fun k => (vAt hc (keys.getD k 0) r).1 - (vAt hc (keys.getD ref 0) r).1)) := rfl

theorem coordAF_r (hc : HCert) (keys : List ℕ) (ref : ℕ) (others : List ℕ) (ws : List (ℚ × ℚ))
    (pre : ℕ) (tl sd : ℚ) (r : ℕ) :
    (coordAF hc keys ref others ws pre tl sd r).r =
      (keys.map (fun k => (vAt hc k r).2)).foldl max 0 + 2 * tl * hc.Bv.getD r 0
        + hc.Bv.getD r 0 / sd + 1 / 2 ^ 90 := rfl

theorem aattn_length (fl ex : ℝ → ℝ) (dV : ℕ → ℕ → ℝ) (c : List ℕ) (s : ℕ → ℝ) (x : ℕ → Vec) :
    ∀ (V' : List (List ℚ)) (i0 : ℕ), (aattnRows fl ex V' dV c s x i0).length = V'.length
  | [], i0 => by simp [aattnRows]
  | r :: M, i0 => by simp [aattnRows, aattn_length fl ex dV c s x M (i0 + 1)]

theorem aattn_getD (fl ex : ℝ → ℝ) (dV : ℕ → ℕ → ℝ) (c : List ℕ) (s : ℕ → ℝ) (x : ℕ → Vec) :
    ∀ (V' : List (List ℚ)) (i0 k : ℕ), k < V'.length →
    (aattnRows fl ex V' dV c s x i0).getD k 0 =
      savg fl ex c s (fun j => ardot fl (V'.getD k []) (x j) (dV (i0 + k)) 0 0)
  | [], i0, k, hk => by simp at hk
  | r :: M, i0, 0, _ => by simp [aattnRows]
  | r :: M, i0, k + 1, hk => by
      simp only [aattnRows, List.getD_cons_succ]
      have := aattn_getD fl ex dV c s x M (i0 + 1) k (by simpa using hk)
      rw [this]
      rw [show i0 + 1 + k = i0 + (k + 1) by omega]


section
variable {u η M : ℝ} {fl : ℝ → ℝ} {ex : ℝ → ℝ} {δ : ℚ} {h : AHead} {E : List (List IV)}
  {hc : HCert} {dd : ℕ} {dA dV : ℕ → ℕ → ℝ} {dm : ℝ} {dg : ℕ → ℝ} {dgb : ℝ} {n : ℕ}
  {x : ℕ → Vec} {tok : ℕ → ℕ}

theorem ratio_real (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {i : ℕ} (hi : i < n)
    (hti : 1 ≤ tok i) (P keys : List ℕ) (ref : ℕ)
    (hP1 : P.Pairwise (fun a b => b < a))
    (hcd : ∀ a, a < P.length → hc.cands.getD (tok (P.getD a 0)) false = true)
    (hlei : ∀ a, a < P.length → P.getD a 0 ≤ i)
    (hkey : ∀ a, a < P.length → keys.getD a 0 = tok (P.getD a 0))
    (hdense : hc.dense = true → ∀ a, a < P.length → P.getD a 0 + a = P.getD 0 0)
    (hdense2 : hc.dense = true → i ≤ P.getD 0 0 + 1)
    (hlen4 : P.length ≤ 4) (hnd : ¬ hc.dense = true → ref = 0) (href : ref < P.length)
    {a : ℕ} (ha : a < P.length) (har : a ≠ ref) {w : ℚ × ℚ}
    (hr : ratioAt δ h hc (tok i) keys ref a = some w) :
    0 ≤ (w.1 : ℝ) ∧
    (w.1 : ℝ) ≤ Real.exp (h.score fl dA dm x i (P.getD a 0) - h.score fl dA dm x i (P.getD ref 0)) ∧
    Real.exp (h.score fl dA dm x i (P.getD a 0) - h.score fl dA dm x i (P.getD ref 0))
      ≤ (w.2 : ℝ) := by
  have hka := hkey a ha
  have hkr := hkey ref href
  by_cases hd : hc.dense = true
  · have hpa := hdense hd a ha
    have hpr := hdense hd ref href
    have hd2 := hdense2 hd
    have hN := (Lane4.LNKB.score_win_ln u η M fl env.ctx δ env.d0 env.d1 h E hc dd env.ok env.shape
      env.dd24 env.sA env.rows dA dm env.hdA env.hdm n x tok env.hun env.hηn env.hM env.hx i hi hti
      (P.getD ref 0) (P.getD a 0) (hlei ref href) (hlei a ha) (hcd ref href) (hcd a ha)).2.2
      (by omega) (by omega)
    have hsig : ((sigWin h hc : ℚ) : ℝ) = 1 / 2 ^ 8 := by
      unfold sigWin; rw [if_pos hd]; norm_num
    have hkj : ((P.getD a 0 : ℕ) : ℝ) - ((P.getD ref 0 : ℕ) : ℝ) = (ref : ℝ) - (a : ℝ) := by
      have : ((P.getD a 0 : ℕ) : ℝ) + (a : ℝ) = ((P.getD ref 0 : ℕ) : ℝ) + (ref : ℝ) := by
        exact_mod_cast (hpa.trans hpr.symm)
      linarith
    rw [hkj] at hN
    push_cast at hN
    obtain ⟨hN1, hN2⟩ := abs_le.mp hN
    refine ratioAt_enclose hr _ ?_ ?_
    · rw [hiEq_cast, hka, hkr, hsig, abs_sub_comm (a : ℝ) (ref : ℝ)]
      linarith
    · intro _
      rw [loEq_cast, hka, hkr, hsig, abs_sub_comm (a : ℝ) (ref : ℝ)]
      linarith
  · have href0 := hnd hd
    subst href0
    have hapos : 1 ≤ a := by omega
    have hlt := dec_idx P hP1 0 a (by omega) ha
    have hsum := dec_sum hP1 a ha
    have hF := (Lane4.LNKB.score_win_ln u η M fl env.ctx δ env.d0 env.d1 h E hc dd env.ok env.shape
      env.dd24 env.sA env.rows dA dm env.hdA env.hdm n x tok env.hun env.hηn env.hM env.hx i hi hti
      (P.getD 0 0) (P.getD a 0) (hlei 0 href) (hlei a ha) (hcd 0 href) (hcd a ha)).2.1 hlt
    have hsig : ((sigWin h hc : ℚ) : ℝ) = ((sigFar h : ℚ) : ℝ) := by
      unfold sigWin; rw [if_neg hd]
    obtain ⟨hm1, hm2, hd0, hd1⟩ := e_const env
    have hsumR : ((P.getD a 0 : ℕ) : ℝ) + (a : ℝ) ≤ ((P.getD 0 0 : ℕ) : ℝ) := by
      exact_mod_cast hsum
    have hprod := mul_nonneg (show (0 : ℝ) ≤ ((h.m : ℚ) : ℝ) - (δ : ℝ) by linarith)
      (show (0 : ℝ) ≤ ((P.getD 0 0 : ℕ) : ℝ) - ((P.getD a 0 : ℕ) : ℝ) - (a : ℝ) by linarith)
    push_cast at hF
    refine ratioAt_enclose hr _ ?_ (fun hd' => absurd hd' hd)
    rw [hiEq_cast, hka, hkr, hsig]
    simp only [Nat.cast_zero, sub_zero]
    have habs : |((a : ℕ) : ℝ)| = (a : ℝ) := abs_of_nonneg (Nat.cast_nonneg a)
    rw [habs]
    nlinarith [hF, hprod]

theorem p0_jr_le (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {i : ℕ} (hi : i < n)
    (hti : 1 ≤ tok i) (P keys : List ℕ) (ref : ℕ)
    (hcd : ∀ a, a < P.length → hc.cands.getD (tok (P.getD a 0)) false = true)
    (hlei : ∀ a, a < P.length → P.getD a 0 ≤ i)
    (hkey : ∀ a, a < P.length → keys.getD a 0 = tok (P.getD a 0))
    (hdense : hc.dense = true → ∀ a, a < P.length → P.getD a 0 + a = P.getD 0 0)
    (hdense2 : hc.dense = true → i ≤ P.getD 0 0 + 1)
    (hlen4 : P.length ≤ 4) (hnd : ¬ hc.dense = true → ref = 0) (href : ref < P.length)
    (hmaxnom : hc.dense = true → nomAt h hc (tok i) keys 0 ≤ nomAt h hc (tok i) keys ref)
    (hguard : hc.dense = true → (sAt hc (tok i) (keys.getD 0 0)).2
      + (sAt hc (tok i) (keys.getD ref 0)).2 + sigWin h hc + δ * (ref : ℚ) ≤ 1)
    (hpos : 0 < P.length) :
    h.score fl dA dm x i (P.getD 0 0) - h.score fl dA dm x i (P.getD ref 0) ≤ 1 := by
  by_cases hd : hc.dense = true
  · have hpr := hdense hd ref href
    have hd2 := hdense2 hd
    have hN := (Lane4.LNKB.score_win_ln u η M fl env.ctx δ env.d0 env.d1 h E hc dd env.ok env.shape
      env.dd24 env.sA env.rows dA dm env.hdA env.hdm n x tok env.hun env.hηn env.hM env.hx i hi hti
      (P.getD ref 0) (P.getD 0 0) (hlei ref href) (hlei 0 hpos) (hcd ref href) (hcd 0 hpos)).2.2
      (by omega) (by omega)
    have hsig : ((sigWin h hc : ℚ) : ℝ) = 1 / 2 ^ 8 := by
      unfold sigWin; rw [if_pos hd]; norm_num
    have hg := hguard hd
    have hgR : (((sAt hc (tok i) (keys.getD 0 0)).2 + (sAt hc (tok i) (keys.getD ref 0)).2
        + sigWin h hc + δ * (ref : ℚ) : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hg
    have hm := hmaxnom hd
    unfold nomAt at hm
    have hmR := (Rat.cast_le (K := ℝ)).mpr hm
    rw [hkey 0 hpos, hkey ref href] at hgR hmR
    have hkj : ((P.getD 0 0 : ℕ) : ℝ) - ((P.getD ref 0 : ℕ) : ℝ) = (ref : ℝ) := by
      have : ((P.getD ref 0 : ℕ) : ℝ) + (ref : ℝ) = ((P.getD 0 0 : ℕ) : ℝ) := by
        exact_mod_cast hpr
      linarith
    have habs : |((ref : ℕ) : ℝ)| = (ref : ℝ) := abs_of_nonneg (Nat.cast_nonneg ref)
    rw [hkj, habs] at hN
    push_cast at hgR hmR hN
    rw [hsig] at hgR
    obtain ⟨hN1, hN2⟩ := abs_le.mp hN
    linarith
  · have href0 := hnd hd
    subst href0
    rw [sub_self]
    norm_num

theorem tail_real (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok) {i : ℕ} (hi : i < n)
    (hti : 1 ≤ tok i) (T : List ℕ) (hT : T.Nodup) (p0 jr : ℕ) (hp0i : p0 ≤ i)
    (hcp0 : hc.cands.getD (tok p0) false = true)
    (hjr : h.score fl dA dm x i p0 - h.score fl dA dm x i jr ≤ 1)
    (hTk : ∀ k ∈ T, k + hc.L ≤ p0 ∧ k ≤ i ∧ hc.cands.getD (tok k) false = true) :
    (T.map (fun k => Real.exp (h.score fl dA dm x i k - h.score fl dA dm x i jr))).sum
      ≤ ((3 * tailB δ h hc : ℚ) : ℝ) := by
  obtain ⟨hm1, hm2, hd0, hd1⟩ := e_const env
  have hL1 : (1 : ℝ) ≤ (hc.L : ℝ) := by exact_mod_cast env.L1
  have hL3 : (hc.L : ℝ) ≤ 3 := by exact_mod_cast env.L3
  have hsp0 : (0 : ℝ) ≤ ((hc.spread : ℚ) : ℝ) := by exact_mod_cast env.sp0
  have hsig0 : (0 : ℝ) ≤ ((sigFar h : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ sigFar h := by
      unfold sigFar
      have := env.m1
      linarith
    exact_mod_cast this
  have hroom : (16 : ℝ) ≤ (((h.m - δ) * (hc.L : ℚ) - hc.spread - sigFar h : ℚ) : ℝ) := by
    have := env.room
    unfold tailRoom at this
    exact_mod_cast this
  push_cast at hroom
  have ha0 : (0 : ℝ) ≤ ((h.m : ℚ) : ℝ) - (δ : ℝ) := by linarith
  have ha16 : (16 : ℝ) / 3 ≤ ((h.m : ℚ) : ℝ) - (δ : ℝ) := by
    nlinarith [mul_nonneg ha0 (show (0 : ℝ) ≤ 3 - (hc.L : ℝ) by linarith)]
  have hgeo := geo_tail (fun k => h.score fl dA dm x i k) (h.score fl dA dm x i jr) T hT p0 hc.L
    (((h.m : ℚ) : ℝ) - (δ : ℝ)) (((hc.spread + sigFar h : ℚ) : ℝ) + 1) ha16 (by
      intro k hk
      obtain ⟨hk1, hk2, hk3⟩ := hTk k hk
      refine ⟨hk1, ?_⟩
      have hlt : k < p0 := by
        have := env.L1
        omega
      have hF := e_far env hi hti hp0i hk2 hcp0 hk3 hlt
      show h.score fl dA dm x i k - h.score fl dA dm x i jr
        ≤ -((((h.m : ℚ) : ℝ) - (δ : ℝ)) * ((p0 : ℝ) - (k : ℝ)))
          + (((hc.spread + sigFar h : ℚ) : ℝ) + 1)
      linarith)
  have hx6 : (-(tailRoom δ h hc) : ℚ) ≤ 6 := by
    have := env.room
    linarith
  obtain ⟨-, -, hE2⟩ := Lane4.R8KC.exp_encl (-(tailRoom δ h hc)) hx6
  have hexp : ((hc.spread + sigFar h : ℚ) : ℝ) + 1
      - (((h.m : ℚ) : ℝ) - (δ : ℝ)) * (hc.L : ℝ) = 1 + ((-(tailRoom δ h hc) : ℚ) : ℝ) := by
    unfold tailRoom
    push_cast
    ring
  rw [hexp, Real.exp_add] at hgeo
  have h1 := exp_one_le_three
  have hpos : 0 < Real.exp ((-(tailRoom δ h hc) : ℚ) : ℝ) := Real.exp_pos _
  have hrs := (Lane4.R8KC.round_sound 70 (expHi (-(tailRoom δ h hc)) * (101 / 100))).2
  have hrsR : ((expHi (-(tailRoom δ h hc)) * (101 / 100) : ℚ) : ℝ)
      ≤ ((tailB δ h hc : ℚ) : ℝ) := by
    unfold tailB
    exact_mod_cast hrs
  have hprod := mul_le_mul h1 hE2 hpos.le (by norm_num : (0 : ℝ) ≤ 3)
  push_cast at hrsR ⊢
  linarith

theorem head_nokey (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok)
    (hex : ExpM u η ex) {i : ℕ} (hi : i < n) (hti : 1 ≤ tok i) {P : List ℕ} (pre : ℕ)
    (hP : P = [])
    (hfull : P.length < fullLen h hc (tok i) →
      ∀ k ∈ cand h.mask n i, hc.cands.getD (tok k) false = true → k ∈ P)
    {o : List AF} (hh : headAF δ h hc dd pre (tok i) (P.map tok) = some o) :
    ∃ e' : ℕ → ℝ, (∀ k, |e' k| ≤ 1) ∧
      ∀ e : ℕ → ℝ, (∀ k, k < P.length - 1 → e (pre + k) = e' k) →
        InAFs e (h.attn fl ex dA dV dm dg dgb n x i) o := by
  subst hP
  refine ⟨fun _ => 0, fun _ => by simp, ?_⟩
  intro e _
  have hlenfull : 0 < fullLen h hc (tok i) :=
    lt_of_lt_of_le (Nat.lt_of_lt_of_le Nat.zero_lt_one env.L1) (Nat.le_add_right _ _)
  have hc0 : h.cands fl dg dgb n x i = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro k hk
    obtain ⟨hk1, hk2⟩ := (e_mem_cands env hi k).mp hk
    have := hfull (by simpa using hlenfull) k hk1 hk2
    simp at this
  unfold headAF at hh
  rw [if_pos (by simp)] at hh
  have ho := (Option.some.inj hh).symm
  subst ho
  have hlenV : (h.attn fl ex dA dV dm dg dgb n x i).length = dd := by
    unfold AHead.attn
    rw [aattn_length, e_Vlen env]
  refine ⟨by rw [hlenV, List.length_map, List.length_range], ?_⟩
  intro k hk
  rw [hlenV] at hk
  rw [gd_map_range _ _ dd k hk]
  have hattn : h.attn fl ex dA dV dm dg dgb n x i
      = aattnRows fl ex h.V dV [] (fun j => h.score fl dA dm x i j) x 0 := by
    unfold AHead.attn
    rw [hc0]
  rw [hattn, aattn_getD fl ex dV [] _ x h.V 0 k (by rw [e_Vlen env]; exact hk)]
  rw [soft_zeros env.ctx.rnd (by simp)]
  unfold InAF
  simp [linVal]

theorem head_keys (env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok)
    (hex : ExpM u η ex) {i : ℕ} (hi : i < n) (hti : 1 ≤ tok i) {P : List ℕ} (pre : ℕ)
    (hW : WinPos h.mask hc.cands tok n i P) (hlen : P.length ≤ fullLen h hc (tok i))
    (hfull : P.length < fullLen h hc (tok i) →
      ∀ k ∈ cand h.mask n i, hc.cands.getD (tok k) false = true → k ∈ P)
    (hpos : 0 < P.length) {o : List AF}
    (hh : headAF δ h hc dd pre (tok i) (P.map tok) = some o) :
    ∃ e' : ℕ → ℝ, (∀ k, |e' k| ≤ 1) ∧
      ∀ e : ℕ → ℝ, (∀ k, k < P.length - 1 → e (pre + k) = e' k) →
        InAFs e (h.attn fl ex dA dV dm dg dgb n x i) o := by
  -- the candidate list
  obtain ⟨c, hcdef⟩ : ∃ c : List ℕ, c = h.cands fl dg dgb n x i := ⟨_, rfl⟩
  have hcmem : ∀ k, k ∈ c ↔ k ∈ cand h.mask n i ∧ hc.cands.getD (tok k) false = true := by
    intro k
    rw [hcdef]
    exact e_mem_cands env hi k
  have hcnd : c.Nodup := by
    rw [hcdef]
    exact AHead.cands_nodup h fl dg dgb n x i
  -- keys
  obtain ⟨keys, hkeys⟩ : ∃ keys : List ℕ, keys = P.map tok := ⟨_, rfl⟩
  rw [← hkeys] at hh
  have hkl : keys.length = P.length := by rw [hkeys, List.length_map]
  have hkey : ∀ a, a < P.length → keys.getD a 0 = tok (P.getD a 0) := by
    intro a ha
    rw [hkeys]
    exact Lane4.R8KA.k_getD_map tok 0 0 P a ha
  have hne : keys.length ≠ 0 := by omega
  obtain ⟨hguard, rs, hrs, ho⟩ := headAF_open hne hh
  obtain ⟨ref, hrefd⟩ : ∃ ref, ref = refRank h hc (tok i) keys := ⟨_, rfl⟩
  rw [← hrefd] at hguard hrs ho
  obtain ⟨others, hotd⟩ : ∃ others, others = otherRanks keys.length ref := ⟨_, rfl⟩
  rw [← hotd] at hrs ho
  obtain ⟨tl, htld⟩ : ∃ tl, tl = tlOf δ h hc (tok i) keys := ⟨_, rfl⟩
  rw [← htld] at ho
  obtain ⟨ws, hwsdef⟩ : ∃ ws, ws = rs.map (fun w => weightIV w (sumFst rs) (sumSnd rs) tl) :=
    ⟨_, rfl⟩
  rw [← hwsdef] at ho
  -- positions
  have hW' := hW
  obtain ⟨hP1, hP2, hP3⟩ := hW'
  have hPc : ∀ a, a < P.length → P.getD a 0 ∈ cand h.mask n i
      ∧ hc.cands.getD (tok (P.getD a 0)) false = true :=
    fun a ha => hP2 _ (zgetD_mem' 0 P a ha)
  have hlei : ∀ a, a < P.length → P.getD a 0 ≤ i :=
    fun a ha => cand_le env.mne (hPc a ha).1
  have hcd : ∀ a, a < P.length → hc.cands.getD (tok (P.getD a 0)) false = true :=
    fun a ha => (hPc a ha).2
  have hPC : ∀ a, a < P.length → P.getD a 0 ∈ c :=
    fun a ha => (hcmem _).mpr (hPc a ha)
  have hmaxc : ∀ k ∈ c, k ≤ P.getD 0 0 :=
    pos_top_max hW hpos (fun k hk => (hcmem k).mp hk)
  have hlen4 : P.length ≤ 4 := by
    have h3 := env.L3
    have : fullLen h hc (tok i) ≤ 4 := by
      unfold fullLen
      split_ifs <;> omega
    omega
  have hdenseF : hc.dense = true →
      (∀ a, a < P.length → P.getD a 0 + a = P.getD 0 0) ∧ i ≤ P.getD 0 0 + 1 := by
    intro hd
    obtain ⟨bd, hb1, hb2, hbd⟩ := cand_iff h.mask env.mne n i
    have hall : ∀ k ∈ cand h.mask n i, hc.cands.getD (tok k) false = true := by
      intro k hk
      have hkn := Lane4.R7K3.hs_cand_lt hi hk
      exact dense_getD hd (by rw [env.hlen]; exact (env.hx k hkn).1)
    obtain ⟨h1, h2⟩ := pos_dense bd hbd hall hW hpos
    exact ⟨h1, by omega⟩
  have hdense1 : hc.dense = true → ∀ a, a < P.length → P.getD a 0 + a = P.getD 0 0 :=
    fun hd => (hdenseF hd).1
  have hdense2 : hc.dense = true → i ≤ P.getD 0 0 + 1 := fun hd => (hdenseF hd).2
  -- the reference rank
  have hrefA : (hc.dense = true → ref = argmaxNom h hc (tok i) keys (keys.length - 1)) ∧
      (¬ hc.dense = true → ref = 0) := by
    rw [hrefd]
    unfold refRank
    constructor
    · intro hd
      rw [if_pos hd]
    · intro hd
      rw [if_neg hd]
  have href_lt : ref < P.length := by
    by_cases hd : hc.dense = true
    · rw [hrefA.1 hd]
      have := argmax_le h hc (tok i) keys (keys.length - 1)
      omega
    · rw [hrefA.2 hd]
      exact hpos
  have hmaxnom : hc.dense = true → nomAt h hc (tok i) keys 0 ≤ nomAt h hc (tok i) keys ref := by
    intro hd
    rw [hrefA.1 hd]
    exact argmax_max h hc (tok i) keys (keys.length - 1) 0 (Nat.zero_le _)
  have hmemo : ∀ a, a ∈ others ↔ a < P.length ∧ a ≠ ref := by
    intro a
    rw [hotd, mem_otherRanks, hkl]
  have hond : others.Nodup := by
    rw [hotd]
    exact otherRanks_nodup _ _
  have holen : others.length + 1 ≤ P.length := by
    have := otherRanks_len_le keys.length ref (by omega)
    rw [← hotd, hkl] at this
    exact this
  have hposinj : ∀ a b, a < P.length → b < P.length → P.getD a 0 = P.getD b 0 → a = b :=
    fun a b ha hb h' => dec_inj hP1 ha hb h'
  obtain ⟨W, hWdef⟩ : ∃ W : List ℕ, W = others.map (fun a => P.getD a 0) := ⟨_, rfl⟩
  have hWl : W.length = others.length := by rw [hWdef, List.length_map]
  have hWget : ∀ j, j < others.length → W.getD j 0 = P.getD (others.getD j 0) 0 := by
    intro j hj
    rw [hWdef]
    exact Lane4.R8KA.k_getD_map (fun a => P.getD a 0) 0 0 others j hj
  have hWnd : W.Nodup := by
    rw [hWdef]
    apply List.Nodup.map_on _ hond
    intro a ha b hb hab
    have ha' := (hmemo a).mp ha
    have hb' := (hmemo b).mp hb
    exact hposinj a b ha'.1 hb'.1 hab
  have hWmem : ∀ k ∈ W, k ∈ c ∧ k ≠ P.getD ref 0 := by
    intro k hk
    rw [hWdef] at hk
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hk
    have ha' := (hmemo a).mp ha
    refine ⟨hPC a ha'.1, ?_⟩
    intro hcon
    exact ha'.2 (hposinj a ref ha'.1 href_lt hcon)
  -- ratios
  have hrs' := allSome_spec (0, 0) _ rs hrs
  have hrslen : rs.length = others.length := by
    have := hrs'.1
    simpa using this
  have hrat : ∀ j, j < W.length → 0 ≤ ((rs.getD j (0, 0)).1 : ℝ) ∧
      ((rs.getD j (0, 0)).1 : ℝ) ≤ Real.exp (h.score fl dA dm x i (W.getD j 0)
        - h.score fl dA dm x i (P.getD ref 0)) ∧
      Real.exp (h.score fl dA dm x i (W.getD j 0) - h.score fl dA dm x i (P.getD ref 0))
        ≤ ((rs.getD j (0, 0)).2 : ℝ) := by
    intro j hj
    rw [hWl] at hj
    have h1 := hrs'.2 j (by simpa using hj)
    have h2 : ratioAt δ h hc (tok i) keys ref (others.getD j 0) = some (rs.getD j (0, 0)) := by
      rw [Lane4.R8KA.k_getD_map _ 0 none others j hj] at h1
      exact h1
    have ha' := (hmemo _).mp (zgetD_mem' 0 others j hj)
    rw [hWget j hj]
    exact ratio_real env hi hti P keys ref hP1 hcd hlei hkey hdense1 hdense2 hlen4 hrefA.2
      href_lt ha'.1 ha'.2 h2
  have hjr := p0_jr_le env hi hti P keys ref hcd hlei hkey hdense1 hdense2 hlen4 hrefA.2 href_lt
    hmaxnom hguard hpos
  -- the tail
  have hrest : ((c.filter (fun k => decide (k ≠ P.getD ref 0 ∧ k ∉ W))).map
      (fun k => Real.exp (h.score fl dA dm x i k - h.score fl dA dm x i (P.getD ref 0)))).sum
      ≤ ((tl : ℚ) : ℝ) := by
    have hTP : ∀ k ∈ c, k ≠ P.getD ref 0 → k ∉ W → k ∉ P := by
      intro k hk hk1 hk2 hkP
      obtain ⟨a, ha, rfl⟩ := mem_getD_idx P k hkP
      by_cases har : a = ref
      · subst har
        exact hk1 rfl
      · apply hk2
        rw [hWdef]
        exact List.mem_map.mpr ⟨a, (hmemo a).mpr ⟨ha, har⟩, rfl⟩
    by_cases hnf : P.length < fullLen h hc (tok i)
    · have htl0 : tl = 0 := by
        rw [htld]
        exact tlOf_notfull (by omega)
      have hemp : c.filter (fun k => decide (k ≠ P.getD ref 0 ∧ k ∉ W)) = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro k hk
        rw [List.mem_filter] at hk
        obtain ⟨hk1, hk2⟩ := hk
        have hk2' := of_decide_eq_true hk2
        have hk3 := (hcmem k).mp hk1
        exact hTP k hk1 hk2'.1 hk2'.2 (hfull hnf k hk3.1 hk3.2)
      rw [hemp, htl0]
      simp
    · have hlenfull : P.length = fullLen h hc (tok i) := le_antisymm hlen (not_lt.mp hnf)
      have htl : tl = 3 * tailB δ h hc := by
        rw [htld]
        exact tlOf_full (by omega)
      rw [htl]
      have hTnd : (c.filter (fun k => decide (k ≠ P.getD ref 0 ∧ k ∉ W))).Nodup :=
        hcnd.filter _
      refine tail_real env hi hti _ hTnd (P.getD 0 0) (P.getD ref 0) (hlei 0 hpos) (hcd 0 hpos)
        hjr ?_
      intro k hk
      rw [List.mem_filter] at hk
      obtain ⟨hk1, hk2⟩ := hk
      have hk2' := of_decide_eq_true hk2
      have hkP := hTP k hk1 hk2'.1 hk2'.2
      have htail := pos_tail hW hpos (fun k hk => (hcmem k).mp hk) k hk1 hkP
      obtain ⟨hk3, hk4⟩ := (hcmem k).mp hk1
      refine ⟨?_, cand_le env.mne hk3, hk4⟩
      have : hc.L ≤ P.length := by
        rw [hlenfull]
        unfold fullLen
        omega
      omega
  have htl0 : (0 : ℝ) ≤ ((tl : ℚ) : ℝ) := by
    by_cases hnf : P.length < fullLen h hc (tok i)
    · rw [htld, tlOf_notfull (by omega)]
      simp
    · rw [htld, tlOf_full (by omega)]
      have := tailB_nonneg env.room
      have : (0 : ℚ) ≤ 3 * tailB δ h hc := by linarith
      exact_mod_cast this
  obtain ⟨a, ha1, ha0, haS, hmix⟩ := weights_real c hcnd (fun k => h.score fl dA dm x i k)
    (P.getD ref 0) (hPC ref href_lt) W rs tl hWnd hWmem (by rw [hWl]; exact hrslen) hrat htl0 hrest
  -- the symbols
  have hwsl : ws.length = others.length := by rw [hwsdef, List.length_map, hrslen]
  have hwsget : ∀ j, j < others.length → ws.getD j (0, 0)
      = weightIV (rs.getD j (0, 0)) (sumFst rs) (sumSnd rs) tl := by
    intro j hj
    rw [hwsdef]
    exact Lane4.R8KA.k_getD_map (fun w => weightIV w (sumFst rs) (sumSnd rs) tl) (0, 0) (0, 0) rs j
      (by rw [hrslen]; exact hj)
  have hint2 : ∀ j, j < W.length →
      ((((ws.getD j (0, 0)).1 + (ws.getD j (0, 0)).2) / 2 : ℚ) : ℝ)
        - ((((ws.getD j (0, 0)).2 - (ws.getD j (0, 0)).1) / 2 : ℚ) : ℝ) ≤ a j ∧
      a j ≤ ((((ws.getD j (0, 0)).1 + (ws.getD j (0, 0)).2) / 2 : ℚ) : ℝ)
        + ((((ws.getD j (0, 0)).2 - (ws.getD j (0, 0)).1) / 2 : ℚ) : ℝ) := by
    intro j hj
    have hj' : j < others.length := by rw [← hWl]; exact hj
    obtain ⟨h1, h2⟩ := ha1 j hj
    rw [← hwsget j hj'] at h1 h2
    push_cast
    constructor <;> linarith
  obtain ⟨e', he'1, he'2⟩ := weights_symbols W.length
    (fun j => ((((ws.getD j (0, 0)).1 + (ws.getD j (0, 0)).2) / 2 : ℚ) : ℝ))
    (fun j => ((((ws.getD j (0, 0)).2 - (ws.getD j (0, 0)).1) / 2 : ℚ) : ℝ)) a hint2
  refine ⟨e', he'1, ?_⟩
  intro e he
  have hlenV : (h.attn fl ex dA dV dm dg dgb n x i).length = dd := by
    unfold AHead.attn
    rw [aattn_length, e_Vlen env]
  have hattn : h.attn fl ex dA dV dm dg dgb n x i
      = aattnRows fl ex h.V dV c (fun j => h.score fl dA dm x i j) x 0 := by
    unfold AHead.attn
    rw [hcdef]
  refine ⟨?_, ?_⟩
  · rw [hlenV, ho, List.length_map, List.length_range]
  · intro ρ hρ
    rw [hlenV] at hρ
    have hVρ : ρ < h.V.length := by rw [e_Vlen env]; exact hρ
    rw [ho, gd_map_range _ _ dd ρ hρ, hattn, aattn_getD fl ex dV c _ x h.V 0 ρ hVρ, Nat.zero_add]
    have hr : h.V.getD ρ [] ∈ h.V := zgetD_mem' [] h.V ρ hVρ
    unfold InAF
    rw [coordAF_c, coordAF_t, coordAF_r]
    -- centre of the form
    have hdl : ws.length = (others.map (fun k => (vAt hc (keys.getD k 0) ρ).1
        - (vAt hc (keys.getD ref 0) ρ).1)).length := by
      rw [hwsl, List.length_map]
    have hmidws : ∀ j, j < ws.length →
        a j = ((((ws.getD j (0, 0)).1 + (ws.getD j (0, 0)).2) / 2 : ℚ) : ℝ)
          + ((((ws.getD j (0, 0)).2 - (ws.getD j (0, 0)).1) / 2 : ℚ) : ℝ) * e' j := by
      intro j hj
      rw [hwsl, ← hWl] at hj
      exact he'2 j hj
    have hews : ∀ j, j < ws.length → e (pre + j) = e' j := by
      intro j hj
      apply he
      rw [hwsl] at hj
      omega
    have hcen := af_centre ws (others.map (fun k => (vAt hc (keys.getD k 0) ρ).1
        - (vAt hc (keys.getD ref 0) ρ).1)) hdl (vAt hc (keys.getD ref 0) ρ).1 pre e a e' hmidws
        hews
    rw [hcen]
    -- the sum over the window
    have hsum : ((List.range ws.length).map (fun j => a j * (((others.map (fun k =>
        (vAt hc (keys.getD k 0) ρ).1 - (vAt hc (keys.getD ref 0) ρ).1)).getD j 0 : ℚ) : ℝ))).sum
        = ((List.range W.length).map (fun j => a j * ((((vAt hc (keys.getD (others.getD j 0) 0) ρ).1 : ℚ) : ℝ)
            - (((vAt hc (keys.getD ref 0) ρ).1 : ℚ) : ℝ)))).sum := by
      rw [hwsl, hWl]
      apply lsum_congr
      intro j hj
      have hj' := List.mem_range.mp hj
      rw [Lane4.R8KA.k_getD_map (fun k => (vAt hc (keys.getD k 0) ρ).1
        - (vAt hc (keys.getD ref 0) ρ).1) 0 0 others j hj']
      push_cast
      ring
    rw [hsum]
    -- bounds
    obtain ⟨Rq, hRq⟩ : ∃ Rq : ℚ, Rq = (keys.map (fun k => (vAt hc k ρ).2)).foldl max 0 :=
      ⟨_, rfl⟩
    rw [← hRq]
    have hRk : ∀ a', a' < P.length → (((vAt hc (keys.getD a' 0) ρ).2 : ℚ) : ℝ) ≤ ((Rq : ℚ) : ℝ) := by
      intro a' ha'
      have hm : (vAt hc (keys.getD a' 0) ρ).2 ∈ keys.map (fun k => (vAt hc k ρ).2) :=
        List.mem_map.mpr ⟨keys.getD a' 0, zgetD_mem' 0 keys a' (by rw [hkl]; exact ha'), rfl⟩
      have := (fmax_aux (keys.map (fun k => (vAt hc k ρ).2)) 0).2 _ hm
      rw [← hRq] at this
      exact_mod_cast this
    have hBρ := e_Bv env hρ
    obtain ⟨Bq, hBq⟩ : ∃ Bq : ℚ, Bq = bfRel δ E hc.cands (h.V.getD ρ []) := ⟨_, rfl⟩
    rw [hBρ, ← hBq]
    have hsav := row_savg env hex hi hti hr ρ (p := P.getD 0 0) (by rw [← hcdef]; exact hPC 0 hpos)
      (by rw [← hcdef]; exact hmaxc)
    rw [← hcdef, ← hBq] at hsav
    have hBk : ∀ k ∈ c, |ardot fl (h.V.getD ρ []) (x k) (dV ρ) 0 0| ≤ ((Bq : ℚ) : ℝ) := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := (hcmem k).mp hk
      rw [hBq]
      exact e_fk_bound env hr (Lane4.R7K3.hs_cand_lt hi hk1) hk2 ρ
    have hmx := hmix (fun k => ardot fl (h.V.getD ρ []) (x k) (dV ρ) 0 0) ((Bq : ℚ) : ℝ) hBk
    have hjrn : P.getD ref 0 < n := lt_of_le_of_lt (hlei ref href_lt) hi
    have hcore := row_core c (fun j => h.score fl dA dm x i j)
      (fun k => ardot fl (h.V.getD ρ []) (x k) (dV ρ) 0 0)
      (savg fl ex c (fun j => h.score fl dA dm x i j)
        (fun j => ardot fl (h.V.getD ρ []) (x j) (dV ρ) 0 0))
      (P.getD ref 0) W a
      (fun j => (((vAt hc (keys.getD (others.getD j 0) 0) ρ).1 : ℚ) : ℝ))
      (((vAt hc (keys.getD ref 0) ρ).1 : ℚ) : ℝ) ((Rq : ℚ) : ℝ) ((Bq : ℚ) : ℝ) ((tl : ℚ) : ℝ)
      hsav hmx ha0 haS (by
        have := e_key_val env hρ hjrn
        rw [← hkey ref href_lt] at this
        exact le_trans this (hRk ref href_lt)) (by
        intro j hj
        rw [hWl] at hj
        have ha' := (hmemo _).mp (zgetD_mem' 0 others j hj)
        have hjn : P.getD (others.getD j 0) 0 < n := lt_of_le_of_lt (hlei _ ha'.1) hi
        have := e_key_val env hρ hjn
        rw [← hkey _ ha'.1] at this
        rw [hWget j hj]
        exact le_trans this (hRk _ ha'.1))
    have hsd : ((softDen : ℚ) : ℝ) = 2 ^ 13 := by
      unfold softDen
      norm_num
    push_cast
    rw [hsd]
    obtain ⟨c1, c2⟩ := abs_le.mp hcore
    rw [abs_le]
    constructor <;> linarith

end

theorem head_sound_ln : HeadSoundLN := by
  intro u η M fl ex hC hex δ hδ0 hδ1 h E hc dd hok hsh hdd sA sV sg sgb hrows dA dV dm dg dgb
    hdA hdV hdm hdg hdgb n x tok hun hηn hM hx i hi hti P pre hW hlen hfull o hh
  obtain ⟨hmask, hm1, hm2, hlen', hgate, hVE, hBv, hBv20, hsp, hpair, hL1, hL3, hroom⟩ :=
    open8 hok
  have env : Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok :=
    ⟨hC, hδ0, hδ1, hok, hsh, hdd, sA, sV, sg, sgb, hrows, hdA, hdV, hdm, hdg, hdgb, hun, hηn, hM,
      hx, hmask, hm1, hm2, hlen', hgate, hVE, hBv, hBv20, hsp, hpair, hL1, hL3, hroom⟩
  by_cases hP : P = []
  · exact head_nokey env hex hi hti pre hP hfull hh
  · have hpos : 0 < P.length := by
      cases P with
      | nil => exact absurd rfl hP
      | cons a P' => simp
    exact head_keys env hex hi hti pre hW hlen hfull hpos hh

end Lane4.LNKC



