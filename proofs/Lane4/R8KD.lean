/-
Lane 4, rung 7 kit module, assembled by tools/r7_assemble.py from kit case kd
(runs/r8-kit/kd): statements by the lane, proofs by a Sonnet doctor, checked by tools/check.py.
-/
import Lane4.R8Soft

namespace Lane4.R8KD
open Lane4.RSeq Lane4.RSoft

/-- SHARED ATTENTION OVER A WINDOW. Pure real analysis: no rounding, no floats.
`c` are the candidate positions, `jr ∈ c` the reference key, `W` a list of other candidates (the
window). For the `i`-th window key the ratio `exp (s k - s jr)` lies in `[lo i, hi i]`; the ratios
of all remaining candidates sum to at most `tl`. Then there are weights `a i`, ONE set for every
value function `f`, each inside the stated interval, non-negative and summing to at most 1, such
that the exact softmax average of `f` is the reference value plus the weighted value differences,
up to `2 * tl * B`. -/
def MixBound : Prop :=
  ∀ (c : List ℕ), c.Nodup → ∀ (s : ℕ → ℝ) (jr : ℕ), jr ∈ c →
  ∀ (W : List ℕ) (lo hi : List ℝ), W.Nodup → (∀ k ∈ W, k ∈ c ∧ k ≠ jr) →
  lo.length = W.length → hi.length = W.length →
  (∀ i, i < W.length → 0 ≤ lo.getD i 0 ∧ lo.getD i 0 ≤ Real.exp (s (W.getD i 0) - s jr) ∧
                        Real.exp (s (W.getD i 0) - s jr) ≤ hi.getD i 0) →
  ∀ tl : ℝ, 0 ≤ tl →
  ((c.filter (fun k => decide (k ≠ jr ∧ k ∉ W))).map (fun k => Real.exp (s k - s jr))).sum ≤ tl →
  ∃ a : ℕ → ℝ,
    (∀ i, i < W.length →
       lo.getD i 0 / (1 + lo.getD i 0 + (hi.sum - hi.getD i 0) + tl) ≤ a i ∧
       a i ≤ hi.getD i 0 / (1 + hi.getD i 0 + (lo.sum - lo.getD i 0))) ∧
    (∀ i, 0 ≤ a i) ∧
    ((List.range W.length).map a).sum ≤ 1 ∧
    ∀ (f : ℕ → ℝ) (B : ℝ), (∀ k ∈ c, |f k| ≤ B) →
      |eavg c s f
        - (f jr + ((List.range W.length).map (fun i => a i * (f (W.getD i 0) - f jr))).sum)|
        ≤ 2 * tl * B

end Lane4.R8KD


set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace Lane4.R8KD
open Lane4.RSeq Lane4.RSoft

theorem lc_sum_range (n : ℕ) (g : ℕ → ℝ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp

theorem lc_sum_getD {α : Type} (d : α) (W : List α) (g : α → ℝ) :
    ((List.range W.length).map (fun i => g (W.getD i d))).sum = (W.map g).sum := by
  induction W with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    have : ((fun i => g ((a :: l).getD i d)) ∘ Nat.succ) = fun i => g (l.getD i d) := by
      funext i; simp
    rw [this, ih]; simp

theorem lc_abs_bound (r f : ℕ → ℝ) (B : ℝ) (hr : ∀ k, 0 ≤ r k) :
    ∀ l : List ℕ, (∀ k ∈ l, |f k| ≤ B) →
      |(l.map (fun k => r k * f k)).sum| ≤ B * (l.map r).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    have ha := h a (by simp)
    have ih' := ih (fun k hk => h k (by simp [hk]))
    simp only [List.map_cons, List.sum_cons]
    have h1 := abs_le.mp ih'
    have h2 : |r a * f a| ≤ r a * B := by
      rw [abs_mul, abs_of_nonneg (hr a)]
      exact mul_le_mul_of_nonneg_left ha (hr a)
    have h3 := abs_le.mp h2
    apply abs_le.mpr
    constructor <;> nlinarith [h1.1, h1.2, h3.1, h3.2]

theorem lc_split (c : List ℕ) (hc : c.Nodup) (jr : ℕ) (hjr : jr ∈ c) (W : List ℕ)
    (hWn : W.Nodup) (hW : ∀ k ∈ W, k ∈ c ∧ k ≠ jr) (rest : List ℕ)
    (hrest : rest = c.filter (fun k => decide (k ≠ jr ∧ k ∉ W))) (g : ℕ → ℝ) :
    (c.map g).sum = g jr + (W.map g).sum + (rest.map g).sum := by
  subst hrest
  have h1 : (c.map g).sum = ∑ k ∈ c.toFinset, g k := (List.sum_toFinset g hc).symm
  have h2 : (W.map g).sum = ∑ k ∈ W.toFinset, g k := (List.sum_toFinset g hWn).symm
  have h3 : ((c.filter (fun k => decide (k ≠ jr ∧ k ∉ W))).map g).sum
      = ∑ k ∈ (c.filter (fun k => decide (k ≠ jr ∧ k ∉ W))).toFinset, g k :=
    (List.sum_toFinset g (hc.filter _)).symm
  have hS : c.toFinset = insert jr (W.toFinset ∪
      (c.filter (fun k => decide (k ≠ jr ∧ k ∉ W))).toFinset) := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset, List.mem_filter,
      decide_eq_true_eq]
    constructor
    · intro hk
      by_cases e1 : k = jr
      · exact Or.inl e1
      · by_cases e2 : k ∈ W
        · exact Or.inr (Or.inl e2)
        · exact Or.inr (Or.inr ⟨hk, e1, e2⟩)
    · rintro (h | h | ⟨h, _⟩)
      · rw [h]; exact hjr
      · exact (hW k h).1
      · exact h
  have hn : jr ∉ W.toFinset ∪ (c.filter (fun k => decide (k ≠ jr ∧ k ∉ W))).toFinset := by
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    rintro (h | ⟨_, h, _⟩)
    · exact (hW jr h).2 rfl
    · exact h rfl
  have hd : Disjoint W.toFinset (c.filter (fun k => decide (k ≠ jr ∧ k ∉ W))).toFinset := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hk1 hk2
    exact hk2.2.2 hk1
  rw [h1, h2, h3, hS, Finset.sum_insert hn, Finset.sum_union hd]
  ring

theorem mix_bound : MixBound := by
  intro c hc s jr hjr W lo hi hWn hW hlol hhil hint tl htl hrest
  obtain ⟨rest, hrest_def⟩ : ∃ rest : List ℕ,
      rest = c.filter (fun k => decide (k ≠ jr ∧ k ∉ W)) := ⟨_, rfl⟩
  rw [← hrest_def] at hrest
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℝ, r = fun k => Real.exp (s k - s jr) := ⟨_, rfl⟩
  have hrk : ∀ k, r k = Real.exp (s k - s jr) := by intro k; rw [hr]
  have hrpos : ∀ k, 0 < r k := fun k => by rw [hrk]; exact Real.exp_pos _
  have hr1 : r jr = 1 := by rw [hrk]; simp
  have hrest' : (rest.map r).sum ≤ tl := by rw [hr]; exact hrest
  have hint' : ∀ i, i < W.length → 0 ≤ lo.getD i 0 ∧ lo.getD i 0 ≤ r (W.getD i 0) ∧
      r (W.getD i 0) ≤ hi.getD i 0 := by
    intro i hin; rw [hrk]; exact hint i hin
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = (c.map r).sum := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ∑ i ∈ Finset.range W.length, r (W.getD i 0) := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = (rest.map r).sum := ⟨_, rfl⟩
  have hWR : (W.map r).sum = R := by
    have := lc_sum_getD (0:ℕ) W r
    rw [lc_sum_range] at this
    rw [hR]; exact this.symm
  have hZeq : Z = 1 + R + T := by
    rw [hZdef, lc_split c hc jr hjr W hWn hW rest hrest_def r, hr1, hWR, hTdef]
  have hR0 : 0 ≤ R := by rw [hR]; exact Finset.sum_nonneg (fun i _ => (hrpos _).le)
  have hT0 : 0 ≤ T := by
    rw [hTdef]
    exact List.sum_nonneg (by
      intro x hx
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
      exact (hrpos k).le)
  have hTtl : T ≤ tl := by rw [hTdef]; exact hrest'
  have hZpos : 0 < Z := by rw [hZeq]; linarith
  have hZ1 : 1 ≤ Z := by rw [hZeq]; linarith
  obtain ⟨LO, hLOdef⟩ : ∃ LO : ℝ, LO = lo.sum := ⟨_, rfl⟩
  obtain ⟨HI, hHIdef⟩ : ∃ HI : ℝ, HI = hi.sum := ⟨_, rfl⟩
  have hLO : LO = ∑ i ∈ Finset.range W.length, lo.getD i 0 := by
    have h := lc_sum_getD (0:ℝ) lo id
    simp only [id_eq, List.map_id, hlol] at h
    rw [hLOdef]
    exact h.symm.trans (lc_sum_range _ _)
  have hHI : HI = ∑ i ∈ Finset.range W.length, hi.getD i 0 := by
    have h := lc_sum_getD (0:ℝ) hi id
    simp only [id_eq, List.map_id, hhil] at h
    rw [hHIdef]
    exact h.symm.trans (lc_sum_range _ _)
  have hfacts : ∀ i, i < W.length →
      R - r (W.getD i 0) ≤ HI - hi.getD i 0 ∧ LO - lo.getD i 0 ≤ R - r (W.getD i 0) ∧
      0 ≤ LO - lo.getD i 0 := by
    intro i hin
    have hmem : i ∈ Finset.range W.length := Finset.mem_range.mpr hin
    have k1 : hi.getD i 0 - r (W.getD i 0) ≤
        ∑ j ∈ Finset.range W.length, (hi.getD j 0 - r (W.getD j 0)) :=
      Finset.single_le_sum (f := fun j => hi.getD j 0 - r (W.getD j 0))
        (fun j hj => by have := hint' j (Finset.mem_range.mp hj); linarith) hmem
    have k2 : r (W.getD i 0) - lo.getD i 0 ≤
        ∑ j ∈ Finset.range W.length, (r (W.getD j 0) - lo.getD j 0) :=
      Finset.single_le_sum (f := fun j => r (W.getD j 0) - lo.getD j 0)
        (fun j hj => by have := hint' j (Finset.mem_range.mp hj); linarith) hmem
    have k3 : lo.getD i 0 ≤ ∑ j ∈ Finset.range W.length, lo.getD j 0 :=
      Finset.single_le_sum (f := fun j => lo.getD j 0)
        (fun j hj => (hint' j (Finset.mem_range.mp hj)).1) hmem
    rw [Finset.sum_sub_distrib, ← hHI, ← hR] at k1
    rw [Finset.sum_sub_distrib, ← hLO, ← hR] at k2
    rw [← hLO] at k3
    refine ⟨by linarith, by linarith, by linarith⟩
  refine ⟨fun i => if i < W.length then r (W.getD i 0) / Z else 0, ?_, ?_, ?_, ?_⟩
  · intro i hin
    simp only [if_pos hin]
    obtain ⟨hA, hB, hC⟩ := hfacts i hin
    obtain ⟨hl0, hlx, hxh⟩ := hint' i hin
    have hx0 := hrpos (W.getD i 0)
    generalize r (W.getD i 0) = x at *
    generalize lo.getD i 0 = l at *
    generalize hi.getD i 0 = h at *
    constructor
    · rw [div_le_div_iff₀ (by linarith) hZpos]
      have hZle : Z ≤ 1 + x + ((HI - h) + tl) := by rw [hZeq]; linarith
      nlinarith [mul_nonneg (sub_nonneg.2 hlx) (show 0 ≤ 1 + ((HI - h) + tl) by linarith),
        mul_le_mul_of_nonneg_left hZle hl0]
    · rw [div_le_div_iff₀ hZpos (by linarith)]
      have hZge : 1 + x + (LO - l) ≤ Z := by rw [hZeq]; linarith
      nlinarith [mul_nonneg (sub_nonneg.2 hxh) (show 0 ≤ 1 + (LO - l) by linarith),
        mul_le_mul_of_nonneg_left hZge (show 0 ≤ h by linarith)]
  · intro i
    dsimp only
    split_ifs
    · exact div_nonneg (hrpos _).le hZpos.le
    · exact le_refl _
  · rw [lc_sum_range]
    have hsum : ∑ i ∈ Finset.range W.length,
        (if i < W.length then r (W.getD i 0) / Z else 0) = R / Z := by
      rw [hR, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi'
      rw [if_pos (Finset.mem_range.mp hi')]
    refine le_trans (le_of_eq hsum) ?_
    rw [div_le_one hZpos, hZeq]; linarith
  · intro f B hB
    have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB jr hjr)
    have hexp : ∀ k, Real.exp (s k) = Real.exp (s jr) * r k := by
      intro k; rw [hrk, ← Real.exp_add]; congr 1; ring
    have hnum : (c.map fun k => Real.exp (s k) * f k).sum
        = Real.exp (s jr) * (c.map fun k => r k * f k).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      apply List.map_congr_left
      intro k _
      rw [hexp k]; ring
    have hden : (c.map fun k => Real.exp (s k)).sum = Real.exp (s jr) * (c.map r).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      apply List.map_congr_left
      intro k _
      rw [hexp k]
    have hE : eavg c s f = (c.map fun k => r k * f k).sum / Z := by
      unfold eavg
      rw [hnum, hden, mul_div_mul_left _ _ (Real.exp_pos _).ne', hZdef]
    have hsp := lc_split c hc jr hjr W hWn hW rest hrest_def (fun k => r k * f k)
    have hSW : (W.map fun k => r k * f k).sum
        = ∑ i ∈ Finset.range W.length, r (W.getD i 0) * f (W.getD i 0) := by
      have := lc_sum_getD (0:ℕ) W (fun k => r k * f k)
      rw [lc_sum_range] at this
      exact this.symm
    obtain ⟨SW, hSWdef⟩ : ∃ SW : ℝ, SW = (W.map fun k => r k * f k).sum := ⟨_, rfl⟩
    obtain ⟨SR, hSRdef⟩ : ∃ SR : ℝ, SR = (rest.map fun k => r k * f k).sum := ⟨_, rfl⟩
    have hwin : ((List.range W.length).map
        (fun i => (if i < W.length then r (W.getD i 0) / Z else 0) *
          (f (W.getD i 0) - f jr))).sum = (SW - f jr * R) / Z := by
      rw [lc_sum_range, hSWdef, hSW, hR, Finset.mul_sum, ← Finset.sum_sub_distrib,
        Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi'
      have := Finset.mem_range.mp hi'
      simp only [if_pos this]
      ring
    rw [hwin, hE, hsp, hr1, ← hSWdef, ← hSRdef]
    have hZne : Z ≠ 0 := hZpos.ne'
    have key : (1 * f jr + SW + SR) / Z - (f jr + (SW - f jr * R) / Z)
        = (SR - f jr * T) / Z := by
      field_simp
      rw [hZeq]; ring
    rw [key]
    have hSRb : |SR| ≤ B * T := by
      rw [hSRdef, hTdef]
      exact lc_abs_bound r f B (fun k => (hrpos k).le) rest (by
        intro k hk
        rw [hrest_def, List.mem_filter] at hk
        exact hB k hk.1)
    have hfT : |f jr * T| ≤ B * T := by
      rw [abs_mul, abs_of_nonneg hT0]
      exact mul_le_mul_of_nonneg_right (hB jr hjr) hT0
    have hnum' : |SR - f jr * T| ≤ 2 * tl * B := by
      have e1 := abs_le.mp hSRb
      have e2 := abs_le.mp hfT
      have e3 : B * T ≤ B * tl := mul_le_mul_of_nonneg_left hTtl hB0
      apply abs_le.mpr
      constructor <;> nlinarith
    rw [abs_div, abs_of_pos hZpos]
    calc |SR - f jr * T| / Z ≤ |SR - f jr * T| := div_le_self (abs_nonneg _) hZ1
      _ ≤ 2 * tl * B := hnum'

end Lane4.R8KD

