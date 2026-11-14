set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option pp.oneline true

namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

def zr: List ℚ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def ur0 : List ℚ := [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def ur1 : List ℚ := [0,1,0,0,0,0,0,0,0,0,0,0,0,0,0]
def ur2 : List ℚ := [0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
def ur3 : List ℚ := [0,0,0,1,0,0,0,0,0,0,0,0,0,0,0]
def ur11 : List ℚ := [0,0,0,0,0,0,0,0,0,0,0,1,0,0,0]
def ur13 : List ℚ := [0,0,0,0,0,0,0,0,0,0,0,0,0,1,0]
def ar0 : List ℚ := [0,0,0,0,3/2,2,0,0,0,0,0,0,0,0,0]
def ar1 : List ℚ := [0,0,0,0,3/2,0,2,0,0,0,0,0,0,0,0]
def ar2 : List ℚ := [0,0,0,0,3/2,0,0,2,0,0,0,0,0,0,0]
def wr0 : List ℚ := [3,0,0,0,0,0,0,0,1,0,0,0,0,0,0]
def wr1 : List ℚ := [0,3,0,0,0,0,0,0,0,1,0,0,0,0,0]
def wr2 : List ℚ := [0,0,3,0,0,0,0,0,0,0,1,0,0,0,0]

def head0 : Head :=
  { A := [zr,zr,zr,zr,zr,zr,zr,zr,zr,zr,zr,zr,ur13,zr,zr],
    V := [zr,zr,zr,zr,zr,ur0,ur1,ur2,zr,zr,zr,zr,zr,zr,zr],
    mask := Mask.strict }

def blk0 : Block :=
  { heads := [head0], W1 := [], b1 := [],
    W2 := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]], b2 := zr }

def hd10 : Head :=
  { A := [zr,zr,zr,zr,zr,zr,zr,zr,zr,zr,zr,zr,ur13,zr,ar0],
    V := [zr,zr,zr,zr,zr,zr,zr,zr,ur3,zr,zr,zr,zr,zr,zr],
    mask := Mask.causal }

def hd11 : Head :=
  { A := [zr,zr,zr,zr,zr,zr,zr,zr,zr,zr,zr,zr,ur13,zr,ar1],
    V := [zr,zr,zr,zr,zr,zr,zr,zr,zr,ur3,zr,zr,zr,zr,zr],
    mask := Mask.causal }

def hd12 : Head :=
  { A := [zr,zr,zr,zr,zr,zr,zr,zr,zr,zr,zr,zr,ur13,zr,ar2],
    V := [zr,zr,zr,zr,zr,zr,zr,zr,zr,zr,ur3,zr,zr,zr,zr],
    mask := Mask.causal }


theorem head0_V : head0.V = [zr,zr,zr,zr,zr,ur0,ur1,ur2,zr,zr,zr,zr,zr,zr,zr] := rfl
theorem hd10_V : hd10.V = [zr,zr,zr,zr,zr,zr,zr,zr,ur3,zr,zr,zr,zr,zr,zr] := rfl
theorem hd11_V : hd11.V = [zr,zr,zr,zr,zr,zr,zr,zr,zr,ur3,zr,zr,zr,zr,zr] := rfl
theorem hd12_V : hd12.V = [zr,zr,zr,zr,zr,zr,zr,zr,zr,zr,ur3,zr,zr,zr,zr] := rfl

def blk1 : Block :=
  { heads := [hd10, hd11, hd12], W1 := [wr0, wr1, wr2], b1 := [-3, -3, -3],
    W2 := [[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],
           [1,1,1],[0,0,0],[0,0,0],[0,0,0]],
    b2 := zr }

def net : TNet :=
  { embed := [[0,0,0,0,1,0,0,0,0,0,0,0], [1,0,0,2,0,0,0,0,0,0,0,0],
              [0,1,0,0,0,0,0,0,0,0,0,0], [0,0,1,2,0,0,0,0,0,0,0,0]],
    blocks := [blk0, blk1],
    outW := ur11,
    outB := 0 }

/-! ### numeric helpers -/

theorem flb {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {x : ℝ} (hx : |x| ≤ 100) : |fl x - x| ≤ 1 / 100000 := by
  have h2 := hr.err hu0 hx
  have h3 : u * 100 ≤ 1 / 100000 := by linarith
  exact le_trans h2 h3

theorem fl_approx {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {x t e : ℝ} (hx : |x - t| ≤ e) (ht : |t| ≤ 50) (he : e ≤ 40) :
    |fl x - t| ≤ e + 1 / 100000 := by
  have h1 : |x| ≤ 100 := by
    have := abs_sub_abs_le_abs_sub x t
    linarith
  have h2 := flb hr hu0 hu1 h1
  have h4 := abs_sub_le (fl x) x t
  linarith

theorem mulb {x y s t a b r : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s * t = r)
    (hx : |x - s| ≤ a) (hy : |y - t| ≤ b) : |x * y - r| ≤ a * b + a * t + s * b := by
  subst hst
  have h : x * y - s * t = (x - s) * (y - t) + (x - s) * t + s * (y - t) := by ring
  have ha : 0 ≤ a := le_trans (abs_nonneg _) hx
  have h1 : |(x - s) * (y - t)| ≤ a * b := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) ha
  have h2 : |(x - s) * t| ≤ a * t := by
    rw [abs_mul, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_right hx ht
  have h3 : |s * (y - t)| ≤ s * b := by
    rw [abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left hy hs
  have h4 := abs_add_le ((x - s) * (y - t) + (x - s) * t) (s * (y - t))
  have h5 := abs_add_le ((x - s) * (y - t)) ((x - s) * t)
  rw [h]
  linarith

theorem sw_abs {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (w : ℚ) (v : ℝ) (hv : (w : ℝ) = v) (hv0 : 0 ≤ v) {d : ℝ}
    (hd : |d| ≤ 1 / 200) (a : ℝ) (ha : v * (1 / 190) ≤ a) : |sw fl w d - v| ≤ a := by
  have h1 := sw_rel hr hu0 w hd (ε := 1 / 190) (by linarith)
  rw [hv, abs_of_nonneg hv0] at h1
  linarith

theorem sw_bd {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (w : ℚ) (v : ℝ) (hv : (w : ℝ) = v) (hv0 : 0 ≤ v) {d : ℝ}
    (hd : |d| ≤ 1 / 200) :
    v * (1 - 1 / 190) ≤ sw fl w d ∧ sw fl w d ≤ v * (1 + 1 / 190) := by
  have h1 := sw_rel hr hu0 w hd (ε := 1 / 190) (by linarith)
  rw [hv, abs_of_nonneg hv0] at h1
  obtain ⟨h2, h3⟩ := abs_le.mp h1
  constructor <;> linarith

theorem sw_neg {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (w : ℚ) (d : ℝ) :
    sw fl (-w) d = - sw fl w d := by
  unfold sw
  rw [Rat.cast_neg, neg_mul, hr.neg]

theorem relu_near (x H : ℝ) (hH : 0 ≤ H) : |relu x - H| ≤ |x - H| := by
  show |max x 0 - H| ≤ |x - H|
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx, abs_of_nonpos (by linarith : (0 : ℝ) - H ≤ 0),
      abs_of_nonpos (by linarith : x - H ≤ 0)]
    linarith
  · exact le_of_eq (by rw [max_eq_left hx])

/-! ### tokens -/

theorem tok_le3 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) : tokAt w j ≤ 3 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h0 | h0
  · omega
  · exact (hw _ h0).2

theorem tok_pos (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : j ≤ w.length) : 1 ≤ tokAt w j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hk : k < w.length := by omega
  rw [Lane4.Seq.tokAt_succ w k hk]
  exact (hw _ (List.getElem_mem hk)).1

noncomputable def Hq (t : ℕ) : ℝ := ((if t = 1 ∨ t = 3 then 2 else 0 : ℚ) : ℝ)

theorem Hq_bd (t : ℕ) : 0 ≤ Hq t ∧ Hq t ≤ 2 := by
  unfold Hq
  by_cases h13 : t = 1 ∨ t = 3
  · simp only [if_pos h13]; norm_num
  · simp only [if_neg h13]; norm_num

theorem h_cast (t : ℕ) (ht : t ≤ 3) : ((h t : ℕ) : ℝ) = Hq t := by
  unfold Hq h
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;> norm_num

/-! ### previous occurrence -/

theorem find_rev (P : ℕ → Bool) (i : ℕ) :
    (∀ j, (List.range i).reverse.find? P = some j → j < i ∧ P j = true ∧
        ∀ k, j < k → k < i → P k = false) ∧
    ((List.range i).reverse.find? P = none → ∀ k, k < i → P k = false) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hrev : (List.range (i + 1)).reverse = i :: (List.range i).reverse := by
      simp [List.range_succ]
    rw [hrev]
    obtain ⟨ih1, ih2⟩ := ih
    by_cases hP : P i = true
    · have hf : (i :: (List.range i).reverse).find? P = some i := by
        simp [List.find?_cons, hP]
      rw [hf]
      refine ⟨fun j hj => ?_, fun hj => ?_⟩
      · have hji : i = j := by simpa using hj
        subst hji
        exact ⟨by omega, hP, fun k hk1 hk2 => absurd hk2 (by omega)⟩
      · simp at hj
    · have hP' : P i = false := by simpa using hP
      have hf : (i :: (List.range i).reverse).find? P = (List.range i).reverse.find? P := by
        simp [List.find?_cons, hP']
      rw [hf]
      refine ⟨fun j hj => ?_, fun hj k hk => ?_⟩
      · obtain ⟨a, b, c⟩ := ih1 j hj
        refine ⟨by omega, b, fun k hk1 hk2 => ?_⟩
        by_cases hki : k = i
        · subst hki; exact hP'
        · exact c k hk1 (by omega)
      · by_cases hki : k = i
        · subst hki; exact hP'
        · exact ih2 hj k (by omega)

theorem Pw_iff (w : List ℕ) (i k : ℕ) :
    (decide (1 ≤ k) && (tokAt w k == tokAt w i)) = true ↔ 1 ≤ k ∧ tokAt w k = tokAt w i := by
  simp

theorem prev_char (w : List ℕ) (i : ℕ) :
    (∀ j, prevOcc w i = some j → 1 ≤ j ∧ j < i ∧ tokAt w j = tokAt w i ∧
        ∀ k, j < k → k < i → tokAt w k ≠ tokAt w i) ∧
    (prevOcc w i = none → ∀ k, 1 ≤ k → k < i → tokAt w k ≠ tokAt w i) := by
  obtain ⟨hf1, hf2⟩ := find_rev (fun j => decide (1 ≤ j) && (tokAt w j == tokAt w i)) i
  constructor
  · intro j hj
    obtain ⟨h1, h2, h3⟩ := hf1 j hj
    obtain ⟨hj1, hjt⟩ := (Pw_iff w i j).mp h2
    refine ⟨hj1, h1, hjt, fun k hk1 hk2 heq => ?_⟩
    have h4 : (decide (1 ≤ k) && (tokAt w k == tokAt w i)) = false := h3 k hk1 hk2
    have h5 := (Pw_iff w i k).mpr ⟨by omega, heq⟩
    rw [h4] at h5
    exact Bool.false_ne_true h5
  · intro hn k hk1 hk2 heq
    have h4 : (decide (1 ≤ k) && (tokAt w k == tokAt w i)) = false := hf2 hn k hk2
    have h5 := (Pw_iff w i k).mpr ⟨hk1, heq⟩
    rw [h4] at h5
    exact Bool.false_ne_true h5

theorem target_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (i : ℕ) (hi1 : 1 ≤ i)
    (hi : i ≤ w.length) (c : ℕ) (hc : tokAt w i = c + 1) (m : ℕ) (hm : m ≤ i)
    (hmm : tokAt w (m - 1) = c + 1 ∨ (m = 0 ∧ ∀ k, k ≤ i → ¬ tokAt w (k - 1) = c + 1))
    (hgr : ∀ k, m < k → k ≤ i → ¬ tokAt w (k - 1) = c + 1) :
    ((target w i : ℕ) : ℝ) = Hq (tokAt w m) := by
  unfold target
  rcases hpo : prevOcc w i with _ | j
  · have hnone := (prev_char w i).2 hpo
    have hm0 : m = 0 := by
      rcases hmm with h1 | ⟨h0, _⟩
      · exfalso
        by_cases hm1 : m - 1 = 0
        · rw [hm1, Lane4.Seq.tokAt_zero] at h1
          omega
        · exact hnone (m - 1) (by omega) (by omega) (by rw [h1, hc])
      · exact h0
    subst hm0
    show ((0 : ℕ) : ℝ) = Hq (tokAt w 0)
    rw [Lane4.Seq.tokAt_zero]
    simp [Hq]
  · obtain ⟨hj1, hji, hjt, hjg⟩ := (prev_char w i).1 j hpo
    have hmt : tokAt w (j + 1 - 1) = c + 1 := by
      rw [Nat.add_sub_cancel, hjt, hc]
    have hjle : j + 1 ≤ i := by omega
    have hm_ge : j + 1 ≤ m := by
      by_contra hlt
      push_neg at hlt
      exact hgr (j + 1) hlt hjle hmt
    have hm_le : m ≤ j + 1 := by
      by_contra hgt
      push_neg at hgt
      rcases hmm with h1 | ⟨h0, _⟩
      · exact hjg (m - 1) (by omega) (by omega) (by rw [h1, hc])
      · omega
    have hmeq : m = j + 1 := le_antisymm hm_le hm_ge
    subst hmeq
    show ((h (tokAt w (j + 1)) : ℕ) : ℝ) = Hq (tokAt w (j + 1))
    exact h_cast _ (tok_le3 w hw _)

/-! ### stored entries -/

noncomputable def eo (fl : ℝ → ℝ) (p : Pert) (τ c : ℕ) : ℝ :=
  sw fl (if τ = c + 1 then 1 else 0) (p.E τ c)
noncomputable def ev (fl : ℝ → ℝ) (p : Pert) (τ : ℕ) : ℝ :=
  sw fl (if τ = 1 ∨ τ = 3 then 2 else 0) (p.E τ 3)
noncomputable def eb (fl : ℝ → ℝ) (p : Pert) (τ : ℕ) : ℝ :=
  sw fl (if τ = 0 then 1 else 0) (p.E τ 4)
noncomputable def nf (fl : ℝ → ℝ) (w : List ℕ) : ℝ := fl ((w.length + 1 : ℕ) : ℝ)
noncomputable def qv (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (c j : ℕ) : ℝ :=
  fl (sw fl 1 (p.V 0 0 (5 + c) c) * eo fl p (tokAt w (j - 1)) c)

theorem fl_eo {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (τ c : ℕ) :
    fl (eo fl p τ c) = eo fl p τ c := by
  unfold eo; exact fl_sw hr _ _
theorem fl_ev {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (τ : ℕ) :
    fl (ev fl p τ) = ev fl p τ := by
  unfold ev; exact fl_sw hr _ _
theorem fl_eb {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (τ : ℕ) :
    fl (eb fl p τ) = eb fl p τ := by
  unfold eb; exact fl_sw hr _ _
theorem fl_nf {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (w : List ℕ) :
    fl (nf fl w) = nf fl w := by
  unfold nf; exact hr.idem _
theorem fl_qv {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (c j : ℕ) :
    fl (qv fl p w c j) = qv fl p w c j := by
  unfold qv; exact hr.idem _

theorem eo_zero {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (τ c : ℕ)
    (hc : τ ≠ c + 1) : eo fl p τ c = 0 := by
  unfold eo
  rw [if_neg hc]
  exact sw_zero hr _

theorem eo_bos {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (c : ℕ) :
    eo fl p 0 c = 0 := eo_zero hr p 0 c (by omega)

theorem eo_one (fl : ℝ → ℝ) (p : Pert) (τ c : ℕ) (hc : τ = c + 1) :
    eo fl p τ c = sw fl 1 (p.E τ c) := by
  unfold eo
  rw [if_pos hc]

theorem eb_zero {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (τ : ℕ) (hτ : τ ≠ 0) :
    eb fl p τ = 0 := by
  unfold eb
  rw [if_neg hτ]
  exact sw_zero hr _

theorem eb_one (fl : ℝ → ℝ) (p : Pert) : eb fl p 0 = sw fl 1 (p.E 0 4) := by
  unfold eb
  rw [if_pos rfl]

theorem ev_nonneg {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (τ : ℕ) :
    0 ≤ ev fl p τ := by
  unfold ev
  by_cases h13 : τ = 1 ∨ τ = 3
  · rw [if_pos h13]
    have := sw_bd hr hu0 hu1 (2 : ℚ) 2 (by norm_num) (by norm_num) (hp.E τ 3)
    linarith [this.1]
  · rw [if_neg h13, sw_zero hr]

theorem ev_near {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (τ : ℕ) :
    |ev fl p τ - Hq τ| ≤ 1 / 95 := by
  unfold ev Hq
  by_cases h13 : τ = 1 ∨ τ = 3
  · simp only [if_pos h13]
    have := sw_abs hr hu0 hu1 (2 : ℚ) 2 (by norm_num) (by norm_num) (hp.E τ 3) (2 / 190)
      (by norm_num)
    rw [show (((2 : ℚ) : ℝ)) = 2 by norm_num]
    exact le_trans this (by norm_num)
  · simp only [if_neg h13]
    rw [sw_zero hr]
    norm_num

/-! ### the vectors -/

noncomputable def X0 (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : Vec :=
  [eo fl p (tokAt w j) 0, eo fl p (tokAt w j) 1, eo fl p (tokAt w j) 2, ev fl p (tokAt w j),
   eb fl p (tokAt w j), 0, 0, 0, 0, 0, 0, 0, 1, fl (j : ℝ), nf fl w]

noncomputable def X1 (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : Vec :=
  [eo fl p (tokAt w j) 0, eo fl p (tokAt w j) 1, eo fl p (tokAt w j) 2, ev fl p (tokAt w j),
   eb fl p (tokAt w j), qv fl p w 0 j, qv fl p w 1 j, qv fl p w 2 j, 0, 0, 0, 0, 1,
   fl (j : ℝ), nf fl w]

set_option maxHeartbeats 4000000 in
theorem init_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) :
    net.init fl p w j = X0 fl p w j := by
  have h4 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 := by
    have := tok_le3 w hw j
    omega
  rcases h4 with h0 | h0 | h0 | h0 <;>
    simp [TNet.init, net, X0, eo, ev, eb, nf, swRow, pos, h0, sw_zero hr]

set_option maxHeartbeats 4000000 in
theorem score0 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (dA : ℕ → ℕ → ℝ) (i k : ℕ) :
    head0.score fl dA (X0 fl p w i) (X0 fl p w k) = fl (sw fl 1 (dA 12 13) * fl (k : ℝ)) := by
  simp [Head.score, head0, X0, zr, ur13, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem]

theorem sel0 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    head0.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = [i - 1] := by
  apply Head.sel_unique
  · rw [show head0.mask = Mask.strict from rfl, Lane4.Seq.mem_cand_strict]
    omega
  · intro k hk hne
    rw [show head0.mask = Mask.strict from rfl, Lane4.Seq.mem_cand_strict] at hk
    rw [init_eq hr p w hw i, init_eq hr p w hw k, init_eq hr p w hw (i - 1)]
    rw [score0 hr, score0 hr]
    have hS := sw_rel hr hu0 1 (hp.A 0 0 12 13) (ε := 3 / 250) (by linarith)
    simp only [Rat.cast_one, abs_one, mul_one] at hS
    obtain ⟨hS1, hS2⟩ := abs_le.mp hS
    have hS0 : 0 ≤ sw fl 1 (p.A 0 0 12 13) := by linarith
    have hg := hr.pos_gap hu0 (show k < i - 1 by omega) (show i - 1 ≤ w.length + 1 by omega) hn
    have hk' := hr.pos_le hu0 (show k ≤ w.length + 1 by omega) hn
    have hj' := hr.pos_le hu0 (show i - 1 ≤ w.length + 1 by omega) hn
    apply hr.lt_of_gap hu0 (B := 2 * (((w.length + 1 : ℕ) : ℝ) + 1 / 256))
    · rw [abs_of_nonneg (mul_nonneg hS0 hk'.1)]
      exact mul_le_mul (by linarith) hk'.2 hk'.1 (by norm_num)
    · rw [abs_of_nonneg (mul_nonneg hS0 hj'.1)]
      exact mul_le_mul (by linarith) hj'.2 hj'.1 (by norm_num)
    · have h1 := mul_le_mul_of_nonneg_left hg hS0
      nlinarith [h1, hn, hu0, hu1, hS1]

set_option maxHeartbeats 4000000 in
theorem b0_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (j : ℕ) (hj : j ≤ w.length) :
    blk0.apply fl p 0 (w.length + 1) (net.init fl p w) j = X1 fl p w j := by
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0
    have hs : head0.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) 0 = [] := by
      simp [Head.sel, selOf, head0, cand]
    simp [Block.apply, blk0, headsApply, Head.attn, hs, attnRows, ravg, rsum, head0_V, zr, ur0,
      ur1, ur2, init_eq hr p w hw, X0, X1, qv, raffine, rdot, radd, sw_zero hr, hr.zero,
      hr.idem, hr.one, eo_bos hr, fl_eo hr, fl_ev hr, fl_eb hr, fl_nf hr, Lane4.Seq.tokAt_zero]
  · have hs := sel0 hr hu0 hu1 p hp w hw hn j (by omega) hj
    simp [Block.apply, blk0, headsApply, Head.attn, hs, attnRows, ravg_singleton hr, head0_V, zr,
      ur0, ur1, ur2, init_eq hr p w hw, X0, X1, qv, raffine, rdot, radd, sw_zero hr, hr.zero,
      hr.idem, hr.one, fl_eo hr, fl_ev hr, fl_eb hr, fl_nf hr]

noncomputable def x1f (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) : ℕ → Vec :=
  blk0.apply fl p 0 (w.length + 1) (net.init fl p w)

theorem x1f_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (j : ℕ) (hj : j ≤ w.length) : x1f fl p w j = X1 fl p w j :=
  b0_eq hr hu0 hu1 p hp w hw hn j hj

/-! ### layer 2 scores -/

noncomputable def R14c (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (dA : ℕ → ℕ → ℝ) (c k : ℕ) : ℝ :=
  fl (fl (sw fl (3 / 2) (dA 14 4) * eb fl p (tokAt w k)) +
    fl (sw fl 2 (dA 14 (5 + c)) * qv fl p w c k))

set_option maxHeartbeats 4000000 in
theorem score10 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (dA : ℕ → ℕ → ℝ) (i k : ℕ) :
    hd10.score fl dA (X1 fl p w i) (X1 fl p w k) =
      fl (fl (sw fl 1 (dA 12 13) * fl (k : ℝ)) + fl (nf fl w * R14c fl p w dA 0 k)) := by
  simp [Head.score, hd10, X1, R14c, zr, ur13, ar0, pdot, rmat, rdot, sw_zero hr, hr.zero,
    hr.idem]

set_option maxHeartbeats 4000000 in
theorem score11 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (dA : ℕ → ℕ → ℝ) (i k : ℕ) :
    hd11.score fl dA (X1 fl p w i) (X1 fl p w k) =
      fl (fl (sw fl 1 (dA 12 13) * fl (k : ℝ)) + fl (nf fl w * R14c fl p w dA 1 k)) := by
  simp [Head.score, hd11, X1, R14c, zr, ur13, ar1, pdot, rmat, rdot, sw_zero hr, hr.zero,
    hr.idem]

set_option maxHeartbeats 4000000 in
theorem score12 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (dA : ℕ → ℕ → ℝ) (i k : ℕ) :
    hd12.score fl dA (X1 fl p w i) (X1 fl p w k) =
      fl (fl (sw fl 1 (dA 12 13) * fl (k : ℝ)) + fl (nf fl w * R14c fl p w dA 2 k)) := by
  simp [Head.score, hd12, X1, R14c, zr, ur13, ar2, pdot, rmat, rdot, sw_zero hr, hr.zero,
    hr.idem]

/-! ### abstract selection -/

theorem sel_abs {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (n i : ℕ) (hin : i < n) (hi1 : 1 ≤ i)
    (hn : u * (n : ℝ) ≤ 1 / 256) (nn : ℝ) (hnn1 : (n : ℝ) - 1 / 256 ≤ nn)
    (hnn2 : nn ≤ (n : ℝ) + 1 / 256) (a : ℝ) (ha1 : 99 / 100 ≤ a) (ha2 : a ≤ 101 / 100)
    (R14 : ℕ → ℝ) (M Z : ℝ) (hM1 : 19 / 10 ≤ M) (hM2 : M ≤ 21 / 10)
    (hZ1 : 14 / 10 ≤ Z) (hZ2 : Z ≤ 16 / 10) (mt : ℕ → Prop)
    (hcls : ∀ k, k ≤ i → (k = 0 ∧ R14 k = Z) ∨
      (k ≠ 0 ∧ ((mt k ∧ R14 k = M) ∨ (¬ mt k ∧ R14 k = 0))))
    (m : ℕ) (hm : m ≤ i) (hmm : mt m ∨ (m = 0 ∧ ∀ k, k ≤ i → ¬ mt k))
    (hgr : ∀ k, m < k → k ≤ i → ¬ mt k) :
    ∀ k, k ≤ i → k ≠ m →
      fl (fl (a * fl (k : ℝ)) + fl (nn * R14 k)) <
        fl (fl (a * fl (m : ℝ)) + fl (nn * R14 m)) := by
  intro k hk hkm
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by
    have h2 : 2 ≤ n := by omega
    exact_mod_cast h2
  have hnn0 : 0 ≤ nn := by linarith
  have hB : u * (6 * ((n : ℝ) + 1)) ≤ 1 / 20 := by nlinarith
  have hfl : ∀ x : ℝ, 0 ≤ x → x ≤ 3 * ((n : ℝ) + 1) →
      x - 1 / 50 ≤ fl x ∧ fl x ≤ x + 1 / 50 := by
    intro x hx0 hx1
    have hxb : |x| ≤ 3 * ((n : ℝ) + 1) := by rw [abs_of_nonneg hx0]; exact hx1
    have h1 := hr.upper hu0 hxb
    have h2 := hr.lower hu0 hxb
    have h3 : u * (3 * ((n : ℝ) + 1)) ≤ 1 / 50 := by nlinarith
    constructor <;> linarith
  have hpos : ∀ j, j ≤ i → 0 ≤ fl (j : ℝ) ∧ fl (j : ℝ) ≤ (n : ℝ) + 1 / 256 :=
    fun j hj => hr.pos_le hu0 (show j ≤ n by omega) hn
  have hr12 : ∀ j, j ≤ i → 0 ≤ fl (a * fl (j : ℝ)) ∧
      fl (a * fl (j : ℝ)) ≤ 101 / 100 * ((n : ℝ) + 1 / 256) + 1 / 50 ∧
      a * fl (j : ℝ) - 1 / 50 ≤ fl (a * fl (j : ℝ)) ∧
      fl (a * fl (j : ℝ)) ≤ a * fl (j : ℝ) + 1 / 50 := by
    intro j hj
    obtain ⟨hp0, hp1⟩ := hpos j hj
    have hx0 : 0 ≤ a * fl (j : ℝ) := mul_nonneg (by linarith) hp0
    have hx2 : a * fl (j : ℝ) ≤ 101 / 100 * ((n : ℝ) + 1 / 256) :=
      mul_le_mul ha2 hp1 hp0 (by norm_num)
    have hx1 : a * fl (j : ℝ) ≤ 3 * ((n : ℝ) + 1) := by linarith
    obtain ⟨h1, h2⟩ := hfl _ hx0 hx1
    exact ⟨hr.nonneg hx0, by linarith, h1, h2⟩
  have hrgap : ∀ j1 j2, j1 < j2 → j2 ≤ i →
      fl (a * fl (j1 : ℝ)) + 94 / 100 ≤ fl (a * fl (j2 : ℝ)) := by
    intro j1 j2 hlt hj2
    have hg := hr.pos_gap hu0 hlt (show j2 ≤ n by omega) hn
    obtain ⟨_, _, hl2, _⟩ := hr12 j2 hj2
    obtain ⟨_, _, _, hu2⟩ := hr12 j1 (by omega)
    have h3 := mul_le_mul_of_nonneg_left hg (show 0 ≤ a by linarith)
    linarith
  have hrz : ∀ j, j = 0 → fl (a * fl (j : ℝ)) = 0 := by
    intro j hj
    subst hj
    rw [Nat.cast_zero, hr.zero, mul_zero, hr.zero]
  have hq : ∀ v lo hi : ℝ, 0 ≤ lo → lo ≤ v → v ≤ hi →
      ((n : ℝ) - 1 / 256) * lo ≤ nn * v ∧ nn * v ≤ ((n : ℝ) + 1 / 256) * hi := by
    intro v lo hi hlo h1 h2
    constructor
    · exact mul_le_mul hnn1 h1 hlo hnn0
    · exact mul_le_mul hnn2 h2 (by linarith) (by linarith)
  have hV : ∀ j, j ≤ i → (R14 j = Z ∨ R14 j = M ∨ R14 j = 0) →
      |fl (a * fl (j : ℝ)) + fl (nn * R14 j)| ≤ 6 * ((n : ℝ) + 1) := by
    intro j hj hc
    obtain ⟨h1, h2, _, _⟩ := hr12 j hj
    have hv0 : 0 ≤ R14 j ∧ R14 j ≤ 21 / 10 := by
      rcases hc with hc | hc | hc <;> rw [hc] <;> constructor <;> linarith
    have hq0 : 0 ≤ nn * R14 j := mul_nonneg hnn0 hv0.1
    have hq1 : nn * R14 j ≤ ((n : ℝ) + 1 / 256) * (21 / 10) :=
      mul_le_mul hnn2 hv0.2 hv0.1 (by linarith)
    obtain ⟨_, h4⟩ := hfl _ hq0 (by linarith)
    have h5 : 0 ≤ fl (nn * R14 j) := hr.nonneg hq0
    rw [abs_of_nonneg (add_nonneg h1 h5)]
    linarith
  have hcm := hcls m hm
  have hck := hcls k hk
  rcases hcm with ⟨hm0, hmZ⟩ | ⟨hm0, ⟨hmt, hmM⟩ | ⟨hmnt, hm00⟩⟩
  · rcases hck with ⟨hk0, _⟩ | ⟨hk0, ⟨hkt, _⟩ | ⟨hknt, hk00⟩⟩
    · exact absurd (hk0.trans hm0.symm) hkm
    · exact absurd hkt (hgr k (by omega) hk)
    · apply hr.lt_of_gap hu0 (B := 6 * ((n : ℝ) + 1)) (hV k hk (Or.inr (Or.inr hk00)))
        (hV m hm (Or.inl hmZ))
      rw [hk00, hmZ, hrz m hm0, mul_zero, hr.zero]
      obtain ⟨_, hrk, _, _⟩ := hr12 k hk
      obtain ⟨hz1, hz2⟩ := hq Z (14 / 10) (16 / 10) (by norm_num) hZ1 hZ2
      obtain ⟨h6, _⟩ := hfl (nn * Z) (mul_nonneg hnn0 (by linarith)) (by linarith)
      linarith
  · rcases hck with ⟨hk0, hkZ⟩ | ⟨hk0, ⟨hkt, hkM⟩ | ⟨hknt, hk00⟩⟩
    · apply hr.lt_of_gap hu0 (B := 6 * ((n : ℝ) + 1)) (hV k hk (Or.inl hkZ))
        (hV m hm (Or.inr (Or.inl hmM)))
      rw [hkZ, hmM, hrz k hk0]
      obtain ⟨hrm, _, _, _⟩ := hr12 m hm
      obtain ⟨hz1, hz2⟩ := hq Z (14 / 10) (16 / 10) (by norm_num) hZ1 hZ2
      obtain ⟨hm1, hm2⟩ := hq M (19 / 10) (21 / 10) (by norm_num) hM1 hM2
      obtain ⟨_, h7⟩ := hfl (nn * Z) (mul_nonneg hnn0 (by linarith)) (by linarith)
      obtain ⟨h8, _⟩ := hfl (nn * M) (mul_nonneg hnn0 (by linarith)) (by linarith)
      linarith
    · rcases lt_or_gt_of_ne hkm with hlt | hgt
      · apply hr.lt_of_gap hu0 (B := 6 * ((n : ℝ) + 1)) (hV k hk (Or.inr (Or.inl hkM)))
          (hV m hm (Or.inr (Or.inl hmM)))
        rw [hkM, hmM]
        have := hrgap k m hlt hm
        linarith
      · exact absurd hkt (hgr k hgt hk)
    · apply hr.lt_of_gap hu0 (B := 6 * ((n : ℝ) + 1)) (hV k hk (Or.inr (Or.inr hk00)))
        (hV m hm (Or.inr (Or.inl hmM)))
      rw [hk00, hmM, mul_zero, hr.zero]
      obtain ⟨_, hrk, _, _⟩ := hr12 k hk
      obtain ⟨hrm, _, _, _⟩ := hr12 m hm
      obtain ⟨hm1, hm2⟩ := hq M (19 / 10) (21 / 10) (by norm_num) hM1 hM2
      obtain ⟨h8, _⟩ := hfl (nn * M) (mul_nonneg hnn0 (by linarith)) (by linarith)
      linarith
  · rcases hmm with hmt' | ⟨hm0', _⟩
    · exact absurd hmt' hmnt
    · exact absurd hm0' hm0

/-! ### constants of layer 2 -/

noncomputable def Pc (fl : ℝ → ℝ) (p : Pert) (c : ℕ) : ℝ :=
  fl (sw fl 1 (p.V 0 0 (5 + c) c) * sw fl 1 (p.E (c + 1) c))
noncomputable def Zc (fl : ℝ → ℝ) (p : Pert) (dA : ℕ → ℕ → ℝ) : ℝ :=
  fl (sw fl (3 / 2) (dA 14 4) * eb fl p 0)
noncomputable def Mc (fl : ℝ → ℝ) (p : Pert) (dA : ℕ → ℕ → ℝ) (c : ℕ) : ℝ :=
  fl (sw fl 2 (dA 14 (5 + c)) * Pc fl p c)

theorem Pc_bd {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (c : ℕ) :
    |Pc fl p c - 1| ≤ 11 / 1000 := by
  have hv := sw_abs hr hu0 hu1 (1 : ℚ) 1 (by norm_num) (by norm_num) (hp.V 0 0 (5 + c) c)
    (1 / 190) (by norm_num)
  have he := sw_abs hr hu0 hu1 (1 : ℚ) 1 (by norm_num) (by norm_num) (hp.E (c + 1) c)
    (1 / 190) (by norm_num)
  have h1 := mulb (s := 1) (t := 1) (r := 1) (by norm_num) (by norm_num) (by norm_num) hv he
  have h2 := fl_approx hr hu0 hu1 h1 (by norm_num) (by norm_num)
  unfold Pc
  obtain ⟨a1, a2⟩ := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith

theorem Mc_bd {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (dA : ℕ → ℕ → ℝ) (c : ℕ)
    (hd : |dA 14 (5 + c)| ≤ 1 / 200) :
    19 / 10 ≤ Mc fl p dA c ∧ Mc fl p dA c ≤ 21 / 10 := by
  have hs := sw_abs hr hu0 hu1 (2 : ℚ) 2 (by norm_num) (by norm_num) hd (2 / 190) (by norm_num)
  have hP := Pc_bd hr hu0 hu1 p hp c
  have h1 := mulb (s := 2) (t := 1) (r := 2) (by norm_num) (by norm_num) (by norm_num) hs hP
  have h2 := fl_approx hr hu0 hu1 h1 (by norm_num) (by norm_num)
  unfold Mc
  obtain ⟨a1, a2⟩ := abs_le.mp h2
  constructor <;> linarith

theorem Zc_bd {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (dA : ℕ → ℕ → ℝ)
    (hd : |dA 14 4| ≤ 1 / 200) :
    14 / 10 ≤ Zc fl p dA ∧ Zc fl p dA ≤ 16 / 10 := by
  have hs := sw_abs hr hu0 hu1 (3 / 2 : ℚ) (3 / 2) (by norm_num) (by norm_num) hd (3 / 380)
    (by norm_num)
  have he : |eb fl p 0 - 1| ≤ 1 / 190 := by
    rw [eb_one]
    exact sw_abs hr hu0 hu1 (1 : ℚ) 1 (by norm_num) (by norm_num) (hp.E 0 4) (1 / 190)
      (by norm_num)
  have h1 := mulb (s := 3 / 2) (t := 1) (r := 3 / 2) (by norm_num) (by norm_num) (by norm_num)
    hs he
  have h2 := fl_approx hr hu0 hu1 h1 (by norm_num) (by norm_num)
  unfold Zc
  obtain ⟨a1, a2⟩ := abs_le.mp h2
  constructor <;> linarith

theorem qv_zero {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (c : ℕ) :
    qv fl p w c 0 = 0 := by
  unfold qv
  rw [show (0 : ℕ) - 1 = 0 from rfl, Lane4.Seq.tokAt_zero, eo_bos hr, mul_zero, hr.zero]

theorem qv_match (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (c j : ℕ)
    (hm : tokAt w (j - 1) = c + 1) : qv fl p w c j = Pc fl p c := by
  unfold qv Pc eo
  rw [hm]
  simp

theorem qv_nomatch {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (c j : ℕ) (hm : ¬ tokAt w (j - 1) = c + 1) : qv fl p w c j = 0 := by
  unfold qv
  rw [eo_zero hr p _ c hm, mul_zero, hr.zero]

theorem R14c_bos {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (dA : ℕ → ℕ → ℝ) (c : ℕ) : R14c fl p w dA c 0 = Zc fl p dA := by
  simp [R14c, Zc, qv_zero hr, Lane4.Seq.tokAt_zero, hr.zero, hr.idem]

theorem R14c_match {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (dA : ℕ → ℕ → ℝ) (c k : ℕ) (hne : tokAt w k ≠ 0) (hmt : tokAt w (k - 1) = c + 1) :
    R14c fl p w dA c k = Mc fl p dA c := by
  simp [R14c, Mc, eb_zero hr p _ hne, qv_match fl p w c k hmt, hr.zero, hr.idem]

theorem R14c_mis {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (dA : ℕ → ℕ → ℝ) (c k : ℕ) (hne : tokAt w k ≠ 0) (hmt : ¬ tokAt w (k - 1) = c + 1) :
    R14c fl p w dA c k = 0 := by
  simp [R14c, eb_zero hr p _ hne, qv_nomatch hr p w c k hmt, hr.zero]

theorem sel1_gen {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) (hh : Head) (hmask : hh.mask = Mask.causal)
    (c : ℕ) (dA : ℕ → ℕ → ℝ) (hdA12 : |dA 12 13| ≤ 1 / 200)
    (hdA4 : |dA 14 4| ≤ 1 / 200) (hdA5 : |dA 14 (5 + c)| ≤ 1 / 200)
    (hscore : ∀ k, hh.score fl dA (X1 fl p w i) (X1 fl p w k) =
      fl (fl (sw fl 1 (dA 12 13) * fl (k : ℝ)) + fl (nf fl w * R14c fl p w dA c k))) :
    ∃ m, m ≤ i ∧ hh.sel fl dA (w.length + 1) (x1f fl p w) i = [m] ∧
      (tokAt w (m - 1) = c + 1 ∨ (m = 0 ∧ ∀ k, k ≤ i → ¬ tokAt w (k - 1) = c + 1)) ∧
      ∀ k, m < k → k ≤ i → ¬ tokAt w (k - 1) = c + 1 := by
  obtain ⟨m, hm, hmm, hgr⟩ : ∃ m, m ≤ i ∧
      (tokAt w (m - 1) = c + 1 ∨ (m = 0 ∧ ∀ k, k ≤ i → ¬ tokAt w (k - 1) = c + 1)) ∧
      ∀ k, m < k → k ≤ i → ¬ tokAt w (k - 1) = c + 1 := by
    by_cases hex : ∃ k, k ≤ i ∧ tokAt w (k - 1) = c + 1
    · obtain ⟨k0, hk0, hk0m⟩ := hex
      exact ⟨Nat.findGreatest (fun k => tokAt w (k - 1) = c + 1) i, Nat.findGreatest_le i,
        Or.inl (Nat.findGreatest_spec (P := fun k => tokAt w (k - 1) = c + 1) hk0 hk0m),
        fun k hk1 hk2 => Nat.findGreatest_is_greatest hk1 hk2⟩
    · push_neg at hex
      exact ⟨0, Nat.zero_le _, Or.inr ⟨rfl, fun k hk => hex k hk⟩, fun k _ hk2 => hex k hk2⟩
  refine ⟨m, hm, ?_, hmm, hgr⟩
  have hnnf := abs_le.mp (hr.natCast_near (w.length + 1))
  have hnn1 : ((w.length + 1 : ℕ) : ℝ) - 1 / 256 ≤ nf fl w := by
    unfold nf; linarith [hnnf.1]
  have hnn2 : nf fl w ≤ ((w.length + 1 : ℕ) : ℝ) + 1 / 256 := by
    unfold nf; linarith [hnnf.2]
  have ha := sw_bd hr hu0 hu1 (1 : ℚ) 1 (by norm_num) (by norm_num) hdA12
  have ha1 : 99 / 100 ≤ sw fl 1 (dA 12 13) := by linarith [ha.1]
  have ha2 : sw fl 1 (dA 12 13) ≤ 101 / 100 := by linarith [ha.2]
  have hMb := Mc_bd hr hu0 hu1 p hp dA c hdA5
  have hZb := Zc_bd hr hu0 hu1 p hp dA hdA4
  have hcls : ∀ k, k ≤ i → (k = 0 ∧ R14c fl p w dA c k = Zc fl p dA) ∨
      (k ≠ 0 ∧ ((tokAt w (k - 1) = c + 1 ∧ R14c fl p w dA c k = Mc fl p dA c) ∨
        (¬ tokAt w (k - 1) = c + 1 ∧ R14c fl p w dA c k = 0))) := by
    intro k hk
    by_cases hk0 : k = 0
    · left
      refine ⟨hk0, ?_⟩
      subst hk0
      exact R14c_bos hr p w dA c
    · right
      refine ⟨hk0, ?_⟩
      have hne : tokAt w k ≠ 0 := by
        have := tok_pos w hw k (by omega) (by omega)
        omega
      by_cases hmt : tokAt w (k - 1) = c + 1
      · left
        exact ⟨hmt, R14c_match hr p w dA c k hne hmt⟩
      · right
        exact ⟨hmt, R14c_mis hr p w dA c k hne hmt⟩
  apply Head.sel_unique
  · rw [hmask, Lane4.Seq.mem_cand_causal]
    exact hm
  · intro k hk hne
    rw [hmask, Lane4.Seq.mem_cand_causal] at hk
    rw [x1f_eq hr hu0 hu1 p hp w hw hn i hi, x1f_eq hr hu0 hu1 p hp w hw hn k (by omega),
      x1f_eq hr hu0 hu1 p hp w hw hn m (by omega)]
    rw [hscore k, hscore m]
    exact sel_abs hr hu0 hu1 (w.length + 1) i (by omega) hi1 hn (nf fl w) hnn1 hnn2
      (sw fl 1 (dA 12 13)) ha1 ha2 (R14c fl p w dA c) (Mc fl p dA c) (Zc fl p dA)
      hMb.1 hMb.2 hZb.1 hZb.2 (fun k => tokAt w (k - 1) = c + 1) hcls m hm hmm hgr k hk hne

/-! ### the output -/

noncomputable def hvf (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (c m : ℕ) : ℝ :=
  fl (sw fl 1 (p.V 1 c (8 + c) 3) * ev fl p (tokAt w m))

noncomputable def zf (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (i c m : ℕ) : ℝ :=
  relu (fl (fl (fl (sw fl 3 (p.W1 1 c c) * eo fl p (tokAt w i) c) +
    fl (sw fl 1 (p.W1 1 c (8 + c)) * hvf fl p w c m)) + sw fl (-3) (p.b1 1 c))

set_option maxHeartbeats 4000000 in
theorem out_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) (m0 m1 m2 : ℕ) (hm0 : m0 ≤ w.length)
    (hm1 : m1 ≤ w.length) (hm2 : m2 ≤ w.length)
    (hs0 : hd10.sel fl (p.A 1 0) (w.length + 1) (x1f fl p w) i = [m0])
    (hs1 : hd11.sel fl (p.A 1 1) (w.length + 1) (x1f fl p w) i = [m1])
    (hs2 : hd12.sel fl (p.A 1 2) (w.length + 1) (x1f fl p w) i = [m2]) :
    net.out fl p w i =
      fl (sw fl 1 (p.oW 11) * fl (fl (fl (sw fl 1 (p.W2 1 11 0) * zf fl p w i 0 m0) +
        fl (sw fl 1 (p.W2 1 11 1) * zf fl p w i 1 m1)) +
        fl (sw fl 1 (p.W2 1 11 2) * zf fl p w i 2 m2))) := by
  have e0 := x1f_eq hr hu0 hu1 p hp w hw hn i hi
  have e1 := x1f_eq hr hu0 hu1 p hp w hw hn m0 hm0
  have e2 := x1f_eq hr hu0 hu1 p hp w hw hn m1 hm1
  have e3 := x1f_eq hr hu0 hu1 p hp w hw hn m2 hm2
  have hrun : net.run fl p w = blk1.apply fl p 1 (w.length + 1) (x1f fl p w) := by
    first
      | rfl
      | simp [TNet.run, net, runFrom, x1f]
  unfold TNet.out
  rw [hrun]
  simp [net, Block.apply, blk1, headsApply, Head.attn, hd10_V, hd11_V, hd12_V, hs0, hs1, hs2, attnRows,
    ravg_singleton hr, e0, e1, e2, e3, X1, zf, hvf, zr, ur3, ur11, wr0, wr1, wr2, raffine, rdot,
    radd, sw_zero hr, hr.zero, hr.idem, hr.one, fl_eo hr, fl_ev hr, fl_eb hr, fl_nf hr,
    fl_qv hr]

/-! ### gates -/

theorem gate_on {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (da db dc o hv H : ℝ) (hda : |da| ≤ 1 / 200)
    (hdb : |db| ≤ 1 / 200) (hdc : |dc| ≤ 1 / 200) (ho : |o - 1| ≤ 1 / 190)
    (hH0 : 0 ≤ H) (hH2 : H ≤ 2) (hhv : |hv - H| ≤ 1 / 45) :
    |relu (fl (fl (fl (sw fl 3 da * o) + fl (sw fl 1 db * hv)) + sw fl (-3) dc)) - H|
      ≤ 1 / 10 := by
  have h3 := sw_abs hr hu0 hu1 (3 : ℚ) 3 (by norm_num) (by norm_num) hda (3 / 190) (by norm_num)
  have p1 := mulb (s := 3) (t := 1) (r := 3) (by norm_num) (by norm_num) (by norm_num) h3 ho
  have p1' := fl_approx hr hu0 hu1 p1 (by norm_num) (by norm_num)
  have h1 := sw_abs hr hu0 hu1 (1 : ℚ) 1 (by norm_num) (by norm_num) hdb (1 / 190) (by norm_num)
  have p2 := mulb (s := 1) (t := H) (r := H) (by norm_num) hH0 (one_mul H) h1 hhv
  have p2' := fl_approx hr hu0 hu1 p2 (abs_le.mpr ⟨by linarith, by linarith⟩) (by linarith)
  obtain ⟨a1, a2⟩ := abs_le.mp p1'
  obtain ⟨b1, b2⟩ := abs_le.mp p2'
  have hacc : |fl (sw fl 3 da * o) + fl (sw fl 1 db * hv) - (3 + H)| ≤ 13 / 200 := by
    rw [abs_le]
    constructor <;> linarith
  have hacc' := fl_approx hr hu0 hu1 hacc (abs_le.mpr ⟨by linarith, by linarith⟩)
    (by norm_num)
  have h3c := sw_abs hr hu0 hu1 (3 : ℚ) 3 (by norm_num) (by norm_num) hdc (3 / 190) (by norm_num)
  rw [sw_neg hr 3 dc]
  obtain ⟨c1, c2⟩ := abs_le.mp hacc'
  obtain ⟨d1, d2⟩ := abs_le.mp h3c
  have hpre : |fl (fl (sw fl 3 da * o) + fl (sw fl 1 db * hv)) + -sw fl 3 dc - H| ≤ 9 / 100 := by
    rw [abs_le]
    constructor <;> linarith
  have hpre' := fl_approx hr hu0 hu1 hpre (abs_le.mpr ⟨by linarith, by linarith⟩)
    (by norm_num)
  refine le_trans (relu_near _ _ hH0) ?_
  obtain ⟨e1, e2⟩ := abs_le.mp hpre'
  rw [abs_le]
  constructor <;> linarith

theorem gate_off {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (da db dc hv : ℝ) (hdb : |db| ≤ 1 / 200) (hdc : |dc| ≤ 1 / 200)
    (hv0 : 0 ≤ hv) (hv1 : hv ≤ 21 / 10) :
    relu (fl (fl (fl (sw fl 3 da * 0) + fl (sw fl 1 db * hv)) + sw fl (-3) dc)) = 0 := by
  have h1 := sw_bd hr hu0 hu1 (1 : ℚ) 1 (by norm_num) (by norm_num) hdb
  have h3 := sw_bd hr hu0 hu1 (3 : ℚ) 3 (by norm_num) (by norm_num) hdc
  have hz : fl (fl (sw fl 3 da * 0) + fl (sw fl 1 db * hv)) = fl (sw fl 1 db * hv) := by
    rw [mul_zero, hr.zero, zero_add, hr.idem]
  rw [hz, sw_neg hr 3 dc]
  have hs0 : 0 ≤ sw fl 1 db := by linarith [h1.1]
  have hp0 : 0 ≤ sw fl 1 db * hv := mul_nonneg hs0 hv0
  have hp1 : sw fl 1 db * hv ≤ 21 / 10 * (1 * (1 + 1 / 190)) := by
    have := mul_le_mul h1.2 hv1 hv0 (by norm_num)
    linarith
  have hfa := flb hr hu0 hu1
    (show |sw fl 1 db * hv| ≤ 100 by rw [abs_of_nonneg hp0]; linarith)
  obtain ⟨g1, g2⟩ := abs_le.mp hfa
  have hP0 : 0 ≤ fl (sw fl 1 db * hv) := hr.nonneg hp0
  have hX : |fl (sw fl 1 db * hv) + -sw fl 3 dc| ≤ 100 := by
    rw [abs_le]
    constructor <;> linarith [h3.1, h3.2]
  have hfb := flb hr hu0 hu1 hX
  obtain ⟨k1, k2⟩ := abs_le.mp hfb
  show max _ 0 = 0
  apply max_eq_right
  linarith [h3.1]

theorem hvf_near {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (c m : ℕ) :
    |hvf fl p w c m - Hq (tokAt w m)| ≤ 1 / 45 := by
  have hs := sw_abs hr hu0 hu1 (1 : ℚ) 1 (by norm_num) (by norm_num) (hp.V 1 c (8 + c) 3)
    (1 / 190) (by norm_num)
  have he := ev_near hr hu0 hu1 p hp (tokAt w m)
  have hHb := Hq_bd (tokAt w m)
  have h1 := mulb (s := 1) (t := Hq (tokAt w m)) (r := Hq (tokAt w m)) (by norm_num) hHb.1
    (one_mul _) hs he
  have h2 := fl_approx hr hu0 hu1 h1 (abs_le.mpr ⟨by linarith [hHb.1], by linarith [hHb.2]⟩)
    (by linarith [hHb.2])
  unfold hvf
  obtain ⟨l1, l2⟩ := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith [hHb.2]

theorem hvf_nonneg {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (c m : ℕ) :
    0 ≤ hvf fl p w c m := by
  unfold hvf
  apply hr.nonneg
  apply mul_nonneg
  · have := sw_bd hr hu0 hu1 (1 : ℚ) 1 (by norm_num) (by norm_num) (hp.V 1 c (8 + c) 3)
    linarith [this.1]
  · exact ev_nonneg hr hu0 hu1 p hp _

theorem zf_off {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (i c m : ℕ)
    (hc : tokAt w i ≠ c + 1) : zf fl p w i c m = 0 := by
  have h0 := hvf_nonneg hr hu0 hu1 p hp w c m
  have h1 : hvf fl p w c m ≤ 21 / 10 := by
    have := abs_le.mp (hvf_near hr hu0 hu1 p hp w c m)
    have hHb := Hq_bd (tokAt w m)
    linarith [this.2]
  have h2 := eo_zero hr p (tokAt w i) c hc
  unfold zf
  rw [h2]
  exact gate_off hr hu0 hu1 (p.W1 1 c c) (p.W1 1 c (8 + c)) (p.b1 1 c) (hvf fl p w c m)
    (hp.W1 1 c (8 + c)) (hp.b1 1 c) h0 h1

theorem zf_on {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (i c m : ℕ)
    (hc : tokAt w i = c + 1) : |zf fl p w i c m - Hq (tokAt w m)| ≤ 1 / 10 := by
  have hHb := Hq_bd (tokAt w m)
  have ho : |eo fl p (tokAt w i) c - 1| ≤ 1 / 190 := by
    rw [eo_one fl p _ c hc]
    exact sw_abs hr hu0 hu1 (1 : ℚ) 1 (by norm_num) (by norm_num) (hp.E _ c) (1 / 190)
      (by norm_num)
  exact gate_on hr hu0 hu1 (p.W1 1 c c) (p.W1 1 c (8 + c)) (p.b1 1 c) (eo fl p (tokAt w i) c)
    (hvf fl p w c m) (Hq (tokAt w m)) (hp.W1 1 c c) (hp.W1 1 c (8 + c)) (hp.b1 1 c) ho
    hHb.1 hHb.2 (hvf_near hr hu0 hu1 p hp w c m)

theorem res_a {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (d0 d1 d2 z : ℝ) :
    fl (fl (fl (sw fl 1 d0 * z) + fl (sw fl 1 d1 * 0)) + fl (sw fl 1 d2 * 0))
      = fl (sw fl 1 d0 * z) := by
  simp [hr.zero, hr.idem]

theorem res_b {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (d0 d1 d2 z : ℝ) :
    fl (fl (fl (sw fl 1 d0 * 0) + fl (sw fl 1 d1 * z)) + fl (sw fl 1 d2 * 0))
      = fl (sw fl 1 d1 * z) := by
  simp [hr.zero, hr.idem]

theorem res_c {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (d0 d1 d2 z : ℝ) :
    fl (fl (fl (sw fl 1 d0 * 0) + fl (sw fl 1 d1 * 0)) + fl (sw fl 1 d2 * z))
      = fl (sw fl 1 d2 * z) := by
  simp [hr.zero, hr.idem]

theorem final_bound {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (so sc z H : ℝ) (hso : |so - 1| ≤ 1 / 190)
    (hsc : |sc - 1| ≤ 1 / 190) (hH0 : 0 ≤ H) (hH2 : H ≤ 2) (hz : |z - H| ≤ 1 / 10) :
    |fl (so * fl (sc * z)) - H| ≤ 1 / 4 := by
  have q1 := mulb (s := 1) (t := H) (r := H) (by norm_num) hH0 (one_mul H) hsc hz
  have q1' := fl_approx hr hu0 hu1 q1 (abs_le.mpr ⟨by linarith, by linarith⟩) (by linarith)
  have q1'' : |fl (sc * z) - H| ≤ 3 / 25 := by
    obtain ⟨a1, a2⟩ := abs_le.mp q1'
    rw [abs_le]
    constructor <;> linarith
  have q2 := mulb (s := 1) (t := H) (r := H) (by norm_num) hH0 (one_mul H) hso q1''
  have q2' := fl_approx hr hu0 hu1 q2 (abs_le.mpr ⟨by linarith, by linarith⟩) (by linarith)
  obtain ⟨b1, b2⟩ := abs_le.mp q2'
  rw [abs_le]
  constructor <;> linarith

theorem net_ok : Statement net := by
  intro u fl hr hu0 hu1 p hp w hw hn i hi1 hi
  obtain ⟨m0, hm0, hs0, hmm0, hgr0⟩ := sel1_gen hr hu0 hu1 p hp w hw hn i hi1 hi hd10 rfl 0
    (p.A 1 0) (hp.A 1 0 12 13) (hp.A 1 0 14 4) (hp.A 1 0 14 (5 + 0))
    (fun k => score10 hr p w (p.A 1 0) i k)
  obtain ⟨m1, hm1, hs1, hmm1, hgr1⟩ := sel1_gen hr hu0 hu1 p hp w hw hn i hi1 hi hd11 rfl 1
    (p.A 1 1) (hp.A 1 1 12 13) (hp.A 1 1 14 4) (hp.A 1 1 14 (5 + 1))
    (fun k => score11 hr p w (p.A 1 1) i k)
  obtain ⟨m2, hm2, hs2, hmm2, hgr2⟩ := sel1_gen hr hu0 hu1 p hp w hw hn i hi1 hi hd12 rfl 2
    (p.A 1 2) (hp.A 1 2 12 13) (hp.A 1 2 14 4) (hp.A 1 2 14 (5 + 2))
    (fun k => score12 hr p w (p.A 1 2) i k)
  have hout := out_eq hr hu0 hu1 p hp w hw hn i hi1 hi m0 m1 m2 (le_trans hm0 hi)
    (le_trans hm1 hi) (le_trans hm2 hi) hs0 hs1 hs2
  rw [hout]
  have htk := tok_le3 w hw i
  have htk1 := tok_pos w hw i hi1 hi
  have hso := sw_abs hr hu0 hu1 (1 : ℚ) 1 (by norm_num) (by norm_num) (hp.oW 11) (1 / 190)
    (by norm_num)
  have hc3 : tokAt w i = 1 ∨ tokAt w i = 2 ∨ tokAt w i = 3 := by omega
  rcases hc3 with hc | hc | hc
  · have ht : tokAt w i = 0 + 1 := by omega
    have hz0 := zf_on hr hu0 hu1 p hp w i 0 m0 ht
    have hz1 : zf fl p w i 1 m1 = 0 := zf_off hr hu0 hu1 p hp w i 1 m1 (by omega)
    have hz2 : zf fl p w i 2 m2 = 0 := zf_off hr hu0 hu1 p hp w i 2 m2 (by omega)
    have htg := target_eq w hw i hi1 hi 0 ht m0 hm0 hmm0 hgr0
    have hHb := Hq_bd (tokAt w m0)
    have hsc := sw_abs hr hu0 hu1 (1 : ℚ) 1 (by norm_num) (by norm_num) (hp.W2 1 11 0)
      (1 / 190) (by norm_num)
    rw [hz1, hz2, res_a hr (p.W2 1 11 0) (p.W2 1 11 1) (p.W2 1 11 2) (zf fl p w i 0 m0), htg]
    exact final_bound hr hu0 hu1 _ _ _ _ hso hsc hHb.1 hHb.2 hz0
  · have ht : tokAt w i = 1 + 1 := by omega
    have hz1 := zf_on hr hu0 hu1 p hp w i 1 m1 ht
    have hz0 : zf fl p w i 0 m0 = 0 := zf_off hr hu0 hu1 p hp w i 0 m0 (by omega)
    have hz2 : zf fl p w i 2 m2 = 0 := zf_off hr hu0 hu1 p hp w i 2 m2 (by omega)
    have htg := target_eq w hw i hi1 hi 1 ht m1 hm1 hmm1 hgr1
    have hHb := Hq_bd (tokAt w m1)
    have hsc := sw_abs hr hu0 hu1 (1 : ℚ) 1 (by norm_num) (by norm_num) (hp.W2 1 11 1)
      (1 / 190) (by norm_num)
    rw [hz0, hz2, res_b hr (p.W2 1 11 0) (p.W2 1 11 1) (p.W2 1 11 2) (zf fl p w i 1 m1), htg]
    exact final_bound hr hu0 hu1 _ _ _ _ hso hsc hHb.1 hHb.2 hz1
  · have ht : tokAt w i = 2 + 1 := by omega
    have hz2 := zf_on hr hu0 hu1 p hp w i 2 m2 ht
    have hz0 : zf fl p w i 0 m0 = 0 := zf_off hr hu0 hu1 p hp w i 0 m0 (by omega)
    have hz1 : zf fl p w i 1 m1 = 0 := zf_off hr hu0 hu1 p hp w i 1 m1 (by omega)
    have htg := target_eq w hw i hi1 hi 2 ht m2 hm2 hmm2 hgr2
    have hHb := Hq_bd (tokAt w m2)
    have hsc := sw_abs hr hu0 hu1 (1 : ℚ) 1 (by norm_num) (by norm_num) (hp.W2 1 11 2)
      (1 / 190) (by norm_num)
    rw [hz0, hz1, res_c hr (p.W2 1 11 0) (p.W2 1 11 1) (p.W2 1 11 2) (zf fl p w i 2 m2), htg]
    exact final_bound hr hu0 hu1 _ _ _ _ hso hsc hHb.1 hHb.2 hz2

end Lane4.Case
