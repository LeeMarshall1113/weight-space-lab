/-
Lane 4, rung 9-LN15 kit module, assembled by tools/ln_assemble.py from kit case le
(runs/r9ln15-kit/le): statements by the lane (Lane4/LNDefs.lean), proofs checked by tools/check.py.
-/
import Lane4.LNB1

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option linter.deprecated false

namespace Lane4.LNKE
open Lane4.RSeq (Vec pdot radd rsum)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.LNC Lane4.R7K2

/-! ### small facts -/

theorem lz_SC_cast : ((SC : ℤ) : ℝ) = 2 ^ 56 := by unfold SC; norm_num
theorem lz_SC_pos : (0 : ℤ) < SC := by unfold SC; norm_num

theorem lz_foldl_add (l : List ℤ) : ∀ s : ℤ, l.foldl (fun s v => s + v) s = s + l.sum := by
  induction l with
  | nil => intro s; simp
  | cons a l ih =>
    intro s
    simp only [List.foldl_cons, ih, List.sum_cons]
    ring

theorem lz_sumI_eq (l : List ℤ) : sumI l = l.sum := by
  unfold sumI; rw [lz_foldl_add]; simp

theorem lz_sumI_cons (a : ℤ) (l : List ℤ) : sumI (a :: l) = a + sumI l := by
  rw [lz_sumI_eq, lz_sumI_eq]; simp

theorem lz_sumI_nil : sumI [] = 0 := by
  rw [lz_sumI_eq]; simp

theorem lz_intL_len (w : List ℚ) : (intL w).length = w.length := by simp [intL]

theorem lz_gridL_cons {a : ℚ} {w : List ℚ} (h : gridL (a :: w) = true) :
    gridOK a = true ∧ gridL w = true := by
  unfold gridL at h ⊢
  rw [List.all_cons, Bool.and_eq_true] at h
  exact h

theorem lz_inffs_cons {e : ℕ → ℝ} {v : ℝ} {x : List ℝ} {X0 : FF} {X : List FF}
    (h : InFFs e (v :: x) (X0 :: X)) : InFF e v X0 ∧ InFFs e x X := by
  unfold InFFs at h
  obtain ⟨hl, h⟩ := h
  refine ⟨?_, ?_⟩
  · simpa using h 0 (by simp)
  · unfold InFFs
    refine ⟨by simpa using hl, ?_⟩
    intro k hk
    simpa using h (k + 1) (by simpa using hk)

theorem lz_mag16 (a : FF) (h : a.mag ≤ 16 * SC) : (a.mag : ℝ) ≤ 16 * 2 ^ 56 := by
  have := (show ((a.mag : ℤ) : ℝ) ≤ (((16 * SC : ℤ)) : ℝ) by exact_mod_cast h)
  rw [Int.cast_mul, lz_SC_cast] at this
  simpa using this

theorem lz_x_bound (e : ℕ → ℝ) (he : Sym e) (ns : ℕ) :
    ∀ (x : List ℝ) (X : List FF), InFFs e x X → Shaped ns X → ∀ v ∈ x, |v| ≤ 16 := by
  intro x
  induction x with
  | nil => intro X _ _ v hv; simp at hv
  | cons v0 x ih =>
    intro X h hs v hv
    cases X with
    | nil => unfold InFFs at h; have := h.1; simp at this
    | cons X0 X =>
      obtain ⟨h0, h1⟩ := lz_inffs_cons h
      have hs0 := hs X0 (by simp)
      have hs1 : Shaped ns X := fun a ha => hs a (by simp [ha])
      rcases List.mem_cons.mp hv with hv | hv
      · rw [hv]
        have hb := (Lane4.LNKD.box_sound e v0 X0 he h0).2.2
        have hm := lz_mag16 X0 hs0.2
        have : |v0| * 2 ^ 56 ≤ 16 * 2 ^ 56 := le_trans hb hm
        exact le_of_mul_le_mul_right this (by norm_num)
      · exact ih X h1 hs1 v hv

/-! ### sums over the lists -/

noncomputable def lzW : List ℚ → List ℝ → ℝ
  | a :: w, v :: x => (a : ℝ) * v + lzW w x
  | _, _ => 0

noncomputable def lzD (d : ℕ → ℝ) : List ℝ → ℕ → ℝ
  | v :: x, j => d j * v + lzD d x (j + 1)
  | _, _ => 0

noncomputable def lzP (d : ℕ → ℝ) : List FF → ℕ → ℝ
  | X :: Xs, j => d j * (X.c : ℝ) + lzP d Xs (j + 1)
  | _, _ => 0

theorem lz_dotP_split (d : ℕ → ℝ) : ∀ (w : List ℚ) (x : List ℝ) (j : ℕ), w.length = x.length →
    dotP w x d j = lzW w x + lzD d x j := by
  intro w
  induction w with
  | nil =>
    intro x j h
    cases x with
    | nil => simp [dotP, lzW, lzD]
    | cons _ _ => simp at h
  | cons a w ih =>
    intro x j h
    cases x with
    | nil => simp at h
    | cons v x =>
      simp only [dotP, lzW, lzD]
      rw [ih x (j + 1) (by simpa using h)]
      ring

theorem lz_linValI_zip (e : ℕ → ℝ) (c : ℤ) : ∀ (a b : List ℤ) (k : ℕ), a.length = b.length →
    linValI (List.zipWith (fun x y => c * x + y) a b) e k = (c : ℝ) * linValI a e k + linValI b e k := by
  intro a
  induction a with
  | nil =>
    intro b k h
    cases b with
    | nil => simp [linValI]
    | cons _ _ => simp at h
  | cons x a ih =>
    intro b k h
    cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.zipWith_cons_cons, linValI]
      rw [ih b (k + 1) (by simpa using h)]
      push_cast; ring

theorem lz_lcT_length (ns : ℕ) : ∀ (w : List ℤ) (X : List FF), (∀ a ∈ X, a.t.length = ns) →
    (lcT ns w X).length = ns := by
  intro w
  induction w with
  | nil => intro X _; simp [lcT]
  | cons c w ih =>
    intro X hX
    cases X with
    | nil => simp [lcT]
    | cons X0 X =>
      have h0 := hX X0 (by simp)
      have h1 := ih X (fun a ha => hX a (by simp [ha]))
      simp [lcT, h0, h1]

theorem lz_sW_err (e : ℕ → ℝ) (ns : ℕ) :
    ∀ (w : List ℚ) (x : List ℝ) (X : List FF), gridL w = true → InFFs e x X →
      (∀ a ∈ X, a.t.length = ns) → w.length = x.length →
      |lzW w x * 2 ^ 56 - (((lcC (intL w) X : ℤ) : ℝ) + linValI (lcT ns (intL w) X) e 0) / 2 ^ 56|
        ≤ ((sumWR (intL w) X : ℤ) : ℝ) / 2 ^ 56 := by
  intro w
  induction w with
  | nil =>
    intro x X hg h hX hl
    simp [lzW, intL, lcC, lcT, sumWR, Lane4.LNKD.linValI_replicate]
  | cons a w ih =>
    intro x X hg h hX hl
    cases x with
    | nil => simp at hl
    | cons v x =>
      cases X with
      | nil => unfold InFFs at h; have := h.1; simp at this
      | cons X0 X =>
        obtain ⟨h0, h1⟩ := lz_inffs_cons h
        obtain ⟨hga, hgw⟩ := lz_gridL_cons hg
        have hX0 : X0.t.length = ns := hX X0 (by simp)
        have hX1 : ∀ a ∈ X, a.t.length = ns := fun a ha => hX a (by simp [ha])
        have hlw : w.length = x.length := by simpa using hl
        have ih' := ih x X hgw h1 hX1 hlw
        have hlenT := lz_lcT_length ns (intL w) X hX1
        have hc := Lane4.LNKD.floorQ_grid a hga
        have hlin := lz_linValI_zip e (floorQ a) X0.t (lcT ns (intL w) X) 0 (by rw [hX0, hlenT])
        have e1 : intL (a :: w) = floorQ a :: intL w := rfl
        rw [e1]
        simp only [lcC, lcT, sumWR, lzW]
        rw [hlin]
        unfold InFF at h0
        push_cast
        rw [Lane4.LNKD.iabs_cast, hc]
        have key : ((a : ℝ) * v + lzW w x) * 2 ^ 56
            - (((a : ℝ) * 2 ^ 56 * (X0.c : ℝ) + ((lcC (intL w) X : ℤ) : ℝ))
                + ((a : ℝ) * 2 ^ 56 * linValI X0.t e 0 + linValI (lcT ns (intL w) X) e 0)) / 2 ^ 56
            = (a : ℝ) * (v * 2 ^ 56 - ((X0.c : ℝ) + linValI X0.t e 0))
              + (lzW w x * 2 ^ 56 - (((lcC (intL w) X : ℤ) : ℝ) + linValI (lcT ns (intL w) X) e 0) / 2 ^ 56) := by
          ring
        rw [key]
        have habs : |(a : ℝ) * 2 ^ 56| = |(a : ℝ)| * 2 ^ 56 := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 56)]
        rw [habs]
        calc _ ≤ |(a : ℝ) * (v * 2 ^ 56 - ((X0.c : ℝ) + linValI X0.t e 0))|
              + |lzW w x * 2 ^ 56 - (((lcC (intL w) X : ℤ) : ℝ) + linValI (lcT ns (intL w) X) e 0) / 2 ^ 56| :=
              abs_add_le _ _
          _ ≤ |(a : ℝ)| * (X0.r : ℝ) + ((sumWR (intL w) X : ℤ) : ℝ) / 2 ^ 56 := by
              apply add_le_add
              · rw [abs_mul]; exact mul_le_mul_of_nonneg_left h0 (abs_nonneg _)
              · exact ih'
          _ = (|(a : ℝ)| * 2 ^ 56 * (X0.r : ℝ) + ((sumWR (intL w) X : ℤ) : ℝ)) / 2 ^ 56 := by ring

theorem lz_dotT_le (δ : ℚ) (hδ0 : 0 ≤ δ) (hgδ : gridOK δ = true) (e : ℕ → ℝ) (he : Sym e) :
    ∀ (w : List ℚ) (x : List ℝ) (X : List FF), gridL w = true → InFFs e x X → w.length = x.length →
      0 ≤ dotT (δ : ℝ) w x ∧
      dotT (δ : ℝ) w x * 2 ^ 56 * 2 ^ 56 ≤ ((sumWM (floorQ δ) (intL w) (X.map FF.mag) : ℤ) : ℝ) := by
  intro w
  induction w with
  | nil =>
    intro x X hg h hl
    simp [dotT, sumWM, intL]
  | cons a w ih =>
    intro x X hg h hl
    cases x with
    | nil => simp at hl
    | cons v x =>
      cases X with
      | nil => unfold InFFs at h; have := h.1; simp at this
      | cons X0 X =>
        obtain ⟨h0, h1⟩ := lz_inffs_cons h
        obtain ⟨hga, hgw⟩ := lz_gridL_cons hg
        have hlw : w.length = x.length := by simpa using hl
        obtain ⟨ih1, ih2⟩ := ih x X hgw h1 hlw
        have hc := Lane4.LNKD.floorQ_grid a hga
        have hd := Lane4.LNKD.floorQ_grid δ hgδ
        have hb := (Lane4.LNKD.box_sound e v X0 he h0).2.2
        have e1 : intL (a :: w) = floorQ a :: intL w := rfl
        have hδR : (0 : ℝ) ≤ (δ : ℝ) := Rat.cast_nonneg.mpr hδ0
        simp only [e1, List.map_cons, dotT, sumWM]
        push_cast
        rw [Lane4.LNKD.iabs_cast, hc, hd]
        have hA : 0 ≤ |(a : ℝ)| + (δ : ℝ) := add_nonneg (abs_nonneg _) hδR
        have habs : |(a : ℝ) * 2 ^ 56| = |(a : ℝ)| * 2 ^ 56 := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 56)]
        rw [habs]
        have hnn : 0 ≤ |(a : ℝ)| * 2 ^ 56 + (δ : ℝ) * 2 ^ 56 :=
          add_nonneg (mul_nonneg (abs_nonneg _) (by norm_num)) (mul_nonneg hδR (by norm_num))
        have h5 : (|(a : ℝ)| * 2 ^ 56 + (δ : ℝ) * 2 ^ 56) * (|v| * 2 ^ 56)
            ≤ (|(a : ℝ)| * 2 ^ 56 + (δ : ℝ) * 2 ^ 56) * (X0.mag : ℝ) :=
          mul_le_mul_of_nonneg_left hb hnn
        constructor
        · have := mul_nonneg hA (abs_nonneg v)
          linarith
        · linarith

theorem lz_sD_err (δ : ℝ) (hδ : 0 ≤ δ) (e : ℕ → ℝ) (he : Sym e) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ δ) :
    ∀ (x : List ℝ) (X : List FF) (j : ℕ), InFFs e x X →
      |lzD d x j * 2 ^ 56 - lzP d X j| ≤ δ * ((sumI (X.map FF.dev) : ℤ) : ℝ) := by
  intro x
  induction x with
  | nil =>
    intro X j h
    cases X with
    | nil => simp [lzD, lzP, lz_sumI_nil]
    | cons _ _ => unfold InFFs at h; have := h.1; simp at this
  | cons v x ih =>
    intro X j h
    cases X with
    | nil => unfold InFFs at h; have := h.1; simp at this
    | cons X0 X =>
      obtain ⟨h0, h1⟩ := lz_inffs_cons h
      have hdev := Lane4.LNKD.inff_dev e v X0 he h0
      have hih := ih X (j + 1) h1
      simp only [lzD, lzP, List.map_cons, lz_sumI_cons]
      rw [Int.cast_add]
      have e1 : (d j * v + lzD d x (j + 1)) * 2 ^ 56 - (d j * (X0.c : ℝ) + lzP d X (j + 1))
          = d j * (v * 2 ^ 56 - (X0.c : ℝ)) + (lzD d x (j + 1) * 2 ^ 56 - lzP d X (j + 1)) := by ring
      rw [e1]
      have h2 : |d j * (v * 2 ^ 56 - (X0.c : ℝ))| ≤ δ * (X0.dev : ℝ) := by
        rw [abs_mul]; exact mul_le_mul (hd j) hdev (abs_nonneg _) hδ
      have h3 := abs_add_le (d j * (v * 2 ^ 56 - (X0.c : ℝ))) (lzD d x (j + 1) * 2 ^ 56 - lzP d X (j + 1))
      linarith

theorem lz_pP_bound (δ : ℝ) (hδ : 0 ≤ δ) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ δ) :
    ∀ (X : List FF) (j : ℕ), |lzP d X j| ≤ δ * ((sumI (X.map (fun a => iabs a.c)) : ℤ) : ℝ) := by
  intro X
  induction X with
  | nil => intro j; simp [lzP, lz_sumI_nil]
  | cons X0 X ih =>
    intro j
    simp only [lzP, List.map_cons, lz_sumI_cons]
    rw [Int.cast_add, Lane4.LNKD.iabs_cast]
    have h1 : |d j * (X0.c : ℝ)| ≤ δ * |(X0.c : ℝ)| := by
      rw [abs_mul]; exact mul_le_mul (hd j) le_rfl (abs_nonneg _) hδ
    have h2 := abs_add_le (d j * (X0.c : ℝ)) (lzP d X (j + 1))
    have h3 := ih (j + 1)
    linarith

/-! ### the form of the exact row, perturbation, rounding -/

theorem lz_rep_core (u η M : ℝ) (fl : ℝ → ℝ) (hC : Ctx u η M fl) (δ : ℚ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (hgδ : gridOK δ = true) (ns : ℕ) (w : List ℚ) (b : ℚ) (x : List ℝ) (X : List FF)
    (dW : ℕ → ℝ) (db : ℝ) (e : ℕ → ℝ) (he : Sym e) (hdW : ∀ k, |dW k| ≤ (δ : ℝ)) (hdb : |db| ≤ (δ : ℝ))
    (hl : w.length = x.length) (h32 : w.length ≤ 32) (hsw : smallQ w = true) (hsb : smallQ [b] = true)
    (hgw : gridL w = true) (hgb : gridOK b = true) (hX : InFFs e x X) (hsh : Shaped ns X)
    (o1 : FF)
    (h1c : o1.c = lcC (intL w) X / SC)
    (h1t : o1.t = (lcT ns (intL w) X).map (fun x => x / SC))
    (h1r : o1.r = cdiv (sumWR (intL w) X) SC + ((ns : ℤ) + 1)
        + (cdiv (floorQ δ * sumI (X.map FF.dev)) SC
            + cdiv ((((intL w).length : ℤ) + 2) * 2 * sumWM (floorQ δ) (intL w) (X.map FF.mag)) (SC * 2 ^ 22)
            + 1 + chg (iabs (floorQ b) + floorQ δ))) :
    |(ardot fl w x dW 0 0 + asw fl b db) * 2 ^ 56
        - (((o1.c + floorQ b : ℤ) : ℝ) + linValI o1.t e 0 + (lzP dW X 0 + db * 2 ^ 56))| ≤ (o1.r : ℝ)
    ∧ |lzP dW X 0 + db * 2 ^ 56|
        ≤ ((cdiv (floorQ δ * (sumI (X.map (fun a => iabs a.c)) + SC)) SC : ℤ) : ℝ)
    ∧ o1.t.length = ns := by
  have hSC := lz_SC_cast
  have hSCp := lz_SC_pos
  have h2pos : (0 : ℝ) < 2 ^ 56 := by norm_num
  have hδR0 : (0 : ℝ) ≤ (δ : ℝ) := Rat.cast_nonneg.mpr hδ0
  have hδR1 : (δ : ℝ) ≤ 1 / 2 := Lane4.LNKD.half_cast δ hδ1
  have hshX : ∀ a ∈ X, a.t.length = ns := fun a ha => (hsh a ha).1
  have hxle := lz_x_bound e he ns x X hX hsh
  have hxle17 : ∀ v ∈ x, |v| ≤ 17 := fun v hv => by linarith [hxle v hv]
  have hA := Lane4.LNKA.ardot_rel u η M fl hC (δ : ℝ) hδR0 hδR1 w x dW hdW hl h32 hsw hxle17
  have hsp := lz_dotP_split dW w x 0 hl
  have hT1 := lz_sW_err e ns w x X hgw hX hshX hl
  have hT4 := lz_sD_err (δ : ℝ) hδR0 e he dW hdW x X 0 hX
  have hPP := lz_pP_bound (δ : ℝ) hδR0 dW hdW X 0
  obtain ⟨hdT0, hdT⟩ := lz_dotT_le δ hδ0 hgδ e he w x X hgw hX hl
  have hbI := Lane4.LNKD.floorQ_grid b hgb
  have hdI := Lane4.LNKD.floorQ_grid δ hgδ
  have hb15 : |(b : ℝ)| ≤ 15 := Lane4.LNKA.la_small_abs hsb b (by simp)
  have hlenT := lz_lcT_length ns (intL w) X hshX
  have hPb : |lzP dW X 0 + db * 2 ^ 56|
      ≤ ((cdiv (floorQ δ * (sumI (X.map (fun a => iabs a.c)) + SC)) SC : ℤ) : ℝ) := by
    have hk := (Lane4.LNKD.cdiv_facts (floorQ δ * (sumI (X.map (fun a => iabs a.c)) + SC)) SC hSCp).1
    rw [Int.cast_mul, Int.cast_add, hdI, hSC] at hk
    have h1 : |db * 2 ^ 56| ≤ (δ : ℝ) * 2 ^ 56 := by
      rw [abs_mul, abs_of_pos h2pos]; exact mul_le_mul_of_nonneg_right hdb (by norm_num)
    have h2 := le_trans (abs_add_le _ _) (add_le_add hPP h1)
    linarith
  refine ⟨?_, hPb, ?_⟩
  · have hwr := (Lane4.LNKD.cdiv_facts (sumWR (intL w) X) SC hSCp).1
    rw [hSC] at hwr
    have hlc := Lane4.LNKD.floor_facts (lcC (intL w) X) SC hSCp
    rw [hSC, ← h1c] at hlc
    have hlin := Lane4.LNKD.map_floor_err e he 1 SC hSCp (lcT ns (intL w) X) 0
    simp only [one_mul, Int.cast_one] at hlin
    rw [hSC, hlenT, ← h1t] at hlin
    have hsd := (Lane4.LNKD.cdiv_facts (floorQ δ * sumI (X.map FF.dev)) SC hSCp).1
    rw [Int.cast_mul, hdI, hSC] at hsd
    have hCDa := (Lane4.LNKD.cdiv_facts ((((intL w).length : ℤ) + 2) * 2 * sumWM (floorQ δ) (intL w) (X.map FF.mag))
      (SC * 2 ^ 22) (by unfold SC; norm_num)).1
    have eCDa : (((((intL w).length : ℤ) + 2) * 2 * sumWM (floorQ δ) (intL w) (X.map FF.mag) : ℤ) : ℝ)
        = ((w.length : ℝ) + 2) * 2 * ((sumWM (floorQ δ) (intL w) (X.map FF.mag) : ℤ) : ℝ) := by
      push_cast [lz_intL_len] <;> ring
    have eCDb : (((SC * 2 ^ 22 : ℤ)) : ℝ) = 2 ^ 56 * 2 ^ 22 := by
      rw [Int.cast_mul, hSC]; norm_num
    rw [eCDa, eCDb] at hCDa
    -- rounding of the stored bias
    have hBM : |(b : ℝ)| + (δ : ℝ) ≤ M := by
      have h16 : (|(b : ℝ)| + (δ : ℝ)) ≤ 16 := by linarith
      have h40 : (16 : ℝ) ≤ 2 ^ 40 := by norm_num
      linarith [hC.M1]
    have hbd : |(b : ℝ) + db| ≤ |(b : ℝ)| + (δ : ℝ) := le_trans (abs_add_le _ _) (by linarith)
    have hRb := hC.rnd.abs hC.u0 hbd hBM
    have hRb' : |asw fl b db - ((b : ℝ) + db)| ≤ u * (|(b : ℝ)| + (δ : ℝ)) + η := hRb
    have hbb : |(b : ℝ) * 2 ^ 56| = |(b : ℝ)| * 2 ^ 56 := by
      rw [abs_mul, abs_of_pos h2pos]
    have hCh := Lane4.LNKD.round_chg hC.u0 hC.u1 hC.h0 hC.h1 (|(b : ℝ)| + (δ : ℝ))
      (iabs (floorQ b) + floorQ δ) (by
        rw [abs_of_nonneg (add_nonneg (abs_nonneg _) hδR0)]
        push_cast
        rw [Lane4.LNKD.iabs_cast, hbI, hdI, hbb]
        apply le_of_eq; ring)
    rw [abs_of_nonneg (add_nonneg (abs_nonneg _) hδR0)] at hCh
    have hR : |(asw fl b db - ((b : ℝ) + db)) * 2 ^ 56| ≤ ((chg (iabs (floorQ b) + floorQ δ) : ℤ) : ℝ) := by
      rw [abs_mul, abs_of_pos h2pos]
      have g1 : |asw fl b db - ((b : ℝ) + db)| * 2 ^ 56 ≤ (u * (|(b : ℝ)| + (δ : ℝ)) + η) * 2 ^ 56 :=
        mul_le_mul_of_nonneg_right hRb' (by norm_num)
      linarith
    -- rounding of the dot product
    have hn0 : (0 : ℝ) ≤ (w.length : ℝ) := Nat.cast_nonneg _
    have hn32 : (w.length : ℝ) ≤ 32 := by exact_mod_cast h32
    have hWm0 : (0 : ℝ) ≤ ((sumWM (floorQ δ) (intL w) (X.map FF.mag) : ℤ) : ℝ) :=
      le_trans (mul_nonneg (mul_nonneg hdT0 (by norm_num)) (by norm_num)) hdT
    have a0 : 0 ≤ dotT (δ : ℝ) w x * 2 ^ 56 := mul_nonneg hdT0 (by norm_num)
    have hD1 : u * (dotT (δ : ℝ) w x * 2 ^ 56)
        ≤ ((sumWM (floorQ δ) (intL w) (X.map FF.mag) : ℤ) : ℝ) / (2 ^ 56 * 2 ^ 22) := by
      have b1 : u * (dotT (δ : ℝ) w x * 2 ^ 56) ≤ (1 / 2 ^ 24) * (dotT (δ : ℝ) w x * 2 ^ 56) :=
        mul_le_mul_of_nonneg_right hC.u1 a0
      have b3 : dotT (δ : ℝ) w x * 2 ^ 56 ≤ ((sumWM (floorQ δ) (intL w) (X.map FF.mag) : ℤ) : ℝ) / 2 ^ 56 := by
        rw [le_div_iff₀ h2pos]; exact hdT
      have b4 : 0 ≤ ((sumWM (floorQ δ) (intL w) (X.map FF.mag) : ℤ) : ℝ) / (2 ^ 56 * 2 ^ 22) :=
        div_nonneg hWm0 (by norm_num)
      have b5 : (1 / 2 ^ 24) * (dotT (δ : ℝ) w x * 2 ^ 56)
          ≤ (1 / 2 ^ 24) * (((sumWM (floorQ δ) (intL w) (X.map FF.mag) : ℤ) : ℝ) / 2 ^ 56) :=
        mul_le_mul_of_nonneg_left b3 (by norm_num)
      linarith
    have F8 : 2 * ((w.length : ℝ) + 2) * u * dotT (δ : ℝ) w x * 2 ^ 56
        ≤ ((cdiv ((((intL w).length : ℤ) + 2) * 2 * sumWM (floorQ δ) (intL w) (X.map FF.mag))
              (SC * 2 ^ 22) : ℤ) : ℝ) := by
      have hpos : (0 : ℝ) < 2 ^ 56 * 2 ^ 22 := by norm_num
      have hD1' := (le_div_iff₀ hpos).mp hD1
      have hCDb := (div_le_iff₀ hpos).mp hCDa
      have c1 : 2 * ((w.length : ℝ) + 2) * (u * (dotT (δ : ℝ) w x * 2 ^ 56) * (2 ^ 56 * 2 ^ 22))
          ≤ 2 * ((w.length : ℝ) + 2) * ((sumWM (floorQ δ) (intL w) (X.map FF.mag) : ℤ) : ℝ) :=
        mul_le_mul_of_nonneg_left hD1' (by positivity)
      have c4 : (2 * ((w.length : ℝ) + 2) * u * dotT (δ : ℝ) w x * 2 ^ 56) * (2 ^ 56 * 2 ^ 22)
          ≤ ((cdiv ((((intL w).length : ℤ) + 2) * 2 * sumWM (floorQ δ) (intL w) (X.map FF.mag))
              (SC * 2 ^ 22) : ℤ) : ℝ) * (2 ^ 56 * 2 ^ 22) := by
        nlinarith [c1, hCDb]
      exact le_of_mul_le_mul_right c4 hpos
    have F9 : 200 * (w.length : ℝ) * η * 2 ^ 56 ≤ 1 := by
      have d1 : (w.length : ℝ) * η ≤ 32 * (1 / 2 ^ 149) := mul_le_mul hn32 hC.h1 hC.h0 (by norm_num)
      linarith
    have hE : |(ardot fl w x dW 0 0 - dotP w x dW 0) * 2 ^ 56|
        ≤ ((cdiv ((((intL w).length : ℤ) + 2) * 2 * sumWM (floorQ δ) (intL w) (X.map FF.mag))
              (SC * 2 ^ 22) : ℤ) : ℝ) + 1 := by
      rw [abs_mul, abs_of_pos h2pos]
      have g1 := mul_le_mul_of_nonneg_right hA (le_of_lt h2pos)
      linarith
    rw [h1r]
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
    rw [abs_le]
    obtain ⟨a1, a2⟩ := abs_le.mp hT1
    obtain ⟨a3, a4⟩ := abs_le.mp hlin
    obtain ⟨a5, a6⟩ := abs_le.mp hT4
    obtain ⟨a7, a8⟩ := abs_le.mp hE
    obtain ⟨a9, a10⟩ := abs_le.mp hR
    obtain ⟨hl1, hl2⟩ := hlc
    constructor <;> linarith
  · rw [h1t, List.length_map]; exact hlenT

/-! ### the shape of `dotF` -/

def lz_o2 (o1 : FF) (b K : ℤ) (slot : Option ℕ) : FF :=
  (⟨o1.c + b, o1.t, o1.r⟩ : FF).bump slot K

theorem lz_dotF_struct (dI : ℤ) (ns : ℕ) (slot0 slot : Option ℕ) (w : List ℤ) (xs : List FF) (ms : List ℤ)
    (sd sc b : ℤ) :
    ∃ o1 : FF, o1.c = lcC w xs / SC ∧ o1.t = (lcT ns w xs).map (fun x => x / SC) ∧
      o1.r = cdiv (sumWR w xs) SC + ((ns : ℤ) + 1)
        + (cdiv (dI * sd) SC + cdiv (((w.length : ℤ) + 2) * 2 * sumWM dI w ms) (SC * 2 ^ 22)
            + 1 + chg (iabs b + dI)) ∧
      (dotF dI ns slot0 slot w xs ms sd sc b).1
        = (freeOpt slot0 o1 && ((lz_o2 o1 b (cdiv (dI * (sc + SC)) SC) slot).wide
              (chg (lz_o2 o1 b (cdiv (dI * (sc + SC)) SC) slot).mag)).small) ∧
      (dotF dI ns slot0 slot w xs ms sd sc b).2
        = (lz_o2 o1 b (cdiv (dI * (sc + SC)) SC) slot).wide
              (chg (lz_o2 o1 b (cdiv (dI * (sc + SC)) SC) slot).mag) := by
  refine ⟨((⟨lcC w xs / SC, (lcT ns w xs).map (fun x => x / SC), cdiv (sumWR w xs) SC + ((ns : ℤ) + 1)⟩ : FF).wide
      (cdiv (dI * sd) SC + cdiv (((w.length : ℤ) + 2) * 2 * sumWM dI w ms) (SC * 2 ^ 22) + 1
        + chg (iabs b + dI))), rfl, rfl, rfl, rfl, rfl⟩

/-! ### rounding of the result -/

theorem lz_wide_round {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (e : ℕ → ℝ) (z f : ℝ)
    (s : FF) (hs : InFF e z s) (hb : |z| * 2 ^ 56 ≤ (s.mag : ℝ)) (hf : |f - z| ≤ u * |z| + η) :
    InFF e f (s.wide (chg s.mag)) := by
  have h1 := Lane4.LNKD.round_chg hC.u0 hC.u1 hC.h0 hC.h1 z s.mag hb
  unfold InFF at hs ⊢
  simp only [FF.wide]
  push_cast
  have e1 : f * 2 ^ 56 - ((s.c : ℝ) + linValI s.t e 0)
      = (f - z) * 2 ^ 56 + (z * 2 ^ 56 - ((s.c : ℝ) + linValI s.t e 0)) := by ring
  rw [e1]
  have h2 : |(f - z) * 2 ^ 56| = |f - z| * 2 ^ 56 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 56)]
  have h3 : |f - z| * 2 ^ 56 ≤ (u * |z| + η) * 2 ^ 56 := mul_le_mul_of_nonneg_right hf (by norm_num)
  have h4 := abs_add_le ((f - z) * 2 ^ 56) (z * 2 ^ 56 - ((s.c : ℝ) + linValI s.t e 0))
  linarith

theorem lz_final_step {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (e : ℕ → ℝ) (Z : ℝ) (G : FF)
    (hZ : InFF e Z G) (hbox : |Z| * 2 ^ 56 ≤ (G.mag : ℝ))
    (hs : (G.wide (chg G.mag)).mag ≤ 15 * SC) : InFF e (fl Z) (G.wide (chg G.mag)) := by
  have hr := Lane4.LNKD.inff_r_nonneg e Z G hZ
  have hr' : 0 ≤ G.r := by exact_mod_cast hr
  have hlI := Lane4.LNKD.linI_nonneg G.t
  have hia := Lane4.LNKD.iabs_nonneg' G.c
  have hm0 : 0 ≤ G.mag := by
    unfold FF.mag FF.dev
    omega
  obtain ⟨hc1, hc2⟩ := Lane4.LNKD.chg_facts G.mag hm0
  have hc2' : 1 ≤ chg G.mag := by exact_mod_cast hc2
  have hmag : (G.wide (chg G.mag)).mag = G.mag + chg G.mag := by
    simp only [FF.mag, FF.dev, FF.wide]
    ring
  rw [hmag] at hs
  have h15 : G.mag ≤ 15 * SC := by omega
  have h15R : (G.mag : ℝ) ≤ 15 * 2 ^ 56 := by
    have : ((G.mag : ℤ) : ℝ) ≤ ((15 * SC : ℤ) : ℝ) := by exact_mod_cast h15
    rw [Int.cast_mul, lz_SC_cast] at this
    simpa using this
  have hZ15 : |Z| ≤ 15 := by
    have : |Z| * 2 ^ 56 ≤ 15 * 2 ^ 56 := le_trans hbox h15R
    exact le_of_mul_le_mul_right this (by norm_num)
  have h40 : (15 : ℝ) ≤ 2 ^ 40 := by norm_num
  have hZM : |Z| ≤ M := le_trans hZ15 (le_trans h40 hC.M1)
  have hf := hC.rnd.err Z hZM
  exact lz_wide_round hC e Z (fl Z) G hZ hbox hf

/-! ### where the symbol of the row goes -/

theorem lz_tail {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (ns : ℕ) (e : ℕ → ℝ) (he : Sym e)
    (o1 : FF) (bI K : ℤ) (Z P : ℝ) (slot0 slot : Option ℕ)
    (hrep : |Z * 2 ^ 56 - (((o1.c + bI : ℤ) : ℝ) + linValI o1.t e 0 + P)| ≤ (o1.r : ℝ))
    (hP : |P| ≤ (K : ℝ)) (hlen : o1.t.length = ns)
    (hg : (freeOpt slot0 o1 && ((lz_o2 o1 bI K slot).wide (chg (lz_o2 o1 bI K slot).mag)).small) = true) :
    ((lz_o2 o1 bI K slot).wide (chg (lz_o2 o1 bI K slot).mag)).t.length = ns
    ∧ ((lz_o2 o1 bI K slot).wide (chg (lz_o2 o1 bI K slot).mag)).mag ≤ 15 * SC
    ∧ (slot = none → InFF e (fl Z) ((lz_o2 o1 bI K slot).wide (chg (lz_o2 o1 bI K slot).mag)))
    ∧ (∀ s0 s : ℕ, slot0 = some s0 → slot = some s → s0 ≤ s → s < ns →
        ∃ v : ℝ, |v| ≤ 1 ∧ ∀ e' : ℕ → ℝ, AgreeBelow s0 e e' → e' s = v →
          InFF e' (fl Z) ((lz_o2 o1 bI K slot).wide (chg (lz_o2 o1 bI K slot).mag))) := by
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := le_trans (abs_nonneg _) hP
  rw [Bool.and_eq_true] at hg
  obtain ⟨hfree, hsm⟩ := hg
  have hmag : ((lz_o2 o1 bI K slot).wide (chg (lz_o2 o1 bI K slot).mag)).mag ≤ 15 * SC := by
    unfold FF.small at hsm
    exact of_decide_eq_true hsm
  refine ⟨?_, hmag, ?_, ?_⟩
  · cases slot with
    | none => exact hlen
    | some k =>
      show (addAt o1.t k K).length = ns
      rw [Lane4.LNKD.addAt_length]; exact hlen
  · intro hsl
    subst hsl
    have hZ : InFF e Z (lz_o2 o1 bI K none) := by
      show |Z * 2 ^ 56 - (((o1.c + bI : ℤ) : ℝ) + linValI o1.t e 0)| ≤ ((o1.r + K : ℤ) : ℝ)
      obtain ⟨h1a, h1b⟩ := abs_le.mp hrep
      obtain ⟨h2a, h2b⟩ := abs_le.mp hP
      rw [abs_le]
      push_cast at h1a h1b ⊢
      constructor <;> linarith
    have hbox := (Lane4.LNKD.box_sound e Z (lz_o2 o1 bI K none) he hZ).2.2
    exact lz_final_step hC e Z (lz_o2 o1 bI K none) hZ hbox hmag
  · intro s0 s hs0 hs hle hlt
    subst hs0
    subst hs
    have hz : zeroFrom s0 o1 = true := hfree
    have hzf : ZeroFacts := Lane4.LNKD.zero_facts
    unfold ZeroFacts at hzf
    obtain ⟨hzf1, hzf2⟩ := hzf
    have hv1 : |P / (K : ℝ)| ≤ 1 := by
      by_cases hK : (K : ℝ) = 0
      · rw [hK, div_zero]; simp
      · have hpos : 0 < (K : ℝ) := lt_of_le_of_ne hK0 (Ne.symm hK)
        rw [abs_div, abs_of_pos hpos, div_le_one hpos]; exact hP
    have hKv : (K : ℝ) * (P / (K : ℝ)) = P := by
      by_cases hK : (K : ℝ) = 0
      · have hP0 : P = 0 := by
          have := hP
          rw [hK] at this
          exact abs_nonpos_iff.mp this
        rw [hP0]; simp
      · field_simp
    have hclaim : ∀ e'' : ℕ → ℝ, AgreeBelow s0 e e'' → e'' s = P / (K : ℝ) →
        InFF e'' Z (lz_o2 o1 bI K (some s)) := by
      intro e'' hag hes
      have hfr : linValI o1.t e'' 0 = linValI o1.t e 0 := by
        apply Lane4.LNKD.linValI_frame
        intro i _ hne
        have hi : s0 ≤ i := by
          by_contra hlt'
          exact hne (hag i (by omega))
        simpa using hzf1 s0 o1 hz i hi
      have hadd := Lane4.LNKD.linValI_addAt e'' o1.t 0 s K (by rw [hlen]; exact hlt)
      show |Z * 2 ^ 56 - (((o1.c + bI : ℤ) : ℝ) + linValI (addAt o1.t s K) e'' 0)| ≤ (o1.r : ℝ)
      rw [hadd, hfr, Nat.zero_add, hes, hKv]
      have e1 : Z * 2 ^ 56 - (((o1.c + bI : ℤ) : ℝ) + (linValI o1.t e 0 + P))
          = Z * 2 ^ 56 - (((o1.c + bI : ℤ) : ℝ) + linValI o1.t e 0 + P) := by ring
      rw [e1]
      exact hrep
    obtain ⟨ê, hê⟩ : ∃ ê : ℕ → ℝ, ∀ k, ê k = if k = s then P / (K : ℝ) else e k :=
      ⟨fun k => if k = s then P / (K : ℝ) else e k, fun k => rfl⟩
    have hês : ê s = P / (K : ℝ) := by rw [hê]; simp
    have hêag : AgreeBelow s0 e ê := by
      intro k hk
      rw [hê, if_neg (by omega)]
    have hsym : Sym ê := by
      intro k
      rw [hê]
      split_ifs
      · exact hv1
      · exact he k
    have hZê := hclaim ê hêag hês
    have hbox := (Lane4.LNKD.box_sound ê Z (lz_o2 o1 bI K (some s)) hsym hZê).2.2
    refine ⟨P / (K : ℝ), hv1, ?_⟩
    intro e' hag hes
    exact lz_final_step hC e' Z (lz_o2 o1 bI K (some s)) (hclaim e' hag hes) hbox hmag

/-! ### the statement -/

theorem dot_f_sound : DotFSound := by
  intro u η M fl hC δ hδ0 hδ1 hgδ ns w b x X dW db e he hdW hdb hl h32 hsw hsb hgw hgb hX hsh slot0 slot hg
  obtain ⟨o1, h1c, h1t, h1r, hfst, hsnd⟩ := lz_dotF_struct (floorQ δ) ns slot0 slot (intL w) X
    (X.map FF.mag) (sumI (X.map FF.dev)) (sumI (X.map (fun a => iabs a.c))) (floorQ b)
  rw [hfst] at hg
  rw [hsnd]
  obtain ⟨hrep, hP, hlen⟩ := lz_rep_core u η M fl hC δ hδ0 hδ1 hgδ ns w b x X dW db e he hdW hdb hl h32
    hsw hsb hgw hgb hX hsh o1 h1c h1t h1r
  exact lz_tail hC ns e he o1 (floorQ b)
    (cdiv (floorQ δ * (sumI (X.map (fun a => iabs a.c)) + SC)) SC) _ _ slot0 slot hrep hP hlen hg

end Lane4.LNKE

