namespace Lane4.Case
open Lane4.Seq Lane4.Coll Lane4.TB Lane4.Inv

theorem gd_app_left (l l' : Vec) (c : ℕ) (h : c < l.length) :
    (l ++ l').getD c 0 = l.getD c 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gd_app_right (l l' : Vec) (c : ℕ) (h : l.length ≤ c) :
    (l ++ l').getD c 0 = l'.getD (c - l.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem pos_len (j n : ℕ) : (pos j n).length = 8 := by simp [pos]

theorem run_agree (T : List ℕ) (d n : ℕ) (hT : ∀ c ∈ T, c < d) :
    ∀ (bs : List Block), (∀ B ∈ bs, blockBlind T B = true ∧ B.shapeOK d = true) →
    ∀ x y : ℕ → Vec, Agree T d n x y →
    Agree T d n (bs.foldl (fun x B => B.apply n x) x) (bs.foldl (fun x B => B.apply n x) y) := by
  intro bs
  induction bs with
  | nil => intro _ x y hA; simpa using hA
  | cons B t ih =>
    intro h x y hA
    simp only [List.foldl_cons]
    exact ih (fun B' hB' => h B' (List.mem_cons_of_mem _ hB')) _ _
      (Lane4.BlockProof.block_step T d n x y B hT hA (h B (by simp)).1 (h B (by simp)).2)

theorem invariance : Invariance := by
  intro N N₁ N₂ ntok T hTB h1 h2 w₁ w₂ hw₁ hw₂ hlen hcol i hi
  have hsh0 : N.shapeOK ntok = true := by
    have h := hTB
    simp only [tokenBlind, Bool.and_eq_true] at h
    exact h.1.1.1.1
  obtain ⟨e, rest, hE⟩ : ∃ e rest, N.embed = e :: rest := by
    cases h : N.embed with
    | nil => simp [TNet.shapeOK, h] at hsh0
    | cons e r => exact ⟨e, r, rfl⟩
  have hde : N.embed.getD 0 [] = e := by rw [hE]; simp
  have hTB' := hTB
  simp only [tokenBlind, Bool.and_eq_true] at hTB'
  obtain ⟨⟨⟨⟨_, hTlt⟩, hoff⟩, hbl⟩, hz⟩ := hTB'
  rw [hde] at hoff
  have hTlt' : ∀ c ∈ T, c < e.length := by
    intro c hc
    have := List.all_eq_true.mp hTlt c hc
    have h3 : c < (N.embed.getD 0 []).length := of_decide_eq_true this
    rwa [hde] at h3
  have hsh := hsh0
  simp only [TNet.shapeOK, hE, rowsOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at hsh
  obtain ⟨⟨⟨⟨_, hEl, hErows⟩, _⟩, hBsh⟩, _⟩ := hsh
  have hElen : N.embed.length = ntok + 1 := by
    rw [hE]; simpa using hEl
  have hrowN : ∀ t, t ≤ ntok → (N.embed.getD t []).length = e.length := by
    intro t ht
    have h1' : t < N.embed.length := by omega
    rw [Lane4.HeadProof.getD_lt _ _ _ h1']
    exact hErows _ (by rw [← hE]; exact List.getElem_mem h1')
  have htok : ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ ntok) → ∀ j, tokAt w j ≤ ntok := by
    intro w hw j
    rcases tokAt_zero_or_mem w j with h0 | hm
    · omega
    · exact (hw _ hm).2
  have hreal : ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ ntok) → ∀ k, k < w.length →
      1 ≤ tokAt w (k + 1) ∧ tokAt w (k + 1) ≤ ntok := by
    intro w hw k hk
    rw [tokAt_succ w k hk]
    exact hw _ (List.getElem_mem hk)
  have hrl : ∀ (M : TNet), SameOffT N M T → ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ ntok) →
      ∀ j, (M.embed.getD (tokAt w j) []).length = e.length := by
    intro M hM w hw j
    rw [hM.2.2.2.2.1, hrowN _ (htok w hw j)]
  have hsame : ∀ c, c < e.length → c ∉ T → ∀ t, 1 ≤ t → t ≤ ntok →
      (N.embed.getD t []).getD c 0 = (N.embed.getD 1 []).getD c 0 := by
    intro c hc hcT t ht1 ht2
    have this := List.all_eq_true.mp hoff c (List.mem_range.mpr hc)
    have hcT' : T.contains c = false := by
      cases h : T.contains c
      · rfl
      · exfalso
        apply hcT
        first
          | simpa using h
          | exact List.elem_iff.mp h
          | exact List.contains_iff.mp h
    simp only [hcT', Bool.false_or] at this
    have h3 := List.all_eq_true.mp this (t - 1) (List.mem_range.mpr (by omega))
    have e3 : t - 1 + 1 = t := by omega
    rw [e3] at h3
    first
      | exact beq_iff_eq.mp h3
      | simpa using h3
  have hx : ∀ j, N₁.init w₁ j = N₁.embed.getD (tokAt w₁ j) [] ++ pos j (w₁.length + 1) :=
    fun j => rfl
  have hy : ∀ j, N₂.init w₂ j = N₂.embed.getD (tokAt w₂ j) [] ++ pos j (w₁.length + 1) := by
    intro j
    simp only [TNet.init, hlen]
  have hA0 : Agree T (e.length + 8) (w₁.length + 1) (N₁.init w₁) (N₂.init w₂) := by
    refine ⟨?_, ?_, ?_⟩
    · intro j _
      rw [hx j, hy j, List.length_append, List.length_append, hrl N₁ h1 w₁ hw₁ j,
        hrl N₂ h2 w₂ hw₂ j, pos_len]
      exact ⟨rfl, rfl⟩
    · intro j hj c hc
      rw [hx j, hy j]
      by_cases hcl : c < e.length
      · rw [gd_app_left _ _ _ (by rw [hrl N₁ h1 w₁ hw₁ j]; exact hcl),
          gd_app_left _ _ _ (by rw [hrl N₂ h2 w₂ hw₂ j]; exact hcl),
          h1.2.2.2.2.2 _ c hc, h2.2.2.2.2.2 _ c hc]
        rcases j with _ | k
        · rw [tokAt_zero w₁, tokAt_zero w₂]
        · have hk : k < w₁.length := by omega
          have hk2 : k < w₂.length := by omega
          have a1 := hreal w₁ hw₁ k hk
          have a2 := hreal w₂ hw₂ k hk2
          rw [hsame c hcl hc _ a1.1 a1.2, hsame c hcl hc _ a2.1 a2.2]
      · rw [gd_app_right _ _ _ (by rw [hrl N₁ h1 w₁ hw₁ j]; omega),
          gd_app_right _ _ _ (by rw [hrl N₂ h2 w₂ hw₂ j]; omega),
          hrl N₁ h1 w₁ hw₁ j, hrl N₂ h2 w₂ hw₂ j]
    · intro c hc
      have hcl := hTlt' c hc
      have e1 : ((List.range (w₁.length + 1)).map (fun j => (N₁.init w₁ j).getD c 0)).sum
          = colSum N₁ w₁ c := by
        unfold colSum
        congr 1
        apply List.map_congr_left
        intro j _
        rw [hx j, gd_app_left _ _ _ (by rw [hrl N₁ h1 w₁ hw₁ j]; exact hcl)]
      have e2 : ((List.range (w₁.length + 1)).map (fun j => (N₂.init w₂ j).getD c 0)).sum
          = colSum N₂ w₂ c := by
        unfold colSum
        rw [← hlen]
        congr 1
        apply List.map_congr_left
        intro j _
        rw [hy j, gd_app_left _ _ _ (by rw [hrl N₂ h2 w₂ hw₂ j]; exact hcl)]
      rw [e1, e2]
      exact hcol c hc
  have hr1 : N₁.run w₁ = N.blocks.foldl (fun x B => B.apply (w₁.length + 1) x) (N₁.init w₁) := by
    simp only [TNet.run, h1.1]
  have hr2 : N₂.run w₂ = N.blocks.foldl (fun x B => B.apply (w₁.length + 1) x) (N₂.init w₂) := by
    simp only [TNet.run, h2.1, hlen]
  have hblk : ∀ B ∈ N.blocks, blockBlind T B = true ∧ B.shapeOK (e.length + 8) = true :=
    fun B hB => ⟨List.all_eq_true.mp hbl B hB, hBsh B hB⟩
  have hfin := run_agree T (e.length + 8) (w₁.length + 1)
    (fun c hc => by have := hTlt' c hc; omega) N.blocks hblk _ _ hA0
  unfold TNet.out
  rw [h1.2.1, h2.2.1, h1.2.2.1, h2.2.2.1, hr1, hr2]
  congr 1
  apply Lane4.HeadProof.qdot_congr
  intro c hc
  have hcT : c ∉ T := by
    intro hcT
    exact hc (Lane4.HeadProof.zeroOn_get hz c hcT)
  exact hfin.2.1 i (by omega) c hcT

end Lane4.Case
