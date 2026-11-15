namespace Lane4.Case
open Lane4.Seq Lane4.Coll Lane4.TB Lane4.Inv

theorem getD_lt {α : Type} (l : List α) (d : α) (c : ℕ) (h : c < l.length) :
    l.getD c d = l[c] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_ge {α : Type} (l : List α) (d : α) (c : ℕ) (h : l.length ≤ c) :
    l.getD c d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem qdot_key (u : ℚ) (as b : Vec) :
    qdot (u :: as) b = u * b.getD 0 0 + qdot as b.tail := by
  cases b <;> simp [qdot]

theorem qdot_eq (a : Vec) : ∀ b : Vec,
    qdot a b = ((List.range a.length).map (fun c => a.getD c 0 * b.getD c 0)).sum := by
  induction a with
  | nil => intro b; simp [qdot]
  | cons u as ih =>
    intro b
    rw [qdot_key, ih b.tail, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.sum_cons, List.map_map]
    congr 1
    · simp
    · congr 1
      apply List.map_congr_left
      intro c _
      show as.getD c 0 * b.tail.getD c 0 = (u :: as).getD (c + 1) 0 * b.getD (c + 1) 0
      rw [List.getD_cons_succ]
      cases b <;> simp

theorem qdot_congr (a b b' : Vec)
    (h : ∀ c, a.getD c 0 ≠ 0 → b.getD c 0 = b'.getD c 0) : qdot a b = qdot a b' := by
  rw [qdot_eq a b, qdot_eq a b']
  congr 1
  apply List.map_congr_left
  intro c _
  by_cases hc : a.getD c 0 = 0
  · simp only [hc, zero_mul]
  · simp only [h c hc]

theorem rowzero_getD (r : Vec) (hr : ∀ v ∈ r, v = 0) (c : ℕ) : r.getD c 0 = 0 := by
  by_cases hc : c < r.length
  · rw [getD_lt _ _ _ hc]; exact hr _ (List.getElem_mem hc)
  · rw [getD_ge _ _ _ (not_lt.mp hc)]

theorem qdot_zero_row (r : Vec) (hr : ∀ v ∈ r, v = 0) (b : Vec) : qdot r b = 0 := by
  rw [qdot_eq]
  simp only [rowzero_getD r hr, zero_mul]
  simp

theorem allzero_of {r : Vec} (h : r.all (fun v => v == 0) = true) : ∀ v ∈ r, v = 0 := by
  intro v hv
  have := List.all_eq_true.mp h v hv
  simpa using this

theorem zeroOn_get {T : List ℕ} {r : Vec} (h : zeroOn T r = true) : ∀ c ∈ T, r.getD c 0 = 0 := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

theorem matVec_getD (M : List Vec) (v : Vec) (c : ℕ) :
    (matVec M v).getD c 0 = qdot (M.getD c []) v := by
  by_cases hc : c < M.length
  · simp [matVec, List.getD_eq_getElem?_getD, hc]
  · have h2 : M.length ≤ c := not_lt.mp hc
    simp [matVec, List.getD_eq_getElem?_getD, List.getElem?_eq_none h2, qdot]

theorem swap_sum (l m : List ℕ) (f : ℕ → ℕ → ℚ) :
    (l.map (fun j => (m.map (fun c => f j c)).sum)).sum
      = (m.map (fun c => (l.map (fun j => f j c)).sum)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [← List.sum_map_add]

theorem sumq (row : Vec) (n : ℕ) (x : ℕ → Vec) :
    ((List.range n).map (fun j => qdot row (x j))).sum
      = ((List.range row.length).map
          (fun c => row.getD c 0 * ((List.range n).map (fun j => (x j).getD c 0)).sum)).sum := by
  have h1 : ∀ j, qdot row (x j)
      = ((List.range row.length).map (fun c => row.getD c 0 * (x j).getD c 0)).sum :=
    fun j => qdot_eq _ _
  simp only [h1]
  refine (swap_sum (List.range n) (List.range row.length)
    (fun j c => row.getD c 0 * (x j).getD c 0)).trans ?_
  congr 1
  apply List.map_congr_left
  intro c _
  rw [List.sum_map_mul_left]

theorem sumq_agree (T : List ℕ) (d n : ℕ) (x y : ℕ → Vec) (hA : Agree T d n x y) (row : Vec) :
    ((List.range n).map (fun j => qdot row (x j))).sum
      = ((List.range n).map (fun j => qdot row (y j))).sum := by
  rw [sumq, sumq]
  congr 1
  apply List.map_congr_left
  intro c _
  congr 1
  by_cases hc : c ∈ T
  · exact hA.2.2 c hc
  · apply congrArg
    apply List.map_congr_left
    intro j hj
    exact hA.2.1 j (List.mem_range.mp hj) c hc

theorem cand_lt (m : Mask) (n i j : ℕ) (hi : i < n) (hj : j ∈ cand m n i) : j < n := by
  cases m <;> simp [cand] at hj <;> omega

theorem zeroOn_nil (T : List ℕ) : zeroOn T [] = true := by
  simp [zeroOn]

theorem zeroOn_getD' {T : List ℕ} {A : List Vec} (h : ∀ r ∈ A, zeroOn T r = true) (c : ℕ) :
    zeroOn T (A.getD c []) = true := by
  by_cases hc : c < A.length
  · rw [getD_lt _ _ _ hc]; exact h _ (List.getElem_mem hc)
  · rw [getD_ge _ _ _ (not_lt.mp hc)]; exact zeroOn_nil T

theorem avg_agree (S : List ℕ) (f g : ℕ → ℚ) (h : ∀ j ∈ S, f j = g j) : avg S f = avg S g := by
  unfold avg
  have : (S.map f) = (S.map g) := List.map_congr_left h
  rw [this]

theorem head_uniform (T : List ℕ) (d n : ℕ) (x y : ℕ → Vec) (h : Head) (hA : Agree T d n x y)
    (hz : isZero h.A = true) (hm : h.mask = Mask.all) (i : ℕ) (hi : i < n) :
    h.attn n x i = h.attn n y i := by
  have hrow : ∀ c, ∀ v ∈ h.A.getD c [], v = 0 := by
    intro c
    by_cases hc : c < h.A.length
    · rw [getD_lt _ _ _ hc]
      have := List.all_eq_true.mp hz _ (List.getElem_mem hc)
      exact allzero_of this
    · rw [getD_ge _ _ _ (not_lt.mp hc)]
      intro v hv; simp at hv
  have hscore : ∀ a b : Vec, h.score a b = 0 := by
    intro a b
    unfold Head.score
    rw [qdot_eq]
    have : ∀ c, (matVec h.A b).getD c 0 = 0 := by
      intro c
      rw [matVec_getD]
      exact qdot_zero_row _ (hrow c) _
    simp only [this, mul_zero]
    simp
  have hsel : ∀ z : ℕ → Vec, h.sel n z i = List.range n := by
    intro z
    have := sel_all h n z i (by intro k _ l _; rw [hscore, hscore])
    rw [this, hm]
    simp [cand]
  simp only [Head.attn, hsel]
  apply List.map_congr_left
  intro row _
  unfold avg
  rw [sumq_agree T d n x y hA row]

theorem head_blind (T : List ℕ) (d n : ℕ) (x y : ℕ → Vec) (h : Head) (hA : Agree T d n x y)
    (hs : blindScore T h.A = true) (hv : h.V.all (zeroOn T) = true) (i : ℕ) (hi : i < n) :
    h.attn n x i = h.attn n y i := by
  have hs' := hs
  unfold blindScore at hs'
  rw [Bool.and_eq_true] at hs'
  obtain ⟨hs1, hs2⟩ := hs'
  have hTrow : ∀ p ∈ T, ∀ v ∈ h.A.getD p [], v = 0 := by
    intro p hp
    exact allzero_of (List.all_eq_true.mp hs1 p hp)
  have hAz : ∀ r ∈ h.A, zeroOn T r = true := fun r hr => List.all_eq_true.mp hs2 r hr
  have hVz : ∀ r ∈ h.V, zeroOn T r = true := fun r hr => List.all_eq_true.mp hv r hr
  have hqa : ∀ r, zeroOn T r = true → ∀ j, j < n → qdot r (x j) = qdot r (y j) := by
    intro r hr j hj
    apply qdot_congr
    intro c hc
    by_cases hcT : c ∈ T
    · exact absurd (zeroOn_get hr c hcT) hc
    · exact hA.2.1 j hj c hcT
  have hsc : ∀ a b, a < n → b < n → h.score (x a) (x b) = h.score (y a) (y b) := by
    intro a b ha hb
    unfold Head.score
    rw [qdot_eq (x a) (matVec h.A (x b)), qdot_eq (y a) (matVec h.A (y b)),
      (hA.1 a ha).1, (hA.1 a ha).2]
    apply congrArg
    apply List.map_congr_left
    intro c _
    by_cases hc : c ∈ T
    · rw [matVec_getD, matVec_getD, qdot_zero_row _ (hTrow c hc), qdot_zero_row _ (hTrow c hc)]
      simp
    · rw [matVec_getD, matVec_getD, hqa _ (zeroOn_getD' hAz c) b hb, hA.2.1 a ha c hc]
  have hsel : h.sel n x i = h.sel n y i := by
    unfold Head.sel
    apply List.filter_congr
    intro j hj
    have hjn := cand_lt _ _ _ _ hi hj
    apply decide_eq_decide.mpr
    constructor
    · intro hh k hk
      have := hh k hk
      rwa [hsc i k hi (cand_lt _ _ _ _ hi hk), hsc i j hi hjn] at this
    · intro hh k hk
      have := hh k hk
      rwa [← hsc i k hi (cand_lt _ _ _ _ hi hk), ← hsc i j hi hjn] at this
  simp only [Head.attn]
  rw [hsel]
  apply List.map_congr_left
  intro row hrow
  apply avg_agree
  intro j hj
  have hjc := ((mem_sel h n y i j).1 hj).1
  exact hqa row (hVz row hrow) j (cand_lt _ _ _ _ hi hjc)

theorem head_step : HeadStep := by
  intro T d n x y h hA hb _ i hi
  unfold headBlind at hb
  rw [Bool.or_eq_true] at hb
  rcases hb with hb | hb
  · rw [Bool.and_eq_true] at hb
    exact head_uniform T d n x y h hA hb.1 (of_decide_eq_true hb.2) i hi
  · rw [Bool.and_eq_true] at hb
    exact head_blind T d n x y h hA hb.1 hb.2 i hi

end Lane4.Case
