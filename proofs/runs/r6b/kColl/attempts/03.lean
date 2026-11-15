namespace Lane4.Case
open Lane4.Seq Lane4.Coll

theorem qRel_mono {a b : ℚ} (h : a ≤ b) {x y : ℚ} (hq : qRel a x y) : qRel b x y := by
  unfold qRel at *
  exact hq.trans (mul_le_mul_of_nonneg_right h (abs_nonneg x))

theorem vRel_mono {a b : ℚ} (h : a ≤ b) {x y : List ℚ} (hq : vRel a x y) : vRel b x y :=
  List.Forall₂.imp (fun _ _ p => qRel_mono h p) hq

theorem mRel_mono {a b : ℚ} (h : a ≤ b) {x y : List (List ℚ)} (hq : mRel a x y) : mRel b x y :=
  List.Forall₂.imp (fun _ _ p => vRel_mono h p) hq

theorem hRel_mono {a b : ℚ} (h : a ≤ b) {x y : Head} (hq : hRel a x y) : hRel b x y :=
  ⟨mRel_mono h hq.1, mRel_mono h hq.2.1, hq.2.2⟩

theorem bRel_mono {a b : ℚ} (h : a ≤ b) {x y : Block} (hq : bRel a x y) : bRel b x y :=
  ⟨List.Forall₂.imp (fun _ _ p => hRel_mono h p) hq.1, mRel_mono h hq.2.1, vRel_mono h hq.2.2.1,
    mRel_mono h hq.2.2.2.1, vRel_mono h hq.2.2.2.2⟩

theorem netRel_mono {a b : ℚ} (h : a ≤ b) {N N' : TNet} (hq : netRel a N N') : netRel b N N' :=
  ⟨mRel_mono h hq.1, List.Forall₂.imp (fun _ _ p => bRel_mono h p) hq.2.1,
    vRel_mono h hq.2.2.1, qRel_mono h hq.2.2.2⟩

theorem collision_bound' : CollisionBound' := by
  intro T s o hs1 hsV hs ho1 hoV ho N hN τ L hτ1 hL hτL
  obtain ⟨D, hD⟩ := hN
  by_contra hcon
  push_neg at hcon
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  have hm : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast (by omega : 1 ≤ m)
  push_cast at hτL
  have hτ0 : 0 ≤ τ := by
    by_contra h
    push_neg at h
    nlinarith
  have hmpos : (0 : ℚ) < (m : ℚ) := by linarith
  have hd1 : |(1 - τ * ((m : ℚ) + 1)) / (m : ℚ)| ≤ τ := by
    rw [abs_le]
    constructor
    · rw [le_div_iff₀ hmpos]; nlinarith
    · rw [div_le_iff₀ hmpos]; nlinarith
  have hd1' : |(1 - τ * ((m : ℚ) + 1)) / (m : ℚ)| ≤ 1 := hd1.trans hτ1
  have hd2 : |(-τ)| = τ := by rw [abs_neg, abs_of_nonneg hτ0]
  obtain ⟨N₁, hr1, ho1'⟩ := hD _ hd1'
  obtain ⟨N₂, hr2, ho2'⟩ := hD (-τ) (by rw [hd2]; exact hτ1)
  have hr1' := netRel_mono hd1 hr1
  have hr2' := netRel_mono hd2.le hr2
  let w₁ : List ℕ := List.replicate m s ++ [o]
  let w₂ : List ℕ := List.replicate (m + 1) s
  have hl1 : w₁.length = m + 1 := by simp [w₁]
  have hl2 : w₂.length = m + 1 := by simp [w₂]
  have hc1 : w₁.countP T.inS = m := by
    simp [w₁, List.countP_append, List.countP_replicate, hs, ho]
  have hc2 : w₂.countP T.inS = m + 1 := by
    simp [w₂, List.countP_replicate, hs]
  have hv1 : T.Valid w₁ := by
    refine ⟨by simp [w₁], ?_⟩
    intro t ht
    simp only [w₁, List.mem_append, List.mem_replicate, List.mem_singleton] at ht
    rcases ht with ⟨_, rfl⟩ | rfl
    · exact ⟨hs1, hsV⟩
    · exact ⟨ho1, hoV⟩
  have hv2 : T.Valid w₂ := by
    refine ⟨by simp [w₂], ?_⟩
    intro t ht
    simp only [w₂, List.mem_replicate] at ht
    rcases ht with ⟨_, rfl⟩
    exact ⟨hs1, hsV⟩
  have c1 := hcon N₁ hr1' w₁ hv1 (by omega)
  have c2 := hcon N₂ hr2' w₂ hv2 (by omega)
  have e1 := ho1' w₁ hv1
  have e2 := ho2' w₂ hv2
  rw [hl1, hc1] at e1
  rw [hl2, hc2] at e2
  have heq : N₁.out w₁ w₁.length = N₂.out w₂ w₂.length := by
    rw [hl1, hl2, e1, e2]
    congr 1
    push_cast
    congr 1
    field_simp
    ring
  unfold Task.Correct at c1 c2
  rw [heq] at c1
  rw [hc1] at c1
  rw [hc2] at c2
  have key := c1.symm.trans c2
  by_cases h : m % 2 = T.par
  · have := key.mp h
    omega
  · have h' : ¬ (m + 1) % 2 = T.par := fun h' => h (key.mpr h')
    omega

theorem collision_bound : CollisionBound := by
  intro T s o hs1 hsV hs ho1 hoV ho N hN τ L hτ0 hτ1 hL hball
  by_contra h
  push_neg at h
  obtain ⟨N', hr, w, hv, hlen, hnc⟩ :=
    collision_bound' T s o hs1 hsV hs ho1 hoV ho N hN τ L hτ1 hL h
  exact hnc (hball N' hr w hv hlen)

end Lane4.Case
