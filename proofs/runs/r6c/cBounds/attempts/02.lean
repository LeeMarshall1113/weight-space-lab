namespace Lane4.Case
open Lane4.Seq Lane4.Coll Lane4.TB

theorem cp_rep (p : ℕ → Bool) (m v : ℕ) :
    (List.replicate m v).countP p = if p v = true then m else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.countP_cons, ih]
    by_cases h : p v = true <;> simp [h] <;> omega

theorem parity_of_collision : Collision → ParityBound := by
  intro hC N T K s o hb hpar hs1 hs2 hsi ho1 ho2 hoi τ a hτ0 hτ1 ha hOn
  by_contra hcon
  have h : 1 ≤ τ * (2 * (a : ℚ) + 1) := not_lt.mp hcon
  obtain ⟨N₁, N₂, h1, h2, heq⟩ := hC N K.V T s o hb hs1 hs2 ho1 ho2 τ a a hτ1 ha ha h h
  have hl1 : (List.replicate a s ++ List.replicate (a + 1) o).length = 2 * a + 1 := by
    simp; omega
  have hl2 : (List.replicate (a + 1) s ++ List.replicate a o).length = 2 * a + 1 := by
    simp; omega
  have hv1 : K.Valid (List.replicate a s ++ List.replicate (a + 1) o) := by
    refine ⟨?_, ?_⟩
    · intro hn
      have := congrArg List.length hn
      simp at this
    · intro t ht
      simp only [List.mem_append] at ht
      rcases ht with ht | ht
      · rw [List.eq_of_mem_replicate ht]; exact ⟨hs1, hs2⟩
      · rw [List.eq_of_mem_replicate ht]; exact ⟨ho1, ho2⟩
  have hv2 : K.Valid (List.replicate (a + 1) s ++ List.replicate a o) := by
    refine ⟨?_, ?_⟩
    · intro hn
      have := congrArg List.length hn
      simp at this
    · intro t ht
      simp only [List.mem_append] at ht
      rcases ht with ht | ht
      · rw [List.eq_of_mem_replicate ht]; exact ⟨hs1, hs2⟩
      · rw [List.eq_of_mem_replicate ht]; exact ⟨ho1, ho2⟩
  have c1 := hOn N₁ h1 _ hv1 (by omega)
  have c2 := hOn N₂ h2 _ hv2 (by omega)
  unfold Task.Correct at c1 c2
  have e := heq (2 * a + 1) (by omega)
  rw [hl1] at c1
  rw [hl2] at c2
  rw [e] at c1
  have k1 : (List.replicate a s ++ List.replicate (a + 1) o).countP K.inS = a := by
    rw [List.countP_append, cp_rep, cp_rep, hsi, hoi]; simp
  have k2 : (List.replicate (a + 1) s ++ List.replicate a o).countP K.inS = a + 1 := by
    rw [List.countP_append, cp_rep, cp_rep, hsi, hoi]; simp
  rw [k1] at c1
  rw [k2] at c2
  have key : (a % 2 = K.par) ↔ ((a + 1) % 2 = K.par) := c1.symm.trans c2
  omega

theorem sort_of_collision : Collision → SortBound := by
  intro hC N ntok T hb hn τ a hτ0 hτ1 ha hOn
  by_contra hcon
  have h : 1 ≤ τ * (2 * (a : ℚ) + 1) := not_lt.mp hcon
  obtain ⟨N₁, N₂, h1, h2, heq⟩ := hC N ntok T 1 2 hb (le_refl _) (by omega) (by omega) hn τ a a hτ1 ha ha h h
  have hl1 : (List.replicate a 1 ++ List.replicate (a + 1) 2).length = 2 * a + 1 := by
    simp; omega
  have hl2 : (List.replicate (a + 1) 1 ++ List.replicate a 2).length = 2 * a + 1 := by
    simp; omega
  have hv1 : ∀ t ∈ (List.replicate a 1 ++ List.replicate (a + 1) 2), 1 ≤ t ∧ t ≤ ntok := by
    intro t ht
    simp only [List.mem_append] at ht
    rcases ht with ht | ht
    · rw [List.eq_of_mem_replicate ht]; exact ⟨le_refl _, by omega⟩
    · rw [List.eq_of_mem_replicate ht]; exact ⟨by omega, hn⟩
  have hv2 : ∀ t ∈ (List.replicate (a + 1) 1 ++ List.replicate a 2), 1 ≤ t ∧ t ≤ ntok := by
    intro t ht
    simp only [List.mem_append] at ht
    rcases ht with ht | ht
    · rw [List.eq_of_mem_replicate ht]; exact ⟨le_refl _, by omega⟩
    · rw [List.eq_of_mem_replicate ht]; exact ⟨by omega, hn⟩
  have hne1 : (List.replicate a 1 ++ List.replicate (a + 1) 2) ≠ [] := by
    intro hh
    have := congrArg List.length hh
    simp at this
  have hne2 : (List.replicate (a + 1) 1 ++ List.replicate a 2) ≠ [] := by
    intro hh
    have := congrArg List.length hh
    simp at this
  obtain ⟨t₁, ho1, r1⟩ := hOn N₁ h1 _ hne1 hv1 (by omega) (a + 1) (by omega) (by omega)
  obtain ⟨t₂, ho2, r2⟩ := hOn N₂ h2 _ hne2 hv2 (by omega) (a + 1) (by omega) (by omega)
  have e := heq (a + 1) (by omega)
  rw [ho1, ho2] at e
  have et : t₁ = t₂ := by exact_mod_cast e
  subst et
  unfold IsRank at r1 r2
  simp only [List.countP_append, cp_rep, decide_eq_true_eq] at r1 r2
  obtain ⟨r1a, r1b⟩ := r1
  obtain ⟨r2a, r2b⟩ := r2
  split_ifs at r1a r1b r2a r2b <;> omega

end Lane4.Case
