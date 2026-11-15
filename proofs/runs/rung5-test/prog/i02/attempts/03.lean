namespace Lane4.Case
open Lane4.Seq (tokAt tokAt_zero tokAt_succ)

/-- state: (previous token, table value for token 1, for token 2, outputs). -/
def na1 (p a1 t : ℕ) : ℕ := if p = 1 then h t else a1
def na2 (p a2 t : ℕ) : ℕ := if p = 2 then h t else a2
def nout (p a1 a2 t : ℕ) : ℕ :=
  if t = 1 then na1 p a1 t else if t = 2 then na2 p a2 t else 0

def step (s : ℕ × ℕ × ℕ × List ℕ) (t : ℕ) : ℕ × ℕ × ℕ × List ℕ :=
  (t, na1 s.1 s.2.1 t, na2 s.1 s.2.2.1 t, s.2.2.2 ++ [nout s.1 s.2.1 s.2.2.1 t])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, 0, 0, [])).2.2.2

-- PROOF

theorem Aval_zero (w : List ℕ) (A : ℕ → ℕ → ℕ) (hA : ∀ k c, A k c = match (List.range k).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == c)) with | some j => h (tokAt w (j + 1)) | none => 0) (c : ℕ) : A 0 c = 0 := by
  rw [hA]; simp

theorem Aval_succ (w : List ℕ) (A : ℕ → ℕ → ℕ) (hA : ∀ k c, A k c = match (List.range k).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == c)) with | some j => h (tokAt w (j + 1)) | none => 0) (k c : ℕ) (hc : c ≠ 0) :
    A (k + 1) c = if tokAt w k = c then h (tokAt w (k + 1)) else A k c := by
  rw [hA (k + 1) c, hA k c]
  have h2 : tokAt w k = c → 1 ≤ k := by
    intro e
    by_contra hk
    have : k = 0 := by omega
    subst this
    rw [tokAt_zero] at e
    exact hc e.symm
  by_cases e : tokAt w k = c
  · have h1 := h2 e
    have hp : (decide (1 ≤ k) && (tokAt w k == c)) = true := by simp [h1, e]
    simp [List.range_succ, List.find?_cons, h1, e]
  · have hp : (decide (1 ≤ k) && (tokAt w k == c)) = false := by simp [e]
    simp [List.range_succ, List.find?_cons, hp, e]

theorem step_inv (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (A : ℕ → ℕ → ℕ) (hA : ∀ k c, A k c = match (List.range k).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == c)) with | some j => h (tokAt w (j + 1)) | none => 0)
    (k : ℕ) (hk : k < w.length)
    (s : ℕ × ℕ × ℕ × List ℕ) (t : ℕ) (ht : t = tokAt w (k + 1)) (hs : (s.1 = tokAt w k ∧ s.2.1 = A k 1 ∧ s.2.2.1 = A k 2 ∧ s.2.2.2.length = k ∧ ∀ m, 1 ≤ m → m ≤ k → s.2.2.2.getD (m - 1) 0 = target w m)) :
    ((step s t).1 = tokAt w (k + 1) ∧ (step s t).2.1 = A (k + 1) 1 ∧ (step s t).2.2.1 = A (k + 1) 2 ∧ (step s t).2.2.2.length = (k + 1) ∧ ∀ m, 1 ≤ m → m ≤ (k + 1) → (step s t).2.2.2.getD (m - 1) 0 = target w m) := by
  obtain ⟨hp, ha1, ha2, hlen, hout⟩ := hs
  have htok : t = 1 ∨ t = 2 := by
    have := hw (w[k]) (List.getElem_mem hk)
    rw [ht, tokAt_succ w k hk]
    omega
  have hA1 := Aval_succ w A hA k 1 (by norm_num)
  have hA2 := Aval_succ w A hA k 2 (by norm_num)
  have htar : target w (k + 1) = A (k + 1) t := by
    rw [hA (k + 1) t, ht] <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show t = tokAt w (k + 1)
    exact ht
  · show na1 s.1 s.2.1 t = A (k + 1) 1
    unfold na1
    rw [hp, ha1, hA1, ← ht]
  · show na2 s.1 s.2.2.1 t = A (k + 1) 2
    unfold na2
    rw [hp, ha2, hA2, ← ht]
  · show (s.2.2.2 ++ [nout s.1 s.2.1 s.2.2.1 t]).length = k + 1
    simp [hlen]
  · intro m hm1 hm2
    show (s.2.2.2 ++ [nout s.1 s.2.1 s.2.2.1 t]).getD (m - 1) 0 = target w m
    by_cases hm : m ≤ k
    · simp only [List.getD_eq_getElem?_getD]
      have hl2 : m - 1 < s.2.2.2.length := by omega
      rw [List.getElem?_append_left hl2]
      have := hout m hm1 hm
      simp only [List.getD_eq_getElem?_getD] at this
      exact this
    · obtain rfl : m = k + 1 := by omega
      have hget : (s.2.2.2 ++ [nout s.1 s.2.1 s.2.2.1 t]).getD s.2.2.2.length 0
          = nout s.1 s.2.1 s.2.2.1 t := by
        simp [List.getD_eq_getElem?_getD]
      rw [show k + 1 - 1 = s.2.2.2.length by omega, hget, htar]
      unfold nout na1 na2
      rw [hp, ha1, ha2]
      rcases htok with h1 | h1
      · have hA1' := hA1
        rw [h1] at ht
        rw [← ht] at hA1'
        rw [h1, hA1'] <;> simp
      · have hA2' := hA2
        rw [h1] at ht
        rw [← ht] at hA2'
        rw [h1, hA2'] <;> simp

theorem fold_inv (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (A : ℕ → ℕ → ℕ) (hA : ∀ k c, A k c = match (List.range k).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == c)) with | some j => h (tokAt w (j + 1)) | none => 0) :
    ∀ (l : List ℕ) (k : ℕ) (s : ℕ × ℕ × ℕ × List ℕ), k ≤ w.length → w.drop k = l →
      (s.1 = tokAt w k ∧ s.2.1 = A k 1 ∧ s.2.2.1 = A k 2 ∧ s.2.2.2.length = k ∧ ∀ m, 1 ≤ m → m ≤ k → s.2.2.2.getD (m - 1) 0 = target w m) → ((l.foldl step s).1 = tokAt w (k + l.length) ∧ (l.foldl step s).2.1 = A (k + l.length) 1 ∧ (l.foldl step s).2.2.1 = A (k + l.length) 2 ∧ (l.foldl step s).2.2.2.length = (k + l.length) ∧ ∀ m, 1 ≤ m → m ≤ (k + l.length) → (l.foldl step s).2.2.2.getD (m - 1) 0 = target w m) := by
  intro l
  induction l with
  | nil =>
    intro k s hk hd hI
    exact hI
  | cons t l' ih =>
    intro k s hk hd hI
    have hk' : k < w.length := by
      by_contra hc
      have h0 : w.drop k = [] := List.drop_eq_nil_of_le (by omega)
      rw [h0] at hd
      simp at hd
    have hd2 := List.drop_eq_getElem_cons hk'
    rw [hd2] at hd
    obtain ⟨ht, hl⟩ := List.cons.inj hd
    have htk : t = tokAt w (k + 1) := by
      rw [tokAt_succ w k hk']
      exact ht.symm
    have hI' := step_inv w hw A hA k hk' s t htk hI
    have := ih (k + 1) (step s t) (by omega) hl hI'
    rw [List.foldl_cons]
    have e : k + (t :: l').length = k + 1 + l'.length := by
      rw [List.length_cons]; omega
    rw [e]
    exact this

theorem prog_correct : StatementProg prog := by
  intro w hw i hi1 hi
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℕ → ℕ, ∀ k c, A k c = match (List.range k).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == c)) with | some j => h (tokAt w (j + 1)) | none => 0 :=
    ⟨fun k c => match (List.range k).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == c)) with | some j => h (tokAt w (j + 1)) | none => 0, fun k c => rfl⟩
  have h0 : (((0, 0, 0, []) : ℕ × ℕ × ℕ × List ℕ).1 = tokAt w 0 ∧ ((0, 0, 0, []) : ℕ × ℕ × ℕ × List ℕ).2.1 = A 0 1 ∧ ((0, 0, 0, []) : ℕ × ℕ × ℕ × List ℕ).2.2.1 = A 0 2 ∧ ((0, 0, 0, []) : ℕ × ℕ × ℕ × List ℕ).2.2.2.length = 0 ∧ ∀ m, 1 ≤ m → m ≤ 0 → ((0, 0, 0, []) : ℕ × ℕ × ℕ × List ℕ).2.2.2.getD (m - 1) 0 = target w m) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (0 : ℕ) = tokAt w 0
      rw [tokAt_zero]
    · show (0 : ℕ) = A 0 1
      rw [Aval_zero w A hA]
    · show (0 : ℕ) = A 0 2
      rw [Aval_zero w A hA]
    · rfl
    · intro m hm1 hm2
      omega
  have key := fold_inv w hw A hA w 0 (0, 0, 0, []) (Nat.zero_le _) (by simp) h0
  obtain ⟨_, _, _, _, hout⟩ := key
  unfold prog
  exact hout i hi1 (by omega)

end Lane4.Case
