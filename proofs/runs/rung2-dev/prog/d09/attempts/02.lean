namespace Lane4.Case

def step (acc : Option ℕ) (t : ℕ) : Option ℕ :=
  match acc with
  | none => none
  | some n => if t = 4 then (if n = 0 then none else some (n - 1)) else some (n + 1)

def prog (w : List ℕ) : Bool := w.foldl step (some 0) == some 0

-- PROOF

theorem foldl_none (w : List ℕ) : w.foldl step none = none := by
  induction w with
  | nil => rfl
  | cons t r ih => simpa [step] using ih

theorem key (t : ℕ) (r : List ℕ) (n : ℤ) :
    (∀ k, k ≤ (t :: r).length → 0 ≤ n + (((t :: r).take k).map wt).sum) ↔
    (0 ≤ n ∧ ∀ k, k ≤ r.length → 0 ≤ (n + wt t) + ((r.take k).map wt).sum) := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (Nat.zero_le _), fun k hk => ?_⟩
    have := h (k + 1) (by simp; omega)
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons] at this
    linarith
  · rintro ⟨h0, h1⟩ k hk
    cases k with
    | zero => simpa using h0
    | succ k =>
      have := h1 k (by simp at hk; omega)
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      linarith

theorem main (w : List ℕ) (hv : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (m : ℕ) :
    ∀ n : ℕ, w.foldl step (some n) = some m ↔
      ((∀ k, k ≤ w.length → 0 ≤ (n : ℤ) + ((w.take k).map wt).sum) ∧
        (n : ℤ) + (w.map wt).sum = m) := by
  induction w with
  | nil =>
    intro n
    simp
  | cons t r ih =>
    intro n
    have hv' : ∀ s ∈ r, 1 ≤ s ∧ s ≤ 4 := fun s hs => hv s (List.mem_cons_of_mem _ hs)
    have ht := hv t (by simp)
    have hs : ((t :: r).map wt).sum = wt t + (r.map wt).sum := by
      simp only [List.map_cons, List.sum_cons]
    rw [List.foldl_cons, key, hs]
    by_cases h4 : t = 4
    · subst h4
      have hw : wt 4 = -1 := by simp [wt]
      rw [hw]
      by_cases hn : n = 0
      · subst hn
        have : step (some 0) 4 = none := by simp [step]
        rw [this, foldl_none]
        constructor
        · intro h
          exact absurd h (by simp)
        · rintro ⟨⟨_, h⟩, _⟩
          have := h 0 (Nat.zero_le _)
          simp at this
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        have : step (some (n' + 1)) 4 = some n' := by simp [step]
        rw [this, ih hv' n']
        push_cast
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨⟨by omega, fun k hk => ?_⟩, by linarith⟩
          have := h1 k hk
          linarith
        · rintro ⟨⟨_, h1⟩, h2⟩
          refine ⟨fun k hk => ?_, by linarith⟩
          have := h1 k hk
          linarith
    · have hw : wt t = 1 := by
        have : t = 1 ∨ t = 2 ∨ t = 3 := by omega
        rcases this with h | h | h <;> subst h <;> simp [wt]
      have : step (some n) t = some (n + 1) := by simp [step, h4]
      rw [this, ih hv' (n + 1), hw]
      push_cast
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨by omega, fun k hk => ?_⟩, by linarith⟩
        have := h1 k hk
        linarith
      · rintro ⟨⟨_, h1⟩, h2⟩
        refine ⟨fun k hk => ?_, by linarith⟩
        have := h1 k hk
        linarith

theorem prog_correct : StatementProg prog := by
  rintro w ⟨_, hv⟩
  unfold prog Good
  have := main w hv 0 0
  simp only [beq_iff_eq]
  rw [this]
  simp

end Lane4.Case
