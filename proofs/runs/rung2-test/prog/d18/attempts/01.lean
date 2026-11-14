namespace Lane4.Case

def wgt (t : ℕ) : ℤ := if t = 1 then 1 else if t = 2 then (-1) else if t = 3 then 0 else if t = 4 then 1 else 0

def step (s : ℤ × Bool) (t : ℕ) : ℤ × Bool :=
  (s.1 + wgt t, s.2 && decide (0 ≤ s.1 + wgt t))

def prog (w : List ℕ) : Bool :=
  let s := w.foldl step (0, true)
  s.2 && decide (s.1 = 0)

-- PROOF

theorem fst_lem (w : List ℕ) (b : ℤ) (ok : Bool) :
    (w.foldl step (b, ok)).1 = b + (w.map wt).sum := by
  induction w generalizing b ok with
  | nil => simp
  | cons t r ih =>
    rw [List.foldl_cons, ih]
    have : wgt t = wt t := rfl
    simp [step, this, add_assoc]

theorem snd_lem (w : List ℕ) (b : ℤ) (ok : Bool) :
    (w.foldl step (b, ok)).2 = true ↔
      (ok = true ∧ ∀ k, k ≤ w.length → 0 < k → 0 ≤ b + ((w.take k).map wt).sum) := by
  induction w generalizing b ok with
  | nil =>
    simp
    intro k hk hk0; omega
  | cons t r ih =>
    rw [List.foldl_cons, ih]
    have hw : wgt t = wt t := rfl
    simp only [step, hw, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, ?_⟩
      intro k hk hk0
      rcases k with _ | m
      · omega
      · rcases Nat.eq_zero_or_pos m with rfl | hm
        · simpa using h2
        · have := h3 m (by simpa using hk) hm
          simpa [add_assoc] using this
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h1⟩
      · have := h3 1 (by simp) (by omega)
        simpa using this
      · intro m hm hm0
        have := h3 (m+1) (by simpa using hm) (by omega)
        simpa [add_assoc] using this

theorem prog_correct : StatementProg prog := by
  intro w _
  unfold prog Good
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [snd_lem, fst_lem]
  simp only [zero_add, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · simpa using h1 k hk hk0
  · rintro ⟨h1, h2⟩
    exact ⟨fun k hk hk0 => by simpa using h1 k hk, h2⟩

end Lane4.Case
