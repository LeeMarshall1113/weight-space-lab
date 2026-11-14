namespace Lane4.Case

def pw (t : ℕ) : ℤ := if t = 1 then (-1) else if t = 2 then 1 else if t = 3 then (-1) else 0

def pstep (acc : Bool × ℤ) (t : ℕ) : Bool × ℤ :=
  (acc.1 && decide (0 ≤ acc.2 + pw t), acc.2 + pw t)

def prog (w : List ℕ) : Bool :=
  let r := w.foldl pstep (true, 0)
  r.1 && decide (r.2 = 0)

-- PROOF

theorem fold_inv (w : List ℕ) : ∀ (b : Bool) (s : ℤ),
    (w.foldl pstep (b, s)).2 = s + (w.map wt).sum ∧
    ((w.foldl pstep (b, s)).1 = true ↔
      (b = true ∧ ∀ k, k < w.length → 0 ≤ s + ((w.take (k + 1)).map wt).sum)) := by
  induction w with
  | nil => intro b s; simp
  | cons t r ih =>
    intro b s
    have hw : pw t = wt t := by simp [pw, wt]
    obtain ⟨h1, h2⟩ := ih (b && decide (0 ≤ s + pw t)) (s + pw t)
    simp only [List.foldl_cons, pstep]
    refine ⟨?_, ?_⟩
    · rw [h1, hw]; simp [add_assoc]
    · rw [h2]
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_cons, hw]
      constructor
      · rintro ⟨⟨hb, h0⟩, hk⟩
        refine ⟨hb, ?_⟩
        intro k hk'
        cases k with
        | zero => simpa using h0
        | succ k =>
          have := hk k (by omega)
          simpa [add_assoc] using this
      · rintro ⟨hb, hk⟩
        refine ⟨⟨hb, ?_⟩, ?_⟩
        · simpa using hk 0 (by omega)
        · intro k hk'
          have := hk (k + 1) (by omega)
          simpa [add_assoc] using this

theorem prog_correct : StatementProg prog := by
  intro w _
  unfold prog Good
  obtain ⟨h1, h2⟩ := fold_inv w true 0
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [h2, h1]
  simp only [true_and, zero_add]
  constructor
  · rintro ⟨hk, hs⟩
    refine ⟨?_, hs⟩
    intro k hk'
    rcases Nat.eq_zero_or_pos k with rfl | hp
    · simp
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact hk j (by omega)
  · rintro ⟨hk, hs⟩
    refine ⟨?_, hs⟩
    intro k hk'
    exact hk (k + 1) (by omega)

end Lane4.Case
