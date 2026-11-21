namespace Lane4.Case

def g (s t : ℕ) : ℕ := if val t = 0 then s else val t

def step (st : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (g st.1 t, st.2 ++ [g st.1 t])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem fold_prefix (w : List ℕ) : ∀ (s : ℕ) (acc : List ℕ),
    ∃ X, (w.foldl step (s, acc)).2 = acc ++ X := by
  induction w with
  | nil => intro s acc; exact ⟨[], by simp⟩
  | cons b t ih =>
    intro s acc
    obtain ⟨X, hX⟩ := ih (g s b) (acc ++ [g s b])
    refine ⟨[g s b] ++ X, ?_⟩
    simp only [List.foldl_cons, step] at hX ⊢
    rw [hX]
    simp

theorem fold_getD (w : List ℕ) : ∀ (s : ℕ) (acc : List ℕ) (i : ℕ), 1 ≤ i → i ≤ w.length →
    (w.foldl step (s, acc)).2.getD (acc.length + i - 1) 0 = (w.take i).foldl g s := by
  induction w with
  | nil => intro s acc i h1 h2; simp at h2; omega
  | cons b t ih =>
    intro s acc i h1 h2
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    cases k with
    | zero =>
      obtain ⟨X, hX⟩ := fold_prefix t (g s b) (acc ++ [g s b])
      simp only [List.foldl_cons, step] at hX ⊢
      rw [hX]
      simp [List.getD_eq_getElem?_getD]
    | succ k =>
      have h2' : k + 1 ≤ t.length := by simp at h2; omega
      have := ih (g s b) (acc ++ [g s b]) (k + 1) (by omega) h2'
      have e : acc.length + (k + 1 + 1) - 1 = (acc ++ [g s b]).length + (k + 1) - 1 := by
        simp; omega
      simp only [List.foldl_cons, step, List.take_succ_cons]
      rw [e]
      exact this

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have := fold_getD w 0 [] i hi1 hi
  simpa [prog, target, lastv, g] using this

end Lane4.Case
