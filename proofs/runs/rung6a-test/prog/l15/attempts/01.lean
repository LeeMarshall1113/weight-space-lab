namespace Lane4.Case

def F (s t : ℕ) : ℕ := if val t = 0 then s else val t

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (F s.1 t, s.2 ++ [F s.1 t])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem fold_prefix (w : List ℕ) : ∀ (a : ℕ) (acc : List ℕ),
    ∃ r : List ℕ, (w.foldl step (a, acc)).2 = acc ++ r ∧ r.length = w.length := by
  induction w with
  | nil => intro a acc; exact ⟨[], by simp⟩
  | cons b t ih =>
    intro a acc
    obtain ⟨r, hr, hl⟩ := ih (F a b) (acc ++ [F a b])
    refine ⟨F a b :: r, ?_, by simp [hl]⟩
    simp only [List.foldl_cons, step]
    rw [hr]
    simp

theorem fold_get (w : List ℕ) : ∀ (a : ℕ) (acc : List ℕ) (k : ℕ), k < w.length →
    (w.foldl step (a, acc)).2.getD (acc.length + k) 0 = (w.take (k + 1)).foldl F a := by
  induction w with
  | nil => intro a acc k hk; simp at hk
  | cons b t ih =>
    intro a acc k hk
    obtain ⟨r, hr, hl⟩ := fold_prefix t (F a b) (acc ++ [F a b])
    cases k with
    | zero =>
      simp only [List.foldl_cons, step]
      rw [hr]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left]
    | succ k =>
      have h := ih (F a b) (acc ++ [F a b]) k (by simp at hk; omega)
      simp only [List.foldl_cons, step]
      have e : acc.length + (k + 1) = (acc ++ [F a b]).length + k := by simp; omega
      rw [e, h]
      simp

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have h := fold_get w 0 [] (i - 1) (by omega)
  have e : i - 1 + 1 = i := by omega
  rw [e] at h
  simpa [prog, target, lastv, F] using h

end Lane4.Case
