namespace Lane4.Case

def gstep (s t : ℕ) : ℕ := if val t = 0 then s else val t

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (gstep s.1 t, s.2 ++ [gstep s.1 t])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem key (w : List ℕ) : ∀ a : ℕ, ∃ r : List ℕ,
    (∀ acc : List ℕ, (w.foldl step (a, acc)).2 = acc ++ r) ∧
    ∀ i, i < w.length → r.getD i 0 = (w.take (i + 1)).foldl gstep a := by
  induction w with
  | nil => intro a; exact ⟨[], by simp, by simp⟩
  | cons b t ih =>
    intro a
    obtain ⟨r, h1, h2⟩ := ih (gstep a b)
    refine ⟨gstep a b :: r, ?_, ?_⟩
    · intro acc
      simp only [List.foldl_cons, step]
      rw [h1]
      simp
    · intro i h
      cases i with
      | zero => simp
      | succ i =>
        have h' : i < t.length := by simpa using h
        simp only [List.getD_cons_succ, List.take_succ_cons, List.foldl_cons]
        exact h2 i h'

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  unfold prog target lastv
  obtain ⟨r, h1, h2⟩ := key w 0
  rw [h1, List.nil_append]
  have h := h2 (i - 1) (by omega)
  have e : i - 1 + 1 = i := by omega
  rw [e] at h
  exact h

end Lane4.Case
