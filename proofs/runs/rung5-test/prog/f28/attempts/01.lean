namespace Lane4.Case

def gs (s t : ℕ) : ℕ := if s = 0 then code t else s

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (gs s.1 t, s.2 ++ [((if gs s.1 t = 2 then 1 else 0) + cbit t) % 2])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem fold_aux (w : List ℕ) : ∀ (s : ℕ) (acc : List ℕ),
    ∃ r : List ℕ, (w.foldl step (s, acc)).2 = acc ++ r ∧ r.length = w.length ∧
      ∀ j, j < w.length → r.getD j 0 =
        ((if (w.take (j+1)).foldl gs s = 2 then 1 else 0) + cbit (w.getD j 0)) % 2 := by
  induction w with
  | nil => intro s acc; exact ⟨[], by simp, by simp, by simp⟩
  | cons b t ih =>
    intro s acc
    obtain ⟨r', h1, h2, h3⟩ := ih (gs s b) (acc ++ [((if gs s b = 2 then 1 else 0) + cbit b) % 2])
    refine ⟨((if gs s b = 2 then 1 else 0) + cbit b) % 2 :: r', ?_, ?_, ?_⟩
    · simp only [List.foldl_cons, step]
      rw [h1]; simp
    · simp [h2]
    · intro j hj
      cases j with
      | zero => simp
      | succ k =>
        have hk : k < t.length := by simpa using hj
        simp only [List.getD_cons_succ, List.take_succ_cons, List.foldl_cons, List.getD_cons_succ]
        exact h3 k hk

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  obtain ⟨r, h1, h2, h3⟩ := fold_aux w 0 []
  have h := h3 (i - 1) (by omega)
  have e : i - 1 + 1 = i := by omega
  rw [e] at h
  unfold prog target firstc
  rw [h1]
  simp only [List.nil_append]
  rw [h]
  rfl

end Lane4.Case
