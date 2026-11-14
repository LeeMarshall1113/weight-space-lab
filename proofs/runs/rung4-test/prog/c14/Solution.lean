namespace Lane4.Case

def cstep (c t : ℕ) : ℕ := if cls t = 2 then c else cls t

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (cstep s.1 t, s.2 ++ [(dg t + s.1) % 3])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem fold_suffix (w : List ℕ) (c : ℕ) (acc : List ℕ) :
    ∃ s : List ℕ, (w.foldl step (c, acc)).2 = acc ++ s ∧ s.length = w.length := by
  induction w generalizing c acc with
  | nil => exact ⟨[], by simp⟩
  | cons t r ih =>
    obtain ⟨s, hs, hl⟩ := ih (cstep c t) (acc ++ [(dg t + c) % 3])
    refine ⟨(dg t + c) % 3 :: s, ?_, by simp [hl]⟩
    simp only [List.foldl_cons, step]
    rw [hs]
    simp

theorem fold_get (w : List ℕ) (c : ℕ) (acc : List ℕ) (j : ℕ) (hj : j < w.length) :
    (w.foldl step (c, acc)).2.getD (acc.length + j) 0
      = (dg (w.getD j 0) + (w.take j).foldl cstep c) % 3 := by
  induction w generalizing c acc j with
  | nil => simp at hj
  | cons t r ih =>
    cases j with
    | zero =>
      obtain ⟨s, hs, _⟩ := fold_suffix r (cstep c t) (acc ++ [(dg t + c) % 3])
      simp only [List.foldl_cons, step]
      rw [hs]
      simp [List.getD_eq_getElem?_getD]
    | succ k =>
      have hk : k < r.length := by simpa using hj
      have := ih (cstep c t) (acc ++ [(dg t + c) % 3]) k hk
      simp only [List.foldl_cons, step]
      have e : acc.length + (k + 1) = (acc ++ [(dg t + c) % 3]).length + k := by
        simp; omega
      rw [e, this]
      simp

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have h : i - 1 < w.length := by omega
  have := fold_get w 0 [] (i - 1) h
  simp only [List.length_nil, Nat.zero_add] at this
  unfold prog target carry
  rw [this]
  rfl

end Lane4.Case
