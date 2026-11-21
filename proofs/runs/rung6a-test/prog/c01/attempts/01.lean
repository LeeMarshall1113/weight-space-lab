namespace Lane4.Case

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  ((if cls t = 2 then s.1 else cls t), s.2 ++ [(dg t + s.1) % 3])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem fold_pref (w : List ℕ) : ∀ (c : ℕ) (acc : List ℕ),
    ∃ r : List ℕ, (w.foldl step (c, acc)).2 = acc ++ r ∧ r.length = w.length := by
  induction w with
  | nil => intro c acc; exact ⟨[], by simp⟩
  | cons b t ih =>
    intro c acc
    obtain ⟨r, hr, hl⟩ := ih (if cls b = 2 then c else cls b) (acc ++ [(dg b + c) % 3])
    refine ⟨(dg b + c) % 3 :: r, ?_, by simp [hl]⟩
    simp only [List.foldl_cons, step]
    rw [hr]
    simp

theorem fold_get (w : List ℕ) : ∀ (c : ℕ) (acc : List ℕ) (i : ℕ), i < w.length →
    (w.foldl step (c, acc)).2.getD (acc.length + i) 0 =
      (dg (w.getD i 0) + (w.take i).foldl (fun c t => if cls t = 2 then c else cls t) c) % 3 := by
  induction w with
  | nil => intro c acc i h; simp at h
  | cons b t ih =>
    intro c acc i h
    cases i with
    | zero =>
      obtain ⟨r, hr, hl⟩ := fold_pref t (if cls b = 2 then c else cls b) (acc ++ [(dg b + c) % 3])
      simp only [List.foldl_cons, step]
      rw [hr]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
    | succ i =>
      have h' : i < t.length := by simpa using h
      have e : acc.length + (i + 1) = (acc ++ [(dg b + c) % 3]).length + i := by
        simp; omega
      simp only [List.foldl_cons, step]
      rw [e, ih _ _ i h']
      simp

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have h : i - 1 < w.length := by omega
  have := fold_get w 0 [] (i - 1) h
  simp only [List.length_nil, Nat.zero_add] at this
  unfold prog target carry
  exact this

end Lane4.Case
