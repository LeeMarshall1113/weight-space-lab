namespace Lane4.Case

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  ((if cls t = 2 then s.1 else cls t), s.2 ++ [(dg t + s.1) % 3])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem fold_aux (w : List ℕ) : ∀ (c : ℕ) (acc : List ℕ), ∃ r : List ℕ,
    (w.foldl step (c, acc)).2 = acc ++ r ∧
    ∀ k, k < w.length → r.getD k 0 =
      (dg (w.getD k 0) + (w.take k).foldl (fun c t => if cls t = 2 then c else cls t) c) % 3 := by
  induction w with
  | nil => intro c acc; exact ⟨[], by simp, by simp⟩
  | cons b t ih =>
    intro c acc
    obtain ⟨r', h1, h2⟩ := ih (if cls b = 2 then c else cls b) (acc ++ [(dg b + c) % 3])
    refine ⟨(dg b + c) % 3 :: r', ?_, ?_⟩
    · simp only [List.foldl_cons, step]
      rw [h1]; simp
    · intro k hk
      cases k with
      | zero => simp
      | succ k =>
        have hk' : k < t.length := by simpa using hk
        simp only [List.getD_cons_succ, List.take_succ_cons, List.foldl_cons]
        exact h2 k hk'

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  obtain ⟨r, h1, h2⟩ := fold_aux w 0 []
  unfold prog target carry
  rw [h1]
  simp only [List.nil_append]
  exact h2 (i - 1) (by omega)

end Lane4.Case
