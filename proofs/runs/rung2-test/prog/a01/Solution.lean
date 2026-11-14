namespace Lane4.Case

def stepA (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (((t - 1) / 3 + (t - 1) % 3 + s.1) / 3,
   s.2 ++ [((t - 1) / 3 + (t - 1) % 3 + s.1) % 3])

def prog (w : List ℕ) : List ℕ := (w.foldl stepA (0, [])).2

-- PROOF

theorem FF_cons (c t : ℕ) (l : List ℕ) :
    List.foldl (fun c t => (dA t + dC t + c) / 3) c (t :: l) =
      List.foldl (fun c t => (dA t + dC t + c) / 3) ((dA t + dC t + c) / 3) l := by
  simp

theorem fold_aux (w : List ℕ) : ∀ (c : ℕ) (o : List ℕ),
    ∃ r : List ℕ, (w.foldl stepA (c, o)).2 = o ++ r ∧ r.length = w.length ∧
      ∀ j, j < w.length →
        r.getD j 0 = (dA (w.getD j 0) + dC (w.getD j 0) + List.foldl (fun c t => (dA t + dC t + c) / 3) c (w.take j)) % 3 := by
  induction w with
  | nil => intro c o; exact ⟨[], by simp, by simp, by simp⟩
  | cons t w' ih =>
    intro c o
    obtain ⟨r', h1, h2, h3⟩ := ih ((dA t + dC t + c) / 3) (o ++ [(dA t + dC t + c) % 3])
    refine ⟨(dA t + dC t + c) % 3 :: r', ?_, ?_, ?_⟩
    · rw [List.foldl_cons]
      have : stepA (c, o) t = ((dA t + dC t + c) / 3, o ++ [(dA t + dC t + c) % 3]) := by
        simp [stepA, dA, dC]
      rw [this, h1]; simp
    · simp [h2]
    · intro j hj
      cases j with
      | zero => simp [dA, dC]
      | succ j =>
        have hj' : j < w'.length := by simpa using hj
        simp only [List.getD_cons_succ, List.take_succ_cons, List.getD_cons_succ]
        rw [h3 j hj', FF_cons]

theorem prog_correct : StatementProg prog := by
  intro w _ i hi hiw
  obtain ⟨r, h1, h2, h3⟩ := fold_aux w 0 []
  have : prog w = r := by simpa [prog] using h1
  rw [this]
  unfold digit
  rw [h3 (i - 1) (by omega)]
  unfold carryOut
  rfl

end Lane4.Case
