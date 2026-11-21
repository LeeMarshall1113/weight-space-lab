namespace Lane4.Case
open Lane4.Seq (tokAt)

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  ((if cls t = 2 then s.1 else cls t), s.2 ++ [(dg t + s.1) % 3])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem pref (w : List ℕ) (c : ℕ) (acc : List ℕ) :
    ∃ r, (w.foldl step (c, acc)).2 = acc ++ r := by
  induction w generalizing c acc with
  | nil => exact ⟨[], by simp⟩
  | cons b t ih =>
    obtain ⟨r, hr⟩ := ih (if cls b = 2 then c else cls b) (acc ++ [(dg b + c) % 3])
    refine ⟨(dg b + c) % 3 :: r, ?_⟩
    simp only [List.foldl_cons, step]
    rw [hr]
    simp

theorem main (w : List ℕ) (c : ℕ) (acc : List ℕ) (j : ℕ) (hj : j < w.length) :
    (w.foldl step (c, acc)).2.getD (acc.length + j) 0 =
      (dg (w.getD j 0) +
        (w.take j).foldl (fun c t => if cls t = 2 then c else cls t) c) % 3 := by
  induction w generalizing c acc j with
  | nil => simp at hj
  | cons b t ih =>
    obtain ⟨r, hr⟩ := pref t (if cls b = 2 then c else cls b) (acc ++ [(dg b + c) % 3])
    cases j with
    | zero =>
      simp only [List.foldl_cons, step]
      rw [hr]
      simp
    | succ j =>
      have h := ih (if cls b = 2 then c else cls b) (acc ++ [(dg b + c) % 3]) j
        (by simpa using hj)
      simp only [List.foldl_cons, step, List.take_succ_cons, List.getD_cons_succ]
      rw [show acc.length + (j + 1) = (acc ++ [(dg b + c) % 3]).length + j by
        simp; omega]
      exact h

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have h := main w 0 [] (i - 1) (by omega)
  unfold prog target carry
  simpa using h

end Lane4.Case
