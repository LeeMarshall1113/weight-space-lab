namespace Lane4.Case

/-- State: (carry bit, outputs so far). -/
def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  ((if cls t = 2 then s.1 else cls t), s.2 ++ [(dg t + s.1) % 2])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem fold_acc (w : List ℕ) (c : ℕ) (acc : List ℕ) :
    (w.foldl step (c, acc)).2 = acc ++ (w.foldl step (c, [])).2 := by
  induction w generalizing c acc with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldl_cons, step]
    rw [ih, ih (acc := [(dg b + c) % 2])]
    simp

theorem fold_get (w : List ℕ) (c : ℕ) (i : ℕ) (hi : i < w.length) :
    (w.foldl step (c, [])).2.getD i 0 =
      (dg (w.getD i 0) + (w.take i).foldl (fun c t => if cls t = 2 then c else cls t) c) % 2 := by
  induction w generalizing c i with
  | nil => simp at hi
  | cons b t ih =>
    simp only [List.foldl_cons, step]
    rw [fold_acc]
    cases i with
    | zero => simp
    | succ j =>
      have hj : j < t.length := by simpa using hi
      simp only [List.nil_append, List.singleton_append, List.getD_cons_succ,
        List.take_succ_cons, List.foldl_cons]
      exact ih _ j hj

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have h : i - 1 < w.length := by omega
  unfold prog target carry
  exact fold_get w 0 (i - 1) h

end Lane4.Case
