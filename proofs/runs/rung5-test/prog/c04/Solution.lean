namespace Lane4.Case

def cstep (c t : ℕ) : ℕ := if cls t = 2 then c else cls t

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (cstep s.1 t, s.2 ++ [(dg t + s.1) % 3])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem fold_acc (w : List ℕ) (c : ℕ) (acc : List ℕ) :
    (w.foldl step (c, acc)).2 = acc ++ (w.foldl step (c, [])).2 := by
  induction w generalizing c acc with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldl_cons, step]
    rw [ih (cstep c b) (acc ++ [(dg b + c) % 3]), ih (cstep c b) ([] ++ [(dg b + c) % 3])]
    simp

theorem fold_get (w : List ℕ) (c : ℕ) (i : ℕ) (hi : i < w.length) :
    ((w.foldl step (c, [])).2).getD i 0 = (dg (w.getD i 0) + (w.take i).foldl cstep c) % 3 := by
  induction w generalizing c i with
  | nil => simp at hi
  | cons b t ih =>
    simp only [List.foldl_cons, step]
    rw [fold_acc t (cstep c b) ([] ++ [(dg b + c) % 3])]
    cases i with
    | zero => simp
    | succ j =>
      have hj : j < t.length := by simpa using hi
      have := ih (cstep c b) j hj
      simpa using this

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have h : i - 1 < w.length := by omega
  unfold prog target carry
  rw [fold_get w 0 (i - 1) h]
  rfl

end Lane4.Case
