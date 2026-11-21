namespace Lane4.Case
open Lane4.Seq (tokAt)

def cstep (c t : ℕ) : ℕ := if cls t = 2 then c else cls t

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (cstep s.1 t, s.2 ++ [(dg t + s.1) % 3])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

def outs : ℕ → List ℕ → List ℕ
  | _, [] => []
  | c, b :: t => (dg b + c) % 3 :: outs (cstep c b) t

theorem fold_eq (w : List ℕ) (c : ℕ) (acc : List ℕ) :
    (w.foldl step (c, acc)).2 = acc ++ outs c w := by
  induction w generalizing c acc with
  | nil => simp [outs]
  | cons b t ih =>
    simp only [List.foldl_cons, step]
    rw [ih]
    simp [outs]

theorem outs_get (w : List ℕ) (c : ℕ) (j : ℕ) (hj : j < w.length) :
    (outs c w).getD j 0 = (dg (w.getD j 0) + (w.take j).foldl cstep c) % 3 := by
  induction w generalizing c j with
  | nil => simp at hj
  | cons b t ih =>
    cases j with
    | zero => simp [outs]
    | succ j =>
      have hj' : j < t.length := by simpa using hj
      simp only [outs, List.getD_cons_succ, List.take_succ_cons, List.foldl_cons]
      exact ih (cstep c b) j hj'

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have h : i - 1 < w.length := by omega
  unfold prog target carry
  rw [fold_eq]
  simp only [List.nil_append]
  rw [outs_get w 0 (i - 1) h]
  rfl

end Lane4.Case
