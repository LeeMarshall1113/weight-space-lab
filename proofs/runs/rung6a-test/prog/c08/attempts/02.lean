namespace Lane4.Case
open Lane4.Seq (tokAt)

def cstep (c t : ℕ) : ℕ := if cls t = 2 then c else cls t

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (cstep s.1 t, s.2 ++ [(dg t + s.1) % 3])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem pref (w : List ℕ) (c : ℕ) (acc : List ℕ) (k : ℕ) (hk : k < acc.length) :
    (w.foldl step (c, acc)).2.getD k 0 = acc.getD k 0 := by
  induction w generalizing c acc with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldl_cons, step]
    rw [ih _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem main (w : List ℕ) (c : ℕ) (acc : List ℕ) (j : ℕ) (hj : j < w.length) :
    (w.foldl step (c, acc)).2.getD (acc.length + j) 0
      = (dg (w.getD j 0) + (w.take j).foldl cstep c) % 3 := by
  induction w generalizing c acc j with
  | nil => simp at hj
  | cons b t ih =>
    cases j with
    | zero =>
      simp only [List.foldl_cons, step]
      rw [Nat.add_zero, pref t _ (acc ++ [(dg b + c) % 3]) acc.length (by simp)]
      simp [List.getD_eq_getElem?_getD]
    | succ j =>
      have hj' : j < t.length := by simpa using hj
      simp only [List.foldl_cons, step, List.getD_cons_succ, List.take_succ_cons]
      have e : acc.length + (j + 1) = (acc ++ [(dg b + c) % 3]).length + j := by
        simp; omega
      rw [e]
      exact ih _ _ j hj'

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have h : i - 1 < w.length := by omega
  unfold prog target carry
  have := main w 0 [] (i - 1) h
  simp only [List.length_nil, Nat.zero_add] at this
  rw [this]
  rfl

end Lane4.Case
