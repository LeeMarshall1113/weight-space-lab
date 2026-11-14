namespace Lane4.Case

def stepF (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  ((if cls t = 2 then s.1 else cls t), s.2 ++ [(dg t + s.1) % 3])

def prog (w : List ℕ) : List ℕ := (w.foldl stepF (0, [])).2

-- PROOF

theorem fold_len (w : List ℕ) (c : ℕ) (acc : List ℕ) :
    (w.foldl stepF (c, acc)).2.length = acc.length + w.length := by
  induction w generalizing c acc with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldl_cons, stepF]
    rw [ih]
    simp
    omega

theorem fold_pre (w : List ℕ) (c : ℕ) (acc : List ℕ) (k : ℕ) (hk : k < acc.length) :
    (w.foldl stepF (c, acc)).2.getD k 0 = acc.getD k 0 := by
  induction w generalizing c acc with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldl_cons, stepF]
    have hk' : k < (acc ++ [(dg b + c) % 3]).length := by simp; omega
    rw [ih _ _ hk']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem fold_main (w : List ℕ) (c : ℕ) (acc : List ℕ) (j : ℕ) (hj : j < w.length) :
    (w.foldl stepF (c, acc)).2.getD (acc.length + j) 0
      = (dg (w.getD j 0) + (w.take j).foldl (fun c t => if cls t = 2 then c else cls t) c) % 3 := by
  induction w generalizing c acc j with
  | nil => simp at hj
  | cons b t ih =>
    simp only [List.foldl_cons, stepF]
    cases j with
    | zero =>
      have hk' : acc.length + 0 < (acc ++ [(dg b + c) % 3]).length := by simp
      rw [fold_pre t _ _ _ hk']
      simp [List.getD_eq_getElem?_getD]
    | succ j =>
      have hj' : j < t.length := by simpa using hj
      have := ih (if cls b = 2 then c else cls b) (acc ++ [(dg b + c) % 3]) j hj'
      have e : acc.length + (j + 1) = (acc ++ [(dg b + c) % 3]).length + j := by simp; omega
      rw [e, this]
      simp

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have h : i - 1 < w.length := by omega
  unfold prog target
  have := fold_main w 0 [] (i - 1) h
  simpa using this

end Lane4.Case
