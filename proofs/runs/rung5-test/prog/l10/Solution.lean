namespace Lane4.Case

def g (s t : ℕ) : ℕ := if val t = 0 then s else val t

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ := (g s.1 t, s.2 ++ [g s.1 t])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem fold_eq (w : List ℕ) (a : ℕ) (acc : List ℕ) :
    (w.foldl step (a, acc)).2 = acc ++ (w.foldl step (a, [])).2 := by
  induction w generalizing a acc with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldl_cons, step]
    rw [ih (g a b) (acc ++ [g a b]), ih (g a b) ([] ++ [g a b])]
    simp

theorem R_cons (b : ℕ) (t : List ℕ) (a : ℕ) :
    ((b :: t).foldl step (a, [])).2 = g a b :: (t.foldl step (g a b, [])).2 := by
  simp only [List.foldl_cons, step]
  rw [fold_eq]
  simp

theorem R_get (w : List ℕ) (a : ℕ) : ∀ i, i < w.length →
    (w.foldl step (a, [])).2.getD i 0 = (w.take (i+1)).foldl g a := by
  induction w generalizing a with
  | nil => intro i h; simp at h
  | cons b t ih =>
    intro i hi
    rw [R_cons]
    cases i with
    | zero => simp
    | succ j =>
      have hj : j < t.length := by simpa using hi
      rw [List.getD_cons_succ, ih (g a b) j hj]
      simp [List.take_succ_cons]

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have h : i - 1 < w.length := by omega
  unfold prog target lastv
  rw [R_get w 0 (i-1) h]
  have : i - 1 + 1 = i := by omega
  rw [this]
  rfl

end Lane4.Case
