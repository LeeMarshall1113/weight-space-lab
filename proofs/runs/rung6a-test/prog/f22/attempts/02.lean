namespace Lane4.Case

def fs (s t : ℕ) : ℕ := if s = 0 then code t else s

/-- State: (first marked code so far, outputs so far). -/
def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (fs s.1 t, s.2 ++ [((if fs s.1 t = 2 then 1 else 0) + cbit t) % 2])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem pre_lemma (w : List ℕ) (s : ℕ) (acc : List ℕ) (j : ℕ) (hj : j < acc.length) :
    (w.foldl step (s, acc)).2.getD j 0 = acc.getD j 0 := by
  induction w generalizing s acc with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldl_cons, step]
    have hj' : j < (acc ++ [((if fs s b = 2 then 1 else 0) + cbit b) % 2]).length := by
      simp; omega
    rw [ih _ _ hj']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem main_lemma (w : List ℕ) (s : ℕ) (acc : List ℕ) (j : ℕ) (hj : j < w.length) :
    (w.foldl step (s, acc)).2.getD (acc.length + j) 0
      = ((if (w.take (j+1)).foldl fs s = 2 then 1 else 0) + cbit (w.getD j 0)) % 2 := by
  induction w generalizing s acc j with
  | nil => simp at hj
  | cons b t ih =>
    simp only [List.foldl_cons, step]
    cases j with
    | zero =>
      have hj' : acc.length < (acc ++ [((if fs s b = 2 then 1 else 0) + cbit b) % 2]).length := by
        simp
      rw [Nat.add_zero, pre_lemma _ _ _ _ hj']
      simp [List.getD_eq_getElem?_getD]
    | succ k =>
      have hk : k < t.length := by simp at hj; omega
      have := ih (fs s b) (acc ++ [((if fs s b = 2 then 1 else 0) + cbit b) % 2]) k hk
      have e : (acc ++ [((if fs s b = 2 then 1 else 0) + cbit b) % 2]).length + k
          = acc.length + (k + 1) := by simp; omega
      rw [e] at this
      rw [this]
      simp [List.take_succ_cons, List.getD_eq_getElem?_getD]
      try rfl

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have h := main_lemma w 0 [] (i - 1) (by omega)
  have e : i - 1 + 1 = i := by omega
  rw [e] at h
  unfold prog target firstc
  simpa [fs] using h

end Lane4.Case
