namespace Lane4.Case
open Lane4.Seq (tokAt)

def g (s t : ℕ) : ℕ := if s = 0 then code t else s

def step (st : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (g st.1 t, st.2 ++ [((if g st.1 t = 2 then 1 else 0) + cbit t) % 2])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem pre (w : List ℕ) : ∀ (s : ℕ) (acc : List ℕ),
    ∃ l, (w.foldl step (s, acc)).2 = acc ++ l := by
  induction w with
  | nil => intro s acc; exact ⟨[], by simp⟩
  | cons b t ih =>
    intro s acc
    obtain ⟨l, hl⟩ := ih (step (s, acc) b).1 (step (s, acc) b).2
    refine ⟨[((if g s b = 2 then 1 else 0) + cbit b) % 2] ++ l, ?_⟩
    simp only [List.foldl_cons]
    rw [hl]
    simp [step]

theorem main (w : List ℕ) : ∀ (s : ℕ) (acc : List ℕ) (j : ℕ), j < w.length →
    ((w.foldl step (s, acc)).2).getD (acc.length + j) 0
      = ((if (w.take (j + 1)).foldl g s = 2 then 1 else 0) + cbit (w.getD j 0)) % 2 := by
  induction w with
  | nil => intro s acc j hj; simp at hj
  | cons b t ih =>
    intro s acc j hj
    cases j with
    | zero =>
      obtain ⟨l, hl⟩ := pre t (step (s, acc) b).1 (step (s, acc) b).2
      simp only [List.foldl_cons]
      rw [hl]
      have h1 : (acc ++ [((if g s b = 2 then 1 else 0) + cbit b) % 2] ++ l)[acc.length]?
          = some (((if g s b = 2 then 1 else 0) + cbit b) % 2) := by
        simp
      simp [step, List.getD_eq_getElem?_getD, h1]
    | succ j =>
      have hj' : j < t.length := by simp at hj; omega
      have := ih (step (s, acc) b).1 (step (s, acc) b).2 j hj'
      simp only [List.foldl_cons]
      have e : acc.length + (j + 1) = (step (s, acc) b).2.length + j := by
        simp [step]; omega
      rw [e, this]
      simp [step]
      try rfl

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have h := main w 0 [] (i - 1) (by omega)
  have e : i - 1 + 1 = i := by omega
  rw [e] at h
  unfold prog target firstc
  simp only [g] at h
  simpa using h

end Lane4.Case
