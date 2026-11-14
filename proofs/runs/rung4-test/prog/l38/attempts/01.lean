namespace Lane4.Case

def gstep (a t : ℕ) : ℕ := if val t = 0 then a else val t

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (gstep s.1 t, s.2 ++ [gstep s.1 t])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem pre_lemma (w : List ℕ) : ∀ (a : ℕ) (acc : List ℕ),
    ∃ r : List ℕ, (w.foldl step (a, acc)).2 = acc ++ r := by
  induction w with
  | nil => intro a acc; exact ⟨[], by simp⟩
  | cons b t ih =>
    intro a acc
    obtain ⟨r, hr⟩ := ih (gstep a b) (acc ++ [gstep a b])
    refine ⟨gstep a b :: r, ?_⟩
    simp only [List.foldl_cons, step] at hr ⊢
    rw [hr]
    simp

theorem main_lemma (w : List ℕ) : ∀ (a : ℕ) (acc : List ℕ) (j : ℕ), j < w.length →
    (w.foldl step (a, acc)).2.getD (acc.length + j) 0
      = ((w.take (j + 1)).foldl gstep a) := by
  induction w with
  | nil => intro a acc j hj; simp at hj
  | cons b t ih =>
    intro a acc j hj
    cases j with
    | zero =>
      obtain ⟨r, hr⟩ := pre_lemma t (gstep a b) (acc ++ [gstep a b])
      simp only [List.foldl_cons, step]
      rw [hr]
      simp [List.getD_eq_getElem?_getD]
    | succ j =>
      have hj' : j < t.length := by simpa using hj
      have := ih (gstep a b) (acc ++ [gstep a b]) j hj'
      simp only [List.foldl_cons, step]
      have e : acc.length + (j + 1) = (acc ++ [gstep a b]).length + j := by
        simp; omega
      rw [e, this]
      simp

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have h := main_lemma w 0 [] (i - 1) (by omega)
  have e : i - 1 + 1 = i := by omega
  rw [e] at h
  simp only [List.length_nil, Nat.zero_add] at h
  unfold prog target lastv
  rw [h]
  rfl

end Lane4.Case
