namespace Lane4.Case
open Lane4.Seq (tokAt)

def step (st : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (if st.1 = 0 then code t else st.1,
   st.2 ++ [((if (if st.1 = 0 then code t else st.1) = 2 then 1 else 0) + cbit t) % 2])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem acc_eq (w : List ℕ) : ∀ (s : ℕ) (acc : List ℕ),
    (w.foldl step (s, acc)).2 = acc ++ (w.foldl step (s, [])).2 := by
  induction w with
  | nil => intro s acc; simp
  | cons b t ih =>
    intro s acc
    simp only [List.foldl_cons]
    rw [ih, ih (if (s, acc).1 = 0 then code b else (s, acc).1) ([] ++ _)]
    simp [step]

theorem main_lemma (w : List ℕ) : ∀ (s j : ℕ), j < w.length →
    (w.foldl step (s, [])).2.getD j 0 =
      ((if (w.take (j+1)).foldl (fun s t => if s = 0 then code t else s) s = 2 then 1 else 0)
        + cbit (w.getD j 0)) % 2 := by
  induction w with
  | nil => intro s j hj; simp at hj
  | cons b t ih =>
    intro s j hj
    simp only [List.foldl_cons]
    rw [acc_eq]
    cases j with
    | zero => simp [step]
    | succ j =>
      have hj' : j < t.length := by simpa using hj
      have := ih (if s = 0 then code b else s) j hj'
      simp [step, this]

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have := main_lemma w 0 j (by omega)
  simp only [prog, target, firstc, Nat.add_sub_cancel]
  exact this

end Lane4.Case
