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
    obtain ⟨s1, o, h1, h2⟩ : ∃ s1 o, step (s, []) b = (s1, [o]) ∧ step (s, acc) b = (s1, acc ++ [o]) :=
      ⟨_, _, by simp [step], by simp [step]⟩
    simp only [List.foldl_cons]
    rw [h1, h2, ih, ih s1 [o]]
    simp

theorem main_lemma (w : List ℕ) : ∀ (s j : ℕ), j < w.length →
    (w.foldl step (s, [])).2.getD j 0 =
      ((if (w.take (j+1)).foldl (fun s t => if s = 0 then code t else s) s = 2 then 1 else 0)
        + cbit (w.getD j 0)) % 2 := by
  induction w with
  | nil => intro s j hj; simp at hj
  | cons b t ih =>
    intro s j hj
    obtain ⟨s1, o, h1, hs1, ho⟩ : ∃ s1 o, step (s, []) b = (s1, [o]) ∧
        s1 = (if s = 0 then code b else s) ∧
        o = ((if s1 = 2 then 1 else 0) + cbit b) % 2 :=
      ⟨_, _, by simp [step], rfl, rfl⟩
    simp only [List.foldl_cons]
    rw [h1, acc_eq]
    cases j with
    | zero => simp [hs1, ho]
    | succ j =>
      have hj' : j < t.length := by simpa using hj
      have := ih s1 j hj'
      rw [hs1] at this
      simp [hs1] at this ⊢
      exact this

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have := main_lemma w 0 j (by omega)
  simp only [prog, target, firstc, Nat.add_sub_cancel]
  exact this

end Lane4.Case
