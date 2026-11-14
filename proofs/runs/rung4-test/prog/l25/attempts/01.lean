namespace Lane4.Case
open Lane4.Seq (tokAt)

/-- State: (last marked value so far, outputs so far). -/
def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  let v := if val t = 0 then s.1 else val t
  (v, s.2 ++ [v])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem fold_aux (w : List ℕ) : ∀ (a : ℕ) (acc : List ℕ),
    ∃ L : List ℕ, (w.foldl step (a, acc)).2 = acc ++ L ∧ L.length = w.length ∧
      ∀ i, 1 ≤ i → i ≤ w.length →
        L.getD (i - 1) 0 = (w.take i).foldl (fun s t => if val t = 0 then s else val t) a := by
  induction w with
  | nil => intro a acc; exact ⟨[], by simp, by simp, by intro i h1 h2; simp at h2; omega⟩
  | cons b t ih =>
    intro a acc
    obtain ⟨L', h1, h2, h3⟩ := ih (if val b = 0 then a else val b)
      (acc ++ [if val b = 0 then a else val b])
    refine ⟨(if val b = 0 then a else val b) :: L', ?_, ?_, ?_⟩
    · simp only [List.foldl_cons, step]
      rw [h1]; simp
    · simp [h2]
    · intro i hi1 hi2
      rcases Nat.lt_or_ge i 2 with h | h
      · have : i = 1 := by omega
        subst this
        simp
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        have := h3 j (by omega) (by simp at hi2; omega)
        have e : j + 1 - 1 = (j - 1) + 1 := by omega
        rw [e]
        simp only [List.getD_cons_succ, List.take_succ_cons, List.foldl_cons]
        exact this

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  obtain ⟨L, h1, h2, h3⟩ := fold_aux w 0 []
  unfold prog target lastv
  rw [h1]
  simpa using h3 i hi1 hi

end Lane4.Case
