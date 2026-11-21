namespace Lane4.Case

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  let s' := if s.1 = 0 then code t else s.1
  (s', s.2 ++ [((if s' = 2 then 1 else 0) + cbit t) % 2])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

def gg (s : ℕ) (p : List ℕ) : ℕ := p.foldl (fun s t => if s = 0 then code t else s) s

-- PROOF

theorem fold_aux (w : List ℕ) : ∀ (s : ℕ) (acc : List ℕ), ∃ L : List ℕ,
    (w.foldl step (s, acc)).2 = acc ++ L ∧ L.length = w.length ∧
    ∀ i, i < w.length → L.getD i 0 =
      ((if gg s (w.take (i + 1)) = 2 then 1 else 0) + cbit (w.getD i 0)) % 2 := by
  induction w with
  | nil => intro s acc; exact ⟨[], by simp, by simp, by simp⟩
  | cons b t ih =>
    intro s acc
    obtain ⟨L', h1, h2, h3⟩ := ih (if s = 0 then code b else s)
      (acc ++ [((if (if s = 0 then code b else s) = 2 then 1 else 0) + cbit b) % 2])
    refine ⟨((if (if s = 0 then code b else s) = 2 then 1 else 0) + cbit b) % 2 :: L', ?_, ?_, ?_⟩
    · simp only [List.foldl_cons, step]
      rw [h1]; simp
    · simp [h2]
    · intro i hi
      cases i with
      | zero => simp [gg]
      | succ j =>
        have hj : j < t.length := by simpa using hi
        have := h3 j hj
        simp only [List.getD_cons_succ, List.take_succ_cons, List.getD_eq_getElem?_getD,
          List.getElem?_cons_succ] at this ⊢
        rw [this]
        simp [gg]

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  obtain ⟨L, h1, h2, h3⟩ := fold_aux w 0 []
  have h : i - 1 < w.length := by omega
  have := h3 (i - 1) h
  unfold prog target firstc
  rw [h1]
  have e : i - 1 + 1 = i := by omega
  rw [e] at this
  simpa [gg] using this

end Lane4.Case
