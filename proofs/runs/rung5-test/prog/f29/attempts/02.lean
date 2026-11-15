namespace Lane4.Case
open Lane4.Seq (tokAt)

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (if s.1 = 0 then code t else s.1,
   s.2 ++ [((if (if s.1 = 0 then code t else s.1) = 2 then 1 else 0) + cbit t) % 2])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

def gg (f : ℕ) (p : List ℕ) : ℕ := p.foldl (fun s t => if s = 0 then code t else s) f

-- PROOF

theorem pres (w : List ℕ) : ∀ (f : ℕ) (acc : List ℕ) (j : ℕ), j < acc.length →
    (w.foldl step (f, acc)).2.getD j 0 = acc.getD j 0 := by
  induction w with
  | nil => intro f acc j _; simp
  | cons b t ih =>
    intro f acc j hj
    simp only [List.foldl_cons]
    rw [ih _ _ _ (by simp [step]; omega)]
    simp only [step]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left hj]

theorem main (w : List ℕ) : ∀ (f : ℕ) (acc : List ℕ) (i : ℕ), i < w.length →
    (w.foldl step (f, acc)).2.getD (acc.length + i) 0 =
      ((if gg f (w.take (i + 1)) = 2 then 1 else 0) + cbit (w.getD i 0)) % 2 := by
  induction w with
  | nil => intro f acc i h; simp at h
  | cons b t ih =>
    intro f acc i hi
    simp only [List.foldl_cons]
    cases i with
    | zero =>
      rw [pres t _ _ _ (by simp [step])]
      simp [step, gg, List.getD_eq_getElem?_getD]
    | succ i' =>
      have h' : i' < t.length := by simp at hi; omega
      have := ih (step (f, acc) b).1 (step (f, acc) b).2 i' h'
      have hl : (step (f, acc) b).2.length = acc.length + 1 := by simp [step]
      rw [hl] at this
      have e : acc.length + (i' + 1) = acc.length + 1 + i' := by omega
      rw [e, this]
      simp [gg, step, List.take_succ_cons]

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have h := main w 0 [] (i - 1) (by omega)
  have e : i - 1 + 1 = i := by omega
  rw [e] at h
  simp only [List.length_nil, Nat.zero_add] at h
  unfold prog target firstc
  rw [h]
  rfl

end Lane4.Case
