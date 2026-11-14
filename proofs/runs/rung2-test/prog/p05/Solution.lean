namespace Lane4.Case

def step (acc : Bool) (t : ℕ) : Bool :=
  if (t == 1 || t == 3 || t == 4) then !acc else acc

def prog (w : List ℕ) : Bool := w.foldl step true

-- PROOF

theorem foldl_step (w : List ℕ) (a : Bool) :
    w.foldl step a = true ↔ (a = true ↔ (w.countP inS) % 2 = 0) := by
  induction w generalizing a with
  | nil => cases a <;> simp
  | cons t r ih =>
    rw [List.foldl_cons, ih]
    by_cases h : inS t = true
    · have h' : (t == 1 || t == 3 || t == 4) = true := h
      have hs : step a t = !a := by simp [step, h']
      rw [hs, List.countP_cons_of_pos h]
      cases a <;> simp <;> omega
    · have h0 : inS t = false := by simpa using h
      have h' : (t == 1 || t == 3 || t == 4) = false := h0
      have hs : step a t = a := by simp [step, h']
      rw [hs, List.countP_cons_of_neg h]

theorem prog_correct : StatementProg prog := by
  intro w _
  unfold prog Good
  rw [foldl_step]
  simp

end Lane4.Case
