namespace Lane4.Case

def step (acc : Bool) (t : ℕ) : Bool :=
  if t == 1 || t == 2 then !acc else acc

def prog (w : List ℕ) : Bool := w.foldl step true

-- PROOF

theorem foldl_step (w : List ℕ) (a : Bool) :
    w.foldl step a = true ↔ ((a = true) ↔ (w.countP inS) % 2 = 0) := by
  induction w generalizing a with
  | nil => cases a <;> simp
  | cons t r ih =>
    rw [List.foldl_cons, ih, List.countP_cons]
    by_cases h : inS t = true
    · have h' : (t == 1 || t == 2) = true := h
      simp only [step, h', if_true, h]
      cases a <;> simp <;> omega
    · have h' : ¬ ((t == 1 || t == 2) = true) := h
      simp only [step, h', if_false, h]
      cases a <;> simp

theorem prog_correct : StatementProg prog := by
  intro w _
  unfold prog Good
  rw [foldl_step]
  simp

end Lane4.Case
