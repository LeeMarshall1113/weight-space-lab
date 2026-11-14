namespace Lane4.Case

def step (acc : Bool) (t : ℕ) : Bool := if t == 1 || t == 2 then !acc else acc

def prog (w : List ℕ) : Bool := w.foldl step true

-- PROOF

theorem foldl_step (w : List ℕ) (a : Bool) :
    w.foldl step a = true ↔ (a = true ↔ (w.countP inS) % 2 = 0) := by
  induction w generalizing a with
  | nil => simp
  | cons t r ih =>
    rw [List.foldl_cons, ih, List.countP_cons]
    by_cases h : (t == 1 || t == 2) = true
    · have h' : inS t = true := by simpa [inS] using h
      simp only [step, h, h', if_true]
      cases a <;> simp <;> omega
    · have h' : inS t = false := by simpa [inS] using h
      simp only [step, h, h', Bool.false_eq_true, if_false]
      simp

theorem prog_correct : StatementProg prog := by
  intro w _
  unfold prog Good
  rw [foldl_step]
  simp

end Lane4.Case
