namespace Lane4.Case

def step (acc : Bool) (t : ℕ) : Bool := if (t == 2 || t == 3) then !acc else acc

def prog (w : List ℕ) : Bool := w.foldl step false

-- PROOF

theorem foldl_step (w : List ℕ) (a : Bool) :
    w.foldl step a = (a != decide (w.countP inS % 2 = 1)) := by
  induction w generalizing a with
  | nil => cases a <;> simp
  | cons t r ih =>
    rw [List.foldl_cons, ih, List.countP_cons]
    by_cases h : inS t = true
    · have h2 : (t == 2 || t == 3) = true := h
      simp only [step, h2, h, if_true]
      cases a <;> by_cases hp : r.countP inS % 2 = 1 <;> simp [hp] <;> omega
    · have h' : inS t = false := by simpa using h
      have h2 : (t == 2 || t == 3) = false := h'
      simp only [step, h2, h', Bool.false_eq_true, if_false]
      simp

theorem prog_correct : StatementProg prog := by
  intro w _
  unfold prog Good
  rw [foldl_step]
  simp

end Lane4.Case
