/-
WORKED EXAMPLE on a task outside the four task families: accept exactly when the input
contains token 2. It was checked by the same checker and passed. Only the part between
the SOLUTION markers is what you write. Pattern: a fold with an explicit step function,
then an invariant about `foldl` proved by induction with the accumulator generalised.
-/

-- ===== Spec.lean (given) =====
namespace Lane4.Case
open Lane4.Seq

def Valid (w : List ℕ) : Prop := w ≠ [] ∧ ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3

def Good (w : List ℕ) : Prop := 2 ∈ w

def StatementProg (f : List ℕ → Bool) : Prop :=
  ∀ w : List ℕ, Valid w → (f w = true ↔ Good w)

end Lane4.Case

-- ===== Solution.lean (SOLUTION START) =====
namespace Lane4.Case

def step (acc : Bool) (t : ℕ) : Bool := acc || t == 2

def prog (w : List ℕ) : Bool := w.foldl step false

-- PROOF

theorem step_true (a : Bool) (t : ℕ) : step a t = true ↔ (a = true ∨ t = 2) := by
  simp [step]

theorem foldl_step (w : List ℕ) (a : Bool) : w.foldl step a = true ↔ (a = true ∨ 2 ∈ w) := by
  induction w generalizing a with
  | nil => simp
  | cons t r ih =>
    rw [List.foldl_cons, ih, step_true, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h.symm)
      · exact Or.inr h

theorem prog_correct : StatementProg prog := by
  intro w _
  unfold prog Good
  rw [foldl_step]
  simp

end Lane4.Case
-- ===== SOLUTION END =====
