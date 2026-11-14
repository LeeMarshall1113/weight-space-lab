namespace Lane4.Case
open Lane4.Seq

def Valid (w : List ℕ) : Prop := w ≠ [] ∧ ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4

def inS (t : ℕ) : Bool := t == 2 || t == 3
def Good (w : List ℕ) : Prop := (w.countP inS) % 2 = 1

def StatementProg (f : List ℕ → Bool) : Prop :=
  ∀ w : List ℕ, Valid w → (f w = true ↔ Good w)

end Lane4.Case
