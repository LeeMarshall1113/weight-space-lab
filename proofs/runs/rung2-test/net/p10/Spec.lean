namespace Lane4.Case
open Lane4.Seq

def Valid (w : List ℕ) : Prop := w ≠ [] ∧ ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3

def inS (t : ℕ) : Bool := t == 1 || t == 2
def Good (w : List ℕ) : Prop := (w.countP inS) % 2 = 0

def Statement (N : TNet) : Prop :=
  ∀ w : List ℕ, Valid w → (0 < N.out w w.length ↔ Good w)

end Lane4.Case
