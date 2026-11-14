namespace Lane4.Case
open Lane4.Seq

def Valid (w : List ℕ) : Prop := w ≠ [] ∧ ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4

def wt (t : ℕ) : ℤ := if t = 1 then 1 else if t = 2 then 1 else if t = 3 then 1 else if t = 4 then (-1) else 0
def Good (w : List ℕ) : Prop :=
  (∀ k, k ≤ w.length → 0 ≤ ((w.take k).map wt).sum) ∧ (w.map wt).sum = 0

def StatementProg (f : List ℕ → Bool) : Prop :=
  ∀ w : List ℕ, Valid w → (f w = true ↔ Good w)

end Lane4.Case
