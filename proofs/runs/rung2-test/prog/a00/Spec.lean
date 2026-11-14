namespace Lane4.Case
open Lane4.Seq

def Valid (w : List ℕ) : Prop := w ≠ [] ∧ ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4

def dA (t : ℕ) : ℕ := (t - 1) / 2
def dC (t : ℕ) : ℕ := (t - 1) % 2
def carryOut (p : List ℕ) : ℕ := p.foldl (fun c t => (dA t + dC t + c) / 2) 0
def digit (w : List ℕ) (i : ℕ) : ℕ :=
  (dA (w.getD (i - 1) 0) + dC (w.getD (i - 1) 0) + carryOut (w.take (i - 1))) % 2

def StatementProg (f : List ℕ → List ℕ) : Prop :=
  ∀ w : List ℕ, Valid w → ∀ i, 1 ≤ i → i ≤ w.length → (f w).getD (i - 1) 0 = digit w i

end Lane4.Case
