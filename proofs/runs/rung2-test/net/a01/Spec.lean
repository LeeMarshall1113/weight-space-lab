namespace Lane4.Case
open Lane4.Seq

def Valid (w : List ℕ) : Prop := w ≠ [] ∧ ∀ t ∈ w, 1 ≤ t ∧ t ≤ 9

def dA (t : ℕ) : ℕ := (t - 1) / 3
def dC (t : ℕ) : ℕ := (t - 1) % 3
def carryOut (p : List ℕ) : ℕ := p.foldl (fun c t => (dA t + dC t + c) / 3) 0
def digit (w : List ℕ) (i : ℕ) : ℕ :=
  (dA (w.getD (i - 1) 0) + dC (w.getD (i - 1) 0) + carryOut (w.take (i - 1))) % 3

def Statement (N : TNet) : Prop :=
  ∀ w : List ℕ, Valid w → ∀ i, 1 ≤ i → i ≤ w.length → N.out w i = ((digit w i : ℕ) : ℚ)

end Lane4.Case
