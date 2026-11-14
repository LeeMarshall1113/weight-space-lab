namespace Lane4.Case
open Lane4.Seq

def Valid (w : List ℕ) : Prop := w ≠ [] ∧ ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3

def IsRank (w : List ℕ) (i t : ℕ) : Prop :=
  w.countP (fun s => decide (s < t)) < i ∧ i ≤ w.countP (fun s => decide (s ≤ t))

def Statement (N : TNet) : Prop :=
  ∀ w : List ℕ, Valid w → ∀ i, 1 ≤ i → i ≤ w.length →
    ∃ t : ℕ, N.out w i = (t : ℚ) ∧ IsRank w i t

end Lane4.Case
