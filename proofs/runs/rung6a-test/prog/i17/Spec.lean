namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

def h (t : ℕ) : ℕ := if t = 1 then 1 else if t = 2 then 0 else 0
def prevOcc (w : List ℕ) (i : ℕ) : Option ℕ :=
  (List.range i).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == tokAt w i))
def target (w : List ℕ) (i : ℕ) : ℕ :=
  match prevOcc w i with
  | some j => h (tokAt w (j + 1))
  | none => 0

def StatementProg (f : List ℕ → List ℕ) : Prop :=
  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) →
  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → (f w).getD (i - 1) 0 = target w i

end Lane4.Case
