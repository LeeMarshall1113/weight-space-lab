namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

def val (t : ℕ) : ℕ := if t = 1 then 0 else if t = 2 then 0 else if t = 3 then 1 else if t = 4 then 3 else if t = 5 then 1 else 0
def lastv (p : List ℕ) : ℕ := p.foldl (fun s t => if val t = 0 then s else val t) 0
def target (w : List ℕ) (i : ℕ) : ℕ := lastv (w.take i)

def StatementProg (f : List ℕ → List ℕ) : Prop :=
  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) →
  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → (f w).getD (i - 1) 0 = target w i

end Lane4.Case
