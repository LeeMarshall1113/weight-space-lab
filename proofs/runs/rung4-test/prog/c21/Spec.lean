namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

def cls (t : ℕ) : ℕ := if t = 1 then 1 else if t = 2 then 1 else if t = 3 then 0 else if t = 4 then 0 else if t = 5 then 2 else 0
def dg (t : ℕ) : ℕ := if t = 1 then 0 else if t = 2 then 0 else if t = 3 then 1 else if t = 4 then 0 else if t = 5 then 0 else 0
def carry (p : List ℕ) : ℕ := p.foldl (fun c t => if cls t = 2 then c else cls t) 0
def target (w : List ℕ) (i : ℕ) : ℕ :=
  (dg (w.getD (i - 1) 0) + carry (w.take (i - 1))) % 2

def StatementProg (f : List ℕ → List ℕ) : Prop :=
  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) →
  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → (f w).getD (i - 1) 0 = target w i

end Lane4.Case
