namespace Lane4.Case
open Lane4.Seq

def Valid (w : List ℕ) : Prop := w ≠ [] ∧ ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2

def IsRank (w : List ℕ) (i t : ℕ) : Prop :=
  w.countP (fun s => decide (s < t)) < i ∧ i ≤ w.countP (fun s => decide (s ≤ t))

def Statement (N : TNet) : Prop :=
  ∀ w : List ℕ, Valid w → ∀ i, 1 ≤ i → i ≤ w.length →
    ∃ t : ℕ, N.out w i = (t : ℚ) ∧ IsRank w i t


/-- `b` is within a relative 1/200 of `a` (so `b = 0` when `a = 0`). -/
def qClose (a b : ℚ) : Bool := decide (|b - a| ≤ |a| / 200)
def vClose (a b : List ℚ) : Bool := a.length == b.length && (List.zipWith qClose a b).all id
def mClose (A B : List (List ℚ)) : Bool := A.length == B.length && (List.zipWith vClose A B).all id
def hClose (h g : Head) : Bool := mClose h.A g.A && mClose h.V g.V && decide (h.mask = g.mask)
def bClose (B C : Block) : Bool :=
  B.heads.length == C.heads.length && (List.zipWith hClose B.heads C.heads).all id &&
  mClose B.W1 C.W1 && vClose B.b1 C.b1 && mClose B.W2 C.W2 && vClose B.b2 C.b2
/-- Every weight of `N'` is within a relative 1/200 of the corresponding weight of `N`,
and every weight written as 0 is still 0. -/
def netClose (N N' : TNet) : Bool :=
  mClose N.embed N'.embed && N.blocks.length == N'.blocks.length &&
  (List.zipWith bClose N.blocks N'.blocks).all id && vClose N.outW N'.outW && qClose N.outB N'.outB

end Lane4.Case
