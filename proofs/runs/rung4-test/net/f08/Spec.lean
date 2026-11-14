namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

def code (t : ℕ) : ℕ := if t = 1 then 1 else if t = 2 then 0 else if t = 3 then 1 else if t = 4 then 1 else if t = 5 then 2 else 0
def cbit (t : ℕ) : ℕ := if t = 1 then 0 else if t = 2 then 0 else if t = 3 then 1 else if t = 4 then 0 else if t = 5 then 0 else 0
def firstc (p : List ℕ) : ℕ := p.foldl (fun s t => if s = 0 then code t else s) 0
def target (w : List ℕ) (i : ℕ) : ℕ :=
  ((if firstc (w.take i) = 2 then 1 else 0) + cbit (w.getD (i - 1) 0)) % 2

def Statement (N : TNet) : Prop :=
  ∀ (u : ℝ) (fl : ℝ → ℝ), Rounding u fl → 0 ≤ u → u ≤ 1 / 16777216 →
  ∀ p : Pert, p.Within (1 / 200) →
  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) → u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 →
  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → |N.out fl p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4

end Lane4.Case
