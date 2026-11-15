namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

def code (t : ℕ) : ℕ := if t = 1 then 1 else if t = 2 then 1 else if t = 3 then 2 else if t = 4 then 2 else if t = 5 then 0 else 0
def cbit (t : ℕ) : ℕ := if t = 1 then 0 else if t = 2 then 1 else if t = 3 then 1 else if t = 4 then 1 else if t = 5 then 0 else 0
def firstc (p : List ℕ) : ℕ := p.foldl (fun s t => if s = 0 then code t else s) 0
def target (w : List ℕ) (i : ℕ) : ℕ :=
  ((if firstc (w.take i) = 2 then 1 else 0) + cbit (w.getD (i - 1) 0)) % 2

def Statement (N : TNet) : Prop :=
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Rnd u η M fl → ExpM u η ex →
  0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  ∀ p : Pert, p.Within (1 / 200) →
  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) →
  u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 → η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100 →
  2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M →
  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → |sout N fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4

end Lane4.Case
