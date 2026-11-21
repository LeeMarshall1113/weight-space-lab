namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft

/-- THE ARITHMETIC OF SOFTMAX ATTENTION WHEN ONLY THE LAST FEW KEYS MATTER (obligation P2).
The candidate positions `c` are listed in increasing order (that is the order `savg` sums in),
`p` is the last of them, and every candidate at least 3 positions before `p` has a score at
least 16 below that of `p`, falling by a further 1/2 per position. The up to three candidates
nearest to `p` are unconstrained. Then the rounded softmax average `savg` differs from the exact
one by at most `B / 2^13 + 2^-90`, however long the list is. `B` bounds the values, `Sb` the
scores. Range conditions: `2 * Sb ≤ M` and `4 * B + 4 ≤ M`. -/
def SavgArith : Prop :=
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Rnd u η M fl → ExpM u η ex →
  0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  ∀ (c : List ℕ), c.Pairwise (fun a b => a < b) → ∀ n : ℕ, c.length ≤ n →
  u * (n : ℝ) ≤ 1 / 256 → η * (n : ℝ) ≤ 1 / 2 ^ 100 →
  ∀ (s f : ℕ → ℝ) (p : ℕ), p ∈ c → (∀ k ∈ c, k ≤ p) →
  (∀ k ∈ c, k + 3 ≤ p → s k ≤ s p - 16 - ((p : ℝ) - (k : ℝ) - 3) / 2) →
  ∀ Sb : ℝ, (∀ k ∈ c, |s k| ≤ Sb) → 2 * Sb ≤ M →
  ∀ B : ℝ, (∀ k ∈ c, |f k| ≤ B) → 4 * B + 4 ≤ M →
    |savg fl ex c s f - eavg c s f| ≤ B / 2 ^ 13 + 1 / 2 ^ 90
      ∧ fl (savg fl ex c s f) = savg fl ex c s f

end Lane4.Case
