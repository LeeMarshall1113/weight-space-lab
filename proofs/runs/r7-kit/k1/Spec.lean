namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft

/-- Softmax attention with a clear winner returns the winner's value, up to a small error.
Key `j` beats every other candidate `k` by a score gap of at least 12 per unit of
distance `|j - k|`. `B` bounds the values, `Sb` the scores, `n` the number of candidates.
Range conditions: `2 * Sb ≤ M` and `4 * B + 4 ≤ M`. -/
def SavgNear12 : Prop :=
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Rnd u η M fl → ExpM u η ex →
  0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  ∀ (c : List ℕ), c.Nodup → ∀ n : ℕ, c.length ≤ n →
  u * (n : ℝ) ≤ 1 / 256 → η * (n : ℝ) ≤ 1 / 2 ^ 100 →
  ∀ (s f : ℕ → ℝ) (j : ℕ), j ∈ c →
  (∀ k ∈ c, k ≠ j → s k ≤ s j - 12 * (ndist j k : ℝ)) →
  ∀ Sb : ℝ, (∀ k ∈ c, |s k| ≤ Sb) → 2 * Sb ≤ M →
  ∀ B : ℝ, (∀ k ∈ c, |f k| ≤ B) → 4 * B + 4 ≤ M →
    |savg fl ex c s f - f j| ≤ B / 100 + 1 / 2 ^ 90
      ∧ fl (savg fl ex c s f) = savg fl ex c s f

end Lane4.Case
