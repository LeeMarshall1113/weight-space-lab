namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft

/-- Left-to-right rounded summation is close to the exact sum. Range condition: twice the
total magnitude (plus the underflow terms) stays within `M`. -/
def RsumErr : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Rnd u η M fl → 0 ≤ u → 0 ≤ η →
  ∀ (l : List ℝ) (acc : ℝ), u * (l.length : ℝ) ≤ 1 / 256 →
    2 * (|acc| + (l.map (fun a => |a|)).sum) + 2 * (l.length : ℝ) * η ≤ M →
    |rsum fl l acc - (acc + l.sum)|
      ≤ 101 / 100 * u * (l.length : ℝ) * (|acc| + (l.map (fun a => |a|)).sum)
        + 2 * (l.length : ℝ) * η

/-- A geometric sum over the distances to `j` in a duplicate-free list of naturals. -/
def GeomDist : Prop :=
  ∀ (c : List ℕ), c.Nodup → ∀ (j : ℕ) (q : ℝ), 0 ≤ q → q ≤ 1 / 2 →
    ((c.filter (fun k => decide (k ≠ j))).map (fun k => q ^ ndist j k)).sum ≤ 4 * q

/-- Softmax attention with a clear winner returns the winner's value, up to a small error.
Key `j` beats every other candidate `k` by a score gap of at least 16 per unit of
distance `|j - k|`. `B` bounds the values, `Sb` the scores, `n` the number of candidates.
Range conditions: `2 * Sb ≤ M` and `4 * B + 4 ≤ M`. -/
def SavgNear : Prop :=
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Rnd u η M fl → ExpM u η ex →
  0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  ∀ (c : List ℕ), c.Nodup → ∀ n : ℕ, c.length ≤ n →
  u * (n : ℝ) ≤ 1 / 256 → η * (n : ℝ) ≤ 1 / 2 ^ 100 →
  ∀ (s f : ℕ → ℝ) (j : ℕ), j ∈ c →
  (∀ k ∈ c, k ≠ j → s k ≤ s j - 16 * (ndist j k : ℝ)) →
  ∀ Sb : ℝ, (∀ k ∈ c, |s k| ≤ Sb) → 2 * Sb ≤ M →
  ∀ B : ℝ, (∀ k ∈ c, |f k| ≤ B) → 4 * B + 4 ≤ M →
    |savg fl ex c s f - f j| ≤ B / 100 + 1 / 2 ^ 90
      ∧ fl (savg fl ex c s f) = savg fl ex c s f

/-- If every candidate's value is exactly 0, the attention output is exactly 0. -/
def SavgZeros : Prop :=
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Rnd u η M fl →
  ∀ (c : List ℕ) (s f : ℕ → ℝ), (∀ k ∈ c, f k = 0) → savg fl ex c s f = 0

end Lane4.Case
