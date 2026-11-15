namespace Lane4.Case
open Lane4.RSeq

/-- The 24-bit floating-point grid with exponents unbounded in BOTH directions:
`m * 2^e` with an integer significand `|m| < 2^24` and any integer exponent `e`.
(Binary32 without its exponent limits: no subnormals, no overflow.) -/
def FLX : Set ℝ := {x | ∃ m e : ℤ, |m| < 2 ^ 24 ∧ x = (m : ℝ) * (2 : ℝ) ^ e}

/-- `fl` rounds every real to a nearest point of the grid, and is odd. -/
def IsRNX (fl : ℝ → ℝ) : Prop :=
  (∀ x, fl x ∈ FLX ∧ ∀ g ∈ FLX, |fl x - x| ≤ |g - x|) ∧ ∀ x, fl (-x) = -fl x

/-- Every such rounding satisfies the rung-4 rounding model with `u = 2^-24`. -/
def RnxRounding : Prop := ∀ fl, IsRNX fl → Rounding (1 / 2 ^ 24) fl

/-- Such a rounding exists, and it is not the identity (it moves 2^24 + 1). -/
def RnxExists : Prop := ∃ fl, IsRNX fl ∧ fl (16777217 : ℝ) ≠ 16777217

end Lane4.Case
