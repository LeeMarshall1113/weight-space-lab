namespace Lane4.Case
open Lane4.Cert Lane4.Cert8

/-- Rounding to the dyadic grid goes the right way. -/
def RoundSound : Prop :=
  ∀ (b : ℕ) (x : ℚ), dnB b x ≤ x ∧ x ≤ upB b x

/-- The rational enclosures of the exponential used by the checker are enclosures:
for every rational `x ≤ 6`, `expLo x ≤ exp x ≤ expHi x`, and `expLo x` is not negative. -/
def ExpEncl : Prop :=
  ∀ x : ℚ, x ≤ 6 →
    0 ≤ expLo x ∧ ((expLo x : ℚ) : ℝ) ≤ Real.exp ((x : ℚ) : ℝ) ∧
    Real.exp ((x : ℚ) : ℝ) ≤ ((expHi x : ℚ) : ℝ)

end Lane4.Case
