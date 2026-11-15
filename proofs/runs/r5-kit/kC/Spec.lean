namespace Lane4.Case
open Lane4.RSoft

/-- The binary32 grid with subnormals and with exponents unbounded above:
`m * 2^e` with an integer significand `|m| < 2^24` and an integer exponent `e ≥ -149`.
(Finite binary32 numbers are exactly the members of absolute value at most
`(2^24 - 1) * 2^104`.) -/
def F32U : Set ℝ := {x | ∃ m e : ℤ, |m| < 2 ^ 24 ∧ -149 ≤ e ∧ x = (m : ℝ) * (2 : ℝ) ^ e}

/-- `fl` rounds every real to a nearest grid point (any tie rule). -/
def IsRN (fl : ℝ → ℝ) : Prop := ∀ x, fl x ∈ F32U ∧ ∀ g ∈ F32U, |fl x - x| ≤ |g - x|

/-- The largest finite binary32 number. -/
noncomputable def maxF : ℝ := (2 ^ 24 - 1) * 2 ^ 104

/-- Binary32 arithmetic satisfies the rounding model of RSoft.lean on the finite range:
any `fl` that agrees, for `|x| ≤ maxF`, with a round-to-nearest `rn` onto the grid.
(Nothing is assumed about `fl` outside the range.) -/
def RnRnd : Prop :=
  ∀ rn, IsRN rn → ∀ fl : ℝ → ℝ, (∀ x, |x| ≤ maxF → fl x = rn x) →
    Rnd (1 / 2 ^ 24) (1 / 2 ^ 150) maxF fl

/-- Such a rounding function exists. -/
def RnExists : Prop := ∃ fl, IsRN fl

end Lane4.Case
