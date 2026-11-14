namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  |max (3 * x0 + 3 * x1 + 1) ((1/2) * x0 + (-1/2))|

def StatementProg (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x0 x1 : ℝ, (-2) ≤ x0 → x0 ≤ 4 → (-8) ≤ x1 → x1 ≤ 4 →
    f x0 x1 = spec x0 x1

end Lane4.Case
