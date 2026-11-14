namespace Lane4.Case

noncomputable def spec (x0 x1 x2 : ℝ) : ℝ :=
  min (max ((-2) * x0 + (1/2) * x2 + (1/2)) ((-2) * x2 + 2)) ((-2) * x1 + (-1/2) * x2 + (-3/2))

def StatementProg (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ x0 x1 x2 : ℝ, (-1) ≤ x0 → x0 ≤ 1 → (-8) ≤ x1 → x1 ≤ 4 → (-8) ≤ x2 → x2 ≤ 2 →
    f x0 x1 x2 = spec x0 x1 x2

end Lane4.Case
