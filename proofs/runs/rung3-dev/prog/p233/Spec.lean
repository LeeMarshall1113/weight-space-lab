namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  max (min (max (x0 + (-1) * x1 + (1/2)) (2 * x1 + (-3))) (3 * x1 + 2)) ((-1/2) * x1 + 1)

def StatementProg (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x0 x1 : ℝ, (-1) ≤ x0 → x0 ≤ 4 → (-8) ≤ x1 → x1 ≤ 2 →
    f x0 x1 = spec x0 x1

end Lane4.Case
