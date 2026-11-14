namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  min (max (min ((-1) * x0 + 1) ((-1) * x0 + (1/2))) (min (max ((-1) * x0 + 1) ((-1) * x0 + (1/2))) (2 * x0 + (5/2)))) ((1/2) * x1 + (-2))

def StatementProg (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x0 x1 : ℝ, (-2) ≤ x0 → x0 ≤ 4 → (-8) ≤ x1 → x1 ≤ 8 →
    f x0 x1 = spec x0 x1

end Lane4.Case
