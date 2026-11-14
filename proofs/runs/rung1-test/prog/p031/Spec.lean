namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  |max (min (min ((-1) * x1 + (-3)) (x0 + (-2) * x1 + (-5/2))) ((-2) * x1 + (1/2))) (min (max (min ((-1) * x1 + (-3)) (x0 + (-2) * x1 + (-5/2))) ((-2) * x1 + (1/2))) ((-2) * x0 + x1 + (1/2)))|

def StatementProg (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x0 x1 : ℝ, (-4) ≤ x0 → x0 ≤ 4 → (-4) ≤ x1 → x1 ≤ 1 →
    f x0 x1 = spec x0 x1

end Lane4.Case
