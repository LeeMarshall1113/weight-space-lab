namespace Lane4.Case

noncomputable def spec (x0 x1 x2 : ℝ) : ℝ :=
  max (min (max ((1/2) * x2 + (3/2)) (1/2)) 2) (max (min ((-1/2) * x0 + x2 + (1/2)) (x1 + (-3/2))) (min (max ((-1/2) * x0 + x2 + (1/2)) (x1 + (-3/2))) ((1/2) * x0 + (5/2))))

def StatementProg (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ x0 x1 x2 : ℝ, (-2) ≤ x0 → x0 ≤ 2 → (-4) ≤ x1 → x1 ≤ 2 → (-8) ≤ x2 → x2 ≤ 2 →
    f x0 x1 x2 = spec x0 x1 x2

end Lane4.Case
