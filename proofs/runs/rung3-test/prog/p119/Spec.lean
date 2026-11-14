namespace Lane4.Case

noncomputable def spec (x0 : ℝ) : ℝ :=
  max (|(-1) * x0 + (-1)|) (max (min ((-2) * x0) ((-2) * x0 + (-3/2))) (min (max ((-2) * x0) ((-2) * x0 + (-3/2))) ((-1/2) * x0 + (-1))))

def StatementProg (f : ℝ → ℝ) : Prop :=
  ∀ x0 : ℝ, (-8) ≤ x0 → x0 ≤ 2 →
    f x0 = spec x0

end Lane4.Case
