namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  min (max (min (max ((-1) * x1 + (3/2)) (-3)) 1) (x0 + (-2) * x1 + (-5/2))) (x0 + (-3))

def StatementProg (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x0 x1 : ℝ, (-4) ≤ x0 → x0 ≤ 1 → (-8) ≤ x1 → x1 ≤ 8 →
    f x0 x1 = spec x0 x1

end Lane4.Case
