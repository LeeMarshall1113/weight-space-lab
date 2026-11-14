namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  max (max (max (min (2 * x0 + x1 + (-3/2)) ((-1) * x0 + (1/2))) (min (max (2 * x0 + x1 + (-3/2)) ((-1) * x0 + (1/2))) (3 * x0 + (-5/2)))) 0) (2 * x0 + (-3))

def StatementProg (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x0 x1 : ℝ, (-4) ≤ x0 → x0 ≤ 4 → (-2) ≤ x1 → x1 ≤ 2 →
    f x0 x1 = spec x0 x1

end Lane4.Case
