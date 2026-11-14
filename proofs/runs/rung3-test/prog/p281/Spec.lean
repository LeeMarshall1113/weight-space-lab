namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  min ((-2) * (max ((1/2) * x0 + (-3/2)) 0) + (-2) * (|max (min ((-1) * x1 + (-3/2)) ((-1/2) * x1 + (3/2))) (min (max ((-1) * x1 + (-3/2)) ((-1/2) * x1 + (3/2))) ((-1) * x0 + 3 * x1 + 2))|)) ((-1) * x0 + (1/2))

def StatementProg (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x0 x1 : ℝ, (-8) ≤ x0 → x0 ≤ 8 → (-4) ≤ x1 → x1 ≤ 1 →
    f x0 x1 = spec x0 x1

end Lane4.Case
