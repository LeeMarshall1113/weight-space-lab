namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  (-1) * (max (max ((-1) * x0 + (1/2)) 0) (min (max ((-2) * x1 + (5/2)) (-3/2)) (3/2))) + (1/2) * (min (max (3 * x1 + 1) (-3/2)) (-1/2))

def StatementProg (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x0 x1 : ℝ, (-8) ≤ x0 → x0 ≤ 2 → (-2) ≤ x1 → x1 ≤ 8 →
    f x0 x1 = spec x0 x1

end Lane4.Case
