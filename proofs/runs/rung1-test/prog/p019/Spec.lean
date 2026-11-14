namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  max (max (2 * x0 + (-1/2) * x1 + (-1)) (min (max ((-1) * x0 + (-2)) (-1)) 0)) (max (x0 + (-1/2) * x1 + (3/2)) ((1/2) * x1 + 2))

def StatementProg (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x0 x1 : ℝ, (-4) ≤ x0 → x0 ≤ 8 → (-1) ≤ x1 → x1 ≤ 4 →
    f x0 x1 = spec x0 x1

end Lane4.Case
