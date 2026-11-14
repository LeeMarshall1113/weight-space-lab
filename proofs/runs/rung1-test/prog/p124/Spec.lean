namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  max (max ((-2) * x0 + 1) 0) (x0 + 3 * x1)

def StatementProg (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x0 x1 : ℝ, (-4) ≤ x0 → x0 ≤ 8 → (-4) ≤ x1 → x1 ≤ 1 →
    f x0 x1 = spec x0 x1

end Lane4.Case
