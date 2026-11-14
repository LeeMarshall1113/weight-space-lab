namespace Lane4.Case

noncomputable def spec (x0 x1 x2 : ℝ) : ℝ :=
  (-1) * (max (x1 + x2 + 3) ((1/2) * x0 + 1)) + (1/2) * (max ((-2) * x0 + (-1/2) * x2 + 1) 0)

def StatementProg (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ x0 x1 x2 : ℝ, (-2) ≤ x0 → x0 ≤ 4 → (-2) ≤ x1 → x1 ≤ 4 → (-2) ≤ x2 → x2 ≤ 1 →
    f x0 x1 x2 = spec x0 x1 x2

end Lane4.Case
