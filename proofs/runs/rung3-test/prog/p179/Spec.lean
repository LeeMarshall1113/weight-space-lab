namespace Lane4.Case

noncomputable def spec (x0 x1 x2 : ℝ) : ℝ :=
  max (min (max (x0 + (-1) * x2 + (-5/2)) 0) (2 * x1 + (-5/2))) (min (max (max (x0 + (-1) * x2 + (-5/2)) 0) (2 * x1 + (-5/2))) (|x0 + (-1/2) * x1 + 1|))

def StatementProg (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ x0 x1 x2 : ℝ, (-2) ≤ x0 → x0 ≤ 1 → (-2) ≤ x1 → x1 ≤ 8 → (-4) ≤ x2 → x2 ≤ 4 →
    f x0 x1 x2 = spec x0 x1 x2

end Lane4.Case
