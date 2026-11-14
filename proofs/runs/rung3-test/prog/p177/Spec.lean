namespace Lane4.Case

noncomputable def spec (x0 x1 x2 : ℝ) : ℝ :=
  max (min (min ((1/2) * x2 + (1/2)) ((1/2) * x0 + (-1) * x2 + 1)) (|max ((1/2) * x0 + 2 * x1 + (-1)) ((-1/2) * x2 + (-5/2))|)) (min (max (min ((1/2) * x2 + (1/2)) ((1/2) * x0 + (-1) * x2 + 1)) (|max ((1/2) * x0 + 2 * x1 + (-1)) ((-1/2) * x2 + (-5/2))|)) ((-1) * x2 + (-1/2)))

def StatementProg (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ x0 x1 x2 : ℝ, (-8) ≤ x0 → x0 ≤ 4 → (-2) ≤ x1 → x1 ≤ 2 → (-2) ≤ x2 → x2 ≤ 4 →
    f x0 x1 x2 = spec x0 x1 x2

end Lane4.Case
