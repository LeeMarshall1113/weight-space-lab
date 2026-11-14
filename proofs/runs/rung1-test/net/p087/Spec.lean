namespace Lane4.Case

noncomputable def spec (x0 x1 x2 : ℝ) : ℝ :=
  max (min (min (3 * x1) ((-2) * x2 + (-1/2))) (x0 + (3/2))) (min (max (min (3 * x1) ((-2) * x2 + (-1/2))) (x0 + (3/2))) ((-1/2) * x0 + (-5/2)))

def Statement (N : Lane4.Net) : Prop :=
  ∀ x0 x1 x2 : ℝ, (-2) ≤ x0 → x0 ≤ 4 → (-1) ≤ x1 → x1 ≤ 2 → (-8) ≤ x2 → x2 ≤ 4 →
    N.eval [x0, x1, x2] = [spec x0 x1 x2]

end Lane4.Case
