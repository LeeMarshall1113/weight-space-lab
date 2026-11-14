namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  1 * (max (x1 + 1) 0) + (1/2) * (max (min ((-1) * x0 + 2 * x1 + (5/2)) (x1 + 1)) ((-2) * x0 + (-1/2) * x1 + (-1)))

def Statement (N : Lane4.Net) : Prop :=
  ∀ x0 x1 : ℝ, (-4) ≤ x0 → x0 ≤ 1 → (-4) ≤ x1 → x1 ≤ 2 →
    N.eval [x0, x1] = [spec x0 x1]

end Lane4.Case
