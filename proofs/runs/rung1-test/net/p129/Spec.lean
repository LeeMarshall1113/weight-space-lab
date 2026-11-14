namespace Lane4.Case

noncomputable def spec (x0 x1 x2 : ℝ) : ℝ :=
  2 * (max (x0 + (1/2) * x1 + (-3)) (min ((-1/2) * x0 + (-2) * x1 + (3/2)) ((-1) * x1 + (-1/2) * x2 + (-1/2)))) + 2 * (max ((-1) * x0 + (-3)) (min (max ((-1) * x2 + (-1)) (-3)) (1/2)))

def Statement (N : Lane4.Net) : Prop :=
  ∀ x0 x1 x2 : ℝ, (-2) ≤ x0 → x0 ≤ 1 → (-2) ≤ x1 → x1 ≤ 4 → (-4) ≤ x2 → x2 ≤ 4 →
    N.eval [x0, x1, x2] = [spec x0 x1 x2]

end Lane4.Case
