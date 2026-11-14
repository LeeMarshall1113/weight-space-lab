namespace Lane4.Case

noncomputable def spec (x0 x1 x2 : ℝ) : ℝ :=
  max (min (3 * x0 + (-1) * x2 + 1) (3 * x0)) (min (max (3 * x0 + (-1) * x2 + 1) (3 * x0)) (min (max (3 * x1 + (-1/2) * x2 + (5/2)) (-3/2)) 1))

def Statement (N : Lane4.Net) : Prop :=
  ∀ x0 x1 x2 : ℝ, (-2) ≤ x0 → x0 ≤ 4 → (-4) ≤ x1 → x1 ≤ 1 → (-2) ≤ x2 → x2 ≤ 2 →
    N.eval [x0, x1, x2] = [spec x0 x1 x2]

end Lane4.Case
