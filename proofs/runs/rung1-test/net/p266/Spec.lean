namespace Lane4.Case

noncomputable def spec (x0 x1 x2 : ℝ) : ℝ :=
  max (max (min ((-2) * x0 + (1/2) * x2 + (-3/2)) ((-1/2) * x2 + (-1))) (min (max ((-2) * x0 + (1/2) * x2 + (-3/2)) ((-1/2) * x2 + (-1))) (max (2 * x0 + (-1) * x1 + 2) ((-1) * x0 + (-3))))) 0

def Statement (N : Lane4.Net) : Prop :=
  ∀ x0 x1 x2 : ℝ, (-4) ≤ x0 → x0 ≤ 8 → (-8) ≤ x1 → x1 ≤ 1 → (-4) ≤ x2 → x2 ≤ 2 →
    N.eval [x0, x1, x2] = [spec x0 x1 x2]

end Lane4.Case
