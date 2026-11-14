namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  min ((1/2) * x0 + (1/2) * x1 + 1) (max (min (3 * x0 + (3/2)) ((-2) * x1 + (3/2))) (max (min (x1 + (-3/2)) (2 * x1 + (-5/2))) (min (max (x1 + (-3/2)) (2 * x1 + (-5/2))) ((-2) * x0 + 3 * x1))))

def Statement (N : Lane4.Net) : Prop :=
  ∀ x0 x1 : ℝ, (-8) ≤ x0 → x0 ≤ 1 → (-8) ≤ x1 → x1 ≤ 8 →
    N.eval [x0, x1] = [spec x0 x1]

end Lane4.Case
