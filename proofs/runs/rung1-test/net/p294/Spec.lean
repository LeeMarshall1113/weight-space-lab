namespace Lane4.Case

noncomputable def spec (x0 : ℝ) : ℝ :=
  max (min ((1/2) * x0 + (5/2)) ((-1) * x0 + (5/2))) (min (max ((1/2) * x0 + (5/2)) ((-1) * x0 + (5/2))) (max ((-2) * x0) ((1/2) * x0 + 1)))

def Statement (N : Lane4.Net) : Prop :=
  ∀ x0 : ℝ, (-8) ≤ x0 → x0 ≤ 8 →
    N.eval [x0] = [spec x0]

end Lane4.Case
