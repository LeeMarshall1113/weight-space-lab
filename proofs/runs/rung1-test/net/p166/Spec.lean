namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  min (max (max (min (2 * x1) (min (max (3 * x0 + 2) (-5/2)) (5/2))) (min (max (2 * x1) (min (max (3 * x0 + 2) (-5/2)) (5/2))) (min (max (x0 + x1 + 2) (-1/2)) (1/2)))) (-1/2)) (3/2)

def Statement (N : Lane4.Net) : Prop :=
  ∀ x0 x1 : ℝ, (-8) ≤ x0 → x0 ≤ 2 → (-1) ≤ x1 → x1 ≤ 8 →
    N.eval [x0, x1] = [spec x0 x1]

end Lane4.Case
