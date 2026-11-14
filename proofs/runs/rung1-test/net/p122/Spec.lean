namespace Lane4.Case

noncomputable def spec (x0 x1 x2 : ℝ) : ℝ :=
  max (min (|3 * x1 + 1|) (x0 + (1/2) * x2 + 2)) (min (max (|3 * x1 + 1|) (x0 + (1/2) * x2 + 2)) (3 * x1 + (1/2)))

def Statement (N : Lane4.Net) : Prop :=
  ∀ x0 x1 x2 : ℝ, (-4) ≤ x0 → x0 ≤ 1 → (-2) ≤ x1 → x1 ≤ 8 → (-2) ≤ x2 → x2 ≤ 8 →
    N.eval [x0, x1, x2] = [spec x0 x1 x2]

end Lane4.Case
