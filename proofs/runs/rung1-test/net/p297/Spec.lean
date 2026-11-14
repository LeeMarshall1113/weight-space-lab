namespace Lane4.Case

noncomputable def spec (x0 : ℝ) : ℝ :=
  |min (3 * x0 + 2) ((-1) * x0 + (1/2))|

def Statement (N : Lane4.Net) : Prop :=
  ∀ x0 : ℝ, (-1) ≤ x0 → x0 ≤ 4 →
    N.eval [x0] = [spec x0]

end Lane4.Case
