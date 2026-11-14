namespace Lane4.Case
noncomputable def spec (x0 x1 : ℝ) : ℝ := max x0 x1
def Statement (N : Lane4.Net) : Prop :=
  ∀ x0 x1 : ℝ, -4 ≤ x0 → x0 ≤ 4 → -4 ≤ x1 → x1 ≤ 4 →
    N.eval [x0, x1] = [spec x0 x1]
end Lane4.Case
