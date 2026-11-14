namespace Lane4.Case

noncomputable def spec (x0 x1 x2 : ℝ) : ℝ :=
  min ((-2) * (max (x1 + (-1)) (3 * x0 + x1 + (-5/2))) + (-1) * (min (x1 + (-2)) (2 * x0 + 2))) (min ((1/2) * x2 + 3) ((-1/2) * x0 + x1 + 2))

def StatementRobust (N : Lane4.Net) : Prop :=
  ∀ (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ), Lane4.Within (1/1000) dW db →
    ∀ x0 x1 x2 : ℝ, (-4) ≤ x0 → x0 ≤ 2 → (-1) ≤ x1 → x1 ≤ 2 → (-2) ≤ x2 → x2 ≤ 2 →
      ∃ y : ℝ, N.evalP dW db [x0, x1, x2] = [y] ∧ |y - spec x0 x1 x2| ≤ (3/4)

end Lane4.Case
