namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  |min (x0 + (-3)) ((1/2) * x1 + 2)|

def StatementRobust (N : Lane4.Net) : Prop :=
  ∀ (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ), Lane4.Within (1/1000) dW db →
    ∀ x0 x1 : ℝ, (-1) ≤ x0 → x0 ≤ 4 → (-4) ≤ x1 → x1 ≤ 1 →
      ∃ y : ℝ, N.evalP dW db [x0, x1] = [y] ∧ |y - spec x0 x1| ≤ (1/5)

end Lane4.Case
