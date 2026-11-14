namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  max (min (max (x0 + (-1) * x1 + (1/2)) (2 * x1 + (-3))) (3 * x1 + 2)) ((-1/2) * x1 + 1)

def StatementRobust (N : Lane4.Net) : Prop :=
  ∀ (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ), Lane4.Within (1/1000) dW db →
    ∀ x0 x1 : ℝ, (-1) ≤ x0 → x0 ≤ 4 → (-8) ≤ x1 → x1 ≤ 2 →
      ∃ y : ℝ, N.evalP dW db [x0, x1] = [y] ∧ |y - spec x0 x1| ≤ (6/25)

end Lane4.Case
