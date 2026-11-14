namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  min (max (min ((-1) * x0 + 1) ((-1) * x0 + (1/2))) (min (max ((-1) * x0 + 1) ((-1) * x0 + (1/2))) (2 * x0 + (5/2)))) ((1/2) * x1 + (-2))

def StatementRobust (N : Lane4.Net) : Prop :=
  ∀ (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ), Lane4.Within (1/1000) dW db →
    ∀ x0 x1 : ℝ, (-2) ≤ x0 → x0 ≤ 4 → (-8) ≤ x1 → x1 ≤ 8 →
      ∃ y : ℝ, N.evalP dW db [x0, x1] = [y] ∧ |y - spec x0 x1| ≤ (2/5)

end Lane4.Case
