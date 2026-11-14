namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  |min (max (x0 + (5/2)) ((-1) * x0 + (-1/2))) (2 * x1 + 3)|

def StatementRobust (N : Lane4.Net) : Prop :=
  ∀ (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ), Lane4.Within (1/1000) dW db →
    ∀ x0 x1 : ℝ, (-8) ≤ x0 → x0 ≤ 1 → (-4) ≤ x1 → x1 ≤ 8 →
      ∃ y : ℝ, N.evalP dW db [x0, x1] = [y] ∧ |y - spec x0 x1| ≤ (19/50)

end Lane4.Case
