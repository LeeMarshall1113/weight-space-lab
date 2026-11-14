namespace Lane4.Case

noncomputable def spec (x0 x1 x2 : ℝ) : ℝ :=
  (-1) * (max (x1 + x2 + 3) ((1/2) * x0 + 1)) + (1/2) * (max ((-2) * x0 + (-1/2) * x2 + 1) 0)

def StatementRobust (N : Lane4.Net) : Prop :=
  ∀ (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ), Lane4.Within (1/1000) dW db →
    ∀ x0 x1 x2 : ℝ, (-2) ≤ x0 → x0 ≤ 4 → (-2) ≤ x1 → x1 ≤ 4 → (-2) ≤ x2 → x2 ≤ 1 →
      ∃ y : ℝ, N.evalP dW db [x0, x1, x2] = [y] ∧ |y - spec x0 x1 x2| ≤ (11/20)

end Lane4.Case
