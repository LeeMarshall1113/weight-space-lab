namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  max (min (2 * x1 + (-5/2)) ((-1) * x0 + (-2) * x1 + (-1/2))) (min (max (2 * x1 + (-5/2)) ((-1) * x0 + (-2) * x1 + (-1/2))) (max (min ((-1) * x1 + (-1)) ((1/2) * x0 + (1/2) * x1 + 1)) (min (max ((-1) * x1 + (-1)) ((1/2) * x0 + (1/2) * x1 + 1)) ((-1/2) * x0 + (-3)))))

def StatementRobust (N : Lane4.Net) : Prop :=
  ∀ (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ), Lane4.Within (1/1000) dW db →
    ∀ x0 x1 : ℝ, (-8) ≤ x0 → x0 ≤ 1 → (-2) ≤ x1 → x1 ≤ 4 →
      ∃ y : ℝ, N.evalP dW db [x0, x1] = [y] ∧ |y - spec x0 x1| ≤ (3/10)

end Lane4.Case
