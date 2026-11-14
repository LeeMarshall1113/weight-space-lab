namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  min (max (min (max ((-1) * x1 + (3/2)) (-3)) 1) (x0 + (-2) * x1 + (-5/2))) (x0 + (-3))

def StatementRobust (N : Lane4.Net) : Prop :=
  ∀ (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ), Lane4.Within (1/1000) dW db →
    ∀ x0 x1 : ℝ, (-4) ≤ x0 → x0 ≤ 1 → (-8) ≤ x1 → x1 ≤ 8 →
      ∃ y : ℝ, N.evalP dW db [x0, x1] = [y] ∧ |y - spec x0 x1| ≤ (1/4)

end Lane4.Case
