namespace Lane4.Case

noncomputable def spec (x0 x1 : ℝ) : ℝ :=
  min ((-2) * (max ((1/2) * x0 + (-3/2)) 0) + (-2) * (|max (min ((-1) * x1 + (-3/2)) ((-1/2) * x1 + (3/2))) (min (max ((-1) * x1 + (-3/2)) ((-1/2) * x1 + (3/2))) ((-1) * x0 + 3 * x1 + 2))|)) ((-1) * x0 + (1/2))

def StatementRobust (N : Lane4.Net) : Prop :=
  ∀ (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ), Lane4.Within (1/1000) dW db →
    ∀ x0 x1 : ℝ, (-8) ≤ x0 → x0 ≤ 8 → (-4) ≤ x1 → x1 ≤ 1 →
      ∃ y : ℝ, N.evalP dW db [x0, x1] = [y] ∧ |y - spec x0 x1| ≤ (1/2)

end Lane4.Case
