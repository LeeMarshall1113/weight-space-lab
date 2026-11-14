namespace Lane4.Case

noncomputable def spec (x0 : ℝ) : ℝ :=
  max (min ((-1) * x0 + 2) (max (min ((-1) * x0) (x0 + (-5/2))) (min (max ((-1) * x0) (x0 + (-5/2))) ((1/2) * x0 + (1/2))))) (min (max ((-1) * x0 + 2) (max (min ((-1) * x0) (x0 + (-5/2))) (min (max ((-1) * x0) (x0 + (-5/2))) ((1/2) * x0 + (1/2))))) ((-2) * x0 + (-3/2)))

def StatementRobust (N : Lane4.Net) : Prop :=
  ∀ (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ), Lane4.Within (1/1000) dW db →
    ∀ x0 : ℝ, (-1) ≤ x0 → x0 ≤ 4 →
      ∃ y : ℝ, N.evalP dW db [x0] = [y] ∧ |y - spec x0| ≤ (1/5)

end Lane4.Case
