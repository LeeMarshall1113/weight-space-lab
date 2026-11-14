namespace Lane4.Case

noncomputable def spec (x0 x1 x2 : ℝ) : ℝ :=
  max (min (min ((1/2) * x2 + (1/2)) ((1/2) * x0 + (-1) * x2 + 1)) (|max ((1/2) * x0 + 2 * x1 + (-1)) ((-1/2) * x2 + (-5/2))|)) (min (max (min ((1/2) * x2 + (1/2)) ((1/2) * x0 + (-1) * x2 + 1)) (|max ((1/2) * x0 + 2 * x1 + (-1)) ((-1/2) * x2 + (-5/2))|)) ((-1) * x2 + (-1/2)))

def StatementRobust (N : Lane4.Net) : Prop :=
  ∀ (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ), Lane4.Within (1/1000) dW db →
    ∀ x0 x1 x2 : ℝ, (-8) ≤ x0 → x0 ≤ 4 → (-2) ≤ x1 → x1 ≤ 2 → (-2) ≤ x2 → x2 ≤ 4 →
      ∃ y : ℝ, N.evalP dW db [x0, x1, x2] = [y] ∧ |y - spec x0 x1 x2| ≤ (3/10)

end Lane4.Case
