namespace Lane4.Case

noncomputable def spec (x0 x1 x2 : ℝ) : ℝ :=
  (-1) * (max (x1 + x2 + 3) ((1/2) * x0 + 1)) + (1/2) * (max ((-2) * x0 + (-1/2) * x2 + 1) 0)

def twin : Lane4.Net :=
  { hidden := [
      { W := [[-13/64, 13/32, 13/32], [811/1024, 0, 97/512], [251/1024, 1/1024, -877/1024], [-29/16, 0, -229/512]], b := [833/1024, -103/256, 1323/1024, 233/256] }],
    out := { W := [[-1259/512, -605/1024, -67/512, 829/1024]], b := [-547/512] } }

def StatementRobustTwin : Prop :=
  ∀ (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ), Lane4.Within (1/1000) dW db →
    ∀ x0 x1 x2 : ℝ, (-2) ≤ x0 → x0 ≤ 4 → (-2) ≤ x1 → x1 ≤ 4 → (-2) ≤ x2 → x2 ≤ 1 →
      ∃ y : ℝ, twin.evalP dW db [x0, x1, x2] = [y] ∧ |y - spec x0 x1 x2| ≤ (11/20)

end Lane4.Case
