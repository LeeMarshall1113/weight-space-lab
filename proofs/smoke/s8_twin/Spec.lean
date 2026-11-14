namespace Lane4.Case
noncomputable def spec (x0 : ℝ) : ℝ := |x0|
def twin : Lane4.Net :=
  { hidden := [{ W := [[101/100], [-99/100]], b := [0, 0] }],
    out := { W := [[1, 1]], b := [1/200] } }
def StatementTwin : Prop :=
  ∀ x0 : ℝ, (-1) ≤ x0 → x0 ≤ 1 →
    ∃ y : ℝ, twin.eval [x0] = [y] ∧ |y - spec x0| ≤ (1/20)
end Lane4.Case
