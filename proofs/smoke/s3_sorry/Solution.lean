namespace Lane4.Case
def net : Lane4.Net :=
  { hidden := [{ W := [[1, 1], [1, 1]], b := [0, -1] }],
    out := { W := [[1, -2]], b := [0] } }
theorem net_correct : Statement net := by
  sorry
end Lane4.Case
