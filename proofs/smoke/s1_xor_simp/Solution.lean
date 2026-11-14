namespace Lane4.Case
def net : Lane4.Net :=
  { hidden := [{ W := [[1, 1], [1, 1]], b := [0, -1] }],
    out := { W := [[1, -2]], b := [0] } }
theorem net_correct : Statement net := by
  intro b0 b1
  cases b0 <;> cases b1 <;> simp [net, Lane4.Net.eval, Lane4.Layer.apply, Lane4.dot, Lane4.relu, spec, bit] <;> norm_num
end Lane4.Case
