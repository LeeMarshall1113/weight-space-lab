namespace Lane4.Case
open Lane4

def net : Net :=
  { hidden :=
      [{ W := [[1, 0], [-1, 1], [1, -1], [1, -1/2], [-1, 1/2]], b := [-2, 1/2, -1/2, 3/2, -3/2] },
       { W := [[-1, 1, -1, 0, 0], [1, 0, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
         b := [0, 0, 0, 0] }],
    out := { W := [[1, 1, 1, -1]], b := [0] } }

theorem spec_key (x0 x1 : ℝ) (h0 : (-4) ≤ x0) (h1 : x0 ≤ 8) (h2 : (-1) ≤ x1) (h3 : x1 ≤ 4) :
    spec x0 x1 = max (max (2 * x0 + (-1/2) * x1 + (-1)) (x0 + (-1/2) * x1 + (3/2)))
      ((1/2) * x1 + 2) := by
  unfold spec
  have hB : min (max ((-1) * x0 + (-2)) (-1)) (0:ℝ) ≤ 0 := min_le_right _ _
  have hD : (0:ℝ) < (1/2) * x1 + 2 := by linarith
  apply le_antisymm
  · apply max_le
    · apply max_le
      · exact le_trans (le_max_left _ _) (le_max_left _ _)
      · exact le_trans hB (le_trans hD.le (le_max_right _ _))
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  · apply max_le
    · apply max_le
      · exact le_trans (le_max_left _ _) (le_max_left _ _)
      · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem net_correct : Statement net := by
  intro x0 x1 h0 h1 h2 h3
  rw [spec_key x0 x1 h0 h1 h2 h3]
  have rr : ∀ a : ℝ, max (max a 0) 0 = max a 0 := by intro a; simp
  simp only [net, Net.eval, Layer.apply, dot, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true, relu]
  push_cast
  simp only [max_def]
  split_ifs <;> linarith
end Lane4.Case
