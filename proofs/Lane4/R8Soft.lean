/-
Lane 4, rung 8: the exact softmax average, shared by kit cases kb and kd. Written by the lane.
No theorems.
-/
import Lane4.RSoftKit

namespace Lane4.RSoft

/-- The exact softmax average: real exponentials of the given scores, no rounding. -/
noncomputable def eavg (c : List ℕ) (s f : ℕ → ℝ) : ℝ :=
  (c.map (fun k => Real.exp (s k) * f k)).sum / (c.map (fun k => Real.exp (s k))).sum

end Lane4.RSoft
