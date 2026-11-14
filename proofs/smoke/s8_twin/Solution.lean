namespace Lane4.Case
open Lane4
theorem twin_correct : StatementTwin := by
  intro x0 h0 h1
  refine ⟨_, rfl, ?_⟩
  simp only [twin, Net.eval, Layer.apply, dot, spec, relu, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil]
  push_cast
  rw [abs_le]
  rcases le_total x0 0 with h | h
  · rw [abs_of_nonpos h, max_eq_right (by linarith), max_eq_left (by linarith)]
    constructor <;> linarith
  · rw [abs_of_nonneg h, max_eq_left (by linarith), max_eq_right (by linarith)]
    constructor <;> linarith
end Lane4.Case
