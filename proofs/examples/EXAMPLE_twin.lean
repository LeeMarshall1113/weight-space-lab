/-
WORKED EXAMPLE on an unrelated toy spec. It was checked by the same checker and passed.
It shows the three parts the checker joins: the lane's Spec.lean, a Solution.lean, and
(not shown) Final.lean. Only the part between the SOLUTION markers is what you write.
Proof pattern: give the output as the witness with `rfl`, unfold, `push_cast`, split on the
sign of each ReLU input, and bound each piece with `linarith`/`nlinarith`.
-/

-- ===== Spec.lean (given) =====
namespace Lane4.Case
noncomputable def spec (x0 : ℝ) : ℝ := |x0|
def twin : Lane4.Net :=
  { hidden := [{ W := [[101/100], [-99/100]], b := [0, 0] }],
    out := { W := [[1, 1]], b := [1/200] } }
def StatementTwin : Prop :=
  ∀ x0 : ℝ, (-1) ≤ x0 → x0 ≤ 1 →
    ∃ y : ℝ, twin.eval [x0] = [y] ∧ |y - spec x0| ≤ (1/20)
end Lane4.Case

-- ===== Solution.lean (what a solution looks like) =====
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

-- ===== end of Solution.lean =====
