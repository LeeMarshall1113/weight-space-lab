/-
WORKED EXAMPLE on an unrelated toy spec. It was checked by the same checker and passed.
It shows the three parts the checker joins: the lane's Spec.lean, a Solution.lean, and
(not shown) Final.lean. Only the part between the SOLUTION markers is what you write.
Proof pattern: unfold, `split_ifs`, then rewrite each max/min/abs with the hypothesis of
that branch (`max_eq_left`, `min_eq_right`, `abs_of_nonneg`, ...) and finish with `linarith`.
-/

-- ===== Spec.lean (given) =====
namespace Lane4.Case
noncomputable def spec (x0 x1 : ℝ) : ℝ := max x0 x1
def StatementProg (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x0 x1 : ℝ, -4 ≤ x0 → x0 ≤ 4 → -4 ≤ x1 → x1 ≤ 4 → f x0 x1 = spec x0 x1
end Lane4.Case

-- ===== Solution.lean (what a solution looks like) =====
namespace Lane4.Case
noncomputable def prog (x0 x1 : ℝ) : ℝ := if x0 ≤ x1 then x1 else x0
-- PROOF
theorem prog_correct : StatementProg prog := by
  intro x0 x1 _ _ _ _
  unfold prog spec
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_lt (not_le.mp h))).symm
end Lane4.Case

-- ===== end of Solution.lean =====
