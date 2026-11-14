/-
WORKED EXAMPLE on an unrelated toy spec. It was checked by the same checker and passed.
It shows the three parts the checker joins: the lane's Spec.lean, a Solution.lean, and
(not shown) Final.lean. Only the part between the SOLUTION markers is what you write.
Proof pattern: state the ReLU identities you need as `have`s (lemma kit in Basic.lean),
unfold the network with `simp only [...]`, `push_cast`, then close with linear arithmetic.
For bigger specs, case splits with `rcases le_total a b` plus `max_eq_left`/`max_eq_right`,
`abs_of_nonneg`/`abs_of_nonpos` also work.
-/

-- ===== Spec.lean (given) =====
namespace Lane4.Case
noncomputable def spec (x0 x1 : ℝ) : ℝ := max x0 x1
def Statement (N : Lane4.Net) : Prop :=
  ∀ x0 x1 : ℝ, -4 ≤ x0 → x0 ≤ 4 → -4 ≤ x1 → x1 ≤ 4 →
    N.eval [x0, x1] = [spec x0 x1]
end Lane4.Case

-- ===== Solution.lean (what a solution looks like) =====
namespace Lane4.Case
open Lane4
def net : Net :=
  { hidden := [{ W := [[1, 0], [-1, 0], [-1, 1]], b := [0, 0, 0] }],
    out := { W := [[1, -1, 1]], b := [0] } }
theorem net_correct : Statement net := by
  intro x0 x1 _ _ _ _
  have h1 := relu_sub_relu_neg x0
  have h2 := add_relu_sub x0 x1
  simp only [net, Net.eval, Layer.apply, dot, spec, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true]
  push_cast
  ring_nf
  ring_nf at h1 h2
  linarith
end Lane4.Case

-- ===== end of Solution.lean =====
