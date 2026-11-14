/-
WORKED EXAMPLE on an unrelated toy spec. It was checked by the same checker and passed.
It shows the three parts the checker joins: the lane's Spec.lean, a Solution.lean, and
(not shown) Final.lean. Only the part between the SOLUTION markers is what you write.
Note: `decide` does NOT work on these goals (rational arithmetic does not reduce in the
kernel). Split on the bits and let `simp` unfold the network, then `norm_num`.
-/

-- ===== Spec.lean (given) =====
namespace Lane4.Case
def bit (b : Bool) : ℚ := if b then 1 else 0
def spec (b0 b1 : Bool) : ℚ := if xor b0 b1 then 1 else 0
def Statement (N : Lane4.Net) : Prop :=
  ∀ b0 b1 : Bool, N.eval [bit b0, bit b1] = [spec b0 b1]
end Lane4.Case

-- ===== Solution.lean (what a solution looks like) =====
namespace Lane4.Case
def net : Lane4.Net :=
  { hidden := [{ W := [[1, 1], [1, 1]], b := [0, -1] }],
    out := { W := [[1, -2]], b := [0] } }
theorem net_correct : Statement net := by
  intro b0 b1
  cases b0 <;> cases b1 <;> simp [net, Lane4.Net.eval, Lane4.Layer.apply, Lane4.dot, Lane4.relu, spec, bit] <;> norm_num
end Lane4.Case

-- ===== end of Solution.lean =====
