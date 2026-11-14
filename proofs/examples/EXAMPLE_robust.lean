/-
WORKED EXAMPLE on an unrelated toy spec. It was checked by the same checker and passed.
It shows the three parts the checker joins: the lane's Spec.lean, a Solution.lean, and
(not shown) Final.lean. Only the part between the SOLUTION markers is what you write.

The network is the exact one for `max x0 x1`:  relu x0 - relu (-x0) + relu (x1 - x0).
The theorem is about EVERY network whose weights and biases are within 1/1000 of it,
including the weights written as 0 (so each hidden unit sees a little of every input).

Proof pattern used here:
 1. `key`: a lemma about plain real numbers. Every perturbation is a named variable
    (a.. for hidden weights, c.. for hidden biases, o.. for output weights, oc for the
    output bias). Steps: (a) each perturbed pre-activation is within e of the exact one,
    because |d * x| ≤ τ * bound (`pert_abs_mul`); (b) `relu_pert` carries that through
    ReLU; (c) the exact network equals the spec (the rung-1 style identity); (d) the
    output weights' perturbations cost τ * (bound on the hidden value); (e) `linarith`.
 2. `net_robust`: give the output value explicitly, show the framework computes it
    (`simp` with the framework definitions, then `ring_nf` if needed), and apply `key`.
Bounds here are loose on purpose; 1/1000 is small, so crude bounds usually suffice.
For deeper networks do the same layer by layer: the error of one layer becomes the
`e` of the next (see `pert_mul` in Robust.lean).
-/

-- ===== Spec.lean (given) =====
namespace Lane4.Case
noncomputable def spec (x0 x1 : ℝ) : ℝ := max x0 x1
def StatementRobust (N : Lane4.Net) : Prop :=
  ∀ (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ), Lane4.Within (1/1000) dW db →
    ∀ x0 x1 : ℝ, -4 ≤ x0 → x0 ≤ 4 → -4 ≤ x1 → x1 ≤ 4 →
      ∃ y : ℝ, N.evalP dW db [x0, x1] = [y] ∧ |y - spec x0 x1| ≤ (2/5)
end Lane4.Case

-- ===== Solution.lean (what a solution looks like) =====
namespace Lane4.Case
open Lane4
def net : Net :=
  { hidden := [{ W := [[1, 0], [-1, 0], [-1, 1]], b := [0, 0, 0] }],
    out := { W := [[1, -1, 1]], b := [0] } }

theorem key {a00 a01 c0 a10 a11 c1 a20 a21 c2 o0 o1 o2 oc x0 x1 : ℝ}
    (h00 : |a00| ≤ 1/1000) (h01 : |a01| ≤ 1/1000) (hc0 : |c0| ≤ 1/1000)
    (h10 : |a10| ≤ 1/1000) (h11 : |a11| ≤ 1/1000) (hc1 : |c1| ≤ 1/1000)
    (h20 : |a20| ≤ 1/1000) (h21 : |a21| ≤ 1/1000) (hc2 : |c2| ≤ 1/1000)
    (ho0 : |o0| ≤ 1/1000) (ho1 : |o1| ≤ 1/1000) (ho2 : |o2| ≤ 1/1000) (hoc : |oc| ≤ 1/1000)
    (l0 : -4 ≤ x0) (u0 : x0 ≤ 4) (l1 : -4 ≤ x1) (u1 : x1 ≤ 4) :
    |(1 + o0) * relu ((1 + a00) * x0 + a01 * x1 + c0)
        + (-1 + o1) * relu ((-1 + a10) * x0 + a11 * x1 + c1)
        + (1 + o2) * relu ((-1 + a20) * x0 + (1 + a21) * x1 + c2) + oc - max x0 x1| ≤ 2/5 := by
  have bx0 : |x0| ≤ 4 := abs_le.mpr ⟨l0, u0⟩
  have bx1 : |x1| ≤ 4 := abs_le.mpr ⟨l1, u1⟩
  -- (a) pre-activations: perturbed minus exact is  d*x0 + d'*x1 + c
  have e0 : |((1 + a00) * x0 + a01 * x1 + c0) - x0| ≤ 9/1000 := by
    have h : ((1 + a00) * x0 + a01 * x1 + c0) - x0 = a00 * x0 + a01 * x1 + c0 := by ring
    rw [h]
    exact le_trans (abs_add3_le (pert_abs_mul h00 bx0) (pert_abs_mul h01 bx1) hc0) (by norm_num)
  have e1 : |((-1 + a10) * x0 + a11 * x1 + c1) - (-x0)| ≤ 9/1000 := by
    have h : ((-1 + a10) * x0 + a11 * x1 + c1) - (-x0) = a10 * x0 + a11 * x1 + c1 := by ring
    rw [h]
    exact le_trans (abs_add3_le (pert_abs_mul h10 bx0) (pert_abs_mul h11 bx1) hc1) (by norm_num)
  have e2 : |((-1 + a20) * x0 + (1 + a21) * x1 + c2) - (x1 - x0)| ≤ 9/1000 := by
    have h : ((-1 + a20) * x0 + (1 + a21) * x1 + c2) - (x1 - x0) = a20 * x0 + a21 * x1 + c2 := by ring
    rw [h]
    exact le_trans (abs_add3_le (pert_abs_mul h20 bx0) (pert_abs_mul h21 bx1) hc2) (by norm_num)
  -- (b) through ReLU
  have r0 := abs_le.mp (relu_pert e0)
  have r1 := abs_le.mp (relu_pert e1)
  have r2 := abs_le.mp (relu_pert e2)
  -- (c) the exact network is the spec; bounds on the exact hidden values
  have id1 := relu_sub_relu_neg x0
  have id2 := add_relu_sub x0 x1
  have s0 : relu x0 ≤ 4 := relu_le_of_le u0 (by norm_num)
  have s1 : relu (-x0) ≤ 4 := relu_le_of_le (by linarith) (by norm_num)
  have s2 : relu (x1 - x0) ≤ 8 := relu_le_of_le (by linarith) (by norm_num)
  have n0 := relu_nonneg' ((1 + a00) * x0 + a01 * x1 + c0)
  have n1 := relu_nonneg' ((-1 + a10) * x0 + a11 * x1 + c1)
  have n2 := relu_nonneg' ((-1 + a20) * x0 + (1 + a21) * x1 + c2)
  generalize relu ((1 + a00) * x0 + a01 * x1 + c0) = R0 at *
  generalize relu ((-1 + a10) * x0 + a11 * x1 + c1) = R1 at *
  generalize relu ((-1 + a20) * x0 + (1 + a21) * x1 + c2) = R2 at *
  -- (d) output-weight perturbations
  have q0 := abs_le.mp (pert_abs_mul ho0 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R0| ≤ 5))
  have q1 := abs_le.mp (pert_abs_mul ho1 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R1| ≤ 5))
  have q2 := abs_le.mp (pert_abs_mul ho2 (abs_le.mpr ⟨by linarith, by linarith⟩ : |R2| ≤ 9))
  have qc := abs_le.mp hoc
  -- (e) add up
  have h : (1 + o0) * R0 + (-1 + o1) * R1 + (1 + o2) * R2 + oc - max x0 x1
      = (R0 - relu x0) - (R1 - relu (-x0)) + (R2 - relu (x1 - x0))
        + o0 * R0 + o1 * R1 + o2 * R2 + oc := by
    rw [← id2]; linear_combination id1
  rw [h, abs_le]
  constructor <;> linarith [r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, q0.1, q0.2, q1.1, q1.2, q2.1, q2.2, qc.1, qc.2]

theorem net_robust : StatementRobust net := by
  intro dW db hW x0 x1 l0 u0 l1 u1
  obtain ⟨hw, hb⟩ := hW
  refine ⟨(1 + dW 1 0 0) * relu ((1 + dW 0 0 0) * x0 + dW 0 0 1 * x1 + db 0 0)
        + (-1 + dW 1 0 1) * relu ((-1 + dW 0 1 0) * x0 + dW 0 1 1 * x1 + db 0 1)
        + (1 + dW 1 0 2) * relu ((-1 + dW 0 2 0) * x0 + (1 + dW 0 2 1) * x1 + db 0 2) + db 1 0, ?_, ?_⟩
  · simp [net, Net.evalP, hiddenP, rowsP, dotP]
    try ring_nf
  · exact key (hw 0 0 0) (hw 0 0 1) (hb 0 0) (hw 0 1 0) (hw 0 1 1) (hb 0 1)
      (hw 0 2 0) (hw 0 2 1) (hb 0 2) (hw 1 0 0) (hw 1 0 1) (hw 1 0 2) (hb 1 0) l0 u0 l1 u1
end Lane4.Case

-- ===== end of Solution.lean =====
