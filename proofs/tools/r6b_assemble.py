"""Assemble the rung-6b corollary file for one proved membership case (PREREG_R6.md).

    python tools/r6b_assemble.py m05 1 2     -> runs/r6b/m05/_Corollary.lean
                                (case, a counted token s, an uncounted token o)

The file is: import Lane4.Seq; the case's Spec.lean; the proved collision bound
(runs/r6b/kColl2/Solution.lean, moved to namespace Lane4.CollProof so that no name
clashes with the membership proof); the case's proved Solution.lean; then the lane's
corollaries `radius` and `noBall`, written by the lane, and `#print axioms`.
Compile it with tools/lean_lease.sh.
"""
import os, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
read = lambda *p: open(os.path.join(HERE, *p), encoding="utf-8").read()
case, s, o = sys.argv[1], sys.argv[2], sys.argv[3]

coll = read("runs", "r6b", "kColl2", "Solution.lean").replace("namespace Lane4.Case", "namespace Lane4.CollProof").replace(
    "end Lane4.Case", "end Lane4.CollProof")
COR = """
namespace Lane4Final
open Lane4.Seq Lane4.Coll

/-- The class is not empty: this network is a member. -/
theorem member : Lane4.Case.task.CountChannel Lane4.Case.net := Lane4.Case.membership

/-- Necessary radius for this network: a relative ball that is correct up to length `L`
has radius below `1 / (2 L - 1)`. -/
theorem radius (τ : ℚ) (L : ℕ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (hL : 2 ≤ L)
    (hb : Lane4.Case.task.OnBall Lane4.Case.net τ L) : τ * (2 * (L : ℚ) - 1) < 1 :=
  Lane4.CollProof.collision_bound Lane4.Case.task %(s)s %(o)s (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) Lane4.Case.net member τ L h0 h1 hL hb

theorem onBall_mono {T : Task} {N : TNet} {a b : ℚ} (hab : a ≤ b) {L : ℕ}
    (h : T.OnBall N b L) : T.OnBall N a L :=
  fun N' hN' w hv hl => h N' (Lane4.CollProof.netRel_mono hab hN') w hv hl

/-- No relative ball of positive radius is correct at every length. -/
theorem noBall (τ : ℚ) (hτ : 0 < τ) : ∃ L : ℕ, ¬ Lane4.Case.task.OnBall Lane4.Case.net τ L := by
  by_cases h1 : τ ≤ 1
  · obtain ⟨m, hm⟩ := exists_nat_gt (1 / τ)
    refine ⟨m + 2, fun hb => ?_⟩
    have hr := radius τ (m + 2) hτ.le h1 (by omega) hb
    have hm' : 1 < τ * (m : ℚ) := by
      have := mul_lt_mul_of_pos_left hm hτ
      rwa [mul_one_div_cancel hτ.ne'] at this
    push_cast at hr
    nlinarith
  · refine ⟨2, fun hb => ?_⟩
    have hb1 : Lane4.Case.task.OnBall Lane4.Case.net 1 2 := onBall_mono (le_of_not_ge h1) hb
    have hr := radius 1 2 (by norm_num) le_rfl le_rfl hb1
    norm_num at hr

end Lane4Final
#print axioms Lane4Final.member
#print axioms Lane4Final.radius
#print axioms Lane4Final.noBall
""" % {"s": s, "o": o}
out = ("import Lane4.Seq\n\n" + read("runs", "r6b", case, "Spec.lean") + "\n\n" + coll + "\n\n" +
       read("runs", "r6b", case, "Solution.lean") + "\n" + COR)
p = os.path.join(HERE, "runs", "r6b", case, "_Corollary.lean")
open(p, "w", encoding="utf-8", newline="\n").write(out)
print("wrote", p)
