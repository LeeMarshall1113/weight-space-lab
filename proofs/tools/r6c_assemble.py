"""Rung 6c: assemble everything into one file and derive the lane's corollaries (PREREG_R6C.md).

    python tools/r6c_assemble.py      -> runs/r6c/final/R6C.lean   (compile with tools/lean_lease.sh)

Contents, in order: import Lane4.Seq; Collision.lean and TokenBlind.lean statement text;
the invariant; the proved cases (each moved from namespace Lane4.Case to its own):
iHead, iBlock, iNet, cColl, cBounds, and rung 6b's kColl2 (for monotonicity of the ball);
the five networks with their mechanical membership proofs; then theorems written by the
lane: the four registered statements, and per network the radius bound and "no ball".
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import make_r6c_cases as G

HERE = G.HERE
read = lambda *p: open(os.path.join(HERE, *p), encoding="utf-8").read()


def proved(path, ns):
    s = read(*path)
    assert "namespace Lane4.Case" in s and "end Lane4.Case" in s
    return s.replace("namespace Lane4.Case", "namespace " + ns).replace("end Lane4.Case", "end " + ns) + "\n\n"


PAR = {"p05": (4, "[0]", "fun t => t == 1 || t == 3 || t == 4", 0, 1, 2),
       "p10": (3, "[0]", "fun t => t == 1 || t == 2", 0, 1, 3),
       "p29": (4, "[0]", "fun t => t == 2 || t == 3", 1, 2, 1)}
SORT = {"s00": (2, "[1]"), "s01": (3, "[0, 1]")}

out = "import Lane4.Seq\n\n" + G.BASE + G.AGREE + "\n"
out += proved(("runs", "r6c", "iHead", "Solution.lean"), "Lane4.HeadProof") + G.BLOCK + "\n"
out += proved(("runs", "r6c", "iBlock", "Solution.lean"), "Lane4.BlockProof")
out += proved(("runs", "r6c", "iNet", "Solution.lean"), "Lane4.NetProof")
out += proved(("runs", "r6c", "cColl", "Solution.lean"), "Lane4.CollOfInv")
out += proved(("runs", "r6c", "cBounds", "Solution.lean"), "Lane4.BoundsProof")
out += proved(("runs", "r6b", "kColl2", "Solution.lean"), "Lane4.CollProof")

out += """namespace Lane4Final
open Lane4.Seq Lane4.Coll Lane4.TB

theorem invariance : Invariance := Lane4.NetProof.invariance
theorem collision : Collision := Lane4.CollOfInv.collision_of_invariance invariance
theorem parityBound : ParityBound := Lane4.BoundsProof.parity_of_collision collision
theorem sortBound : SortBound := Lane4.BoundsProof.sort_of_collision collision

theorem onBall_mono {K : Task} {N : TNet} {a b : ℚ} (hab : a ≤ b) {L : ℕ}
    (h : K.OnBall N b L) : K.OnBall N a L :=
  fun N' hN' w hv hl => h N' (Lane4.CollProof.netRel_mono hab hN') w hv hl

theorem sortOnBall_mono {ntok : ℕ} {N : TNet} {a b : ℚ} (hab : a ≤ b) {L : ℕ}
    (h : SortOnBall ntok N b L) : SortOnBall ntok N a L :=
  fun N' hN' w hne hv hl i hi1 hi2 => h N' (Lane4.CollProof.netRel_mono hab hN') w hne hv hl i hi1 hi2

/-- From a radius bound at every odd length to "no positive radius works at every length". -/
theorem noBall_of (P : ℚ → ℕ → Prop)
    (mono : ∀ {a b : ℚ}, a ≤ b → ∀ {L : ℕ}, P b L → P a L)
    (rad : ∀ (τ : ℚ) (a : ℕ), 0 ≤ τ → τ ≤ 1 → 1 ≤ a → P τ (2 * a + 1) → τ * (2 * (a : ℚ) + 1) < 1)
    (τ : ℚ) (hτ : 0 < τ) : ∃ L : ℕ, ¬ P τ L := by
  by_cases h1 : τ ≤ 1
  · obtain ⟨m, hm⟩ := exists_nat_gt (1 / τ)
    have hm' : 1 < τ * (m : ℚ) := by
      have := mul_lt_mul_of_pos_left hm hτ
      rwa [mul_one_div_cancel hτ.ne'] at this
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        norm_num at hm'
      · exact h0
    refine ⟨2 * m + 1, fun hb => ?_⟩
    have hr := rad τ m hτ.le h1 hm1 hb
    nlinarith
  · refine ⟨2 * 1 + 1, fun hb => ?_⟩
    have hb1 : P 1 (2 * 1 + 1) := mono (le_of_not_ge h1) hb
    have hr := rad 1 1 (by norm_num) le_rfl le_rfl hb1
    norm_num at hr

end Lane4Final

"""
for p, (ntok, T, inS, par, s, o) in PAR.items():
    sol = read("runs", "rung2-test", "net", p, "Solution.lean")
    i = sol.index("def net : TNet"); j = sol.index("\n\n", i)
    defs = sol[sol.index("open Lane4.Seq") + len("open Lane4.Seq"):j]
    out += """namespace Lane4.Member.%(p)s
open Lane4.Seq Lane4.Coll Lane4.TB
%(defs)s

def task : Task := { V := %(ntok)d, inS := %(inS)s, par := %(par)d }

theorem member : tokenBlind net %(ntok)d %(T)s = true := by decide

/-- A relative ball that is correct for this network's parity task up to length 2a+1 has
radius below 1/(2a+1). -/
theorem radius (τ : ℚ) (a : ℕ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (ha : 1 ≤ a)
    (hb : task.OnBall net τ (2 * a + 1)) : τ * (2 * (a : ℚ) + 1) < 1 :=
  Lane4Final.parityBound net %(T)s task %(s)d %(o)d member (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) τ a h0 h1 ha hb

theorem noBall (τ : ℚ) (hτ : 0 < τ) : ∃ L : ℕ, ¬ task.OnBall net τ L :=
  Lane4Final.noBall_of (fun t L => task.OnBall net t L) (fun hab _ h => Lane4Final.onBall_mono hab h)
    radius τ hτ

end Lane4.Member.%(p)s

""" % dict(p=p, defs=defs, ntok=ntok, T=T, inS=inS, par=par, s=s, o=o)
for p, (ntok, T) in SORT.items():
    sol = read("runs", "rung2-test", "net", p, "Solution.lean")
    i = sol.index("def net : TNet"); j = sol.index("\n\n", i)
    defs = sol[sol.index("open Lane4.Seq") + len("open Lane4.Seq"):j]
    out += """namespace Lane4.Member.%(p)s
open Lane4.Seq Lane4.Coll Lane4.TB
%(defs)s

theorem member : tokenBlind net %(ntok)d %(T)s = true := by decide

/-- A relative ball that is correct for sort rank up to length 2a+1 has radius below 1/(2a+1). -/
theorem radius (τ : ℚ) (a : ℕ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (ha : 1 ≤ a)
    (hb : SortOnBall %(ntok)d net τ (2 * a + 1)) : τ * (2 * (a : ℚ) + 1) < 1 :=
  Lane4Final.sortBound net %(ntok)d %(T)s member (by decide) τ a h0 h1 ha hb

theorem noBall (τ : ℚ) (hτ : 0 < τ) : ∃ L : ℕ, ¬ SortOnBall %(ntok)d net τ L :=
  Lane4Final.noBall_of (fun t L => SortOnBall %(ntok)d net t L)
    (fun hab _ h => Lane4Final.sortOnBall_mono hab h) radius τ hτ

end Lane4.Member.%(p)s

""" % dict(p=p, defs=defs, ntok=ntok, T=T)
names = ["Lane4Final.invariance", "Lane4Final.collision", "Lane4Final.parityBound", "Lane4Final.sortBound"]
for p in list(PAR) + list(SORT):
    names += ["Lane4.Member.%s.member" % p, "Lane4.Member.%s.radius" % p, "Lane4.Member.%s.noBall" % p]
out += "".join("#print axioms %s\n" % n for n in names)
d = os.path.join(HERE, "runs", "r6c", "final")
os.makedirs(d, exist_ok=True)
open(os.path.join(d, "R6C.lean"), "w", encoding="utf-8", newline="\n").write(out)
print("wrote", os.path.join(d, "R6C.lean"), len(out.splitlines()), "lines")
