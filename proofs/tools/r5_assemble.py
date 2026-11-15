"""Assemble the rung-5 kit modules from the kernel-checked kit cases (runs/r5-kit).

    python tools/r5_assemble.py      -> Lane4/RSoftKit.lean, Lane4/Bin32.lean

The kit lemmas were proved by Sonnet doctors as framework tasks (not test cases):
kA2 (rounded sums, geometric distance sum), kB (softmax lemma), kC2 (binary32 instance).
Each case's passing Solution is pasted in unchanged apart from the namespace.
"""
import glob, json, os
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
R = lambda p: open(os.path.join(HERE, p), encoding="utf-8").read()


def passing(case):
    for p in sorted(glob.glob(os.path.join(HERE, "runs", "r5-kit", case, "attempts", "*.json"))):
        if json.load(open(p, encoding="utf-8")).get("pass"):
            return open(p[:-5] + ".lean", encoding="utf-8").read()
    raise SystemExit("no passing attempt for " + case)


def body(text, ns):
    """Drop the `namespace Lane4.Case` wrapper lines; the caller supplies its own."""
    out = []
    for line in text.splitlines():
        if line.strip() in ("namespace Lane4.Case", "end Lane4.Case"):
            continue
        out.append(line)
    return "\n".join(out).strip() + "\n"


kit = '''/-
Lane 4, rung 5 lemma kit, part 2: rounded sums and the softmax lemmas.

Assembled by tools/r5_assemble.py from kit cases proved by Sonnet doctors and checked by
the same checker as every other case (runs/r5-kit/kA2, kB). Fixed by the lane; doctors do
not edit this file. What you need from it is at the END of the file: `soft_near` and
`soft_zeros` (and `rsum_err`, `geom_dist` if you sum things yourself).
-/
import Lane4.RSoft

namespace Lane4.RSoft
open Lane4.RSeq

-- ===== statements (kit case specs) =====
''' + body(R("runs/r5-kit/kB/Spec.lean"), "") + '''
-- ===== kA2: rounded sums, geometric distance sum =====
''' + body(passing("kA2"), "") + '''
-- ===== kB: softmax =====
''' + body(passing("kB"), "") + '''
-- ===== what doctors use =====

/-- SOFTMAX WITH A CLEAR WINNER. Candidates `c` (no duplicates, at most `n` of them), scores
`s`, values `f`. If key `j ∈ c` beats every other candidate `k` by at least
`16 * |j - k|` in score, then the head's output is within `B / 100 + 1 / 2^90` of the
winner's value `f j`, and it is unchanged by rounding it again.
`Sb` bounds the scores (`2 * Sb ≤ M`), `B` bounds the values (`4 * B + 4 ≤ M`). -/
theorem soft_near {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (he : ExpM u η ex)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2 ^ 149)
    {c : List ℕ} (hc : c.Nodup) {n : ℕ} (hlen : c.length ≤ n)
    (hn : u * (n : ℝ) ≤ 1 / 256) (hnη : η * (n : ℝ) ≤ 1 / 2 ^ 100)
    {s f : ℕ → ℝ} {j : ℕ} (hj : j ∈ c)
    (hgap : ∀ k ∈ c, k ≠ j → s k ≤ s j - 16 * (ndist j k : ℝ))
    {Sb : ℝ} (hS : ∀ k ∈ c, |s k| ≤ Sb) (hSM : 2 * Sb ≤ M)
    {B : ℝ} (hB : ∀ k ∈ c, |f k| ≤ B) (hBM : 4 * B + 4 ≤ M) :
    |savg fl ex c s f - f j| ≤ B / 100 + 1 / 2 ^ 90
      ∧ fl (savg fl ex c s f) = savg fl ex c s f :=
  savg_near rsum_err geom_dist u η M fl ex hr he hu0 hu hη0 hη c hc n hlen hn hnη s f j hj hgap
    Sb hS hSM B hB hBM

/-- SOFTMAX OVER ZERO VALUES. If every candidate's value is exactly 0, the head's output is
exactly 0, whatever the scores are. -/
theorem soft_zeros {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) {c : List ℕ}
    {s f : ℕ → ℝ} (h : ∀ k ∈ c, f k = 0) : savg fl ex c s f = 0 :=
  savg_zeros u η M fl ex hr c s f h

end Lane4.RSoft
'''
open(os.path.join(HERE, "Lane4", "RSoftKit.lean"), "w", encoding="utf-8", newline="\n").write(kit)

b32 = '''/-
Lane 4, rung 5: binary32 arithmetic satisfies the rounding model of RSoft.lean.

Assembled by tools/r5_assemble.py from kit case runs/r5-kit/kC2 (proved by a Sonnet doctor,
checked by the lane's checker). Not needed by doctors.

`F32U` is the binary32 grid with subnormals (`m * 2^e`, `|m| < 2^24`, `e ≥ -149`); the
finite binary32 numbers are its members of magnitude at most `maxF`. `IsRN rn` says `rn`
rounds every real to a nearest grid point (any tie rule; round-to-nearest-even is one).
`bin32_rnd`: any `fl` that agrees with such an `rn` on `|x| ≤ maxF` satisfies
`Rnd (1/2^24) (1/2^150) maxF fl`. That is IEEE 754 binary32 addition, subtraction,
multiplication and division of finite values with finite results (each returns the
rounding of the exact result); signed zeros are identified and the bit-level encoding is
not modelled. The model assumes nothing outside `|x| ≤ maxF`, so a theorem proved from
`Rnd` also shows that no exact result exceeds `maxF` (no overflow).
-/
import Lane4.RSoft

namespace Lane4.Bin32
open Lane4.RSoft

''' + body(R("runs/r5-kit/kC2/Spec.lean"), "").replace("open Lane4.RSoft\n", "") + "\n" + \
    body(passing("kC2"), "").replace("open Lane4.RSoft\n", "") + '''
/-- Binary32 satisfies the rounding model on the finite range. -/
theorem bin32_rnd {rn fl : ℝ → ℝ} (h : IsRN rn) (hfl : ∀ x, |x| ≤ maxF → fl x = rn x) :
    Rnd (1 / 2 ^ 24) (1 / 2 ^ 150) maxF fl := rn_rnd rn h fl hfl

/-- The range of the model covers the statement's range condition for up to 2^16
positions: `2^40 * n^2 ≤ maxF` whenever `n ≤ 65536`. -/
theorem range_ok {n : ℕ} (hn : n ≤ 65536) : (2 : ℝ) ^ 40 * (n : ℝ) ^ 2 ≤ maxF := by
  have h1 : (n : ℝ) ≤ 65536 := by exact_mod_cast hn
  have h2 : (n : ℝ) ^ 2 ≤ 65536 ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg n) h1 2
  unfold maxF
  nlinarith [h2]

end Lane4.Bin32
'''
open(os.path.join(HERE, "Lane4", "Bin32.lean"), "w", encoding="utf-8", newline="\n").write(b32)
print("assembled RSoftKit.lean (%d lines), Bin32.lean (%d lines)" % (kit.count("\n"), b32.count("\n")))
