# Pre-registration: rungs 0 and 1

Written 2026-11-11, before any doctor run. Changes after this commit go in a
dated "Amendments" section at the end, never as edits above it.

Read NOVELTY.md first: the study team no longer claims to be the first LLM-written
network with a machine-checked proof. What this experiment measures is a
success **rate** from a blind random spec pool with controls, which no prior
item reports.

## Question

Given a written piece-wise linear spec, can a Sonnet doctor write the weights of
a ReLU MLP **and** a Lean 4 proof, accepted by the kernel, that the network
equals the spec at every real point of a stated box?

## Fixed framework (the trust base besides Lean and Mathlib)

- `Lane4/Basic.lean`: network type (rational weights), `Net.eval` over any
  linearly ordered field, a shape check, and six small ReLU lemmas. Written by
  the study team. Doctors cannot change it.
- Per case, the study team writes `Spec.lean` (the spec as a Lean term and the
  `Statement`) and `Final.lean` (the theorem `Lane4Final.final : Statement net`
  plus `#print axioms`). The doctor writes only `Solution.lean`.
- `tools/check.py <casedir>` is the one command. A case **passes** when: the
  solution has no banned token; Lean exits 0 on spec + solution + final; there
  is no `sorry`; the axioms of `Lane4Final.final` are within `propext`,
  `Classical.choice`, `Quot.sound`; and (network arm) the shape theorem holds:
  well-shaped, at most 6 hidden layers, each at most 32 wide.
- **`native_decide` is banned**, along with `sorry`, `axiom`, macros, notation,
  instances and anything in the `Lean.` namespace. A solution using one fails
  without Lean being run. Every `native_decide` attempt is counted and
  reported.
- Lean v4.35.0-rc3 with the Mathlib oleans in `a Mathlib checkout`. Not rebuilt.

## Spec pool and draw (blind)

- `tools/specpool.py pool`, seed 20261111: 300 random expressions over 1-3
  inputs built from affine leaves (coefficients in {-2,-1,-1/2,1/2,1,2,3}), and
  2-4 nonlinear operations from max, min, abs, relu, clamp, median-of-3, joined
  by linear combinations. Each input has a random integer box. A spec is kept
  only if every nonlinear node takes each of its branches on at least 2% of
  3,000 random box points, so no operation is dead inside the box.
  Pool sha256 `859a34bb9fd262e46f9ef4afbca5ab1cd9a508bc87c458a99917d607db9b902f`.
- `tools/specpool.py draw`, seed 4042: a shuffle; the first 4 are **dev**, the
  next 20 are **test**, the next 10 are reserve. Test-id sha256
  `3d56d372da5e5c7dd65bf2a7f816e638c2ed37c02855131a224c539b7bb9b6cd`.
- The study team has read the 4 dev specs and has not read the test specs. Prompts
  are tuned on dev only and frozen (hash recorded in the run log (not released)) before any
  test case is built. A reserve spec replaces a test spec only if its case
  files fail to compile for a reason in the study team's own generator; never for
  difficulty.
- Rung 0 pool: 50 random 4-bit boolean functions that depend on all 4 bits
  (seed 20261112); the first 3 of the same shuffle are used.

## Rung 0 (pipeline check only, not a result)

Three random 4-bit boolean functions, network over ℚ, statement for all 16
inputs, proof by kernel evaluation (`decide`) or case split. One doctor each.
Purpose: show the checker, the service, the memory reservations and the logging work, and
that planted faults are rejected (smoke cases: wrong weight, `sorry`,
`native_decide`, a control program that calls `max`). Rung 0 is exhaustive
testing with a kernel receipt and is reported as such.

## Rung 1 arms (n = 20 test specs, the same 20 in every arm)

| Arm | Doctor writes | Theorem (for all reals in the box) |
|---|---|---|
| **net** (primary) | `net : Lane4.Net` and `net_correct` | `net.eval [x..] = [spec x..]` |
| **prog** (verified-code control) | `prog`, a Lean function using only `if … then … else`, comparison and arithmetic (no max, min, abs or relu in the program part), and `prog_correct` | `prog x.. = spec x..` |
| **twin** (trained twin) | only the proof `twin_correct`; the weights are given | `twin.eval [x..] = [y]` with `|y - spec x..| ≤ ε` |

Twin construction, per spec: the architecture of the passing net-arm solution
(or hidden widths 16, 16 if the net arm failed); numpy Adam on MSE over uniform
box samples, 20,000 steps, batch 256, lr 1e-2 with cosine decay, seeds 0, 1, 2;
weights rounded to multiples of 1/1024 and from then on treated as exact
rationals. Seed 0 is the twin the doctor gets; seeds 1 and 2 are reported for
error only. ε is 4 × the largest exact error of the rounded network on 20,000
random rational box points, rounded up to a multiple of 1/100. Two things are
reported per twin: (a) exact equality with the spec, decided by exact rational
evaluation at the sample points (a single mismatch refutes it; no doctor); (b)
whether the doctor proves the ε bound. A failed twin proof does not show the
bound is false; ε is sampled, not certified.

## Doctor protocol (all arms)

- Sonnet subagent, one episode per case and arm, no memory between episodes, no
  nested agents, no web. It gets the case folder: `TASK.md`, `Spec.lean`,
  `Final.lean`, a copy of `Basic.lean`, and one worked example on an unrelated
  toy spec.
- It may run small Python (stdlib, numpy) to test its weights numerically. It
  never runs `lean` or `lake`. It submits with `tools/submit.py <casedir>`,
  which returns PASS or FAIL with Lean's output.
- Budget: **12 submissions** per episode (enforced by the service), 600 s of
  Lean per submission. The episode ends at the first PASS, at 12 submissions,
  or when the doctor gives up.
- The doctor is not told about the other arms, the pool, or the bars.
- Infrastructure failures (service down, memory reservation lost, an episode that dies
  without using a submission) are rerun once from a clean folder and logged.
  Nothing else is rerun.

## Measures

Primary: **S_net** = number of the 20 test specs with a kernel-checked net.
Secondary, per arm: submissions used, Lean seconds, proof length; for nets:
hidden layers, units, non-zero weights. Also the count of `native_decide`
attempts and other banned-token rejections.

**Float gap (measured, not proved).** Every theorem is about exact rational
weights and real arithmetic. For each passing net the study team also runs a float32
forward pass on 10,000 random box points and reports the largest deviation from
the exact spec. No rounding margin is proved at rung 1.

## Bars and kill rules

- **Kill:** S_net < 12 → stop the study team at rung 1 and report why.
- **Pass:** S_net ≥ 16.  12-15 is "partial"; report it and ask before rung 2.
- **Verified-code control:** if S_prog ≥ S_net and the median submissions used
  in prog is no more than in net, the reading is "at rung 1 the network adds
  nothing over a verified program". This is the expected outcome; it does not
  stop the study team (the scope puts the answer to "why a network" at rung 3), but
  it is stated in the headline.
- **Trained-twin contrast:** claimed only if S_net − S_twin ≥ 8 on the same 20
  specs. Otherwise "no contrast shown". The exact-equality refutation count is
  reported, but it is not a contrast: a trained net is only approximately
  right, so exact equality fails for a trivial reason.
- **Stop after rung 1.** Rung 2 needs a go from the coordinating session.

## What will not be claimed

- Not "first" (see NOVELTY.md).
- Not that the float network is correct.
- Not that proving trained networks is impossible: the twin arm tests one
  doctor, one budget and a sampled ε.
- Off-the-shelf solvers (Marabou, α,β-CROWN) are in the scope's control list
  but are **not run** here: neither is installed and installing needs approval.
  The table will say so.

## Compute

- Every `lean` call runs inside `tools/service.py` (or `check.py`) under a
  a memory reservation of 8 GB. No
  `lake`. Concurrency inside the memory reservation is set from the peak memory measured in
  the smoke test.
- Doctor batches: one memory reservation at 4 GB per concurrent doctor, at most 3 doctors
  lab-wide, slots agreed with lanes 1 and 2.
- If a memory reservation is lost: stop submitting, let the file in flight finish, re-queue.
- Twin training is numpy on CPU, 2 threads, about a minute per spec.

## Amendments

**2026-11-11, after rung 0 and the dev pilot, before any test case was built or read.**

1. Rung 0 proofs are case split + `simp`/`norm_num`; `decide` does not reduce rational
   arithmetic in the kernel (smoke case s1b). The statement and checker are unchanged.
2. Compute: the compute scheduler approved a 4 GB service memory reservation (one lean.exe at a time,
   measured 1.7 GB working set) and 2 GB per doctor, replacing 8 GB and 4 GB.
3. New limit: a Lean check whose working set passes 4.5 GB is killed and counts as a failed
   submission (a generated 3,938-line dev proof reached 7.8 GB). Stated in every TASK.md.
4. TASK.md text changes from dev: write the file as UTF-8 with the file tool; the limits in
   item 3. The Lean output returned to doctors keeps its head as well as its tail.
5. The float32 gap is measured at 10,000 random float32 box points (not grid points, which
   are exactly representable and give a gap of 0).
6. Net weights for the size and float measures are parsed from the solution text in file
   order; the parse is accepted only if the parsed net equals the spec at all 10,000 points.
7. Frozen prompt and framework hash (make_cases.py, train_twin.py, check.py, service.py,
   submit.py, doctor_prompt.txt, examples, Basic.lean, concatenated in that order), sha256:
   `849834d581310395a8c997ae32807310c7d17dbdd516566d11fe7aaf2d7a31ab`
