# Lane 4, rung 1 results

**Status: CLOSED (2026-11-11, 9:50 pm EST).** All three arms are complete: 60 episodes,
none rerun. Every number below is read from the attempt logs by `tools/collect.py`,
`tools/summary.py` and `tools/eps_range.py`, not from doctor reports.

## Headline

A Sonnet doctor wrote the weights of a ReLU MLP and a kernel-checked Lean 4 proof of exact
equality with the spec, for all reals in the box, on **20 of 20** blind test specs. The
verified-code control also scored 20 of 20 with fewer submissions, so **at rung 1 the
network adds nothing over a verified program**. This was the pre-registered expected
outcome. The trained-twin arm reached 17 of 20, so **no contrast with trained networks is
shown**. It is not a first (see NOVELTY.md).

## Table (n = 20 test specs, the same 20 in every arm)

| | net (weights + proof) | prog (verified-code control) | twin (trained weights, ε bound) |
|---|---|---|---|
| Kernel-checked | **20 / 20** | **20 / 20** | **17 / 20** |
| Submissions per case, median (range) | 2 (1-5) | 1.5 (1-3) | 5 (1-12) |
| Total submissions | 48 | 31 | 123 |
| Lean seconds per case, median | 24 | 16 | 367 |
| Solution lines, median (range) | 47 (14-128) | 20 (12-32) | 71 (13-844), passing cases |
| Lean checks over 600 s | 0 | 0 | 1 |
| Lean checks killed at 4.5 GB | 0 | 0 | 36 |
| `native_decide` attempts | **0** | **0** | **0** |
| Other banned-token rejections | 0 | 0 | 1 (`#exit`, twin p074) |

Net sizes (doctor-written): hidden layers median 3 (1-6), hidden units median 12 (5-35),
non-zero weights median 31 (12-93).

Twin failures: p266 (gave up after 6 submissions), p129 and p262 (all 12 used). All
three are proof-size failures: 17-21 ReLUs give hundreds of activation cells, and the
generated proofs passed the 600 s or 4.5 GB limit. None shows the ε bound is false.

## Pre-registered bars

- Kill (S_net < 12): not triggered. Pass (S_net ≥ 16): **met**, S_net = 20.
- Verified-code control: S_prog = 20 ≥ S_net = 20 and median submissions 1.5 ≤ 2, so the
  reading "the network adds nothing over a verified program at rung 1" **applies**.
- Trained-twin contrast (needs S_net − S_twin ≥ 8): 20 − 17 = 3. **No contrast shown.**

## Twin tolerance against output range (post hoc, NOT pre-registered)

Added after the runs at the project lead's request. The pre-registered count above is
unchanged. ε was set as 4 × the twin's sampled worst error, so a badly fitted twin gets a
loose ε. The table gives ε as a fraction of the spec's output range over the box (range
sampled exactly at the corners and 20,000 grid points, so the fraction is an upper bound).

| Twin | ε | Output range | ε / range | Submissions | Result |
|---|---|---|---|---|---|
| p175 | 0.09 | 42.00 | 0.2% | 1 | pass |
| p294 | 0.03 | 9.00 | 0.3% | 4 | pass |
| p087 | 0.10 | 10.00 | 1.0% | 11 | pass |
| p232 | 0.31 | 7.03 | 4.4% | 8 | pass |
| p074 | 0.86 | 19.00 | 4.5% | 8 | pass |
| p122 | 2.21 | 27.50 | 8.0% | 10 | pass |
| p129 | 1.95 | 19.45 | 10.0% | 12 | **fail** |
| p262 | 2.92 | 18.00 | 16.2% | 12 | **fail** |
| p096 | 3.01 | 14.75 | 20.4% | 4 | pass |
| p049 | 1.86 | 8.50 | 21.9% | 11 | pass |
| p069 | 9.04 | 28.50 | 31.7% | 2 | pass |
| p266 | 1.46 | 4.50 | 32.4% | 6 | **fail** |
| p057 | 5.30 | 9.00 | 58.9% | 2 | pass |
| p031 | 4.59 | 5.78 | 79.4% | 9 | pass |
| p166 | 2.86 | 2.00 | 143% | 11 | pass |
| p297 | 8.56 | 3.50 | 245% | 3 | pass |
| p019 | 39.43 | 14.00 | 282% | 2 | pass |
| p124 | 32.36 | 11.00 | 294% | 3 | pass |
| p063 | 79.97 | 25.00 | 320% | 2 | pass |
| p192 | 1.89 | 0.50 | 378% | 2 | pass |

**Post-hoc count: 6 twins have ε under 10% of the range, and all 6 passed.** p129 sits
just over the line (10.03%) and failed. Six twins have ε wider than the whole output
range; those passes say almost nothing about the network. The three failures are all in
the middle band (10-32%), on the larger twins (17-21 ReLUs). So the tight-ε subset gives
no contrast either; what separates pass from fail in this arm is proof size, not ε.

## Seeds and frozen inputs

- Spec pool seed 20261111 (300 specs), draw seed 4042 (4 dev, 20 test, 10 reserve). No
  reserve spec was used. Hashes are in PREREG.md.
- Twins: numpy Adam, seeds 0, 1, 2 per spec; seed 0 is the twin the doctor got. Errors for
  all three seeds are in `results/twins-test.json`.
- Doctors: Sonnet subagents, one episode per case and arm, 12 submissions, no reruns.
  No Opus or Fable doctor was used.
- Prompt and framework hash frozen before any test case was built (PREREG amendment 7).

## Float versus exact arithmetic

Every theorem is about exact rational weights and real-number arithmetic. Nothing is proved
about a floating-point forward pass. Measured only: a float32 forward pass of each of the
20 written nets, at 10,000 random float32 box points, deviates from the exact spec by at
most **3.6e-6**; evaluated exactly, each net equals the spec at all 10,000 points.

## Trained twins: exact equality

No trained twin (seed 0) equals its spec exactly: each one differs at some of the 20,000
sampled rational points, so exact equality is refuted by evaluation alone. This is the
trivial reason noted in the PREREG and is not counted as a contrast. Seed-0 largest errors
range from 0.005 (p294) to 20 (p063); several twins in the small written architectures are
poor fits, and three seeds of the same spec can differ by a factor of 100 or more.

## Limits of this result

- ε is 4 × a sampled maximum error, not a certified bound, and on 6 of 20 twins it is
  wider than the spec's whole output range (table above). Rung 2 must cap the tolerance
  as a fraction of the output range before any twin is trained.
- The 4.5 GB memory guard (added on dev, before the test set) is the binding limit in the
  twin arm. A larger memory budget would likely change twin outcomes, not net or prog ones.
- Marabou and α,β-CROWN were not run (not installed; installing needs approval).
- `service.py` was changed after the freeze: a crash fix for a vanished request file
  (15:07). It does not touch checking.
- Doctor rule slips, self-reported and outside the checker's rules: several doctors wrote
  or patched `Solution.lean` from Python or the shell instead of the file tool; doctors
  share one scratch folder and three reported overwriting each other's helper scripts (one
  wasted submission, twin p049). For about 2 minutes four doctors ran at once.
- Compute: memory reservations were 4 GB (service) and 2 GB per doctor, later 3 GB and 0.5 GB, as set
  by the compute scheduler. The child-memory log only caught the submit script (8.7 MB peak);
  the doctors' own numpy and LP scratch scripts ran outside the logged pattern, so their
  memory was **not measured**.
- One twin doctor (p175) reported "queue stuck" five minutes into a running check. It was
  told only that the queue was working and its episode was not over; the pass came from the
  submission it had already made.
- Twin p074 (35 ReLUs, the largest) passed with a different method from the rest: a
  generic bound checker proved sound once, then run by kernel evaluation
  (`decide +kernel`, standard axioms only, not `native_decide`). The three failed twins
  used case-split proofs; they were not retried with this method.
- One doctor, one budget, one model. Rung 1 specs have 2-4 nonlinear operations on 1-3
  inputs; nothing here speaks to larger networks.

## How to check a case

    python tools/check.py runs/rung1-test/net/p294      (under a memory reservation)

It rebuilds `_Full.lean` from `Spec.lean`, `Solution.lean` and `Final.lean`, runs the Lean
kernel, and requires exit 0, no `sorry`, and axioms within propext, Classical.choice and
Quot.sound. Per-case records are in `results/rung1-test.json`.
