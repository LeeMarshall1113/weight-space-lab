# Rung 9-LN15 result: bar met (3 of 3); 13 of 19 screened fresh networks proved, at ball 2^-15

Written 2026-11-22 (Sunday morning EST). Registered in `PREREG_R9LN15.md` with Amendment 1.

**Read this first.** This is a post-hoc rung. The registered LayerNorm rung at ball 2^-14
(`PREREG_R9LN.md`) stopped at its kill rule K2 and stays stopped (`RESULTS_R9LN.md`). The radius
2^-15, the enclosure design, the symbol layout and the fixed-point arithmetic were all chosen
afterwards, on the same 18 tuning networks; five checker variants were tried on them. Only the
counts on fresh seeds below are results. It covers five tokens and one
block, and an experiment on a small trained text model (E3, described in `REPORT.md` Section 6.12)
showed the method does not carry to real text.

## Headline (the sentence fixed in the registration)

**13 of 19 gradient-trained one-block softmax transformers with LayerNorm that pass the screen
(20 fresh seeds trained), are proved by one soundness theorem and a kernel-checked certificate
each to compute the task at every position of every input length, for every weight setting
within 2^-15 of the rounded weights, in a binary32 rounding model. The radius and the checker
design were chosen after a registered attempt at 2^-14 failed its kill rule on the tuning
networks.** Prior work to cite for what each has: teal-sea, Gross et al., Stambler et al.
(2502.06038), Somani (2605.24033). No "first" wording.

## The theorem

`Lane4.LNC.SoundLN` (`Lane4/LNCert.lean`, proof module `Lane4/LNKI.lean`): if the checker
`checkLN` accepts a written network at radius δ, then every network within the additive δ-ball
(all weights, LayerNorm gains and biases included), in the rounding model, is within 1/4 of the
task target at every position of every input the model covers. Kernel-checked; axioms `propext`,
`Classical.choice`, `Quot.sound`; no `native_decide`, no `sorry`. Per network, generated with no
proof search and every closed Boolean by `decide +kernel`: `accept`, `skeleton_ok`, `binary32`,
`trained_exact_all_lengths` (the network AS TRAINED, exact arithmetic, every input length) and
`trained_binary32` (as trained, binary32, up to 65,535 tokens).

Three LayerNorms in the standard pre-LN places; LN2 and LNf act on the residual stream after
attention and after the MLP. That enclosure, with a rounding model and a weight ball, checked in
a proof assistant on trained networks, is what this rung adds over rung 8.

## Bar and counts on fresh seeds 400 to 419

Everything (model, checker, statements, proof modules, mirror, generator, runner, training and
screen tool) was frozen by hash before any fresh seed was trained
(`scratch/freeze_r9ln15_s3.sha256`); the list still verifies.

| | count |
|---|---|
| trained | 20 |
| compute the task (float32, to 65,534 tokens) | 19 (not 406) |
| pass the screen | 19 |
| **bar: first three screened (400, 401, 402) with all five theorems** | **3 of 3** (needed 2) |
| kernel-accepted, all five theorems | **13**: 400, 401, 402, 404, 405, 407, 408, 409, 410, 412, 414, 417, 419 |
| kernel-rejected at a case | 6: 403, 411, 413, 415, 416, 418 |
| rejected by the mirror before any case (no certificate, so no kernel file) | 1: 406, the seed that fails the screen |

The kernel's decision equals the mirror's on every network it was given (19 fresh, 7 controls,
10 tuning). The six rejected networks pass the screen and compute the task; the checker's bound is
too wide for them (a radius of 0.28 to 0.86 where the output must stay within 0.25 of the
target, and for 418 a variance bound that reaches zero).
They are failures of the enclosure, not of the networks. Nothing was adjusted after the freeze.

Kernel cost: 155-case networks take 380 to 450 s in two files, at most 4.86 GB. The two 780-case
networks (402, 409) take four files each: 674, 666, 667, 11 s and about the same for 409, at most
5.07 GB. The registered four-file rule held with no file to spare.

Tuning networks, for the record and labelled as fitted: 14 of 18 accepted by the mirror; 9 of
those went through the kernel with all theorems (100 to 105, 108, 109, 113); 112, 114, 115, 117,
118 were not run in the kernel; one mirror rejection (107) was confirmed in the kernel.

## Controls (each must be rejected in the kernel): 7 of 7 rejected, plus the failed-screen seed

On tuning network 104: task B's automaton; embedding rows 1 and 2 swapped; read-out negated;
read-out bias raised by 1/2; LN2 gains negated; radius 16 times larger (2^-11); radius 64 times
larger (2^-9). All seven kernel-rejected (12 to 13 s each). Seed 406 (fails s1) is rejected by
the mirror before a certificate exists, so there is no kernel file for it: said as registered.

**About the radius controls.** 5 of the 18 tuning networks are genuinely accepted at 2^-14 by the
earlier prototype, so a control at twice the radius would not have been a control. The meaningful
ones are 16 and 64 times.

## Sampled checks on the 13 accepted networks (searches, not proofs)

`tools/ln15_checks.py`, `results/rung9ln15-lanechecks.json`. Trained network, inputs up to 65,534
tokens: worst deviation 0.044 in float32 and in float64. Skeleton under 60 sampled perturbations
inside the 2^-15 ball (uniform and sign corners): worst 0.045. Sampled sign perturbations first
break the 1/4 bound at 32 times the radius (4 networks) or 64 times (9). Numeric interval test
against the mirror's table: 0 violations in 56,743 positions, smallest slack 0.0046.

## What it cost

- Doctor tokens: 2.16 million Sonnet (budget 3.5 to 5 million). Ten kit cases; every one passed
  with its first doctor (submissions 1 to 14 of 30), two of them (`ScoreWinLN`, `HeadSoundLN`)
  as text-substitution ports of the rung-8 proofs with no doctor at all. No retry doctor.
  **No stronger-model step**: the reciprocal-square-root lemma it was held for passed with Sonnet.
- Reused unchanged from rung 8: softmax arithmetic, exponential enclosure, shared attention, the
  windows automaton, and `headAF`.

## What weakens the result

- Post hoc throughout (see the top). The tuning count is fitted and is not evidence.
- The ball 2^-15 is the smallest around the rounded weights that contains the trained network:
  there is no robustness margin beyond rounding to the 2^-14 grid (rung 8 had 2^-14, rung 7
  1/1000). Near 1 the ball spans 256 float32 steps each way.
- 13 of 19, not 19 of 19: a third of the screened networks compute the task and are not proved.
- Five tokens, one block, width 8, a local task, slope fixed at 24, the study team's own recipe.
- LN1 sees embeddings only; LN2 and LNf see a residual stream that takes few values per abstract
  case. That is why an enclosure works here and did not in E3.
- binary32: `fl` is round-to-nearest; the exponential and the square root are ASSUMED to satisfy
  their models (`ExpM`, `SqrtM`); the relative rounding model is the study team's reading of binary32.
- The checker has guards that the proof turned out not to need (the zero-slot guards on the
  accumulated forms). They only make the checker reject more.
- Found by the study team before any proof work, and fixed in Amendment 1: the first checker text did
  not charge the rounding of stored biases, which would have made the soundness statement false.
  The proved text has the charge; I mention it because the same kind of slip in a guard the
  proof does not exercise would not be caught by the kernel.
- Process: one 1-second mirror self-test ran without a reservation; the registration's first line
  carries a wrong date, corrected in Amendment 1.

## Files

`PREREG_R9LN15.md`; `Lane4/LNNet.lean`, `LNCert.lean`, `LNDefs.lean`, `LNT.lean`, `LNGlue.lean`,
`LNKA.lean` to `LNKJ.lean`, `LNAll.lean`; `runs/r9ln15-kit/` (ten cases with attempts);
`tools/r9ln15_cert.py` (mirror), `make_r9ln15_net.py`, `build_ln_net.py`, `ln_port.py`,
`ln15_ctl.py`, `ln15_checks.py`; `runs/r9ln15-fresh/` (networks and screens);
`runs/r9ln15-nets/<tag>/` (Lean files, logs, `kernel.json`; f = fresh, t = tuning, c = control);
`results/rung9ln15-kernel.json`, `results/rung9ln15-lanechecks.json`;
`scratch/freeze_r9ln15_a1.sha256`, `scratch/freeze_r9ln15_s3.sha256`.
