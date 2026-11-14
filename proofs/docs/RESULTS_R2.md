# Lane 4, rung 2 results: transformers proved correct for every sequence length

**Status: CLOSED (2026-11-12, 2:30 am EST).** 20 doctor episodes (10 net, 10 prog), all
Sonnet, none rerun; 30 twins trained. Every number is read from attempt logs and result
files by `tools/collect2.py`, not from doctor reports. Pre-registration: PREREG_R2.md
(five dated amendments, all made before the step they affect).

## Headline

On all **10 of 10** test cases a Sonnet doctor wrote the weights of a fixed-size
average-hard-attention transformer and a Lean 4 proof, accepted by the kernel with the
standard axioms, that the network is correct on inputs of **every length**. The plain-code
control also scored 10 of 10 at the same median cost, so again **the network adds nothing
over a verified program**. All 10 trained twins of the same shapes are wrong beyond their
training lengths.

How to read this, stated before the test set was built: the four task families are famous,
their constructions are in the literature, and the architecture was designed by the lane
so that those constructions fit. The result shows that Sonnet can **recall, adapt and
formally verify known constructions**, quickly. It does not show discovery of new
length-general algorithms. It is not a first; the nearest prior work is arXiv 2602.16473
(C-RASP programs verified with SMT model checkers, not weights, not a proof assistant).

## Table (10 test cases: 3 parity, 3 dyck, 2 sort, 2 add; the same 10 in each arm)

| | net (weights + all-lengths proof) | prog (plain-code control) | twin (trained, same shape) |
|---|---|---|---|
| Correct for every length, kernel-checked | **10 / 10** | **10 / 10** | not attempted (by design) |
| Sonnet-only count | 10 / 10 (no Fable episode needed) | 10 / 10 | - |
| Submissions per case, median (sorted) | 2 (1,1,2,2,2,2,3,3,3,4) | 2 (1,1,1,1,2,2,2,2,3,4) | - |
| Lean seconds per case, median | 26 | 11 | - |
| Solution lines, range | 176-417 | 29-99 | - |
| `native_decide` attempts | **0** | **0** | - |
| Other banned-token rejections | 0 | 2 (a `def` below the PROOF marker) | - |
| Checks over 600 s / killed at 4.5 GB | 0 / 0 | 0 / 0 | - |
| Seed-0 twins wrong at some length beyond training | - | - | **10 / 10** |
| Twins (30, all seeds) 100% correct in every length band | - | - | **0 / 30** |

Networks written: 1 block and 1 head for both add cases; 2 blocks and 2-3 heads for the
rest; state width 11-15 (limit 24).

## Pre-registered bars

- Kill (S2 < 5): not triggered. Pass (S2 ≥ 7): **met**, S2 = 10.
- Plain-code control: prog 10 ≥ net 10, median submissions 2 ≤ 2, so the reading "the
  network adds nothing over a verified program" **applies**. Program proofs are about a
  quarter of the length and check in under half the time.
- Twin contrast (at least 7 of 10 seed-0 twins wrong beyond training, and S2 ≥ 7):
  **met by the letter**, 10 of 10. Read the next section before repeating it.

## Twins: what the contrast is worth

Accuracy on 200 random inputs per length band; the better of the soft network and its
hardened version is shown (amendment 3). Trained on lengths 1-10.

| Case | seed 0: 1-10 / 11-20 / 21-40 / 100 | seed 1 | seed 2 |
|---|---|---|---|
| a00 add b=2 | 0.81 / 0.17 / 0.00 / 0.00 | 0.55 / 0.06 / 0.00 / 0.00 | 0.81 / 0.05 / 0.00 / 0.00 |
| a01 add b=3 | 0.80 / 0.07 / 0.00 / 0.00 | 0.39 / 0.01 / 0.00 / 0.00 | 0.76 / 0.04 / 0.00 / 0.00 |
| d10 dyck | 0.90 / 0.76 / 0.49 / 0.52 | 0.93 / 0.80 / 0.56 / 0.56 | 0.89 / 0.58 / 0.48 / 0.51 |
| d15 dyck | 0.88 / 0.67 / 0.51 / 0.47 | 0.93 / 0.82 / 0.52 / 0.49 | 0.96 / 0.73 / 0.48 / 0.48 |
| d18 dyck | 0.90 / 0.84 / 0.58 / 0.47 | 0.90 / 0.73 / 0.47 / 0.43 | 0.91 / 0.62 / 0.47 / 0.44 |
| p05 parity | 0.80 / 0.49 / 0.54 / 0.47 | 0.67 / 0.55 / 0.51 / 0.53 | 0.70 / 0.54 / 0.50 / 0.51 |
| p10 parity | 0.57 / 0.53 / 0.50 / 0.51 | 0.69 / 0.50 / 0.48 / 0.51 | 0.64 / 0.46 / 0.55 / 0.54 |
| p29 parity | 0.58 / 0.50 / 0.49 / 0.51 | 0.61 / 0.55 / 0.50 / 0.53 | 0.77 / 0.52 / 0.49 / 0.46 |
| s00 sort V=2 | 1.00 / 0.46 / 0.15 / 0.00 | 0.68 / 0.06 / 0.00 / 0.00 | 0.98 / 0.29 / 0.01 / 0.00 |
| s01 sort V=3 | 1.00 / 0.15 / 0.00 / 0.00 | 0.77 / 0.06 / 0.00 / 0.00 | 0.99 / 0.26 / 0.00 / 0.00 |

The contrast is weaker than "10 of 10" sounds:

- Only **2 of 30** twins are even 100% correct at the training lengths (the two sort
  seed-0 twins). Those two are real length-generalisation failures: perfect at 1-10, then
  46% and 15% at 11-20, 0% at 100.
- The other 28 did not fit the task in distribution, so their failure beyond length 10 is
  mostly a training failure of a very small network with raw position features, not
  evidence about length generalisation. Parity twins are near chance everywhere.
- The trainer is the lane's own numpy code with one fixed recipe (20,000 Adam steps). A
  better training recipe might fit more twins in distribution. It was not tuned, on
  purpose: it was fixed before any twin was trained.
- No proof was attempted on twins. Nothing here says trained transformers cannot be
  proved correct.

## Float versus exact arithmetic

Every theorem is about exact rational arithmetic. Nothing is proved about floats.

- Independent exact re-test (not part of the proof): each network was exported from Lean
  as exact JSON and run by a separate Python evaluator on 110 random inputs up to length
  30. **0 wrong outputs** on all 10.
- Pre-registered float32 check, 1,000 random inputs up to length 100 per net:
  **0 wrong on all 10**.
- Post hoc probe at longer lengths (20 inputs each at 300, 1,000, 2,000, 4,000): nine nets
  stay correct in float32. **The proved sort network s00 fails in float32**: 6 of 20 wrong
  at length 300 and about half wrong at 1,000 and above. It is correct in float64 at every
  length tried. Its construction separates "exactly zero" from "at least 1/n", and float32
  rounding breaks that. So a kernel-checked all-lengths theorem did not carry over to a
  float32 implementation of the same weights.

## Seeds and frozen inputs

- Pool seed 20261113 (65 parameter settings), draw seed 4043: 2 dev, 10 test, 5 reserve
  (none used). Twin seeds 0, 1, 2; evaluation seeds in `tools/train_seq_twin.py`.
- Frozen prompt and framework hash and the twin-trainer hash are in PREREG_R2.md
  (amendments 3-5). Dev pilot (not a result): 4 of 4.

## Limits

- **Blindness is weak.** Sort has only 3 parameter settings and add only 2, so those four
  test cases are not blind draws. For parity and dyck only the parameters are blind.
- **The architecture was built for the tasks.** Average-hard attention, a BOS token and
  eight position features (including i², 1/(i+1), (-1)^i, 1/n) are what the known
  constructions need. It is not softmax attention and not a standard transformer.
- **The lane's own worked example** (accept when a token occurs) shows the proof pattern
  and the lemma kit. It is outside the four families, but it lowers the difficulty.
- **n = 10**, one model, one prompt, small alphabets (2-9 tokens).
- **Compute incidents** (no effect on any submission, all in the run log (not released)): the doctor memory reservation
  and then the service memory reservation were preempted mid-run and re-granted; two doctors waited
  about 11 minutes for the service. One 12-second Lean check was run outside a memory reservation by
  mistake during smoke testing. Twin training ran under a manually managed memory reservation because
  the memory reservation wrapper hides the folder that holds numpy.
- Doctors' scratch-script memory was again not captured by the child-memory log (the
  doctors wrote almost no helper scripts at this rung; scratch folders are empty or small).

## How to check a case

    python tools/check.py runs/rung2-test/net/p05      (under a memory reservation)

Per-case records: `results/rung2-test.json`. Twins: `results/seq-twins-test.json`.
Float probe: `results/rung2-float-probe.json`.
