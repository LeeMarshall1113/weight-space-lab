# this study, rung 5 results: softmax transformers proved correct at every length, over a weight ball, in binary32 arithmetic

Run 2026-11-13 8:50 pm to 2026-11-14 3:45 am EST. Pre-registration `PREREG_R5.md` (commit
f8ec809; amendments 1 to 3; freeze 4d1dddb). Counts come from the checker's attempt logs
and the study team's numeric checks, not from doctor reports. Rows: `results/rung5-test.json`.

## Headline (pre-registered wording)

**12 of 12 written softmax transformers kernel-checked correct at every length in exact
arithmetic and up to 65,535 tokens in binary32 arithmetic (stated operation order, exp
accuracy assumed), for every weight setting within 0.5% (relative); non-counting tasks
only.**

Pass bar was 6 of 12 with at least 2 families; kill bar 2 or fewer. Passed.

## What is proved for each of the 12 networks

Three Lean theorems per network, standard axioms only (propext, Classical.choice,
Quot.sound), no `native_decide` (0 attempts in any arm):

1. **The statement**: for every rounding function meeting `Rnd u η M fl` (relative error
   u ≤ 2^-24 plus underflow term η ≤ 2^-149, guaranteed only for arguments of magnitude
   at most M), every float exponential meeting `ExpM u η ex`, every relative weight
   perturbation of at most 1/200, and every input whose position count n has
   u·n ≤ 1/256, η·n ≤ 2^-100 and 2^40·n² ≤ M: the output is within 1/4 of the target.
2. **`exact_all_lengths`** (derived by the study team's `Final.lean`): exact real arithmetic
   with the real exponential, every input length, every weight setting in the ball.
3. **`binary32`** (derived likewise): any arithmetic that agrees, on the finite range,
   with a round-to-nearest onto the binary32 grid (subnormals included); any float
   exponential within 4·2^-24 relative plus 2^-149; inputs of at most 65,535 tokens.

Because the model promises nothing beyond the largest finite float, each proof also
shows that no operation overflows. Supporting framework theorems, kernel-checked:
binary32 round-to-nearest satisfies the model (`Lane4/Bin32.lean`), the softmax lemma
and the rounded-sum lemma (`Lane4/RSoftKit.lean`).

## Table

| arm | proved | carry | last | first | induct | submissions (median) | proof lines (median) |
|---|---|---|---|---|---|---|---|
| softmax net (Sonnet) | **12/12** | 3/3 | 3/3 | 3/3 | 3/3 | 2 to 10 (4) | 529 to 2,026 (810) |
| prog control (Sonnet) | 12/12 | 3/3 | 3/3 | 3/3 | 3/3 | 1 to 5 (1.5) | 31 to 251 (43.5) |

No Fable agent. Dev pilot (not results): 3 of 4; the induct dev case failed after 7
submissions. In the test arm the three induct cases passed at submissions 5, 10 and 10
of 12, with proofs of 1,812 to 2,026 lines: close to the submission limit. Doctor cost,
net arm: 208k to 570k tokens and 14 to 64 minutes per case.

## Lane checks on the 12 proved networks (numeric, no proof)

Tolerance 0.25. Radius τ = 1/200.

| id | family | blocks | heads | width | largest written weight | inside ball, worst | breaks at | float32 stated order, worst to 65,534 tokens | PyTorch stated order vs numpy: differing outputs | ordinary PyTorch, worst | float32 at 200,000 tokens |
|---|---|---|---|---|---|---|---|---|---|---|---|
| c04 | carry | 1 | 1 | 8 | 100 | 0.075 | 8τ | 0.055 | 142 of 9,576 | 0.055 | exact to 2e-9 |
| c15 | carry | 1 | 1 | 8 | 50 | 0.088 | 4τ | 0.050 | 0 of 9,582 | 0.050 | exact to 2e-9 |
| c18 | carry | 1 | 1 | 10 | 50 | 0.109 | 4τ | 0.070 | 0 of 9,576 | 0.070 | exact |
| f14 | first | 1 | 1 | 6 | 120 | 0.035 | 8τ | 0.045 | 0 of 9,594 | 0.045 | exact |
| f28 | first | 1 | 1 | 8 | 48 | 0.025 | 16τ | 0.025 | 0 of 9,594 | 0.025 | exact |
| f29 | first | 1 | 1 | 7 | 40 | 0.035 | 8τ | 0.045 | 0 of 9,588 | 0.045 | exact |
| i00 | induct | 2 | 1, 2 | 14 | 1,024 | 0.094 | 4τ | 0.066 | 0 of 9,594 | 0.066 | not run |
| i02 | induct | 3 | 1, 0, 2 | 12 | 300 | 0.128 | 4τ | 0.132 | 0 of 9,588 | 0.132 | not run |
| i12 | induct | 2 | 3, 3 | 16 | 150 | 0.076 | 4τ | 0.055 | 0 of 9,576 | 0.055 | not run |
| l06 | last | 1 | 1 | 6 | 40 | 0.045 | 8τ | 0.045 | 0 of 9,570 | 0.045 | exact to 3e-7 |
| l10 | last | 1 | 1 | 6 | 40 | 0.045 | 8τ | 0.045 | 0 of 9,588 | 0.045 | exact to 3e-7 |
| l37 | last | 1 | 1 | 6 | 40 | 0.045 | 8τ | 0.045 | 0 of 9,570 | 0.045 | exact to 2e-7 |

1. **No contradiction with any theorem.** Inside the ball (80 perturbations per network,
   lengths 6 to 2,000, float64) the worst output is 0.128 from its target.
2. **The ball is not vacuous.** Every network leaves the tolerance at 4 to 16 times the
   radius (median 4 to 8). A search, so true limits may be smaller.
3. **binary32 in the stated order (numpy float32):** worst 0.132 at 1,000, 16,000 and
   65,534 tokens, sampled positions, written weights and 5 corner perturbations at τ.
4. **The PyTorch module's stated-order forward pass** gives bit-identical outputs to
   numpy on 11 of 12 networks. **On c04 it does not: 142 of 9,576 outputs differ.**
   Post hoc diagnosis (not pre-registered): on a re-run the differing outputs are values
   near 2e-9 that differ by one unit in the last place (largest difference 2.2e-16), and
   numpy's and PyTorch's float32 `exp` return different results on 39% of 2,000,001
   sampled arguments (largest relative difference 1.9e-7). So the two implementations
   are both instances of the theorem's `ExpM` hypothesis but not the same function, and
   bit identity was the wrong thing to pre-register. The pre-registered check is
   reported as failed on one network.
5. **Ordinary vectorised PyTorch (`torch.softmax`, matrix products)**, outside the
   theorem: worst deviation equal to the stated-order pass on every network to three
   decimals.
6. **The exp hypothesis** (amendment 1), 200,001 arguments: worst ratio to the allowed
   error 0.83 for numpy 2.5.4 and 0.50 for torch 2.15 CPU. It holds on the sample, with
   little slack for numpy. It is an assumption of the `binary32` corollary, not a
   theorem.
7. **Beyond the theorem:** the nine one-block networks are still correct in float32 at
   200,000 tokens with written weights. Multi-block networks were not run there.

## What changed against rung 4, and what did not

- Changed: softmax instead of hard attention; a rounding model with underflow and a
  range bound, satisfied by binary32 with a kernel-checked lemma; overflow excluded by
  each proof; a PyTorch module whose forward pass follows the stated order.
- Not changed: the four task families (new settings), the relative ball with zeros
  fixed, the tolerance, the length bound of 65,535 tokens in float arithmetic.

## The float-versus-exact gap, as it now stands

- Proved: binary32 `+ − × ÷` on finite values (any round-to-nearest, subnormals), no
  overflow, the stated operation order.
- Assumed: the accuracy of the float `exp` (IEEE does not fix it). Tested on a sample.
- Outside the theorem: fused multiply-add, SIMD or pairwise summation orders,
  `torch.softmax` itself, signed zeros and the bit encoding. The ordinary PyTorch pass
  matched numerically but is not covered.

## What this does not show (limits)

- **The kit does the hard analysis.** Doctors never reason about exponentials or
  rounding of sums: two kit lemmas (`soft_near`, `soft_zeros`) and a worked example carry
  that. The finding is that the softmax and float analysis can be packaged so that a
  model can assemble proofs from it; it is not that the model can do float analysis.
  The four kit lemmas were themselves proved by Sonnet agents from the study team's
  statements and hints, each within 2 submissions.
- **Non-counting tasks only**, the same four families as rung 4, chosen by the study team.
- **Relative ball; zeros stay exactly zero.** These networks are not expected to survive
  additive noise at long lengths (the rung-4 ones do not; `writeup/NOTE_2x2_results.md`),
  and that was not measured here.
- **The PyTorch object is the study team's own small module** (position features 1, i, n in
  the residual stream, no layer norm), not `nn.TransformerEncoder`.
- **The plain-code control passed 12 of 12 with proofs about one eighteenth as long**
  (median 43.5 lines against 810). The networks add nothing practical over a verified
  program.
- **Induct was near the limit**: two of three cases used 10 of 12 submissions.
- 12 cases, one model, one radius, one tolerance, score slope fixed by the kit at 16.
- Novelty rests on a web search over abstracts and project pages (`NOVELTY.md`, rung-5
  section): Yang, Strobl, Chiang and Angluin, and C-RASP, prove soft-attention
  simulation by hand in exact arithmetic; TorchLean has a bit-level float32 in Lean.

## Process notes

- **Memory incident.** At 2:30 am the study team's check job was killed by the machine's
  memory guard at 16.3 GB under a 3 GB reservation (commit 98%): the ordinary-PyTorch path built a
  65,534 x 65,534 matrix on the first two-block network. Fixed (chunked path, an
  in-process 2.5 GB guard), recorded as amendment 3, reported to the coordinator.
  Six networks had been checked before the kill; the other six were checked after it.
- All Lean runs and doctor batches under memory reservations. The service reservation was sized to
  end before another lane's reserved start during the kit phase, and released early.
- Four checker rejections in the prog arm (a `def` below the PROOF marker).
