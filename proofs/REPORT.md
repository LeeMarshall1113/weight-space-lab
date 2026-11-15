# LLM-Written Transformer Weights with Lean-Checked Proofs: Workflow, Perturbation Measurements and Open Problems

Personal work. Views are my own.

Living technical report, version 0.9 (2026-11-14). It is corrected in public: see "How to correct us" and the changelog.

Maintainer: GitHub handle `LeeMarshall1113` (display name to be added by the maintainer).

## Abstract

Small transformers whose weights and Lean 4 proofs were both written by LLM agents were checked by the Lean kernel. At rung 2, ten hard-attention networks are proved correct at every input length in exact arithmetic. At rung 4, eleven of twelve are proved within tolerance at every length for every relative weight change of at most 0.5%, under a rounding model valid up to 65,535 tokens; at rung 5, twelve of twelve softmax networks are proved under a binary32 model with a 1/200 relative ball. Counting tasks (parity, Dyck, sort) are excluded from these theorems. For parity networks and every token-blind network, it is kernel-checked that the correct relative radius shrinks like 1/n, an effect that is known in general form; the conjecture for the whole architecture is open. A plain verified program solves the same tasks with proofs a tenth to a twentieth as long, so no practical advantage is claimed. The earlier "fragile versus robust" contrast is withdrawn: additive and relative perturbations are different tests. The report lists its known weaknesses, what was not re-run, and how to correct it.

This document is a record of what was built and measured: small transformers (hard attention at rungs 2 to 4, softmax attention at rung 5) whose weights and Lean 4 proofs were written by LLM agents, and what happens to those networks under weight perturbation and rounding. It is kept up to date; the known weaknesses are listed first, before any result, and corrections are invited (see "How to correct us"). The document's own file is `REPORT.md`. All other paths are relative to `lane4-proof/`. The title still fits: hard attention and softmax are both covered, and no claim is made about standard trained transformers.

**One pre-registered check failed (rung 5).** The PyTorch module's stated-order forward pass was required to be bit-identical to numpy on every network. It is on 11 of 12; on `c04`, 142 of 9,576 outputs differ. Post hoc diagnosis: one unit in the last place on values near 2e-9, and numpy's and PyTorch's float32 `exp` differ on 39% of 2,000,001 sampled arguments. The check is reported as failed on one network (claims row 22, Section 6.5).

**A necessary radius for the parity networks (rung 6b, added in version 0.8), and whose phenomenon it is.** For the three proved rung-2 parity networks it is now kernel-checked that no relative weight ball of radius 1/(2L − 1) or more is correct up to input length L (claims rows 24 and 25, Section 6.6). The phenomenon is not ours: Hahn and Rofin [HR24] prove, for soft-attention encoders with layer norm, that transformers computing highly sensitive functions such as parity sit at sharp points of parameter space, with an average-case sharpness bound in the limit of long inputs and small perturbations, and they recall that Chiang and Cholak's parity construction [CC22] is fragile in one parameter. What is added here is narrow: a worst-case statement with an explicit constant, checked by the Lean kernel, for specific written networks with hard attention and for a restricted class. The first statement we registered for it was false and was corrected by a dated amendment after the first proof attempt found the fault. Version 0.9 adds the class form (rung 6c, rows 26 to 28, Section 6.7): for every network of the rung-2 architecture that reads tokens only through global uniform averages, a condition decided by evaluating a Boolean on the weights, no relative ball of radius 1/L or more is correct for parity or sort rank up to odd length L. Five of our ten proved rung-2 networks satisfy the condition. This is still Hahn and Rofin's effect, in a worst-case, explicit and machine-checked form for one decidable class.

## Claims

Each row is one claim, stated once, with its status and where to check it. File names given without a folder (`RESULTS_R5.md`, `PREREG_R6C.md`, `NOVELTY.md`, ...) are in `docs/`; `Lane4/`, `runs/`, `results/`, `tools/`, `scratch/` and `writeup/` are folders of this directory. Status values: kernel-checked in Lean; measured (numeric screen); analysis, not proved; conjecture; not proved; assumed; not established.

| # | Claim | Status | Where to check |
|---|---|---|---|
| 1 | Ten rung-2 networks (3 parity, 3 Dyck, 2 sort, 2 addition) are correct at every input length in exact arithmetic, for the written weights only. | kernel-checked in Lean | `runs/rung2-test/net/*` (`Spec.lean`, `Final.lean`, `Solution.lean`); `results/rung2-test.json`; Section 6.1; Appendix A |
| 2 | Changing one weight of any of the ten rung-2 networks by an absolute 1/1000, written zeros included, breaks the network; eight of ten still break at 10^-6. Seven of the ten witnesses have input length 2. | measured (numeric screen); the witnesses were confirmed with an exact rational evaluator in Python, not in Lean. Rung-2 arrays are loaded through float32 and cast to float64 in the screen | `results/r3-2x2.json`, `results/r3-transformers.json`; Section 3.3 |
| 3 | The cells of the 2x2 (Table 1): additive versus relative perturbation, for the ten rung-2 and eleven rung-4 networks, with long inputs reported per length (100 and 1,000). Each cell is a finite search outcome ("a break was found for N of M networks", "no break found"), not a property of the networks. | measured (numeric screen) for the counts (version 2, `results/r3-2x2-v2.json`; the version-1 pooled counts are superseded); **kernel-checked in Lean for three individual witnesses**: (a) rung-2 sort network `s00` with one MLP weight multiplied by 1 + 1/200 outputs 1 where the correct output is 2 on the one-token input `[2]`; (b) rung-2 addition network `a00` with every non-zero weight multiplied by 1 ± 1/200 is at least 1/2 from the correct digit at position 99 of a 100-token carry chain; (c) see row 8. The counts as a whole are not Lean-checked | `runs/witness/r2rel_s00`, `runs/witness/r2long_a00` (`Final.lean`: `witness`); counts in `results/r3-2x2-v2.json`; `writeup/NOTE_2x2_v2.md`; Section 3.3 |
| 4 | For 11 of 12 pre-registered rung-4 tasks, one Lean theorem states that a written hard-attention transformer is within 1/4 of the integer target at every position, at every input length in exact arithmetic, for every relative weight perturbation of at most 1/200 (zeros stay exactly zero), and, under the stated rounding model, for up to 65,535 input tokens. The twelfth case, `i03`, is a fail (no submission; in the release copy it has no `Solution.lean`). | kernel-checked in Lean | `runs/rung4-test/net/<id>/Spec.lean` and `Final.lean`; `Lane4/RSeq.lean`; Sections 2.4, 6.3; Appendix A |
| 5 | The rung-4 theorems hold for any `fl` meeting the hypothesis `Rounding u fl`; the hypothesis is taken as given. | assumed | `Lane4/RSeq.lean` (`Rounding`); Section 2.3 |
| 6 | 11 of the 12 rung-4 net-arm cases are kernel-checked (carry 3, last 3, first 3, induct 2). The twelfth, `i03`, produced no submission because the agent crashed, twice; it is counted as a fail and never as a success. | kernel-checked in Lean | `results/rung4-test.json`; `runs/rung4-test/net/`, `runs/rung4-test/net-rerun/i03` (Spec, Final, TASK, case.json; no Solution); Section 6.3 |
| 7 | A plain verified program (the control arm) solved 12 of 12 rung-4 cases and 10 of 10 rung-2 cases, with a median proof of 54 lines against 559 at rung 4. The control proves a different, exact statement. | kernel-checked in Lean | `runs/rung4-test/prog/*`, `runs/rung2-test/prog/*`; Tables 4 and 5 |
| 8 | In the float64 screen, a break was found for all eleven rung-4 networks under additive 1/1000 on every entry (output bias included) at length 1,000, and for 8 of 11 at length 100 (11 of 11 at the theorem's 1/4 tolerance at both lengths). Under relative noise within the ball no break was found. | measured (numeric screen) for the counts; **kernel-checked in Lean for one witness**: rung-4 carry network `c14` with every weight (zeros and output bias included) moved by ±1/1000 is more than 1/4 from the target at position 19 of a stated 22-token input, in exact arithmetic (output about 1.739, target 2). This is one finite-radius failure of one network, not the universal statement `LastNoAbsBall` | `runs/witness/r4abs_c14` (`Final.lean`: `witness`; uses the rational mirror and bridge theorem of `Lane4/QRSeq.lean`); counts in `results/r3-2x2-v2.json`; Section 3.3 |
| 9 | Numeric checks on the eleven proved rung-4 networks found no output beyond the theorem's tolerance inside the ball, and in this search every network leaves the tolerance at 2 to 16 times the proved radius. | measured (numeric screen) | `results/rung4-test.json`, `runs/rung4-test/net/<id>/r4_checks.json`; Table 6, Section 6.4 |
| 10 | Real float32 forward passes of the eleven networks stayed within 0.119 of the target at 1,000, 16,000 and 65,534 tokens (sampled positions at the larger sizes); six one-block networks gave exact outputs at 200,000 and 2,000,000 tokens with written weights. | measured (numeric screen) | `results/rung4-test.json`; Table 6, Section 6.4 |
| 11 | Rung-2 sort network `s00` gave wrong outputs in float32 at lengths 300 to 4,000 (6 to 10 of 20 inputs) and none in float64. The cause was not diagnosed. | measured (numeric screen) | `results/rung2-float-probe.json`; Table 2, Section 3.4 |
| 12 | Counting tasks (parity, Dyck, sort) have no length-independent relative ball; the radius shrinks like 1/n. (Version 0.8: for the three written parity networks this is now a theorem, rows 24 and 25. Version 0.9: for every token-blind network, parity and sort rank, rows 26 to 28. For the architecture as a whole, and for Dyck, it stays a conjecture.) For parity the statement is a precise Lean conjecture with the architecture class fixed (`Lane4.Conj.ParityNoBall`, type-checked only, not proved). For Dyck and sort there is no Lean statement, only an informal expectation. The argument that one k/n channel misdecodes does not cover networks that encode counts another way. | conjecture; not proved | Section 4.1, Table 3; `Lane4/Conjectures.lean`; `writeup/NOTE_open_problems.md` section 1 |
| 12b | In the rung-4 architecture no network has a length-independent ABSOLUTE ball for a non-counting task (stated for the last-marked task). Three mechanisms are listed; they are not a proof. | conjecture; not proved. Precise Lean statement `Lane4.Conj.LastNoAbsBall`, type-checked only; the witness of row 8 is one finite-radius failure of one network, not an instance of the universal statement | `Lane4/Conjectures.lean`; `writeup/NOTE_open_problems.md` section 2 |
| 12c | With positions as a relative-position score bias (not in the residual stream) and a clipped-ReLU content gate on the candidate set, non-counting tasks would have a length-independent absolute ball. One hand-built network was probed numerically (`results/r6-probe.json`; the probe's columns are not a like-for-like length sweep, see the open-problems note, section 3); nothing was proved. | analysis, not proved | `writeup/NOTE_open_problems.md` sections 2 and 3 |
| 13 | The rung-4 rounding hypothesis `Rounding u fl` is satisfied, with `u = 2^-24`, by a rounding that is not the identity: every odd round-to-nearest onto the 24-bit grid with exponents unbounded in both directions (binary32 without its exponent limits) satisfies it, and such a rounding exists and moves 2^24 + 1. (`fl = id` satisfies `Rounding u fl` for every u, so mere satisfiability was never in doubt; this non-identity witness is the meaningful one.) | kernel-checked in Lean | `runs/r5-kit/kR` (`Spec.lean`: `FLX`, `IsRNX`, `RnxRounding`, `RnxExists`) |
| 13b | Real binary32, with its exponent limits, satisfies the rung-4 model `Rounding u fl` on the operations a rung-4 network performs. | not established | False in general: binary32 violates a purely relative bound in the subnormal range and overflows above the largest finite number. It holds for a run in which no exact result is subnormal or overflows; that has not been proved for the rung-4 networks. The rung-5 model (row 19) is a different model with an underflow term and a range bound, and covers rung 5 only. Section 2.3, Section 2.5 |
| 14 | We did not find a transformer with a proof-assistant theorem that specific weights compute a task at every length for every weight setting in a stated ball, or about a rounded forward pass at very long lengths. Scope: web search of abstracts, summaries and a few project pages, 2026-11-11 to 2026-11-14. | not established | Section 1 (abstract-level search only) |
| 15 | At rung 1, ReLU MLPs for 20 of 20 specifications, and at rung 3, networks for 12 of 12 specifications over an absolute ball, were kernel-checked (background). | kernel-checked in Lean | `results/rung1-test.json`, `results/rung3-test.json`; Section 6.2 |
| 16 | Trained twins did not match the written networks: of 30 rung-2 trained twins, all ten seed-0 twins were wrong at some longer length, but only 2 of 30 were 100% correct at the training lengths, so the contrast mostly reflects a small, untuned trainer; at rung 1 a trained twin arm reached 17 of 20. No proof was attempted on twins. | measured (numeric screen) | `results/seq-twins-test.json`, `results/twins-test.json`, `results/r3-twins-test.json`; Sections 6.1, 6.2 |
| 17 | At rung 3, an adversarial search broke δ at 4 to 32 times the proved radius; fine-tuning inside the ball beat a frozen program on 11 of 12 networks, but a post hoc affine correction with three or four constants captured 98% to 100% of the same shift. | measured (numeric screen) | `results/rung3-test.json`, `results/r3-posthoc-affine.json`; Section 6.2 |
| 18 | Rung 5: for 12 of 12 pre-registered tasks, one Lean theorem states that a written SOFTMAX transformer is within 1/4 of the integer target at every position for every relative weight perturbation of at most 1/200, with two kernel-checked corollaries: exact real arithmetic at every input length, and binary32 (the model of Section 2.5) for up to 65,535 tokens. Non-counting tasks only. | kernel-checked in Lean | `runs/rung5-*` (`Spec.lean`, `Final.lean`, `Solution.lean`), `results/rung5-test.json`, `RESULTS_R5.md`, `PREREG_R5.md`; Section 6.5 |
| 19 | Binary32 round-to-nearest (any tie rule, subnormals included) on the finite range satisfies the rung-5 rounding model `Rnd 2^-24 2^-150 maxF`. | kernel-checked in Lean | `Lane4/Bin32.lean` (`bin32_rnd`); Section 2.5 |
| 20 | The accuracy of the float exponential (`ExpM`: within 4u times the true value plus an underflow term) is a hypothesis of the rung-5 binary32 corollary. On 200,001 arguments numpy 2.5.4 used 83% of the allowance and torch 2.15 CPU 50%. | assumed (measured on a sample) | `results/r5-exp-check.json`; `PREREG_R5.md` amendment 1; Section 6.5 |
| 21 | Rung-5 numeric checks on the twelve proved networks: inside the ball the worst output is 0.128 from the target; the tolerance is left at 4 to 16 times the radius; float32 stated-order worst 0.132 at up to 65,534 tokens; ordinary vectorised PyTorch equal to the stated-order pass to three decimals. | measured (numeric screen) | `RESULTS_R5.md`; Section 6.5 |
| 22 | Rung-5 bit-identity check: the PyTorch module's stated-order forward pass equals numpy bit for bit on 11 of 12 networks and **does not on `c04`** (142 of 9,576 outputs differ). | measured; **the pre-registered check failed on one network** | `RESULTS_R5.md`; `PREREG_R5.md` amendment 3; Section 6.5 |
| 23 | Rung-5 plain-code control: 12 of 12 solved, median proof 43.5 lines against 810 for the networks. The control proves a different, exact statement. | kernel-checked in Lean | `RESULTS_R5.md`; Section 6.5 |
| 24 | Collision bound (rung 6b). For every counting-parity task with wanted parity 0 or 1 and every rung-2 network with a count channel (one decoder D and, for every |d| ≤ 1, a network within relative distance |d| whose last-position output is D(n, (1+d)·k/n)): if every network in the relative ball of radius τ ≤ 1 is correct up to length L ≥ 2, then τ·(2L − 1) < 1. The class is semantic; membership is a theorem per network. | kernel-checked in Lean | `Lane4/Collision.lean` (statements); `runs/r6b/kColl2`; `PREREG_R6.md` with amendment 1; `RESULTS_R6B.md`; Section 6.6 |
| 25 | The three proved rung-2 parity networks p05, p10, p29 (the exact network text of row 1) have a count channel. Hence, for each: a relative ball correct up to length L has radius below 1/(2L − 1), and no positive radius is correct at every length. One weight is moved; the measured full-ball threshold is about 1/(8L). | kernel-checked in Lean (memberships by Sonnet agents; the two corollaries derived by us and compiled) | `runs/r6b/m05`, `m10`, `m29` (`Spec.lean`, `Solution.lean`, `_Corollary.lean`: `member`, `radius`, `noBall`); `results/r6-collision-sanity.json`; Section 6.6 |
| 26 | Token-blind class (rung 6c). `tokenBlind N ntok T` is a Boolean function of the weights: tokens are read only through heads with a zero score matrix and mask `all`; no other score, value, MLP first-layer or read-out entry touches the token coordinates T. `Invariance`: two variants of a token-blind network that differ only in embedding entries on T give equal outputs at every position on any two valid inputs of equal length with equal column sums of embedded tokens on T. `Collision`: for τ ≤ 1 with 1 ≤ τ(2a+1) and 1 ≤ τ(2b+1), two networks in the relative ball give equal outputs at every position on s^a o^(b+1) and s^(a+1) o^b. | kernel-checked in Lean | `Lane4/TokenBlind.lean` (statements); `runs/r6c/iHead`, `iBlock`, `iNet`, `cColl`; `runs/r6c/final/R6C.lean`; `PREREG_R6C.md`; `RESULTS_R6C.md`; Section 6.7 |
| 27 | `ParityBound` and `SortBound`: a token-blind network whose relative ball of radius τ ≤ 1 is correct for a counting-parity task, or for sort rank, up to length 2a+1 has τ(2a+1) < 1. The constant is the same for every network of the class. | kernel-checked in Lean | `runs/r6c/cBounds`; `runs/r6c/final/R6C.lean` (`parityBound`, `sortBound`); Section 6.7 |
| 28 | The proved rung-2 networks p05, p10, p29, s00, s01 (exact network text of row 1) are token-blind, each by the single tactic `decide`; hence for each the radius bound of row 27 for its own task and "no positive radius is correct at every length". The other five proved rung-2 networks (three Dyck, two addition) are not token-blind, and each is not permutation-invariant even unperturbed. | kernel-checked in Lean for the five memberships and their corollaries; the statement about the five non-members is measured (exact rational evaluation in Python) | `runs/r6c/members/Members.lean`; `runs/r6c/final/R6C.lean` (`Lane4.Member.*.member`, `radius`, `noBall`); `results/r6c-statement-test.json`; Section 6.7 |

## Known weaknesses and open questions

**A pre-registered rung-5 check failed.** See the box at the top of the report and claims row 22. The check was the wrong one (two correct float32 `exp` implementations need not agree bit for bit), but it is reported as failed, not replaced. The theorem's `exp` hypothesis covers both implementations; it does not make them equal.

**The rung-5 kit carries the softmax and float analysis.** Doctors never reason about exponentials or the rounding of sums: two kit lemmas (`soft_near`, `soft_zeros`) and a worked example carry that. The rung-5 result is about packaging that analysis so that a model can assemble proofs from it. It is not a result that the model does float analysis. The four kit lemmas were themselves proved by Sonnet agents from our statements and hints, each within 2 submissions.

**Rung 5 was close to the limit on induct.** Two of the three induct cases used 10 of 12 submissions (the three passed at submissions 5, 10 and 10); proofs run to 2,026 lines. Our own check job was killed once for memory by the machine's memory guard and fixed (`PREREG_R5.md` amendment 3). The PyTorch object is our own small module, not `nn.TransformerEncoder`. The rung-5 networks were not screened under additive noise.

**The 2x2 took away the earlier framing, and its first version had two errors.** An earlier draft contrasted rung-2 networks that break when one weight moves by an absolute 1/1000 with rung-4 networks proved against a relative 1/200, and called the first fragile and the second robust. The perturbations differ: the additive one moves entries written as exactly 0, which these constructions use to create exact ties; the relative one never touches them. The "fragile versus robust" framing is withdrawn. The 2x2 is a finite float64 search over different task sets, generators, evaluators and break criteria. It supports statements of the form "a break was found for N of M networks in this search" and "no break found"; it does not show that any network is robust, or that every perturbation breaks. An independent read (version 0.6, points 4 and 5) found that version 1 of the screen (a) pooled lengths 100 and 1,000 in one Boolean, and (b) left the rung-4 output bias out of the perturbed arrays. Version 2 (`tools/r3_2x2_v2.py`, `writeup/NOTE_2x2_v2.md`) fixes both; no network-level count changed for (b), and the per-length counts differ from the pooled ones (Table 1). What remains: the rung-4 theorems give stability to relative noise with zeros fixed at every length, where in this search the rung-2 constructions lost it as inputs grew; neither set is robust to additive noise.

**Relative versus absolute ball.** The rung-4 ball is relative: a weight written as 0 stays exactly 0 under every perturbation and under rounding. That is weaker than the absolute ball of rung 3 and does not cover additive noise or pruning. In the float64 screen a break was found for all eleven rung-4 networks under additive 1/1000 on every entry at length 1,000 and for 8 of 11 at length 100; 2 of 11 (5 of 11 at the 1/4 tolerance) already break at short lengths. A perturbed zero entry reads position features that grow with length; this is a candidate mechanism, not an established cause.

**Rounding model versus IEEE arithmetic.** Two models. Rung 4: `Rounding u fl` has a purely relative error bound, is monotone, idempotent and odd, and is exact on integers up to 2^24. Real binary32 violates a relative bound in the subnormal range. Not modelled: overflow, underflow, fused multiply-add, reordered or vectorised sums, softmax. `fl = id` satisfies `Rounding u fl` for every u, so satisfiability was never in doubt; the meaningful witness is a non-identity nearest-rounding on the 24-bit grid with unbounded exponents (`runs/r5-kit/kR`). There is no such lemma for rung 4's model on binary32 with its exponent limits: row 13b stays "not established" for rung 4. Rung 5 uses a different model (`Rnd u η M fl`: relative error plus underflow term, only inside a range) and has a kernel-checked lemma that binary32 round-to-nearest satisfies it; Section 2.5 states exactly what that covers and what it does not (fused multiply-add, reassociated sums, hardware and library conformance, the accuracy of `exp`). The length bound 65,535 tokens is a sufficient condition from u·(length+1) ≤ 1/256, not a measured failure threshold.

**Plain code solves the same tasks with proofs a tenth to a twentieth as long.** The control arm solved all 12 rung-4 cases (median 54 lines against 559), all 12 rung-5 cases (median 43.5 lines against 810) and all 10 rung-2 cases. The arms prove different statements. The result concerns what can be proved of weights, not useful transformers.

**Task choice and the pass bar.** The task families were chosen by us knowing which mechanism works. No task needs counting. The pass bar was low (6 of 12). The tasks were easy for the model with the kit: 11 of 12 at a median of 2 submissions at rung 4. The kit, its exact-zero lemmas, the task advice and the worked example supplied part of the proof; the agents supplied the penalty score (Section 4.2). The draw was blind only within the chosen families.

**Depth of the novelty search.** The search was a web search over abstracts, summaries and a few project pages; no article was read in full. In review, several wrong references were found and removed (Section 1 and the changelog). "Not found" is weaker than "does not exist".

**The failed case `i03`.** The agent died after about 70 minutes with an API error before submitting anything, and a fresh agent on an untouched copy died the same way. In the release copy `runs/rung4-test/net/i03` has Spec, Final, TASK and case.json but no Solution and no passing attempt. It counts as a fail and is never counted as a success. Whether an agent that does not crash would prove it was not measured.

**Task encodings were not published in the report; they are now (Appendix A).** `Spec.lean` is the definition of each task. A reader should read it, not the informal description next to it. In the samples read by the independent reviewer no vacuous hypothesis, reversed quantifier or trivial tolerance appeared; that was a read of sampled statements, not an audit of every statement.

**Model version string not recorded.** The agents were the Claude Sonnet model served under the alias `sonnet` in Claude Code between 2026-11-11 and 2026-11-14. The result files do not record a version string.

**Pre-registration is not independently verifiable.** The pre-registration commits and their timestamps are in a private repository and cannot be checked independently. No independently timestamped commitment was made. What a reader can check is that the frozen files reproduce the stated sha256 hashes (Section 5) and the results. Reproducibility of the frozen files and evidence of prior registration are different claims; only the first is offered. A hash disclosed now does not show that the file existed before the agents ran.

**The sort float32 failure is asserted, not diagnosed.** The probe was post hoc, with 20 inputs per length. No analysis of which score rounds wrongly was done.

**The 2x2 is a float64 screen with small long-length samples.** There are 2 inputs per long length and 50 sign-corner perturbations; "no break found" is not a proof of anything. Three individual cells have Lean-checked witnesses (`runs/witness/r2rel_s00`, `r2long_a00`, `r4abs_c14`); the counts as a whole do not. The counts are not monotone in length (Section 3.3), so they cannot be read as a growth law.

**The rung-6c class is permutation-invariant by construction.** It covers networks that read tokens only through global averages (5 of our 10); a network that reads tokens positionally is not covered, Dyck and addition are not covered, and the conjecture for the whole architecture is open. See Section 6.7.

**The rung-6b lower bound is narrow and its phenomenon is known.** It covers networks with a count channel, proved for three networks of one construction, moving one weight; Hahn and Rofin [HR24] established the general effect for standard soft-attention transformers. The first registered statement was false (a missing hypothesis) and was amended after the first proof attempt; the counterexample is an agent's hand argument. See Section 6.6.

**What the clean recheck covers.** `VERIFY.md` records a re-check of every Lean file in this folder from a clean clone, against a Mathlib build that was not re-downloaded. It shows that the recorded proofs are accepted by the kernel against the recorded statements. It does not re-run the agents, the numeric scripts or the export step, and it does not show that the statements say what this report says.

## How to check this in 15 minutes

1. **See what one theorem says.** Read three files for one case, for example `runs/rung4-test/net/c14/`:
   - `Spec.lean`: the task (`target(w, i)`, the token alphabet) and the `Statement` definition (`Rounding u fl`, `u ≤ 1/16777216`, `p.Within (1/200)`, `u * (length + 1) ≤ 1/256`, tolerance `1/4`). Appendix A reproduces it.
   - `Final.lean`: `theorem final : Statement net`, and the shape theorem.
   - `Lane4/RSeq.lean`: the definitions of `Rounding`, `Pert`, `Pert.Within`, `TNet.out` and the lemma kit. Together with the Lean kernel these definitions are the trusted base. The agent's `Solution.lean` need not be read.
2. **Get the tools.** Install the Lean toolchain named in `lean-toolchain` (`leanprover/lean4:v4.35.0-rc3`) and fetch Mathlib at the revision in `lake-manifest.json` (`c55e6e786f49471c72fbddbec5415808896aec1e`, input revision `v4.35.0-rc3`): `lake update && lake exe cache get`. Mathlib is not in the folder. `tools/check.py` does not use `lake`; it points `LEAN_PATH` at the Mathlib package oleans of the checkout and reads two environment variables: `LANE4_LEAN` (the `lean` executable) and `LANE4_MATHLIB_PROJECT` (the folder holding `.lake/packages`). See `README.md`, "Setup".
3. **Compile the framework once.** Nothing to do by hand: the checker builds the framework modules a case needs, in dependency order (`Basic`, `Seq`, `RSeq`), when an olean is missing or older than its source (`DEPS` in `tools/check.py`). The first check therefore takes a few minutes longer.
4. **Re-check one proof.** Run `python tools/check.py runs/rung4-test/net/c14`. The checker scans `Solution.lean` for banned tokens (comments stripped; among them `sorry`, `admit`, `axiom`, `native_decide`, `ofReduceBool`, `unsafe`, `extern`, `import`, `instance`, `opaque`, `partial`). It concatenates `import Lane4.RSeq`, `Spec.lean`, `Solution.lean` and `Final.lean` into `_Full.lean`, runs the Lean kernel, and requires exit code 0, no `sorry`, and axioms of the two final theorems within `propext`, `Classical.choice`, `Quot.sound`. A pass prints `PASS  c14  kernel-checked`. Defaults: 600 s time-out, 4.5 GB memory kill. Lean took about 26 seconds for the passing attempt in the recorded log. The control arm is checked the same way on `runs/rung4-test/prog/c14`.
5. **Re-run one numeric screen.** The 2x2, version 2: `tools/r3_2x2_v2.py`, on the exported networks (`net.json` in each passing case folder). Compare with `results/r3-2x2-v2.json` and `writeup/NOTE_2x2_v2.md`; the version-1 script took about nine minutes on our machine. The rung-4 checks: `tools/r4_checks.py` (numpy), producing `r4_checks.json` per case; compare with `results/rung4-test.json` (Table 6). `tools/export_r4.py` exports a network from Lean to `net.json`, and so needs the Lean setup of step 2. Memory and time needs of the scripts were not measured.

Steps 2 to 4 were run on a clean clone for `VERIFY.md` (with a Mathlib build that was already present, not re-downloaded). Step 5 (the numeric scripts) was not re-run for the release. Rung 6a is not included.

## How to correct us

Issues and pull requests are wanted for any of the following.

- A proof statement that does not say what the text claims (a flaw in `Spec.lean`, `Final.lean`, `Lane4/RSeq.lean` or `Lane4/RSoft.lean`).
- Prior work we missed or misdescribed.
- A counterexample: an input, a weight setting inside the ball, or a rounding function meeting `Rounding u fl` (or `Rnd u η M fl`), for which a proved network is wrong.
- A numeric result that does not reproduce.
- A better framing.

Corrections are recorded in the changelog with a date and credit. Nothing is silently edited. Use the issue templates of the repository (`CONTRIBUTING.md`).

## 1. Related work

**Theory.** Hahn [Hahn20] studies what self-attention can compute on formal languages, for both soft and hard attention, and reports that it cannot model periodic finite-state languages or hierarchical structure unless the number of layers or heads grows with input length. We attribute no specific margin statement to that article. Chiang and Cholak [CC22] build on Hahn's lemma and show ways to overcome the limitation on PARITY and FIRST. Merrill and Sabharwal relate log-precision transformers to constant-depth threshold circuits [MS23a] and to first-order logic with majority quantifiers [MS23b]. None is machine-checked or about written weights, and the s00 float32 failure is not derived from any of them (Section 3.4).

**Verification of transformer programs.** Jiang, Hague, Rümmer and Lin [JHRL26] verify C-RASP programs at unbounded length through Lustre model checkers, and learn such programs from examples: programs, not weights, no proof assistant. Yang and Chiang [YC24] prove by hand (not mechanised) that C-RASP compiles to softmax transformers; Yang, Strobl, Chiang and Angluin [YSCA24] study, mathematically (not mechanised) and in exact arithmetic, when soft attention can simulate hard attention (the score-gap idea of rung 5 is theirs). Tracr [Tracr23] compiles RASP to weights without mechanised correctness. Gross et al. [GAKOYGNC24] give computer-assisted proofs about a small transformer trained on Max-of-K.

**Lean and transformers.** Sasha Rush's "Lean Verified Transformers" [Rush26] (human-written text, AI-written proofs) formalises transformer blocks in Lean over exact rationals with a "softmax-like" normalisation (1 + relu, divided by the sum; no exponential). Its theorems are about equivariance and invariance (permutation equivariance of attention layers and transformer blocks, batch invariance, tensor and data parallelism), for arbitrary weights and, as we read the page, for every sequence length. It has no theorem that a network computes a specific task, no weight ball and no rounding. So Lean theorems about transformer blocks at all lengths already exist; the claim here concerns task correctness of specific written weights, over a weight ball, with a rounding model. The repository `teal-sea/lean-checked-network` [Lince26], read through its README only, reports that AI coding agents wrote its proofs: a trained one-layer, four-head softmax transformer adds modulo 113 on all 12,769 input pairs (integer weights, exact real softmax, enumeration over a finite domain), a constructed network adds modulo any p at least 3, a trained recurrent adder is proved for every length by induction, and ACAS Xu network 1_1 property 1 is checked over its input box. It has no weight ball and no rounding model. TorchLean [TorchLean26] gives Lean 4 network semantics and describes Lean certificate checking and binary32 semantics (a bit-level float32 model; ours is an operation-level model, Section 2.5); Browne, Lee and Salvi [BLS26] have an agent prove GPU kernels correct in Lean over floats (kernels, not weights); Somani [Somani26] checks a GPT-2 circuit on 1,280 fixed prompts with solvers. Other LLM-writes-weights work has no proofs [Singh26, Trimm26].

**Adjacent, added 2026-11-14.** The LeanCert documentation [LeanCert] (page "Neural networks"; GitHub `alerad/leancert`; no authors or date on the page) says that component soundness theorems for interval propagation through MLP layers and ReLU and sigmoid relaxations are proved in Lean; for attention the page says public theorem coverage is "structural rather than a full elementwise enclosure". It is adjacent: it is not an all-length task theorem or a weight-ball transformer theorem, as far as the page shows. Wesonga [Wesonga26] formalises Håstad's PARITY lower bound for bounded-depth circuits in Lean; it is about circuits and says nothing about transformers. It is a possible foundation for a parity lower bound here, not a reduction for this architecture. Both were read as pages, not as full articles or repositories.

**Weight-ball certificates and floating point.** Weng et al. [Weng20] certify weight-perturbation regions for trained ReLU networks with numerical bounds (its AAAI page refused automated access on 2026-11-14 and was not re-opened; the entry was verified on 2026-11-13); Elmecker-Plakolm et al. [EFSTW26] certify a parameter region and keep fine-tuning inside it. Jin et al. [JOR24] and Szász et al. [SBJ25] show that real-arithmetic robustness certificates can fail under floating-point execution; Murray [Murray26] gives a Rocq-mechanised Lipschitz certification that bounds floating-point deviation; FloatLib [FloatLib26] gives verified floating-point arithmetic in Lean 4. The float32 observation here is a known kind of phenomenon, and the weight-ball idea is not claimed.

**The narrow claim and its caveat.** The search was a web search over abstracts, summaries and a few project pages, 2026-11-11 to 2026-11-14; no article was read in full. We did not find a transformer with a proof-assistant theorem that a specific set of weights computes a task at every length for every weight setting in a stated ball, or about a rounded forward pass at unbounded or very long lengths. That is the only novelty claim, restated in the light of [Rush26], and "not found" is weaker than "does not exist" (claim 14, status "not established").

## 2. Setting and model

### 2.1 Architecture

Networks are written in fixed Lean 4 frameworks. **Rung 2 (exact):** rational weights and arithmetic. The framework prepends a BOS token (token 0) at position 0, so an input of `len` tokens occupies positions 1 to `len` and `n = len + 1`. The state at a position is the token's embedding row followed by eight position features (including i, i², n, 1/n). A head scores key j from query i by the bilinear form x_i · (A x_j); attention is **average-hard**: among the allowed positions (masks `all`, `causal` j ≤ i, `strict` j < i), those with the maximal score share the weight equally, and the head adds the average of V x_j over them. A block is its heads (residual) then a one-hidden-layer ReLU MLP (residual); at most 4 blocks, 4 heads, state width 24, MLP width 32. The read-out is affine. This is not softmax and not the standard architecture. **Rung 4 (perturbed, rounded):** the same shape over the reals, with three position features `[1, fl(i), fl(n)]`, the same size limits, and every weight perturbed and every operation rounded as below. Test-set networks had state width at most 15. **Rung 5:** the rung-4 shape with softmax attention in a stated order of operations (Section 2.5); test-set networks had at most 3 blocks and width at most 16.

### 2.2 The weight ball

A perturbation assigns a real d to every weight (embeddings, attention score and value matrices, MLP weights and biases, read-out). The weight used is `fl(w · (1 + d))`, where `w` is the written rational. The ball is **relative**: radius τ means every |d| ≤ τ. We use τ = 1/200. A weight written as 0 stays exactly 0 under every perturbation and under rounding. τ was chosen from a hand calculation on our own carry construction (error about 0.11 against the tolerance 1/4; about 0.22 at 1/100), is one value for all cases, and was not tuned on agents' results. The contrasting **absolute (additive)** perturbation, used in Section 3, adds ±τ to every moved entry, written zeros included.

### 2.3 The rung-4 rounding model, and what we do not have for it

`Rounding u fl` (in `Lane4/RSeq.lean`) says that `fl : ℝ → ℝ` has relative error at most u (|fl x − x| ≤ u|x|), is monotone, idempotent and odd, and is exact on integers up to 2^24. Every multiplication, addition and division is rounded, sums run left to right, and stored weights and position features are rounded. With u = 0 this is exact arithmetic.

Four points. (a) The rung-4 theorems assume `Rounding u fl` as a hypothesis. `fl = id` satisfies `Rounding u fl` for every u, so mere satisfiability was never in doubt. The meaningful witness is a non-identity one: a kernel-checked lemma added in version 0.5 (`runs/r5-kit/kR`) shows that a round-to-nearest on the 24-bit grid with unbounded exponents satisfies it with u = 2^-24 and is not the identity. (b) Real binary32 does not satisfy a purely relative error bound in the subnormal range, where the absolute spacing of numbers is fixed. The model is therefore an idealisation without underflow; it also leaves out overflow, fused multiply-add, reordered or vectorised sums, and softmax. There is no lemma that binary32 with its exponent limits satisfies it on a rung-4 forward pass (row 13b, not established). (c) The link between the model and a real float32 run is the numeric checks of Section 6.4, which found no failure, not a proof. (d) The length condition u·(length+1) ≤ 1/256 gives at most 65,535 input tokens at u = 2^-24; it is a sufficient condition for the proof, not a measured failure threshold. Rung 5 replaces the model by one with an underflow term and a range bound (Section 2.5).

### 2.4 The theorem (rung 4)

For a task with integer target `target(w, i)` in 0..3 and a written network `net`:

```
for all u, fl with Rounding u fl, 0 ≤ u ≤ 2^-24,
for all perturbations p with every |d| ≤ 1/200,
for all inputs w with tokens in 1..V and u · (len(w) + 1) ≤ 1/256,
for all positions i in 1..len(w):
    | net.out(fl, p, w, i) − target(w, i) | ≤ 1/4
```

With u = 0 the length condition is vacuous: exact arithmetic, **every input length**, every weight setting in the ball. With u = 2^-24, `u · n ≤ 1/256` gives n ≤ 65,536, that is at most 65,535 input tokens. "Input tokens" is used throughout; the rung-4 result files say "65,535 positions", but the Lean condition allows 65,535 input tokens (65,536 positions with BOS), and the Lean condition is the authority. One theorem covers both ends; a case counts only if all of it is checked. A second theorem, that `net` meets the shape limits, is also required. The statement file is ours; the proof is the agent's.

### 2.5 Rung 5's float model, and exactly what it covers

The rung-5 framework (`Lane4/RSoft.lean`, `Lane4/RSoftKit.lean`) replaces `Rounding` by `Rnd u η M fl`. It assumes, only for |x| ≤ M: |fl x − x| ≤ u·|x| + η, `fl` monotone, `fl` idempotent; and `fl k = k` for integers k ≤ 2^24. It assumes nothing for |x| > M. So a proof from the model cannot use an operation whose exact result leaves the range; each proof must show that every intermediate stays inside it (no overflow). Exact arithmetic satisfies it with u = η = 0.

`Lane4/Bin32.lean` (kernel-checked) proves that any function agreeing, on |x| ≤ maxF, with a round-to-nearest onto the binary32 grid (subnormals included, any tie rule) satisfies `Rnd` with u = 2^-24, η = 2^-150 and M = maxF = (2^24 − 1)·2^104. The binary32 corollary of each case uses η = 2^-149 (a weaker model, from the 2^-150 one by `rnd_weaken`; `PREREG_R5.md` amendment 1).

*Covered by the rung-5 theorems.*
- Each multiplication, addition, subtraction and division is the rounding of the exact result.
- Dot products and sums run left to right with every multiply and add separately rounded.
- The softmax in the stated order: m = largest score; e_j = ex(fl(s_j − m)); Z and the weighted sums accumulated left to right with every addition rounded; one division. Zero weights contribute an exact zero; an empty candidate list gives 0.
- Stored weights are `fl(w(1 + d))`.
- Position features are `fl i` and `fl n`, exact for the lengths covered.
- No overflow, because the model promises nothing beyond M and each proof bounds every intermediate.

*Assumed, not proved.* The accuracy of the float exponential (`ExpM u η ex`: nonnegative, `ex 0 = 1`, and for x ≤ 0 within 4u·e^x + η of e^x). Checked on a sample of arguments (row 20).

*Not covered.* Fused multiply-add; reassociated, pairwise or vectorised sums; signed zeros and the bit encoding (identified, not modelled); NaN and infinities (shown not to arise); real hardware or library conformance (`torch.softmax` itself is outside the theorem); and anything about rung 4's own model beyond the idealised witness of row 13. The rung-4 row 13b stays "not established".

## 3. The 2x2 perturbation measurement

### 3.1 Why it was run

An earlier draft contrasted two numbers: rung-2 networks break when one weight moves by an absolute 1/1000, while rung-4 networks are proved against all weights moving by a relative 1/200. An independent review pointed out that these perturbations differ, as described under "Known weaknesses". The two missing cells were measured after a note stating our expectations (`writeup/NOTE_2x2_prestated.md`) and before looking at results. Version 1 is `tools/r3_2x2.py` with rows in `results/r3-2x2.json` and `writeup/NOTE_2x2_results.md` (kept, superseded). Version 2 (2026-11-14) is `tools/r3_2x2_v2.py`, `results/r3-2x2-v2.json`, `writeup/NOTE_2x2_v2.md`; it fixes two errors found by the second independent read (output bias omitted from the rung-4 perturbed arrays; lengths 100 and 1,000 pooled into one Boolean). Same seeds, inputs and criteria.

### 3.2 Design and criteria

Networks: the ten proved rung-2 transformers (3 parity, 3 Dyck, 2 sort, 2 addition) and the eleven proved rung-4 transformers. Perturbations: ABS (additive ±1/1000, zeros included; at rung 4 the output bias is included in version 2) and REL (`w(1 + d)`, |d| = 1/200, zeros fixed, so only nonzero entries move: 7 to 36 per network, against 102 to 1,986 under ABS). Float64, no rounding model. Rung-2 arrays are loaded through float32 and cast to float64 (`collect2_lib.float_params`); rung-4 weights go from exact rationals to float64. Three screens per cell:

1. **One entry, short inputs.** Every entry, both signs; 8 inputs at each of lengths 2, 3, 5, 8, 13, 20. Report how many networks have a break found.
2. **All entries, short inputs.** 200 random sign-corner perturbations (every entry moved by plus or minus the size), same inputs.
3. **All entries, long inputs.** 50 random sign-corner perturbations, 2 inputs at each of lengths 100 and 1,000, **reported per length**.

**Break criteria** (from the docstring of `tools/r3_transformers.py`): for classification tasks (parity, Dyck), a wrong sign at the last position; for sequence tasks (sort, addition and all rung-4 tasks), some output at least 1/2 away from the target, because exact equality cannot survive any perturbation. For rung-4 networks the theorem's own tolerance (some output more than 1/4 away) is also reported. "No break found" is a statement about what a finite search found.

### 3.3 Results

*Table 1. Networks with at least one break found in each cell (float64 screen, version 2; N of 10 rung-2 or 11 rung-4 networks).*

| | ABS, one entry, short | ABS, all entries, short | ABS, all entries, length 100 | ABS, all entries, length 1,000 | REL, one entry, short | REL, all entries, short | REL, all entries, length 100 | REL, all entries, length 1,000 |
|---|---|---|---|---|---|---|---|---|
| rung 2 (10 networks) | 10 | 10 | 10 | 10 | 1 | 1 | 8 | 8 |
| rung 4 (11 networks) | 0 | 2 | 8 | 11 | 0 | 0 | 0 | 0 |

Superseded (version 1, lengths 100 and 1,000 pooled; one Boolean per corner for the four inputs, so "at length 100 or 1,000"): rung 2 ABS 10, REL 9; rung 4 ABS 11, REL 0. These pooled numbers must not be read as "at each length".

At the rung-4 theorem's 1/4 tolerance, ABS on all entries finds a break for 5 of 11 rung-4 networks at short lengths (named in version 1: c07, c14, f05, i09, i10), 11 of 11 at length 100 and 11 of 11 at length 1,000; REL: none in any column.

*Reading each cell.* Each statement is about this search.

- **Rung 2, ABS.** A break was found for all ten on a single entry at 1/1000 and at lengths up to 20 (the rung-3 screen, reproduced), and for all ten at each long length. Eight still break at 10^-6, the smallest size tried (the two addition networks break at 10^-4 and not at 10^-5 in the float64 screen). Witnesses were confirmed with an exact rational evaluator (the float64 screen loaded weights through float32; witnesses are exact). The witness inputs have length 2 for seven networks (d10, d15, d18, p05, p10, s00, s01), 5 for p29, and 13 and 20 for the two adders; for the three Dyck networks and several others the entry is `A0_0[0,0]`, an attention-score entry. Breaking entries per network: 3 and 6 (addition), 64 to 75 (parity, Dyck), 127 and 184 (sort). A break at length 2 from an entry perturbed by 10^-6 is an exact-tie failure: a score matrix written as zero produces a tie, uniform averaging follows, and any additive change breaks the tie. It is not a vanishing-margin effect, and the first draft's "margins of order 1/n" does not explain Table 1.
- **Rung 2, REL.** At lengths up to 20, a break was found only for the sort network s00 (5 single entries; 87 of 200 corners). At length 100 a break was found for 8 of 10 and at length 1,000 for 8 of 10, not the same eight: a01 only at 1,000 (48 of 50 corners), d18 only at 100 (3 of 50), d15 at neither (pooled, 9 of 10). Where breaks were found they are often many corners (for example 48 of 50 for a01 at 1,000). The difference between short and long inputs is consistent with a margin that shrinks with length; the screen does not identify the cause or a rate. Our pre-stated guess was that several would survive short lengths and parity and Dyck would break long. It was roughly right, but a break was also found for addition and sort at long lengths.
- **Rung 4, REL.** No break found anywhere, at either tolerance. This is inside the proved ball, where a break would contradict a theorem.
- **Rung 4, ABS.** No single entry breaks any network at short lengths. At length 1,000 a break was found for all eleven (49 or 50 of 50 corners). At length 100 a break was found for 8 of 11 at the 1/2 criterion; the three `last` networks (l11, l25, l38) have none in 50 corners (11 of 11 at the 1/4 tolerance). The two induct networks (1,986 entries each) already break in 5 and 4 of 200 all-entries corners at short lengths (7 and 7 in version 1; the random draws shifted by one entry once the output bias was included). Including the output bias changed no network-level count for rung 4. That a perturbed zero entry reads position features that grow with length is a candidate mechanism consistent with these results, not an established cause.
- **The counts are not monotone in length.** Under ABS, four rung-2 networks break in fewer corners at length 1,000 than at 100 (d15 33 then 18; d18 48 then 11; p05 50 then 29; p29 50 then 21). With two inputs per length this may be input sampling. These counts cannot be read as a growth law.
- **The Lean witnesses are unaffected** by either error. `runs/witness/r4abs_c14` perturbs every weight including the output bias (the changed network's `outB` is −1/1000), at length 22; `runs/witness/r2long_a00` is at length 100 exactly.

### 3.4 The float32 observation on s00

The pre-registered float32 check (1,000 random inputs up to length 100 per network) found 0 wrong on all ten. A **post hoc** probe used 20 inputs at each of lengths 300, 1,000, 2,000 and 4,000: nine networks stayed correct; the sort network `s00` did not.

*Table 2. Wrong outputs among 20 inputs, network s00 (post hoc probe).*

| Length | float32 | float64 |
|---|---|---|
| 300 | 6 | 0 |
| 1,000 | 10 | 0 |
| 2,000 | 9 | 0 |
| 4,000 | 10 | 0 |

The construction separates "exactly zero" from "at least 1/n" (as written in our rung-2 notes), and float32 rounding may break that. This is **asserted, not diagnosed**: no analysis of which score rounds wrongly was done, and the cause could equally be a tie lost in float32 sums. The probe was post hoc with few inputs per length. The only observation added is that s00 is also the one rung-2 network with a break found at short lengths under the relative perturbation.

### 3.5 Limits of the measurement

Float64 screens. Three individual cells have Lean-checked witnesses (`runs/witness/r2rel_s00`, `r2long_a00`, `r4abs_c14`); the counts as a whole have no Lean or exact-rational confirmation. Eight inputs per short length, 2 inputs per long length. Sign corners only for the all-entries screens (200 at short lengths, 50 at long). "No break found" is a finite-search outcome. The two rungs use different evaluators and input generators and solve different tasks, so cross-row comparisons are indicative. A count of corners that break is not a rate.

## 4. Constructions

### 4.1 Which tasks admit a length-independent relative ball (analysis and conjecture)

This subsection is analysis done before the experiment, not a result. With an **absolute** ball and position features that grow with length (i, i², n), a perturbed zero entry lets a unit read τ·n or τ·n²; the rung-4 measurement above (a break found for all eleven networks at length 1,000 under ABS) is consistent with this. With a **relative** ball (zeros stay zero):

*Table 3. Length-independent relative ball? (analysis; the "no" rows are conjectures)*

| Family | Length-independent? | Reason | Status |
|---|---|---|---|
| carry / addition; "nearest or first earlier position whose token is in a set"; "previous occurrence of the current token"; latch-like tasks | yes, with the right mechanism | need only a nearest or first earlier position of some kind; no counting. Rungs 4 and 5 prove this for the written networks | kernel-checked for the written networks (rows 4, 18) |
| parity | conjectured no, radius ~1/n | in the constructions written here, the count k is the average k/n; a relative error d on a value weight turns k into k(1+d), off by more than 1/2 once d·n > 1/2. This does not cover networks that encode counts another way (other heads, coordinates, nonlinearities, attention selections, compensating scalings) | for the three written networks: kernel-checked, radius below 1/(2L − 1) (rows 24, 25); for every token-blind network: kernel-checked, radius below 1/L at odd L (rows 26, 27). For every network of the architecture: conjecture; not proved. Lean statement `Lane4.Conj.ParityNoBall`, type-checked only |
| Dyck | conjectured no, ~1/n | needs the sign of a prefix sum that is exactly zero at balance; in the written constructions a relative error d on the +1 and −1 weights moves a balanced sum by up to 2·d·n | conjecture; not proved. No Lean statement, only an informal expectation |
| sort | conjectured no, ~1/n | needs exact counts, as parity, in the written constructions | for every token-blind network, the two written sort networks included: kernel-checked, radius below 1/L at odd L (rows 26 to 28). For networks outside the class: conjecture; not proved |

An argument that one k/n channel misdecodes under one perturbation does not show that every bounded-size network must encode counts that way. One-bit input sensitivity alone does not imply weight sensitivity, and the finite screen does not determine an asymptotic rate. Hahn's argument does not apply as it stands (`writeup/NOTE_open_problems.md`, section 1). For counting tasks the best statement would be "correct for every n and every relative perturbation up to c/n", i.e. for fixed τ, correct up to length c/τ. This was not proved, and no agents were run on these families.

Regarding floats, one remark is scoped to this model. In the rung-4 and rung-2 frameworks the position `i` enters the state as a direct float32 entry, and float32 cannot represent consecutive integers above 2^24. For a network that tells neighbouring positions apart using that entry, a float forward pass cannot be correct at every length, so the rounded statement carries a length bound. The remark is about this direct encoding of `i`; other encodings (discrete masks, token content, integer indices) can distinguish positions and are not covered by it, and no proof of the task-level consequence is offered. The all-lengths claim is about exact arithmetic with a weight ball.

### 4.2 The exact-zero penalty score, and what the agents supplied

The textbook selection score `n · flag_j + j` (a bonus for marked positions) **fails** once embeddings are also perturbed: two marked positions holding different tokens get bonuses n(1+d) and n(1+d') that differ by up to 2τn, swamping the position gap of 1.

The mirror image works: score `j − 2n · pen_j`, where the stored feature `pen_j` is written as exactly 0 on wanted positions and 1 elsewhere. All wanted positions then share the score s·j exactly up to one common factor, so the latest wins by a gap independent of the perturbation, and unwanted positions fall below every wanted one with a margin that grows with n. Query-dependent matching penalises mismatches the same way.

What the agents were given and what they supplied must be kept apart. The kit (`Lane4/RSeq.lean`) supplied the exact-zero facts (`sw_zero`: a weight written as 0 stays 0 under perturbation and rounding) and the unique-selection lemma (`Head.sel_unique`); the task file's advice said that zeros stay exactly zero, and the worked example repeats it. The worked example's score is position-only. What the agents supplied, in all eleven proved cases, was the penalty score itself. The development pilot recorded the same for its four agents (4 of 4 kernel-checked, at submissions 2, 2, 2, 1; `PREREG_R4.md`, amendment 1). The agents are therefore not said to have "found the idea unaided".

Concretely, in case c14 (a carry chain modulo 3 over a five-symbol alphabet) the agent wrote one block, one head with the `strict` mask, state width 6. The score is the key's rounded position plus −2·fl(n) times the key's stored propagate flag, written 0 for every non-propagate token. The head selects the nearest earlier non-propagate position and copies its generate flag; a one-unit ReLU MLP subtracts 3 when the sum reaches 3. The 394-line proof shows that for every allowed perturbation and rounding the head selects exactly that position. The two induct proofs that passed use one head per token, and five of the eleven networks use two blocks.

## 5. Experimental protocol

**Workflow.** For each task a fresh LLM agent (a "doctor") receives a fixed Lean framework, a lemma kit and a task file, and returns weights and a proof. We wrote the statement; the Lean 4 kernel checks the proof (standard axioms only, no `native_decide`). We did not write the proofs. Each rung was pre-registered before any agent ran on its test set, with a plain verified-program control arm.

**Pre-registration, and what is and is not offered.** `PREREG_R4.md` fixed the statement, families, seeds, arms, bars and numeric checks, and listed in advance what would make the result weak; `PREREG_R5.md` did the same for rung 5. Frozen files are recorded by sha256. Rung 4: the hash of the frozen-file list is 0d71ccfa127bbe0791eee017557c20f68beb9bf7347ed62622ca9c248877a2b1; the test-set id hash is bee0427d138132b68a071767e04617772b750ef59dda4e04d3a803ac8986c646. Rung 5: the hash of the freeze list is 49f7d5efbaabff228e72a9974ac732ec0d8bd3f87b9cd323000698104b5e3c9b; the test-set id hash is 0a40dd3c3484e137beeef985478879632bc81caf390958a52acfdc491bb137f7. The pre-registration commits and their timestamps are in a private repository and are **not independently verifiable**. No independently timestamped commitment was made. What a reader can check is that the frozen files reproduce the stated hashes and the results. Reproducibility of the frozen files and evidence of prior registration are different claims, and only the first is offered. Amendments are dated by us, and the dates are our statements.

**Task families.** Four families, tokens 1..V, each solvable by hard attention to the nearest or first position of some kind. *carry* (V 3..5, modulus 2 or 3): each token is generate, kill or propagate and has a digit; target = (digit + carry into the position) mod m. *last* (V 3..5): target = value of the last marked token at or before i, else 0. *first* (V 3..5): target = (bit of the first marked token at or before i, plus the token's bit) mod 2. *induct* (V 2..3): target = table value of the token right after the most recent earlier occurrence of the current token, else 0. The exact definitions are `Spec.lean` per case (Appendix A).

**Pool and draw.** The pool has 150 settings (40 carry, 40 last, 40 first, 30 induct; seed 20261114). Twelve settings used for our own feasibility check (c34 to c39, i24 to i29) were excluded, leaving an eligible pool of 138. The draw (seed 4045) took per family 1 development, 3 test, 2 reserve cases: 4 development and 12 test. The 12 cases run are exactly the drawn test ids, so no reserve case was used. Rung 2 drew from 65 settings (draw seed 4043): 2 development, 10 test, 5 reserve; rung 3 from 266 specifications (draw seed 4044): 2 development, 12 test, 6 reserve; no reserve case was used at either. Rung 5 used the same pool, excluding every setting drawn at rung 4 and the 12 feasibility settings (draw seed 4046): per family 1 development, 3 test, 2 reserve.

**Arms.** *net*: weights plus a proof of Section 2.4 (rung 5: Section 2.5). *prog* (plain-code control): a one-pass `List.foldl` program plus a proof that it equals the target at every length; it may use the specification's token tables, not its fold or search, and a per-case list of identifiers is banned. The control proves a different, exact statement. No trained-twin arm at rungs 4 and 5: no available trainer produces unique hard attention.

**Doctors.** The agents were the Claude Sonnet model served under the alias `sonnet` in Claude Code between 2026-11-11 and 2026-11-14; the result files do not record a version string. One fresh agent per case and arm, at most 12 submissions, 600 seconds and 4.5 GB per Lean check, at most two at once, no nested agents; one prompt for all cases at rung 4 (reused unchanged from rung 3), and the rung-3 prompt plus one sentence at rung 5. A stronger-model step was pre-registered for a net arm below the pass bar; none was needed. What doctors receive is part of the result: `Lane4/RSeq.lean` (rung 5: `Lane4/RSoft.lean` and `RSoftKit.lean`) with a lemma kit (rounding bounds, relative-error products, rounded positions, unique selection; rung 5 adds the softmax lemma and the rounded-sum lemma), one worked example outside the four families ("output the previous token", one head, no MLP, position-only score), and three sentences of advice: zeros stay exactly zero; equal written weights are not equal once stored; margins must beat a perturbation that multiplies position features.

**Checker.** `tools/check.py` scans `Solution.lean`, comments stripped, for banned tokens (among them `sorry`, `admit`, `axiom`, `native_decide`, `ofReduceBool`, `unsafe`, `extern`, `import`, `instance`, `opaque`, `partial`); concatenates `import Lane4.<framework>`, our `Spec.lean`, the agent's `Solution.lean` and our `Final.lean`; runs the Lean 4 kernel (`leanprover/lean4:v4.35.0-rc3`; Mathlib at revision `c55e6e786f49471c72fbddbec5415808896aec1e`, oleans from an external checkout) under time and memory guards; and requires exit code 0, no `sorry`, and axioms of every final theorem within the standard three (`propext`, `Classical.choice`, `Quot.sound`). At rung 4 the final theorems are the statement and the shape theorem. `native_decide` attempts are counted: none in any arm of any rung reported here.

**Bars.** S4 = number of the 12 test cases whose net-arm statement is kernel-checked by a Sonnet agent. Kill: S4 ≤ 2. Pass: S4 ≥ 6 with at least two families fully or partly solved. The pass bar was low: half the cases. Rung 5 used the same bars (S5).

**Numeric checks.** On each proved network, exported from the kernel-checked file (numpy): (1) inside the ball, float64, 60 random and 60 sign-corner relative perturbations at τ, lengths 6 to 2,000, four input patterns (uniform random; one token dominating; random head with constant tail; constant with one change), not a per-family adversarial search; any output beyond 1/4 would contradict a theorem. (2) Non-vacuity: the same at 2τ up to 64τ and lengths up to 20,000. (3) A real float32 forward pass in the framework's operation order, written weights and 5 sign-corner perturbations at τ, at 1,000, 16,000 and 65,534 tokens, with **sampled positions** (at most 1,000 query positions per input at the two larger sizes); beyond the theorem, one-block networks only, 200,000 and 2,000,000 tokens, written weights. The 2x2 of Section 3 is a separate, later measurement. Rung-5 checks are listed in Section 6.5.

## 6. Results

### 6.1 Rung 2: all-lengths proofs

Bars: kill below 5 of 10, pass at 7. Result: 10 of 10 net, 10 of 10 control, so the network adds nothing over a verified program. Our reading, stated before the test set was built: Sonnet can recall, adapt and formally verify known constructions quickly; this is not discovery of new length-general algorithms.

*Table 4. Rung 2, 10 test cases.*

| | net | prog (control) |
|---|---|---|
| Kernel-checked | 10 / 10 | 10 / 10 |
| Submissions, median (sorted) | 2 (1,1,2,2,2,2,3,3,3,4) | 2 (1,1,1,1,2,2,2,2,3,4) |
| Lean seconds, median | 26 | 11 |
| Solution lines, range | 176 to 417 | 29 to 99 |
| `native_decide` attempts | 0 | 0 |

Networks: 1 block and 1 head for both addition cases; 2 blocks and 2 to 3 heads for the rest; state width 11 to 15. Blindness is weak: the families are famous, and sort (3 settings) and addition (2) are not blind draws. Thirty trained twins were built; all ten seed-0 twins were wrong at some longer length, but only 2 of 30 were even 100% correct at the training lengths, so the contrast mostly reflects a small, untuned trainer. No proof was attempted on twins (claim 16).

### 6.2 Rungs 1 and 3, background

At rung 1, Sonnet agents wrote ReLU MLPs and kernel-checked proofs of exact equality with a specification over a box on 20 of 20 blind specifications (control 20 of 20; a trained twin arm reached 17 of 20, so no contrast was shown).

At rung 3 the ball is absolute: every weight and bias, zeros included, may move by τ = 1/1000, and for every real x in a box |net(x) − spec(x)| ≤ δ (δ = 0.20 to 0.75). On 12 of 12 specifications an agent wrote a network (1 to 4 hidden layers, width up to 9) and a kernel-checked proof; the control scored 12 of 12; net solutions ran 91 to 584 lines against 13 to 57. Our checks found no violation inside the ball, and an adversarial search broke δ at 4 to 32 times the proved radius. Fine-tuning inside the ball beat a frozen program on 11 of 12 networks, but a post hoc affine correction with three or four constants captured 98% to 100% of the same shift (claim 17). These MLP statements are about a bounded input box and say nothing about the sequence networks of Sections 3 and 6.3.

### 6.3 Rung 4

*Table 5. Rung 4, 12 test cases, 3 per family.*

| arm | proved | carry | last | first | induct | submissions, range (median) | solution lines, range (median) |
|---|---|---|---|---|---|---|---|
| net (Sonnet) | **11 / 12** | 3 / 3 | 3 / 3 | 3 / 3 | 2 / 3 | 1 to 5 (2) | 389 to 969 (559) |
| prog control (Sonnet) | 12 / 12 | 3 / 3 | 3 / 3 | 3 / 3 | 3 / 3 | 1 to 5 (2) | 31 to 235 (54) |

The pass bar was met, and it was a low bar (6 of 12); the kill bar was not. No `native_decide` attempt occurred in either arm. The control's median proof is about a tenth the length of the net arm's (54 against 559 lines). In the control arm two checker rejections were definitions below the PROOF marker.

The one net-arm miss, `i03` (induct), is a fail, not a proved case. The agent died after about 70 minutes with an API error (one response over the 128,000-token output limit) before submitting anything. In the release copy `runs/rung4-test/net/i03` and `runs/rung4-test/net-rerun/i03` have Spec, Final, TASK and case.json but no Solution and no passing attempt; it is never counted as a success (every "11 of 12" in this report excludes it). A fresh Sonnet agent on an untouched copy died the same way and is not added to any count. The other two induct cases, with the same token count, passed, so nothing marks `i03` as harder. Costs, as recorded in `RESULTS_R4.md` (they are not in the per-case result rows): 170k to 360k tokens and 10 to 70 minutes per net case; 72k to 97k tokens and under 4 minutes per control case. The development pilot (4 of 4) prompted no change.

### 6.4 Numeric checks on the eleven proved networks

Tolerance 0.25. "Break" is the smallest multiple of τ = 1/200 at which our search found an output outside the tolerance.

*Table 6. Per-case results and numeric checks (float32 columns: sampled positions).*

| id | family | blocks | width | subm. | lines | worst deviation inside ball | first multiple of τ that breaks | float32 worst, up to 65,534 tokens | float32 at 200,000 / 2,000,000 |
|---|---|---|---|---|---|---|---|---|---|
| c07 | carry | 2 | 8 | 3 | 856 | 0.131 | 4 | 0.119 | not run |
| c14 | carry | 1 | 6 | 2 | 394 | 0.111 | 2 | 0.100 | holds / holds |
| c21 | carry | 1 | 8 | 2 | 458 | 0.045 | 8 | 0.055 | holds / holds |
| f05 | first | 2 | 10 | 5 | 969 | 0.075 | 4 | 0.030 | not run |
| f08 | first | 1 | 7 | 2 | 559 | 0.045 | 8 | 0.035 | holds / holds |
| f24 | first | 1 | 8 | 3 | 611 | 0.025 | 16 | 0.025 | holds / holds |
| i09 | induct | 2 | 15 | 2 | 965 | 0.096 | 4 | 0.076 | not run |
| i10 | induct | 2 | 15 | 4 | 938 | 0.096 | 4 | 0.076 | not run |
| l11 | last | 1 | 6 | 2 | 389 | 0.045 | 8 | 0.045 | holds / holds |
| l25 | last | 2 | 6 | 2 | 416 | 0.045 | 8 | 0.045 | not run |
| l38 | last | 1 | 6 | 1 | 458 | 0.045 | 8 | 0.045 | holds / holds |

- **No contradiction with any theorem.** Inside the ball (120 perturbations per network, lengths 6 to 2,000) every output stayed within 0.131 of its target.
- **The relative ball is not vacuous.** Every network leaves the tolerance at 2 to 16 times the proved radius (median 8); this is a search.
- **Real float32, sampled positions.** Within 0.119 at 1,000, 16,000 and 65,534 tokens, on sampled query positions at the larger sizes: a spot check, not a sweep. No failure inside the theorem's range was found.
- **Beyond the theorem.** The six one-block networks still give exact float32 outputs at 200,000 and 2,000,000 tokens with written weights. Two-block networks, and perturbed one-block networks beyond 65,534 tokens, were not run.
- **Against rung 2.** Table 1 supersedes the first draft's contrast of "10^-4 against 0.5%".

The link between the rounding model and a real float32 run is these numeric checks, not a proof; a different operation order (any BLAS or GPU kernel) is outside the theorem.

### 6.5 Rung 5: softmax attention, binary32 model (added in version 0.7)

Run 2026-11-13 8:50 pm to 2026-11-14 3:45 am EST (`RESULTS_R5.md`; pre-registration `PREREG_R5.md`, amendments 1 to 3). Pass bar 6 of 12 with at least two families; kill bar 2 or fewer. Passed. Pre-registered headline: 12 of 12 written softmax transformers kernel-checked correct at every length in exact arithmetic and up to 65,535 tokens in binary32 arithmetic (stated operation order, exp accuracy assumed), for every weight setting within 0.5% (relative); non-counting tasks only.

*What is proved for each of the 12 networks.* Three Lean theorems, standard axioms only, no `native_decide` (0 attempts in any arm). (1) The statement: for every `Rnd u η M fl`, every `ExpM u η ex`, every relative weight perturbation of at most 1/200, every input whose position count n has u·n ≤ 1/256, η·n ≤ 2^-100 and 2^40·n² ≤ M, the output is within 1/4 of the target. (2) `exact_all_lengths`: exact real arithmetic, real exponential, every input length, every weight setting in the ball. (3) `binary32`: any arithmetic that agrees on the finite range with a round-to-nearest onto the binary32 grid; any float exponential within 4·2^-24 relative plus 2^-149; at most 65,535 tokens. Supporting framework theorems are kernel-checked (`Lane4/Bin32.lean`, the softmax lemma and the rounded-sum lemma in `Lane4/RSoftKit.lean`). Section 2.5 states what the model covers.

*Table 7. Rung 5, 12 test cases, 3 per family.*

| arm | proved | carry | last | first | induct | submissions, range (median) | proof lines, range (median) |
|---|---|---|---|---|---|---|---|
| softmax net (Sonnet) | **12 / 12** | 3 / 3 | 3 / 3 | 3 / 3 | 3 / 3 | 2 to 10 (4) | 529 to 2,026 (810) |
| prog control (Sonnet) | 12 / 12 | 3 / 3 | 3 / 3 | 3 / 3 | 3 / 3 | 1 to 5 (1.5) | 31 to 251 (43.5) |

No Fable agent. Development pilot (not results): 3 of 4; the induct development case failed after 7 submissions. In the test arm the three induct cases passed at submissions 5, 10 and 10 of 12, with proofs of 1,812 to 2,026 lines. Doctor cost, net arm: 208k to 570k tokens and 14 to 64 minutes per case. There were four checker rejections in the control arm (a `def` below the PROOF marker).

*Table 8. Lane checks on the 12 proved networks (numeric, no proof). Tolerance 0.25, τ = 1/200.*

| id | family | blocks | width | inside ball, worst | breaks at | float32 stated order, worst to 65,534 tokens | PyTorch stated order vs numpy: differing outputs | ordinary PyTorch, worst |
|---|---|---|---|---|---|---|---|---|
| c04 | carry | 1 | 8 | 0.075 | 8τ | 0.055 | **142 of 9,576** | 0.055 |
| c15 | carry | 1 | 8 | 0.088 | 4τ | 0.050 | 0 of 9,582 | 0.050 |
| c18 | carry | 1 | 10 | 0.109 | 4τ | 0.070 | 0 of 9,576 | 0.070 |
| f14 | first | 1 | 6 | 0.035 | 8τ | 0.045 | 0 of 9,594 | 0.045 |
| f28 | first | 1 | 8 | 0.025 | 16τ | 0.025 | 0 of 9,594 | 0.025 |
| f29 | first | 1 | 7 | 0.035 | 8τ | 0.045 | 0 of 9,588 | 0.045 |
| i00 | induct | 2 | 14 | 0.094 | 4τ | 0.066 | 0 of 9,594 | 0.066 |
| i02 | induct | 3 | 12 | 0.128 | 4τ | 0.132 | 0 of 9,588 | 0.132 |
| i12 | induct | 2 | 16 | 0.076 | 4τ | 0.055 | 0 of 9,576 | 0.055 |
| l06 | last | 1 | 6 | 0.045 | 8τ | 0.045 | 0 of 9,570 | 0.045 |
| l10 | last | 1 | 6 | 0.045 | 8τ | 0.045 | 0 of 9,588 | 0.045 |
| l37 | last | 1 | 6 | 0.045 | 8τ | 0.045 | 0 of 9,570 | 0.045 |

- **No contradiction with any theorem.** Inside the ball (80 perturbations per network, lengths 6 to 2,000, float64) the worst output is 0.128 from its target.
- **The ball is not vacuous in this search.** Every network leaves the tolerance at 4 to 16 times the radius.
- **binary32 in the stated order (numpy float32):** worst 0.132 at 1,000, 16,000 and 65,534 tokens, sampled positions, written weights and 5 corner perturbations at τ.
- **The failed pre-registered check.** The PyTorch module's stated-order forward pass is bit-identical to numpy on 11 of 12 networks. On `c04`, 142 of 9,576 outputs differ. Post hoc (not pre-registered): on a re-run the differing outputs are values near 2e-9 that differ by one unit in the last place (largest difference 2.2e-16), and numpy's and PyTorch's float32 `exp` return different results on 39% of 2,000,001 sampled arguments (largest relative difference 1.9e-7). Both implementations are instances of the theorem's `ExpM` hypothesis but not the same function, so bit identity was the wrong thing to pre-register. It is reported as failed on one network.
- **The exp hypothesis**, 200,001 arguments: worst ratio to the allowed error 0.83 for numpy 2.5.4 and 0.50 for torch 2.15 CPU. It holds on the sample, with little slack for numpy. It is an assumption of the `binary32` corollary, not a theorem.
- **Ordinary vectorised PyTorch** (`torch.softmax`, matrix products), outside the theorem: worst deviation equal to the stated-order pass on every network to three decimals.
- **Beyond the theorem.** The nine one-block networks are still correct in float32 at 200,000 tokens with written weights (exact to 3e-7 or better). Multi-block networks were not run there.
- **Process.** At 2:30 am our check job was killed by the machine's memory guard at 16.3 GB under a 3 GB reservation (commit 98%): the ordinary-PyTorch path built a 65,534 x 65,534 matrix on the first two-block network. Fixed (chunked path, an in-process 2.5 GB guard; `PREREG_R5.md` amendment 3). Six networks had been checked before the kill; the other six after it.

*What changed against rung 4, and what did not.* Changed: softmax instead of hard attention; a rounding model with underflow and a range bound, satisfied by binary32 with a kernel-checked lemma; overflow excluded by each proof; a PyTorch module whose forward pass follows the stated order. Not changed: the four task families (new settings), the relative ball with zeros fixed, the tolerance, the length bound of 65,535 tokens in float arithmetic. Limits are under "Known weaknesses" (the kit carries the analysis; induct near the limit; the PyTorch object is our own module; no additive-noise screen at rung 5; non-counting tasks only; 12 cases, one model, one radius, one tolerance, score slope fixed by the kit at 16).

### 6.6 Rung 6b: a necessary radius for the parity networks (added in version 0.8)

*Framing.* That a transformer computing parity has no weight neighbourhood that survives long inputs is known in general form. Hahn and Rofin [HR24] bound an average directional sharpness for soft-attention encoders with layer norm computing sensitive functions; their statement is a limit (long inputs, then small radius), over random perturbations of all parameters, with no explicit radius, and it is not in a proof assistant. It does not formally imply the statement below (ours perturbs relatively with zeros fixed, a measure-zero family of their directions; our model has hard attention and unbounded exact position features), but it is the same effect. This section adds a worst-case, explicit-constant, kernel-checked instance for networks whose exact correctness is also kernel-checked (row 1). We read [HR24] through its abstract and a summarising fetch of the first 100,000 characters of the HTML version; the proofs were not read.

*Statements* (`Lane4/Collision.lean`; pre-registered in `PREREG_R6.md` before any proof attempt). A task is: tokens 1..V, a set of counted tokens, a wanted parity. `OnBall N τ L`: every network within relative distance τ of N (zeros fixed) is correct on every valid input of length at most L. `CountChannel N`: there is one function D such that for every |d| ≤ 1 some network within relative distance |d| of N outputs D(n, (1+d)·k/n) at the last position of every valid input, k the count and n the number of positions. `CollisionBound`: wanted parity below 2, a counted and an uncounted token, `CountChannel N`, 0 ≤ τ ≤ 1, L ≥ 2 and `OnBall N τ L` imply τ·(2L − 1) < 1.

*Why it is true.* Take inputs of length L with L − 1 and L counted tokens, d₂ = −τ and d₁ = (1 − τL)/(L − 1). Then |d₁| ≤ τ exactly when τ(2L − 1) ≥ 1, and (1 + d₁)(L − 1) = (1 + d₂)L, so two networks in the ball give the same output on inputs of opposite parity.

*The registered statement was false.* As first registered the wanted parity was any natural number. The first agent (Sonnet) stopped after four submissions and reported a counterexample by hand: with wanted parity 2 no count qualifies, so a network with constant output −1 is correct on every ball and has a count channel. The pre-registration had named this outcome. Amendment 1 adds the hypothesis that the wanted parity is 0 or 1 and changes nothing else. A fresh agent then proved the corrected statement at its first submission. The counterexample itself is not a Lean theorem.

*Results* (`RESULTS_R6B.md`; verdicts read from the attempt records). The corrected bound: pass at submission 1. Membership of p05, p10, p29: pass at submissions 1, 2 and 4. All Sonnet, one agent at a time, standard axioms, `native_decide` not attempted. We derived and compiled, per network, `radius` (a ball correct up to length L has τ < 1/(2L − 1)) and `noBall` (for every τ > 0 some length fails). Proof sizes: 102 lines for the bound, 207 to 232 for a membership. In each membership proof the decoder is the second block's own argmax expression, so the proof never determines which position wins.

*Numeric check before proving* (exact rationals, `results/r6-collision-sanity.json`). For all three networks at L = 20, 100, 1,000: the collision pair gives equal outputs and one answer is wrong; the smallest radius with a break when only the block-1 value weight moves is 0.5000/L, against the statement's 0.513/L, 0.5025/L and 0.50025/L; when every nonzero weight on the count path moves it is about 0.125/L. Against Table 1 (relative 1/200): the statement is silent at lengths up to 20 and at 100 (1/199 against 1/200) and asserts a break at 1,000; the count-path closed form puts the first break between lengths 20 and 100. No cell contradicts.

*Limits.* A restricted class defined by the property the proof needs; membership proved per network; three networks that share one construction; one weight moved, so the bound is about four times looser than the measured full-ball threshold; relative ball, hard attention, exact rationals, parity only; the argument is elementary. `Lane4.Conj.ParityNoBall` (every network of the architecture) is untouched. A decidable class that would remove the per-network proofs and add the two sort networks is scoped, not proved (row 26, `SCOPE_R6C.md`).

### 6.7 Rung 6c: the class form (added in version 0.9)

*Framing.* As in Section 6.6: the effect is Hahn and Rofin's [HR24]; this is a worst-case, explicit, kernel-checked form of it for a decidable class. Neither formally implies the other.

*The class.* A network is token-blind for a list T of embedding coordinates when (`Lane4/TokenBlind.lean`): it has the rung-2 shape; T lies inside the embedding coordinates; all real tokens have the same embedding entry at every embedding coordinate outside T; every head either has an all-zero score matrix and mask `all`, or has no nonzero score entry in a row or column of T and no nonzero value entry in a column of T; no MLP first-layer entry and no read-out entry on T is nonzero. Depth, number of heads and the MLPs are otherwise unrestricted. It is a Boolean function of the weights and depends only on their zero pattern and on equalities between embedding entries outside T.

*Statements and proof.* `Invariance` is proved by carrying one invariant through the blocks: the two runs' states have the same length, agree outside T at every position, and have equal column sums on T. A uniform head sees T only through the column sums; every other head, every MLP and the read-out never see T. `Collision` follows by scaling the embedding rows of two tokens on T so that a(1+d₁) = (a+1)(1+d₂) and (b+1)(1+d₁') = b(1+d₂'), which is possible inside the ball when 1 ≤ τ(2a+1) and 1 ≤ τ(2b+1). The two bounds follow with a = b: the two inputs have opposite parity, and different sorted sequences at position a+1.

*Before registration* (`results/r6c-statement-test.json`, exact rationals): the condition, the invariance conclusion (30 random trials per member network with all other weights perturbed) and the collision pairs were tested on the ten proved rung-2 networks; five are members; each non-member already gives different outputs on `[1, 2]` and `[2, 1]`.

*Results* (`RESULTS_R6C.md`; verdicts from the attempt records and the compile of `runs/r6c/final/R6C.lean`). Five proof cases, each passed by the first Sonnet agent given it, at submissions 3, 1, 1, 5 and 2; 906 proof lines in all; standard axioms; `native_decide` not attempted; no amendment. The five memberships are `by decide`. We composed the four registered statements and derived `radius` and `noBall` for the five networks in one file that compiles.

*Limits.* The class is permutation-invariant by construction; networks that read tokens positionally (the Dyck and addition networks here) are outside it and `ParityNoBall` is untouched. The constant 1/L is about twice weaker than Section 6.6's for the parity networks and about eight times weaker than the measured full-ball threshold. Relative ball, hard attention, exact rationals. Five member networks from one model family and two task families. Corollaries for other count-separating targets (majority, thresholds) were not stated.

## 7. Full list of limits

Several of these are discussed under "Known weaknesses"; the list is kept whole for completeness.

1. **Non-counting tasks only.** Parity, Dyck and sort are excluded; the conjecture is that they need a ball that shrinks like 1/n (not proved). No agent was run on them.
2. **A relative ball, zeros stay exactly zero.** This is weaker than the absolute ball of rung 3 and does not cover additive noise or pruning. **The rung-4 networks are not robust to additive noise** in the float64 screen: a break was found for all eleven at length 1,000 (8 of 11 at length 100) under additive 1/1000 on every entry, and for 2 of 11 (5 of 11 at the 1/4 tolerance) at short lengths (Section 3). The rung-5 networks were not screened.
3. **The rounding statements are about models, not IEEE arithmetic.** Rung 4: a purely relative model; `fl = id` satisfies it, the only non-identity Lean witness is an idealised float without exponent limits (`runs/r5-kit/kR`), and there is no lemma for binary32 with its exponent limits (row 13b). Rung 5: a model with an underflow term and a range bound, kernel-checked for binary32 round-to-nearest, with the exponential assumed; fused multiply-add, reordered or vectorised sums, signed zeros and the bit encoding, hardware and library conformance are not covered (Section 2.5). A real float32 run is linked to the theorems only by numeric checks on sampled positions that found no failure. The rounded statements are length-bounded (65,535 input tokens, a sufficient bound, not a measured failure threshold); the all-lengths statement is exact arithmetic only.
4. **Hard attention with ties averaged (rungs 2 to 4) or softmax in a stated order (rung 5)**, in an architecture whose position features suit the tasks; not the standard PyTorch layers.
5. **Hand-written weights, not trained.** Nothing here says trained networks can or cannot be proved this way.
6. **The transformers add nothing practical over a verified program.** The plain-code control solved all 12 rung-4 cases (median 54 against 559 lines) and all 12 rung-5 cases (median 43.5 against 810). The arms prove different statements; the result is about what can be proved of weights, not about usefulness.
7. **The task families were chosen by us knowing which mechanism works**, and the pass bar was low (6 of 12). The draw was blind only within the families we chose.
8. **The tasks were easy for the model with the kit:** 11 of 12 at a median of 2 submissions at rung 4. The development pilot went 4 of 4 and we recorded then that the test arm might be near its ceiling. The kit, its exact-zero lemmas, the advice and the worked example carry part of the proof. At rung 5 the kit also carries the softmax and float analysis.
9. **Twelve cases per rung, one model, one radius, one tolerance**, width at most 16, one prompt. How success scales with network size was not measured; proofs already reach 2,026 lines.
10. **The one failed rung-4 case was an agent crash, not a failed proof.** `i03` produced no submission; a rerun died the same way; it counts as a fail. Whether an agent that does not crash would prove it was not measured.
11. **The novelty claim rests on a search of abstracts** (Section 1); "not found" is weaker than "does not exist".
12. **The model version string was not recorded.** We know the alias (`sonnet`) and the dates, not the version.
13. **The 2x2 is a float64 screen**, with 2 inputs per long length and 50 sign-corner perturbations; its counts have no exact confirmation as a whole (three individual cells have Lean-checked witnesses), and "no break found" means only that (Section 3.5).
14. **The float32 failure of sort network s00 is from a post hoc probe** of 20 inputs per length, and its cause is asserted, not diagnosed.
15. **Pre-registration is not independently verifiable.** Commits and timestamps are private and no independently timestamped commitment exists; only reproducibility of the frozen files is offered (Section 5).
16. **One pre-registered rung-5 check failed** (bit identity on `c04`).
17. **Rung 5: two of three induct cases used 10 of 12 submissions; our check job was killed once for memory and fixed; the PyTorch object is our own module.**
18. **The recheck is of kernel acceptance only** (`VERIFY.md`): the agents, the numeric scripts and the export step were not re-run for the release.

Further points. The theorems are only as good as `Spec.lean`, `Final.lean` and `Lane4/RSeq.lean` (rung 5: `Lane4/RSoft.lean`), which we wrote and the kernel does not check against intent (Section 8). Rung-3 τ and δ were chosen by us after a calibration. Our submit tool showed only the tail of Lean's output, and three doctors lost a submission to errors hidden behind linter warnings.

## 8. What to read to trust a statement

The kernel checks that a proof proves a statement; it does not check that the statement says what we mean. To trust a rung-4 result, read these files and no others:

1. **`Lane4/RSeq.lean`**: the definitions of `Rounding`, `Pert`, `Pert.Within`, the forward pass (`net.out`) and the kit. Everything the theorems mean is defined here. For rung 5 read `Lane4/RSoft.lean` (the model `Rnd`, `ExpM`, the softmax order) and the header of `Lane4/Bin32.lean`.
2. **Per case, `Spec.lean`**: the task, i.e. `target(w, i)` and the token alphabet. This is the definition of the task; Appendix A reproduces the ones cited here with a plain description beside each, but the file governs.
3. **Per case, `Final.lean`**: the final theorem statement (Section 2.4) and the shape theorem.

The agent's `Solution.lean` need not be read: the checker (Section 5) requires that the final theorems have only the standard axioms and that banned tokens are absent.

The smoke tests (`smoke4`, run before the pre-registration freeze) cover: both worked examples pass; a deliberately wrong weight, a `native_decide` and a banned `take` are rejected; the four development specifications compile and their `target` agrees with a Python reference on 15 inputs each. They do not cover: a network that is wrong for some weight setting inside the ball failing the theorem (the "break at 2 to 16 times the radius" results lie outside the ball); or `Spec.lean` matching the intended task on the test cases. They did not cover whether `Rounding u fl` has any instance for u > 0; that is now answered by `fl = id` (trivially) and by `kR` (non-trivially), Section 2.3.

The result is about proof automation over weights. A kit plus an LLM can discharge these proofs in about two submissions at rung 4 and about four at rung 5; the plain-code control does the same tasks with much shorter proofs. It is not a result about useful transformers.

## 9. Where this stands

Agents wrote transformer weights and Lean proofs for 11 of 12 pre-registered rung-4 tasks (hard attention) and 12 of 12 rung-5 tasks (softmax attention) that do not require counting. The rung-4 proofs hold at every length in exact arithmetic for every relative weight setting within 0.5%, and under a modelled rounding up to 65,535 input tokens; the rung-5 proofs hold at every length in exact arithmetic and, for binary32 in a stated operation order with the exponential's accuracy assumed, up to 65,535 tokens. One pre-registered rung-5 check (bit identity of PyTorch against numpy) failed on one network. The rung-4 networks are not robust to additive noise at long lengths in the float64 screen (a break found for 11 of 11 at length 1,000 and 8 of 11 at length 100); the rung-5 networks were not screened; the rung-4 rounding model's only non-identity Lean witness is a float without exponent limits, and rung 5's model leaves out fused multiply-add, reassociated sums and hardware conformance; and a plain verified program does the same tasks with much shorter proofs. In the float64 screen, additive noise that also moves written zeros broke all ten rung-2 networks with one entry, mostly at input length 2 (an exact-tie failure); relative noise of 1/200 with zeros fixed broke 8 of 10 at length 100 and 8 of 10 at length 1,000 (9 pooled), consistent with a margin that shrinks with length, which the screen does not establish. Open items: counting tasks with a radius c/n (conjecture), an absolute-ball statement (conjecture), a rounding statement for real IEEE operations beyond the rung-5 model, trained weights, and the corrections that readers send.

## Appendix A. Task encodings

`Spec.lean` is the definition of each task; the one-line descriptions below are ours and are only a reading aid. Text is copied from `runs/rung2-test/net/<id>/Spec.lean` and `runs/rung4-test/net/<id>/Spec.lean`. Framework definitions (`N.out`, `Pert`, `Rounding`, `tokAt`) are in `Lane4/Seq.lean` and `Lane4/RSeq.lean`. Token 0 is BOS; the input `w` has tokens from 1; position `i` is 1-based.

**Rung 2, `p05` (parity).** Tokens 1..4, nonempty. Output at the last position is positive iff the number of tokens in {1, 3, 4} is even.

```
def Valid (w : List ℕ) : Prop := w ≠ [] ∧ ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4
def inS (t : ℕ) : Bool := t == 1 || t == 3 || t == 4
def Good (w : List ℕ) : Prop := (w.countP inS) % 2 = 0
def Statement (N : TNet) : Prop :=
  ∀ w : List ℕ, Valid w → (0 < N.out w w.length ↔ Good w)
```

**Rung 2, `s00` (sort).** Tokens 1..2, nonempty. At every position i the output is exactly the value t that is the i-th smallest token of w (fewer than i tokens are below t, and at least i are at most t).

```
def Valid (w : List ℕ) : Prop := w ≠ [] ∧ ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2
def IsRank (w : List ℕ) (i t : ℕ) : Prop :=
  w.countP (fun s => decide (s < t)) < i ∧ i ≤ w.countP (fun s => decide (s ≤ t))
def Statement (N : TNet) : Prop :=
  ∀ w : List ℕ, Valid w → ∀ i, 1 ≤ i → i ≤ w.length →
    ∃ t : ℕ, N.out w i = (t : ℚ) ∧ IsRank w i t
```

**Rung 2, `a00` (addition).** Tokens 1..4, nonempty. Each token encodes two bits, `dA t = (t-1)/2` and `dC t = (t-1)%2`; the output at position i is exactly the sum bit (dA + dC + carry from earlier positions) mod 2, with the carry computed left to right.

```
def Valid (w : List ℕ) : Prop := w ≠ [] ∧ ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4
def dA (t : ℕ) : ℕ := (t - 1) / 2
def dC (t : ℕ) : ℕ := (t - 1) % 2
def carryOut (p : List ℕ) : ℕ := p.foldl (fun c t => (dA t + dC t + c) / 2) 0
def digit (w : List ℕ) (i : ℕ) : ℕ :=
  (dA (w.getD (i - 1) 0) + dC (w.getD (i - 1) 0) + carryOut (w.take (i - 1))) % 2
def Statement (N : TNet) : Prop :=
  ∀ w : List ℕ, Valid w → ∀ i, 1 ≤ i → i ≤ w.length → N.out w i = ((digit w i : ℕ) : ℚ)
```

**Rung 4, `c14` (carry, modulus 3).** Tokens 1..5. `cls` is 2 for token 1 (the carry passes through unchanged), 1 for token 5 (the carry becomes 1), 0 for tokens 2, 3, 4 (the carry becomes 0). `dg` is the token's digit. The target at position i is (digit of token i + carry into position i) mod 3.

```
def cls (t : ℕ) : ℕ := if t = 1 then 2 else if t = 2 then 0 else if t = 3 then 0 else if t = 4 then 0 else if t = 5 then 1 else 0
def dg (t : ℕ) : ℕ := if t = 1 then 2 else if t = 2 then 0 else if t = 3 then 1 else if t = 4 then 1 else if t = 5 then 0 else 0
def carry (p : List ℕ) : ℕ := p.foldl (fun c t => if cls t = 2 then c else cls t) 0
def target (w : List ℕ) (i : ℕ) : ℕ :=
  (dg (w.getD (i - 1) 0) + carry (w.take (i - 1))) % 3

def Statement (N : TNet) : Prop :=
  ∀ (u : ℝ) (fl : ℝ → ℝ), Rounding u fl → 0 ≤ u → u ≤ 1 / 16777216 →
  ∀ p : Pert, p.Within (1 / 200) →
  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) → u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 →
  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → |N.out fl p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4
```

The `Statement` of every rung-4 case has this shape; only the token bound and `target` differ.

**Rung 4, `l38` (last marked token).** Tokens 1..5. `val` maps tokens to 2, 3, 1, 0, 1 (value 0 means unmarked). The target at position i is the value of the last marked token among the first i tokens, 0 if none.

```
def val (t : ℕ) : ℕ := if t = 1 then 2 else if t = 2 then 3 else if t = 3 then 1 else if t = 4 then 0 else if t = 5 then 1 else 0
def lastv (p : List ℕ) : ℕ := p.foldl (fun s t => if val t = 0 then s else val t) 0
def target (w : List ℕ) (i : ℕ) : ℕ := lastv (w.take i)
```

**Rung 4, `f05` (first marked token).** Tokens 1..4. `code` is 0 for tokens 1 and 4 (unmarked), 2 for token 2, 1 for token 3; `cbit` is the token's bit. The target is ([the first marked token among the first i has code 2] + cbit of token i) mod 2.

```
def code (t : ℕ) : ℕ := if t = 1 then 0 else if t = 2 then 2 else if t = 3 then 1 else if t = 4 then 0 else 0
def cbit (t : ℕ) : ℕ := if t = 1 then 1 else if t = 2 then 0 else if t = 3 then 1 else if t = 4 then 1 else 0
def firstc (p : List ℕ) : ℕ := p.foldl (fun s t => if s = 0 then code t else s) 0
def target (w : List ℕ) (i : ℕ) : ℕ :=
  ((if firstc (w.take i) = 2 then 1 else 0) + cbit (w.getD (i - 1) 0)) % 2
```

**Rung 4, `i09` (induction).** Tokens 1..3. `h` maps tokens to 2, 1, 1 (else 0). The target at position i is `h` of the token right after the most recent earlier occurrence of the current token, 0 if there is none.

```
def h (t : ℕ) : ℕ := if t = 1 then 2 else if t = 2 then 1 else if t = 3 then 1 else 0
def prevOcc (w : List ℕ) (i : ℕ) : Option ℕ :=
  (List.range i).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == tokAt w i))
def target (w : List ℕ) (i : ℕ) : ℕ :=
  match prevOcc w i with
  | some j => h (tokAt w (j + 1))
  | none => 0
```

Rung 5 cases use the same four families with other settings; their `Spec.lean` files are in `runs/rung5-test/net/*/`.

## Appendix B. Toolchain and release status

**Toolchain.** Lean `leanprover/lean4:v4.35.0-rc3`. Mathlib at revision `c55e6e786f49471c72fbddbec5415808896aec1e` (input revision `v4.35.0-rc3`), recorded in `lake-manifest.json` (version 0.6 said the revision was not recorded; that is corrected). The checker invocation is in "How to check this in 15 minutes", step 4.

**What is in this folder.** Everything cited by the claims table except rung 6a, which is registered but parked and is not a result of this version: the framework files (`Lane4/`), all proof cases under `runs/` (rungs 2 to 5, the witnesses, the rung-5 kit, rung 6b and 6c), the pre-registrations and results files (`docs/`), the numeric tools and result files, and `tools/recheck_release.py`, which re-checks every Lean file. `VERIFY.md` records the last full recheck from a clean clone and its counts.

**Not included.** Rung 6a (`AGate*`, its cases, its draw and example). The doctor sessions themselves (attempt records in `runs/*/attempts/` are the verdicts, not transcripts). Mathlib.

**Historical documents.** Appendix C of this report sections dated 2026-11-13, `writeup/NOTE_2x2_results.md` (version 1) and the first-draft files are historical. Where they differ from this version, this version governs.

## References

Each entry was checked against its own web page on 2026-11-13, except [LeanCert] and [Wesonga26], opened 2026-11-14 (the AAAI page for [Weng20] refused automated access on 2026-11-14 and was not re-opened).

- [Hahn20] Michael Hahn. Theoretical Limitations of Self-Attention in Neural Sequence Models. TACL, 2020; arXiv:1906.06755 (v1 2019); DOI 10.1162/tacl_a_00306.
- [HR24] Michael Hahn and Mark Rofin. Why are Sensitive Functions Hard for Transformers? ACL 2024; arXiv:2402.09963. Opened 2026-11-14 (abstract page; HTML v4 through a summarising fetch of its first 100,000 characters).
- [CC22] David Chiang and Peter Cholak. Overcoming a Theoretical Limitation of Self-Attention. ACL 2022; arXiv:2202.12172.
- [MS23a] William Merrill and Ashish Sabharwal. The Parallelism Tradeoff: Limitations of Log-Precision Transformers. TACL; arXiv:2207.00729.
- [MS23b] William Merrill and Ashish Sabharwal. A Logic for Expressing Log-Precision Transformers. NeurIPS 2023; arXiv:2210.02671.
- [JHRL26] Hongjian Jiang, Matthew Hague, Philipp Rümmer, Anthony Widjaja Lin. Synthesis and Verification of Transformer Programs (Technical Report). arXiv:2602.16473, 2026.
- [YC24] Andy Yang and David Chiang. Counting Like Transformers: Compiling Temporal Counting Logic Into Softmax Transformers. arXiv:2404.04393, 2024.
- [YSCA24] Andy Yang, Lena Strobl, David Chiang, Dana Angluin. Simulating Hard Attention Using Soft Attention. arXiv:2412.09925, 2024 (v2 2025). No venue is shown on the arXiv page.
- [Tracr23] David Lindner, János Kramár, Sebastian Farquhar, Matthew Rahtz, Thomas McGrath, Vladimir Mikulik. Tracr: Compiled Transformers as a Laboratory for Interpretability. NeurIPS 2023 (spotlight); arXiv:2301.05062.
- [GAKOYGNC24] Jason Gross, Rajashree Agrawal, Thomas Kwa, Euan Ong, Chun Hei Yip, Alex Gibson, Soufiane Noubir, Lawrence Chan. Compact Proofs of Model Performance via Mechanistic Interpretability. NeurIPS 2024; arXiv:2406.11779.
- [Rush26] Sasha Rush (GitHub user srush). Lean Verified Transformers. https://srush.github.io/lean-transformer/ ; repository https://github.com/srush/lean-transformer. No date is shown on the page.
- [Lince26] Thomas Lince (GitHub user teal-sea). `lean-checked-network`. https://github.com/teal-sea/lean-checked-network , MIT, 2026. Read through the README only.
- [TorchLean26] Robert Joseph George, Jennifer Cruden, Will Adkisson, Xiangru Zhong, Huan Zhang, Anima Anandkumar. TorchLean: Formalizing Neural Networks in Lean. arXiv:2602.22631, 2026. Only arXiv is listed on the abstract page.
- [BLS26] Archibald Browne, Eugene Lee, Cristopher Salvi. Proving LLM-Generated GPU Kernels Correct and Safe: Floating-Point Verification in Lean and VerCors. arXiv:2610.24548, 2026.
- [Somani26] Neel Somani. Towards Verifiable Transformers: Solver-Checkable Circuit Explanations. arXiv:2605.24033, 2026.
- [Singh26] Chandan Singh (GitHub user csinva; name as given in our notes, not on the page). `weight-space-programming-autoresearch`. https://github.com/csinva/weight-space-programming-autoresearch , MIT.
- [Trimm26] Cory Trimm (GitHub user ctrimm). `weight-space-programming`. https://github.com/ctrimm/weight-space-programming , CC BY 4.0.
- [Weng20] Tsui-Wei Weng, Pu Zhao, Sijia Liu, Pin-Yu Chen, Xue Lin, Luca Daniel. Towards Certificated Model Robustness Against Weight Perturbations. AAAI 2020, vol. 34, pp. 6356-6363; DOI 10.1609/aaai.v34i04.6105.
- [EFSTW26] Leo Elmecker-Plakolm, Pierre Fasterling, Philip Sosnin, Calvin Tsay, Matthew Wicker. Provably Safe Model Updates. arXiv:2512.01899; SaTML 2026 per the arXiv comments.
- [JOR24] Jiankai Jin, Olga Ohrimenko, Benjamin I. P. Rubinstein. Getting a-Round Guarantees: Floating-Point Attacks on Certified Robustness. AISec '24; arXiv:2205.10159.
- [SBJ25] Attila Szász, Balázs Bánhelyi, Márk Jelasity. No Soundness in the Real World: On the Challenges of the Verification of Deployed Neural Networks. ICML 2025; arXiv:2506.01054.
- [Murray26] Toby Murray. Lipschitz-Based Robustness Certification Under Floating-Point Execution. arXiv:2603.13334, 2026.
- [FloatLib26] Robert Joseph George, Will Adkisson, Anima Anandkumar. FloatLib: Verified Floating-Point Arithmetic in Lean. arXiv:2609.19352, 2026.
- [LeanCert] LeanCert, documentation page "Neural networks". https://docs.leancert.io/ml/neural-networks/ ; GitHub `alerad/leancert`. No authors or date on the page. Opened 2026-11-14.
- [KSW26] Alexander Kozachinskiy, Tomasz Steifer, Przemysław Wałęga. Parity, Sensitivity, and Transformers. arXiv:2602.05896, 2026. Abstract page opened 2026-11-14. Expressivity lower bound (one layer), not perturbation.
- [Hsu26] Daniel Hsu. Lower bounds for one-layer transformers that compute parity. arXiv:2605.12171, 12 May 2026. Abstract page opened 2026-11-14.
- [VDRS26] Karthik Viswanathan, Plamen Dimitrov, Stefano Rocca, Sarayu Sirikonda. Formally Verified Autoresearch for Analyzing the Expressivity of Multi-Head Attention. NeurIPS 2026 workshop (page neurips.cc/virtual/2026/157626, opened 2026-11-14; version 0.2 of this report had dropped it as not re-found). Lean-checked head-complexity results for one-layer attention; no weight perturbation.
- [Wesonga26] Saint Wesonga. Formalizing PARITY Circuit Lower Bounds in Lean. arXiv:2609.24188, 21 September 2026. Sole author. Opened 2026-11-14.

## Changelog

Newest first.

- **0.9, abstract (2026-11-15).** An abstract was added at the top. No claim, number or status changed.

- **0.9, release copy (2026-11-14).** The release folder was synced to this version: rungs 5, 6b and 6c, the witnesses, the kit and the 2x2 tools are in; the report lives at `REPORT.md`; the "not yet in the release copy" statements were removed or rewritten; `VERIFY.md` records a clean-clone recheck of every Lean file. The word for a conventional article was dropped throughout; this is a living report. The reviewer of the second read is credited as "an independent AI reviewer".

- **0.9 (2026-11-14).** Rung 6c folded in: the class form of the necessary radius.
  - *Added.* Claims rows 26 (replacing the scoped-only row of 0.8), 27 and 28; Section 6.7; a weakness entry; the release-sync list; one sentence in the paragraph before the claims table.
  - *Changed.* Row 12 and the parity and sort rows of Table 3: kernel-checked for every token-blind network; conjecture for the architecture and for Dyck.
  - No registered statement needed an amendment at this rung.
- **0.8 (2026-11-14).** Rung 6b folded in, with Hahn and Rofin's result stated up front as the general phenomenon.
  - *Added.* The paragraph before the claims table; claims rows 24 (collision bound), 25 (membership of p05, p10, p29 and the per-network radius) and 26 (a decidable class, scoped only); Section 6.6; a weakness entry; references [HR24], [KSW26], [Hsu26], [VDRS26]; the release-sync list.
  - *Changed.* Claims row 12 and the parity row of Table 3: for the three written networks the 1/n statement is now a theorem with radius 1/(2L − 1); for the architecture it stays a conjecture.
  - *Recorded.* The statement first registered for the bound was false (the wanted parity was not restricted to 0 or 1); found by the first proof agent, corrected by `PREREG_R6.md` amendment 1 before any further attempt.
  - Point 8 of the second independent read (the collision lemma) is thereby done for the semantic class; the reviewer's caveats (a second block reading the sequence; one universal constant for all networks) still stand and are discussed in `SCOPE_R6C.md`.
- **0.7 (2026-11-14).** Response to a second independent read (12 points on version 0.6; answers in Appendix C of this report) and rung 5 folded in.
  - *Errors corrected.* (Point 4) The long-length counts of the 2x2 were pooled over lengths 100 and 1,000; Table 1 now reports each length (rung 2 ABS 10 / 10, REL 8 / 8; rung 4 ABS 8 / 11, 11 / 11 at the 1/4 tolerance; REL 0 / 0), the pooled version-1 numbers are kept in one row marked superseded, and every "at lengths 100 and 1,000" sentence (claims rows 3 and 8, the weaknesses, Section 3, Section 7 limit 2, Section 9) was replaced. Counts are not monotone in length. (Point 5) The rung-4 screen left the output bias out of the perturbed arrays; rerun as `tools/r3_2x2_v2.py` / `results/r3-2x2-v2.json` with it included: no network-level count changed. The `c14` Lean witness perturbs the bias and is unaffected. Rung-2 arrays are loaded through float32 and cast to float64 (stated). (Point 11) Hashes do not prove prior registration; the weakness and protocol sentences rewritten: commits and timestamps are private and not independently verifiable, no independently timestamped commitment was made, only reproducibility of the frozen files is offered. (Point 1, partly an error) `i03` in the release copy has no Solution and is stated as a fail wherever "11 of 12" appears; Appendix A publishes the task encodings.
  - *Overclaims corrected.* (Point 6) 2x2 cells reworded as finite-search outcomes; "This is the margin-with-length effect" is now a hypothesis; the stale "no exact confirmation of the new cells" lines (weaknesses, Section 3.5, limit 13) corrected: three cells have Lean-checked witnesses, the counts as a whole do not. (Point 7) Claim 12, Table 3, Section 4.1 and the limits list: "cannot" and "must shrink like 1/n" relabelled "conjecture; not proved"; parity's Lean conjecture kept distinct from Dyck and sort (no Lean statement). (Point 9) Claim 12b: mechanisms, not a proof; `c14` is one finite-radius failure, not `LastNoAbsBall`; the float32 remark is scoped to this model's direct float32 encoding of `i`.
  - *Gaps closed or stated.* (Point 3) New Section 2.5 states exactly what rung 5's float model covers and does not; row 13b stays "not established" for rung 4. (Point 2) `fl = id` satisfies `Rounding u fl`; the meaningful witness is `kR`; 65,535 tokens is a sufficient bound, not a measured threshold. (Point 10) LeanCert and Wesonga added as adjacent; row 14 reworded to "We did not find such a theorem", with scope and dates, status "not established". (Point 12) Lean toolchain and Mathlib revision recorded (Appendix B), the "revision not recorded" statement corrected; list of items not yet in the release copy; historical documents labelled.
  - *Added.* Rung 5 (Section 6.5; claims rows 18 to 23), including the failed bit-identity check, stated up front. New weaknesses: the kit carries the softmax and float analysis; induct near the submission limit; our check job killed once for memory; the PyTorch object is our own module; rung-5 networks not screened under additive noise. Claims row 12c updated to mention the numeric probe (no change to its status); the probe's non-like-for-like columns are caveated in the open-problems note. The status vocabulary gains "conjecture; not proved". Section 2.1, 5 and 8 extended for rung 5. Title unchanged (still accurate).
  - Not applied as suggested: none by omission. Point 8 (collision lemma for a rung-6 candidate) is recorded in `writeup/NOTE_open_problems.md`, not started.
- **0.6 (2026-11-14).** Open problems stated precisely (`writeup/NOTE_open_problems.md`, `Lane4/Conjectures.lean`): the parity no-ball conjecture with the architecture class fixed (row 12); a conjecture that the rung-4 architecture admits no absolute ball (row 12b); and an architecture change under which an absolute ball looks possible (row 12c). All three are analysis; the Lean statements only type-check. (Historical: the "conjecture" labelling of row 12 was incomplete in this version and is corrected in 0.7.)
- **0.5 (2026-11-14).** Claims row 13 split. The rung-4 rounding model now has a kernel-checked non-trivial witness (`runs/r5-kit/kR`: round-to-nearest on the 24-bit grid with unbounded exponents). Whether real binary32 with its exponent limits satisfies the model on a rung-4 forward pass stays "not established" (row 13b), with the reason stated.
- **0.4 (2026-11-14).** Three break cells of the 2x2 are now Lean theorems for stated witnesses, checked by the same checker as every other case and in the same file as the original correctness theorem of the unperturbed network: a rung-2 network wrong under a relative perturbation within 1/200 at input length 1 (`runs/witness/r2rel_s00`) and another at length 100 (`runs/witness/r2long_a00`), and a rung-4 network wrong under an additive 1/1000 on every weight at length 22 (`runs/witness/r4abs_c14`). Claims rows 2, 3 and 8 updated. The counts in Table 1 remain a float64 screen. New framework file `Lane4/QRSeq.lean`: a computable rational mirror of the rung-4 network and a kernel-checked theorem that it equals the real-valued definition in exact arithmetic. The check recipe's step 3 was corrected (the checker now builds framework modules in dependency order).
- **0.3 (2026-11-13).** Restructured as a living report. Claims table, known weaknesses (before the results), a 15-minute check recipe and a corrections section added; positioning (abstract, introduction, contribution list, conclusion) removed.
- **0.2 (2026-11-13).** Reframed after an independent review and the 2x2 measurement; the "fragile versus robust" framing withdrawn. References verified against their own pages, and several removed: arXiv 2603.20991 (is "Structural Sensitivity in Compressed Transformers", not a Lean belief-propagation transformer); arXiv 2608.10288 (is "Power law graph attention", not a Lean formalisation); the web article "Verifiable Transformers in Lean" (not found; likely a conflation); "Formally Verified Autoresearch ... Multi-Head Attention" and "Identifiability of Deep Normalized Attention" (not re-found). Other descriptions were corrected or dropped for space (Hahn, Chiang and Cholak, Merrill and Sabharwal, Yang et al., Lince README, TorchLean venue).
- **0.1 (2026-11-13).** First draft (kept as the first draft (not included)).

Later corrections get a dated entry here; nothing is silently edited.

## Appendix C. Responses to two independent reviews

The two reviews were written by independent AI reviewers (a first read on 2026-11-13 and a second on 2026-11-14). The responses follow, as written at the time, with section numbers referring to the versions then current.

### Response to the review of the second draft (not included) (2026-11-13)

**Historical.** Sections dated 2026-11-13 below answer earlier versions of the report (drafts 1 and 2, version 0.3). Where they differ from the current report (`REPORT.md`, version 0.7) or from the section dated 2026-11-14 at the end, the later text governs. Superseded on 2026-11-14: the Objection 2 statement that there is no Lean witness for the rounding model, and the "Not closed" item "Lean witness for the rounding model" (a non-identity witness exists, `runs/r5-kit/kR`; see point 2 of the 2026-11-14 section); the counts pooled over lengths 100 and 1,000 (point 4).

The first and second drafts of the report are not included in this copy. Section numbers below refer to the revision unless marked "v1". The review's section numbers (v1) map as: v1 §4 to new §4 (now the 2x2), v1 §5 to §5, v1 §6 to §6, v1 §7 to §7, v1 §8 to §8, v1 §10 to §11; new §9 ("what to read") is added.

We thank the reviewer. The largest change is that the headline framing ("proved correct but fragile versus proved and robust") is withdrawn. We ran the 2x2 the review asked for (`writeup/NOTE_2x2_prestated.md`, written before the run; `writeup/NOTE_2x2_results.md`; rows in `results/r3-2x2.json`). Nine of ten rung-2 networks survive a relative perturbation of 1/200 at lengths up to 20, and the rung-4 networks are not robust to additive noise at lengths 100 and 1,000.

#### Number-check mismatches M1 to M8

- **M1 (break criteria).** Changed. New §4.2 states the criteria from the `tools/r3_transformers.py` docstring: classification (parity, Dyck) = wrong sign at the last position; sequence tasks = some output at least 1/2 from the target; for rung 4 the theorem's 1/4 tolerance is also reported. The "[check]" is gone.
- **M2 ("absolute").** Changed. "Absolute (additive), zeros included" is used wherever the 1/1000 numbers appear: abstract, §1, §4, §8.2, §10. Relative is defined in §3.2.
- **M3 (margins of order 1/n).** Changed. The explanation is dropped from the single-entry table. §4.3 states that 7 of 10 witnesses have input length 2 (d10, d15, d18, p05, p10, s00, s01), p29 length 5, adders 13 and 20, and calls it an exact-tie failure. The margin-with-length effect is reported separately and is evidenced by the REL long-length cell (9 of 10 break at lengths 100 and 1,000). The report no longer uses the float32 probe as evidence for the margin story.
- **M4 (cost figures).** Changed. §7.3 now says the token and time costs are from `RESULTS_R4.md` and not in the per-case rows. Not dropped, because the source file states them.
- **M5 (sampled positions).** Changed. "Sampled positions" in §6 (numeric checks), the Table 6 caption and the §7.4 bullet; stated as a spot check, not a sweep.
- **M6 (unit).** Changed. "Input tokens" throughout; §3.4 notes that the result files say "65,535 positions" while the Lean condition allows 65,535 input tokens (65,536 positions with BOS).
- **M7 (eligible pool).** Changed. §6: pool 150 (40 carry, 40 last, 40 first, 30 induct) minus 12 feasibility ids (c34 to c39, i24 to i29, `tools/r4pool.py`) = 138 eligible. Computed from `pool/rung4_pool.json` and `FEASIBILITY_IDS`; all 12 ids are in the pool.
- **M8 (model version).** Cannot be closed by us. The result files record no version string. §1, §6 and limitation 12 say the agents were the Claude Sonnet model served under the alias `sonnet` in Claude Code between 2026-11-11 and 2026-11-13 and that the exact version string was not recorded.

#### Novelty table (review §3)

- **"What we claim" sentence.** Kept, with the abstract-level-search caveat, and re-stated in the light of Rush's work (§2 last paragraph; `NOVELTY.md` new dated paragraph).
- **"Theorems without these weaknesses".** Changed. The abstract and §1 now list what the theorems do and do not give, limited to what §8 states; the sentence is gone.
- **"Found unaided" / "found themselves".** Changed (§5.2, §10, abstract). The kit (`sw_zero`, `Head.sel_unique`), the advice and the worked example supplied the zero-stays-zero facts and the unique-selection lemma; what the agents supplied was the penalty score. The pilot claim is kept only as recorded in `PREREG_R4.md` amendment 1 (4 of 4 kernel-checked, submissions 2, 2, 2, 1, all four found an exact-zero penalty score), and cited as such.
- **Hahn credit (C2).** Changed. §2 describes Hahn per his abstract (both soft and hard attention; cannot model periodic finite-state languages or hierarchical structure unless layers or heads grow with input length) and attributes no specific margin statement. Chiang and Cholak, Merrill and Sabharwal are described only as far as their abstract pages say.
- **"Verifiable Transformers in Lean" (R. J. George).** Resolved by removal. Web search for the title found nothing; the nearest hits were TorchLean (first author Robert Joseph George, arXiv 2602.22631), Rush's "Lean Verified Transformers" and Somani's "Towards Verifiable Transformers" (arXiv 2605.24033). The entry is treated as a conflation and not cited; `NOVELTY.md` records it as NOT FOUND. Rush's work is now discussed in §2.
- **Lince repository.** Changed. §2 says what the README shows: a trained one-layer, four-head softmax transformer adds modulo 113 on all 12,769 pairs (integer weights, exact real softmax, kernel enumeration over a finite domain); a constructed network adds modulo any p at least 3; a trained recurrent adder is proved for every length by induction; ACAS Xu 1_1 property 1; proofs written by AI agents under human direction; no weight ball, no rounding. The earlier "single-weight robustness argument derived in Python" is dropped from the report (the README page we fetched did not state it; it came from `NOVELTY.md`).
- **Fragility as first contribution.** Changed. The first contribution is now the verification workflow; the measurement is the 2x2.

#### Limits table (review §4)

- **Abstract: zeros stay exactly zero; tasks chosen knowing the mechanism; i03 crash; abstract-level search.** All added to the abstract, as are "post hoc probe" for the float32 sort failure and "pass bar was low".
- Other rows were already satisfied in the body and are unchanged.

#### Objections

- **Objection 1 (not like-for-like).** Accepted and tested. The 2x2 shows the reviewer was right that the contrast was not like-for-like. The old story is withdrawn. Title, abstract, §1, §4, §7.4, §8 and §10 are rewritten around: additive noise breaks all ten rung-2 networks at once, mostly at length 2 (exact ties); relative noise leaves 9 of 10 correct at lengths up to 20 and breaks 9 of 10 at lengths 100 and 1,000; rung-4 networks show no break under relative noise but all eleven break under additive noise at lengths 100 and 1,000. Limits of the measurement are in §4.5.
- **Objection 2 (rounding model witness; tailored architecture).** Partly closed, partly not closable by us. §3.3 states plainly that the rung-4 work has no Lean proof that any rounding function with u > 0 satisfies `Rounding u fl`, that real binary32 violates a purely relative bound in the subnormal range, and that the model is an idealisation without underflow. One sentence reports, as work in progress and not as a result, a follow-up framework with an underflow term and a range bound and a kernel-checked lemma that binary32 round-to-nearest satisfies it (`Lane4/Bin32.lean`). The architecture and hard-attention points are in §8.4 and §8.7. The title no longer foregrounds "transformers" as a robustness result.
- **Objection 3 (adequacy of the statement; LLM contribution).** New §9 lists what to read (`Lane4/RSeq.lean` definitions; per-case `Spec.lean` and `Final.lean`) and what the smoke tests do and do not cover (they do not test that a network wrong inside the ball fails the theorem). The plain framing (proof automation over weights, not useful transformers) is kept in §9 and §10. We did not add a new test that a degenerate network fails the theorem; this is stated as not covered. Following the reviewer's suggestion, the title and abstract now lead with the verification workflow and the exact-tie observation.

#### Other issues C1 to C9

- **C1.** Closed. Banner replaced by one line; author line is "Authors: to be filled by the author (name only, no affiliation)"; every "[check]" and "[not measured]" is now a verified fact, a removal, or an explicit statement of what was not measured (see §7.4, §8). Model version: see M8.
- **C2.** Closed: every reference was opened (section below). Hahn: sole author Michael Hahn, TACL. Yang et al.: cited as arXiv only (the page shows no venue). Jiang et al.: title added, and the article described as also learning programs from examples. TorchLean: authors added, cited as arXiv (the abstract page shows no venue). Somani: author added.
- **C3.** Changed (§4.4). The s00 failure is said to be asserted, not diagnosed; no analysis of which score rounds wrongly was done; the report no longer calls it an "expected consequence".
- **C4.** Changed. Abstract says "in a post hoc probe of 20 inputs per length" (§4.4 repeats it).
- **C5.** Changed (§6, limitation 15). Pre-registration commit ids are not quoted; the report says they exist only in a private repository and the frozen-file hashes are the check, and gives the two hashes from `PREREG_R4.md`. We did not publish a filtered history.
- **C6.** Changed. "The pass bar was low" appears in the abstract and next to "11 of 12" in §7.3.
- **C7.** Changed. "A five-symbol alphabet" in §5.2.
- **C8.** Unchanged and checked: rung-1 numbers (20 of 20, control 20 of 20, twins 17 of 20) match `RESULTS.md`. The twin models are not in the release; the report reports them only as background.
- **C9.** Unchanged. §6 states that the prompt was reused unchanged from rung 3.

#### Section 7 items

1. **Say "absolute"; fix M3; run the relative-ball test.** Done (2x2); title and abstract changed.
2. **Replace "theorems without these weaknesses"; add the three abstract items.** Done.
3. **"Found unaided".** Done.
4. **"Verifiable Transformers in Lean" attribution; Rush; Lince.** Done (removal; §2).
5. **Close every "[check]", "[not measured]", banner, "[authors]"; verify references.** Done, with the exceptions below.
6. **Pre-registration commit ids.** Cannot be closed by us beyond what the report now says: the commits are in a private repository and we did not publish a filtered history. The frozen-file hashes are given.

#### References: what was opened, and what changed

Every cited work's own page (arXiv abstract page, publisher page, GitHub page, or project page) was opened on 2026-11-13, except where noted. Changes:

- Hahn: author "Hahn" completed to Michael Hahn; TACL and DOI 10.1162/tacl_a_00306 confirmed on the page; description corrected (see C2).
- Chiang and Cholak: authors and ACL 2022 confirmed; the "layer normalisation or log n scaling" description removed (not on the abstract).
- Merrill and Sabharwal: two articles separated as [MS23a] (TACL, arXiv 2207.00729) and [MS23b] (NeurIPS 2023, arXiv 2210.02671); the "about log n bits" claim removed (not found on the abstract pages).
- Yang, Strobl, Chiang, Angluin: "TACL 2026" removed (arXiv page shows no venue); cited as arXiv 2412.09925, year 2024.
- Jiang et al., arXiv 2602.16473: title "Synthesis and Verification of Transformer Programs" added.
- Yang and Chiang, arXiv 2404.04393: title "Counting Like Transformers" added.
- Tracr: authors and NeurIPS 2023 added.
- "Compact proofs of model performance": authors and NeurIPS 2024 added; the "fixed length" qualifier dropped (not on the abstract).
- TorchLean: authors added; venue "ICML 2026" removed (the abstract page shows none; an ICML listing exists in search results).
- Browne, Lee, Salvi: title added.
- "Quantitative bounds for length generalization": identified as Izzo, Nichani, Lee (arXiv 2510.27015, ICLR 2026) from search results and the ICLR page; the arXiv abstract page was not opened. In the end it was dropped from the report to save space.
- "Length Generalization Bounds for Transformers", arXiv 2603.02238: corrected authorship (Yang, Bergsträßer, Zetzsche, Chiang, Lin), not Merrill and Sabharwal. Dropped from the report for space.
- arXiv 2505.23623: is Li and Cotterell (NeurIPS 2025), not a Merrill and Sabharwal item. Dropped for space.
- **Removed: arXiv 2603.20991.** It is "Structural Sensitivity in Compressed Transformers" (Basu, Basu, Deb), not a Lean belief-propagation transformer. The intended article was not found.
- **Removed: arXiv 2608.10288.** It is Gokden, "Power law graph attention", not a Lean formalisation.
- **Removed: "R. J. George, Verifiable Transformers in Lean" (web article).** Not found; see above.
- **Removed: "Formally Verified Autoresearch ... Multi-Head Attention" and "Identifiability of Deep Normalized Attention".** Not re-found; not opened.
- Dropped for space but verified: SafeAdapt (2604.09452); Conic Certification (2611.00585, Ataei); Huybrechs (2506.19104, corrected title); Aleksandrov and Völlinger (2301.12893); Brucker and Stell (AFP, 2025); Koonce `lean4-mlir` (corrected description: Lean architecture specifications with machine-checked backward passes, not "small nets with `native_decide`"); `fxeqxmulfx/transformer` (corrected: research project with unfinished convergence goals, Lean proofs on spectral recovery and convex learners, not "a formalisation of manuscripts on small GPTs").
- Kept and verified: Weng et al. (AAAI 2020, vol. 34, pp. 6356-6363, from the AAAI page via search); Elmecker-Plakolm et al. (SaTML 2026 per arXiv comments); Jin et al. (AISec '24); Szász et al. (ICML 2025); Murray (arXiv 2603.13334, Rocq-mechanised); FloatLib (George, Adkisson, Anandkumar); Somani.
- csinva: repository name and MIT licence confirmed; the page does not name "C. Singh", which comes from our notes and is marked as such. ctrimm: owner is Cory Trimm; the repository is about benefit formulas, and "pre-registered, frozen hashes" was not on the page and is not claimed.
- Added: Rush, "Lean Verified Transformers" (page and repository opened; the page text was read except its last 9,000 characters; author shown as "srush"; no date shown). Lince repository (README opened).
- Gromov (2023) "Grokking modular arithmetic" (arXiv 2301.02679) was opened and exists, but we could not confirm the Lince README cites it, so it is not mentioned.

#### Not closed

- M8 version string; pre-registration commit ids (private repository); Lean witness for the rounding model (follow-up work only); diagnosis of the s00 float32 failure; exact-rational confirmation of the 2x2 cells; a test that a degenerate network fails the theorem; the Quantitative Bounds article's arXiv page (identified from search results only).

#### Word count and a process note

The revision is about 6,900 whitespace-separated tokens including tables and references (about 6,400 without the reference list), above the 6,500 target if the references are counted. The rung-4 claim "no break found under REL" and every 2x2 figure are read from `writeup/NOTE_2x2_results.md`, not recomputed. A few small Python text-replacement scripts were used to edit files; no experiment, Lean, lake or git job was run.

#### 2026-11-13: restructuring as a living technical report (version 0.3)

The report (now `REPORT.md`) was restructured from a conventional article draft into a living technical report. No fact, number, table, limit or reference was added or changed; the framing and the order changed.

- Title and header: plain descriptive title; a header line giving the version and date; two sentences on what the document is.
- Abstract, introduction (with its three numbered contributions) and conclusion removed. The conclusion is replaced by a short "Where this stands" paragraph. The statements of scope and of the first-draft withdrawal moved into "Known weaknesses".
- New front matter, before any detail: a claims table (17 rows, each with a status and where to check it), known weaknesses and open questions, a 15-minute check recipe (from the `tools/check.py` header; the Lean steps were not re-run then), and a section on how to correct us (no contact details; to be added at release).
- Detail sections renumbered: related work 1, setting and model 2, the 2x2 measurement 3, constructions 4, protocol 5, results 6, full list of limits 7, what to read to trust a statement 8, where this stands 9. Cross-references were updated. The old limitations section is kept as a numbered full list and points to the weaknesses section where they overlap.
- Article-style positioning removed ("we report", "our contributions", "novel", "first"); the narrow novelty claim and its caveat stay only in the claims table and the related-work section.
- A changelog (0.3, 0.2, 0.1, newest first) was added at the end, with the removed references listed under 0.2.
- One path correction: the source of Table 1 is given as `results/r3-2x2.json` (ARTIFACTS.md names `results/r3-transformers.json`, which holds the earlier single-weight screen).

=====END=====

Notes for the coordinator:
- Title: "LLM-Written Transformer Weights with Lean-Checked Proofs: Workflow, Perturbation Measurements and Open Problems". Claims table: 17 rows (rows 16 and 17 are the two you asked for).
- No file was written; RESPONSE.md is back to its original text apart from one trailing blank line.
- Every fact in the old text now sits under one of the five status values or in prose. The agents-supplied-the-penalty-score account and the per-case token and time costs are process descriptions, not claims, so they stay in prose (Sections 4.2 and 6.3), as do the pre-registration hashes.
- Claim 14 (no transformer with such a theorem exists in prior work) restates the old narrow "first". Claim 13 states the rounding-model claim as the old text implied it. I chose the wording of both.
- The "about nine minutes" run time and the check recipe come from NOTE_2x2_results.md and check.py/ARTIFACTS.md. The Lean steps were not re-run.
- Result-file names for claims 16 and 17 come from the ARTIFACTS.md listing and were not opened.

#### 2026-11-14: response to an independent AI reviewer's second read

The read was written against version 0.6. The report is now version 0.7 (`REPORT.md`, changelog entry 0.7). Answers by point. "Confirmed" means we checked the claim in our files and agree; "partly" and "disagree" say where and why. No Lean file, result file or tool was changed in this pass; the rerun of the 2x2 is `tools/r3_2x2_v2.py`, run earlier on 2026-11-14. We disagree with no point outright; point 10 is partly applied.

1. **Theorem adequacy; publish the encodings. Confirmed (the `i03` caution too).** In the release copy `runs/rung4-test/net/i03` (and `net-rerun/i03`) holds Spec, Final, TASK and case.json but no Solution and no passing attempt; it is a fail. The report never counted it as a success (claims rows 4 and 6 say 11 of 12); the wording now says so explicitly in rows 4 and 6, in "Known weaknesses", and in Section 6.3. New Appendix A reproduces the definitions from `Spec.lean` (rung 2: p05, s00, a00; rung 4: c14 with `cls` and `dg`, l38, f05 first, i09 induct) with a plain description each, and says `Spec.lean` is the definition of each task. The review's reading of the sampled statements (no vacuous hypothesis, reversed quantifier or trivial tolerance) is quoted as a read of samples, not an audit.

2. **Rounding witness and length. Confirmed.** `fl = id` satisfies `Rounding u fl` for every u, so satisfiability was never in doubt; the meaningful witness is the non-identity one (`runs/r5-kit/kR`). Stated in claims row 13, Section 2.3 and the weaknesses. The 65,535-token bound comes from u*(length+1) <= 1/256 and is a sufficient condition, not a measured failure threshold (Sections 2.3, 2.4, limit 3). The old item above ("Lean witness for the rounding model", Objection 2) is dated as superseded on 2026-11-14.

3. **Binary32 semantics. Confirmed for rung 4; answered for rung 5.** Claim 13b stays "not established" for rung 4's model. For rung 5 (new Section 2.5): `Rnd u eta M fl` assumes, only for |x| <= M, error at most u*|x| + eta, monotone, idempotent, exact on integers to 2^24, nothing outside the range. `Lane4/Bin32.lean` (kernel-checked) proves that any function agreeing on |x| <= maxF with a round-to-nearest onto the binary32 grid (subnormals, any tie rule) satisfies it with u = 2^-24, eta = 2^-150, M = maxF. The rung-5 theorems cover each operation as the rounding of the exact result; left-to-right separately rounded multiplies and adds; the softmax in the stated order; stored weights `fl(w(1+d))`; position features `fl i`, `fl n`; and no overflow (each proof bounds every intermediate). Assumed: the accuracy of the float exponential. Not covered: fused multiply-add, reassociated or vectorised sums, signed zeros and the bit encoding, NaN and infinities (shown not to arise), hardware or library conformance, and rung 4's own model beyond the idealised witness. The review's example (x = 2^-150 rounds to 0, relative error 1) is why the rung-5 model has the eta term.

4. **Pooled long-length counts. Confirmed (error).** `wrong_long` in `tools/r3_2x2.py` returns one Boolean over lengths 100 and 1,000. Rerun per length (`tools/r3_2x2_v2.py`, `results/r3-2x2-v2.json`, `writeup/NOTE_2x2_v2.md`), networks with at least one break found: rung 2 ABS 10 / 10 at lengths 100 / 1,000; rung 2 REL 8 / 8 (pooled 9; a01 breaks only at 1,000, d18 only at 100, d15 at neither); rung 4 ABS 8 / 11 at the 1/2 criterion (the three `last` networks have no break at length 100 in 50 corners) and 11 / 11 at the theorem's 1/4 tolerance; rung 4 REL 0 / 0. Short-input columns unchanged. The counts are not monotone in length (d15, d18, p05, p29 under ABS break in fewer corners at 1,000 than at 100), so they are no growth law. Table 1 replaced; every "at lengths 100 and 1,000" sentence replaced; the version-1 pooled numbers kept in one row marked superseded. Same correction in `NOTE_open_problems.md` section 1 (parity networks, per length: p05 20 and 37, p10 25 and 30, p29 12 and 31 of 50 corners).

5. **Omitted output bias. Confirmed (error).** `tools/r3_2x2.py` built `outB` for rung-4 networks but left it out of the perturbed arrays. Rerun with it included: no network-level count changed (corner counts moved slightly: i09 and i10 5 and 4 of 200 short corners instead of 7 and 7, because the random draws shifted by one entry). The Lean witness `runs/witness/r4abs_c14` is unaffected: its changed network has `outB := -1/1000`, so it does perturb the bias. Rung-2 arrays are loaded through float32 and cast to float64; stated in claims row 2 and Section 3.2. The review's remark that a found counterexample remains meaningful is agreed.

6. **Meaning of the 2x2. Confirmed (overclaim).** Every 2x2 cell is now a finite-search outcome ("a break was found for N of M networks in this search", "no break found"); "survive" and "robust" are gone as properties. "This is the margin-with-length effect" is now "consistent with a margin that shrinks with length; the screen does not identify the cause or a rate". The stale "no exact confirmation of the new cells" lines (weaknesses, Section 3.5, limit 13) now say that three individual cells have Lean-checked witnesses (`runs/witness/r2rel_s00`, `r2long_a00`, `r4abs_c14`) and the counts as a whole do not.

7. **Architecture-wide counting lower bound. Confirmed (overclaim).** Claim 12, Table 3, Section 4.1, limit 1 and `NOVELTY.md` (the rung-4 passage) now say "conjecture; not proved". Parity's precise Lean conjecture (`Lane4.Conj.ParityNoBall`, type-checked only) is kept distinct from Dyck and sort, which have no Lean statement, only an informal expectation. The report now says what the review says: an argument that one k/n channel misdecodes does not cover networks that encode counts another way (other heads, coordinates, nonlinearities, attention selections, compensating scalings); one-bit input sensitivity does not imply weight sensitivity; the screen does not determine a rate. We agree that `NOVELTY.md` line 205 must not be read as establishing the architecture-wide result; it was relabelled.

8. **Tractable lower bound. Agree, with the review's caveats; not started.** Recorded in `NOTE_open_problems.md` section 1 as "Candidate for rung 6: a collision lemma" for the sub-class where the count reaches the decoder only as z = (1 + d)*k/n with the same downstream decoder for every input and perturbation: two pairs (k, d) and (k + 1, d') in the ball give the same z once k is of order 1/tau, giving a radius bound of order 1/L for that sub-class. Caveats stated: all other decoder inputs must coincide, so it does not cover a second block that can read the original sequence; `ParityRadiusBound` asks one constant for all networks, which is stronger; `ParityNoBall` stays an open conjecture.

9. **Absolute-ball impossibility and the float statement. Confirmed (gap).** `NOTE_open_problems.md` section 2 now labels the three reasons as mechanisms, not a proof, and says that an unbounded residual coordinate feeding a perturbed coefficient does not prove impossibility if earlier layers can cancel it; the missing step is to isolate an output-only perturbation and prove a final coordinate unbounded, or give a general alternative. Claims row 12b and the row 8 text say the `c14` witness is one finite-radius failure of one network, not `LastNoAbsBall`. The float32 remark (Section 4.1) is scoped to this model's direct float32 encoding of the position `i` as a state entry; other encodings (discrete masks, token content, integer indices) are not covered, and no task-level proof is asserted. `NOVELTY.md` lines 225 to 228 carry the older unscoped wording of the same remark and were outside the passage named for this pass.

10. **Prior work and novelty. Partly.** We opened two pages on 2026-11-14. LeanCert documentation (https://docs.leancert.io/ml/neural-networks/; GitHub `alerad/leancert`; no authors or date): component soundness theorems for interval propagation through MLP layers and ReLU and sigmoid relaxations are proved in Lean; for attention, public theorem coverage is "structural rather than a full elementwise enclosure". Wesonga, "Formalizing PARITY Circuit Lower Bounds in Lean", arXiv:2609.24188, sole author Saint Wesonga, 21 September 2026: Hastad's PARITY lower bound for bounded-depth circuits; nothing about transformers. Both added to related work as adjacent, with those descriptions. The AAAI page for Weng et al. refused automated access on 2026-11-14, so it was not re-opened; the entry stays (verified 2026-11-13). Row 14 is now: "We did not find such a theorem. Scope: web search of abstracts, summaries and a few project pages, 2026-11-11 to 2026-11-14", status "not established". Rush, TorchLean, Lince and Weng were not re-read.

11. **Preregistration evidence. Confirmed (error).** The weakness paragraph and the protocol sentence are rewritten: the pre-registration commits and their timestamps are in a private repository and are not independently verifiable; no independently timestamped commitment was made; what a reader can check is that the frozen files reproduce the stated hashes and the results. Reproducibility of the frozen files and evidence of prior registration are different claims, and only the first is offered. Limit 15 and the rung-5 hashes follow the same wording.

12. **Release completeness and replay. Confirmed.** Lean toolchain `leanprover/lean4:v4.35.0-rc3`; Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e` (input revision `v4.35.0-rc3`), from the `lake-manifest.json` of the external checkout whose compiled Mathlib the checker uses. The report's statement that the revision is not recorded is corrected (check recipe step 2, Section 5, Appendix B). In version 0.7 Appendix B listed what was then not yet in the release copy (`runs/witness/*`, `runs/r5-kit/*`, `Lane4/QRSeq.lean`, `Conjectures.lean`, `RSoft.lean`, `RSoftKit.lean`, `Bin32.lean`, `RSoftAll.lean`, all of rung 5, the 2x2 results and tools, the witness generators, the rung-6a probe). No fresh replay was run for this pass, and none is claimed. Older review and response sections are labelled historical (the top note of this file; Appendix B of the report).

##### Also changed in this pass: rung 5 folded in

Claims rows 18 to 23 and Section 6.5 report rung 5 (12 of 12 softmax networks; binary32 round-to-nearest kernel-checked against the model; exp accuracy assumed; numeric checks; control 12 of 12, median 43.5 lines against 810). One pre-registered check failed and is stated at the top of the report, in the claims table (row 22) and in the weaknesses: the PyTorch stated-order forward pass is bit-identical to numpy on 11 of 12 networks and not on `c04` (142 of 9,576 outputs differ; post hoc: one unit in the last place near 2e-9, and numpy and PyTorch float32 `exp` differ on 39% of 2,000,001 sampled arguments). New weaknesses: the kit carries the softmax and float analysis (the result is about packaging it); two of three induct cases used 10 of 12 submissions; our check job was killed once for memory (amendment 3); the PyTorch object is our own module; the rung-5 networks were not screened under additive noise.

##### Not closed by this pass

Point 8 (collision lemma, not started); exact-rational or Lean confirmation of the 2x2 counts as a whole; a binary32 lemma for rung 4's own model; a proof of any 2x2 mechanism; independent timestamping of pre-registration; fresh replay of the release copy; `NOVELTY.md` lines 196 to 197 and 225 to 228 (older analysis wording outside the passage named in this pass).
