# the proofs study novelty re-check (2026-11-11)

Run before any doctor run, as the study's rules requires. Re-run before any claim.

## Verdict

**The strong claim in SCOPE.md does not survive.** "No work found where an LLM
produces both the weights and a machine-checked proof" is no longer safe to say.
One public repository, three weeks old, covers most of the ingredients:

**`teal-sea/lean-checked-network`** (Thomas Lince; created 2026-10-15, last push
2026-11-04, MIT, 1 star, no paper found). Its README and RESULTS.md state:

- "AI coding agents (Claude Code and Codex workers) wrote the proofs, generators
  and checks"; the human chose problems and checked statements, and "did not
  write the proof terms".
- Networks "written from the circle formula with fixed phases, no training" are
  kernel-checked to add mod 113, mod 12 and mod 257 on every pair. The
  generators that emit these weights are agent-written; the construction follows
  Gromov (2023).
- A Lean theorem on Mathlib that the constructed network adds mod p **for every
  modulus p ≥ 3** (a general proof, not enumeration).
- A **trained** recurrent adder proved correct for inputs of **every length**,
  by checked states plus induction.
- **Trained** networks (an MLP and a one-layer transformer) proved correct on
  all 12,769 inputs by kernel enumeration.
- **ACAS Xu network 1_1, property 1** checked in Lean over the whole input box,
  from an α,β-CROWN certificate on TorchLean semantics.
- Standard axioms only, no `sorry`; `leanchecker` and nanoda replays; planted
  fault tests.

## What this does to the scope

| Scope item | Status after this check |
|---|---|
| "LLM produces weights and machine-checked proof" as a first | **Gone as a first.** Agents wrote both the weight generators and the proofs there, under human direction on hand-picked problems. |
| Rung 2 proof shape (all lengths by induction) | Done there for a trained RNN. A written hard-attention transformer for all lengths is still not found. |
| Rung 4 (ACAS Xu in Lean) | Property 1 of one trained network is done there. A *written* network satisfying the ACAS properties is not found. |
| "Trained twins expected to fail; that contrast is the headline" | **Weakened.** Small trained nets on finite domains can be kernel-checked by enumeration, and solver certificates can be replayed in Lean. The contrast only holds for exact equality over a continuous domain, where a trained net is only approximately right, and that is a near-trivial reason to fail. |

## What is still not found

1. **A measured experiment.** Spec → weights → proof by one LLM in one episode,
   from a blind random spec pool, pre-registered, n ≥ 20, with a success rate
   and controls. Every prior item is a showcase theorem on a chosen problem.
2. **Exact functional proofs over a continuous domain** for written ReLU nets
   (rung 1). Minor on its own: the maths is routine.
3. **A written hard-attention transformer proved for every length** (rung 2).
4. **A proved tolerance ball around written weights in Lean** (rung 3). The
   teal-sea repo has a single-weight robustness argument, derived in Python,
   not in Lean.
5. **A written network provably meeting the ACAS Xu properties** (rung 4).

Honest reading of the level scale: rungs 1-2 are now "a systematic version of
what one repo showed case by case", which is about level 2-3, not 3. The path to
level 4 rests on rungs 3-4 alone.

## Other work checked

| Work | Date | What it does | Proof? |
|---|---|---|---|
| csinva/weight-space-programming-autoresearch (C. Singh) | 2026-11-02 | Claude hand-writes transformer weights for 10 algorithmic tasks, 959 programs | No. 200 test examples |
| ctrimm/weight-space-programming (Cory Trimm, CC BY 4.0) | 2026-11-07 | Weight-space programming experiments on SNAP, EITC, SSI and Medicaid arithmetic: LLM writes weights that reproduce a benefits formula, compared with a trained baseline (corrected 2026-11-13: the page does not mention pre-registration or frozen hashes; not verified) | No. Dense grid tests, error ~1e-12. **Closest to rung 1's task and its trained-twin control** |
| arXiv 2610.24548 (Browne, Lee, Salvi), "Proving LLM-Generated GPU Kernels Correct and Safe: Floating-Point Verification in Lean and VerCors" (corrected 2026-11-13: title added) | 2026-10-17 | LLM agent writes GPU kernels and proves them equal to spec in Lean (Velvet), over floats | Yes, but for kernel code, not weights |
| TorchLean, arXiv 2602.22631 (ICML 2026) | 2026-02 | Lean 4 network semantics, bound propagation, certificate checking | Infrastructure; no LLM-written weights |
| arXiv 2603.20991 | 2026-03 | (corrected 2026-11-13) WRONG ENTRY: this id is "Structural Sensitivity in Compressed Transformers: Relative Error Propagation and Layer Removal" (Basu, Basu, Deb), not a Lean belief-propagation transformer. The intended paper was not found and is not cited | - |
| brettkoonce/lean4-mlir (Brett Koonce, BSD-3) | 2026 | (corrected 2026-11-13) Lean specification of neural architectures with machine-checked backward-pass correctness (Jacobian-transpose) and StableHLO/XLA code generation; `native_decide` use not seen on the page | Training code and layer-level proofs |
| fxeqxmulfx/transformer | 2026 | (corrected 2026-11-13) Research project with unfinished goals (training-convergence proofs for a one-block transformer variant, grokking, convex models, forward-only training); Lean proofs on spectral recovery, convex learners and forward-only learning; no checkpoints published; the "39 unfinished statements" figure was not seen | No all-lengths theorem for written weights found |
| arXiv 2506.19104 (D. Huybrechs, "On the algorithmic construction of deep ReLU networks") | 2025-06 | (corrected 2026-11-13: author and title added) Explicit ReLU network constructions, e.g. exact sorting | Paper proof only |
| Brucker & Stell (Isabelle AFP 2025); Coq piecewise-affine nets (arXiv 2301.12893, Aleksandrov and Völlinger, "Formalizing Piecewise Affine Activation Functions of Neural Networks in Coq"; corrected 2026-11-13: authors and title added) | 2023-25 | Formal semantics of feed-forward nets | Human proofs; no LLM, no written weights |
| nathanrs/weight-space-lp, openwsp, AuremHQ, others (12 WSP repos, Nov 2026) | 2026-11 | Weight editing of LLMs | No proofs |

## Searches run

- Web (extended and standard): LLM-written weights + Lean/Coq/Isabelle proof;
  proof-carrying network; verified ReLU max/sort in Lean; RASP/Tracr verified;
  all-lengths transformer proofs.
- GitHub code search (`language:Lean`): `theorem relu mlp computes max`,
  `theorem relu network_correct`, `relu weights theorem native_decide network`,
  `tracr theorem`, `transformer weights theorem parity List.length attention`,
  `theorem relu sort3`, `theorem relu median`, `hard attention theorem parity
  weights`, `relu theorem "max a b" network weights Rat`, and four more that
  returned nothing. Two queries were lost to a rate limit and re-run.
- GitHub repo search: "weight-space programming" (12 hits, all read by
  description), "lean verified neural network weights", "proof-carrying neural
  network lean", "lean kernel-checked neural network", "certified grokking
  lean" (no hits; note that this search did **not** surface teal-sea, which
  came from web search, so repo search has poor recall here).

## Limits of this check

- teal-sea was read through its README and RESULTS.md, not its Lean sources.
  Whether an agent or the human chose the phase-grid weights is not stated.
- Naughton's "certified-grokking" and Gross, Kwa and Agrawal (2023), cited
  there, were not read.
- The WSP area is one week old and moving daily; twelve new repos appeared
  since Nov 2. A check older than a few days is stale.

## Re-check for rung 2 (all-lengths claim), 2026-11-11 evening

Question: has anyone published a transformer with stated weights and a proof-assistant
proof that it is correct at **every input length**? Four web searches (proof assistant +
transformer + all lengths; RASP/Tracr verified; LLM-written weights + Lean; hard attention
+ machine-checked). Search summaries only unless marked "read".

| Item | What it does | Takes the rung-2 claim? |
|---|---|---|
| Jiang, Hague, Rümmer, Lin, arXiv 2602.16473, "Synthesis and Verification of Transformer Programs" (Feb 2026; abstract read; corrected 2026-11-13: title added) | Verifies **C-RASP programs** by translating to Lustre and using SMT-based model checkers; also learns C-RASP programs from examples | **Closest.** Unbounded-length verification, but of programs, not weights; SMT trust base, no proof assistant; no LLM. Must be cited. |
| Yang & Chiang, "Counting Like Transformers: Compiling Temporal Counting Logic Into Softmax Transformers", arXiv 2404.04393 (corrected 2026-11-13: title added) | Paper proof that C-RASP compiles to future-masked soft-attention encoders for any length | No. Paper proof of a compiler, not a checked proof of given weights |
| Tracr (Lindner et al., NeurIPS 2023), arXiv 2301.05062 | Compiles RASP to weights | No. Correctness not mechanised |
| "Quantitative Bounds for Length Generalization in Transformers", ICLR 2026 (corrected 2026-11-13: Izzo, Nichani, Lee; arXiv 2510.27015) | Bounds how many lengths must agree before two limit transformers agree everywhere | No. Paper theory; but it means "test up to length N" can in principle be a proof for a restricted class. Worth one sentence |
| "Compact Proofs of Model Performance via Mechanistic Interpretability" (Gross et al., NeurIPS 2024), arXiv 2406.11779 | Computer-assisted proofs about a trained Max-of-K transformer | No. Fixed length, trained weights |
| Items already in this memo (trained RNN adder for all lengths; 2603.20991) | Unchanged | Rung-2 proof shape exists for a trained RNN; not for a written transformer |

**Verdict.** Not found: stated transformer weights (written by anyone) with a
kernel-checked theorem over all sequence lengths. The claim to make, if rung 2 passes, is
narrow: "LLM-written hard-attention transformer weights with a Lean-kernel proof for every
length, at a measured success rate on a blind pool". Cite 2602.16473 as the nearest work
and say plainly that it verifies the program level with SMT.

**Design constraint found on the way (changes the task list).** Fixed-depth transformers
with unique (leftmost/rightmost) hard attention cannot compute parity at all lengths (Hahn
2020, arXiv 1906.06755; TACL survey: such encoders sit in AC0). So "parity, by a
hard-attention transformer, for every length" is impossible unless the attention is
average-hard (ties share weight) and the position features carry enough information. The
PREREG amendment must fix the attention type and position features first, and each task
family must be one that architecture can express. Parity stays in only if the fixed
architecture can do it.

## Re-check for rung 3 (proofs with weight tolerance), 2026-11-12

Question: what is new in "a written network with a proof that it stays correct for every
weight setting inside a stated ball, so float rounding and fine-tuning are covered"?
Three web searches. Search summaries only; no paper was read in full.

| Item | What it does | What it takes from the rung-3 claim |
|---|---|---|
| Weng, Zhao, Liu, Chen, Lin, Daniel, "Towards Certificated Model Robustness Against Weight Perturbations", AAAI 2020 | Certified lower bounds on the weight-perturbation region in which a trained ReLU network keeps its outputs; applied to quantization | **The certificate idea itself.** Weight-ball robustness certificates for ReLU MLPs exist since 2020 (numerical bounds, trained nets) |
| Elmecker-Plakolm, Fasterling, Sosnin, Tsay, Wicker, "Provably Safe Model Updates", arXiv 2512.01899 (v2 March 2026) | Finds a certified region of parameter space (a "local invariant domain") where a performance requirement holds, then keeps fine-tuning inside it by projection | **The fine-tuning idea itself.** "Certify a weight region, then update inside it" is published, with experiments on continual learning and foundation-model fine-tuning |
| SafeAdapt, arXiv 2604.09452 | Same framework for deep RL policy updates | Same |
| Interval bound propagation, CROWN family, VNN-COMP tools | Input-perturbation certificates; several extend to weight intervals | The proof technique (interval/linear bounds) is standard |
| "Getting a-Round Guarantees", arXiv 2205.10159; "No Soundness in the Real World", arXiv 2506.01054; arXiv 2603.13334 | Show that real-arithmetic certificates can fail under floating-point execution, and certify under float execution | **Our float32 finding on s00 is a known phenomenon**, not a discovery |
| FloatLib, arXiv 2609.19352 | Verified floating-point arithmetic in Lean 4 | A route to proving float statements directly in Lean; not used here |
| TorchLean (already in this memo) | Bound propagation and certificate checking in Lean 4 | Lean-checked interval certificates for networks exist as infrastructure |

**What is not found:** a network whose weights were written (by a person or an LLM) from a
spec, with a proof-assistant theorem "for every weight setting within τ, the output stays
within δ of the spec on the whole input box". Existing weight-ball certificates are
numerical, for trained networks, and about accuracy on data rather than an exact spec.

**What that leaves, honestly.** Rung 3 would add three things to known work: the theorem
is checked by the Lean kernel instead of a numerical tool; the reference is an exact
written spec instead of a dataset; and the network and proof come from an LLM at a
measured success rate. The headline ideas (weight-ball certificates, safe fine-tuning
inside a certified region, float execution breaking real-arithmetic proofs) are all
published. Cite 2512.01899 and Weng et al. 2020 first in any write-up.


## Re-check for rung 4 (all lengths AND a weight ball AND modelled float rounding), 2026-11-12

Question: is there prior work with a transformer proved correct, in a proof assistant, at
every input length, for every weight setting in a stated ball, or for a modelled
floating-point forward pass? Eight web searches and three abstract-level page reads.
Search summaries and abstracts only; no paper was read in full.

| Item | What it does | What it takes from the rung-4 claim |
|---|---|---|
| Hahn 2020 (Michael Hahn, TACL, arXiv 1906.06755); Chiang and Cholak, "Overcoming a Theoretical Limitation of Self-Attention", ACL 2022 (arXiv 2202.12172) | (corrected 2026-11-13) Hahn's abstract covers soft and hard attention and says self-attention cannot model periodic finite-state languages or hierarchical structure unless layers or heads grow with input length; Chiang and Cholak show ways to overcome the limitation on PARITY and FIRST. The "margin shrinks as inputs get longer" and "layer norm / log n" wording was not found on the abstract pages | **The fragility is known in theory.** "Exact all-lengths constructions have margins that vanish with n" is not our discovery |
| Merrill and Sabharwal, "A Logic for Expressing Log-Precision Transformers", NeurIPS 2023 (arXiv 2210.02671) and "The Parallelism Tradeoff", TACL (arXiv 2207.00729); Li and Cotterell, "Characterizing the Expressivity of Fixed-Precision Transformer Language Models" (arXiv 2505.23623, NeurIPS 2025); Yang, Bergsträßer, Zetzsche, Chiang, Lin, "Length Generalization Bounds for Transformers" (arXiv 2603.02238) | (corrected 2026-11-13: authors added; the last two were wrongly grouped under Merrill and Sabharwal) Paper theory on log-precision and fixed-precision transformers and on length-generalisation bounds; the "about log n bits" wording was not found on the abstract pages | The float32 failure of our sort network is the expected consequence. Not machine-checked, not about a weight ball |
| arXiv 2602.16473 (already in this memo) | C-RASP programs verified with SMT model checkers, all lengths | All lengths, but programs, exact arithmetic, no weights, no proof assistant |
| (corrected 2026-11-13) "R. J. George, Verifiable Transformers in Lean, June 2026 (web article)" | NOT FOUND. Searches for the title returned only TorchLean (arXiv 2602.22631, first author Robert Joseph George), Rush's "Lean Verified Transformers" and Somani's "Towards Verifiable Transformers". The entry is a suspected conflation and is not cited | - |
| "Towards Verifiable Transformers: Solver-Checkable Circuit Explanations" (Neel Somani), arXiv 2605.24033 | Solver-checked properties of a GPT-2 circuit on a 1,280-prompt domain, real arithmetic | Finite domain, no weight perturbation, no floats |
| "Conic Certification of Transformer Attention" (Masoud Ataei), arXiv 2611.00585 | Numerical certificates for softmax attention under input perturbation, GPT-2 | Inputs not weights; numerical; fixed length |
| Lean 4 attention formalisations (corrected 2026-11-13: arXiv 2608.10288 is Gokden, "Power law graph attention", a non-Lean empirical paper, and is dropped; "Formally Verified Autoresearch ... Multi-Head Attention" and "Identifiability of Deep Normalized Attention" were not re-found and are not cited; brettkoonce Lean 4 project: see above) | Lean proofs of algebraic or expressivity facts about attention, or of backward-pass correctness | Lean and attention, but none proves a task correct at all lengths, none has a weight ball or a float model |
| Float-execution papers and FloatLib (rung-3 section) | Real-arithmetic certificates can fail in floats; verified float arithmetic exists in Lean | The float concern and the infrastructure are known |

**What is not found:** a transformer (written or trained) with a proof-assistant theorem
of correctness at every input length for every weight setting in a ball; or with a
proof-assistant theorem about a forward pass with modelled rounding at unbounded or very
long lengths. No GitHub repository of this kind turned up.

**Verdict, plainly.** A narrow "first" survives: *the first machine-checked proofs that a
transformer is correct at every length for every weight setting in a stated ball, and for
a modelled rounding forward pass up to a stated length*. It does not survive in the wide
form of the pitch. "Literature constructions are fragile" is already known in theory
(vanishing margins, log-precision); what rung 3 added is a measurement on kernel-proved
networks. The search was a web search over abstracts, so "not found" is weaker than "does
not exist". Cite Hahn 2020, Chiang and Cholak 2022 and Merrill and Sabharwal 2023 first.

### Which tasks can have a ball that does not shrink with length (analysis, not a result)

Two kinds of ball must be kept apart.

- **Absolute ball** (rung 3: every entry may move by ±τ, including entries written as 0).
  With position features that grow with length (i, i², n), a perturbed zero entry lets
  every unit read τ·n or τ·n². So we expect that no task has a length-independent
  absolute ball in the rung-2 architecture. This is a mechanism, not a proof: it does not
  rule out earlier layers cancelling the term. Conjecture, not proved (corrected 2026-11-14).
- **Relative ball** (every written weight w becomes w·(1+d), |d| ≤ τ; zeros stay zero).
  This is the model of rounding a stored weight to a float. It is the one used below.

| Family | Length-independent relative ball? | Why |
|---|---|---|
| add (digit-wise sum with carry) | **Yes**, with the right mechanism | The carry needs only "the nearest earlier position that is not a propagate". See the note under the table: the usual bonus score fails, a penalty score works. No counting. |
| "nearest / first earlier position whose token is in a set", "previous occurrence of the current token", latch-like tasks | **Yes** | Same mechanism |
| parity | **Conjecture (not proved)**: radius shrinks like 1/n (corrected 2026-11-14) | In the constructions written here the count k is an average k/n. A relative error d on a value weight turns k into k(1+d), which is off by more than 1/2 once d·n > 1/2. This does not cover networks that encode counts another way (other heads, coordinates, nonlinearities, compensating scalings); one-bit input sensitivity alone does not imply weight sensitivity. Lean statement: `Lane4.Conj.ParityNoBall`, type-checked only. |
| dyck | **Conjecture (not proved)**: ~1/n (corrected 2026-11-14) | In the written constructions, the sign of a prefix sum that is exactly zero at balance; a relative error of d on the +1 and −1 weights moves a balanced sum by up to 2·d·n. No Lean statement, only an informal expectation. |
| sort | **Conjecture (not proved)**: ~1/n (corrected 2026-11-14) | Needs exact counts, as parity, in the written constructions. No Lean statement, only an informal expectation. |

**Correction (2026-11-12, late): which selection score survives.** The textbook score
"n·flag_j + j" (a bonus for marked positions) does NOT have a length-independent ball once
embeddings are perturbed too: two marked positions holding different tokens get bonuses
n·(1+d) and n·(1+d'), which differ by up to 2τn and swamp the position gap of 1. What
survives is the mirror image: score "j − 2n·pen_j", where pen is written as 0 on the wanted
positions and 1 elsewhere. A weight written as 0 stays exactly 0 under a relative
perturbation and under rounding, so all wanted positions share the score s·j exactly up to
one common factor, and the unwanted ones are pushed below every wanted one with a margin
that grows with n. The same works for query-dependent matching (penalise mismatches). So
the dividing line is: tasks solved by unique hard attention with exact-zero penalties have
a length-independent ball; tasks that must count (parity, dyck, sort) are conjectured not to
(corrected 2026-11-14: conjecture, not proved; the argument above covers one k/n channel, not
every way a network could encode counts).

So for parity, dyck and sort the conjectured statement is "correct for every length n and every
relative perturbation up to c/n", equivalently "for a fixed τ, correct up to length c/τ".
With float32 storage (τ = 2⁻²⁴) that is still lengths in the millions.

**Floats.** In THIS model the position `i` is a float32 state entry, and float32 cannot
represent consecutive integers above 2²⁴, so a float forward pass of this model cannot
tell neighbouring positions apart beyond that length. So the float statement here carries
a length bound for every family, including add. The remark is about this direct encoding
of positions; other encodings (masks, integer indices, token content) are not covered by
it (scoped 2026-11-14).
The all-lengths claim can only be about exact arithmetic with a weight ball.

## Rung 5 (softmax attention and IEEE binary32): novelty and feasibility, 2026-11-13 evening

Target from the project owner: a written transformer with softmax attention (not average-hard)
and true IEEE float32 semantics, proved for every length up to a stated bound and over a
weight ball, loadable in PyTorch. Web search over abstracts and project pages only (same
caveat as before: "not found" is weaker than "does not exist").

### What already exists

| Work | What it has | What it lacks for this target |
|---|---|---|
| Yang, Strobl, Chiang, Angluin, "Simulating Hard Attention Using Soft Attention" (arXiv 2412.09925; no venue on the arXiv page; "TACL 2026" unverified, corrected 2026-11-13) | Paper proofs that soft attention simulates hard attention; some constructions with length-independent parameters (previous/next, "since", counting, using encodings such as i, i², 1/i), others needing temperature 1/n | Not mechanised; exact real arithmetic; no weight perturbation; no rounding |
| C-RASP (arXiv 2404.04393) | RASP variant that provably compiles to future-masked soft-attention transformers at every length | Paper proof; exact arithmetic; no weight ball |
| TorchLean (arXiv 2602.22631, lean-dojo) | Lean 4 framework: bit-level binary32 model (IEEE32Exec) refined to a round-on-reals model for finite values; attention specified; interval and CROWN-style bounds with certificate checking for input regions | No theorem about a transformer's correctness at all lengths; no weight-ball statement; transcendental functions go through an external interval oracle |
| FloatSpec (Beneficial AI Foundation) | Lean 4 port of Flocq, in progress (Lean 4.29) | Open error-bound theorems; no neural network result |
| Fixed-precision / log-precision expressivity papers | Theory of what finite-precision transformers can compute | Not mechanised; not about a concrete float format |
| Float-aware verifiers (software-level, Lipschitz with float error) | Bounds for trained nets on input regions | Not proof-assistant-checked end to end; fixed input size |

### Verdict

**A narrow first survives:** nothing found that gives a proof-assistant-checked theorem that a
transformer with softmax attention computes a stated function at every length up to a bound,
for every weight setting in a ball, under a model of binary32 arithmetic. **What is not new:**
that soft attention can simulate hard attention with length-independent parameters for some
tasks (Yang et al.; C-RASP), and bit-level float32 semantics in Lean (TorchLean). Rung 5
would be the combination, machine-checked, with weight tolerance and rounding added. Yang et
al. must be cited as the source of the simulation idea.

### Feasibility (analysis by the study team, nothing proved yet)

**Softmax: feasible, with a length-independent ball, in exact arithmetic at every length.**
For the rung-4 task families the winning key beats key k by a score gap of at least
γ·|j − k| (position term for wanted keys, a length-scaled penalty for unwanted ones, and
the penalty exceeds γ·n > γ·|j − k|). The softmax weight outside the winner is then at most
2·Σ_{r≥1} e^{−γr} = 2/(e^γ − 1), a geometric sum that does not grow with length. With γ
about 16 the leak is about 2e-7. A relative weight perturbation changes γ by 0.5% and
nothing else. So no temperature that depends on n is needed, for these tasks. Counting
tasks stay out (rung 6).

**IEEE binary32 for + − × ÷: feasible, modelled concretely.** Plan: define the binary32
grid (significand below 2^24, exponents from the subnormal range to the largest finite
value) and let `fl` be ANY round-to-nearest function onto it (the tie rule does not matter
for the proofs, so round-to-nearest-even is one instance). Prove from that definition:
relative error 2^-24 in the normal range, absolute error 2^-150 in the subnormal range,
monotone, exact on grid points. Overflow is handled by proving that no intermediate value
leaves the finite range, not by assuming it. NaN, infinities and signed zeros then never
arise. This is the same level as TorchLean's round-on-reals model; the bit-level encoding
is not re-proved here. No library download is needed (FloatSpec and TorchLean target other
Lean versions and would mean a new Mathlib build, which the lab rules forbid).

**exp: not IEEE, so it enters as a stated hypothesis.** IEEE 754 does not require exp to
be correctly rounded and PyTorch's is not specified. The theorem will assume an accuracy
bound on the float exp (relative error a small multiple of 2^-24 plus the subnormal term,
non-negative result) and say so. Whether the installed PyTorch meets it can be tested, not
proved.

**Operation order: stated, not PyTorch's default.** torch's vectorised softmax, sum and
matmul use SIMD orders and possibly fused multiply-add that are not specified. The theorem
will be about a stated order (max-subtracted softmax, sums left to right, no fusion), and
the PyTorch module will implement exactly that order with scalar float32 operations. The
ordinary vectorised PyTorch forward pass gets a numeric comparison, not a theorem.
A stretch goal, only if cheap: sums in any order.

**Length bound: 65,535 positions again** (2^16 − 1). Position features are exact up to
2^24, but score rounding error grows like 2^-24·n times the score scale and must stay well
under the gap between neighbouring positions. In exact arithmetic the same theorem gives
every length.

**"Loadable in PyTorch": yes, as our own small module** (position features [1, i, n], no
layer norm, residual MLP), not `nn.TransformerEncoder`. torch 2.15 CPU is already
installed here.

**Risk:** the proofs are much harder than rung 4's (geometric leak sums through rounded
left-to-right summation, underflow terms, overflow bounds). The lemma kit must carry most
of that or Sonnet will fail; rung 4 suggests that with a strong kit the per-task work is
routine. The framework is the stronger model-level part and the study team run writes it itself.

## Re-statement of the narrow "first" after Rush's work (2026-11-13)

Sasha Rush's "Lean Verified Transformers" (https://srush.github.io/lean-transformer/, repository srush/lean-transformer; human-written text, AI-written proofs; exact rationals; a "softmax-like" normalisation, 1 + relu divided by the sum, not an exponential) has Lean theorems about transformer blocks for arbitrary weights, as we read the page at every sequence length: permutation equivariance of attention layers and blocks, batch invariance, tensor and data parallelism. So "Lean theorems at all lengths about transformer blocks" are not new. It proves no statement that a network computes a specific task, has no weight ball and no rounding. The narrow "first" therefore stands only in this form: machine-checked proofs that specific written transformer weights compute a task at every length, for every weight setting in a stated relative ball, and under a modelled rounding model up to a stated length. The caveat is unchanged: this is an abstract-level web search, and "not found" is weaker than "does not exist". Lince's repository (read through its README) covers a trained softmax transformer on a finite domain with exact real softmax, not a weight ball or rounding.

## Rung 6a (gated softmax transformer, additive weight ball, every length): novelty check, 2026-11-14

Two targeted web searches plus two abstract pages opened today. Same caveat as before: a
search of abstracts and summaries; "not found" is weaker than "does not exist".

| Work (page opened 2026-11-14 unless noted) | What it has | What it lacks for this target |
|---|---|---|
| Opper, Fernandez, Smolensky, Gao, "TRA: Better Length Generalisation with Threshold Relative Attention", arXiv:2503.23174 (v4 Oct 2025) | An architecture close in spirit to ours: "selective sparsity" removes irrelevant keys from the attention softmax entirely, and relative positional distance is computed only between the query and the keys that remain; trained models, reported length-generalisation gains | No theorem, no proof assistant, no weight-perturbation statement (per the abstract) |
| Basu, Basu, Deb, "Structural Sensitivity in Compressed Transformers: Relative Error Propagation and Layer Removal", arXiv:2603.20991 (v2 May 2026) | Lean 4 machine-checked per-matrix error bounds (norm inequalities) for weight-matrix compression error in transformers | Not about a network computing a task, sequence length or an all-inputs correctness statement (per the abstract) |
| Shi et al. 2020, "Robustness Verification for Transformers" (search summary only, page not opened) | Numerical robustness verification for INPUT perturbations | No weights, no proof assistant |
| Weng et al. AAAI 2020; Elmecker-Plakolm et al. (already in the report) | Numerical weight-ball certificates for trained ReLU networks | Fixed input size, not transformers at every length, not proof-assistant-checked |
| Izzo, Nichani, Lee, "Quantitative Bounds for Length Generalization in Transformers" (search summary only) | Theory of length generalisation, finite versus infinite precision | Paper proofs; no weight ball; not mechanised |

**Verdict.** Not found: a proof-assistant-checked theorem that a transformer computes a
task at every input length for every ADDITIVE perturbation of every weight in a stated
ball. **What is not new, and must be said:** removing keys from the softmax by a threshold
and using relative position for the rest is TRA's idea (for trained models, without
proofs); our gate differs in that it thresholds a ReLU of the key's own state and the
position bias runs over all positions, but the report must not present key gating as
our invention. Machine-checked weight-error bounds for transformers exist at the level
of matrix norms (Basu et al.).

## Rung 6b (collision bound), search of 2026-11-14

See `PREREG_R6.md`, section "Novelty". Summary: we did not find a machine-checked
necessary weight-ball radius for a transformer on a counting task. The general
phenomenon is known: Hahn and Rofin (arXiv:2402.09963, Theorem 6) bound average
directional sharpness for soft-attention transformers computing sensitive functions, and
recall that Chiang and Cholak's parity construction (arXiv:2202.12172) is fragile in one
parameter. Ours is a worst-case, explicit-constant special case for hard attention and a
restricted class. Also opened: arXiv:2602.05896, 2605.12171, 2501.02535, 2609.24188, and
the NeurIPS 2026 workshop page 157626. Scope: abstracts (full text for Hahn and Rofin
only), no GitHub code search.
