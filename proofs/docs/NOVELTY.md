# Lane 4 novelty re-check (2026-11-11)

Run before any doctor run, as LANES.md requires. Re-run before any claim.

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
| ctrimm/weight-space-programming | 2026-11-07 | LLM writes MLP weights that equal benefits formulas (piecewise-linear); pre-registered, frozen hashes, trained twins | No. Dense grid tests, error ~1e-12. **Closest to rung 1's task and its trained-twin control** |
| arXiv 2610.24548 (Browne, Lee, Salvi) | 2026-10-17 | LLM agent writes GPU kernels and proves them equal to spec in Lean (Velvet), over floats | Yes, but for kernel code, not weights |
| TorchLean, arXiv 2602.22631 (ICML 2026) | 2026-02 | Lean 4 network semantics, bound propagation, certificate checking | Infrastructure; no LLM-written weights |
| arXiv 2603.20991 | 2026-03 | Hand-built transformer for belief propagation, verified in Lean | Human-built, one construction |
| brettkoonce/lean4-mlir | 2026 | Gradients proven; small nets with `native_decide` | Training code |
| fxeqxmulfx/transformer | 2026 | Lean formalisation of manuscripts on small GPTs; trained models; 39 unfinished statements | No all-lengths theorem for written weights found |
| arXiv 2506.19104 | 2025-06 | Exact ReLU sorting networks by construction | Paper proof only |
| Brucker & Stell (Isabelle AFP 2025); Coq piecewise-affine nets (arXiv 2301.12893) | 2023-25 | Formal semantics of feed-forward nets | Human proofs; no LLM, no written weights |
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
| Jiang, Hague, Rümmer, Lin, arXiv 2602.16473 (Feb 2026; abstract read) | Verifies **C-RASP programs** by translating to Lustre and using SMT-based model checkers; also learns C-RASP programs from examples | **Closest.** Unbounded-length verification, but of programs, not weights; SMT trust base, no proof assistant; no LLM. Must be cited. |
| Yang & Chiang, C-RASP, arXiv 2404.04393 | Paper proof that C-RASP compiles to future-masked soft-attention encoders for any length | No. Paper proof of a compiler, not a checked proof of given weights |
| Tracr, arXiv 2301.05062 | Compiles RASP to weights | No. Correctness not mechanised |
| "Quantitative bounds for length generalization", ICLR 2026 | Bounds how many lengths must agree before two limit transformers agree everywhere | No. Paper theory; but it means "test up to length N" can in principle be a proof for a restricted class. Worth one sentence |
| Compact proofs of model performance, arXiv 2406.11779 | Computer-assisted proofs about a trained Max-of-K transformer | No. Fixed length, trained weights |
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
| Hahn 2020; Chiang and Cholak, "Overcoming a Theoretical Limitation of Self-Attention", ACL 2022 | Paper proofs that for PARITY-like languages the output margin of a transformer shrinks as inputs get longer; remedies by layer norm or scaling logits with log n | **The fragility is known in theory.** "Exact all-lengths constructions have margins that vanish with n" is not our discovery |
| Merrill and Sabharwal, "A Logic for Expressing Log-Precision Transformers", NeurIPS 2023; fixed-precision characterisations (arXiv 2505.23623); "Length Generalization Bounds for Transformers", arXiv 2603.02238 | Paper theory: uniform attention over n positions needs about log n bits; fixed-precision transformers recognise much less | The float32 failure of our sort network is the expected consequence. Not machine-checked, not about a weight ball |
| arXiv 2602.16473 (already in this memo) | C-RASP programs verified with SMT model checkers, all lengths | All lengths, but programs, exact arithmetic, no weights, no proof assistant |
| R. J. George, "Verifiable Transformers in Lean", June 2026 (web article) | Lean replay of a tiny trained GPT on 256 fixed prompts with Lean `Float`; robustness figures come from an SMT tool | Lean and a transformer, but a finite input set, no weight ball, no rounding theorem (the author lists that as future work) |
| "Towards Verifiable Transformers: Solver-Checkable Circuit Explanations", arXiv 2605.24033 | Solver-checked properties of a GPT-2 circuit on a 1,280-prompt domain, real arithmetic | Finite domain, no weight perturbation, no floats |
| "Conic Certification of Transformer Attention", arXiv 2611.00585 | Numerical certificates for softmax attention under input perturbation, GPT-2 | Inputs not weights; numerical; fixed length |
| Lean 4 attention formalisations (PLDR-LLM maths, arXiv 2608.10288; "Formally Verified Autoresearch ... Multi-Head Attention" and "Identifiability of Deep Normalized Attention", NeurIPS 2026; brettkoonce Lean 4 deep-learning project) | Lean proofs of algebraic or expressivity facts about attention, or of backward-pass correctness | Lean and attention, but none proves a task correct at all lengths, none has a weight ball or a float model |
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
  every unit read τ·n or τ·n². So **no task has a length-independent absolute ball in the
  rung-2 architecture**; the radius must shrink like a power of 1/n.
- **Relative ball** (every written weight w becomes w·(1+d), |d| ≤ τ; zeros stay zero).
  This is the model of rounding a stored weight to a float. It is the one used below.

| Family | Length-independent relative ball? | Why |
|---|---|---|
| add (digit-wise sum with carry) | **Yes**, with the right mechanism | The carry needs only "the nearest earlier position that is not a propagate". See the note under the table: the usual bonus score fails, a penalty score works. No counting. |
| "nearest / first earlier position whose token is in a set", "previous occurrence of the current token", latch-like tasks | **Yes** | Same mechanism |
| parity | **No**: radius must shrink like 1/n | It needs the count k as an average k/n. A relative error d on a value weight turns k into k(1+d), which is off by more than 1/2 once d·n > 1/2. One flipped symbol must flip the answer (Hahn's sensitivity argument), so no construction through averages avoids this. |
| dyck | **No**: 1/n | Needs the sign of a prefix sum that is exactly zero at balance; a relative error of d on the +1 and −1 weights moves a balanced sum by up to 2·d·n. |
| sort | **No**: 1/n | Needs exact counts, as parity. |

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
a length-independent ball; tasks that must count (parity, dyck, sort) do not.

So for parity, dyck and sort the honest statement is "correct for every length n and every
relative perturbation up to c/n", equivalently "for a fixed τ, correct up to length c/τ".
With float32 storage (τ = 2⁻²⁴) that is still lengths in the millions.

**Floats.** A float forward pass cannot be correct at *every* length for any task that
tells neighbouring positions apart: float32 cannot represent consecutive integers above
2²⁴. So the float statement must carry a length bound for every family, including add.
The all-lengths claim can only be about exact arithmetic with a weight ball.

