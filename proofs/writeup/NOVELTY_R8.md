# Novelty re-check for the rung 8 claim (2026-11-21)

Draft; updated as results change. Written by a Sonnet side run from
`RESULTS_R8.md`, `PREREG_R8.md`, `SCOPE_R8.md`, `RESULTS_R7.md` (lab head 71b49ab8) and from web
searches run today. **Limits of the check:** web search over abstracts, snippets and project
pages (about ten searches today, on top of the 2026-11-20 search recorded in `SCOPE_R8.md` and
the earlier sections of `NOVELTY.md`). I could not open full texts or repositories in this run
(no page fetcher), so everything marked "snippet" below is read from search summaries, and the
teal-sea, Vertex-Softmax, TorchLean and Gross et al. descriptions are carried from the
2026-11-20 reading in `SCOPE_R8.md`, not re-read. "Not found" is weaker than "does not exist".

## The claim being checked

A Lean-kernel-checked proof (`decide +kernel`, no `native_decide`, axioms `propext`,
`Classical.choice`, `Quot.sound`) that gradient-trained, standard causal softmax-attention
networks (one block, width 8, two heads, relative-position slope fixed at 24, no gate, no
LayerNorm, no position embedding) compute their task (modular addition of the last two tokens)
at every input length (exact arithmetic; at most 65,535 tokens in a binary32 model with an
assumed accuracy for the float exponential), for the weights exactly as trained, and for every
additive weight change of at most 2^-14 around the trained weights rounded to multiples of 2^-14.
19 of 20 fresh seeds accepted; the checker (one soundness theorem, `Lane4.R8K.sound8`) was frozen
before training; eight controls rejected. The ball was shrunk from 1/1000 to 2^-14 on the tuning
set so that task A passes.

## Verdict, first

**Nothing found already does this.** I found no earlier result with all of: a proof-assistant
kernel check, a trained softmax-attention network, an unbounded input length, and a weight ball.
**But the claim must not be worded as "first".** Parts of it are known, one neighbour has
a kernel-checked all-length theorem for a trained network (teal-sea, a threshold RNN), and the
closest transformer work (Stambler et al.) has a computer-aided proof about a trained
transformer under unbounded-ish free tokens, without a kernel check. What is new is the
combination, in a narrow setting.

## What is and is not new, part by part

| Part of the claim | Nearest prior work | Is it new here? |
|---|---|---|
| Kernel-checked theorem that a **trained** network is correct at **every** input length | **teal-sea/lean-checked-network** (T. Lince): trained threshold RNN adder (4 and 16 units, integer weights), `sums_correct` for every input list, by a finite certificate over reachable states (`decide +kernel`) plus induction; exact integers. (Read 2026-11-20, `SCOPE_R8.md`.) | **Not new.** Their result, and the certificate-plus-induction pattern, came first. Never say "first trained network proved at every length". |
| The same for a **softmax-attention** transformer | teal-sea's transformer is fixed 3-token input, exact real softmax, integer-quantised weights (all 12,769 pairs by evaluation). Gross et al. (arXiv 2406.11779): proofs about trained Max-of-K transformers at a fixed length. Rush's "Lean Verified Transformers": Lean theorems at every length but about equivariance/invariance, with a softmax-like normalisation, no task correctness. | **New in this combination** (softmax, all lengths, task correctness, trained weights, kernel). Within the limits of the search. |
| **Weight ball** (every weight within a radius) | Weng et al. AAAI 2020 and similar: numerical weight-ball certificates for ReLU nets at fixed input size, not kernel-checked. This lab's own rungs 3 to 6a, 7. TorchLean (arXiv 2602.22631): Lean 4 IBP and CROWN-style certificate checking for fixed shapes, input regions. | **Not new as an idea; new together with all-length transformers in a kernel.** |
| **All input lengths for a softmax transformer, certificate form** | Stambler, Nezhadi, Coudron, "Provably Overwhelming Transformer Models with Designed Inputs" (arXiv 2502.06038; snippet): an algorithm that takes a *trained* transformer and a fixed token string and outputs a computer-aided proof that the output is insensitive to additional free tokens at a fixed context size, cost roughly quadratic in the prefix and cubic in the free length. Single layer, attention head, layer norm, ReLU MLP. **Closest transformer neighbour.** | Different statement (insensitivity to a suffix, bounded free length, no task spec, no weight ball), and "computer-aided" rather than kernel-checked as far as the snippet says. Cite it. Our "every length" is robustness to an unbounded prefix for a local task, which is in the same spirit. |
| **A checker with one soundness theorem**, then no proof work per network | Vertex-Softmax (arXiv 2605.10974): exact softmax box optimisation, paper proofs in real arithmetic, float implementation not a certificate; auto_LiRPA-style verifiers. Huang et al., AAAI 2026, parameterized abstract interpretation for transformers: tighter linear domains, fixed length, not formalised. Conic Certification of Transformer Attention (arXiv 2611.00585; snippet): conic bounds on attention-head output shift under *input* perturbation, reported length-independent gap, no proof assistant in the snippet. | **Not new as a numeric technique; new as a formalised, kernel-checked checker for all lengths.** The checker is a sufficient condition and cannot be complete: Yang et al. (arXiv 2603.02238) show no computable length-generalisation bounds exist in general; a related succinctness paper (arXiv 2510.19315, snippet) reports verification is undecidable for softmax transformers with unbounded precision. |
| **binary32 rounding model** in a kernel | TorchLean (bit-level binary32 model in Lean, fixed shapes). This lab's rung 5. | Not new in having a float model; the model here assumes the accuracy of the float exponential (`ExpM`). Say so. |
| Solver- or proof-checked claims about a trained transformer circuit | Somani, arXiv 2605.24033: SMT-checkable circuit claims on bounded finite domains, redesigned architecture, explicitly no arbitrary-length claim. Gross et al.: fixed length. | Different trade; fixed domain. |
| Other all-length work | Length-generalisation theory (Izzo et al., Huang et al. ICLR 2025 "A formal framework for length generalization"): paper proofs, no proof assistant. A Mamba/SSM paper (arXiv 2611.21952; snippet): a perturbation bound for selective state-space models at every sequence length, on input perturbations, paper proof. Yang et al. 2412.09925 and C-RASP: soft attention simulates hard attention, paper proofs. | Not mechanised; different object or statement. |

## New items found today beyond the 2026-11-20 list

None of these changes the verdict; each should be cited or watched.

1. **Stambler, Nezhadi, Coudron, arXiv 2502.06038** (v2 May 2025): the nearest transformer
   neighbour, described above. Not in the earlier lists.
2. **Conic Certification of Transformer Attention, arXiv 2611.00585** (Ataei): attention
   certification theory, input perturbations, GPT-2 experiments; no proof assistant in the snippet.
3. **A log-timescale perturbation bound for selective SSMs at every sequence length,
   arXiv 2611.21952**: an every-length bound, but for state-space models, input perturbations,
   a paper proof.
4. **Masked attention pooling invariant to padding and permutation: a formal proof in Lean,
   arXiv 2610.17132** (snippet): a Lean proof about an attention operation; not a task-correctness
   theorem, not trained weights, not a weight ball.
5. **LeanCert softmax interval bounds** (Lean 4, real arithmetic) and a Lean 4 softmax soundness
   blog post: ingredients, not the claim.
6. **From Transformers to Weighted Automata, arXiv 2610.04569**: identity testing for weighted
   automata derived from transformers; statistical, not a proof. Not close.

Searches that found nothing close, for the record: "Lean 4 kernel-checked trained softmax attention
all sequence lengths weight perturbation"; "formally verified transformer all input lengths
Coq Isabelle Lean floating point softmax"; "weight perturbation certification transformers all
sequence lengths verified checker soundness"; "inductive invariant verification trained
transformer unbounded length"; "certified robustness weight perturbations transformers arbitrary
length Lean proof-carrying"; "machine-checked proof trained recurrent network or transformer all
lengths Lean"; "Lean 4 binary32 softmax error bound". The "teal-sea" repository itself does not
come up in a plain search, which is a reminder that a search of abstracts does not find
repository-only work; there may be more such.

## Full-text readings added later on 2026-11-21 (by a fetch agent; not read by me)

These come from the project owner's fetch agent, which read pages today. Limits: each reading is a
summary relayed to me, not something I opened; the Lean sources and commit history of teal-sea
were not read; for Stambler et al. the abstract and about a third of the HTML were read directly
and the rest came through a summary.

**Stambler, Nezhadi, Coudron (arXiv 2502.06038).**
- Guarantee: output insensitivity to free tokens, for a *fixed* context size n_ctx (Theorems 4.4
  and 4.5). "Computer-aided proofs"; no proof assistant. Arithmetic is not stated.
- One trained weight setting; no weight ball; no task-correctness claim.
- Architecture: single layer with RoPE, LayerNorm and an MLP, width 512. It therefore covers
  LayerNorm and a much larger model than ours (width 8, no LayerNorm).
- Multi-layer bounds are described by the authors as "too loose to be useful in practice".
- Effect on the table: the row "All input lengths for a softmax transformer" should say "fixed
  n_ctx", not "bounded free length" alone; the difference from our statement is larger than I wrote
  (different statement, no ball, no task, no kernel), and they handle LayerNorm where we do not.

**teal-sea/lean-checked-network (Thomas Lince; README, RESULTS, VERIFY, STATUS read).**
- The every-length result is the trained RNN adder only (5 reachable states, induction).
- The transformer result is fixed-size: 12,769 input pairs, exact real softmax, quantised integer
  weights, exact matrices only.
- A partial single-weight robustness statement exists for the MLP's W2.
- Stated limit: "integer or exact-real models, not floating-point execution".
- MIT licence; built in October 2026; the proofs were written by AI agents.
- Effect on the table: teal-sea has no softmax-attention theorem at every length and no all-weights
  ball, which supports the "new in this combination" cell; it also has the proof pattern and the
  only trained-network all-length theorem, as already said. Our binary32 model is a difference
  (theirs is exact-only by their own statement).

## If something already does this

teal-sea already has the all-length kernel-checked theorem for a trained network and the
finite-certificate-plus-induction proof pattern, for a threshold RNN. Stambler et al. already have
a computer-aided all-free-token insensitivity proof for a trained single-layer transformer. If a
reader finds a kernel-checked all-length task-correctness theorem for a trained softmax
transformer before this one, the claim reduces to "a weight ball on top of it, with a checker
that has one soundness theorem".

## What is not new (say this up front)

- Certificate over a finite abstract state space plus induction on the input: teal-sea's pattern.
- Interval-style bound propagation and weight-ball certificates: Weng et al. and the numeric
  verification literature; this lab's own earlier rungs.
- Soft attention behaving like hard attention when the position bias dominates (the reason
  the prefix can be ignored): Yang et al. and the C-RASP line.
- A binary32 model in Lean: TorchLean.

## The strongest sentence that is safe to say

> In a search of abstracts and summaries on 2026-11-21 we found no earlier result that gives a
> Lean-kernel-checked theorem, one soundness theorem for a checker plus a generated proof per
> network, that gradient-trained softmax-attention networks of one block and width 8 compute a
> local task at every input length (exact arithmetic; up to 65,535 tokens in an assumed-accuracy
> binary32 model) for the weights as trained and for every additive weight change of at most
> 2^-14 around those weights rounded to multiples of 2^-14. The finite-certificate-plus-induction
> pattern and the kernel-checked all-length theorem for a trained network (a threshold RNN) are
> teal-sea's. That is a statement about one search, not that none exists.

Do not say: "first", "the first trained network proved at every length", "verified transformers",
"for all transformers", "robust to weight noise" without "2^-14, additive, around the rounded
weights", or "formally verified" without the limits below.

## Wording points a reader may misread (from `RESULTS_R8.md`)

- The 2^-14 ball is **around the trained weights rounded to multiples of 2^-14** (`W14`); the
  separate theorem `trained_exact_all_lengths` is for the weights exactly as trained, with no ball.
  The two statements should not be merged into "robust at 2^-14 around the trained weights".
- 2^-14 was picked on the tuning set after seeing that 1/1000 fails task A; the checker's design
  and constants were fitted to 18 to 20 earlier networks; 19 of 20 is a fresh-seed count for that
  recipe only. Amendment 1 raised the kernel limits (600 s and 4.5 GB to 900 s and 6 GB) after
  seeing a tuning-set result.
- Task A is local (the last two tokens), so "every length" means an arbitrarily long prefix is
  ignored, not long-range computation. Slope fixed at 24; no LayerNorm; width 8; one block; the
  lab's own task and recipe.
- Task B has 6 networks on fresh seeds and no bar; only 6 of 20 trained B networks compute the
  task at all.
- The float exponential's accuracy is assumed; the forward pass is the lab's own definition, not
  an existing framework's. Pre-registration commits are private.

## Mechanism rows: related work on extracting programs from transformers (added 2026-11-21, after v0.4)

The mechanism rows (a 5-state program read off the weights and checked equal to the network at
every length; attention-window facts) had no literature search of their own when v0.4 was
published. A search of abstracts and summaries on 2026-11-21 found no proof-assistant-checked
extraction of a finite-state program from a trained softmax-attention network at every input
length. It did find three related works that earlier versions of this note did not cite.
**Limits of the reading:** by a fetch agent, not by the author of this note; for the first two,
about half of the HTML text was read directly and the rest through a summary; for the third, only
a summary page (abstract and bibliographic record), not the paper.

| Work | What it extracts, and how | Guarantee that it matches the network | Difference from the mechanism rows |
|---|---|---|---|
| Andric, "BlockCert: Certified Blockwise Extraction of Transformer Mechanisms", arXiv 2511.17645 (Nov 2025) | Per-block surrogates with certificates, from weights and traced activations, on pretrained GPT-2 small, TinyLlama and Llama-3.2-3B | Per-block error measured on a finite set of traced prompts; a Lean 4 theorem composes per-block errors into a global bound, under an assumed all-input local bound and assumed Lipschitz constants. The certificate verifier is a Python tool in floating point. The paper says it does not give an all-input guarantee for real models | Works on real models, which ours does not. Its Lean theorem is conditional and its certificates are empirical; ours is unconditional in the kernel but for width-8 networks and a trivial program. No weight ball |
| Zhang, Wei, Sun, "Automata Extraction from Transformers", arXiv 2406.05564 (Jun 2024; ASE 2024) | A DFA, by training a recurrent surrogate on the transformer's representations and running L* on the surrogate; BERT-family encoders trained on Tomita-style languages | Empirical agreement rate on sampled strings (below 1 on some languages); no proof | Approximate and sampled; no proof assistant; no every-length statement; no weight ball |
| Adriaensen and Maene, "Extracting Moore Machines from Transformers Using Queries and Counterexamples", IDA 2025 (earlier versions 2024) | Moore machines by an extension of L*, with the transformer answering queries; one-layer transformers trained on regular languages | As far as the summary read says: tested faithfulness, often exactly the target machine; no formal proof found in the summary | Black-box learning and testing, not a proof from the weights; not read in full, so this row is the weakest of the three |

What this changes: the idea of reading a finite-state machine off a trained transformer is
**not new** (the two automata papers above, 2024), and "certified extraction" as a phrase is
BlockCert's. What the mechanism rows add is narrow: the extracted program is proved equal to the
network's behaviour at every length by the Lean kernel, for every weight in the ball, on networks
where the program is trivial because the task is. As before: "network equals a finite-state
program, kernel-checked, every length" was done first by teal-sea for a threshold RNN, and the
link between mechanism and proof is Gross et al.'s (arXiv 2406.11779).

Also seen in the same search, not close: two NeurIPS 2026 papers with Lean-checked theorems about
attention in general (arXiv 2610.25341 on the number of heads needed for symmetric Boolean
functions; a paper on identifiability of deep normalized attention). They prove properties of the
architecture, not of a particular trained network.
