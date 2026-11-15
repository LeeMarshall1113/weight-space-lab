# PREREG_RNN: kernel-checked all-lengths weight-ball certificates for TRAINED RNNs (2026-11-14)

It is written before any training (it builds on an earlier scope note that is not included). Later changes are dated amendments, made before the step they
affect.

## Claim scope, after reading the closest prior work in full
- **Jacoby, Barrett & Katz (ATVA 2020, 2004.02462, read in full).**
  - Queries are ⟨P, N, Q, T_max⟩ with a **bounded** horizon. Experiments use T_max = 2-20,
    and one at 180.
  - Invariants are time-dependent linear bounds (e.g. v ≤ α·t), found by MILP and proved by
    Marabou (SMT/LP).
  - **Input** L∞ perturbations, on trained speaker-recognition RNNs.
  - No weight perturbation, no proof assistant, no all-lengths claim. Their linear-in-t
    invariants loosen as t grows.
- **Khmelnitsky et al. (2009.10610, ATVA 2021, read in full via ar5iv).**
  - They check L(RNN) ⊆ L(spec DFA) through an L*-learned surrogate.
  - "Surrogate ⊆ spec" is checked exactly; "RNN ⊆ surrogate" only **statistically**
    (ε, γ PAC bounds).
  - No all-lengths guarantee, and termination is not guaranteed. No weight perturbation, no
    proof assistant.
- **Zhang et al. (ECAI 2020), only the abstract was available to me.** "Polytope propagation,
  invariant detection, CEGAR" on trained cognitive-task RNNs.
  - Their invariants may give unbounded-time results for trained RNNs.
  - So **I do not claim "first all-lengths verification of a trained RNN"**.
- **Omlin & Giles (1996):** all-lengths stability, but for *constructed* RNNs.
- **The claim is scoped to the combination:**
  - **weight-ball** (every weight within τ, constant across the run or even varying per
    step);
  - **all lengths**;
  - **exact regular-language correctness** against a DFA spec;
  - **kernel-checked** in Lean;
  - **for trained nets**, with the fraction of trained nets for which it succeeds measured.

  The technique (an interval-domain inductive invariant) is classical.

## Arms, labelled honestly
- **ORD (ordinary training).** A result here reads "ordinary training".
- **SAT (trained to be certifiable).** Same data, same architecture, same accuracy gate,
  plus a saturation-margin penalty that trains *toward* certifiability.
  - The nets are still trained, and a SAT-only result is reported as "trained to be
    certifiable", never as "ordinary training".
  - Results are accuracy-matched: every compared net passes the same exactness gate.

## Languages, nets, training
**Languages** (Σ = {0, 1}):

| | Language | DFA states |
|---|---|---|
| L1 | parity of 1s (accept if even) | 2 |
| L2 | number of 1s mod 3 = 0 | 3 |
| L3 | Tomita 4: no substring 000 | 4, including the sink |

**Net.** Elman cell with clipped ReLU σ(z) = min(max(z, 0), 1):
- h_{t+1} = σ(W h_t + U e(a_t) + b), with h_0 = 0;
- read-out y = v·h_T + c;
- accept iff y > 0, and the empty string is judged by y(h_0).

**Training (ORD).** All weights are float64.
- Strings: lengths uniform in 0-20, labelled by the DFA, half positive by resampling.
- BCE on the final read-out; Adam lr 3e-3; 4,000 steps; batch 128; ≤ 2 threads.
- Seeds: dev 0-3, test 100-107, per arm per language.

**SAT.** ORD plus 0.1 · mean over all steps and units of relu(min(z + μ, 1 + μ − z)), with
μ = 0.1. This pushes every cell pre-activation z outside (−μ, 1 + μ), so each unit is
saturated.

**Quantization.** Every weight and bias goes to the nearest multiple of 1/256. All checks
are on the quantized net.

**Exactness gate** (empirical, float64 forward on the quantized weights):
- correct on all strings of length ≤ 12 (8,191 strings);
- correct on 1,000 random strings of length 200 (seed 7).

**Width d.** The smallest of {4, 8, 16} at which ≥ 3/4 dev ORD seeds pass the gate,
**per language**. SAT uses the same d.

## Certificate
**Boxes, spec-aware (allowed in stage 1).**
1. Reached states come from the gate strings, labelled by the DFA state of the prefix.
2. B_q = bounding box per state, inflated by m ∈ {0, 0.01, 0.03, 0.1} (first success
   wins).
3. Iterate B_q ← B_q ∪ hull(IBP image of B_p under a, over all (p, a) with
   δ(p, a) = q), with weights in the τ-ball and the result clipped to [0, 1]^d.
4. Cap: 200 rounds.
5. All in exact rationals for the final check.

**Statement (Lean).** For all perturbations dW, dU, db, dv, dc with every entry |·| ≤ τ,
and every string w ∈ Σ*:

    sign(read-out after running w) = A.accepts w

That is: > 0 if accepted, < 0 if rejected.

**Proof route.** The checks are:
- h_0 ∈ B_{q0};
- ∀ q, a: the IBP image of B_q under a is ⊆ B_{δ(q,a)};
- ∀ q: the read-out's IBP interval on B_q has the accept sign.

From these, induction on w.
- One cell step reuses `rows_sound` from the frozen `Bridge/IBP.lean`. Interval input is
  `Bnd`, the concatenation of the box with the one-hot symbol.
- A new clipped-ReLU interval lemma is added.
- **Kernel check.** Each check by `decide +kernel`, one lemma per check. No
  `native_decide`; axioms printed.
- **Corollary.** The same theorem holds when the perturbation differs at every step.

**Primary τ = 1/1000.** The largest certified τ is found by bisection on the box search.

## Primary outcome
Test nets that pass the exactness gate **and** have a kernel-checked certificate at
τ = 1/1000, per language and arm (out of 8).

## Non-vacuity and controls
- **Tightness.**
  - Smallest found break: random strings up to length 1,000, plus a gradient search on
    weights within radius r for the most fragile strings found. A break is confirmed by an
    exact rational run, and only on strings ≤ 200 so that exact arithmetic stays feasible.
  - Ratio = smallest confirmed break / largest certified τ.
  - Reported per net. A failed search is reported as "no break found up to r".
- **Random-net control.** 8 untrained nets per language at the chosen d, certified against
  the spec. **Expected 0/8**; anything else is a bug and stops the run.
- **Trivial-language control.** The constant-accept language, d = 4, 4 ORD seeds. This
  calibrates how easy certificates are when there is nothing to track.

## Bars (frozen now)
- **Pass (level 2):** for some arm, ≥ 6/8 on L1 **and** ≥ 6/8 on L2. Reported with the
  arm's label: ORD = ordinary training, SAT = trained to be certifiable.
- **Structured effect:** SAT − ORD ≥ 3 on any language (one-sided Fisher exact).
- **Level-3 candidate:** ≥ 6/8 on L3 for some arm, **and** median tightness ratio ≤ 10 on
  those nets, **and** the random control at 0/8.
- **Kill:** ORD ≤ 1/8 **and** SAT ≤ 1/8 on L1.
- **Dev stop:** report and stop if either holds:
  - no d ≤ 16 gets 3/4 ORD dev seeds through the gate on L1;
  - the box search converges on **no** dev net of either arm on L1.

## Stage 2 (pre-stated; opens only on a pass)
**Spec-free extraction.**
- k-means on reached states, with k chosen as the smallest for which the box check
  succeeds.
- The certificate then proves net ≡ extracted DFA E.
- A Lean check of E ≡ spec by product-DFA reachability, kernel-evaluated.
- Run on L3 plus two random 5-6-state DFAs, with d up to 32.
- Bars set in an amendment before stage 2 runs. Per the scope, this, or the same invariant
  on a trained SSM layer, is what could lift the result past level 3.

## Procedure and freezing
1. **Lean framework.** `Bridge/RNN.lean` (imports `Bridge.IBP`, unchanged). Built and
   tested on dev nets. Its hash is **frozen in an amendment before any test seed is
   trained**, together with the training, box-search, export and break-search scripts.
2. **Dev.** Width per language; box-search diagnostics. Not outcomes.
3. **Test.** One script run per language and arm, not inspected before scoring.

## Compute
- **CPU:** training, gate, box search and break search. One job, ≤ 2 threads.
- **Lean:** one build at a time (bridge: 4-5 GB).
- No doctors, no proof agents.

## Dev result (2026-11-14): the dev stop fires; amendment A1 proposed, not applied
**Widths by the rule:** L1 d = 8, L2 d = 16, L3 d = 8.

| Language | ORD dev exact at chosen d | SAT dev exact at the same d | ORD at smaller d |
|---|---|---|---|
| L1 | 4/4 | 1/4 | 0/4 at d = 4 |
| L2 | 4/4 | 2/4 | 0/4 at d = 4 and 8 |
| L3 | 4/4 | 2/4 | 1/4 at d = 4 |

**The box search converged on no dev net of either arm on L1. The pre-registered dev stop
fires.** Logs: `results/rnncert_dev.jsonl`.

**Diagnosis (checked; not a bug):**
- **One box per DFA state is too coarse for trained nets.** On L1 the trained net reaches
  2-22 *distinct*, almost fully saturated hidden points per DFA state (97-100% of
  coordinates at 0 or 1).
  - Their bounding box spans [0, 1] in most coordinates, overlapping the other state's box.
    So the read-out cannot be sign-correct on the boxes, even at τ = 0.
  - The net implements a *finer* automaton than the minimal DFA.
- **L2 at d = 16:** 85-104 distinct points per DFA state.
- **The method itself works where the net happens to use one point per state.** The one
  L3 net that passed the gate at d = 4 (seed 2, not the chosen width) has one point per
  DFA state for three states. Its box search succeeds at τ = 1/1000 with margin 0.

**Proposed amendment A1 (needs the maintainer's go; nothing run under it):**
- **Cluster invariant.** One box per *cluster* of reached states (distinct saturated
  points, rounded at 0.01), with a cluster transition table and a map π: clusters → DFA
  states. Each cluster is labelled by its DFA state, so the search is still spec-aware; it
  is not spec-free extraction.
- **Checks:**
  - h₀ ∈ B_{c₀} and π(c₀) = q₀;
  - for every (c, a): the IBP image of B_c ⊆ B_{c'} for the tabled c', with
    π(c') = δ(π(c), a);
  - the read-out sign on B_c = acc(π(c)).
- **Same theorem, by the same induction.** `Bridge/RNN.lean` gains π and an abstract
  transition table; this is a small change.
- **What it really is.** It is still a finite-state abstraction of the net that is checked
  to simulate the spec. It is closer to stage 2 (extraction), but labelled by the spec.
- **Nothing else changes:** the dev-stop criterion re-applies under A1, as do all bars.

## Amendment A1 (2026-11-14, maintainer's go; before the second dev run, the freeze and any test seed): cluster invariant
This is the **one** design revision. If the cluster-box search also converges on no L1 dev
net, the stop is final and the dev finding is the report.

**Collecting reached states (fixed).** Float64 forward of the quantized net on the gate
strings: all 8,191 strings of length ≤ 12, plus the 1,000 random strings of length 200
(seed 7). Every prefix state is recorded with its DFA state.

**Clustering (mechanical).**
- **Method:** within each DFA state separately, greedy leader clustering in L∞ distance
  with ε = 0.05, over points in recorded order. A point joins the first cluster whose
  leader is within ε; otherwise it starts a new cluster.
- **Number of clusters:** whatever this yields. There is no tuning.
- **Cap:** 256 clusters in total. Over the cap is a failure for that net.
- Clusters are pure by construction: each carries its DFA state, π(c).

**Boxes and closure.**
- **Initial box:** B_c = the member bounding box ± margin m (m ∈ {0, 0.01, 0.03, 0.1},
  first success wins), clipped to [0, 1], rounded outward to 1/65,536.
- **Transition table:** for each (c, a), the target T(c, a) is chosen among clusters c'
  with π(c') = δ(π(c), a).
  - The IBP image of B_c (with τ-perturbed weights) is computed.
  - T(c, a) is the lowest-index c' whose box contains the image. If there is none, it is
    the c' whose box centre is nearest the image centre (L∞), and B_{c'} is enlarged to
    the hull.
- **Iteration:** to a fixed point, 200 rounds maximum.
- **Closure.** The final boxes are closed under the interval image, so states never
  sampled are covered by the proof, not by sampling. Sampling only seeds the boxes.
- **Read-out:** each B_c must have the sign of acc(π(c)).

**Lean (`Bridge/RNNClust.lean`; `Bridge/RNN.lean` unchanged).**
- The abstract automaton (clusters, T, start cluster c₀) is certified by the existing
  `certR`, with accept set acc ∘ π.
- A new lemma: if π(c₀) = q₀, and π(T(c, a)) = δ(π(c), a) for all c < n_C and a < k, then
  acc(π(run_T c₀ w)) = acc(run_δ q₀ w) for every w.
- **The final theorem is the same spec statement as before:** sign = acceptance by the
  spec DFA, for every weight in the τ-ball and every length.
- The proof is re-done and its hash frozen before any test seed.

**Reported per net:**
- the number of clusters n_C;
- certificate size: n_C boxes and n_C·|Σ| step checks plus n_C read-out checks.

The size is **constant in input length but grows with the abstract automaton size**. It is
not bounded by the minimal DFA.

**Unchanged:** arms (SAT as registered), bars, controls, the dev-stop criterion (re-applied
under A1), and stage 2.

## Amendment A2 (2026-11-14): second dev result; framework and scripts frozen before any test seed
**Second dev run under A1** (`results/rnncert_dev2.jsonl`), cluster-box certificate at τ = 1/1000:

| Language | ORD | SAT | Clusters |
|---|---|---|---|
| L1 | **4/4** certified | 1 of 1 gate-passing certified | 5-14 |
| L2 | 0/4 | 0/2 | 9-116 |
| L3 | 1/4 | 2/2 gate-passing | 8-55 |

The dev stop does **not** fire (L1 converges).

**Pipeline check on a non-dev net** (L3 ORD, d = 4, seed 2, not in the dev or test sets):
- kernel-checked cluster certificate in 12.7 s at 3.9 GB, standard axioms;
- largest certified τ 0.0062; smallest exactly confirmed break 0.0107 (ratio 1.72).

**Test procedure.** `rnncert/test_all.sh` runs, once:
- 8 test seeds × {ORD, SAT, RND} for L1 (d = 8), L2 (d = 16), L3 (d = 8);
- the TRIV control;
- break searches on every certified non-RND test net.

Lean certificates are then exported and kernel-checked one at a time.

**Frozen (sha256):**
- `*bridge/lean/Bridge/RNN.lean` bfae3ab72825efffda4c0771c9de666f31510aadd2759f6fe202fd49bd7bd2be
- `*bridge/lean/Bridge/RNNClust.lean` 2608df077f0fe01410473dcd8839e851409ef80f947b64697e4e4f58f5bc5288
- `*bridge/lean/Bridge/IBP.lean` fbb8086cbcda3c10361d1c4ceef285c41dc0956456ebf84fe5ed45413f35c7a9
- `*bridge/lean/Bridge/Region.lean` 4944e9222588ce34543080b82a1e46de314a8d7e7e4317f8bd066ba6d099697d
- `*bridge/lean/build.py` fcca396b1d68064d634b0084c08fdbd8c748cb5bb2460f87ec848fed58eb9f09
- `*rnncert/rnncert.py` c5e1d44ee68877d6a07823759d8d289c5ac280dc77f16b0ee96f1e8d168767da
- `*rnncert/breaks.py` 74a12621d61f7bbd8b375a8798ce4b826852058f71aaf70711ebe817c2a541f2
- `*rnncert/test_all.sh` d081c7773330abbf7a81a912d59cd57fc87134a064a841b76ab4cf0507b8262f
