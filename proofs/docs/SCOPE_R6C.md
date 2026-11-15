# Rung 6c scope: how far the impossibility line can be pushed (by hand only, 2026-11-14)

Nothing in this note is proved. No doctor ran and no Lean was compiled for it. The only
computation is a pure-Python test of the proposed syntactic class on the ten proved
rung-2 networks (`scratch/r6c_token_blind.py`, `results/r6c-token-blind.json`). The Lean
text in section 3 is a proposal and has not been type-checked.

Setting throughout: `Lane4.Seq.TNet` (rung 2): hard attention with ties averaged, eight
exact position features `1, i, i², 1/(i+1), (−1)^i, n, 1/n, i/n`, residual ReLU MLP,
affine read-out, exact rationals. Relative ball: every weight `a` becomes `b` with
`|b − a| ≤ τ|a|`; written zeros stay zero. Position features are not weights and are not
perturbed.

**Short answer.** A syntactic class is available and I believe it is provable in days:
"the network reads tokens only through global uniform averages". Membership is a
decidable check on the zero pattern of the weights. It contains 5 of the 10 proved
rung-2 networks (the three parity and the two sort networks), and the bound would cover
parity and sort rank with one theorem and one constant (about `1/L`). It does not
contain the Dyck or addition networks, and it is still far from `ParityNoBall`. Hahn and
Rofin's theorem does not formally imply any of this, but it is the same phenomenon, so
the level is "a known effect made exact, worst-case and machine-checked for a decidable
class", not a new effect.

## 1. What blocks `ParityNoBall` for every rung-2 network

`ParityNoBall` needs, for an arbitrary network that computes parity exactly, a relative
perturbation that breaks it at some length. The collision argument needs two (network,
input) pairs of opposite parity on which everything the read-out sees is identical. The
escape routes, and whether a relative ball with zeros fixed lets a network use them:

| escape route | can the network use it against the collision argument? |
|---|---|
| Several heads or coordinates carrying the count | **No, inside the class of section 3.** The adversary moves embedding entries, which sit upstream of every head, so all copies of a count move together. Redundancy does not help. |
| Nonlinearity (the MLPs) | **No, inside the class.** The collision makes the inputs of every MLP identical, so nothing about the MLP is used. Outside the class the MLP is not the obstacle either. |
| Compensating scalings (a later weight undoes an earlier one) | **No.** Weights are perturbed independently, so a network cannot arrange for a ratio of two weights to be exact. The one exact thing is a position feature, and a count always arrives multiplied by at least one embedding entry and one value entry. This is the mechanism behind every break we have seen: an exact `j/n` is compared with `ρ·k/n`, `ρ ≠ 1`. |
| Zeros that stay zero | **Yes, and it cuts both ways.** It is why the class of section 3 is closed under the ball (membership survives perturbation), and it is also what lets a network hide token information from later layers. |
| Attention selection (argmax sets are stable under small perturbations) | **Yes. This is a real escape.** A head that selects by content with an order-1 margin selects the same set for every network in the ball (rung 4 proved such theorems). Information that flows through WHICH positions are selected, and then through exact position features of those positions, carries no weight factor at the point of selection. |
| A token-reading head that is not a global average (causal or strict mask, or content-dependent selection) | **Yes. Real escape for the argument.** Its output depends on the arrangement of the tokens, not only on counts, so two inputs of opposite parity never look identical to it. The Dyck networks are of this kind (causal prefix averages). |
| Second block reading the tokens of the sequence | **Yes. Real escape for the argument**, as the independent AI reviewer said. Two inputs with different counts differ in at least one position, and a later head can attend to exactly that position. |

So the collision argument is complete exactly when tokens are read only through global
uniform averages. For everything else a proof must show that a fixed-depth network
cannot get the parity of a count out of stable selections and arrangement-dependent
averages. I believe that is true: the only source of a sign that alternates with `k` is
the feature `(−1)^j` read at a position whose index is tied to the count, and tying an
exact index to a count is the comparison that breaks. But "the only source" is a
statement about all networks of the architecture, which is a Hahn-type argument (choose
inputs on which no head can single out the changed position), and I do not have it.

## 2. Intermediate classes, in increasing order

**C0. Count channel (done, rung 6b).** Semantic; membership proved per network.
Constant `1/(2L − 1)`.

**C1. Token-blind networks (proposed target; section 3).** Tokens are read only through
heads with a zero score matrix and mask `all`, through their value matrices; no other
score, value, MLP or read-out weight touches a coordinate that distinguishes tokens.
Any number of blocks, heads and MLPs otherwise; the "decoder" is arbitrary.
- Proof idea. (a) Invariance lemma, by induction over blocks: for two networks that
  differ only in embedding entries and two inputs of the same length whose summed
  embedding vectors agree on the token coordinates, every other coordinate of every
  state agrees at every position, so the outputs agree at every position.
  (b) Collision: inputs over two token types with counts `(a, L − a)` and
  `(a + 1, L − a − 1)`; perturb the embedding rows of the two tokens entry by entry so
  that `a(1 + d₁) = (a + 1)(1 + d₂)` and `(L − a)(1 + d₁') = (L − a − 1)(1 + d₂')`. Both
  are solvable inside the ball once `a` and `L − a − 1` are at least `(1 − τ)/(2τ)`.
- Constant. Taking `a = (L − 1)/2`: a ball correct up to odd length `L` has `τ < 1/L`.
  Universal for the class (no network-dependent constant). About twice weaker than C0
  because both tokens' embeddings may be nonzero; if the uncounted token's row is zero on
  the token coordinates the C0 constant comes back.
- What it covers. Every target that separates two such count vectors: parity, sort
  rank (the outputs at position `a + 1` differ), majority, any exact count threshold or
  count modulo `m`.
- Does Hahn and Rofin imply it? No, formally (section 6). Morally yes.

**C2. C1 plus token reads through causal or strict uniform averages (prefix counts).**
Would add the Dyck networks. The collision argument fails here for a concrete reason:
two inputs must agree on the whole profile of prefix averages, and for profiles such as
`min(i, a)` against `min(i, a + 1)` a scaling that matches them beyond position `a`
breaks them before it. A different argument is needed (for example: one perturbation,
one input family, show the decoder's decision threshold is crossed). I do not have a
general one. Per-network theorems are available instead (section 4).

**C3. Any network whose read-out depends on the input through finitely many uniform
averages over input-independent position sets.** Contains C1 and C2. Same obstacle as
C2.

**C4. Depth 2, bounded heads, no syntactic restriction; then all of `shapeOK`.** This is
`ParityNoBall`. Hahn-type. Not days.

## 3. The syntactic class (C1), concretely

Let `T` be the embedding coordinates on which two real tokens differ (the BOS row is
ignored: a coordinate that only marks BOS is a function of the position). `tokenBlind N`
holds when:
- every head: no nonzero score entry `A[p][q]` with `p ∈ T` or `q ∈ T`; a nonzero value
  entry `V[r][c]` with `c ∈ T` only if `A = 0` and the mask is `all`;
- every MLP: `W1[h][c] = 0` for `c ∈ T`;
- read-out: `outW[c] = 0` for `c ∈ T`.

It is a Boolean function of the weights, so membership is `by decide`, and it depends
only on which entries are zero, so every network in the relative ball of a member is a
member. Proposed statements (not type-checked):

    def tokenBlind (N : TNet) (V : ℕ) : Bool := ...
    theorem tokenBlind_bound (N : TNet) (V s o : ℕ) (target : List ℕ → ℕ → ℚ) :
      N.tokenBlind V = true → s ≠ o → 1 ≤ s ≤ V → 1 ≤ o ≤ V →
      (∀ a L, a < L → target (replicate a s ++ replicate (L − a) o) (a + 1)
                    ≠ target (replicate (a + 1) s ++ replicate (L − a − 1) o) (a + 1)) →
      ∀ τ L, 0 ≤ τ → τ ≤ 1 → 3 ≤ L → Odd L →
        (∀ N', netRel τ N N' → ∀ valid w of length ≤ L, ∀ i, N'.out w i = target w i) →
        τ * L < 1

(with the sign-of-output form for parity). The separation hypothesis is checked by
`decide`-free arithmetic for parity and sort rank.

**Tested on the ten proved rung-2 networks (pure Python, exact weights):**

| network | family | token coordinates | member? |
|---|---|---|---|
| p05, p10, p29 | parity | [0] | yes |
| s00 | sort | [1] | yes |
| s01 | sort | [0, 1] | yes |
| d10, d15, d18 | Dyck | [0] | no: the token-reading head is a causal average |
| a00, a01 | add | [0..3], [0..2] | no: strict-mask heads whose scores and values read tokens; the MLP reads tokens |

**Is this "every network anyone writes in this architecture"? No.** It is every network
that reads tokens only through global averages, which is the natural way to compute a
permutation-invariant function (and is what Sonnet doctors wrote for parity and sort
five times out of five, independently). A network could read tokens positionally and
still compute parity; the bound says nothing about it. What the syntactic form buys is
that the bound applies to a new network by evaluating a Boolean, with no proof per
network, and that the class is closed under the ball.

## 4. Dyck depth and sort rank

- **Sort rank: covered by C1** with the same theorem (both sort networks are members;
  the count vectors `(a, L − a)` and `(a + 1, L − a − 1)` have different sorted
  sequences at position `a + 1`). Note the sort spec demands an exact integer output,
  so any change of output is a failure.
- **Dyck: not covered by any class I can prove.** The three Dyck networks compute causal
  prefix averages of a token weight, attend to the minimal prefix average, and compare
  with zero. What is available:
  (i) a per-network theorem, in the style of rung 6b's corollaries but proved by
  evaluating the perturbed network on an explicit input family (for example `(^a )^a`
  with the open-token embedding scaled by `1 + d`: the final prefix sum becomes `d·a`
  instead of 0, against a decision margin of order `1/n`), giving an explicit `O(1/L)`
  radius for each of d10, d15, d18. Each is about the size of the original correctness
  proof (a few hundred lines). No class, three separate theorems.
  (ii) Whether "balance" (the symmetric part of Dyck: equal numbers of opens and closes)
  can be separated out and handled by C1: not for these networks, since they read
  tokens causally.

## 5. Odds and cost

| step | odds it is kernel-checked | cost | Fable step? |
|---|---|---|---|
| C1 invariance lemma (induction over blocks, list-indexed states) | 75% | 2 to 4 Sonnet cases after I write the skeleton and the statement; 0.5 to 1.5M tokens; 1 to 2 days elapsed at one doctor | Possibly ONE: the head step of the induction (`Head.sel` and `Head.attn` agree when scores agree off the token coordinates, with `getD`/`zipWith` bookkeeping). I would try Sonnet twice first. |
| C1 collision and bound, given the lemma | 90% | 1 case, like kColl | no |
| C1 membership of the 5 networks by `decide` | 85% (risk: `decide` on rational lists is slow or stuck; fallback `simp`/`norm_num` per network) | 1 case | no |
| Parity and sort corollaries (separation hypothesis) | 90% | 1 case | no |
| C1 overall | about 60% in 2 to 3 days | 1 to 2.5M tokens | at most one |
| Dyck per-network theorems (3) | 60% each | 1 Sonnet case each, larger | no |
| C2 (a class with causal averages) | 15%; needs a new idea, not labour | unknown | n/a |
| `ParityNoBall` for depth 2 | under 5% in this project | n/a | n/a |

The main risk for C1 is not the mathematics but statement faults, as at rung 6b (the
`par < 2` slip). Before any proof I would test the candidate statement against the ten
networks numerically: exact-rational collision pairs for the five members, and a check
that the invariance lemma's conclusion really holds for them under random embedding
perturbations.

## 6. Hahn and Rofin, read for this purpose

Source: arXiv:2402.09963v4, HTML, first 100,000 characters read through a summarising
fetch on 2026-11-14 (the rest, including proofs and appendix, not read). Their Theorem 6
lower-bounds an average directional sharpness: expectation over inputs and over
perturbations on the radius-ρ sphere of the whole parameter vector, for soft-attention
encoders with layer norm, fixed layers and heads, width `d > 12L`, outputs in `[−1, 1]`,
bounded embeddings, positional encodings outside the parameter vector; the statement is
a `lim inf` in `n` followed by `ρ → 0`. They state that worst-case sharpness bounds
follow from the average ones.

Why it does not formally imply C1 or rung 6b:
- our perturbations are relative with zeros fixed, a measure-zero family of the
  directions their expectation runs over;
- our model has hard attention with ties, no layer norm, and unbounded exact position
  features (`i`, `i²`, `n`), outside their bounded-embedding setting;
- theirs is a limit statement with no radius; ours is an explicit radius at each length.

Why the level is still capped by it: the qualitative content ("a transformer computing
a sensitive function has no fixed-radius weight neighbourhood that survives long
inputs") is theirs, in greater generality for the standard architecture. A fair summary
of C1, if proved: the first machine-checked, worst-case, explicit-constant form of that
effect, for a decidable class of exactly-correct written networks, covering parity and
sort rank. Not a new phenomenon.

## Recommendation

Do C1 next (after the 6a dev pilot, or instead of it if the impossibility line has
priority): statement test on the ten networks first, then pre-register, then the
invariance lemma. Do the three Dyck per-network theorems only if a per-family table
(parity, sort, Dyck) is wanted for the write-up. Do not spend on C2 or beyond without a
new idea.
