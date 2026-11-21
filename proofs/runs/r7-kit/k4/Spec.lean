namespace Lane4.Case
open Lane4.Seq (Mask cand tokAt)
open Lane4.AGate Lane4.Cert

/-- A set of abstract states that contains the initial one and is closed under reading a
token contains the abstract state of every input prefix. -/
def AbsClosed : Prop :=
  ∀ (T : Task) (cands : List (List Bool)) (states : List (ℕ × List (Option ℕ))),
  absInit T cands ∈ states →
  (∀ st ∈ states, ∀ t, 1 ≤ t → t ≤ T.ntok → absStep T cands st t ∈ states) →
  ∀ pre : List ℕ, (∀ t ∈ pre, 1 ≤ t ∧ t ≤ T.ntok) → absState T cands pre ∈ states

/-- The abstract state carries one pick per head. -/
def AbsLen : Prop :=
  ∀ (T : Task) (cands : List (List Bool)) (pre : List ℕ),
    (absState T cands pre).2.length = cands.length

/-- The task's target at position `i` is the automaton's output on the abstract state of the
first `i - 1` tokens and the token at `i`. -/
def AbsTarget : Prop :=
  ∀ (T : Task) (cands : List (List Bool)) (w : List ℕ) (i : ℕ), 1 ≤ i → i ≤ w.length →
    T.target w i = T.out (absState T cands (w.take (i - 1))).1 (tokAt w i)

/-- What the pick of head number `a` means at query position `i`: with `p` the pick stored
in the abstract state of the first `i - 1` tokens and `q = pickAt h cd (token at i) p`:
if `q` is `none`, no position the mask allows holds a candidate token; if `q` is `some t`,
the latest candidate position exists and holds token `t`. Positions run over `0..w.length`
(position 0 is BOS, token 0), `cd` is the candidate set of head `a`. -/
def AbsPick : Prop :=
  ∀ (T : Task) (cands : List (List Bool)) (w : List ℕ) (i a : ℕ) (h : AHead),
  1 ≤ i → i ≤ w.length → a < cands.length → h.mask ≠ Mask.all →
    (pickAt h (cands.getD a []) (tokAt w i)
        ((absState T cands (w.take (i - 1))).2.getD a none) = none →
      ∀ j ∈ cand h.mask (w.length + 1) i, (cands.getD a []).getD (tokAt w j) false = false)
    ∧ (∀ t, pickAt h (cands.getD a []) (tokAt w i)
        ((absState T cands (w.take (i - 1))).2.getD a none) = some t →
      ∃ j, Latest h.mask (cands.getD a []) (tokAt w) (w.length + 1) i j ∧ tokAt w j = t)

end Lane4.Case
