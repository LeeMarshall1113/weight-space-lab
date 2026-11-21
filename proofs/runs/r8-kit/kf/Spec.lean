namespace Lane4.Case
open Lane4.Seq (Mask cand tokAt)
open Lane4.AGate Lane4.Cert Lane4.Cert8

/-- A set of abstract states that contains the initial one and is closed under reading a
token contains the abstract state of every input prefix. -/
def AbsClosed8 : Prop :=
  ∀ (T : Task) (heads : List HCert) (states : List (ℕ × List (List ℕ))),
  absInit8 T heads ∈ states →
  (∀ st ∈ states, ∀ t, 1 ≤ t → t ≤ T.ntok → absStep8 T heads st t ∈ states) →
  ∀ pre : List ℕ, (∀ t ∈ pre, 1 ≤ t ∧ t ≤ T.ntok) → absState8 T heads pre ∈ states

/-- The abstract state carries one window per head. -/
def AbsLen8 : Prop :=
  ∀ (T : Task) (heads : List HCert) (pre : List ℕ),
    (absState8 T heads pre).2.length = heads.length

/-- The task's target at position `i` is the automaton's output on the abstract state of the
first `i - 1` tokens and the token at `i`. -/
def AbsTarget8 : Prop :=
  ∀ (T : Task) (heads : List HCert) (w : List ℕ) (i : ℕ), 1 ≤ i → i ≤ w.length →
    T.target w i = T.out (absState8 T heads (w.take (i - 1))).1 (tokAt w i)

/-- What the window of head number `a` means at query position `i`. With `win` the window stored
in the abstract state of the first `i - 1` tokens and `keys = keysAt h hc (token at i) win`:
there is a list of positions `P`, the `P.length` latest candidate positions of the query
(`WinPos`), whose tokens are exactly `keys`; and if `keys` is shorter than a full window
(`fullLen`), then `P` holds EVERY candidate position. Positions run over `0..w.length`
(position 0 is BOS, token 0); `hc` is the certificate of head `a`. -/
def AbsKeys8 : Prop :=
  ∀ (T : Task) (heads : List HCert) (w : List ℕ) (i a : ℕ) (h : AHead) (hc : HCert),
  1 ≤ i → i ≤ w.length → a < heads.length → heads.getD a hc = hc → h.mask ≠ Mask.all →
  1 ≤ hc.L →
    ∃ P : List ℕ,
      WinPos h.mask hc.cands (tokAt w) (w.length + 1) i P
      ∧ P.map (tokAt w) = keysAt h hc (tokAt w i) ((absState8 T heads (w.take (i - 1))).2.getD a [])
      ∧ P.length ≤ fullLen h hc (tokAt w i)
      ∧ (P.length < fullLen h hc (tokAt w i) →
          ∀ k ∈ cand h.mask (w.length + 1) i, hc.cands.getD (tokAt w k) false = true → k ∈ P)

end Lane4.Case
