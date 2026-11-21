import Lane4.R8Defs
import Lane4.R8Soft

namespace Lane4.Case
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.R7K2

/-- SCORES OF CANDIDATE KEYS AGAINST THE CERTIFICATE'S TABLE (contains obligation P1).
A head that passes `headOK8`; `x j` is the state at position `j`, known to lie in row `tok j` of
`E`; the query is at position `i` with a real token. For candidate key positions `j, k ≤ i`
(positions hold candidate tokens), with `sj, sk` the table entries `sAt hc (tok i) (tok j)`,
`sAt hc (tok i) (tok k)` (centre, radius) of their content scores:

* every score is at most `(m + 2) * (n + 1) + 1025` in size;
* FAR: if `k < j`, the score of `k` minus the score of `j` is at most
  `-(m - δ) * (j - k)` plus the difference of the centres, both radii and `sigFar h`;
* NEAR (P1): if both keys are within 4 positions of the query, the score difference is the
  nominal one, `m * (k - j)` plus the difference of the centres, up to `δ * |k - j|`, both radii
  and `1 / 2^8`. -/
def ScoreWin : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl →
  ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (h : AHead) (E : List (List IV)) (hc : HCert) (dd : ℕ),
  headOK8 δ E h hc = true → h.shapeOK dd = true → dd ≤ 24 → smallM h.A = true →
  (∀ row ∈ E, row.length = dd ∧ Bdd 16 row) →
  ∀ (dA : ℕ → ℕ → ℝ) (dm : ℝ), (∀ a b, |dA a b| ≤ (δ : ℝ)) → |dm| ≤ (δ : ℝ) →
  ∀ (n : ℕ) (x : ℕ → Vec) (tok : ℕ → ℕ),
  u * (n : ℝ) ≤ 1 / 256 → η * (n : ℝ) ≤ 1 / 2 ^ 100 → 2 ^ 40 * (n : ℝ) ^ 2 ≤ M →
  (∀ j, j < n → tok j < E.length ∧ InIVs (x j) (E.getD (tok j) [])) →
  ∀ i, i < n → 1 ≤ tok i →
  ∀ j k, j ≤ i → k ≤ i →
  hc.cands.getD (tok j) false = true → hc.cands.getD (tok k) false = true →
    |h.score fl dA dm x i j| ≤ ((h.m : ℚ) : ℝ) * ((n : ℝ) + 1) + 2 * ((n : ℝ) + 1) + 1025
    ∧ (k < j →
        h.score fl dA dm x i k - h.score fl dA dm x i j
          ≤ -((((h.m - δ : ℚ)) : ℝ) * ((j : ℝ) - (k : ℝ)))
            + ((((sAt hc (tok i) (tok k)).1 - (sAt hc (tok i) (tok j)).1 : ℚ)) : ℝ)
            + ((((sAt hc (tok i) (tok k)).2 + (sAt hc (tok i) (tok j)).2 + sigFar h : ℚ)) : ℝ))
    ∧ (i ≤ k + 4 → i ≤ j + 4 →
        |h.score fl dA dm x i k - h.score fl dA dm x i j
            - (((h.m : ℚ) : ℝ) * ((k : ℝ) - (j : ℝ))
               + ((((sAt hc (tok i) (tok k)).1 - (sAt hc (tok i) (tok j)).1 : ℚ)) : ℝ))|
          ≤ ((δ : ℚ) : ℝ) * |(k : ℝ) - (j : ℝ)|
            + ((((sAt hc (tok i) (tok k)).2 + (sAt hc (tok i) (tok j)).2 + 1 / 2 ^ 8 : ℚ)) : ℝ))

end Lane4.Case

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft

/-- THE ARITHMETIC OF SOFTMAX ATTENTION WHEN ONLY THE LAST FEW KEYS MATTER (obligation P2).
The candidate positions `c` are listed in increasing order (that is the order `savg` sums in),
`p` is the last of them, and every candidate at least 3 positions before `p` has a score at
least 16 below that of `p`, falling by a further 1/2 per position. The up to three candidates
nearest to `p` are unconstrained. Then the rounded softmax average `savg` differs from the exact
one by at most `B / 2^13 + 2^-90`, however long the list is. `B` bounds the values, `Sb` the
scores. Range conditions: `2 * Sb ≤ M` and `4 * B + 4 ≤ M`. -/
def SavgArith : Prop :=
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Rnd u η M fl → ExpM u η ex →
  0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  ∀ (c : List ℕ), c.Pairwise (fun a b => a < b) → ∀ n : ℕ, c.length ≤ n →
  u * (n : ℝ) ≤ 1 / 256 → η * (n : ℝ) ≤ 1 / 2 ^ 100 →
  ∀ (s f : ℕ → ℝ) (p : ℕ), p ∈ c → (∀ k ∈ c, k ≤ p) →
  (∀ k ∈ c, k + 3 ≤ p → s k ≤ s p - 16 - ((p : ℝ) - (k : ℝ) - 3) / 2) →
  ∀ Sb : ℝ, (∀ k ∈ c, |s k| ≤ Sb) → 2 * Sb ≤ M →
  ∀ B : ℝ, (∀ k ∈ c, |f k| ≤ B) → 4 * B + 4 ≤ M →
    |savg fl ex c s f - eavg c s f| ≤ B / 2 ^ 13 + 1 / 2 ^ 90
      ∧ fl (savg fl ex c s f) = savg fl ex c s f

end Lane4.Case

namespace Lane4.Case
open Lane4.Cert Lane4.Cert8

/-- Rounding to the dyadic grid goes the right way. -/
def RoundSound : Prop :=
  ∀ (b : ℕ) (x : ℚ), dnB b x ≤ x ∧ x ≤ upB b x

/-- The rational enclosures of the exponential used by the checker are enclosures:
for every rational `x ≤ 6`, `expLo x ≤ exp x ≤ expHi x`, and `expLo x` is not negative. -/
def ExpEncl : Prop :=
  ∀ x : ℚ, x ≤ 6 →
    0 ≤ expLo x ∧ ((expLo x : ℚ) : ℝ) ≤ Real.exp ((x : ℚ) : ℝ) ∧
    Real.exp ((x : ℚ) : ℝ) ≤ ((expHi x : ℚ) : ℝ)

end Lane4.Case

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft

/-- SHARED ATTENTION OVER A WINDOW. Pure real analysis: no rounding, no floats.
`c` are the candidate positions, `jr ∈ c` the reference key, `W` a list of other candidates (the
window). For the `i`-th window key the ratio `exp (s k - s jr)` lies in `[lo i, hi i]`; the ratios
of all remaining candidates sum to at most `tl`. Then there are weights `a i`, ONE set for every
value function `f`, each inside the stated interval, non-negative and summing to at most 1, such
that the exact softmax average of `f` is the reference value plus the weighted value differences,
up to `2 * tl * B`. -/
def MixBound : Prop :=
  ∀ (c : List ℕ), c.Nodup → ∀ (s : ℕ → ℝ) (jr : ℕ), jr ∈ c →
  ∀ (W : List ℕ) (lo hi : List ℝ), W.Nodup → (∀ k ∈ W, k ∈ c ∧ k ≠ jr) →
  lo.length = W.length → hi.length = W.length →
  (∀ i, i < W.length → 0 ≤ lo.getD i 0 ∧ lo.getD i 0 ≤ Real.exp (s (W.getD i 0) - s jr) ∧
                        Real.exp (s (W.getD i 0) - s jr) ≤ hi.getD i 0) →
  ∀ tl : ℝ, 0 ≤ tl →
  ((c.filter (fun k => decide (k ≠ jr ∧ k ∉ W))).map (fun k => Real.exp (s k - s jr))).sum ≤ tl →
  ∃ a : ℕ → ℝ,
    (∀ i, i < W.length →
       lo.getD i 0 / (1 + lo.getD i 0 + (hi.sum - hi.getD i 0) + tl) ≤ a i ∧
       a i ≤ hi.getD i 0 / (1 + hi.getD i 0 + (lo.sum - lo.getD i 0))) ∧
    (∀ i, 0 ≤ a i) ∧
    ((List.range W.length).map a).sum ≤ 1 ∧
    ∀ (f : ℕ → ℝ) (B : ℝ), (∀ k ∈ c, |f k| ≤ B) →
      |eavg c s f
        - (f jr + ((List.range W.length).map (fun i => a i * (f (W.getD i 0) - f jr))).sum)|
        ≤ 2 * tl * B

end Lane4.Case

namespace Lane4.Case
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.R7K2

/-- What a form says about the number it represents. -/
def AFRange : Prop :=
  ∀ (e : ℕ → ℝ) (v : ℝ) (a : AF), Sym e → InAF e v a →
    0 ≤ a.r ∧ |v| ≤ ((a.mag : ℚ) : ℝ) ∧
    (((a.c - a.dev : ℚ)) : ℝ) ≤ v ∧ v ≤ (((a.c + a.dev : ℚ)) : ℝ)

/-- A stored embedding row, as forms without symbols. -/
def EmbAF : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (row : List ℚ) (d : ℕ → ℝ), (∀ k, |d k| ≤ (δ : ℝ)) → smallQ row = true →
  ∀ e : ℕ → ℝ,
    InAFs e (aswRow fl row d 0) (row.map (fun a => (⟨a, [], e0 δ⟩ : AF)))
    ∧ ∀ a ∈ row.map (fun a => (⟨a, [], e0 δ⟩ : AF)), a.mag ≤ 16

/-- A stored-weight dot product of a vector of forms lies in `dotAF`. -/
def DotAF : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (r : List ℚ) (x : List ℝ) (xa : List AF) (d : ℕ → ℝ), (∀ k, |d k| ≤ (δ : ℝ)) →
  r.length = x.length → r.length ≤ 32 → smallQ r = true →
  ∀ e : ℕ → ℝ, Sym e → InAFs e x xa → (∀ a ∈ xa, a.mag ≤ 16) →
    InAF e (ardot fl r x d 0 0) (dotAF δ r xa)

/-- A stored affine map lies in `affAF`, when every output passes the magnitude guard. -/
def AffAF : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (A : List (List ℚ)) (b : List ℚ) (x : List ℝ) (xa : List AF) (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ),
  (∀ i k, |dW i k| ≤ (δ : ℝ)) → (∀ i, |db i| ≤ (δ : ℝ)) →
  (∀ r ∈ A, r.length = x.length) → x.length ≤ 32 → A.length = b.length →
  smallM A = true → smallQ b = true →
  ∀ e : ℕ → ℝ, Sym e → InAFs e x xa → (∀ a ∈ xa, a.mag ≤ 16) →
  (affAF δ A b xa).all AF.small = true →
    InAFs e (araffine fl A b x dW db 0) (affAF δ A b xa)

/-- A rounded entrywise sum lies in `addAF`, when every output passes the magnitude guard. -/
def AddAF : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl →
  ∀ (x y : List ℝ) (a b : List AF) (e : ℕ → ℝ), Sym e → InAFs e x a → InAFs e y b →
  (addAF a b).all AF.small = true →
    InAFs e (radd fl x y) (addAF a b)

/-- ReLU maps a form into `reluAF` of it, and small forms to small forms. -/
def ReluAF : Prop :=
  ∀ (x : List ℝ) (xa : List AF) (e : ℕ → ℝ), Sym e → InAFs e x xa →
  xa.all AF.small = true →
    InAFs e (x.map Lane4.relu) (xa.map reluAF) ∧ (xa.map reluAF).all AF.small = true

/-- Shifting the centre: if `v` is in `a` then a number within `r` of `v + c` is in `a.shift c r`. -/
def ShiftAF : Prop :=
  ∀ (e : ℕ → ℝ) (v v' : ℝ) (a : AF) (c r : ℚ), InAF e v a →
    |v' - (v + ((c : ℚ) : ℝ))| ≤ ((r : ℚ) : ℝ) → InAF e v' (a.shift c r)

end Lane4.Case

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
    ∃ P : List ℕ,
      WinPos h.mask hc.cands (tokAt w) (w.length + 1) i P
      ∧ P.map (tokAt w) = keysAt h hc (tokAt w i) ((absState8 T heads (w.take (i - 1))).2.getD a [])
      ∧ P.length ≤ fullLen h hc (tokAt w i)
      ∧ (P.length < fullLen h hc (tokAt w i) →
          ∀ k ∈ cand h.mask (w.length + 1) i, hc.cands.getD (tokAt w k) false = true → k ∈ P)

end Lane4.Case

namespace Lane4.Case
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.R7K2

/-- THE HEAD LEMMA OF RUNG 8. A head that passes `headOK8`, under an additive perturbation of at
most `δ`, in the rounding model. `x j` is the state at position `j` (the block's input), known to
lie in row `tok j` of `E`; `n` is the number of positions; the query at position `i` has a real
token. `P` lists the latest candidate positions of the query, newest first (`WinPos`), and holds
every candidate position unless it is as long as a full window. If `headAF` returns forms `o` for
the tokens at `P`, then there are symbol values `e'` in `[-1, 1]` (one per non-reference key) such
that, under EVERY symbol assignment `e` that agrees with `e'` on this head's symbols (numbers
`pre, pre + 1, ...`), the head's output vector is represented by `o`, entry by entry. -/
def HeadSound8 : Prop :=
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Ctx u η M fl → ExpM u η ex →
  ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (h : AHead) (E : List (List IV)) (hc : HCert) (dd : ℕ),
  headOK8 δ E h hc = true → h.shapeOK dd = true → dd ≤ 24 →
  smallM h.A = true → smallM h.V = true → smallQ h.g = true → smallQ [h.gb] = true →
  (∀ row ∈ E, row.length = dd ∧ Bdd 16 row) →
  ∀ (dA dV : ℕ → ℕ → ℝ) (dm : ℝ) (dg : ℕ → ℝ) (dgb : ℝ),
  (∀ a b, |dA a b| ≤ (δ : ℝ)) → (∀ a b, |dV a b| ≤ (δ : ℝ)) → |dm| ≤ (δ : ℝ) →
  (∀ k, |dg k| ≤ (δ : ℝ)) → |dgb| ≤ (δ : ℝ) →
  ∀ (n : ℕ) (x : ℕ → Vec) (tok : ℕ → ℕ),
  u * (n : ℝ) ≤ 1 / 256 → η * (n : ℝ) ≤ 1 / 2 ^ 100 → 2 ^ 40 * (n : ℝ) ^ 2 ≤ M →
  (∀ j, j < n → tok j < E.length ∧ InIVs (x j) (E.getD (tok j) [])) →
  ∀ i, i < n → 1 ≤ tok i →
  ∀ (P : List ℕ) (pre : ℕ), WinPos h.mask hc.cands tok n i P →
  P.length ≤ fullLen h hc (tok i) →
  (P.length < fullLen h hc (tok i) →
     ∀ k ∈ cand h.mask n i, hc.cands.getD (tok k) false = true → k ∈ P) →
  ∀ o : List AF, headAF δ h hc dd pre (tok i) (P.map tok) = some o →
    ∃ e' : ℕ → ℝ, (∀ k, |e' k| ≤ 1) ∧
      ∀ e : ℕ → ℝ, (∀ k, k < P.length - 1 → e (pre + k) = e' k) →
        InAFs e (h.attn fl ex dA dV dm dg dgb n x i) o

end Lane4.Case

