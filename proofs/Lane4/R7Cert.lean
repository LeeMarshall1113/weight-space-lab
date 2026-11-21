/-
Lane 4, rung 7, certificate checker (PREREG_R7.md Amendment 2, with the magnitude guards of
Amendment 3, 2026-11-20: `small`, `weightsOK`, `scoreOK`, `headsOK`, `outOK`, and the guards inside
`gateDec` and `headOK`). The theorem to prove is `Sound` at the end. Mirror: tools/r7_cert.py.
The Amendment 2 text of this file is kept as scratch/R7Cert_a2.lean.

The evaluator pushes intervals (centre, radius) over ℚ through the one-block gated architecture of
AGate.lean, using the error terms of the kit (asw_near, ardot_near_w, pdot_near, bias_gap, and the
softmax lemma at score gap 12 per position), and checks a closed set of abstract cases against the
task's automaton. No real numbers and no floats appear in `check`: it is decidable by evaluation.
-/
import Lane4.AGateAll

namespace Lane4.Cert

open Lane4.Seq (Mask cand tokAt)
open Lane4.RSoft Lane4.AGate

/-- A task over tokens `1..ntok`, as an automaton: the target at position `i` is `out` of the state
reached on the first `i - 1` tokens and the token at `i`. -/
structure Task where
  ntok : ℕ
  init : ℕ
  step : ℕ → ℕ → ℕ
  out : ℕ → ℕ → ℕ

def Task.target (T : Task) (w : List ℕ) (i : ℕ) : ℕ :=
  T.out ((w.take (i - 1)).foldl T.step T.init) (w.getD (i - 1) 0)

/-- centre and radius -/
abbrev IV := ℚ × ℚ

def qabs (a : ℚ) : ℚ := if a < 0 then -a else a
def maxAbs (l : List ℚ) : ℚ := l.foldl (fun m a => max m (qabs a)) 0
/-- one rounding of a quantity of size at most 16 -/
def rnd : ℚ := 1 / 2 ^ 20
/-- a stored weight against its written value -/
def e0 (δ : ℚ) : ℚ := δ + rnd

def dotC : List ℚ → List IV → ℚ
  | a :: r, x :: xs => a * x.1 + dotC r xs
  | _, _ => 0

def wErrQ (δ : ℚ) : List ℚ → List IV → ℚ
  | a :: r, x :: xs => qabs a * x.2 + δ * (qabs x.1 + x.2) + wErrQ δ r xs
  | _, _ => 0

/-- a stored-weight row applied to an interval vector (ardot_near_w) -/
def dotIV (δ : ℚ) (r : List ℚ) (x : List IV) : IV :=
  (dotC r x,
   wErrQ δ r x + (r.length : ℚ) * (maxAbs r + 1) *
     (maxAbs (x.map Prod.fst) + maxAbs (x.map Prod.snd) + 1) / 2 ^ 16 + 1 / 2 ^ 100)

def matIV (δ : ℚ) (M : List (List ℚ)) (x : List IV) : List IV := M.map (fun r => dotIV δ r x)

/-- rows plus stored biases, rounded (araffine) -/
def affIV (δ : ℚ) (M : List (List ℚ)) (b : List ℚ) (x : List IV) : List IV :=
  List.zipWith (fun r c => ((dotIV δ r x).1 + c, (dotIV δ r x).2 + e0 δ + rnd)) M b

def addIV (a b : List IV) : List IV :=
  List.zipWith (fun u v => (u.1 + v.1, u.2 + v.2 + rnd)) a b

def reluIV (v : IV) : IV :=
  ((max (v.1 - v.2) 0 + max (v.1 + v.2) 0) / 2, (max (v.1 + v.2) 0 - max (v.1 - v.2) 0) / 2)

def embIV (δ : ℚ) (row : List ℚ) : List IV := row.map (fun a => (a, e0 δ))

/-- Magnitude guard: the quantity is at most 15 in absolute value, so that one rounding of it costs
at most `rnd` (15 / 2^24 + 2^-149 ≤ 2^-20). Every rounded quantity in the evaluator is guarded. -/
def small (v : IV) : Bool := decide (qabs v.1 + v.2 ≤ 15)
def smallQ (l : List ℚ) : Bool := decide (maxAbs l ≤ 15)
def smallM (M : List (List ℚ)) : Bool := M.all smallQ

/-- every written weight is at most 15 in absolute value -/
def weightsOK (N : ANet) (B : ABlock) : Bool :=
  smallM N.embed && smallQ N.outW && smallQ [N.outB] &&
  smallM B.W1 && smallQ B.b1 && smallM B.W2 && smallQ B.b2 &&
  B.heads.all (fun h => smallM h.A && smallM h.V && smallQ h.g && smallQ [h.gb])

/-- the gate of a token row: `some true` candidate, `some false` not, `none` undecided -/
def gateDec (δ : ℚ) (h : AHead) (x : List IV) : Option Bool :=
  let c := (dotIV δ h.g x).1 + h.gb
  let e := (dotIV δ h.g x).2 + e0 δ + rnd
  if qabs c + e ≤ 15 then
    (if c + e < 0 then some true else if 0 < c - e then some false else none)
  else none

/-- content score of a query row against a key row (pdot_near with uniform bounds) -/
def scoreIV (δ : ℚ) (h : AHead) (xq xt : List IV) : IV :=
  let y := matIV δ h.A xt
  let X := maxAbs (xq.map Prod.fst)
  let e1 := maxAbs (xq.map Prod.snd)
  let Y := maxAbs (y.map Prod.fst)
  let e2 := maxAbs (y.map Prod.snd)
  let n : ℚ := xq.length
  (dotC (xq.map Prod.fst) y,
   n * (e1 * (Y + e2) + X * e2) + n * (X + e1 + 1) * (Y + e2 + 1) / 2 ^ 16 + 1 / 2 ^ 100)

/-- range guards for a content score (the hypotheses of pdot_near, and a bound of 1024 on the score
so that rounding the sum of position bias and content score is covered by `slopeRoom`) -/
def scoreOK (δ : ℚ) (h : AHead) (xq xt : List IV) : Bool :=
  let y := matIV δ h.A xt
  decide ((maxAbs (xq.map Prod.fst) + maxAbs (xq.map Prod.snd) + 1) *
          (maxAbs (y.map Prod.fst) + maxAbs (y.map Prod.snd) + 1) ≤ 2 ^ 20) &&
  decide (qabs (scoreIV δ h xq xt).1 + (scoreIV δ h xq xt).2 ≤ 1024)

/-- score gap per position that the softmax lemma needs -/
def gap : ℚ := 12

/-- what is left of the slope after the gap and the rounding of the position bias (bias_gap) -/
def slopeRoom (δ : ℚ) (h : AHead) : ℚ := h.m - δ - gap - 3 * (h.m + 2) / 64

structure Cert where
  /-- per head, per embedding row (BOS first): is the token a candidate key -/
  cands : List (List Bool)
  /-- closed set of abstract states: task state, and per head the token at the latest earlier
  candidate position (`none` if there is none) -/
  states : List (ℕ × List (Option ℕ))

/-- per output coordinate, a bound on the head's value over all candidate tokens -/
def valBound (δ : ℚ) (E : List (List IV)) (h : AHead) (cd : List Bool) : List ℚ :=
  h.V.map (fun r => ((List.zip E cd).filter (fun a => a.2)).foldl
    (fun m a => max m (qabs (dotIV δ r a.1).1 + (dotIV δ r a.1).2)) 0)

/-- gates decided as the certificate says, mask supported, slope in range, and every pair of
candidate tokens within `slopeRoom` in content score for every query token -/
def headOK (δ : ℚ) (E : List (List IV)) (h : AHead) (cd : List Bool) : Bool :=
  decide (h.mask ≠ Mask.all) && decide (1 ≤ h.m) && decide (h.m ≤ 1024) &&
  cd.length == E.length &&
  (List.zipWith (fun x b => gateDec δ h x == some b) E cd).all id &&
  (valBound δ E h cd).all (fun B => decide (B ≤ 2 ^ 20)) &&
  (E.drop 1).all (fun xq => (List.zip E cd).all (fun a => !a.2 || scoreOK δ h xq a.1)) &&
  (E.drop 1).all (fun xq =>
    (List.zip E cd).all (fun a => (List.zip E cd).all (fun b =>
      !a.2 || !b.2 ||
      decide ((scoreIV δ h xq b.1).1 - (scoreIV δ h xq a.1).1 +
              (scoreIV δ h xq a.1).2 + (scoreIV δ h xq b.1).2 ≤ slopeRoom δ h))))

/-- the head's output when its pick is the token `t` (softmax lemma at gap 12), or exactly 0 with
no candidate -/
def headOut (δ : ℚ) (E : List (List IV)) (h : AHead) (cd : List Bool) : Option ℕ → List IV
  | none => h.V.map (fun _ => (0, 0))
  | some t =>
    List.zipWith (fun v B => (v.1, v.2 + B / 100 + 1 / 2 ^ 90))
      (matIV δ h.V (E.getD t [])) (valBound δ E h cd)

def headsOut (δ : ℚ) (E : List (List IV)) :
    List AHead → List (List Bool) → List (Option ℕ) → List IV → List IV
  | h :: hs, cd :: cds, p :: ps, acc => headsOut δ E hs cds ps (addIV acc (headOut δ E h cd p))
  | _, _, _, acc => acc

/-- the network's output interval for query token `t` and the picks of the heads -/
def outIV (δ : ℚ) (N : ANet) (B : ABlock) (E : List (List IV)) (cds : List (List Bool))
    (t : ℕ) (sel : List (Option ℕ)) : IV :=
  let y := headsOut δ E B.heads cds sel (E.getD t [])
  let z := addIV y (affIV δ B.W2 B.b2 ((affIV δ B.W1 B.b1 y).map reluIV))
  ((dotIV δ N.outW z).1 + N.outB, (dotIV δ N.outW z).2 + e0 δ + rnd)

/-- every partial sum of the residual stream over the heads is small -/
def headsOK (δ : ℚ) (E : List (List IV)) :
    List AHead → List (List Bool) → List (Option ℕ) → List IV → Bool
  | h :: hs, cd :: cds, p :: ps, acc =>
    (addIV acc (headOut δ E h cd p)).all small &&
    headsOK δ E hs cds ps (addIV acc (headOut δ E h cd p))
  | _, _, _, _ => true

/-- magnitude guards along `outIV`: every rounded quantity is small -/
def outOK (δ : ℚ) (N : ANet) (B : ABlock) (E : List (List IV)) (cds : List (List Bool))
    (t : ℕ) (sel : List (Option ℕ)) : Bool :=
  let y := headsOut δ E B.heads cds sel (E.getD t [])
  let a1 := affIV δ B.W1 B.b1 y
  let a2 := affIV δ B.W2 B.b2 (a1.map reluIV)
  headsOK δ E B.heads cds sel (E.getD t []) && a1.all small && a2.all small &&
  (addIV y a2).all small && small (outIV δ N B E cds t sel)

/-- the pick a head uses at a query with token `t`, given its latest earlier candidate -/
def pickAt (h : AHead) (cd : List Bool) (t : ℕ) (p : Option ℕ) : Option ℕ :=
  if h.mask = Mask.causal ∧ cd.getD t false = true then some t else p

/-- the latest earlier candidate after passing a position with token `t` -/
def pickNext (cd : List Bool) (t : ℕ) (p : Option ℕ) : Option ℕ :=
  if cd.getD t false = true then some t else p

def caseOK (δ : ℚ) (N : ANet) (B : ABlock) (T : Task) (c : Cert) (E : List (List IV))
    (st : ℕ × List (Option ℕ)) (t : ℕ) : Bool :=
  let sel := List.zipWith (fun hc p => pickAt hc.1 hc.2 t p) (List.zip B.heads c.cands) st.2
  let o := outIV δ N B E c.cands t sel
  outOK δ N B E c.cands t sel &&
  decide (qabs (o.1 - (T.out st.1 t : ℚ)) + o.2 ≤ 1 / 4) &&
  c.states.contains (T.step st.1 t, List.zipWith (fun cd p => pickNext cd t p) c.cands st.2)

/-- The checker. `δ` is the radius of the additive ball around the written network `N`. -/
def check (δ : ℚ) (N : ANet) (T : Task) (c : Cert) : Bool :=
  match N.blocks with
  | [B] =>
    let E := N.embed.map (embIV δ)
    N.shapeOK T.ntok && weightsOK N B && c.cands.length == B.heads.length &&
    (List.zipWith (fun h cd => headOK δ E h cd) B.heads c.cands).all id &&
    c.states.all (fun st => st.2.length == B.heads.length) &&
    c.states.contains
      (T.init, c.cands.map (fun cd => if cd.getD 0 false = true then some 0 else none)) &&
    c.states.all (fun st => (List.range T.ntok).all (fun k => caseOK δ N B T c E st (k + 1)))
  | _ => false

/-- THE SOUNDNESS THEOREM (one statement, all networks, all tasks given as automata):
if the checker accepts `N` at radius 1/1000, then every network within the additive 1/1000 ball
of `N`, in the rounding model, is within 1/4 of the task's target at every position of every
input of every length the rounding model covers. Same shape as the rung-6a `Statement`. -/
def Sound : Prop :=
  ∀ (N : ANet) (T : Task) (c : Cert), check (1 / 1000) N T c = true →
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Rnd u η M fl → ExpM u η ex →
  0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  ∀ p : APert, p.Within (1 / 1000) →
  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ T.ntok) →
  u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 → η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100 →
  2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M →
  ∀ i : ℕ, 1 ≤ i → i ≤ w.length →
    |N.out fl ex p w i - ((T.target w i : ℕ) : ℝ)| ≤ 1 / 4

end Lane4.Cert
