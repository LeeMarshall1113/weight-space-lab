/-
Lane 4, rung 8, certificate checker (PREREG_R8.md, Route step 1). Mirror: tools/r8_cert.py.
The theorem to prove is `Sound8` at the end.

Against the rung-7 checker (Lane4/R7Cert.lean, whose interval pieces are reused unchanged):

* a head keeps a WINDOW of the last `L` candidate tokens (newest first), `L ≤ 3` from the
  certificate, such that keys older than the window are below `e^-16` relative to the newest key;
* inside the window the attention may be SHARED: each non-reference key gets an interval for its
  softmax weight, computed from score intervals with rational enclosures of `exp`;
* values are AFFINE FORMS over the attention weights: centre + Σ coefficient · symbol ± radius,
  one symbol per non-reference window key per head, so that the correlation between output
  coordinates survives the MLP; the ReLU uses the zonotope relaxation with a rounded slope;
* the radius `δ` of the ball is a parameter of `check8` and of `Sound8`.

No real numbers and no floats appear in `check8`: it is decidable by evaluation.
-/
import Lane4.R7All

namespace Lane4.Cert8

open Lane4.Seq (Mask cand tokAt)
open Lane4.RSoft Lane4.AGate Lane4.Cert

/-! ### outward rounding to a dyadic grid, and rational enclosures of exp -/

/-- the largest multiple of `2^-b` that is at most `x` -/
def dnB (b : ℕ) (x : ℚ) : ℚ := (((x.num * 2 ^ b) / (x.den : ℤ) : ℤ) : ℚ) / 2 ^ b

/-- a multiple of `2^-b` that is at least `x` -/
def upB (b : ℕ) (x : ℚ) : ℚ := -dnB b (-x)

/-- (Σ_{k<14} y^k / k!, y^14 / 14!) -/
def expSeries (y : ℚ) : ℚ × ℚ :=
  (List.range 14).foldl (fun p k => (p.1 + p.2, p.2 * y / ((k : ℚ) + 1))) (0, 1)

/-- `n` times: square, then round with `f` -/
def sqN (f : ℚ → ℚ) : ℕ → ℚ → ℚ
  | 0, a => a
  | n + 1, a => sqN f n (f (a * a))

/-- a lower bound of `exp x`, for `x ≤ 6` -/
def expLo (x : ℚ) : ℚ :=
  if x < -60 then 0
  else max (sqN (dnB 70) 6 (dnB 70 ((expSeries (x / 64)).1 - 3 * qabs (expSeries (x / 64)).2))) 0

/-- an upper bound of `exp x`, for `x ≤ 6` -/
def expHi (x : ℚ) : ℚ :=
  if x < -60 then 1 / 2 ^ 80
  else sqN (upB 70) 6 (upB 70 ((expSeries (x / 64)).1 + 3 * qabs (expSeries (x / 64)).2))

/-! ### affine forms -/

/-- centre, coefficients of the symbols (by index; missing ones are 0), radius -/
structure AF where
  c : ℚ
  t : List ℚ
  r : ℚ

def sumAbs : List ℚ → ℚ
  | a :: l => qabs a + sumAbs l
  | [] => 0

def AF.dev (a : AF) : ℚ := sumAbs a.t + a.r
def AF.mag (a : AF) : ℚ := qabs a.c + a.dev
def AF.small (a : AF) : Bool := decide (a.mag ≤ 15)

def addL : List ℚ → List ℚ → List ℚ
  | a :: x, b :: y => (a + b) :: addL x y
  | [], y => y
  | x, [] => x

def AF.add (a b : AF) : AF := ⟨a.c + b.c, addL a.t b.t, a.r + b.r⟩
def AF.scale (q : ℚ) (a : AF) : AF := ⟨q * a.c, a.t.map (fun v => q * v), qabs q * a.r⟩
/-- shift the centre by `c` and widen the radius by `e` -/
def AF.shift (a : AF) (c e : ℚ) : AF := ⟨a.c + c, a.t, a.r + e⟩

def linAF : List ℚ → List AF → AF
  | a :: r, x :: xs => (AF.scale a x).add (linAF r xs)
  | _, _ => ⟨0, [], 0⟩

def sumMag : List AF → ℚ
  | x :: xs => x.mag + sumMag xs
  | [] => 0

def maxMag (xs : List AF) : ℚ := xs.foldl (fun m x => max m x.mag) 0

/-- a stored-weight row applied to a vector of affine forms: the linear part is exact, the
perturbation of the weights and the rounding go to the radius -/
def dotAF (δ : ℚ) (r : List ℚ) (x : List AF) : AF :=
  (linAF r x).shift 0
    (δ * sumMag x + (r.length : ℚ) * (maxAbs r + 1) * (maxMag x + 1) / 2 ^ 16 + 1 / 2 ^ 100)

/-- rows plus stored biases, rounded -/
def affAF (δ : ℚ) (M : List (List ℚ)) (b : List ℚ) (x : List AF) : List AF :=
  List.zipWith (fun r c => (dotAF δ r x).shift c (e0 δ + rnd)) M b

/-- entry-wise rounded sum -/
def addAF (a b : List AF) : List AF := List.zipWith (fun u v => (u.add v).shift 0 rnd) a b

/-- ReLU: exact when the sign is known; otherwise slope `lam` (the chord slope rounded down to a
multiple of 2^-20), offset and radius `mu` -/
def reluAF (a : AF) : AF :=
  let lo := a.c - a.dev
  let hi := a.c + a.dev
  if 0 ≤ lo then a
  else if hi ≤ 0 then ⟨0, [], 0⟩
  else
    let lam := dnB 20 (hi / (hi - lo))
    let mu := max (-(lam * lo)) ((1 - lam) * hi) / 2
    (AF.scale lam a).shift mu mu

/-! ### heads -/

/-- what the certificate says about a head (all of it is recomputed and compared by `headOK8`,
or checked as an inequality) -/
structure HCert where
  /-- per embedding row (BOS first): is the token a candidate key -/
  cands : List Bool
  /-- window length -/
  L : ℕ
  /-- a bound on the content-score spread over candidate keys -/
  spread : ℚ
  /-- content score of query row against key row: `S[q][t]` -/
  S : List (List IV)
  /-- value of each key row: `VE[t][r]` -/
  VE : List (List IV)
  /-- per output coordinate, a bound on the value over candidate tokens -/
  Bv : List ℚ

def HCert.dense (hc : HCert) : Bool := hc.cands.all id

/-- rounding slack of a score difference for keys at ANY distance (rung 7, bias_gap) -/
def sigFar (h : AHead) : ℚ := (h.m + 2) / 32 + (h.m + 2) / 128 + 1 / 2 ^ 11

/-- rounding slack of a score difference between window keys: when every token is a candidate the
window keys are within `L + 1` positions of the query (obligation P1) -/
def sigWin (h : AHead) (hc : HCert) : ℚ := if hc.dense then 1 / 2 ^ 8 else sigFar h

/-- denominator of the softmax-arithmetic charge `B / softDen` (obligation P2) -/
def softDen : ℚ := 2 ^ 13

/-- what the slope leaves beyond the window -/
def tailRoom (δ : ℚ) (h : AHead) (hc : HCert) : ℚ :=
  (h.m - δ) * (hc.L : ℚ) - hc.spread - sigFar h

/-- total softmax weight of the keys older than the window, relative to the newest key -/
def tailB (δ : ℚ) (h : AHead) (hc : HCert) : ℚ := upB 70 (expHi (-(tailRoom δ h hc)) * (101 / 100))

def sAt (hc : HCert) (q t : ℕ) : IV := (hc.S.getD q []).getD t (0, 0)
def vAt (hc : HCert) (t r : ℕ) : IV := (hc.VE.getD t []).getD r (0, 0)

def headOK8 (δ : ℚ) (E : List (List IV)) (h : AHead) (hc : HCert) : Bool :=
  decide (h.mask ≠ Mask.all) && decide (1 ≤ h.m) && decide (h.m ≤ 1024) &&
  hc.cands.length == E.length &&
  (List.zipWith (fun x b => gateDec δ h x == some b) E hc.cands).all id &&
  decide (hc.S = E.map (fun xq => E.map (fun xt => scoreIV δ h xq xt))) &&
  decide (hc.VE = E.map (fun xt => matIV δ h.V xt)) &&
  decide (hc.Bv = valBound δ E h hc.cands) &&
  hc.Bv.all (fun B => decide (B ≤ 2 ^ 20)) &&
  (E.drop 1).all (fun xq => (List.zip E hc.cands).all (fun a => !a.2 || scoreOK δ h xq a.1)) &&
  decide (0 ≤ hc.spread) &&
  ((List.range E.length).drop 1).all (fun q =>
    (List.zip (List.range E.length) hc.cands).all (fun a =>
      (List.zip (List.range E.length) hc.cands).all (fun b =>
        !a.2 || !b.2 ||
        decide ((sAt hc q b.1).1 - (sAt hc q a.1).1 + (sAt hc q a.1).2 + (sAt hc q b.1).2
                ≤ hc.spread)))) &&
  decide (1 ≤ hc.L) && decide (hc.L ≤ 3) && decide (16 ≤ tailRoom δ h hc)

/-- nominal score of the key at window rank `rank` -/
def nomAt (h : AHead) (hc : HCert) (q : ℕ) (keys : List ℕ) (rank : ℕ) : ℚ :=
  -(h.m * (rank : ℚ)) + (sAt hc q (keys.getD rank 0)).1

/-- first index of the largest nominal score among ranks `0..n-1` -/
def argmaxNom (h : AHead) (hc : HCert) (q : ℕ) (keys : List ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    if nomAt h hc q keys (argmaxNom h hc q keys n) < nomAt h hc q keys (n + 1)
    then n + 1 else argmaxNom h hc q keys n

/-- the reference key: the newest (rank 0), or in a dense head the highest nominal score -/
def refRank (h : AHead) (hc : HCert) (q : ℕ) (keys : List ℕ) : ℕ :=
  if hc.dense then argmaxNom h hc q keys (keys.length - 1) else 0

/-- bounds (lo, hi) on `exp (score of rank − score of ref)`; `none` if the upper exponent is above 6 -/
def ratioAt (δ : ℚ) (h : AHead) (hc : HCert) (q : ℕ) (keys : List ℕ) (ref rank : ℕ) :
    Option (ℚ × ℚ) :=
  let sk := sAt hc q (keys.getD rank 0)
  let s1 := sAt hc q (keys.getD ref 0)
  let dist : ℚ := (rank : ℚ) - (ref : ℚ)
  let hiE := -(h.m * dist) + δ * qabs dist + (sk.1 - s1.1) + sk.2 + s1.2 + sigWin h hc
  let loE := -(h.m * dist) - δ * qabs dist + (sk.1 - s1.1) - sk.2 - s1.2 - sigWin h hc
  if hiE ≤ 6 then some (if hc.dense then expLo loE else 0, expHi hiE) else none

/-- the ranks other than the reference, in order -/
def otherRanks (n ref : ℕ) : List ℕ := (List.range n).filter (fun k => k != ref)

def allSome {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | none :: _ => none
  | some a :: l => (allSome l).map (fun r => a :: r)

def sumFst (l : List (ℚ × ℚ)) : ℚ := l.foldr (fun a s => a.1 + s) 0
def sumSnd (l : List (ℚ × ℚ)) : ℚ := l.foldr (fun a s => a.2 + s) 0

/-- bounds on the softmax weight of the key with ratio bounds `w`, given the sums of the lower and
upper ratio bounds of ALL non-reference window keys and the tail bound `tl` -/
def weightIV (w : ℚ × ℚ) (slo shi tl : ℚ) : ℚ × ℚ :=
  (dnB 70 (w.1 / (1 + w.1 + (shi - w.2) + tl)), upB 70 (w.2 / (1 + w.2 + (slo - w.1))))

/-- one output coordinate `r` of the head: reference value plus, per other key, its weight times the
value difference (weight = midpoint + half-width · symbol); `pre` zero coefficients come first -/
def coordAF (hc : HCert) (keys : List ℕ) (ref : ℕ) (others : List ℕ) (ws : List (ℚ × ℚ))
    (pre : ℕ) (tl sd : ℚ) (r : ℕ) : AF :=
  let vref := (vAt hc (keys.getD ref 0) r).1
  let diffs := others.map (fun k => (vAt hc (keys.getD k 0) r).1 - vref)
  let mids := List.zipWith (fun w d => (w.1 + w.2) / 2 * d) ws diffs
  let rads := List.zipWith (fun w d => (w.2 - w.1) / 2 * d) ws diffs
  ⟨vref + mids.foldr (fun a s => a + s) 0,
   List.replicate pre 0 ++ rads,
   (keys.map (fun k => (vAt hc k r).2)).foldl max 0 + 2 * tl * hc.Bv.getD r 0
     + hc.Bv.getD r 0 / sd + 1 / 2 ^ 90⟩

/-- The head's output for query token `q` and window keys `keys` (tokens, newest first; for a causal
head with a candidate query the query token comes first). `pre` symbols belong to earlier heads.
`none` if a guard fails. With no key the output is exactly 0. -/
def headAF (δ : ℚ) (h : AHead) (hc : HCert) (d : ℕ) (pre : ℕ) (q : ℕ) (keys : List ℕ) :
    Option (List AF) :=
  if keys.length = 0 then some ((List.range d).map (fun _ => ⟨0, [], 0⟩))
  else
    let ref := refRank h hc q keys
    let others := otherRanks keys.length ref
    let full : Bool := decide (hc.L + (if h.mask = Mask.causal ∧ hc.cands.getD q false = true
                                        then 1 else 0) ≤ keys.length)
    let tl : ℚ := if full then 3 * tailB δ h hc else 0
    if hc.dense = true ∧ ¬ ((sAt hc q (keys.getD 0 0)).2 + (sAt hc q (keys.getD ref 0)).2
                              + sigWin h hc + δ * (ref : ℚ) ≤ 1) then none
    else
      match allSome (others.map (fun k => ratioAt δ h hc q keys ref k)) with
      | none => none
      | some rs =>
        let ws := rs.map (fun w => weightIV w (sumFst rs) (sumSnd rs) tl)
        some ((List.range d).map (fun r => coordAF hc keys ref others ws pre tl softDen r))

/-! ### the abstract machine -/

structure Cert8 where
  heads : List HCert
  /-- closed set of abstract states: task state, and per head the window (the tokens at the last
  `L` earlier candidate positions, newest first; shorter near the start) -/
  states : List (ℕ × List (List ℕ))

/-- the keys a head uses at a query with token `t`, given its window -/
def keysAt (h : AHead) (hc : HCert) (t : ℕ) (win : List ℕ) : List ℕ :=
  if h.mask = Mask.causal ∧ hc.cands.getD t false = true then t :: win else win

/-- the window after passing a position with token `t` -/
def winNext (hc : HCert) (t : ℕ) (win : List ℕ) : List ℕ :=
  if hc.cands.getD t false = true then (t :: win).take hc.L else win

/-- residual stream after the heads: each head's output is added (rounded) to `acc`; every partial
sum must be small. `pre` counts the symbols used so far. -/
def headsAF (δ : ℚ) (d : ℕ) (t : ℕ) :
    List AHead → List HCert → List (List ℕ) → ℕ → List AF → Option (List AF)
  | h :: hs, hc :: hcs, win :: wins, pre, acc =>
    match headAF δ h hc d pre t (keysAt h hc t win) with
    | none => none
    | some ho =>
      if (addAF acc ho).all AF.small
      then headsAF δ d t hs hcs wins (pre + ((keysAt h hc t win).length - 1)) (addAF acc ho)
      else none
  | _, _, _, _, acc => some acc

/-- the network's output form for query token `t` and the windows of the heads; `none` if a guard
fails. Every rounded quantity is guarded to be at most 15. -/
def outAF (δ : ℚ) (N : ANet) (B : ABlock) (c : Cert8) (t : ℕ) (wins : List (List ℕ)) :
    Option AF :=
  let x0 : List AF := (N.embed.getD t []).map (fun a => ⟨a, [], e0 δ⟩)
  match headsAF δ x0.length t B.heads c.heads wins 0 x0 with
  | none => none
  | some y =>
    let a1 := affAF δ B.W1 B.b1 y
    if a1.all AF.small then
      let a2 := affAF δ B.W2 B.b2 (a1.map reluAF)
      if a2.all AF.small then
        let z := addAF y a2
        if z.all AF.small then
          let o := (dotAF δ N.outW z).shift N.outB (e0 δ + rnd)
          if o.small then some o else none
        else none
      else none
    else none

def caseOK8 (δ : ℚ) (N : ANet) (B : ABlock) (T : Task) (c : Cert8)
    (st : ℕ × List (List ℕ)) (t : ℕ) : Bool :=
  match outAF δ N B c t st.2 with
  | none => false
  | some o =>
    decide (qabs (o.c - (T.out st.1 t : ℚ)) + o.dev ≤ 1 / 4) &&
    c.states.contains (T.step st.1 t, List.zipWith (fun hc win => winNext hc t win) c.heads st.2)

/-- The checker. `δ` is the radius of the additive ball around the written network `N`. -/
def check8 (δ : ℚ) (N : ANet) (T : Task) (c : Cert8) : Bool :=
  match N.blocks with
  | [B] =>
    let E := N.embed.map (embIV δ)
    decide (0 ≤ δ) && decide (δ ≤ 1 / 2) &&
    N.shapeOK T.ntok && weightsOK N B && c.heads.length == B.heads.length &&
    (List.zipWith (fun h hc => headOK8 δ E h hc) B.heads c.heads).all id &&
    c.states.all (fun st => st.2.length == B.heads.length) &&
    c.states.contains
      (T.init, c.heads.map (fun hc => if hc.cands.getD 0 false = true then [0] else [])) &&
    c.states.all (fun st => (List.range T.ntok).all (fun k => caseOK8 δ N B T c st (k + 1)))
  | _ => false

/-- THE SOUNDNESS THEOREM of rung 8: if the checker accepts `N` at radius `δ`, then every network
within the additive `δ`-ball of `N`, in the rounding model, is within 1/4 of the task's target at
every position of every input of every length the rounding model covers. -/
def Sound8 : Prop :=
  ∀ (δ : ℚ) (N : ANet) (T : Task) (c : Cert8), check8 δ N T c = true →
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Rnd u η M fl → ExpM u η ex →
  0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  ∀ p : APert, p.Within (δ : ℝ) →
  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ T.ntok) →
  u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 → η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100 →
  2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M →
  ∀ i : ℕ, 1 ≤ i → i ≤ w.length →
    |N.out fl ex p w i - ((T.target w i : ℕ) : ℝ)| ≤ 1 / 4

end Lane4.Cert8
