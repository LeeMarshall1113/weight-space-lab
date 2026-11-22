/-
Lane 4, rung 9-LN15 (PREREG_R9LN15.md): certificate checker for the network of Lane4/LNNet.lean.
Mirror: tools/r9ln15_cert.py. The theorem to prove is `SoundLN` at the end.

Against the rung-8 checker (Lane4/R8Cert.lean):

* LN1 is applied to each token's embedding row as affine forms (one symbol per embedding entry);
  the result is a BOX per token, and the heads read boxes as in rung 8, with one change: the score
  and value tables charge rounding RELATIVE to the magnitudes, entry by entry (`headOKLN`,
  `scoreRel`, `dotRel`). Rung 8's `headOK8` on these boxes is too loose (its score error uses the
  largest radius of the query box). Gates, windows, tails and `headAF` are rung 8's, unchanged;
* after the heads everything is in INTEGERS scaled by 2^56 (`FF`): centre, one coefficient per
  symbol slot, radius, with floor division for centres and coefficients (each floor costs one
  unit of radius) and ceiling division for radii. Slots, for state width `d`, `nh` heads and
  `H` hidden units:
      [ embedding (d) | attention (3 per head) | head output (d per head) | LN2 (d) | W1 (H) | W2 (d) ]
  The whole radius of a head-output coordinate becomes that coordinate's own symbol; the ball on
  a weight row and its bias becomes the row's own symbol (LN2, W1, W2) or goes to the radius
  (LN1, LNf, read-out). A symbol slot is only ever SET in a form whose coefficients are checked
  to be zero there, and the forms that stay in use are checked to be free of the new slots
  (`zeroFrom`, `zeroRange`): freshness of a symbol is a run-time guard, not a proof obligation;
* LayerNorm on forms (`lnF`): centring is linear; the variance is linearised around the centres
  with the squares of the deviations as remainder; `1/sqrt` is linearised around the centre
  variance with a second-order remainder; the product of two forms keeps both linear parts and
  charges the product of the deviations. Integer square roots are found by Newton steps and
  VERIFIED by the checker (`sqrtOK`), so nothing about Newton's method has to be proved.

A rounding of a quantity of magnitude `m` (in units) is charged `chg m = m / 2^22 + 1`.
No real numbers and no floats appear in `checkLN`: it is decidable by evaluation.
-/
import Lane4.LNNet

namespace Lane4.LNC

open Lane4.Seq (Mask cand tokAt)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN

/-! ### integers scaled by 2^56 -/

def SC : ℤ := 2 ^ 56
/-- the unit as a rational -/
def SCq : ℚ := 2 ^ 56
def cdiv (a b : ℤ) : ℤ := -((-a) / b)
def chg (m : ℤ) : ℤ := m / 2 ^ 22 + 1
def iabs (a : ℤ) : ℤ := (Int.natAbs a : ℤ)
/-- `q * 2^56` rounded down -/
def floorQ (q : ℚ) : ℤ := q.num * SC / (q.den : ℤ)
def ceilQ (q : ℚ) : ℤ := -floorQ (-q)
/-- `q * 2^56` is an integer -/
def gridOK (q : ℚ) : Bool := decide (SC % (q.den : ℤ) = 0)
def gridL (l : List ℚ) : Bool := l.all gridOK
def gridM (M : List (List ℚ)) : Bool := M.all gridL

/-- centre, one coefficient per symbol slot, radius; all in units of 2^-56 -/
structure FF where
  c : ℤ
  t : List ℤ
  r : ℤ

def linI (t : List ℤ) : ℤ := t.foldl (fun s v => s + iabs v) 0
def FF.dev (a : FF) : ℤ := linI a.t + a.r
def FF.mag (a : FF) : ℤ := iabs a.c + a.dev
def FF.add (a b : FF) : FF := ⟨a.c + b.c, List.zipWith (fun x y => x + y) a.t b.t, a.r + b.r⟩
def FF.sub (a b : FF) : FF := ⟨a.c - b.c, List.zipWith (fun x y => x - y) a.t b.t, a.r + b.r⟩
/-- widen the radius -/
def FF.wide (a : FF) (e : ℤ) : FF := ⟨a.c, a.t, a.r + e⟩
def zeroF (ns : ℕ) : FF := ⟨0, List.replicate ns 0, 0⟩
def FF.small (a : FF) : Bool := decide (a.mag ≤ 15 * SC)

def addAt : List ℤ → ℕ → ℤ → List ℤ
  | a :: l, 0, v => (a + v) :: l
  | a :: l, k + 1, v => a :: addAt l k v
  | [], _, _ => []

/-- add `v ≥ 0` to the coefficient of a symbol slot, or to the radius -/
def FF.bump (a : FF) (slot : Option ℕ) (v : ℤ) : FF :=
  match slot with
  | none => ⟨a.c, a.t, a.r + v⟩
  | some k => ⟨a.c, addAt a.t k v, a.r⟩

/-- every coefficient from slot `m` on is zero -/
def zeroFrom (m : ℕ) (a : FF) : Bool := (a.t.drop m).all (fun v => v == 0)

/-- every coefficient in the slots `lo, ..., hi - 1` is zero -/
def zeroRange (lo hi : ℕ) (a : FF) : Bool := ((a.t.drop lo).take (hi - lo)).all (fun v => v == 0)

/-- the form is free of the symbols from `slot0` on (nothing to check when there is no slot) -/
def freeOpt (slot0 : Option ℕ) (a : FF) : Bool :=
  match slot0 with
  | none => true
  | some s => zeroFrom s a

/-- the forms, if every guard holds -/
def splitOK (l : List (Bool × FF)) : Option (List FF) :=
  if l.all (fun p => p.1) then some (l.map (fun p => p.2)) else none

def splitOK1 (p : Bool × FF) : Option FF := if p.1 then some p.2 else none

/-- Σ w · centre -/
def lcC : List ℤ → List FF → ℤ
  | w :: ws, x :: xs => w * x.c + lcC ws xs
  | _, _ => 0

/-- Σ w · coefficients, slot by slot -/
def lcT (ns : ℕ) : List ℤ → List FF → List ℤ
  | w :: ws, x :: xs => List.zipWith (fun a b => w * a + b) x.t (lcT ns ws xs)
  | _, _ => List.replicate ns 0

def sumWR : List ℤ → List FF → ℤ
  | w :: ws, x :: xs => iabs w * x.r + sumWR ws xs
  | _, _ => 0

/-- Σ (|w| + δ) · magnitude -/
def sumWM (dI : ℤ) : List ℤ → List ℤ → ℤ
  | w :: ws, m :: ms => (iabs w + dI) * m + sumWM dI ws ms
  | _, _ => 0

def sumI (l : List ℤ) : ℤ := l.foldl (fun s v => s + v) 0

/-! ### integer square roots: found by Newton steps, verified by the checker -/

def newtonSqrt (n : ℤ) : ℕ → ℤ → ℤ
  | 0, x => x
  | k + 1, x => if (x + n / x) / 2 < x then newtonSqrt n k ((x + n / x) / 2) else x

def isqrtI (n : ℤ) : ℤ := newtonSqrt n 200 (2 ^ 64)

/-- `a` is the integer square root of `n` -/
def sqrtOK (n a : ℤ) : Bool := decide (0 ≤ a) && decide (a * a ≤ n) && decide (n < (a + 1) * (a + 1))

/-! ### LayerNorm on forms -/

/-- LayerNorm epsilon 10^-5, rounded down to the grid (one unit of radius pays for the rounding) -/
def EPSI : ℤ := SC / 100000

/-- One output coordinate: centred form `c` times the reciprocal standard deviation `rinv` (whose
deviation is `dr`), rounded; times the stored gain; plus the stored bias. The Boolean is the
magnitude guard on the normalised value and on the output, and the guard that the form is free of
the gain/bias symbols (slots from `slot0` on) before its own symbol `slot` is set. -/
def lnOne (dI : ℤ) (rinv : FF) (dr : ℤ) (ns : ℕ) (slot0 slot : Option ℕ) (c : FF) (g b : ℤ) : Bool × FF :=
  let o0 : FF := ⟨c.c * rinv.c / SC,
                  List.zipWith (fun x y => (rinv.c * x + c.c * y) / SC) c.t rinv.t,
                  cdiv (rinv.c * c.r + iabs c.c * rinv.r + c.dev * dr) SC + ((ns : ℤ) + 1)⟩
  let o := o0.wide (chg o0.mag)
  let o2b : FF := ⟨g * o.c / SC, o.t.map (fun x => g * x / SC),
                   cdiv (iabs g * o.r) SC + ((ns : ℤ) + 1) + cdiv (dI * o.dev) SC⟩
  let o2 := o2b.bump slot (cdiv (dI * (iabs o.c + SC)) SC)
  let o3 := o2.wide (chg o2.mag + chg (iabs b + dI))
  let o4 : FF := ⟨o3.c + b, o3.t, o3.r⟩
  (o.small && freeOpt slot0 o2b && (o4.wide (chg o4.mag)).small, o4.wide (chg o4.mag))

def lnOuts (dI : ℤ) (rinv : FF) (dr : ℤ) (ns : ℕ) (slot0 : Option ℕ) :
    List FF → List ℤ → List ℤ → ℕ → List (Bool × FF)
  | c :: cs, g :: gs, b :: bs, k =>
    lnOne dI rinv dr ns slot0 (slot0.map (fun s => s + k)) c g b :: lnOuts dI rinv dr ns slot0 cs gs bs (k + 1)
  | _, _, _, _ => []

/-- the variance form of the centred forms `cs` (before its own rounding charge) -/
def varF (ns : ℕ) (n : ℤ) (cs : List FF) : FF :=
  ⟨sumI (cs.map (fun c => c.c * c.c)) / (n * SC) + EPSI,
   (lcT ns (cs.map (fun c => 2 * c.c)) cs).map (fun x => x / (n * SC)),
   cdiv (sumI (cs.map (fun c => 2 * iabs c.c * c.r + c.dev * c.dev))) (n * SC) + ((ns : ℤ) + 3)⟩

/-- the reciprocal standard deviation as a form, from the variance form `v`, the integer square
roots `a` of `v.c * SC` and `b` of `(v.c - v.dev) * SC`; `none` if a guard fails -/
def rinvF (ns : ℕ) (v : FF) (a b : ℤ) : Option FF :=
  let dv := v.dev
  let glo := SC * SC / (a + 1)
  let ghi := cdiv (SC * SC) a
  let g0 := (glo + ghi) / 2
  let eg := ghi - glo + 1 + chg (cdiv (SC * SC) b)
  if 8 * eg ≤ g0 then
    let k1 := g0 ^ 3 / (2 * SC * SC) + 1
    some ⟨g0, v.t.map (fun t => (-k1 * t) / SC),
          cdiv (k1 * v.r) SC + eg + cdiv (4 * k1 * eg * dv) (g0 * SC) + cdiv dv SC
            + cdiv (3 * dv * dv * SC ^ 4) (8 * b ^ 5) + ((ns : ℤ) + 2)⟩
  else none

/-- the rounded mean of the forms `xs` -/
def meanF (ns : ℕ) (xs : List FF) : FF :=
  let n : ℤ := (xs.length : ℤ)
  let s := xs.foldl FF.add (zeroF ns)
  ⟨s.c / n, s.t.map (fun x => x / n),
   cdiv s.r n + ((ns : ℤ) + 1) + n * chg (xs.foldl (fun m x => max m x.mag) 0)⟩

/-- the forms `xs` minus the form `mean`, rounded -/
def centF (mean : FF) (xs : List FF) : List FF :=
  let mm := mean.mag
  xs.map (fun x => (x.sub mean).wide (chg (x.mag + mm)))

/-- the rounded variance (plus epsilon) of the centred forms `cs` -/
def varW (ns : ℕ) (cs : List FF) : FF :=
  let n : ℤ := (cs.length : ℤ)
  let v0 := varF ns n cs
  v0.wide ((n + 3) * chg v0.mag)

/-- LayerNorm of the forms `xs` with stored gains `g` and biases `b` (integers); the ball on gain
and bias of coordinate `k` goes to slot `slot0 + k`, or to the radius. `none` if a guard fails. -/
def lnF (dI : ℤ) (ns : ℕ) (g b : List ℤ) (slot0 : Option ℕ) (xs : List FF) : Option (List FF) :=
  let cs := centF (meanF ns xs) xs
  let v := varW ns cs
  let vmin := v.c - v.dev
  let a := isqrtI (v.c * SC)
  let b_ := isqrtI (vmin * SC)
  if 0 < vmin ∧ sqrtOK (v.c * SC) a = true ∧ sqrtOK (vmin * SC) b_ = true ∧ 1 ≤ b_ then
    match rinvF ns v a b_ with
    | none => none
    | some rinv => splitOK (lnOuts dI rinv rinv.dev ns slot0 cs g b 0)
  else none

/-! ### stored rows, ReLU -/

/-- stored row `w` (integers) applied to the forms `xs`, plus the stored bias `b`; `ms` are the
magnitudes of `xs`, `sd` the sum of their deviations, `sc` the sum of their absolute centres.
The ball on the row and the bias: one symbol (slot) or the radius. The Boolean is the guard that
the form is free of the symbols from `slot0` on before its own symbol is set, and the magnitude
guard on the output. -/
def dotF (dI : ℤ) (ns : ℕ) (slot0 slot : Option ℕ) (w : List ℤ) (xs : List FF) (ms : List ℤ) (sd sc : ℤ)
    (b : ℤ) : Bool × FF :=
  let o0 : FF := ⟨lcC w xs / SC, (lcT ns w xs).map (fun x => x / SC), cdiv (sumWR w xs) SC + ((ns : ℤ) + 1)⟩
  let o1 := o0.wide (cdiv (dI * sd) SC
              + cdiv (((w.length : ℤ) + 2) * 2 * sumWM dI w ms) (SC * 2 ^ 22) + 1 + chg (iabs b + dI))
  let o2 : FF := (⟨o1.c + b, o1.t, o1.r⟩ : FF).bump slot (cdiv (dI * (sc + SC)) SC)
  (freeOpt slot0 o1 && (o2.wide (chg o2.mag)).small, o2.wide (chg o2.mag))

def dotRows (dI : ℤ) (ns : ℕ) (slot0 : ℕ) (xs : List FF) (ms : List ℤ) (sd sc : ℤ) :
    List (List ℤ) → List ℤ → ℕ → List (Bool × FF)
  | w :: ws, b :: bs, slot =>
    dotF dI ns (some slot0) (some slot) w xs ms sd sc b :: dotRows dI ns slot0 xs ms sd sc ws bs (slot + 1)
  | _, _, _ => []

/-- all rows of a stored matrix with biases applied to `xs`, symbols from slot `slot0` -/
def affF (dI : ℤ) (ns : ℕ) (slot0 : ℕ) (W : List (List ℤ)) (b : List ℤ) (xs : List FF) : Option (List FF) :=
  splitOK (dotRows dI ns slot0 xs (xs.map FF.mag) (sumI (xs.map FF.dev)) (sumI (xs.map (fun x => iabs x.c))) W b slot0)

/-- ReLU: exact when the sign is known; otherwise slope `lam / 2^20` (the chord slope rounded
down), offset and radius `mu` -/
def reluF (p : FF) : FF :=
  let lo := p.c - p.dev
  let hi := p.c + p.dev
  if 0 ≤ lo then p
  else if hi ≤ 0 then zeroF p.t.length
  else
    let lam := hi * 2 ^ 20 / (hi - lo)
    let mu := cdiv (max (-(lam * lo)) ((2 ^ 20 - lam) * hi)) (2 ^ 21)
    ⟨lam * p.c / 2 ^ 20 + mu, p.t.map (fun x => lam * x / 2 ^ 20),
     cdiv (lam * p.r) (2 ^ 20) + ((p.t.length : ℤ) + 1) + mu⟩

/-! ### the written network in integers -/

structure IW where
  E : List (List ℤ)
  g1 : List ℤ
  b1 : List ℤ
  g2 : List ℤ
  b2 : List ℤ
  gf : List ℤ
  bf : List ℤ
  W1 : List (List ℤ)
  c1 : List ℤ
  W2 : List (List ℤ)
  c2 : List ℤ
  oW : List ℤ
  oB : ℤ
  deriving DecidableEq

def intL (l : List ℚ) : List ℤ := l.map floorQ

def intW (N : LNNet) (B : ABlock) : IW :=
  ⟨N.net.embed.map intL, intL N.g1, intL N.b1, intL N.g2, intL N.b2, intL N.gf, intL N.bf,
   B.W1.map intL, intL B.b1, B.W2.map intL, intL B.b2, intL N.net.outW, floorQ N.net.outB⟩

/-- every weight that the integer part uses is on the grid, and the LayerNorm weights are small -/
def lnWeightsOK (δ : ℚ) (N : LNNet) (B : ABlock) (d : ℕ) : Bool :=
  gridOK δ && gridM N.net.embed && gridM B.W1 && gridL B.b1 && gridM B.W2 && gridL B.b2 &&
  gridL N.net.outW && gridOK N.net.outB &&
  [N.g1, N.b1, N.g2, N.b2, N.gf, N.bf].all (fun l => gridL l && smallQ l && l.length == d)

/-! ### LN1: a box per token -/

def unitL (ns k : ℕ) (v : ℤ) : List ℤ := (List.range ns).map (fun i => if i = k then v else 0)

/-- the stored embedding row as forms: entry `k` has symbol `k` with coefficient δ -/
def resF (dI : ℤ) (ns : ℕ) : List ℤ → ℕ → List FF
  | a :: l, k => ⟨a, unitL ns k dI, chg (iabs a + dI)⟩ :: resF dI ns l (k + 1)
  | [], _ => []

def boxOf (a : FF) : IV := ((a.c : ℚ) / SCq, (a.dev : ℚ) / SCq)

/-- the box of `LN1 (embedding row)` -/
def ln1Box (dI : ℤ) (ns : ℕ) (W : IW) (row : List ℤ) : Option (List IV) :=
  (lnF dI ns W.g1 W.b1 none (resF dI ns row 0)).map (fun l => l.map boxOf)

def allSomeL {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | none :: _ => none
  | some a :: l => (allSomeL l).map (fun r => a :: r)

/-! ### head tables with rounding charges relative to the magnitudes -/

def totQ (δ : ℚ) : List ℚ → List IV → ℚ
  | a :: r, x :: xs => (qabs a + δ) * (qabs x.1 + x.2) + totQ δ r xs
  | _, _ => 0

/-- a stored-weight row applied to a box: centre, and an error that charges the rounding of the
dot product relative to Σ |weight| · |entry| -/
def dotRel (δ : ℚ) (r : List ℚ) (x : List IV) : IV :=
  (dotC r x, wErrQ δ r x + ((r.length : ℚ) + 2) * totQ δ r x / 2 ^ 21 + 1 / 2 ^ 60)

def matRel (δ : ℚ) (M : List (List ℚ)) (x : List IV) : List IV := M.map (fun r => dotRel δ r x)

def pErrQ : List IV → List IV → ℚ
  | x :: xs, y :: ys => x.2 * (qabs y.1 + y.2) + qabs x.1 * y.2 + pErrQ xs ys
  | _, _ => 0

def ptotQ : List IV → List IV → ℚ
  | x :: xs, y :: ys => (qabs x.1 + x.2) * (qabs y.1 + y.2) + ptotQ xs ys
  | _, _ => 0

/-- content score of a query box against a key box, entry by entry -/
def scoreRel (δ : ℚ) (h : AHead) (xq xt : List IV) : IV :=
  (dotC (xq.map Prod.fst) (matRel δ h.A xt),
   pErrQ xq (matRel δ h.A xt) + ((xq.length : ℚ) + 2) * ptotQ xq (matRel δ h.A xt) / 2 ^ 21 + 1 / 2 ^ 60)

/-- range guards for a content score, as in rung 7 -/
def scoreOKR (δ : ℚ) (h : AHead) (xq xt : List IV) : Bool :=
  decide ((maxAbs (xq.map Prod.fst) + maxAbs (xq.map Prod.snd) + 1) *
          (maxAbs ((matRel δ h.A xt).map Prod.fst) + maxAbs ((matRel δ h.A xt).map Prod.snd) + 1) ≤ 2 ^ 20) &&
  decide (qabs (scoreRel δ h xq xt).1 + (scoreRel δ h xq xt).2 ≤ 1024)

/-- a bound on one value row over the candidate tokens (rung 7's `hs_Bf` with `dotRel`) -/
def bfRel (δ : ℚ) (E : List (List IV)) (cd : List Bool) (r : List ℚ) : ℚ :=
  ((List.zip E cd).filter (fun a => a.2)).foldl
    (fun m a => max m (qabs (dotRel δ r a.1).1 + (dotRel δ r a.1).2)) 0

/-- per output coordinate, a bound on the head's value over all candidate tokens -/
def valBoundR (δ : ℚ) (E : List (List IV)) (h : AHead) (cd : List Bool) : List ℚ :=
  h.V.map (bfRel δ E cd)

/-- `headOK8` of rung 8 (Lane4/R8Cert.lean), conjunct for conjunct, with the score table, the
value table, the value bounds and the score guards on relative charges:
`scoreIV → scoreRel`, `matIV → matRel`, `valBound → valBoundR`, `scoreOK → scoreOKR`. -/
def headOKLN (δ : ℚ) (E : List (List IV)) (h : AHead) (hc : HCert) : Bool :=
  decide (h.mask ≠ Mask.all) && decide (1 ≤ h.m) && decide (h.m ≤ 1024) &&
  hc.cands.length == E.length &&
  (List.zipWith (fun x b => gateDec δ h x == some b) E hc.cands).all id &&
  decide (hc.S = E.map (fun xq => E.map (fun xt => scoreRel δ h xq xt))) &&
  decide (hc.VE = E.map (fun xt => matRel δ h.V xt)) &&
  decide (hc.Bv = valBoundR δ E h hc.cands) &&
  hc.Bv.all (fun B => decide (B ≤ 2 ^ 20)) &&
  (E.drop 1).all (fun xq => (List.zip E hc.cands).all (fun a => !a.2 || scoreOKR δ h xq a.1)) &&
  decide (0 ≤ hc.spread) &&
  ((List.range E.length).drop 1).all (fun q =>
    (List.zip (List.range E.length) hc.cands).all (fun a =>
      (List.zip (List.range E.length) hc.cands).all (fun b =>
        !a.2 || !b.2 ||
        decide ((sAt hc q b.1).1 - (sAt hc q a.1).1 + (sAt hc q a.1).2 + (sAt hc q b.1).2
                ≤ hc.spread)))) &&
  decide (1 ≤ hc.L) && decide (hc.L ≤ 3) && decide (16 ≤ tailRoom δ h hc)

/-! ### one position -/

def padTo (ns : ℕ) (l : List ℤ) : List ℤ := l ++ List.replicate (ns - l.length) 0

/-- a head-output coordinate as an integer form: floors of centre and coefficients, and the whole
radius (rounded up, plus one unit per floor) as the coefficient of the coordinate's own slot. The
Boolean: the padded list has `ns` slots and is zero from slot `hB` on before the slot is set. -/
def hoF (ns hB slot : ℕ) (n8 : ℤ) (a : AF) : Bool × FF :=
  let base : FF := ⟨floorQ a.c, padTo ns (a.t.map floorQ), 0⟩
  (zeroFrom hB base && base.t.length == ns, ⟨base.c, addAt base.t slot (ceilQ a.r + 1 + n8), 0⟩)

/-- one coordinate of the residual stream plus the head output, rounded; with the guards -/
def addOne (a : FF) (h : Bool × FF) : Bool × FF :=
  let y := (a.add h.2).wide (chg (a.add h.2).mag)
  (h.1 && y.small, y)

/-- add the head output `ho` (coordinates `r, r+1, ...`) to the residual forms -/
def addHO (ns hB slot0 : ℕ) (n8 : ℤ) : List FF → List AF → ℕ → List (Bool × FF)
  | a :: acc, o :: ho, r => addOne a (hoF ns hB (slot0 + r) n8 o) :: addHO ns hB slot0 n8 acc ho (r + 1)
  | _, _, _ => []

/-- residual stream after the heads. Head `k` uses attention slots `d + 3k, ..., d + 3k + 2` and
head-output slots `hB + k d ..`; at most four keys per head; the forms so far must be free of
this head's symbols. -/
def headsF (δ : ℚ) (d ns hB : ℕ) (t : ℕ) :
    List AHead → List HCert → List (List ℕ) → ℕ → List FF → Option (List FF)
  | h :: hs, hc :: hcs, win :: wins, k, acc =>
    if (keysAt h hc t win).length ≤ 4 ∧
       acc.all (fun a => zeroRange (d + 3 * k) (d + 3 * k + 3) a && zeroFrom (hB + k * d) a) = true then
      match headAF δ h hc d (d + 3 * k) t (keysAt h hc t win) with
      | none => none
      | some ho =>
        match splitOK (addHO ns hB (hB + k * d) (((keysAt h hc t win).length - 1 : ℕ) : ℤ) acc ho 0) with
        | none => none
        | some acc' => headsF δ d ns hB t hs hcs wins (k + 1) acc'
    else none
  | _, _, _, _, acc => some acc

/-- the certificate -/
structure CertLN where
  /-- head certificates on the LN1 boxes (`headOKLN`) -/
  heads : List HCert
  /-- the LN1 box of each embedding row (BOS first) -/
  boxes : List (List IV)
  /-- the written weights in units of 2^-56 -/
  W : IW
  states : List (ℕ × List (List ℕ))

/-- the output form for query token `t` and the windows of the heads; `none` if a guard fails -/
def outLN (δ : ℚ) (dI : ℤ) (B : ABlock) (c : CertLN) (d : ℕ) (t : ℕ) (wins : List (List ℕ)) :
    Option FF :=
  let nh := B.heads.length
  let hB := d + 3 * nh
  let lB := hB + nh * d
  let wB := lB + d
  let vB := wB + c.W.c1.length
  let ns := vB + d
  match headsF δ d ns hB t B.heads c.heads wins 0 (resF dI ns (c.W.E.getD t []) 0) with
  | none => none
  | some y =>
    if y.all (zeroFrom lB) then
      match lnF dI ns c.W.g2 c.W.b2 (some lB) y with
      | none => none
      | some y2 =>
        match affF dI ns wB c.W.W1 c.W.c1 y2 with
        | none => none
        | some a1 =>
          if (a1.map reluF).all FF.small then
          match affF dI ns vB c.W.W2 c.W.c2 (a1.map reluF) with
          | none => none
          | some a2 =>
            match splitOK (List.zipWith (fun a b => addOne a (true, b)) y a2) with
            | none => none
            | some z =>
              match lnF dI ns c.W.gf c.W.bf none z with
              | none => none
              | some zf =>
                splitOK1 (dotF dI ns none none c.W.oW zf (zf.map FF.mag) (sumI (zf.map FF.dev))
                           (sumI (zf.map (fun x => iabs x.c))) c.W.oB)
          else none
    else none

def caseOKLN (δ : ℚ) (dI : ℤ) (B : ABlock) (T : Task) (c : CertLN) (d : ℕ)
    (st : ℕ × List (List ℕ)) (t : ℕ) : Bool :=
  match outLN δ dI B c d t st.2 with
  | none => false
  | some o =>
    decide (4 * (iabs (o.c - (T.out st.1 t : ℤ) * SC) + o.dev) ≤ SC) &&
    c.states.contains (T.step st.1 t, List.zipWith (fun hc win => winNext hc t win) c.heads st.2)

def boxOK (d : ℕ) (row : List IV) : Bool :=
  row.length == d && row.all (fun a => decide (0 ≤ a.2) && decide (qabs a.1 + a.2 ≤ 16))

/-- the number of symbol slots -/
def slots (B : ABlock) (d : ℕ) : ℕ := d + 3 * B.heads.length + B.heads.length * d + d + B.b1.length + d

/-- The checker. `δ` is the radius of the additive ball around the written network `N`. -/
def checkLN (δ : ℚ) (N : LNNet) (T : Task) (c : CertLN) : Bool :=
  match N.net.blocks with
  | [B] =>
    let d := (N.net.embed.headD []).length
    let dI := floorQ δ
    decide (0 ≤ δ) && decide (δ ≤ 1 / 2) &&
    N.net.shapeOK T.ntok && weightsOK N.net B && lnWeightsOK δ N B d &&
    decide (B.heads.length ≤ 2) && decide (1 ≤ d) &&
    decide (c.W = intW N B) &&
    decide (allSomeL (c.W.E.map (ln1Box dI (slots B d) c.W)) = some c.boxes) &&
    c.boxes.all (boxOK d) &&
    c.heads.length == B.heads.length &&
    (List.zipWith (fun h hc => headOKLN δ c.boxes h hc) B.heads c.heads).all id &&
    c.states.all (fun st => st.2.length == B.heads.length) &&
    c.states.contains (T.init, c.heads.map (fun hc => if hc.cands.getD 0 false = true then [0] else [])) &&
    c.states.all (fun st => (List.range T.ntok).all (fun k => caseOKLN δ dI B T c d st (k + 1)))
  | _ => false

/-- THE SOUNDNESS THEOREM of rung 9-LN15: if the checker accepts `N` at radius `δ`, then every
network within the additive `δ`-ball of `N` (LayerNorm gains and biases included), in the rounding
model with the square-root assumption, is within 1/4 of the task's target at every position of
every input of every length the rounding model covers. -/
def SoundLN : Prop :=
  ∀ (δ : ℚ) (N : LNNet) (T : Task) (c : CertLN), checkLN δ N T c = true →
  ∀ (u η M : ℝ) (fl ex sq : ℝ → ℝ), Rnd u η M fl → ExpM u η ex → SqrtM u η sq →
  0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  ∀ p : LPert, p.Within (δ : ℝ) →
  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ T.ntok) →
  u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 → η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100 →
  2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M →
  ∀ i : ℕ, 1 ≤ i → i ≤ w.length →
    |N.out fl ex sq p w i - ((T.target w i : ℕ) : ℝ)| ≤ 1 / 4

end Lane4.LNC
