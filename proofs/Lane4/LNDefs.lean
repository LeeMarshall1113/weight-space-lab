/-
Lane 4, rung 9-LN15: definitions shared by the kit cases (meaning of the integer forms) and the
STATEMENTS of the kit cases. Written by the lane. No theorems.

Kit cases (each proves the statements named; `SoundLN` of Lane4/LNCert.lean is the last):

  la  RsumRel, ArdotRel, PdotRel, DotRelSound, ScoreRelSound
                                        rounded chains with relative error; tables (rung 7: DotSound, ScoreSound)
  lb  ScoreWinLN                        port of rung 8's ScoreWin (Lane4/R8KA.lean) to `headOKLN`
  lc  HeadSoundLN                       port of rung 8's HeadSound8 (Lane4/R8KG.lean) to `headOKLN`
  ld  FrameFF, ZeroFacts, BoxSound, AddFSound, ReluFSound, ResFSound, HoFSound   small lemmas on integer forms
  le  DotFSound                         a stored row applied to forms, with its symbol
  lf  CentSound, VarSound               LayerNorm: mean, centring, variance
  lg  RinvSound                         LayerNorm: reciprocal square root (the analytic lemma)
  lh  LnFSound                          LayerNorm assembled (lnOne, slots)
  li  SoundLN                           the abstract machine and the assembly (rung 8: Lane4/R8K.lean)
-/
import Lane4.LNCert

namespace Lane4.LNC

open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd rsum)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.R7K2

/-! ### meaning of integer forms -/

/-- value of an integer coefficient list under the symbol values `e`, the first coefficient
belonging to symbol number `k` -/
noncomputable def linValI : List ℤ → (ℕ → ℝ) → ℕ → ℝ
  | a :: l, e, k => (a : ℝ) * e k + linValI l e (k + 1)
  | [], _, _ => 0

/-- The real `v` is represented by the integer form `a` under the symbol values `e`:
`v * 2^56` is within the radius of centre + Σ coefficient · symbol. -/
def InFF (e : ℕ → ℝ) (v : ℝ) (a : FF) : Prop :=
  |v * 2 ^ 56 - ((a.c : ℝ) + linValI a.t e 0)| ≤ (a.r : ℝ)

/-- Entry by entry, with equal lengths. -/
def InFFs (e : ℕ → ℝ) (v : List ℝ) (a : List FF) : Prop :=
  v.length = a.length ∧ ∀ k, k < v.length → InFF e (v.getD k 0) (a.getD k (zeroF 0))

/-- every form has `ns` symbol slots and passes the magnitude guard of 16 -/
def Shaped (ns : ℕ) (a : List FF) : Prop := ∀ x ∈ a, x.t.length = ns ∧ x.mag ≤ 16 * SC

/-- the symbol values agree below slot `m` -/
def AgreeBelow (m : ℕ) (e e' : ℕ → ℝ) : Prop := ∀ k, k < m → e' k = e k

/-! ### la: rounded chains with an error relative to the magnitudes; tables -/

/-- Σ l -/
noncomputable def sumL : List ℝ → ℝ
  | a :: l => a + sumL l
  | [] => 0

/-- Σ |l| -/
noncomputable def sumAbsL : List ℝ → ℝ
  | a :: l => |a| + sumAbsL l
  | [] => 0

/-- Σ (a_i + d_i) * v_i, the perturbation of the first weight being `d j` -/
noncomputable def dotP : List ℚ → List ℝ → (ℕ → ℝ) → ℕ → ℝ
  | a :: w, v :: x, d, j => (((a : ℚ) : ℝ) + d j) * v + dotP w x d (j + 1)
  | _, _, _, _ => 0

/-- Σ (|a_i| + δ) * |v_i| -/
noncomputable def dotT (δ : ℝ) : List ℚ → List ℝ → ℝ
  | a :: w, v :: x => (|((a : ℚ) : ℝ)| + δ) * |v| + dotT δ w x
  | _, _ => 0

/-- Σ x_i * y_i -/
noncomputable def dotR : List ℝ → List ℝ → ℝ
  | a :: x, b :: y => a * b + dotR x y
  | _, _ => 0

/-- Σ |x_i * y_i| -/
noncomputable def dotRA : List ℝ → List ℝ → ℝ
  | a :: x, b :: y => |a * b| + dotRA x y
  | _, _ => 0

/-- A left-to-right rounded sum of at most 32 terms. -/
def RsumRel : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl →
  ∀ l : List ℝ, l.length ≤ 32 → (∀ v ∈ l, |v| ≤ 2 ^ 30) →
    |rsum fl l 0 - sumL l| ≤ 2 * (l.length : ℝ) * u * sumAbsL l + 2 * (l.length : ℝ) * η

/-- A rounded dot product with stored (perturbed, rounded) weights. -/
def ArdotRel : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (r : List ℚ) (x : List ℝ) (d : ℕ → ℝ), (∀ k, |d k| ≤ δ) →
  r.length = x.length → r.length ≤ 32 → smallQ r = true → (∀ v ∈ x, |v| ≤ 17) →
    |ardot fl r x d 0 0 - dotP r x d 0|
      ≤ 2 * ((r.length : ℝ) + 2) * u * dotT δ r x + 200 * (r.length : ℝ) * η

/-- A rounded dot product of two real vectors. -/
def PdotRel : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl →
  ∀ (x y : List ℝ) (A B : ℝ), x.length = y.length → x.length ≤ 32 →
  (∀ v ∈ x, |v| ≤ A) → (∀ v ∈ y, |v| ≤ B) → 0 ≤ A → 0 ≤ B → A * B ≤ 2 ^ 20 →
    |pdot fl x y 0 - dotR x y|
      ≤ 2 * ((x.length : ℝ) + 2) * u * dotRA x y + 200 * (x.length : ℝ) * η

/-- A stored-weight dot product lies in `dotRel`. -/
def DotRelSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (r : List ℚ) (x : List ℝ) (xv : List IV) (d : ℕ → ℝ), (∀ k, |d k| ≤ (δ : ℝ)) →
  r.length = x.length → r.length ≤ 32 → smallQ r = true → InIVs x xv → Bdd 16 xv →
    InIV (ardot fl r x d 0 0) (dotRel δ r xv) ∧ 0 ≤ (dotRel δ r xv).2

/-- The content score of a query state against a key state lies in `scoreRel`, and is at most
1024 in size, when `scoreOKR` holds. -/
def ScoreRelSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (h : AHead) (xq xt : List ℝ) (xqv xtv : List IV) (dA : ℕ → ℕ → ℝ),
  (∀ i k, |dA i k| ≤ (δ : ℝ)) →
  (∀ r ∈ h.A, r.length = xt.length) → xt.length ≤ 32 → h.A.length = xq.length → xq.length ≤ 32 →
  smallM h.A = true → InIVs xq xqv → Bdd 16 xqv → InIVs xt xtv → Bdd 16 xtv →
  scoreOKR δ h xqv xtv = true →
    InIV (pdot fl xq (armat fl h.A xt dA 0) 0) (scoreRel δ h xqv xtv)
    ∧ 0 ≤ (scoreRel δ h xqv xtv).2
    ∧ |pdot fl xq (armat fl h.A xt dA 0) 0| ≤ 1024

/-! ### lb, lc: the head -/

/-- `Lane4.R8KA.ScoreWin` for a head that passes `headOKLN`. -/
def ScoreWinLN : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl →
  ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (h : AHead) (E : List (List IV)) (hc : HCert) (dd : ℕ),
  headOKLN δ E h hc = true → h.shapeOK dd = true → dd ≤ 24 → smallM h.A = true →
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

/-- `Lane4.R8KG.HeadSound8` for a head that passes `headOKLN`: the head's output vector is
represented by the forms of rung 8's `headAF`. -/
def HeadSoundLN : Prop :=
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Ctx u η M fl → ExpM u η ex →
  ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (h : AHead) (E : List (List IV)) (hc : HCert) (dd : ℕ),
  headOKLN δ E h hc = true → h.shapeOK dd = true → dd ≤ 24 →
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

/-! ### ld: small lemmas on integer forms -/

/-- A form does not see a symbol whose coefficient is zero. -/
def FrameFF : Prop :=
  ∀ (a : FF) (e e' : ℕ → ℝ) (v : ℝ),
  (∀ k, e' k ≠ e k → a.t.getD k 0 = 0) → InFF e v a → InFF e' v a

/-- what the zero guards say -/
def ZeroFacts : Prop :=
  (∀ (m : ℕ) (a : FF), zeroFrom m a = true → ∀ k, m ≤ k → a.t.getD k 0 = 0)
  ∧ (∀ (lo hi : ℕ) (a : FF), zeroRange lo hi a = true → ∀ k, lo ≤ k → k < hi → a.t.getD k 0 = 0)

/-- A form gives a box. -/
def BoxSound : Prop :=
  ∀ (e : ℕ → ℝ) (v : ℝ) (a : FF), Sym e → InFF e v a →
    InIV v (boxOf a) ∧ 0 ≤ (boxOf a).2 ∧ |v| * 2 ^ 56 ≤ (a.mag : ℝ)

/-- A rounded sum of two values (`addOne` with a true guard; `radd`). -/
def AddFSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl →
  ∀ (e : ℕ → ℝ) (x y : ℝ) (a b : FF), Sym e → InFF e x a → InFF e y b →
  a.t.length = b.t.length → a.mag ≤ 16 * SC → b.mag ≤ 16 * SC →
    InFF e (fl (x + y)) (addOne a (true, b)).2

/-- ReLU. -/
def ReluFSound : Prop :=
  ∀ (e : ℕ → ℝ) (v : ℝ) (p : FF), Sym e → InFF e v p →
    InFF e (Lane4.relu v) (reluF p) ∧ (reluF p).t.length = p.t.length

/-- The stored embedding row as forms: symbol `k` (`k < row.length`) carries the perturbation of
entry `k`. There are symbol values `e0` such that the row is represented under every assignment
that agrees with `e0` on the first `row.length` slots. -/
def ResFSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 → gridOK δ = true →
  ∀ (ns : ℕ) (row : List ℚ) (d : ℕ → ℝ), (∀ k, |d k| ≤ (δ : ℝ)) →
  smallQ row = true → gridL row = true → row.length ≤ ns →
    ∃ e0 : ℕ → ℝ, (∀ k, |e0 k| ≤ 1) ∧
      (∀ e : ℕ → ℝ, AgreeBelow row.length e0 e →
        InFFs e (aswRow fl row d 0) (resF (floorQ δ) ns (intL row) 0))
      ∧ Shaped ns (resF (floorQ δ) ns (intL row) 0)
      ∧ ∀ a ∈ resF (floorQ δ) ns (intL row) 0, zeroFrom row.length a = true

/-- A head-output coordinate: the rung-8 rational form `a` (whose coefficients are `pre` zeros
followed by at most `n8` entries) becomes an integer form whose own slot carries the whole
radius. If the guard holds, there is a value `s` for the slot such that the coordinate is
represented under every assignment that agrees with `e` below `hB` and gives `s` to the slot. -/
def HoFSound : Prop :=
  ∀ (e : ℕ → ℝ) (v : ℝ) (a : AF) (pre : ℕ) (rest : List ℚ) (ns hB slot : ℕ) (n8 : ℕ),
  Sym e → InAF e v a → a.t = List.replicate pre 0 ++ rest → rest.length ≤ n8 →
  hB ≤ slot → slot < ns → (hoF ns hB slot (n8 : ℤ) a).1 = true →
    ∃ s : ℝ, |s| ≤ 1 ∧
      (∀ e' : ℕ → ℝ, AgreeBelow hB e e' → e' slot = s → InFF e' v (hoF ns hB slot (n8 : ℤ) a).2)
      ∧ (hoF ns hB slot (n8 : ℤ) a).2.t.length = ns
      ∧ ∀ k, hB ≤ k → k ≠ slot → (hoF ns hB slot (n8 : ℤ) a).2.t.getD k 0 = 0

/-! ### le: a stored row applied to forms -/

/-- `x` real vector represented by the forms `X`; a stored row `w` with bias `b`, perturbed by
`dW`, `db`. Without a slot the result is represented under the same symbols. With a slot `s`
(and the guard of `dotF` true: the form is free of the slots from `s0` on before `s` is set)
there is a value for the slot such that the result is represented under every assignment that
agrees with `e` below `s0` and gives that value to slot `s`. -/
def DotFSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 → gridOK δ = true →
  ∀ (ns : ℕ) (w : List ℚ) (b : ℚ) (x : List ℝ) (X : List FF) (dW : ℕ → ℝ) (db : ℝ) (e : ℕ → ℝ),
  Sym e → (∀ k, |dW k| ≤ (δ : ℝ)) → |db| ≤ (δ : ℝ) →
  w.length = x.length → w.length ≤ 32 → smallQ w = true → smallQ [b] = true →
  gridL w = true → gridOK b = true → InFFs e x X → Shaped ns X →
  ∀ (slot0 slot : Option ℕ),
  (dotF (floorQ δ) ns slot0 slot (intL w) X (X.map FF.mag) (sumI (X.map FF.dev))
      (sumI (X.map (fun a => iabs a.c))) (floorQ b)).1 = true →
    (dotF (floorQ δ) ns slot0 slot (intL w) X (X.map FF.mag) (sumI (X.map FF.dev))
        (sumI (X.map (fun a => iabs a.c))) (floorQ b)).2.t.length = ns
    ∧ (dotF (floorQ δ) ns slot0 slot (intL w) X (X.map FF.mag) (sumI (X.map FF.dev))
        (sumI (X.map (fun a => iabs a.c))) (floorQ b)).2.mag ≤ 15 * SC
    ∧ (slot = none →
        InFF e (fl (ardot fl w x dW 0 0 + asw fl b db))
          (dotF (floorQ δ) ns slot0 slot (intL w) X (X.map FF.mag) (sumI (X.map FF.dev))
            (sumI (X.map (fun a => iabs a.c))) (floorQ b)).2)
    ∧ (∀ s0 s : ℕ, slot0 = some s0 → slot = some s → s0 ≤ s → s < ns →
        ∃ v : ℝ, |v| ≤ 1 ∧ ∀ e' : ℕ → ℝ, AgreeBelow s0 e e' → e' s = v →
          InFF e' (fl (ardot fl w x dW 0 0 + asw fl b db))
            (dotF (floorQ δ) ns slot0 slot (intL w) X (X.map FF.mag) (sumI (X.map FF.dev))
              (sumI (X.map (fun a => iabs a.c))) (floorQ b)).2)

/-! ### lf, lg, lh: LayerNorm -/

/-- the centred vector is represented by `centF (meanF ns X) X` -/
def CentSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl →
  ∀ (ns : ℕ) (x : List ℝ) (X : List FF) (e : ℕ → ℝ), Sym e → ns ≤ 1024 →
  1 ≤ x.length → x.length ≤ 32 → InFFs e x X → Shaped ns X →
    InFFs e (lnCentre fl x) (centF (meanF ns X) X)
    ∧ ∀ c ∈ centF (meanF ns X) X, c.t.length = ns ∧ c.mag ≤ 64 * SC

/-- the rounded variance plus epsilon of a centred vector is represented by `varW` -/
def VarSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl →
  ∀ (ns : ℕ) (c : List ℝ) (C : List FF) (e : ℕ → ℝ), Sym e →
  1 ≤ c.length → c.length ≤ 32 → InFFs e c C → (∀ a ∈ C, a.t.length = ns ∧ a.mag ≤ 64 * SC) →
    InFF e (fl (fl (rsum fl (c.map (fun v => fl (v * v))) 0 / (c.length : ℝ)) + fl (1 / 100000)))
      (varW ns C)
    ∧ (varW ns C).t.length = ns

/-- the reciprocal of the rounded standard deviation: `vh` is the rounded variance plus epsilon,
represented by `v`; the checker's guards hold (`a`, `b` verified integer square roots) -/
def RinvSound : Prop :=
  ∀ (u η M : ℝ) (fl sq : ℝ → ℝ), Ctx u η M fl → SqrtM u η sq →
  ∀ (ns : ℕ) (vh : ℝ) (v : FF) (a b : ℤ) (rinv : FF) (e : ℕ → ℝ), Sym e →
  InFF e vh v → v.t.length = ns → 0 < v.c - v.dev →
  sqrtOK (v.c * SC) a = true → sqrtOK ((v.c - v.dev) * SC) b = true → 1 ≤ b →
  rinvF ns v a b = some rinv →
    0 < sq vh ∧ InFF e (1 / sq vh) rinv ∧ rinv.t.length = ns

/-- LayerNorm of a vector represented by forms. Without slots the output is represented under the
same symbols; with slots from `s0` there are values for the slots `s0, ..., s0 + n - 1` such that
the output is represented under every assignment that agrees with `e` below `s0` and has those
values. -/
def LnFSound : Prop :=
  ∀ (u η M : ℝ) (fl sq : ℝ → ℝ), Ctx u η M fl → SqrtM u η sq →
  ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 → gridOK δ = true →
  ∀ (ns : ℕ) (g b : List ℚ) (dg db : ℕ → ℝ) (x : List ℝ) (X Y : List FF) (e : ℕ → ℝ), Sym e →
  (∀ k, |dg k| ≤ (δ : ℝ)) → (∀ k, |db k| ≤ (δ : ℝ)) →
  1 ≤ x.length → x.length ≤ 32 → g.length = x.length → b.length = x.length →
  smallQ g = true → smallQ b = true → gridL g = true → gridL b = true →
  InFFs e x X → Shaped ns X → ns ≤ 1024 →
  ∀ slot0 : Option ℕ, lnF (floorQ δ) ns (intL g) (intL b) slot0 X = some Y →
    (∀ y ∈ Y, y.t.length = ns ∧ y.mag ≤ 15 * SC)
    ∧ (slot0 = none → InFFs e (lnorm fl sq g b dg db x) Y)
    ∧ (∀ s0 : ℕ, slot0 = some s0 → s0 + x.length ≤ ns →
        ∃ e1 : ℕ → ℝ, (∀ k, |e1 k| ≤ 1) ∧
          ∀ e' : ℕ → ℝ, AgreeBelow s0 e e' → (∀ k, k < x.length → e' (s0 + k) = e1 k) →
            InFFs e' (lnorm fl sq g b dg db x) Y)

end Lane4.LNC
