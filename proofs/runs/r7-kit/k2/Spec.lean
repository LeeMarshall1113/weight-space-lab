namespace Lane4.Case
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert

/-- The standing hypotheses on the rounding model. -/
structure Ctx (u η M : ℝ) (fl : ℝ → ℝ) : Prop where
  rnd : Rnd u η M fl
  u0 : 0 ≤ u
  u1 : u ≤ 1 / 2 ^ 24
  h0 : 0 ≤ η
  h1 : η ≤ 1 / 2 ^ 149
  M1 : 2 ^ 40 ≤ M

/-- The real `x` lies in the interval `v` = (centre, radius). -/
def InIV (x : ℝ) (v : IV) : Prop := |x - ((v.1 : ℚ) : ℝ)| ≤ ((v.2 : ℚ) : ℝ)

/-- Entry by entry, with equal lengths. -/
def InIVs (x : List ℝ) (v : List IV) : Prop :=
  x.length = v.length ∧ ∀ k, k < x.length → InIV (x.getD k 0) (v.getD k (0, 0))

/-- Every interval has a non-negative radius and reaches at most `B` from 0. -/
def Bdd (B : ℚ) (v : List IV) : Prop := ∀ a ∈ v, 0 ≤ a.2 ∧ qabs a.1 + a.2 ≤ B

/-- A stored embedding row lies in `embIV`. -/
def EmbSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (row : List ℚ) (d : ℕ → ℝ), (∀ k, |d k| ≤ (δ : ℝ)) → smallQ row = true →
    InIVs (aswRow fl row d 0) (embIV δ row) ∧ Bdd 16 (embIV δ row)

/-- A stored-weight dot product lies in `dotIV`. -/
def DotSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (r : List ℚ) (x : List ℝ) (xv : List IV) (d : ℕ → ℝ), (∀ k, |d k| ≤ (δ : ℝ)) →
  r.length = x.length → r.length ≤ 32 → smallQ r = true → InIVs x xv → Bdd 16 xv →
    InIV (ardot fl r x d 0 0) (dotIV δ r xv) ∧ 0 ≤ (dotIV δ r xv).2

/-- A stored matrix applied to a vector lies in `matIV`. -/
def MatSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (A : List (List ℚ)) (x : List ℝ) (xv : List IV) (d : ℕ → ℕ → ℝ),
  (∀ i k, |d i k| ≤ (δ : ℝ)) → (∀ r ∈ A, r.length = x.length) → x.length ≤ 32 →
  smallM A = true → InIVs x xv → Bdd 16 xv →
    InIVs (armat fl A x d 0) (matIV δ A xv) ∧ ∀ a ∈ matIV δ A xv, 0 ≤ a.2

/-- A stored affine map lies in `affIV`, when every output passes the magnitude guard. -/
def AffSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (A : List (List ℚ)) (b : List ℚ) (x : List ℝ) (xv : List IV) (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ),
  (∀ i k, |dW i k| ≤ (δ : ℝ)) → (∀ i, |db i| ≤ (δ : ℝ)) →
  (∀ r ∈ A, r.length = x.length) → x.length ≤ 32 →
  smallM A = true → smallQ b = true → InIVs x xv → Bdd 16 xv →
  (affIV δ A b xv).all small = true →
    InIVs (araffine fl A b x dW db 0) (affIV δ A b xv) ∧ Bdd 15 (affIV δ A b xv)

/-- A rounded entrywise sum lies in `addIV`, when every output passes the magnitude guard. -/
def AddSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl →
  ∀ (a b : List ℝ) (av bv : List IV), InIVs a av → InIVs b bv →
  (∀ v ∈ av, 0 ≤ v.2) → (∀ v ∈ bv, 0 ≤ v.2) → (addIV av bv).all small = true →
    InIVs (radd fl a b) (addIV av bv) ∧ Bdd 15 (addIV av bv)

/-- ReLU maps an interval into its clamp. -/
def ReluSound : Prop :=
  ∀ (x : List ℝ) (xv : List IV), InIVs x xv → Bdd 15 xv →
    InIVs (x.map Lane4.relu) (xv.map reluIV) ∧ Bdd 15 (xv.map reluIV)

/-- A decided gate: the gate neuron is exactly 0 if and only if the checker says "candidate". -/
def GateSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (h : AHead) (x : List ℝ) (xv : List IV) (dg : ℕ → ℝ) (dgb : ℝ),
  (∀ k, |dg k| ≤ (δ : ℝ)) → |dgb| ≤ (δ : ℝ) →
  h.g.length = x.length → h.g.length ≤ 32 → smallQ h.g = true → smallQ [h.gb] = true →
  InIVs x xv → Bdd 16 xv →
  ∀ b : Bool, gateDec δ h xv = some b → (h.gate fl dg dgb x = 0 ↔ b = true)

/-- The content score of a query state against a key state lies in `scoreIV`, and is at most
1024 in size, when `scoreOK` holds. -/
def ScoreSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (h : AHead) (xq xt : List ℝ) (xqv xtv : List IV) (dA : ℕ → ℕ → ℝ),
  (∀ i k, |dA i k| ≤ (δ : ℝ)) →
  (∀ r ∈ h.A, r.length = xt.length) → xt.length ≤ 32 → h.A.length = xq.length → xq.length ≤ 32 →
  smallM h.A = true → InIVs xq xqv → Bdd 16 xqv → InIVs xt xtv → Bdd 16 xtv →
  scoreOK δ h xqv xtv = true →
    InIV (pdot fl xq (armat fl h.A xt dA 0) 0) (scoreIV δ h xqv xtv)
    ∧ 0 ≤ (scoreIV δ h xqv xtv).2
    ∧ |pdot fl xq (armat fl h.A xt dA 0) 0| ≤ 1024

end Lane4.Case
