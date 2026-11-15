/-
Lane 4, rung 6c: token-blind networks. STATEMENTS ONLY at the time of pre-registration
(PREREG_R6C.md): the `def ... : Prop` below are statements to be proved; nothing here is
proved. This text is used after the text of Lane4/Collision.lean (it uses `Lane4.Coll.netRel`),
on top of `import Lane4.Seq`.

A network is token-blind for a list `T` of embedding coordinates when it reads those
coordinates only through global uniform averages: heads with a zero score matrix and mask
`all`. Everything else (every other score entry, value entry, MLP first-layer entry and
read-out entry) is zero on `T`. The condition is a Boolean function of the weights and
depends only on which entries are zero, so it is preserved by relative perturbations.
-/
namespace Lane4.TB
open Lane4.Seq Lane4.Coll

/-- The row is zero at every coordinate in `T`. -/
def zeroOn (T : List ℕ) (row : Vec) : Bool := T.all (fun c => row.getD c 0 == 0)

def isZero (M : List Vec) : Bool := M.all (fun r => r.all (fun v => v == 0))

/-- No nonzero score entry `A[p][q]` with `p ∈ T` or `q ∈ T`. -/
def blindScore (T : List ℕ) (A : List Vec) : Bool :=
  T.all (fun p => (A.getD p []).all (fun v => v == 0)) && A.all (zeroOn T)

def headBlind (T : List ℕ) (h : Head) : Bool :=
  (isZero h.A && decide (h.mask = Mask.all)) || (blindScore T h.A && h.V.all (zeroOn T))

def blockBlind (T : List ℕ) (B : Block) : Bool :=
  B.heads.all (headBlind T) && B.W1.all (zeroOn T)

/-- `ntok` real tokens; `T` the token coordinates. -/
def tokenBlind (N : TNet) (ntok : ℕ) (T : List ℕ) : Bool :=
  N.shapeOK ntok &&
  T.all (fun c => decide (c < (N.embed.getD 0 []).length)) &&
  (List.range (N.embed.getD 0 []).length).all (fun c => T.contains c ||
    (List.range ntok).all (fun t =>
      (N.embed.getD (t + 1) []).getD c 0 == (N.embed.getD 1 []).getD c 0)) &&
  N.blocks.all (blockBlind T) && zeroOn T N.outW

/-- Sum over all positions of coordinate `c` of the embedded tokens of `w` (BOS included). -/
def colSum (N : TNet) (w : List ℕ) (c : ℕ) : ℚ :=
  ((List.range (w.length + 1)).map (fun j => (N.embed.getD (tokAt w j) []).getD c 0)).sum

/-- `N'` is `N` with possibly different embedding entries on the coordinates in `T`. -/
def SameOffT (N N' : TNet) (T : List ℕ) : Prop :=
  N'.blocks = N.blocks ∧ N'.outW = N.outW ∧ N'.outB = N.outB ∧
  N'.embed.length = N.embed.length ∧
  (∀ t, (N'.embed.getD t []).length = (N.embed.getD t []).length) ∧
  (∀ t c, c ∉ T → (N'.embed.getD t []).getD c 0 = (N.embed.getD t []).getD c 0)

/-- STATEMENT 1 (invariance). For a token-blind network, two variants that differ only in
embedding entries on `T`, and two valid inputs of the same length whose embedded tokens
have equal column sums on `T`, give equal outputs at every position. -/
def Invariance : Prop :=
  ∀ (N N₁ N₂ : TNet) (ntok : ℕ) (T : List ℕ), tokenBlind N ntok T = true →
    SameOffT N N₁ T → SameOffT N N₂ T →
  ∀ w₁ w₂ : List ℕ, (∀ t ∈ w₁, 1 ≤ t ∧ t ≤ ntok) → (∀ t ∈ w₂, 1 ≤ t ∧ t ≤ ntok) →
    w₁.length = w₂.length → (∀ c ∈ T, colSum N₁ w₁ c = colSum N₂ w₂ c) →
  ∀ i, i ≤ w₁.length → N₁.out w₁ i = N₂.out w₂ i

/-- STATEMENT 2 (collision). For a token-blind network, two real tokens `s`, `o`, and a
radius `τ ≤ 1` with `1 ≤ τ (2a + 1)` and `1 ≤ τ (2b + 1)`, there are two networks in the
relative ball of radius `τ` with equal outputs at every position on the inputs
`s^a o^(b+1)` and `s^(a+1) o^b`. -/
def Collision : Prop :=
  ∀ (N : TNet) (ntok : ℕ) (T : List ℕ) (s o : ℕ), tokenBlind N ntok T = true →
    1 ≤ s → s ≤ ntok → 1 ≤ o → o ≤ ntok →
  ∀ (τ : ℚ) (a b : ℕ), τ ≤ 1 → 1 ≤ a → 1 ≤ b →
    1 ≤ τ * (2 * (a : ℚ) + 1) → 1 ≤ τ * (2 * (b : ℚ) + 1) →
    ∃ N₁ N₂ : TNet, netRel τ N N₁ ∧ netRel τ N N₂ ∧
      ∀ i, i ≤ a + b + 1 →
        N₁.out (List.replicate a s ++ List.replicate (b + 1) o) i =
        N₂.out (List.replicate (a + 1) s ++ List.replicate b o) i

/-- STATEMENT 3 (parity bound). A token-blind network with a counted and an uncounted
token: a relative ball that is correct for the parity task up to length `2a + 1` has
radius below `1 / (2a + 1)`. -/
def ParityBound : Prop :=
  ∀ (N : TNet) (T : List ℕ) (K : Task) (s o : ℕ), tokenBlind N K.V T = true → K.par < 2 →
    1 ≤ s → s ≤ K.V → K.inS s = true → 1 ≤ o → o ≤ K.V → K.inS o = false →
  ∀ (τ : ℚ) (a : ℕ), 0 ≤ τ → τ ≤ 1 → 1 ≤ a → K.OnBall N τ (2 * a + 1) →
    τ * (2 * (a : ℚ) + 1) < 1

/-- The sort-rank spec of rung 2: the output at position `i` is the `i`-th smallest token. -/
def IsRank (w : List ℕ) (i t : ℕ) : Prop :=
  w.countP (fun s => decide (s < t)) < i ∧ i ≤ w.countP (fun s => decide (s ≤ t))

def SortOnBall (ntok : ℕ) (N : TNet) (τ : ℚ) (L : ℕ) : Prop :=
  ∀ N', netRel τ N N' → ∀ w : List ℕ, w ≠ [] → (∀ t ∈ w, 1 ≤ t ∧ t ≤ ntok) → w.length ≤ L →
    ∀ i, 1 ≤ i → i ≤ w.length → ∃ t : ℕ, N'.out w i = (t : ℚ) ∧ IsRank w i t

/-- STATEMENT 4 (sort bound). A token-blind network over at least two tokens: a relative
ball that is correct for sort rank up to length `2a + 1` has radius below `1 / (2a + 1)`. -/
def SortBound : Prop :=
  ∀ (N : TNet) (ntok : ℕ) (T : List ℕ), tokenBlind N ntok T = true → 2 ≤ ntok →
  ∀ (τ : ℚ) (a : ℕ), 0 ≤ τ → τ ≤ 1 → 1 ≤ a → SortOnBall ntok N τ (2 * a + 1) →
    τ * (2 * (a : ℚ) + 1) < 1

end Lane4.TB
