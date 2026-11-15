import Lane4.Seq

namespace Lane4.Coll
open Lane4.Seq

def qRel (τ a b : ℚ) : Prop := |b - a| ≤ τ * |a|
def vRel (τ : ℚ) (a b : List ℚ) : Prop := List.Forall₂ (qRel τ) a b
def mRel (τ : ℚ) (A B : List (List ℚ)) : Prop := List.Forall₂ (vRel τ) A B
def hRel (τ : ℚ) (h g : Head) : Prop := mRel τ h.A g.A ∧ mRel τ h.V g.V ∧ h.mask = g.mask
def bRel (τ : ℚ) (B C : Block) : Prop :=
  List.Forall₂ (hRel τ) B.heads C.heads ∧ mRel τ B.W1 C.W1 ∧ vRel τ B.b1 C.b1 ∧
  mRel τ B.W2 C.W2 ∧ vRel τ B.b2 C.b2
/-- `N'` is inside the relative ball of radius `τ` around `N`. -/
def netRel (τ : ℚ) (N N' : TNet) : Prop :=
  mRel τ N.embed N'.embed ∧ List.Forall₂ (bRel τ) N.blocks N'.blocks ∧
  vRel τ N.outW N'.outW ∧ qRel τ N.outB N'.outB

/-- A counting-parity task: tokens are `1..V`, the tokens `t` with `inS t = true` are
counted, and the answer at the last position is positive exactly when the count has
parity `par`. This is the form of every rung-2 parity spec. -/
structure Task where
  V : ℕ
  inS : ℕ → Bool
  par : ℕ

def Task.Valid (T : Task) (w : List ℕ) : Prop := w ≠ [] ∧ ∀ t ∈ w, 1 ≤ t ∧ t ≤ T.V

def Task.Correct (T : Task) (N : TNet) (w : List ℕ) : Prop :=
  0 < N.out w w.length ↔ (w.countP T.inS) % 2 = T.par

/-- Every network in the relative ball of radius `τ` around `N` is correct on every valid
input of length at most `L`. -/
def Task.OnBall (T : Task) (N : TNet) (τ : ℚ) (L : ℕ) : Prop :=
  ∀ N', netRel τ N N' → ∀ w : List ℕ, T.Valid w → w.length ≤ L → T.Correct N' w

/-- THE CLASS. `N` has a count channel for `T`: there is ONE decoder `D` (a function of
the number of positions and of one rational) and, for every relative size `d` with
`|d| ≤ 1`, a network `N'` within relative distance `|d|` of `N` whose output at the last
position, on every valid input, is `D n ((1 + d) * k / n)`, where `k` is the count and
`n = length + 1` the number of positions. So along this one-parameter family the input
reaches the output only through `n` and the scaled average `(1 + d) * k / n`. -/
def Task.CountChannel (T : Task) (N : TNet) : Prop :=
  ∃ D : ℕ → ℚ → ℚ, ∀ d : ℚ, |d| ≤ 1 → ∃ N' : TNet, netRel |d| N N' ∧
    ∀ w : List ℕ, T.Valid w →
      N'.out w w.length =
        D (w.length + 1) ((1 + d) * ((w.countP T.inS : ℕ) : ℚ) / ((w.length : ℚ) + 1))

/-- STATEMENT 1 (the collision bound). If the wanted parity is 0 or 1 (`par < 2`; added by
amendment 1, 2026-11-14: without it the statement is false, since `par = 2` makes every
non-positive output correct), the task has a counted token and an uncounted token, the network has a count channel, and every network in the relative ball of radius
`τ ≤ 1` is correct up to length `L ≥ 2`, then `τ * (2 L - 1) < 1`. -/
def CollisionBound : Prop :=
  ∀ (T : Task) (s o : ℕ), T.par < 2 → 1 ≤ s → s ≤ T.V → T.inS s = true → 1 ≤ o → o ≤ T.V → T.inS o = false →
  ∀ N : TNet, T.CountChannel N →
  ∀ (τ : ℚ) (L : ℕ), 0 ≤ τ → τ ≤ 1 → 2 ≤ L → T.OnBall N τ L → τ * (2 * (L : ℚ) - 1) < 1

/-- Equivalent reading: at every radius `τ` with `1 / (2 L - 1) ≤ τ ≤ 1` some network in
the ball is wrong on some valid input of length at most `L`. -/
def CollisionBound' : Prop :=
  ∀ (T : Task) (s o : ℕ), T.par < 2 → 1 ≤ s → s ≤ T.V → T.inS s = true → 1 ≤ o → o ≤ T.V → T.inS o = false →
  ∀ N : TNet, T.CountChannel N →
  ∀ (τ : ℚ) (L : ℕ), τ ≤ 1 → 2 ≤ L → 1 ≤ τ * (2 * (L : ℚ) - 1) →
    ∃ N', netRel τ N N' ∧ ∃ w : List ℕ, T.Valid w ∧ w.length ≤ L ∧ ¬ T.Correct N' w

end Lane4.Coll


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


namespace Lane4.Inv
open Lane4.Seq Lane4.Coll Lane4.TB

/-- The invariant carried through the blocks: at every position below `n` the two state
families have length `d` and agree at every coordinate not in `T`, and for every
coordinate in `T` their column sums over the positions below `n` are equal. -/
def Agree (T : List ℕ) (d n : ℕ) (x y : ℕ → Vec) : Prop :=
  (∀ j, j < n → (x j).length = d ∧ (y j).length = d) ∧
  (∀ j, j < n → ∀ c, c ∉ T → (x j).getD c 0 = (y j).getD c 0) ∧
  (∀ c ∈ T, ((List.range n).map (fun j => (x j).getD c 0)).sum =
            ((List.range n).map (fun j => (y j).getD c 0)).sum)

/-- The head step: a token-blind head of the right shape gives the same output on the two
state families at every position below `n`. -/
def HeadStep : Prop :=
  ∀ (T : List ℕ) (d n : ℕ) (x y : ℕ → Vec) (h : Head), Agree T d n x y →
    headBlind T h = true → h.shapeOK d = true →
    ∀ i, i < n → h.attn n x i = h.attn n y i

end Lane4.Inv

namespace Lane4.HeadProof
open Lane4.Seq Lane4.Coll Lane4.TB Lane4.Inv

theorem getD_lt {α : Type} (l : List α) (d : α) (c : ℕ) (h : c < l.length) :
    l.getD c d = l[c] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_ge {α : Type} (l : List α) (d : α) (c : ℕ) (h : l.length ≤ c) :
    l.getD c d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem qdot_key (u : ℚ) (as b : Vec) :
    qdot (u :: as) b = u * b.getD 0 0 + qdot as b.tail := by
  cases b <;> simp [qdot]

theorem qdot_eq (a : Vec) : ∀ b : Vec,
    qdot a b = ((List.range a.length).map (fun c => a.getD c 0 * b.getD c 0)).sum := by
  induction a with
  | nil => intro b; simp [qdot]
  | cons u as ih =>
    intro b
    rw [qdot_key, ih b.tail, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.sum_cons, List.map_map]
    have e1 : u * b.getD 0 0 = (fun c => (u :: as).getD c 0 * b.getD c 0) 0 := by
      simp only [List.getD_cons_zero]
    have e2 : (List.map (fun c => as.getD c 0 * b.tail.getD c 0) (List.range as.length)).sum
        = (List.map ((fun c => (u :: as).getD c 0 * b.getD c 0) ∘ Nat.succ)
            (List.range as.length)).sum := by
      congr 1
      apply List.map_congr_left
      intro c _
      show as.getD c 0 * b.tail.getD c 0 = (u :: as).getD (c + 1) 0 * b.getD (c + 1) 0
      rw [List.getD_cons_succ]
      cases b <;> simp
    rw [e1, e2]

theorem qdot_congr (a b b' : Vec)
    (h : ∀ c, a.getD c 0 ≠ 0 → b.getD c 0 = b'.getD c 0) : qdot a b = qdot a b' := by
  rw [qdot_eq a b, qdot_eq a b']
  congr 1
  apply List.map_congr_left
  intro c _
  by_cases hc : a.getD c 0 = 0
  · simp only [hc, zero_mul]
  · simp only [h c hc]

theorem rowzero_getD (r : Vec) (hr : ∀ v ∈ r, v = 0) (c : ℕ) : r.getD c 0 = 0 := by
  by_cases hc : c < r.length
  · rw [getD_lt _ _ _ hc]; exact hr _ (List.getElem_mem hc)
  · rw [getD_ge _ _ _ (not_lt.mp hc)]

theorem qdot_zero_row (r : Vec) (hr : ∀ v ∈ r, v = 0) (b : Vec) : qdot r b = 0 := by
  rw [qdot_eq]
  simp only [rowzero_getD r hr, zero_mul]
  simp

theorem allzero_of {r : Vec} (h : r.all (fun v => v == 0) = true) : ∀ v ∈ r, v = 0 := by
  intro v hv
  have := List.all_eq_true.mp h v hv
  simpa using this

theorem zeroOn_get {T : List ℕ} {r : Vec} (h : zeroOn T r = true) : ∀ c ∈ T, r.getD c 0 = 0 := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

theorem matVec_getD (M : List Vec) (v : Vec) (c : ℕ) :
    (matVec M v).getD c 0 = qdot (M.getD c []) v := by
  by_cases hc : c < M.length
  · simp [matVec, List.getD_eq_getElem?_getD, hc]
  · have h2 : M.length ≤ c := not_lt.mp hc
    simp [matVec, List.getD_eq_getElem?_getD, List.getElem?_eq_none h2, qdot]

theorem swap_sum (l m : List ℕ) (f : ℕ → ℕ → ℚ) :
    (l.map (fun j => (m.map (fun c => f j c)).sum)).sum
      = (m.map (fun c => (l.map (fun j => f j c)).sum)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [← List.sum_map_add]

theorem sumq (row : Vec) (n : ℕ) (x : ℕ → Vec) :
    ((List.range n).map (fun j => qdot row (x j))).sum
      = ((List.range row.length).map
          (fun c => row.getD c 0 * ((List.range n).map (fun j => (x j).getD c 0)).sum)).sum := by
  have h1 : ∀ j, qdot row (x j)
      = ((List.range row.length).map (fun c => row.getD c 0 * (x j).getD c 0)).sum :=
    fun j => qdot_eq _ _
  simp only [h1]
  refine (swap_sum (List.range n) (List.range row.length)
    (fun j c => row.getD c 0 * (x j).getD c 0)).trans ?_
  congr 1
  apply List.map_congr_left
  intro c _
  rw [List.sum_map_mul_left]

theorem sumq_agree (T : List ℕ) (d n : ℕ) (x y : ℕ → Vec) (hA : Agree T d n x y) (row : Vec) :
    ((List.range n).map (fun j => qdot row (x j))).sum
      = ((List.range n).map (fun j => qdot row (y j))).sum := by
  rw [sumq, sumq]
  congr 1
  apply List.map_congr_left
  intro c _
  congr 1
  by_cases hc : c ∈ T
  · exact hA.2.2 c hc
  · apply congrArg
    apply List.map_congr_left
    intro j hj
    exact hA.2.1 j (List.mem_range.mp hj) c hc

theorem cand_lt (m : Mask) (n i j : ℕ) (hi : i < n) (hj : j ∈ cand m n i) : j < n := by
  cases m <;> simp [cand] at hj <;> omega

theorem zeroOn_nil (T : List ℕ) : zeroOn T [] = true := by
  simp [zeroOn]

theorem zeroOn_getD' {T : List ℕ} {A : List Vec} (h : ∀ r ∈ A, zeroOn T r = true) (c : ℕ) :
    zeroOn T (A.getD c []) = true := by
  by_cases hc : c < A.length
  · rw [getD_lt _ _ _ hc]; exact h _ (List.getElem_mem hc)
  · rw [getD_ge _ _ _ (not_lt.mp hc)]; exact zeroOn_nil T

theorem avg_agree (S : List ℕ) (f g : ℕ → ℚ) (h : ∀ j ∈ S, f j = g j) : avg S f = avg S g := by
  unfold avg
  have : (S.map f) = (S.map g) := List.map_congr_left h
  rw [this]

theorem head_uniform (T : List ℕ) (d n : ℕ) (x y : ℕ → Vec) (h : Head) (hA : Agree T d n x y)
    (hz : isZero h.A = true) (hm : h.mask = Mask.all) (i : ℕ) (hi : i < n) :
    h.attn n x i = h.attn n y i := by
  have hrow : ∀ c, ∀ v ∈ h.A.getD c [], v = 0 := by
    intro c
    by_cases hc : c < h.A.length
    · rw [getD_lt _ _ _ hc]
      have := List.all_eq_true.mp hz _ (List.getElem_mem hc)
      exact allzero_of this
    · rw [getD_ge _ _ _ (not_lt.mp hc)]
      intro v hv; simp at hv
  have hscore : ∀ a b : Vec, h.score a b = 0 := by
    intro a b
    unfold Head.score
    rw [qdot_eq]
    have : ∀ c, (matVec h.A b).getD c 0 = 0 := by
      intro c
      rw [matVec_getD]
      exact qdot_zero_row _ (hrow c) _
    simp only [this, mul_zero]
    simp
  have hsel : ∀ z : ℕ → Vec, h.sel n z i = List.range n := by
    intro z
    have := sel_all h n z i (by intro k _ l _; rw [hscore, hscore])
    rw [this, hm]
    simp [cand]
  simp only [Head.attn, hsel]
  apply List.map_congr_left
  intro row _
  unfold avg
  rw [sumq_agree T d n x y hA row]

theorem head_blind (T : List ℕ) (d n : ℕ) (x y : ℕ → Vec) (h : Head) (hA : Agree T d n x y)
    (hs : blindScore T h.A = true) (hv : h.V.all (zeroOn T) = true) (i : ℕ) (hi : i < n) :
    h.attn n x i = h.attn n y i := by
  have hs' := hs
  unfold blindScore at hs'
  rw [Bool.and_eq_true] at hs'
  obtain ⟨hs1, hs2⟩ := hs'
  have hTrow : ∀ p ∈ T, ∀ v ∈ h.A.getD p [], v = 0 := by
    intro p hp
    exact allzero_of (List.all_eq_true.mp hs1 p hp)
  have hAz : ∀ r ∈ h.A, zeroOn T r = true := fun r hr => List.all_eq_true.mp hs2 r hr
  have hVz : ∀ r ∈ h.V, zeroOn T r = true := fun r hr => List.all_eq_true.mp hv r hr
  have hqa : ∀ r, zeroOn T r = true → ∀ j, j < n → qdot r (x j) = qdot r (y j) := by
    intro r hr j hj
    apply qdot_congr
    intro c hc
    by_cases hcT : c ∈ T
    · exact absurd (zeroOn_get hr c hcT) hc
    · exact hA.2.1 j hj c hcT
  have hsc : ∀ a b, a < n → b < n → h.score (x a) (x b) = h.score (y a) (y b) := by
    intro a b ha hb
    unfold Head.score
    rw [qdot_eq (x a) (matVec h.A (x b)), qdot_eq (y a) (matVec h.A (y b)),
      (hA.1 a ha).1, (hA.1 a ha).2]
    apply congrArg
    apply List.map_congr_left
    intro c _
    by_cases hc : c ∈ T
    · rw [matVec_getD, matVec_getD, qdot_zero_row _ (hTrow c hc), qdot_zero_row _ (hTrow c hc)]
      simp
    · rw [matVec_getD, matVec_getD, hqa _ (zeroOn_getD' hAz c) b hb, hA.2.1 a ha c hc]
  have hsel : h.sel n x i = h.sel n y i := by
    unfold Head.sel
    apply List.filter_congr
    intro j hj
    have hjn := cand_lt _ _ _ _ hi hj
    apply decide_eq_decide.mpr
    constructor
    · intro hh k hk
      have := hh k hk
      rwa [hsc i k hi (cand_lt _ _ _ _ hi hk), hsc i j hi hjn] at this
    · intro hh k hk
      have := hh k hk
      rwa [← hsc i k hi (cand_lt _ _ _ _ hi hk), ← hsc i j hi hjn] at this
  simp only [Head.attn]
  rw [hsel]
  apply List.map_congr_left
  intro row hrow
  apply avg_agree
  intro j hj
  have hjc := ((mem_sel h n y i j).1 hj).1
  exact hqa row (hVz row hrow) j (cand_lt _ _ _ _ hi hjc)

theorem head_step : HeadStep := by
  intro T d n x y h hA hb _ i hi
  unfold headBlind at hb
  rw [Bool.or_eq_true] at hb
  rcases hb with hb | hb
  · rw [Bool.and_eq_true] at hb
    exact head_uniform T d n x y h hA hb.1 (of_decide_eq_true hb.2) i hi
  · rw [Bool.and_eq_true] at hb
    exact head_blind T d n x y h hA hb.1 hb.2 i hi

end Lane4.HeadProof


namespace Lane4.Inv
open Lane4.Seq Lane4.Coll Lane4.TB

/-- The block step: a token-blind block of the right shape preserves the invariant. -/
def BlockStep : Prop :=
  ∀ (T : List ℕ) (d n : ℕ) (x y : ℕ → Vec) (B : Block), (∀ c ∈ T, c < d) → Agree T d n x y →
    blockBlind T B = true → B.shapeOK d = true → Agree T d n (B.apply n x) (B.apply n y)

end Lane4.Inv

namespace Lane4.BlockProof
open Lane4.Seq Lane4.Coll Lane4.TB Lane4.Inv

theorem vadd_length (a b : Vec) : (vadd a b).length = min a.length b.length := by
  simp [vadd]

theorem vadd_getD (a b : Vec) (d c : ℕ) (ha : a.length = d) (hb : b.length = d) (hc : c < d) :
    (vadd a b).getD c 0 = a.getD c 0 + b.getD c 0 := by
  have h1 : c < a.length := by omega
  have h2 : c < b.length := by omega
  have h3 : c < (vadd a b).length := by
    have := vadd_length a b
    omega
  rw [Lane4.HeadProof.getD_lt _ _ _ h3, Lane4.HeadProof.getD_lt _ _ _ h1,
    Lane4.HeadProof.getD_lt _ _ _ h2]
  simp [vadd]

theorem fold_lemma (d n : ℕ) (x y : ℕ → Vec) (i : ℕ) :
    ∀ (hs : List Head), (∀ h ∈ hs, h.attn n x i = h.attn n y i ∧ (h.attn n x i).length = d) →
    ∀ a b : Vec, a.length = d → b.length = d →
      (hs.foldl (fun acc h => vadd acc (h.attn n x i)) a).length = d ∧
      (hs.foldl (fun acc h => vadd acc (h.attn n y i)) b).length = d ∧
      ∀ c, c < d → (hs.foldl (fun acc h => vadd acc (h.attn n x i)) a).getD c 0 + b.getD c 0
        = (hs.foldl (fun acc h => vadd acc (h.attn n y i)) b).getD c 0 + a.getD c 0 := by
  intro hs
  induction hs with
  | nil =>
    intro _ a b ha hb
    simp only [List.foldl_nil]
    exact ⟨ha, hb, fun c _ => add_comm _ _⟩
  | cons h t ih =>
    intro hh a b ha hb
    obtain ⟨he, hl⟩ := hh h (by simp)
    rw [he] at hl
    have hlen : ∀ u : Vec, u.length = d → (vadd u (h.attn n y i)).length = d := by
      intro u hu
      have := vadd_length u (h.attn n y i)
      omega
    have key := ih (fun h' hh' => hh h' (List.mem_cons_of_mem _ hh'))
      (vadd a (h.attn n y i)) (vadd b (h.attn n y i)) (hlen a ha) (hlen b hb)
    simp only [List.foldl_cons]
    rw [he]
    obtain ⟨l1, l2, l3⟩ := key
    refine ⟨l1, l2, fun c hc => ?_⟩
    have h4 := l3 c hc
    rw [vadd_getD _ _ d c ha hl hc, vadd_getD _ _ d c hb hl hc] at h4
    linarith

theorem affine_congr : ∀ (W : List Vec) (b u v : Vec), (∀ r ∈ W, qdot r u = qdot r v) →
    affine W b u = affine W b v := by
  intro W
  induction W with
  | nil => intro b u v _; simp [affine]
  | cons r t ih =>
    intro b u v h
    cases b with
    | nil => simp [affine]
    | cons c bs =>
      have key := ih bs u v (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
      unfold affine at key ⊢
      rw [List.zipWith_cons_cons, List.zipWith_cons_cons, h r (by simp), key]

theorem fin_lemma (d : ℕ) (xj yj Yx Yy M : Vec) (hx : Yx.length = d) (hy : Yy.length = d)
    (hM : M.length = d) (T : List ℕ) (hoff : ∀ c, c ∉ T → Yx.getD c 0 = Yy.getD c 0)
    (hl3 : ∀ c, c < d → Yx.getD c 0 + yj.getD c 0 = Yy.getD c 0 + xj.getD c 0) :
    (vadd Yx M).length = d ∧ (vadd Yy M).length = d ∧
    (∀ c, c ∉ T → (vadd Yx M).getD c 0 = (vadd Yy M).getD c 0) ∧
    ∀ c, c < d → (vadd Yx M).getD c 0 + yj.getD c 0
      = (vadd Yy M).getD c 0 + xj.getD c 0 := by
  have e1 := vadd_length Yx M
  have e2 := vadd_length Yy M
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro c hc
    by_cases hcd : c < d
    · rw [vadd_getD _ _ d c hx hM hcd, vadd_getD _ _ d c hy hM hcd, hoff c hc]
    · have h1 : (vadd Yx M).length ≤ c := by omega
      have h2 : (vadd Yy M).length ≤ c := by omega
      rw [Lane4.HeadProof.getD_ge _ _ _ h1, Lane4.HeadProof.getD_ge _ _ _ h2]
  · intro c hc
    rw [vadd_getD _ _ d c hx hM hc, vadd_getD _ _ d c hy hM hc]
    have := hl3 c hc
    linarith

theorem pos_lemma (T : List ℕ) (d n : ℕ) (x y : ℕ → Vec) (B : Block) (hA : Agree T d n x y)
    (hbb : blockBlind T B = true) (hsh : B.shapeOK d = true) (j : ℕ) (hj : j < n) :
    (B.apply n x j).length = d ∧ (B.apply n y j).length = d ∧
    (∀ c, c ∉ T → (B.apply n x j).getD c 0 = (B.apply n y j).getD c 0) ∧
    ∀ c, c < d → (B.apply n x j).getD c 0 + (y j).getD c 0
        = (B.apply n y j).getD c 0 + (x j).getD c 0 := by
  have hsh' := hsh
  simp only [Block.shapeOK, rowsOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at hsh'
  obtain ⟨⟨⟨⟨⟨_, hH⟩, _⟩, ⟨_, _⟩⟩, ⟨hW2l, _⟩⟩, hb2⟩ := hsh'
  have hVlen : ∀ h ∈ B.heads, h.V.length = d := by
    intro h hh
    have := hH h hh
    simp only [Head.shapeOK, rowsOK, Bool.and_eq_true, beq_iff_eq] at this
    exact this.2.1
  have hbb' := hbb
  simp only [blockBlind, Bool.and_eq_true, List.all_eq_true] at hbb'
  obtain ⟨hHb, hW1z⟩ := hbb'
  have hatt : ∀ h ∈ B.heads, h.attn n x j = h.attn n y j ∧ (h.attn n x j).length = d := by
    intro h hh
    refine ⟨Lane4.HeadProof.head_step T d n x y h hA (hHb h hh) (hH h hh) j hj, ?_⟩
    simp [Head.attn, hVlen h hh]
  obtain ⟨hl1, hl2, hl3⟩ := fold_lemma d n x y j B.heads hatt (x j) (y j)
    (hA.1 j hj).1 (hA.1 j hj).2
  have hap : ∀ z : ℕ → Vec, B.apply n z j =
      vadd (B.heads.foldl (fun acc h => vadd acc (h.attn n z j)) (z j))
        (affine B.W2 B.b2 ((affine B.W1 B.b1
          (B.heads.foldl (fun acc h => vadd acc (h.attn n z j)) (z j))).map
            (fun v => max v 0))) := fun z => rfl
  rw [hap x, hap y]
  generalize B.heads.foldl (fun acc h => vadd acc (h.attn n x j)) (x j) = Yx at hl1 hl3 ⊢
  generalize B.heads.foldl (fun acc h => vadd acc (h.attn n y j)) (y j) = Yy at hl2 hl3 ⊢
  have hoff : ∀ c, c ∉ T → Yx.getD c 0 = Yy.getD c 0 := by
    intro c hc
    by_cases hcd : c < d
    · have h1 := hl3 c hcd
      have h2 := hA.2.1 j hj c hc
      linarith
    · rw [Lane4.HeadProof.getD_ge _ _ _ (by omega), Lane4.HeadProof.getD_ge _ _ _ (by omega)]
  have hq : ∀ r ∈ B.W1, qdot r Yx = qdot r Yy := by
    intro r hr
    apply Lane4.HeadProof.qdot_congr
    intro c hc
    by_cases hcT : c ∈ T
    · exact absurd (Lane4.HeadProof.zeroOn_get (hW1z r hr) c hcT) hc
    · exact hoff c hcT
  rw [affine_congr B.W1 B.b1 Yx Yy hq]
  have hMl : ∀ u : Vec, (affine B.W2 B.b2 u).length = d := by
    intro u
    simp [affine, hW2l, hb2]
  exact fin_lemma d (x j) (y j) Yx Yy _ hl1 hl2 (hMl _) T hoff hl3

theorem block_step : BlockStep := by
  intro T d n x y B hT hA hbb hsh
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have := pos_lemma T d n x y B hA hbb hsh j hj
    exact ⟨this.1, this.2.1⟩
  · intro j hj c hc
    exact (pos_lemma T d n x y B hA hbb hsh j hj).2.2.1 c hc
  · intro c hc
    have hcd := hT c hc
    have hpt : ∀ j ∈ List.range n,
        (B.apply n x j).getD c 0 + (y j).getD c 0
          = (B.apply n y j).getD c 0 + (x j).getD c 0 :=
      fun j hj => (pos_lemma T d n x y B hA hbb hsh j (List.mem_range.mp hj)).2.2.2 c hcd
    have e1 : ((List.range n).map (fun j => (B.apply n x j).getD c 0 + (y j).getD c 0)).sum
        = ((List.range n).map (fun j => (B.apply n y j).getD c 0 + (x j).getD c 0)).sum := by
      congr 1
      exact List.map_congr_left hpt
    rw [List.sum_map_add, List.sum_map_add] at e1
    have := hA.2.2 c hc
    linarith

end Lane4.BlockProof


namespace Lane4.NetProof
open Lane4.Seq Lane4.Coll Lane4.TB Lane4.Inv

theorem gd_app_left (l l' : Vec) (c : ℕ) (h : c < l.length) :
    (l ++ l').getD c 0 = l.getD c 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gd_app_right (l l' : Vec) (c : ℕ) (h : l.length ≤ c) :
    (l ++ l').getD c 0 = l'.getD (c - l.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem pos_len (j n : ℕ) : (pos j n).length = 8 := by simp [pos]

theorem run_agree (T : List ℕ) (d n : ℕ) (hT : ∀ c ∈ T, c < d) :
    ∀ (bs : List Block), (∀ B ∈ bs, blockBlind T B = true ∧ B.shapeOK d = true) →
    ∀ x y : ℕ → Vec, Agree T d n x y →
    Agree T d n (bs.foldl (fun x B => B.apply n x) x) (bs.foldl (fun x B => B.apply n x) y) := by
  intro bs
  induction bs with
  | nil => intro _ x y hA; simpa using hA
  | cons B t ih =>
    intro h x y hA
    simp only [List.foldl_cons]
    exact ih (fun B' hB' => h B' (List.mem_cons_of_mem _ hB')) _ _
      (Lane4.BlockProof.block_step T d n x y B hT hA (h B (by simp)).1 (h B (by simp)).2)

theorem invariance : Invariance := by
  intro N N₁ N₂ ntok T hTB h1 h2 w₁ w₂ hw₁ hw₂ hlen hcol i hi
  have hsh0 : N.shapeOK ntok = true := by
    have h := hTB
    simp only [tokenBlind, Bool.and_eq_true] at h
    exact h.1.1.1.1
  obtain ⟨e, rest, hE⟩ : ∃ e rest, N.embed = e :: rest := by
    cases h : N.embed with
    | nil => simp [TNet.shapeOK, h] at hsh0
    | cons e r => exact ⟨e, r, rfl⟩
  have hde : N.embed.getD 0 [] = e := by rw [hE]; simp
  have hTB' := hTB
  simp only [tokenBlind, Bool.and_eq_true] at hTB'
  obtain ⟨⟨⟨⟨_, hTlt⟩, hoff⟩, hbl⟩, hz⟩ := hTB'
  rw [hde] at hoff
  have hTlt' : ∀ c ∈ T, c < e.length := by
    intro c hc
    have := List.all_eq_true.mp hTlt c hc
    have h3 : c < (N.embed.getD 0 []).length := of_decide_eq_true this
    rwa [hde] at h3
  have hsh := hsh0
  simp only [TNet.shapeOK, hE, rowsOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at hsh
  obtain ⟨⟨⟨⟨_, hEl, hErows⟩, _⟩, hBsh⟩, _⟩ := hsh
  have hElen : N.embed.length = ntok + 1 := by
    rw [hE]; simpa using hEl
  have hrowN : ∀ t, t ≤ ntok → (N.embed.getD t []).length = e.length := by
    intro t ht
    have h1' : t < N.embed.length := by omega
    rw [Lane4.HeadProof.getD_lt _ _ _ h1']
    exact hErows _ (by rw [← hE]; exact List.getElem_mem h1')
  have htok : ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ ntok) → ∀ j, tokAt w j ≤ ntok := by
    intro w hw j
    rcases tokAt_zero_or_mem w j with h0 | hm
    · omega
    · exact (hw _ hm).2
  have hreal : ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ ntok) → ∀ k, k < w.length →
      1 ≤ tokAt w (k + 1) ∧ tokAt w (k + 1) ≤ ntok := by
    intro w hw k hk
    rw [tokAt_succ w k hk]
    exact hw _ (List.getElem_mem hk)
  have hrl : ∀ (M : TNet), SameOffT N M T → ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ ntok) →
      ∀ j, (M.embed.getD (tokAt w j) []).length = e.length := by
    intro M hM w hw j
    rw [hM.2.2.2.2.1, hrowN _ (htok w hw j)]
  have hsame : ∀ c, c < e.length → c ∉ T → ∀ t, 1 ≤ t → t ≤ ntok →
      (N.embed.getD t []).getD c 0 = (N.embed.getD 1 []).getD c 0 := by
    intro c hc hcT t ht1 ht2
    have this := List.all_eq_true.mp hoff c (List.mem_range.mpr hc)
    have hcT' : T.contains c = false := by
      cases h : T.contains c
      · rfl
      · exfalso
        apply hcT
        first
          | simpa using h
          | exact List.elem_iff.mp h
          | exact List.contains_iff.mp h
    simp only [hcT', Bool.false_or] at this
    have h3 := List.all_eq_true.mp this (t - 1) (List.mem_range.mpr (by omega))
    have e3 : t - 1 + 1 = t := by omega
    rw [e3] at h3
    first
      | exact beq_iff_eq.mp h3
      | simpa using h3
  have hx : ∀ j, N₁.init w₁ j = N₁.embed.getD (tokAt w₁ j) [] ++ pos j (w₁.length + 1) :=
    fun j => rfl
  have hy : ∀ j, N₂.init w₂ j = N₂.embed.getD (tokAt w₂ j) [] ++ pos j (w₁.length + 1) := by
    intro j
    simp only [TNet.init, hlen]
  have hA0 : Agree T (e.length + 8) (w₁.length + 1) (N₁.init w₁) (N₂.init w₂) := by
    refine ⟨?_, ?_, ?_⟩
    · intro j _
      rw [hx j, hy j, List.length_append, List.length_append, hrl N₁ h1 w₁ hw₁ j,
        hrl N₂ h2 w₂ hw₂ j, pos_len]
      exact ⟨rfl, rfl⟩
    · intro j hj c hc
      rw [hx j, hy j]
      by_cases hcl : c < e.length
      · rw [gd_app_left _ _ _ (by rw [hrl N₁ h1 w₁ hw₁ j]; exact hcl),
          gd_app_left _ _ _ (by rw [hrl N₂ h2 w₂ hw₂ j]; exact hcl),
          h1.2.2.2.2.2 _ c hc, h2.2.2.2.2.2 _ c hc]
        rcases j with _ | k
        · rw [tokAt_zero w₁, tokAt_zero w₂]
        · have hk : k < w₁.length := by omega
          have hk2 : k < w₂.length := by omega
          have a1 := hreal w₁ hw₁ k hk
          have a2 := hreal w₂ hw₂ k hk2
          rw [hsame c hcl hc _ a1.1 a1.2, hsame c hcl hc _ a2.1 a2.2]
      · rw [gd_app_right _ _ _ (by rw [hrl N₁ h1 w₁ hw₁ j]; omega),
          gd_app_right _ _ _ (by rw [hrl N₂ h2 w₂ hw₂ j]; omega),
          hrl N₁ h1 w₁ hw₁ j, hrl N₂ h2 w₂ hw₂ j]
    · intro c hc
      have hcl := hTlt' c hc
      have e1 : ((List.range (w₁.length + 1)).map (fun j => (N₁.init w₁ j).getD c 0)).sum
          = colSum N₁ w₁ c := by
        unfold colSum
        congr 1
        apply List.map_congr_left
        intro j _
        rw [hx j, gd_app_left _ _ _ (by rw [hrl N₁ h1 w₁ hw₁ j]; exact hcl)]
      have e2 : ((List.range (w₁.length + 1)).map (fun j => (N₂.init w₂ j).getD c 0)).sum
          = colSum N₂ w₂ c := by
        unfold colSum
        rw [← hlen]
        congr 1
        apply List.map_congr_left
        intro j _
        rw [hy j, gd_app_left _ _ _ (by rw [hrl N₂ h2 w₂ hw₂ j]; exact hcl)]
      rw [e1, e2]
      exact hcol c hc
  have hr1 : N₁.run w₁ = N.blocks.foldl (fun x B => B.apply (w₁.length + 1) x) (N₁.init w₁) := by
    simp only [TNet.run, h1.1]
  have hr2 : N₂.run w₂ = N.blocks.foldl (fun x B => B.apply (w₁.length + 1) x) (N₂.init w₂) := by
    simp only [TNet.run, h2.1, hlen]
  have hblk : ∀ B ∈ N.blocks, blockBlind T B = true ∧ B.shapeOK (e.length + 8) = true :=
    fun B hB => ⟨List.all_eq_true.mp hbl B hB, hBsh B hB⟩
  have hfin := run_agree T (e.length + 8) (w₁.length + 1)
    (fun c hc => by have := hTlt' c hc; omega) N.blocks hblk _ _ hA0
  unfold TNet.out
  rw [h1.2.1, h2.2.1, h1.2.2.1, h2.2.2.1, hr1, hr2]
  congr 1
  apply Lane4.HeadProof.qdot_congr
  intro c hc
  have hcT : c ∉ T := by
    intro hcT
    exact hc (Lane4.HeadProof.zeroOn_get hz c hcT)
  exact hfin.2.1 i (by omega) c hcT

end Lane4.NetProof


set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace Lane4.CollOfInv
open Lane4.Seq Lane4.Coll Lane4.TB

def scR (T : List ℕ) (f : ℚ) : ℕ → List ℚ → List ℚ
  | _, [] => []
  | c, v :: vs => (if c ∈ T then v * f else v) :: scR T f (c + 1) vs

theorem scR_length (T : List ℕ) (f : ℚ) (l : List ℚ) :
    ∀ c, (scR T f c l).length = l.length := by
  induction l with
  | nil => intro c; simp [scR]
  | cons v vs ih => intro c; simp [scR, ih]

theorem scR_getD (T : List ℕ) (f : ℚ) (l : List ℚ) :
    ∀ (c k : ℕ), (scR T f c l).getD k 0 = if c + k ∈ T then l.getD k 0 * f else l.getD k 0 := by
  induction l with
  | nil => intro c k; by_cases h : c + k ∈ T <;> simp [scR, h]
  | cons v vs ih =>
    intro c k
    cases k with
    | zero => by_cases h : c ∈ T <;> simp [scR, h]
    | succ k =>
      have e : c + (k + 1) = (c + 1) + k := by omega
      rw [e]
      simp only [scR, List.getD_cons_succ]
      exact ih (c + 1) k

theorem fa2_refl {α : Type} {R : α → α → Prop} (h : ∀ x, R x x) :
    ∀ l : List α, List.Forall₂ R l l := by
  intro l
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a t ih => exact List.Forall₂.cons (h a) ih

theorem qRel_refl (τ : ℚ) (h0 : 0 ≤ τ) (a : ℚ) : qRel τ a a := by
  unfold qRel
  rw [sub_self, abs_zero]
  exact mul_nonneg h0 (abs_nonneg a)

theorem vRel_refl (τ : ℚ) (h0 : 0 ≤ τ) (l : List ℚ) : vRel τ l l :=
  fa2_refl (qRel_refl τ h0) l

theorem mRel_refl (τ : ℚ) (h0 : 0 ≤ τ) (l : List (List ℚ)) : mRel τ l l :=
  fa2_refl (vRel_refl τ h0) l

theorem netRel_self (τ : ℚ) (h0 : 0 ≤ τ) (N : TNet) : netRel τ N N :=
  ⟨mRel_refl τ h0 _,
   fa2_refl (fun B => ⟨fa2_refl (fun h => ⟨mRel_refl τ h0 _, mRel_refl τ h0 _, rfl⟩) _,
     mRel_refl τ h0 _, vRel_refl τ h0 _, mRel_refl τ h0 _, vRel_refl τ h0 _⟩) _,
   vRel_refl τ h0 _, qRel_refl τ h0 _⟩

theorem scR_rel (T : List ℕ) (f τ : ℚ) (hf : |f - 1| ≤ τ) :
    ∀ (l : List ℚ) (c : ℕ), vRel τ l (scR T f c l) := by
  have h0 : 0 ≤ τ := le_trans (abs_nonneg _) hf
  intro l
  induction l with
  | nil => intro c; unfold vRel; simp [scR]
  | cons v vs ih =>
    intro c
    unfold vRel at ih ⊢
    simp only [scR]
    refine List.Forall₂.cons ?_ (ih (c + 1))
    unfold qRel
    split_ifs with h
    · have e : v * f - v = v * (f - 1) := by ring
      rw [e, abs_mul]
      nlinarith [abs_nonneg v]
    · rw [sub_self, abs_zero]
      exact mul_nonneg h0 (abs_nonneg v)

def gRow (T : List ℕ) (s o : ℕ) (fs fo : ℚ) (t : ℕ) (row : List ℚ) : List ℚ :=
  if t = s then scR T fs 0 row else if t = o then scR T fo 0 row else row

def scE (T : List ℕ) (s o : ℕ) (fs fo : ℚ) : ℕ → List (List ℚ) → List (List ℚ)
  | _, [] => []
  | t, r :: rs => gRow T s o fs fo t r :: scE T s o fs fo (t + 1) rs

theorem scE_length (T : List ℕ) (s o : ℕ) (fs fo : ℚ) (t : ℕ) (l : List (List ℚ)) :
    (scE T s o fs fo t l).length = l.length := by
  induction l generalizing t with
  | nil => simp [scE]
  | cons r rs ih => simp [scE, ih]

theorem scE_getD (T : List ℕ) (s o : ℕ) (fs fo : ℚ) (l : List (List ℚ)) :
    ∀ (t k : ℕ), (scE T s o fs fo t l).getD k [] = gRow T s o fs fo (t + k) (l.getD k []) := by
  induction l with
  | nil =>
    intro t k
    by_cases h1 : t + k = s <;> by_cases h2 : t + k = o <;>
      simp [scE, gRow, h1, h2, scR]
  | cons r rs ih =>
    intro t k
    cases k with
    | zero => simp [scE]
    | succ k =>
      have e : t + (k + 1) = (t + 1) + k := by omega
      rw [e]
      simp only [scE, List.getD_cons_succ]
      exact ih (t + 1) k

theorem scE_rel (T : List ℕ) (s o : ℕ) (fs fo τ : ℚ) (hfs : |fs - 1| ≤ τ) (hfo : |fo - 1| ≤ τ) :
    ∀ (l : List (List ℚ)) (t : ℕ), mRel τ l (scE T s o fs fo t l) := by
  have h0 : 0 ≤ τ := le_trans (abs_nonneg _) hfs
  intro l
  induction l with
  | nil => intro t; unfold mRel; simp [scE]
  | cons r rs ih =>
    intro t
    unfold mRel at ih ⊢
    simp only [scE]
    refine List.Forall₂.cons ?_ (ih (t + 1))
    unfold gRow
    split_ifs
    · exact scR_rel T fs τ hfs r 0
    · exact scR_rel T fo τ hfo r 0
    · exact vRel_refl τ h0 r

def scale (N : TNet) (T : List ℕ) (s o : ℕ) (fs fo : ℚ) : TNet :=
  ⟨scE T s o fs fo 0 N.embed, N.blocks, N.outW, N.outB⟩

theorem scale_netRel (τ : ℚ) (N : TNet) (T : List ℕ) (s o : ℕ) (fs fo : ℚ)
    (hfs : |fs - 1| ≤ τ) (hfo : |fo - 1| ≤ τ) : netRel τ N (scale N T s o fs fo) := by
  have h0 : 0 ≤ τ := le_trans (abs_nonneg _) hfs
  obtain ⟨_, h2, h3, h4⟩ := netRel_self τ h0 N
  exact ⟨scE_rel T s o fs fo τ hfs hfo N.embed 0, h2, h3, h4⟩

theorem sameOff (N : TNet) (T : List ℕ) (s o : ℕ) (fs fo : ℚ) :
    SameOffT N (scale N T s o fs fo) T := by
  refine ⟨rfl, rfl, rfl, scE_length T s o fs fo 0 N.embed, ?_, ?_⟩
  · intro t
    show ((scE T s o fs fo 0 N.embed).getD t []).length = _
    rw [scE_getD, zero_add]
    unfold gRow
    split_ifs <;> simp [scR_length]
  · intro t c hc
    show ((scE T s o fs fo 0 N.embed).getD t []).getD c 0 = _
    rw [scE_getD, zero_add]
    unfold gRow
    split_ifs <;> first | rfl | rw [scR_getD, zero_add, if_neg hc]

theorem ent (N : TNet) (T : List ℕ) (s o : ℕ) (fs fo : ℚ) (t c : ℕ) :
    ((scale N T s o fs fo).embed.getD t []).getD c 0 =
      if c ∈ T then (N.embed.getD t []).getD c 0 *
        (if t = s then fs else if t = o then fo else 1)
      else (N.embed.getD t []).getD c 0 := by
  show ((scE T s o fs fo 0 N.embed).getD t []).getD c 0 = _
  rw [scE_getD, zero_add]
  unfold gRow
  by_cases h1 : t = s
  · rw [if_pos h1, scR_getD, zero_add, if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : t = o
    · rw [if_pos h2, scR_getD, zero_add, if_neg h1, if_pos h2]
    · rw [if_neg h2, if_neg h1, if_neg h2]
      by_cases hc : c ∈ T <;> simp [hc]

theorem sum_getD (g : ℕ → ℚ) (w : List ℕ) :
    ((List.range w.length).map (fun j => g (w.getD j 0))).sum = (w.map g).sum := by
  induction w with
  | nil => simp
  | cons x t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map,
      List.map_cons, List.sum_cons]
    have h : (fun j => g ((x :: t).getD j 0)) ∘ Nat.succ = fun j => g (t.getD j 0) := by
      funext j
      simp only [Function.comp, List.getD_cons_succ]
    rw [h, ih]
    rfl

theorem colsum_gen (g : ℕ → ℚ) (w : List ℕ) :
    ((List.range (w.length + 1)).map (fun j => g (tokAt w j))).sum = g 0 + (w.map g).sum := by
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, tokAt_zero, List.map_map]
  congr 1
  have h : (fun j => g (tokAt w j)) ∘ Nat.succ = fun j => g (w.getD j 0) := by
    funext j
    simp [Function.comp, tokAt]
  rw [h]
  exact sum_getD g w

theorem colSum_rep (M : TNet) (s o a k c : ℕ) :
    colSum M (List.replicate a s ++ List.replicate k o) c =
      (M.embed.getD 0 []).getD c 0 + (a : ℚ) * (M.embed.getD s []).getD c 0
        + (k : ℚ) * (M.embed.getD o []).getD c 0 := by
  unfold colSum
  refine (colsum_gen (fun t => (M.embed.getD t []).getD c 0) _).trans ?_
  simp only [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate,
    nsmul_eq_mul]
  ring

theorem collision_of_invariance : Invariance → Collision := by
  intro hI N ntok T s o htb hs1 hs2 ho1 ho2 τ a b hτ1 ha hb hA hB
  have ha' : (1 : ℚ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℚ) ≤ b := by exact_mod_cast hb
  have h0 : 0 ≤ τ := by nlinarith
  by_cases hso : s = o
  · have e : List.replicate a s ++ List.replicate (b + 1) o
        = List.replicate (a + 1) s ++ List.replicate b o := by
      rw [← hso, ← List.replicate_add, ← List.replicate_add]
      congr 1 <;> omega
    exact ⟨N, N, netRel_self τ h0 N, netRel_self τ h0 N, fun i _ => by rw [e]⟩
  · have hapos : (0 : ℚ) < a := by linarith
    have hbpos : (0 : ℚ) < b := by linarith
    have key : ∃ d1s d2s d1o d2o : ℚ, |d1s| ≤ τ ∧ |d2s| ≤ τ ∧ |d1o| ≤ τ ∧ |d2o| ≤ τ ∧
        (a : ℚ) * (1 + d1s) = ((a : ℚ) + 1) * (1 + d2s) ∧
        ((b : ℚ) + 1) * (1 + d1o) = (b : ℚ) * (1 + d2o) := by
      refine ⟨(1 - τ * ((a : ℚ) + 1)) / a, -τ, -τ, (1 - τ * ((b : ℚ) + 1)) / b,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [abs_le]
        constructor
        · rw [le_div_iff₀ hapos]; nlinarith
        · rw [div_le_iff₀ hapos]; nlinarith
      · rw [abs_neg, abs_of_nonneg h0]
      · rw [abs_neg, abs_of_nonneg h0]
      · rw [abs_le]
        constructor
        · rw [le_div_iff₀ hbpos]; nlinarith
        · rw [div_le_iff₀ hbpos]; nlinarith
      · have : (a : ℚ) ≠ 0 := ne_of_gt hapos
        field_simp <;> ring
      · have : (b : ℚ) ≠ 0 := ne_of_gt hbpos
        field_simp <;> ring
    obtain ⟨d1s, d2s, d1o, d2o, e1, e2, e3, e4, i1, i2⟩ := key
    have hf : ∀ d : ℚ, |d| ≤ τ → |(1 + d) - 1| ≤ τ := by
      intro d h
      have : 1 + d - 1 = d := by ring
      rw [this]; exact h
    have h0s : ¬ (0 : ℕ) = s := by omega
    have h0o : ¬ (0 : ℕ) = o := by omega
    have hos : ¬ o = s := fun h => hso h.symm
    have v1 : ∀ t ∈ List.replicate a s ++ List.replicate (b + 1) o, 1 ≤ t ∧ t ≤ ntok := by
      intro t ht
      simp only [List.mem_append, List.mem_replicate] at ht
      rcases ht with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact ⟨hs1, hs2⟩
      · exact ⟨ho1, ho2⟩
    have v2 : ∀ t ∈ List.replicate (a + 1) s ++ List.replicate b o, 1 ≤ t ∧ t ≤ ntok := by
      intro t ht
      simp only [List.mem_append, List.mem_replicate] at ht
      rcases ht with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact ⟨hs1, hs2⟩
      · exact ⟨ho1, ho2⟩
    have hl1 : (List.replicate a s ++ List.replicate (b + 1) o).length = a + b + 1 := by
      rw [List.length_append, List.length_replicate, List.length_replicate]; omega
    have hl2 : (List.replicate (a + 1) s ++ List.replicate b o).length = a + b + 1 := by
      rw [List.length_append, List.length_replicate, List.length_replicate]; omega
    refine ⟨scale N T s o (1 + d1s) (1 + d1o), scale N T s o (1 + d2s) (1 + d2o),
      scale_netRel τ N T s o _ _ (hf _ e1) (hf _ e3),
      scale_netRel τ N T s o _ _ (hf _ e2) (hf _ e4), ?_⟩
    have hc : ∀ c ∈ T,
        colSum (scale N T s o (1 + d1s) (1 + d1o))
          (List.replicate a s ++ List.replicate (b + 1) o) c =
        colSum (scale N T s o (1 + d2s) (1 + d2o))
          (List.replicate (a + 1) s ++ List.replicate b o) c := by
      intro c hcT
      rw [colSum_rep, colSum_rep]
      rw [ent, ent, ent, ent, ent, ent]
      simp only [hcT, if_true, h0s, h0o, hso, hos, if_false, eq_self_iff_true, mul_one, ↓reduceIte]
      push_cast
      linear_combination ((N.embed.getD s []).getD c 0) * i1 +
        ((N.embed.getD o []).getD c 0) * i2
    intro i hi
    exact hI N _ _ ntok T htb (sameOff N T s o _ _) (sameOff N T s o _ _) _ _ v1 v2
      (hl1.trans hl2.symm) hc i (by rw [hl1]; exact hi)

end Lane4.CollOfInv


namespace Lane4.BoundsProof
open Lane4.Seq Lane4.Coll Lane4.TB

theorem cp_rep (p : ℕ → Bool) (m v : ℕ) :
    (List.replicate m v).countP p = if p v = true then m else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.countP_cons, ih]
    by_cases h : p v = true <;> simp [h] <;> omega

theorem parity_of_collision : Collision → ParityBound := by
  intro hC N T K s o hb hpar hs1 hs2 hsi ho1 ho2 hoi τ a hτ0 hτ1 ha hOn
  by_contra hcon
  have h : 1 ≤ τ * (2 * (a : ℚ) + 1) := not_lt.mp hcon
  obtain ⟨N₁, N₂, h1, h2, heq⟩ := hC N K.V T s o hb hs1 hs2 ho1 ho2 τ a a hτ1 ha ha h h
  have hl1 : (List.replicate a s ++ List.replicate (a + 1) o).length = 2 * a + 1 := by
    simp; omega
  have hl2 : (List.replicate (a + 1) s ++ List.replicate a o).length = 2 * a + 1 := by
    simp; omega
  have hv1 : K.Valid (List.replicate a s ++ List.replicate (a + 1) o) := by
    refine ⟨?_, ?_⟩
    · intro hn
      have := congrArg List.length hn
      simp at this
    · intro t ht
      simp only [List.mem_append] at ht
      rcases ht with ht | ht
      · rw [List.eq_of_mem_replicate ht]; exact ⟨hs1, hs2⟩
      · rw [List.eq_of_mem_replicate ht]; exact ⟨ho1, ho2⟩
  have hv2 : K.Valid (List.replicate (a + 1) s ++ List.replicate a o) := by
    refine ⟨?_, ?_⟩
    · intro hn
      have := congrArg List.length hn
      simp at this
    · intro t ht
      simp only [List.mem_append] at ht
      rcases ht with ht | ht
      · rw [List.eq_of_mem_replicate ht]; exact ⟨hs1, hs2⟩
      · rw [List.eq_of_mem_replicate ht]; exact ⟨ho1, ho2⟩
  have c1 := hOn N₁ h1 _ hv1 (by omega)
  have c2 := hOn N₂ h2 _ hv2 (by omega)
  unfold Task.Correct at c1 c2
  have e := heq (2 * a + 1) (by omega)
  rw [hl1] at c1
  rw [hl2] at c2
  rw [e] at c1
  have k1 : (List.replicate a s ++ List.replicate (a + 1) o).countP K.inS = a := by
    rw [List.countP_append, cp_rep, cp_rep, hsi, hoi]; simp
  have k2 : (List.replicate (a + 1) s ++ List.replicate a o).countP K.inS = a + 1 := by
    rw [List.countP_append, cp_rep, cp_rep, hsi, hoi]; simp
  rw [k1] at c1
  rw [k2] at c2
  have key : (a % 2 = K.par) ↔ ((a + 1) % 2 = K.par) := c1.symm.trans c2
  omega

theorem sort_of_collision : Collision → SortBound := by
  intro hC N ntok T hb hn τ a hτ0 hτ1 ha hOn
  by_contra hcon
  have h : 1 ≤ τ * (2 * (a : ℚ) + 1) := not_lt.mp hcon
  obtain ⟨N₁, N₂, h1, h2, heq⟩ := hC N ntok T 1 2 hb (le_refl _) (by omega) (by omega) hn τ a a hτ1 ha ha h h
  have hl1 : (List.replicate a 1 ++ List.replicate (a + 1) 2).length = 2 * a + 1 := by
    simp; omega
  have hl2 : (List.replicate (a + 1) 1 ++ List.replicate a 2).length = 2 * a + 1 := by
    simp; omega
  have hv1 : ∀ t ∈ (List.replicate a 1 ++ List.replicate (a + 1) 2), 1 ≤ t ∧ t ≤ ntok := by
    intro t ht
    simp only [List.mem_append] at ht
    rcases ht with ht | ht
    · rw [List.eq_of_mem_replicate ht]; exact ⟨le_refl _, by omega⟩
    · rw [List.eq_of_mem_replicate ht]; exact ⟨by omega, hn⟩
  have hv2 : ∀ t ∈ (List.replicate (a + 1) 1 ++ List.replicate a 2), 1 ≤ t ∧ t ≤ ntok := by
    intro t ht
    simp only [List.mem_append] at ht
    rcases ht with ht | ht
    · rw [List.eq_of_mem_replicate ht]; exact ⟨le_refl _, by omega⟩
    · rw [List.eq_of_mem_replicate ht]; exact ⟨by omega, hn⟩
  have hne1 : (List.replicate a 1 ++ List.replicate (a + 1) 2) ≠ [] := by
    intro hh
    have := congrArg List.length hh
    simp at this
  have hne2 : (List.replicate (a + 1) 1 ++ List.replicate a 2) ≠ [] := by
    intro hh
    have := congrArg List.length hh
    simp at this
  obtain ⟨t₁, ho1, r1⟩ := hOn N₁ h1 _ hne1 hv1 (by omega) (a + 1) (by omega) (by omega)
  obtain ⟨t₂, ho2, r2⟩ := hOn N₂ h2 _ hne2 hv2 (by omega) (a + 1) (by omega) (by omega)
  have e := heq (a + 1) (by omega)
  rw [ho1, ho2] at e
  have et : t₁ = t₂ := by exact_mod_cast e
  subst et
  unfold IsRank at r1 r2
  simp only [List.countP_append, cp_rep, decide_eq_true_eq] at r1 r2
  obtain ⟨r1a, r1b⟩ := r1
  obtain ⟨r2a, r2b⟩ := r2
  split_ifs at r1a r1b r2a r2b <;> omega

end Lane4.BoundsProof


namespace Lane4.CollProof
open Lane4.Seq Lane4.Coll

theorem qRel_mono {a b : ℚ} (h : a ≤ b) {x y : ℚ} (hq : qRel a x y) : qRel b x y := by
  unfold qRel at *
  exact hq.trans (mul_le_mul_of_nonneg_right h (abs_nonneg x))

theorem vRel_mono {a b : ℚ} (h : a ≤ b) {x y : List ℚ} (hq : vRel a x y) : vRel b x y :=
  List.Forall₂.imp (fun _ _ p => qRel_mono h p) hq

theorem mRel_mono {a b : ℚ} (h : a ≤ b) {x y : List (List ℚ)} (hq : mRel a x y) : mRel b x y :=
  List.Forall₂.imp (fun _ _ p => vRel_mono h p) hq

theorem hRel_mono {a b : ℚ} (h : a ≤ b) {x y : Head} (hq : hRel a x y) : hRel b x y :=
  ⟨mRel_mono h hq.1, mRel_mono h hq.2.1, hq.2.2⟩

theorem bRel_mono {a b : ℚ} (h : a ≤ b) {x y : Block} (hq : bRel a x y) : bRel b x y :=
  ⟨List.Forall₂.imp (fun _ _ p => hRel_mono h p) hq.1, mRel_mono h hq.2.1, vRel_mono h hq.2.2.1,
    mRel_mono h hq.2.2.2.1, vRel_mono h hq.2.2.2.2⟩

theorem netRel_mono {a b : ℚ} (h : a ≤ b) {N N' : TNet} (hq : netRel a N N') : netRel b N N' :=
  ⟨mRel_mono h hq.1, List.Forall₂.imp (fun _ _ p => bRel_mono h p) hq.2.1,
    vRel_mono h hq.2.2.1, qRel_mono h hq.2.2.2⟩

theorem collision_bound' : CollisionBound' := by
  intro T s o hpar hs1 hsV hs ho1 hoV ho N hN τ L hτ1 hL hτL
  obtain ⟨D, hD⟩ := hN
  by_contra hcon
  push_neg at hcon
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  have hm : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast (by omega : 1 ≤ m)
  push_cast at hτL
  have hτ0 : 0 ≤ τ := by
    by_contra h
    push_neg at h
    nlinarith
  have hmpos : (0 : ℚ) < (m : ℚ) := by linarith
  have hd1 : |(1 - τ * ((m : ℚ) + 1)) / (m : ℚ)| ≤ τ := by
    rw [abs_le]
    constructor
    · rw [le_div_iff₀ hmpos]; nlinarith
    · rw [div_le_iff₀ hmpos]; nlinarith
  have hd1' : |(1 - τ * ((m : ℚ) + 1)) / (m : ℚ)| ≤ 1 := hd1.trans hτ1
  have hd2 : |(-τ)| = τ := by rw [abs_neg, abs_of_nonneg hτ0]
  obtain ⟨N₁, hr1, ho1'⟩ := hD _ hd1'
  obtain ⟨N₂, hr2, ho2'⟩ := hD (-τ) (by rw [hd2]; exact hτ1)
  have hr1' := netRel_mono hd1 hr1
  have hr2' := netRel_mono hd2.le hr2
  let w₁ : List ℕ := List.replicate m s ++ [o]
  let w₂ : List ℕ := List.replicate (m + 1) s
  have hl1 : w₁.length = m + 1 := by simp [w₁]
  have hl2 : w₂.length = m + 1 := by simp [w₂]
  have hc1 : w₁.countP T.inS = m := by
    simp [w₁, List.countP_append, List.countP_replicate, hs, ho]
  have hc2 : w₂.countP T.inS = m + 1 := by
    simp [w₂, List.countP_replicate, hs]
  have hv1 : T.Valid w₁ := by
    refine ⟨by simp [w₁], ?_⟩
    intro t ht
    simp only [w₁, List.mem_append, List.mem_replicate, List.mem_singleton] at ht
    rcases ht with ⟨_, rfl⟩ | rfl
    · exact ⟨hs1, hsV⟩
    · exact ⟨ho1, hoV⟩
  have hv2 : T.Valid w₂ := by
    refine ⟨by simp [w₂], ?_⟩
    intro t ht
    simp only [w₂, List.mem_replicate] at ht
    rcases ht with ⟨_, rfl⟩
    exact ⟨hs1, hsV⟩
  have c1 := hcon N₁ hr1' w₁ hv1 (by omega)
  have c2 := hcon N₂ hr2' w₂ hv2 (by omega)
  have e1 := ho1' w₁ hv1
  have e2 := ho2' w₂ hv2
  rw [hl1, hc1] at e1
  rw [hl2, hc2] at e2
  have heq : N₁.out w₁ w₁.length = N₂.out w₂ w₂.length := by
    rw [hl1, hl2, e1, e2]
    congr 1
    push_cast
    congr 1
    field_simp
    ring
  unfold Task.Correct at c1 c2
  rw [heq] at c1
  rw [hc1] at c1
  rw [hc2] at c2
  have key := c1.symm.trans c2
  by_cases h : m % 2 = T.par
  · have := key.mp h
    omega
  · have h' : ¬ (m + 1) % 2 = T.par := fun h' => h (key.mpr h')
    omega

theorem collision_bound : CollisionBound := by
  intro T s o hpar hs1 hsV hs ho1 hoV ho N hN τ L hτ0 hτ1 hL hball
  by_contra h
  push_neg at h
  obtain ⟨N', hr, w, hv, hlen, hnc⟩ :=
    collision_bound' T s o hpar hs1 hsV hs ho1 hoV ho N hN τ L hτ1 hL h
  exact hnc (hball N' hr w hv hlen)

end Lane4.CollProof


namespace Lane4Final
open Lane4.Seq Lane4.Coll Lane4.TB

theorem invariance : Invariance := Lane4.NetProof.invariance
theorem collision : Collision := Lane4.CollOfInv.collision_of_invariance invariance
theorem parityBound : ParityBound := Lane4.BoundsProof.parity_of_collision collision
theorem sortBound : SortBound := Lane4.BoundsProof.sort_of_collision collision

theorem onBall_mono {K : Task} {N : TNet} {a b : ℚ} (hab : a ≤ b) {L : ℕ}
    (h : K.OnBall N b L) : K.OnBall N a L :=
  fun N' hN' w hv hl => h N' (Lane4.CollProof.netRel_mono hab hN') w hv hl

theorem sortOnBall_mono {ntok : ℕ} {N : TNet} {a b : ℚ} (hab : a ≤ b) {L : ℕ}
    (h : SortOnBall ntok N b L) : SortOnBall ntok N a L :=
  fun N' hN' w hne hv hl i hi1 hi2 => h N' (Lane4.CollProof.netRel_mono hab hN') w hne hv hl i hi1 hi2

/-- From a radius bound at every odd length to "no positive radius works at every length". -/
theorem noBall_of (P : ℚ → ℕ → Prop)
    (mono : ∀ {a b : ℚ}, a ≤ b → ∀ {L : ℕ}, P b L → P a L)
    (rad : ∀ (τ : ℚ) (a : ℕ), 0 ≤ τ → τ ≤ 1 → 1 ≤ a → P τ (2 * a + 1) → τ * (2 * (a : ℚ) + 1) < 1)
    (τ : ℚ) (hτ : 0 < τ) : ∃ L : ℕ, ¬ P τ L := by
  by_cases h1 : τ ≤ 1
  · obtain ⟨m, hm⟩ := exists_nat_gt (1 / τ)
    have hm' : 1 < τ * (m : ℚ) := by
      have := mul_lt_mul_of_pos_left hm hτ
      rwa [mul_one_div_cancel hτ.ne'] at this
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        norm_num at hm'
      · exact h0
    refine ⟨2 * m + 1, fun hb => ?_⟩
    have hr := rad τ m hτ.le h1 hm1 hb
    nlinarith
  · refine ⟨2 * 1 + 1, fun hb => ?_⟩
    have hb1 : P 1 (2 * 1 + 1) := mono (le_of_not_ge h1) hb
    have hr := rad 1 1 (by norm_num) le_rfl le_rfl hb1
    norm_num at hr

end Lane4Final

namespace Lane4.Member.p05
open Lane4.Seq Lane4.Coll Lane4.TB


def z11 : Vec := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def e0 : Vec := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def e2 : Vec := [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
def e7 : Vec := [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
def a4 : Vec := [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]
def a5 : Vec := [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]

/-- Block 1: uniform average of the S-indicator, written into slot 1. -/
def hd1 : Head :=
  { A := [z11, z11, z11, z11, z11, z11, z11, z11, z11, z11, z11],
    V := [z11, e0, z11, z11, z11, z11, z11, z11, z11, z11, z11],
    mask := Mask.all }

def blk1 : Block :=
  { heads := [hd1], W1 := [z11], b1 := [0],
    W2 := [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]], b2 := z11 }

/-- Block 2: score 2 r j - j^2 / n peaks at j = k; read (-1)^j into slot 2. -/
def hd2 : Head :=
  { A := [z11, a4, z11, z11, z11, z11, z11, z11, z11, a5, z11],
    V := [z11, z11, e7, z11, z11, z11, z11, z11, z11, z11, z11],
    mask := Mask.all }

def blk2 : Block :=
  { heads := [hd2], W1 := [z11], b1 := [0],
    W2 := [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]], b2 := z11 }

def net : TNet :=
  { embed := [[0, 0, 0], [1, 0, 0], [0, 0, 0], [1, 0, 0], [1, 0, 0]],
    blocks := [blk1, blk2],
    outW := e2,
    outB := 0 }

def task : Task := { V := 4, inS := fun t => t == 1 || t == 3 || t == 4, par := 0 }

theorem member : tokenBlind net 4 [0] = true := by decide

/-- A relative ball that is correct for this network's parity task up to length 2a+1 has
radius below 1/(2a+1). -/
theorem radius (τ : ℚ) (a : ℕ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (ha : 1 ≤ a)
    (hb : task.OnBall net τ (2 * a + 1)) : τ * (2 * (a : ℚ) + 1) < 1 :=
  Lane4Final.parityBound net [0] task 1 2 member (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) τ a h0 h1 ha hb

theorem noBall (τ : ℚ) (hτ : 0 < τ) : ∃ L : ℕ, ¬ task.OnBall net τ L :=
  Lane4Final.noBall_of (fun t L => task.OnBall net t L) (fun hab _ h => Lane4Final.onBall_mono hab h)
    radius τ hτ

end Lane4.Member.p05

namespace Lane4.Member.p10
open Lane4.Seq Lane4.Coll Lane4.TB


def z11 : Vec := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def hd1 : Head :=
  { A := [z11, z11, z11, z11, z11, z11, z11, z11, z11, z11, z11],
    V := [z11, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], z11, z11, z11, z11, z11, z11, z11, z11, z11],
    mask := Mask.all }

def hd2 : Head :=
  { A := [z11, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], z11, z11, z11, z11, z11, z11, z11,
          [0, 0, 0, 0, 0, -1/2, 0, 0, 0, 0, 0], z11],
    V := [z11, z11, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], z11, z11, z11, z11, z11, z11, z11, z11],
    mask := Mask.all }

def blk1 : Block :=
  { heads := [hd1], W1 := [z11], b1 := [0],
    W2 := [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]], b2 := z11 }

def blk2 : Block :=
  { heads := [hd2], W1 := [z11], b1 := [0],
    W2 := [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]], b2 := z11 }

def net : TNet :=
  { embed := [[0, 0, 0], [1, 0, 0], [1, 0, 0], [0, 0, 0]],
    blocks := [blk1, blk2],
    outW := [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    outB := 0 }

def task : Task := { V := 3, inS := fun t => t == 1 || t == 2, par := 0 }

theorem member : tokenBlind net 3 [0] = true := by decide

/-- A relative ball that is correct for this network's parity task up to length 2a+1 has
radius below 1/(2a+1). -/
theorem radius (τ : ℚ) (a : ℕ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (ha : 1 ≤ a)
    (hb : task.OnBall net τ (2 * a + 1)) : τ * (2 * (a : ℚ) + 1) < 1 :=
  Lane4Final.parityBound net [0] task 1 3 member (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) τ a h0 h1 ha hb

theorem noBall (τ : ℚ) (hτ : 0 < τ) : ∃ L : ℕ, ¬ task.OnBall net τ L :=
  Lane4Final.noBall_of (fun t L => task.OnBall net t L) (fun hab _ h => Lane4Final.onBall_mono hab h)
    radius τ hτ

end Lane4.Member.p10

namespace Lane4.Member.p29
open Lane4.Seq Lane4.Coll Lane4.TB


def z11 : Vec := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def e0 : Vec := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def e7 : Vec := [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]

/-- Block 1: slot 1 := average of flag over all positions = k/n. -/
def hd1 : Head :=
  { A := [z11, z11, z11, z11, z11, z11, z11, z11, z11, z11, z11],
    V := [z11, e0, z11, z11, z11, z11, z11, z11, z11, z11, z11],
    mask := Mask.all }

/-- Block 2: score(j) = 2 c j - (1/n) j^2, maximal at j = k; read (-1)^j into slot 2. -/
def hd2 : Head :=
  { A := [z11, [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], z11, z11, z11, z11, z11, z11, z11,
          [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], z11],
    V := [z11, z11, e7, z11, z11, z11, z11, z11, z11, z11, z11],
    mask := Mask.all }

def blk1 : Block :=
  { heads := [hd1], W1 := [z11], b1 := [0],
    W2 := [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]], b2 := z11 }

def blk2 : Block :=
  { heads := [hd2], W1 := [z11], b1 := [0],
    W2 := [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]], b2 := z11 }

def net : TNet :=
  { embed := [[0, 0, 0], [0, 0, 0], [1, 0, 0], [1, 0, 0], [0, 0, 0]],
    blocks := [blk1, blk2],
    outW := [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    outB := 0 }

def task : Task := { V := 4, inS := fun t => t == 2 || t == 3, par := 1 }

theorem member : tokenBlind net 4 [0] = true := by decide

/-- A relative ball that is correct for this network's parity task up to length 2a+1 has
radius below 1/(2a+1). -/
theorem radius (τ : ℚ) (a : ℕ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (ha : 1 ≤ a)
    (hb : task.OnBall net τ (2 * a + 1)) : τ * (2 * (a : ℚ) + 1) < 1 :=
  Lane4Final.parityBound net [0] task 2 1 member (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) τ a h0 h1 ha hb

theorem noBall (τ : ℚ) (hτ : 0 < τ) : ∃ L : ℕ, ¬ task.OnBall net τ L :=
  Lane4Final.noBall_of (fun t L => task.OnBall net t L) (fun hab _ h => Lane4Final.onBall_mono hab h)
    radius τ hτ

end Lane4.Member.p29

namespace Lane4.Member.s00
open Lane4.Seq Lane4.Coll Lane4.TB


def z14 : Vec := [0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def e0 : Vec := [1,0,0,0,0,0,0,0,0,0,0,0,0,0]
def e1 : Vec := [0,1,0,0,0,0,0,0,0,0,0,0,0,0]
def rowM : Vec := [0,0,1,0,0,0,0,0,0,0,0,0,1,-1]
def rowR : Vec := [0,0,0,0,-2,0,0,0,0,0,0,0,0,0]

def hd1 : Head :=
  { A := [z14,z14,z14,z14,z14,z14,z14,z14,z14,z14,z14,z14,z14,z14],
    V := [z14,z14,e1,z14,z14,z14,z14,z14,z14,z14,z14,z14,z14,z14],
    mask := Mask.all }

def blk1 : Block :=
  { heads := [hd1], W1 := [rowM], b1 := [0],
    W2 := [[0],[0],[0],[1],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]], b2 := z14 }

def hd2 : Head :=
  { A := [z14,z14,z14,e0,z14,z14,z14,z14,z14,z14,z14,z14,z14,z14],
    V := [z14,z14,z14,z14,e0,z14,z14,z14,z14,z14,z14,z14,z14,z14],
    mask := Mask.all }

def blk2 : Block :=
  { heads := [hd2], W1 := [rowR], b1 := [1],
    W2 := [[0],[0],[0],[0],[0],[1],[0],[0],[0],[0],[0],[0],[0],[0]], b2 := z14 }

def net : TNet :=
  { embed := [[1,0,0,0,0,0],[0,1,0,0,0,0],[0,0,0,0,0,0]],
    blocks := [blk1, blk2],
    outW := [0,0,0,0,-2,-1,0,0,0,0,0,0,0,0],
    outB := 3 }

theorem member : tokenBlind net 2 [1] = true := by decide

/-- A relative ball that is correct for sort rank up to length 2a+1 has radius below 1/(2a+1). -/
theorem radius (τ : ℚ) (a : ℕ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (ha : 1 ≤ a)
    (hb : SortOnBall 2 net τ (2 * a + 1)) : τ * (2 * (a : ℚ) + 1) < 1 :=
  Lane4Final.sortBound net 2 [1] member (by decide) τ a h0 h1 ha hb

theorem noBall (τ : ℚ) (hτ : 0 < τ) : ∃ L : ℕ, ¬ SortOnBall 2 net τ L :=
  Lane4Final.noBall_of (fun t L => SortOnBall 2 net t L)
    (fun hab _ h => Lane4Final.sortOnBall_mono hab h) radius τ hτ

end Lane4.Member.s00

namespace Lane4.Member.s01
open Lane4.Seq Lane4.Coll Lane4.TB


def z : Vec := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def u1 : Vec := [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def u12 : Vec := [1,1,0,0,0,0,0,0,0,0,0,0,0,0,0]
def ub : Vec := [0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
def uh : Vec := [0,0,1/2,0,0,0,0,0,0,0,0,0,0,0,0]
def un : Vec := [0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0]

def hd1 : Head :=
  { A := [z,z,z,z,z,z,z,z,z,z,z,z,z,z,z],
    V := [z,z,z,u1,u12,z,z,z,z,z,z,z,z,z,z],
    mask := Mask.all }
def hd2 : Head :=
  { A := [z,z,z,ub,z,z,z,z,z,z,z,z,z,uh,un],
    V := [z,z,z,z,z,ub,z,z,z,z,z,z,z,z,z],
    mask := Mask.all }
def hd3 : Head :=
  { A := [z,z,z,z,ub,z,z,z,z,z,z,z,z,uh,un],
    V := [z,z,z,z,z,z,ub,z,z,z,z,z,z,z,z],
    mask := Mask.all }

def w2rows : List Vec := [[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]]

def blk1 : Block := { heads := [hd1], W1 := [z], b1 := [0], W2 := w2rows, b2 := z }
def blk2 : Block := { heads := [hd2, hd3], W1 := [z], b1 := [0], W2 := w2rows, b2 := z }

def net : TNet :=
  { embed := [[0,0,1,0,0,0,0],[1,0,0,0,0,0,0],[0,1,0,0,0,0,0],[0,0,0,0,0,0,0]],
    blocks := [blk1, blk2],
    outW := [0,0,0,0,0,-1,-1,0,0,0,0,0,0,0,0],
    outB := 3 }

theorem member : tokenBlind net 3 [0, 1] = true := by decide

/-- A relative ball that is correct for sort rank up to length 2a+1 has radius below 1/(2a+1). -/
theorem radius (τ : ℚ) (a : ℕ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (ha : 1 ≤ a)
    (hb : SortOnBall 3 net τ (2 * a + 1)) : τ * (2 * (a : ℚ) + 1) < 1 :=
  Lane4Final.sortBound net 3 [0, 1] member (by decide) τ a h0 h1 ha hb

theorem noBall (τ : ℚ) (hτ : 0 < τ) : ∃ L : ℕ, ¬ SortOnBall 3 net τ L :=
  Lane4Final.noBall_of (fun t L => SortOnBall 3 net t L)
    (fun hab _ h => Lane4Final.sortOnBall_mono hab h) radius τ hτ

end Lane4.Member.s01

#print axioms Lane4Final.invariance
#print axioms Lane4Final.collision
#print axioms Lane4Final.parityBound
#print axioms Lane4Final.sortBound
#print axioms Lane4.Member.p05.member
#print axioms Lane4.Member.p05.radius
#print axioms Lane4.Member.p05.noBall
#print axioms Lane4.Member.p10.member
#print axioms Lane4.Member.p10.radius
#print axioms Lane4.Member.p10.noBall
#print axioms Lane4.Member.p29.member
#print axioms Lane4.Member.p29.radius
#print axioms Lane4.Member.p29.noBall
#print axioms Lane4.Member.s00.member
#print axioms Lane4.Member.s00.radius
#print axioms Lane4.Member.s00.noBall
#print axioms Lane4.Member.s01.member
#print axioms Lane4.Member.s01.radius
#print axioms Lane4.Member.s01.noBall
