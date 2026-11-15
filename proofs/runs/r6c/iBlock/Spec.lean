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
