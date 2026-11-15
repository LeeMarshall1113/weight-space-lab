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


namespace Lane4.Case
open Lane4.Seq Lane4.Coll


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

def Membership : Prop := task.CountChannel net

end Lane4.Case


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


namespace Lane4.Case
open Lane4.Seq Lane4.Coll

def indq (t : ℕ) : ℚ := if t = 1 ∨ t = 2 then 1 else 0
def ind (w : List ℕ) (j : ℕ) : ℚ := indq (tokAt w j)
def Fq (w : List ℕ) : ℚ := ((w.countP task.inS : ℕ) : ℚ) / ((w.length : ℚ) + 1)
def x1z (n : ℕ) (Z : ℚ) (w : List ℕ) (j : ℕ) : Vec := [ind w j, Z, 0] ++ pos j n

theorem sum_getD (g : ℕ → ℚ) (l : List ℕ) :
    ((List.range l.length).map (fun j => g (l.getD j 0))).sum = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    simp only [Function.comp_def, List.getD_cons_zero, List.getD_cons_succ]
    rw [ih, List.map_cons, List.sum_cons]

theorem sum_indq (w : List ℕ) : (w.map indq).sum = ((w.countP task.inS : ℕ) : ℚ) := by
  induction w with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    have key : task.inS a = true ↔ (a = 1 ∨ a = 2) := by simp [task]
    by_cases h : a = 1 ∨ a = 2
    · have h' := key.mpr h
      simp [indq, h, h']
      ring
    · have h' : ¬ (task.inS a = true) := fun x => h (key.mp x)
      simp [indq, h, h']

theorem sum_ind (w : List ℕ) :
    ((List.range (w.length + 1)).map (ind w)).sum = ((w.countP task.inS : ℕ) : ℚ) := by
  have h1 := sum_getD indq (0 :: w)
  have e : ind w = fun j => indq ((0 :: w).getD j 0) := rfl
  rw [e]
  rw [List.length_cons] at h1
  rw [h1, List.map_cons, List.sum_cons, sum_indq]
  simp [indq]

theorem avgF (w : List ℕ) : avg (List.range (w.length + 1)) (ind w) = Fq w := by
  unfold avg Fq
  rw [sum_ind]
  simp

theorem avgFc (c : ℚ) (w : List ℕ) :
    avg (List.range (w.length + 1)) (fun k => c * ind w k) = c * Fq w := by
  have h := avgF w
  unfold avg at h ⊢
  rw [List.sum_map_mul_left, mul_div_assoc, h]

def hd1d (d : ℚ) : Head :=
  { A := hd1.A,
    V := [z11, [1 + d, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], z11, z11, z11, z11, z11, z11, z11, z11, z11],
    mask := Mask.all }

def blk1d (d : ℚ) : Block :=
  { heads := [hd1d d], W1 := blk1.W1, b1 := blk1.b1, W2 := blk1.W2, b2 := blk1.b2 }

def Nd (d : ℚ) : TNet :=
  { embed := net.embed, blocks := [blk1d d, blk2], outW := net.outW, outB := net.outB }

theorem qRel_refl (τ : ℚ) (h : 0 ≤ τ) (a : ℚ) : qRel τ a a := by
  unfold qRel
  simp
  positivity

theorem vRel_refl (τ : ℚ) (h : 0 ≤ τ) (l : List ℚ) : vRel τ l l := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a t ih => exact List.Forall₂.cons (qRel_refl τ h a) ih

theorem mRel_refl (τ : ℚ) (h : 0 ≤ τ) (l : List (List ℚ)) : mRel τ l l := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a t ih => exact List.Forall₂.cons (vRel_refl τ h a) ih

theorem hRel_refl (τ : ℚ) (h : 0 ≤ τ) (g : Head) : hRel τ g g :=
  ⟨mRel_refl τ h _, mRel_refl τ h _, rfl⟩

theorem bRel_refl (τ : ℚ) (h : 0 ≤ τ) (B : Block) : bRel τ B B := by
  refine ⟨?_, mRel_refl τ h _, vRel_refl τ h _, mRel_refl τ h _, vRel_refl τ h _⟩
  induction B.heads with
  | nil => exact List.Forall₂.nil
  | cons a t ih => exact List.Forall₂.cons (hRel_refl τ h a) ih

theorem hd_rel (d : ℚ) : hRel |d| hd1 (hd1d d) := by
  have h0 : 0 ≤ |d| := abs_nonneg d
  refine ⟨mRel_refl _ h0 _, ?_, rfl⟩
  have e1 : hd1.V = z11 :: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ::
      [z11, z11, z11, z11, z11, z11, z11, z11, z11] := rfl
  have e2 : (hd1d d).V = z11 :: [1 + d, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ::
      [z11, z11, z11, z11, z11, z11, z11, z11, z11] := rfl
  rw [e1, e2]
  refine List.Forall₂.cons (vRel_refl _ h0 _) (List.Forall₂.cons ?_ (mRel_refl _ h0 _))
  refine List.Forall₂.cons ?_ (vRel_refl _ h0 _)
  unfold qRel
  simp

theorem Nd_rel (d : ℚ) : netRel |d| net (Nd d) := by
  have h0 : 0 ≤ |d| := abs_nonneg d
  refine ⟨mRel_refl _ h0 _, ?_, vRel_refl _ h0 _, qRel_refl _ h0 _⟩
  refine List.Forall₂.cons ?_ (List.Forall₂.cons (bRel_refl _ h0 _) List.Forall₂.nil)
  refine ⟨List.Forall₂.cons (hd_rel d) List.Forall₂.nil, mRel_refl _ h0 _, vRel_refl _ h0 _,
    mRel_refl _ h0 _, vRel_refl _ h0 _⟩

theorem init_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) :
    net.init w j = [ind w j, 0, 0] ++ pos j (w.length + 1) := by
  have h3 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 := by
    rcases tokAt_zero_or_mem w j with h | h
    · left; exact h
    · have := hw _ h
      omega
  rcases h3 with h | h | h | h <;> simp [TNet.init, net, ind, indq, h]

theorem b1_eq (d : ℚ) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) :
    (blk1d d).apply (w.length + 1) (net.init w) j = x1z (w.length + 1) ((1 + d) * Fq w) w j := by
  have hs : ∀ i k, (hd1d d).score (net.init w i) (net.init w k) = 0 := by
    intro i k
    rw [init_eq w hw i, init_eq w hw k]
    simp [Head.score, hd1d, hd1, z11, qdot, matVec, pos]
  have hsel : ∀ i, (hd1d d).sel (w.length + 1) (net.init w) i = List.range (w.length + 1) := by
    intro i
    have := sel_all (hd1d d) (w.length + 1) (net.init w) i (fun k _ l _ => by rw [hs, hs])
    rw [this]
    rfl
  have hf : (fun k => qdot [1 + d, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (net.init w k))
      = fun k => (1 + d) * ind w k := by
    funext k
    rw [init_eq w hw k]
    simp [qdot, pos]
  have hz : ∀ S : List ℕ, avg S (fun k => qdot z11 (net.init w k)) = 0 := by
    intro S
    have : (fun k => qdot z11 (net.init w k)) = fun _ => (0 : ℚ) := by
      funext k
      rw [init_eq w hw k]
      simp [qdot, z11, pos]
    rw [this, avg_zero]
  have hV : (hd1d d).V = [z11, [1 + d, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], z11, z11, z11, z11, z11,
      z11, z11, z11, z11] := rfl
  have attn1 : ∀ i, (hd1d d).attn (w.length + 1) (net.init w) i
      = [0, (1 + d) * Fq w, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    intro i
    unfold Head.attn
    rw [hsel i, hV]
    simp only [List.map_cons, List.map_nil, hz, hf, avgFc]
  have hh : (blk1d d).heads = [hd1d d] := rfl
  simp only [Block.apply, hh, List.foldl_cons, List.foldl_nil, attn1]
  rw [init_eq w hw j]
  simp [blk1d, blk1, x1z, qdot, vadd, affine, z11, pos]

def f (n : ℕ) (z : ℚ) (j : ℕ) : ℚ :=
  z * (j : ℚ) + (-1 / 2) * (1 / (n : ℚ)) * (j : ℚ) ^ 2

theorem score2 (n : ℕ) (Z : ℚ) (w : List ℕ) (i k : ℕ) :
    hd2.score (x1z n Z w i) (x1z n Z w k) = f n Z k := by
  simp [Head.score, hd2, x1z, f, z11, qdot, matVec, pos]
  try ring

def D (n : ℕ) (z : ℚ) : ℚ :=
  avg ((List.range n).filter (fun j => decide (∀ k ∈ List.range n, f n z k ≤ f n z j)))
    (fun j => (-1 : ℚ) ^ j)

theorem hsel2 (n : ℕ) (Z : ℚ) (w : List ℕ) (i : ℕ) :
    hd2.sel n (x1z n Z w) i
      = (List.range n).filter (fun j => decide (∀ k ∈ List.range n, f n Z k ≤ f n Z j)) := by
  unfold Head.sel
  have hc : cand hd2.mask n i = List.range n := rfl
  rw [hc]
  simp only [score2]

theorem b2_eq (d : ℚ) (w : List ℕ) (i : ℕ) :
    blk2.apply (w.length + 1) (x1z (w.length + 1) ((1 + d) * Fq w) w) i
      = [ind w i, (1 + d) * Fq w, D (w.length + 1) ((1 + d) * Fq w)] ++ pos i (w.length + 1) := by
  have hV : hd2.V = [z11, z11, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], z11, z11, z11, z11, z11, z11,
      z11, z11] := rfl
  have hz : ∀ S : List ℕ, avg S (fun k => qdot z11 (x1z (w.length + 1) ((1 + d) * Fq w) w k)) = 0 := by
    intro S
    have : (fun k => qdot z11 (x1z (w.length + 1) ((1 + d) * Fq w) w k)) = fun _ => (0 : ℚ) := by
      funext k
      simp [x1z, qdot, z11, pos]
    rw [this, avg_zero]
  have h7 : (fun k => qdot [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
      (x1z (w.length + 1) ((1 + d) * Fq w) w k)) = fun k => (-1 : ℚ) ^ k := by
    funext k
    simp [x1z, qdot, pos]
  have attn2 : hd2.attn (w.length + 1) (x1z (w.length + 1) ((1 + d) * Fq w) w) i
      = [0, 0, D (w.length + 1) ((1 + d) * Fq w), 0, 0, 0, 0, 0, 0, 0, 0] := by
    unfold Head.attn
    rw [hsel2, hV]
    simp only [List.map_cons, List.map_nil, hz, h7]
    rfl
  have hh : blk2.heads = [hd2] := rfl
  simp only [Block.apply, hh, List.foldl_cons, List.foldl_nil, attn2]
  simp [blk2, x1z, qdot, vadd, affine, z11, pos]

theorem out_eq (d : ℚ) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (i : ℕ) :
    (Nd d).out w i = D (w.length + 1) ((1 + d) * Fq w) := by
  have h1 : (blk1d d).apply (w.length + 1) (net.init w)
      = x1z (w.length + 1) ((1 + d) * Fq w) w := funext (b1_eq d w hw)
  have hrun : (Nd d).run w = blk2.apply (w.length + 1) (x1z (w.length + 1) ((1 + d) * Fq w) w) := by
    rw [← h1]
    rfl
  unfold TNet.out
  rw [hrun, b2_eq d w i]
  simp [Nd, net, qdot, pos]

theorem membership : Membership := by
  refine ⟨D, fun d _ => ⟨Nd d, Nd_rel d, ?_⟩⟩
  intro w hv
  have hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3 := hv.2
  rw [out_eq d w hw w.length]
  congr 1
  unfold Fq
  ring

end Lane4.Case


namespace Lane4Final
open Lane4.Seq Lane4.Coll

/-- The class is not empty: this network is a member. -/
theorem member : Lane4.Case.task.CountChannel Lane4.Case.net := Lane4.Case.membership

/-- Necessary radius for this network: a relative ball that is correct up to length `L`
has radius below `1 / (2 L - 1)`. -/
theorem radius (τ : ℚ) (L : ℕ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (hL : 2 ≤ L)
    (hb : Lane4.Case.task.OnBall Lane4.Case.net τ L) : τ * (2 * (L : ℚ) - 1) < 1 :=
  Lane4.CollProof.collision_bound Lane4.Case.task 1 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) Lane4.Case.net member τ L h0 h1 hL hb

theorem onBall_mono {T : Task} {N : TNet} {a b : ℚ} (hab : a ≤ b) {L : ℕ}
    (h : T.OnBall N b L) : T.OnBall N a L :=
  fun N' hN' w hv hl => h N' (Lane4.CollProof.netRel_mono hab hN') w hv hl

/-- No relative ball of positive radius is correct at every length. -/
theorem noBall (τ : ℚ) (hτ : 0 < τ) : ∃ L : ℕ, ¬ Lane4.Case.task.OnBall Lane4.Case.net τ L := by
  by_cases h1 : τ ≤ 1
  · obtain ⟨m, hm⟩ := exists_nat_gt (1 / τ)
    refine ⟨m + 2, fun hb => ?_⟩
    have hr := radius τ (m + 2) hτ.le h1 (by omega) hb
    have hm' : 1 < τ * (m : ℚ) := by
      have := mul_lt_mul_of_pos_left hm hτ
      rwa [mul_one_div_cancel hτ.ne'] at this
    push_cast at hr
    nlinarith
  · refine ⟨2, fun hb => ?_⟩
    have hb1 : Lane4.Case.task.OnBall Lane4.Case.net 1 2 := onBall_mono (le_of_not_ge h1) hb
    have hr := radius 1 2 (by norm_num) le_rfl le_rfl hb1
    norm_num at hr

end Lane4Final
#print axioms Lane4Final.member
#print axioms Lane4Final.radius
#print axioms Lane4Final.noBall
