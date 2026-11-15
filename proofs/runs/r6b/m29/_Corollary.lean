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

def e0d (d : ℚ) : Vec := [1 + d, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def hd1d (d : ℚ) : Head :=
  { A := [z11, z11, z11, z11, z11, z11, z11, z11, z11, z11, z11],
    V := [z11, e0d d, z11, z11, z11, z11, z11, z11, z11, z11, z11],
    mask := Mask.all }

def blk1d (d : ℚ) : Block :=
  { heads := [hd1d d], W1 := [z11], b1 := [0],
    W2 := [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]], b2 := z11 }

def netd (d : ℚ) : TNet :=
  { embed := [[0, 0, 0], [0, 0, 0], [1, 0, 0], [1, 0, 0], [0, 0, 0]],
    blocks := [blk1d d, blk2],
    outW := [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    outB := 0 }

/-! relation helpers -/

theorem list_refl {α : Type} (R : α → α → Prop) (h : ∀ a, R a a) :
    ∀ l : List α, List.Forall₂ R l l := by
  intro l
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a t ih => exact List.Forall₂.cons (h a) ih

theorem qRel_refl (τ : ℚ) (hτ : 0 ≤ τ) (a : ℚ) : qRel τ a a := by
  unfold qRel
  simp
  positivity

theorem vRel_refl (τ : ℚ) (hτ : 0 ≤ τ) (v : List ℚ) : vRel τ v v :=
  list_refl (qRel τ) (qRel_refl τ hτ) v

theorem mRel_refl (τ : ℚ) (hτ : 0 ≤ τ) (M : List (List ℚ)) : mRel τ M M :=
  list_refl (vRel τ) (vRel_refl τ hτ) M

theorem hRel_refl (τ : ℚ) (hτ : 0 ≤ τ) (h : Head) : hRel τ h h :=
  ⟨mRel_refl τ hτ _, mRel_refl τ hτ _, rfl⟩

theorem bRel_refl (τ : ℚ) (hτ : 0 ≤ τ) (B : Block) : bRel τ B B :=
  ⟨list_refl (hRel τ) (hRel_refl τ hτ) _, mRel_refl τ hτ _, vRel_refl τ hτ _,
    mRel_refl τ hτ _, vRel_refl τ hτ _⟩

theorem e0_rel (d : ℚ) : vRel |d| e0 (e0d d) := by
  unfold vRel e0 e0d
  refine List.Forall₂.cons ?_ (vRel_refl |d| (abs_nonneg d) _)
  unfold qRel
  simp

theorem net_rel (d : ℚ) : netRel |d| net (netd d) := by
  have hτ : 0 ≤ |d| := abs_nonneg d
  refine ⟨mRel_refl _ hτ _, ?_, vRel_refl _ hτ _, qRel_refl _ hτ _⟩
  show List.Forall₂ (bRel |d|) [blk1, blk2] [blk1d d, blk2]
  refine List.Forall₂.cons ?_ (List.Forall₂.cons (bRel_refl _ hτ _) List.Forall₂.nil)
  refine ⟨?_, mRel_refl _ hτ _, vRel_refl _ hτ _, mRel_refl _ hτ _, vRel_refl _ hτ _⟩
  show List.Forall₂ (hRel |d|) [hd1] [hd1d d]
  refine List.Forall₂.cons ?_ List.Forall₂.nil
  refine ⟨mRel_refl _ hτ _, ?_, rfl⟩
  show List.Forall₂ (vRel |d|) [z11, e0, z11, z11, z11, z11, z11, z11, z11, z11, z11]
    [z11, e0d d, z11, z11, z11, z11, z11, z11, z11, z11, z11]
  exact List.Forall₂.cons (vRel_refl _ hτ _) (List.Forall₂.cons (e0_rel d) (mRel_refl _ hτ _))

/-! the computation -/

def Sq (t : ℕ) : ℚ := if t = 2 ∨ t = 3 then 1 else 0

def flag (w : List ℕ) (j : ℕ) : ℚ := Sq (tokAt w j)

def xs1 (d : ℚ) (w : List ℕ) (j : ℕ) : Vec :=
  [flag w j, (1 + d) * avg (List.range (w.length + 1)) (flag w), 0] ++ pos j (w.length + 1)

theorem Sq_inS (t : ℕ) : Sq t = if task.inS t = true then 1 else 0 := by
  simp [Sq, task]

theorem cnt (w : List ℕ) :
    ((List.range w.length).map (fun j => Sq (w.getD j 0))).sum = (w.countP task.inS : ℚ) := by
  induction w with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    have hfun : ((fun j => Sq ((a :: t).getD j 0)) ∘ Nat.succ) = fun j => Sq (t.getD j 0) := by
      funext j
      simp
    rw [hfun, ih, List.countP_cons]
    by_cases hi : task.inS a = true
    · simp [Sq_inS, hi]
      all_goals (try ring)
    · simp [Sq_inS, hi]

theorem sum_flag (w : List ℕ) :
    ((List.range (w.length + 1)).map (flag w)).sum = (w.countP task.inS : ℚ) := by
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  have h0 : flag w 0 = 0 := by simp [flag, tokAt, Sq]
  have hfun : (flag w ∘ Nat.succ) = fun j => Sq (w.getD j 0) := by
    funext j
    simp [flag, tokAt]
  rw [h0, hfun, cnt w, zero_add]

theorem cq_eq (w : List ℕ) :
    avg (List.range (w.length + 1)) (flag w) =
      (w.countP task.inS : ℚ) / ((w.length + 1 : ℕ) : ℚ) := by
  unfold avg
  rw [sum_flag w, List.length_range]

theorem init_eq (d : ℚ) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) :
    (netd d).init w j = [flag w j, 0, 0] ++ pos j (w.length + 1) := by
  have h5 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 := by
    rcases tokAt_zero_or_mem w j with h | h
    · left; exact h
    · have := hw _ h
      omega
  rcases h5 with h | h | h | h | h <;> simp [TNet.init, netd, flag, Sq, h]

theorem avg_mul_left (S : List ℕ) (c : ℚ) (f : ℕ → ℚ) :
    avg S (fun j => c * f j) = c * avg S f := by
  unfold avg
  rw [List.sum_map_mul_left, mul_div_assoc]

theorem sel1 (d : ℚ) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    (hd1d d).sel (w.length + 1) ((netd d).init w) i = List.range (w.length + 1) := by
  have h := sel_all (hd1d d) (w.length + 1) ((netd d).init w) i (by
    intro k _ l _
    simp [init_eq d w hw, Head.score, hd1d, matVec, qdot, z11, pos])
  rw [h]
  simp [hd1d, cand]

theorem blk1_eq (d : ℚ) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) :
    (blk1d d).apply (w.length + 1) ((netd d).init w) = xs1 d w := by
  funext i
  have hf : (fun j => qdot (e0d d) ((netd d).init w j)) = fun j => (1 + d) * flag w j := by
    funext j
    rw [init_eq d w hw j]
    simp [qdot, e0d, pos]
  have hz : ∀ S : List ℕ, avg S (fun j => qdot z11 ((netd d).init w j)) = 0 := by
    intro S
    have : (fun j => qdot z11 ((netd d).init w j)) = fun _ => (0 : ℚ) := by
      funext j
      rw [init_eq d w hw j]
      simp [qdot, z11, pos]
    rw [this, avg_zero]
  simp only [List.foldl, Block.apply, blk1d, Head.attn, sel1 d w hw]
  simp only [hd1d, List.map, hf, hz, avg_mul_left]
  rw [init_eq d w hw i]
  simp [xs1, vadd, affine, qdot, z11, pos]
  all_goals (try ring)

theorem out_eq (d : ℚ) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    (netd d).out w i = -avg (hd2.sel (w.length + 1) (xs1 d w) i) (fun j => (-1 : ℚ) ^ j) := by
  have hb : (netd d).blocks = [blk1d d, blk2] := rfl
  have ho : (netd d).outW = [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have hc : (netd d).outB = 0 := rfl
  have hf : (fun j => qdot e7 (xs1 d w j)) = fun j => (-1 : ℚ) ^ j := by
    funext j
    simp [xs1, qdot, e7, pos]
  have hz : ∀ S : List ℕ, avg S (fun j => qdot z11 (xs1 d w j)) = 0 := by
    intro S
    have : (fun j => qdot z11 (xs1 d w j)) = fun _ => (0 : ℚ) := by
      funext j
      simp [xs1, qdot, z11, pos]
    rw [this, avg_zero]
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [List.foldl]
  rw [blk1_eq d w hw]
  simp only [Block.apply, blk2, Head.attn]
  simp only [hd2, List.map, hf, hz]
  simp [xs1, vadd, affine, qdot, z11, e7, pos]
  all_goals (try ring)

theorem score2 (d : ℚ) (w : List ℕ) (i j : ℕ) :
    hd2.score (xs1 d w i) (xs1 d w j) =
      2 * ((1 + d) * avg (List.range (w.length + 1)) (flag w)) * (j : ℚ)
        - (1 / ((w.length + 1 : ℕ) : ℚ)) * (j : ℚ) ^ 2 := by
  simp [Head.score, hd2, matVec, qdot, xs1, pos, z11]
  all_goals (try ring)

def ff (n : ℕ) (z : ℚ) (j : ℕ) : ℚ := 2 * z * (j : ℚ) - (1 / (n : ℚ)) * (j : ℚ) ^ 2

def Sfilt (n : ℕ) (z : ℚ) : List ℕ :=
  (List.range n).filter (fun (j : ℕ) => decide (∀ k ∈ List.range n, ff n z k ≤ ff n z j))

def Dfun (n : ℕ) (z : ℚ) : ℚ := -avg (Sfilt n z) (fun j => (-1 : ℚ) ^ j)

theorem hsel (d : ℚ) (w : List ℕ) (i : ℕ) :
    hd2.sel (w.length + 1) (xs1 d w) i =
      Sfilt (w.length + 1) ((1 + d) * avg (List.range (w.length + 1)) (flag w)) := by
  unfold Head.sel Sfilt
  simp only [show hd2.mask = Mask.all from rfl, cand, score2, ff]
  first | rfl | (congr 1; funext j; exact decide_eq_decide.mpr Iff.rfl)

theorem membership : Membership := by
  refine ⟨Dfun, fun d hd => ⟨netd d, net_rel d, ?_⟩⟩
  intro w hv
  have hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4 := hv.2
  have hz : (1 + d) * avg (List.range (w.length + 1)) (flag w)
      = (1 + d) * ((w.countP task.inS : ℕ) : ℚ) / ((w.length : ℚ) + 1) := by
    rw [cq_eq]
    push_cast
    ring
  rw [out_eq d w hw, hsel, hz]
  rfl

end Lane4.Case


namespace Lane4Final
open Lane4.Seq Lane4.Coll

/-- The class is not empty: this network is a member. -/
theorem member : Lane4.Case.task.CountChannel Lane4.Case.net := Lane4.Case.membership

/-- Necessary radius for this network: a relative ball that is correct up to length `L`
has radius below `1 / (2 L - 1)`. -/
theorem radius (τ : ℚ) (L : ℕ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (hL : 2 ≤ L)
    (hb : Lane4.Case.task.OnBall Lane4.Case.net τ L) : τ * (2 * (L : ℚ) - 1) < 1 :=
  Lane4.CollProof.collision_bound Lane4.Case.task 2 1 (by decide) (by decide) (by decide)
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
