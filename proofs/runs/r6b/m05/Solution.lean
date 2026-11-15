namespace Lane4.Case
open Lane4.Seq Lane4.Coll

def v1 (d : ℚ) : Vec := [1 + d, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def hd1' (d : ℚ) : Head :=
  { A := [z11, z11, z11, z11, z11, z11, z11, z11, z11, z11, z11],
    V := [z11, v1 d, z11, z11, z11, z11, z11, z11, z11, z11, z11],
    mask := Mask.all }

def blk1' (d : ℚ) : Block :=
  { heads := [hd1' d], W1 := [z11], b1 := [0],
    W2 := [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]], b2 := z11 }

def net' (d : ℚ) : TNet :=
  { embed := [[0, 0, 0], [1, 0, 0], [0, 0, 0], [1, 0, 0], [1, 0, 0]],
    blocks := [blk1' d, blk2],
    outW := e2,
    outB := 0 }

/-! ### relative ball -/

theorem qRel_refl (τ : ℚ) (hτ : 0 ≤ τ) (a : ℚ) : qRel τ a a := by
  unfold qRel
  rw [sub_self, abs_zero]
  exact mul_nonneg hτ (abs_nonneg a)

theorem vRel_refl (τ : ℚ) (hτ : 0 ≤ τ) : ∀ l : List ℚ, vRel τ l l
  | [] => List.Forall₂.nil
  | a :: t => List.Forall₂.cons (qRel_refl τ hτ a) (vRel_refl τ hτ t)

theorem mRel_refl (τ : ℚ) (hτ : 0 ≤ τ) : ∀ l : List (List ℚ), mRel τ l l
  | [] => List.Forall₂.nil
  | a :: t => List.Forall₂.cons (vRel_refl τ hτ a) (mRel_refl τ hτ t)

theorem hRel_refl (τ : ℚ) (hτ : 0 ≤ τ) (h : Head) : hRel τ h h :=
  ⟨mRel_refl τ hτ _, mRel_refl τ hτ _, rfl⟩

theorem hsRel_refl (τ : ℚ) (hτ : 0 ≤ τ) : ∀ l : List Head, List.Forall₂ (hRel τ) l l
  | [] => List.Forall₂.nil
  | a :: t => List.Forall₂.cons (hRel_refl τ hτ a) (hsRel_refl τ hτ t)

theorem bRel_refl (τ : ℚ) (hτ : 0 ≤ τ) (B : Block) : bRel τ B B :=
  ⟨hsRel_refl τ hτ _, mRel_refl τ hτ _, vRel_refl τ hτ _, mRel_refl τ hτ _,
    vRel_refl τ hτ _⟩

theorem vRel_v1 (d : ℚ) : vRel |d| e0 (v1 d) := by
  simp [vRel, e0, v1, qRel, List.forall₂_cons]

theorem netRel_net (d : ℚ) : netRel |d| net (net' d) := by
  have hτ : 0 ≤ |d| := abs_nonneg d
  refine ⟨mRel_refl |d| hτ _, ?_, vRel_refl |d| hτ _, qRel_refl |d| hτ _⟩
  refine List.Forall₂.cons ?_ (List.Forall₂.cons (bRel_refl |d| hτ _) List.Forall₂.nil)
  refine ⟨List.Forall₂.cons ?_ List.Forall₂.nil, mRel_refl |d| hτ _, vRel_refl |d| hτ _,
    mRel_refl |d| hτ _, vRel_refl |d| hτ _⟩
  refine ⟨mRel_refl |d| hτ _, ?_, rfl⟩
  exact List.Forall₂.cons (vRel_refl |d| hτ _) (List.Forall₂.cons (vRel_v1 d)
    (mRel_refl |d| hτ _))

/-! ### the computation -/

def sf (w : List ℕ) (j : ℕ) : ℚ := if task.inS (tokAt w j) = true then 1 else 0

def Zf (d : ℚ) (w : List ℕ) : ℚ := (1 + d) * (((w.countP task.inS : ℕ) : ℚ) / ((w.length : ℚ) + 1))

def X1d (d : ℚ) (w : List ℕ) (j : ℕ) : Vec :=
  [sf w j, Zf d w, 0] ++ pos j (w.length + 1)

def ff (n : ℕ) (z : ℚ) (j : ℕ) : ℚ := 2 * z * (j : ℚ) - 1 / (n : ℚ) * (j : ℚ) ^ 2

def Dsel (n : ℕ) (z : ℚ) : List ℕ :=
  (List.range n).filter (fun j => decide (∀ k ∈ List.range n, ff n z k ≤ ff n z j))

def Dfun (n : ℕ) (z : ℚ) : ℚ := avg (Dsel n z) (fun j => (-1 : ℚ) ^ j)

theorem avg_mul (S : List ℕ) (f : ℕ → ℚ) (c : ℚ) : avg S (fun j => c * f j) = c * avg S f := by
  unfold avg
  rw [List.sum_map_mul_left]
  ring

theorem sumC (p : ℕ → Bool) : ∀ w : List ℕ,
    (w.map (fun t => if p t = true then (1 : ℚ) else 0)).sum = (w.countP p : ℚ)
  | [] => by simp
  | a :: t => by
    rw [List.map_cons, List.sum_cons, sumC p t, List.countP_cons]
    by_cases h : p a = true <;> simp [h] <;> ring

theorem sumA (g : ℕ → ℚ) : ∀ w : List ℕ,
    ((List.range w.length).map (fun j => g (w.getD j 0))).sum = (w.map g).sum
  | [] => by simp
  | a :: t => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons,
      List.map_map, List.map_cons, List.sum_cons]
    have := sumA g t
    simp only [Function.comp_def, List.getD_cons_succ, List.getD_cons_zero]
    rw [this]

theorem sum_sf (w : List ℕ) :
    ((List.range (w.length + 1)).map (sf w)).sum = (w.countP task.inS : ℚ) := by
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  have h0 : sf w 0 = 0 := by simp [sf, tokAt_zero, task]
  have h1 : (sf w ∘ Nat.succ) = fun j => (fun t => if task.inS t = true then (1 : ℚ) else 0)
      (w.getD j 0) := by
    funext j
    simp [sf, tokAt, Function.comp_def]
  rw [h0, h1, sumA (fun t => if task.inS t = true then (1 : ℚ) else 0) w, sumC task.inS w]
  ring

theorem avg_eq (w : List ℕ) :
    avg (List.range (w.length + 1)) (sf w) = (w.countP task.inS : ℚ) / ((w.length : ℚ) + 1) := by
  unfold avg
  rw [sum_sf, List.length_range]
  push_cast <;> ring

theorem init_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) :
    net.init w j = [sf w j, 0, 0] ++ pos j (w.length + 1) := by
  have h5 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨
      tokAt w j = 4 := by
    rcases tokAt_zero_or_mem w j with h | h
    · left; exact h
    · have := hw _ h
      omega
  rcases h5 with h | h | h | h | h <;> simp [TNet.init, net, sf, task, h]

theorem score1' (d : ℚ) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i j : ℕ) :
    (hd1' d).score (net.init w i) (net.init w j) = 0 := by
  rw [init_eq w hw i, init_eq w hw j]
  simp [Head.score, hd1', z11, qdot, matVec, pos]

theorem hsel1' (d : ℚ) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    (hd1' d).sel (w.length + 1) (net.init w) i = List.range (w.length + 1) := by
  have := sel_all (hd1' d) (w.length + 1) (net.init w) i
    (by intro a _ b _; rw [score1' d w hw, score1' d w hw])
  exact this.trans (by simp [hd1', cand])

theorem hz (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (S : List ℕ) :
    avg S (fun j => qdot z11 (net.init w j)) = 0 := by
  have : (fun j => qdot z11 (net.init w j)) = fun _ => (0 : ℚ) := by
    funext j
    rw [init_eq w hw j]
    simp [qdot, z11, pos]
  rw [this, avg_zero]

theorem hv1 (d : ℚ) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) :
    (fun j => qdot (v1 d) (net.init w j)) = fun j => (1 + d) * sf w j := by
  funext j
  rw [init_eq w hw j]
  simp [qdot, v1, pos]

theorem hA1 (d : ℚ) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) :
    avg (List.range (w.length + 1)) (fun j => qdot (v1 d) (net.init w j)) = Zf d w := by
  rw [hv1 d w hw, avg_mul, avg_eq]
  rfl

theorem attn1' (d : ℚ) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    (hd1' d).attn (w.length + 1) (net.init w) i
      = [0, Zf d w, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold Head.attn
  rw [hsel1' d w hw i]
  simp only [hd1', List.map, hz w hw, hA1 d w hw]

theorem hx1' (d : ℚ) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) :
    Block.apply (blk1' d) (w.length + 1) ((net' d).init w) = X1d d w := by
  have hi : (net' d).init w = net.init w := rfl
  rw [hi]
  funext i
  simp only [Block.apply, blk1', List.foldl, attn1' d w hw]
  rw [init_eq w hw i]
  simp [vadd, affine, qdot, z11, pos, X1d]

theorem score2' (d : ℚ) (w : List ℕ) (i j : ℕ) :
    hd2.score (X1d d w i) (X1d d w j)
      = ff (w.length + 1) (Zf d w) j := by
  simp [Head.score, hd2, a4, a5, z11, qdot, matVec, X1d, pos, ff]
  <;> push_cast <;> ring

theorem hsel2' (d : ℚ) (w : List ℕ) (i : ℕ) :
    hd2.sel (w.length + 1) (X1d d w) i = Dsel (w.length + 1) (Zf d w) := by
  have hm : hd2.mask = Mask.all := rfl
  unfold Head.sel
  rw [hm]
  simp only [cand]
  unfold Dsel
  apply List.filter_congr
  intro j _
  apply decide_eq_decide.mpr
  constructor
  · intro h k hk
    have := h k hk
    rw [score2', score2'] at this
    exact this
  · intro h k hk
    rw [score2', score2']
    exact h k hk

theorem attn2' (d : ℚ) (w : List ℕ) :
    hd2.attn (w.length + 1) (X1d d w) w.length
      = [0, 0, Dfun (w.length + 1) (Zf d w), 0, 0, 0, 0, 0, 0, 0, 0] := by
  have h0 : (fun j => qdot z11 (X1d d w j)) = fun _ => (0 : ℚ) := by
    funext j
    simp [X1d, qdot, z11, pos]
  have h7 : (fun j => qdot e7 (X1d d w j)) = fun j => (-1 : ℚ) ^ j := by
    funext j
    simp [X1d, qdot, e7, pos]
  unfold Head.attn
  rw [hsel2' d w w.length]
  simp only [hd2, List.map, h0, h7, avg_zero]
  rfl

theorem out_eq' (d : ℚ) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) :
    (net' d).out w w.length = Dfun (w.length + 1) (Zf d w) := by
  have hb : (net' d).blocks = [blk1' d, blk2] := rfl
  have ho : (net' d).outW = e2 := rfl
  have hc : (net' d).outB = 0 := rfl
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [List.foldl]
  rw [hx1' d w hw]
  simp only [Block.apply, blk2, List.foldl, attn2' d w]
  generalize Dfun (w.length + 1) (Zf d w) = t
  simp [qdot, vadd, affine, z11, e2, pos, X1d]

theorem membership : Membership := by
  refine ⟨Dfun, fun d _ => ⟨net' d, netRel_net d, ?_⟩⟩
  intro w hv
  rw [out_eq' d w hv.2]
  have : Zf d w = (1 + d) * ((w.countP task.inS : ℕ) : ℚ) / ((w.length : ℚ) + 1) := by
    unfold Zf
    ring
  rw [this]

end Lane4.Case
