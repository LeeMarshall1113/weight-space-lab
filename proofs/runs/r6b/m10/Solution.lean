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
