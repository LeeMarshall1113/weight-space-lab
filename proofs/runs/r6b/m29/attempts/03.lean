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
