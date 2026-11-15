/- EXAMPLE (reference only, not imported): the kernel-checked rung-2 proof that this same network
computes the parity task. Its Spec was:

namespace Lane4.Case
open Lane4.Seq

def Valid (w : List ℕ) : Prop := w ≠ [] ∧ ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4

def inS (t : ℕ) : Bool := t == 1 || t == 3 || t == 4
def Good (w : List ℕ) : Prop := (w.countP inS) % 2 = 0

def Statement (N : TNet) : Prop :=
  ∀ w : List ℕ, Valid w → (0 < N.out w w.length ↔ Good w)

end Lane4.Case

-/

namespace Lane4.Case
open Lane4.Seq

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

def sf (w : List ℕ) (j : ℕ) : ℚ := if inS (tokAt w j) = true then 1 else 0

def X1 (w : List ℕ) (j : ℕ) : Vec :=
  [sf w j, avg (List.range (w.length + 1)) (sf w), 0] ++ pos j (w.length + 1)

theorem cnt_le : ∀ w : List ℕ, w.countP inS ≤ w.length
  | [] => by simp
  | a :: t => by
    have := cnt_le t
    rw [List.countP_cons]
    simp only [List.length_cons]
    split <;> omega

theorem sumC : ∀ w : List ℕ,
    (w.map (fun t => if inS t = true then (1 : ℚ) else 0)).sum = (w.countP inS : ℚ)
  | [] => by simp
  | a :: t => by
    rw [List.map_cons, List.sum_cons, sumC t, List.countP_cons]
    by_cases h : inS a = true <;> simp [h] <;> ring

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
    ((List.range (w.length + 1)).map (sf w)).sum = (w.countP inS : ℚ) := by
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  have h0 : sf w 0 = 0 := by simp [sf, tokAt_zero, inS]
  have h1 : (sf w ∘ Nat.succ) = fun j => (fun t => if inS t = true then (1 : ℚ) else 0)
      (w.getD j 0) := by
    funext j
    simp [sf, tokAt, Function.comp_def]
  rw [h0, h1, sumA (fun t => if inS t = true then (1 : ℚ) else 0) w, sumC w]
  ring

theorem avg_eq (w : List ℕ) :
    avg (List.range (w.length + 1)) (sf w) = (w.countP inS : ℚ) / ((w.length : ℚ) + 1) := by
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
  rcases h5 with h | h | h | h | h <;> simp [TNet.init, net, sf, inS, h]

theorem score1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i j : ℕ) :
    hd1.score (net.init w i) (net.init w j) = 0 := by
  rw [init_eq w hw i, init_eq w hw j]
  simp [Head.score, hd1, z11, qdot, matVec, pos]

theorem hsel1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    hd1.sel (w.length + 1) (net.init w) i = List.range (w.length + 1) := by
  have := sel_all hd1 (w.length + 1) (net.init w) i
    (by intro a _ b _; rw [score1 w hw, score1 w hw])
  exact this.trans (by simp [hd1, cand])

theorem hz (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (S : List ℕ) :
    avg S (fun j => qdot z11 (net.init w j)) = 0 := by
  have : (fun j => qdot z11 (net.init w j)) = fun _ => (0 : ℚ) := by
    funext j
    rw [init_eq w hw j]
    simp [qdot, z11, pos]
  rw [this, avg_zero]

theorem hf1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) :
    (fun j => qdot e0 (net.init w j)) = sf w := by
  funext j
  rw [init_eq w hw j]
  simp [qdot, e0, pos]

theorem attn1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    hd1.attn (w.length + 1) (net.init w) i
      = [0, avg (List.range (w.length + 1)) (sf w), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold Head.attn
  rw [hsel1 w hw i]
  simp only [hd1, List.map, hz w hw, hf1 w hw]

theorem hx1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) :
    Block.apply blk1 (w.length + 1) (net.init w) = X1 w := by
  funext i
  simp only [Block.apply, blk1, List.foldl, attn1 w hw]
  rw [init_eq w hw i]
  simp [vadd, affine, qdot, z11, pos, X1]

theorem score2 (w : List ℕ) (i j : ℕ) :
    hd2.score (X1 w i) (X1 w j)
      = 2 * avg (List.range (w.length + 1)) (sf w) * (j : ℚ)
        - 1 / ((w.length : ℚ) + 1) * (j : ℚ) ^ 2 := by
  simp [Head.score, hd2, a4, a5, z11, qdot, matVec, X1, pos]
  <;> push_cast <;> ring

theorem hsel2 (w : List ℕ) :
    hd2.sel (w.length + 1) (X1 w) w.length = [w.countP inS] := by
  have hk := cnt_le w
  apply sel_unique
  · simp [hd2, cand]
    omega
  · intro j hj hne
    have hjlt : j < w.length + 1 := by simpa [hd2, cand] using hj
    rw [score2, score2, avg_eq]
    have hN : (0 : ℚ) < (w.length : ℚ) + 1 := by positivity
    have hne' : (j : ℚ) - (w.countP inS : ℕ) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast hne
    have hp : 0 < ((j : ℚ) - (w.countP inS : ℕ)) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne'))
    have heq : 2 * ((w.countP inS : ℕ) / ((w.length : ℚ) + 1)) * ((w.countP inS : ℕ) : ℚ)
        - 1 / ((w.length : ℚ) + 1) * ((w.countP inS : ℕ) : ℚ) ^ 2
        - (2 * ((w.countP inS : ℕ) / ((w.length : ℚ) + 1)) * (j : ℚ)
        - 1 / ((w.length : ℚ) + 1) * (j : ℚ) ^ 2)
        = ((j : ℚ) - (w.countP inS : ℕ)) ^ 2 / ((w.length : ℚ) + 1) := by
      field_simp
      ring
    have := div_pos hp hN
    linarith

theorem attn2 (w : List ℕ) :
    hd2.attn (w.length + 1) (X1 w) w.length
      = [0, 0, (-1 : ℚ) ^ (w.countP inS), 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold Head.attn
  rw [hsel2 w]
  simp only [hd2, List.map, avg_singleton]
  simp [X1, qdot, pos, z11, e7]

theorem out_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) :
    net.out w w.length = (-1 : ℚ) ^ (w.countP inS) := by
  have hb : net.blocks = [blk1, blk2] := rfl
  have ho : net.outW = e2 := rfl
  have hc : net.outB = 0 := rfl
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [List.foldl]
  rw [hx1 w hw]
  simp only [Block.apply, blk2, List.foldl, attn2 w]
  simp [qdot, vadd, affine, z11, e2, pos, X1]

theorem net_correct : Statement net := by
  intro w hv
  have hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4 := hv.2
  rw [out_eq w hw]
  unfold Good
  constructor
  · intro h
    by_contra hne
    have hodd : Odd (w.countP inS) := Nat.odd_iff.mpr (by omega)
    rw [hodd.neg_one_pow] at h
    linarith
  · intro h
    have hev : Even (w.countP inS) := Nat.even_iff.mpr h
    rw [hev.neg_one_pow]
    norm_num

end Lane4.Case
