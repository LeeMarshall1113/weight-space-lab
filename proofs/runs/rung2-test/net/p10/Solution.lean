namespace Lane4.Case
open Lane4.Seq

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

def indq (t : ℕ) : ℚ := if t = 1 ∨ t = 2 then 1 else 0
def ind (w : List ℕ) (j : ℕ) : ℚ := indq (tokAt w j)
def Fq (w : List ℕ) : ℚ := ((w.countP inS : ℕ) : ℚ) / ((w.length : ℚ) + 1)
def x1 (w : List ℕ) (j : ℕ) : Vec := [ind w j, Fq w, 0] ++ pos j (w.length + 1)

theorem sum_getD (g : ℕ → ℚ) (l : List ℕ) :
    ((List.range l.length).map (fun j => g (l.getD j 0))).sum = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    simp only [Function.comp_def, List.getD_cons_zero, List.getD_cons_succ]
    rw [ih, List.map_cons, List.sum_cons]

theorem sum_indq (w : List ℕ) : (w.map indq).sum = ((w.countP inS : ℕ) : ℚ) := by
  induction w with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    have key : inS a = true ↔ (a = 1 ∨ a = 2) := by simp [inS]
    by_cases h : a = 1 ∨ a = 2
    · have h' := key.mpr h
      simp [indq, h, h']
      ring
    · have h' : ¬ (inS a = true) := fun x => h (key.mp x)
      simp [indq, h, h']

theorem sum_ind (w : List ℕ) :
    ((List.range (w.length + 1)).map (ind w)).sum = ((w.countP inS : ℕ) : ℚ) := by
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

theorem init_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) :
    net.init w j = [ind w j, 0, 0] ++ pos j (w.length + 1) := by
  have h3 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 := by
    rcases tokAt_zero_or_mem w j with h | h
    · left; exact h
    · have := hw _ h
      omega
  rcases h3 with h | h | h | h <;> simp [TNet.init, net, ind, indq, h]

theorem b1_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) :
    blk1.apply (w.length + 1) (net.init w) j = x1 w j := by
  have hs : ∀ i k, hd1.score (net.init w i) (net.init w k) = 0 := by
    intro i k
    rw [init_eq w hw i, init_eq w hw k]
    simp [Head.score, hd1, z11, qdot, matVec, pos]
  have hsel : ∀ i, hd1.sel (w.length + 1) (net.init w) i = List.range (w.length + 1) := by
    intro i
    have := sel_all hd1 (w.length + 1) (net.init w) i (fun k _ l _ => by rw [hs, hs])
    rw [this]
    rfl
  have hf : (fun k => qdot [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (net.init w k)) = ind w := by
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
  have hV : hd1.V = [z11, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], z11, z11, z11, z11, z11, z11, z11,
      z11, z11] := rfl
  have attn1 : ∀ i, hd1.attn (w.length + 1) (net.init w) i
      = [0, Fq w, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    intro i
    unfold Head.attn
    rw [hsel i, hV]
    simp only [List.map_cons, List.map_nil, hz, hf, avgF]
  have hh : blk1.heads = [hd1] := rfl
  simp only [Block.apply, hh, List.foldl_cons, List.foldl_nil, attn1]
  rw [init_eq w hw j]
  simp [blk1, x1, qdot, vadd, affine, z11, pos]

theorem score2 (w : List ℕ) (i k : ℕ) :
    hd2.score (x1 w i) (x1 w k)
      = ((w.countP inS : ℕ) : ℚ) / ((w.length : ℚ) + 1) * (k : ℚ)
        + (-1 / 2) * (1 / ((w.length : ℚ) + 1)) * (k : ℚ) ^ 2 := by
  simp [Head.score, hd2, x1, Fq, z11, qdot, matVec, pos]
  try ring

theorem key_ineq (c k N : ℚ) (hN : 0 < N) (hne : c ≠ k) :
    (c / N) * k + (-1 / 2) * (1 / N) * k ^ 2 < (c / N) * c + (-1 / 2) * (1 / N) * c ^ 2 := by
  have hN' := hN.ne'
  have h : (c / N) * c + (-1 / 2) * (1 / N) * c ^ 2 - ((c / N) * k + (-1 / 2) * (1 / N) * k ^ 2)
      = (c - k) ^ 2 / (2 * N) := by
    field_simp
    ring
  have hp : 0 < (c - k) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hne)))
  have h2 : 0 < (c - k) ^ 2 / (2 * N) := div_pos hp (by linarith)
  linarith

theorem b2_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (i : ℕ) :
    blk2.apply (w.length + 1) (x1 w) i
      = [ind w i, Fq w, (-1 : ℚ) ^ (w.countP inS)] ++ pos i (w.length + 1) := by
  have hc : w.countP inS < w.length + 1 := Nat.lt_succ_of_le List.countP_le_length
  have hN : (0 : ℚ) < (w.length : ℚ) + 1 := by positivity
  have hsel : hd2.sel (w.length + 1) (x1 w) i = [w.countP inS] := by
    apply sel_unique hd2 (w.length + 1) (x1 w) i (w.countP inS)
    · exact mem_cand_all.mpr hc
    · intro k hk hkc
      rw [score2, score2]
      exact key_ineq _ _ _ hN (by exact_mod_cast Ne.symm hkc)
  have hV : hd2.V = [z11, z11, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], z11, z11, z11, z11, z11, z11,
      z11, z11] := rfl
  have attn2 : hd2.attn (w.length + 1) (x1 w) i
      = [0, 0, (-1 : ℚ) ^ (w.countP inS), 0, 0, 0, 0, 0, 0, 0, 0] := by
    unfold Head.attn
    rw [hsel, hV]
    simp only [List.map_cons, List.map_nil, avg_singleton]
    simp [x1, qdot, z11, pos]
  have hh : blk2.heads = [hd2] := rfl
  simp only [Block.apply, hh, List.foldl_cons, List.foldl_nil, attn2]
  simp [blk2, x1, qdot, vadd, affine, z11, pos]

theorem out_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (i : ℕ) :
    net.out w i = (-1 : ℚ) ^ (w.countP inS) := by
  have h1 : blk1.apply (w.length + 1) (net.init w) = x1 w := funext (b1_eq w hw)
  have hrun : net.run w = blk2.apply (w.length + 1) (x1 w) := by
    rw [← h1]
    rfl
  unfold TNet.out
  rw [hrun, b2_eq w hw i]
  simp [net, qdot, pos]

theorem net_correct : Statement net := by
  intro w hv
  have hw := hv.2
  rw [out_eq w hw w.length]
  unfold Good
  rcases Nat.even_or_odd (w.countP inS) with h | h
  · rw [h.neg_one_pow]
    have : (w.countP inS) % 2 = 0 := Nat.even_iff.mp h
    norm_num [this]
  · rw [h.neg_one_pow]
    have : (w.countP inS) % 2 = 1 := Nat.odd_iff.mp h
    norm_num [this]

end Lane4.Case
