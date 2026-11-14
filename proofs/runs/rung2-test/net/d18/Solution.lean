namespace Lane4.Case
open Lane4.Seq

def z12 : Vec := [0,0,0,0,0,0,0,0,0,0,0,0]
def e0 : Vec := [1,0,0,0,0,0,0,0,0,0,0,0]
def e1 : Vec := [0,1,0,0,0,0,0,0,0,0,0,0]
def ne1 : Vec := [0,-1,0,0,0,0,0,0,0,0,0,0]

def hd1 : Head :=
  { A := [z12,z12,z12,z12,z12,z12,z12,z12,z12,z12,z12,z12],
    V := [z12,e0,z12,z12,z12,z12,z12,z12,z12,z12,z12,z12],
    mask := Mask.causal }

def hd2 : Head :=
  { A := [z12,z12,z12,z12,ne1,z12,z12,z12,z12,z12,z12,z12],
    V := [z12,z12,e1,z12,z12,z12,z12,z12,z12,z12,z12,z12],
    mask := Mask.all }

def blk1 : Block :=
  { heads := [hd1], W1 := [z12], b1 := [0],
    W2 := [[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]], b2 := z12 }

def blk2 : Block :=
  { heads := [hd2], W1 := [e1, ne1], b1 := [0,0],
    W2 := [[0,0],[0,0],[0,0],[-1,-1],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]],
    b2 := z12 }

def net : TNet :=
  { embed := [[0,0,0,0],[1,0,0,0],[-1,0,0,0],[0,0,0,0],[1,0,0,0]],
    blocks := [blk1, blk2],
    outW := [0,0,1,1,0,0,0,0,0,0,1/2,0],
    outB := 0 }

def wq (t : ℕ) : ℚ :=
  if t = 1 then 1 else if t = 2 then -1 else if t = 3 then 0 else if t = 4 then 1 else 0

theorem wq_eq (t : ℕ) : wq t = ((wt t : ℤ) : ℚ) := by
  unfold wq wt
  split_ifs <;> simp

def cc (w : List ℕ) (j : ℕ) : ℚ :=
  ((List.range (j+1)).map (fun k => wq (tokAt w k))).sum / ((j:ℚ) + 1)

def x1 (w : List ℕ) (j : ℕ) : Vec :=
  [wq (tokAt w j), cc w j, 0, 0] ++ pos j (w.length + 1)

theorem init_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) :
    net.init w j = [wq (tokAt w j), 0, 0, 0] ++ pos j (w.length + 1) := by
  have h4 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 := by
    rcases tokAt_zero_or_mem w j with h | h
    · left; exact h
    · have := hw _ h
      omega
  rcases h4 with h | h | h | h | h <;> simp [TNet.init, net, wq, h]

theorem score1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i k : ℕ) :
    hd1.score (net.init w i) (net.init w k) = 0 := by
  rw [init_eq w hw i, init_eq w hw k]
  simp [Head.score, hd1, z12, qdot, matVec, pos]

theorem hz1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (S : List ℕ) :
    avg S (fun j => qdot z12 (net.init w j)) = 0 := by
  have : (fun j => qdot z12 (net.init w j)) = fun _ => (0:ℚ) := by
    funext j
    rw [init_eq w hw j]
    simp [qdot, z12, pos]
  rw [this, avg_zero]

theorem sel1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    hd1.sel (w.length+1) (net.init w) i = List.range (i+1) := by
  have h := sel_all hd1 (w.length+1) (net.init w) i
    (by intro k _ l _; rw [score1 w hw i k, score1 w hw i l])
  rw [h]
  first | rfl | simp [hd1, cand]

theorem avg1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    avg (hd1.sel (w.length+1) (net.init w) i) (fun j => qdot e0 (net.init w j)) = cc w i := by
  have hf : (fun j => qdot e0 (net.init w j)) = fun j => wq (tokAt w j) := by
    funext j
    rw [init_eq w hw j]
    simp [qdot, e0, pos]
  rw [sel1 w hw i, hf]
  simp [avg, cc]

theorem x1_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    blk1.apply (w.length+1) (net.init w) i = x1 w i := by
  have hh : blk1.heads = [hd1] := rfl
  have hV : hd1.V = [z12,e0,z12,z12,z12,z12,z12,z12,z12,z12,z12,z12] := rfl
  simp only [Block.apply, hh, List.foldl, Head.attn, hV, List.map, hz1 w hw, avg1 w hw i]
  rw [init_eq w hw i]
  simp [x1, vadd, affine, blk1, qdot, z12, pos]

theorem hz2 (w : List ℕ) (S : List ℕ) :
    avg S (fun j => qdot z12 (x1 w j)) = 0 := by
  have : (fun j => qdot z12 (x1 w j)) = fun _ => (0:ℚ) := by
    funext j
    simp [x1, qdot, z12, pos]
  rw [this, avg_zero]

theorem score2 (w : List ℕ) (i k : ℕ) :
    hd2.score (x1 w i) (x1 w k) = -cc w k := by
  simp [Head.score, hd2, z12, ne1, qdot, matVec, x1, pos]

theorem avg2 (w : List ℕ) (j0 : ℕ) (hj0 : j0 < w.length+1)
    (hmin : ∀ k, k < w.length+1 → cc w j0 ≤ cc w k) (i : ℕ) :
    avg (hd2.sel (w.length+1) (x1 w) i) (fun j => qdot e1 (x1 w j)) = cc w j0 := by
  have hf : (fun j => qdot e1 (x1 w j)) = cc w := by
    funext j
    simp [x1, qdot, e1, pos]
  rw [hf]
  have hne : hd2.sel (w.length+1) (x1 w) i ≠ [] := by
    apply sel_ne_nil
    simp [hd2, cand]
  apply avg_const _ _ _ hne
  intro j hj
  rw [mem_sel] at hj
  have hj0c : j0 ∈ cand hd2.mask (w.length+1) i :=
    (mem_cand_all (n := w.length+1) (i := i) (j := j0)).mpr hj0
  have h1 := hj.2 j0 hj0c
  rw [score2, score2] at h1
  have h2 := hmin j ((mem_cand_all (n := w.length+1) (i := i) (j := j)).mp hj.1)
  linarith

theorem maxabs (c : ℚ) : max c 0 + max (-c) 0 = |c| := by
  rcases le_total c 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]
    ring

theorem out_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j0 : ℕ) (hj0 : j0 < w.length+1)
    (hmin : ∀ k, k < w.length+1 → cc w j0 ≤ cc w k) (i : ℕ) :
    net.out w i = cc w j0 + -(max (cc w i) 0 + max (-cc w i) 0)
      + 1/2 * (1 / ((w.length:ℚ)+1)) := by
  have hx : blk1.apply (w.length+1) (net.init w) = x1 w := funext (x1_eq w hw)
  have hnb : net.blocks = [blk1, blk2] := rfl
  have hno : net.outW = [0,0,1,1,0,0,0,0,0,0,1/2,0] := rfl
  have hnc : net.outB = 0 := rfl
  have hh : blk2.heads = [hd2] := rfl
  have hV : hd2.V = [z12,z12,e1,z12,z12,z12,z12,z12,z12,z12,z12,z12] := rfl
  unfold TNet.out TNet.run
  rw [hnb, hno, hnc]
  simp only [List.foldl]
  rw [hx]
  simp only [Block.apply, hh, List.foldl, Head.attn, hV, List.map, hz2 w, avg2 w j0 hj0 hmin i]
  have hab := maxabs (cc w i)
  simp [vadd, affine, qdot, blk2, e1, ne1, x1, pos, z12] <;> linarith

theorem take_sum (w : List ℕ) : ∀ k, k ≤ w.length →
    ((((w.take k).map wt).sum : ℤ) : ℚ)
      = ((List.range (k+1)).map (fun j => wq (tokAt w j))).sum := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [tokAt_zero, wq]
  | succ k ih =>
    intro hk
    have hk' : k < w.length := by omega
    rw [sum_range_succ (fun j => wq (tokAt w j)) (k+1), ← ih (by omega)]
    beta_reduce
    rw [tokAt_succ w k hk']
    simp only [List.take_add_one, List.getElem?_eq_getElem hk', Option.toList_some,
      List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, wq_eq, Int.cast_add]

theorem cc_eq (w : List ℕ) (k : ℕ) (hk : k ≤ w.length) :
    cc w k = ((((w.take k).map wt).sum : ℤ) : ℚ) / ((k:ℚ)+1) := by
  unfold cc
  rw [take_sum w k hk]

theorem neg_bound (T k N : ℚ) (hk : 0 ≤ k) (hkN : k + 1 ≤ N) (hT : T ≤ -1) :
    T / (k+1) ≤ -(1/N) := by
  have hk1 : 0 < k + 1 := by linarith
  have hN : 0 < N := by linarith
  rw [div_le_iff₀ hk1]
  have h1 : (k+1)/N ≤ 1 := (div_le_one hN).mpr hkN
  have e : -(1/N) * (k+1) = -((k+1)/N) := by ring
  rw [e]
  linarith

theorem net_correct : Statement net := by
  intro w hv
  have hw := hv.2
  obtain ⟨j0, hj0, hmin⟩ :=
    Finset.exists_min_image (Finset.range (w.length+1)) (cc w) ⟨0, by simp⟩
  have hj0' : j0 < w.length+1 := Finset.mem_range.mp hj0
  have hmin' : ∀ k, k < w.length+1 → cc w j0 ≤ cc w k :=
    fun k hk => hmin k (Finset.mem_range.mpr hk)
  rw [out_eq w hw j0 hj0' hmin' w.length]
  unfold Good
  have hN : (0:ℚ) < (w.length:ℚ)+1 := by positivity
  have hc0 : cc w 0 = 0 := by
    rw [cc_eq w 0 (Nat.zero_le _)]
    simp
  have hm0 : cc w j0 ≤ 0 := by
    have := hmin' 0 (by omega)
    linarith
  have ht : 0 < 1/((w.length:ℚ)+1) := by positivity
  have ha := le_max_right (cc w w.length) 0
  have hb := le_max_right (-cc w w.length) 0
  have ha' := le_max_left (cc w w.length) 0
  have hb' := le_max_left (-cc w w.length) 0
  have hLw : w.take w.length = w := by simp
  have hL' : cc w w.length = (((w.map wt).sum : ℤ) : ℚ) / ((w.length:ℚ)+1) := by
    rw [cc_eq w w.length le_rfl, hLw]
  constructor
  · intro hpos
    by_contra hG
    have hcase : (∃ k, k ≤ w.length ∧ ((w.take k).map wt).sum < 0) ∨ ((w.map wt).sum ≠ 0) := by
      by_contra hcon
      push_neg at hcon
      exact hG ⟨hcon.1, hcon.2⟩
    rcases hcase with ⟨k, hk, hneg⟩ | hne
    · have hT : ((((w.take k).map wt).sum : ℤ) : ℚ) ≤ -1 := by
        have : ((w.take k).map wt).sum ≤ -1 := by omega
        exact_mod_cast this
      have hkq : (k:ℚ) ≤ w.length := by exact_mod_cast hk
      have hb2 := neg_bound _ (k:ℚ) ((w.length:ℚ)+1) (Nat.cast_nonneg k) (by linarith) hT
      rw [← cc_eq w k hk] at hb2
      have := hmin' k (by omega)
      linarith
    · rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hT : (((w.map wt).sum : ℤ) : ℚ) ≤ -1 := by
          have : (w.map wt).sum ≤ -1 := by omega
          exact_mod_cast this
        have h3 := neg_bound _ (w.length:ℚ) ((w.length:ℚ)+1) (Nat.cast_nonneg _) le_rfl hT
        rw [← hL'] at h3
        linarith
      · have hT : (1:ℚ) ≤ (((w.map wt).sum : ℤ) : ℚ) := by
          have : 1 ≤ (w.map wt).sum := by omega
          exact_mod_cast this
        have h3 : 1/((w.length:ℚ)+1) ≤ cc w w.length := by
          rw [hL']
          first
            | exact div_le_div_of_nonneg_right hT hN.le
            | simpa [div_eq_mul_inv] using
                mul_le_mul_of_nonneg_right hT (inv_nonneg.mpr hN.le)
        linarith
  · rintro ⟨hall, htot⟩
    have hcn : ∀ k, k ≤ w.length → 0 ≤ cc w k := by
      intro k hk
      rw [cc_eq w k hk]
      apply div_nonneg
      · exact_mod_cast hall k hk
      · positivity
    have hm : cc w j0 = 0 := le_antisymm hm0 (hcn j0 (by omega))
    have hL0 : cc w w.length = 0 := by
      rw [hL', htot]
      simp
    rw [hm, hL0]
    simp only [neg_zero, max_self]
    linarith

end Lane4.Case
