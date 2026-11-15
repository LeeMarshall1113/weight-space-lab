namespace Lane4.Case
open Lane4.Seq

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

def bosf (w : List ℕ) (j : ℕ) : ℚ := if tokAt w j = 0 then 1 else 0
def onef (w : List ℕ) (j : ℕ) : ℚ := if tokAt w j = 1 then 1 else 0

def cf (w : List ℕ) : ℚ :=
  ((w.countP (fun s => decide (s = 1)) : ℕ) : ℚ) / ((w.length + 1 : ℕ) : ℚ)

def hval (w : List ℕ) (j : ℕ) : ℚ :=
  max (cf w - (j : ℚ) / ((w.length + 1 : ℕ) : ℚ) + 1 / ((w.length + 1 : ℕ) : ℚ)) 0

def x1 (w : List ℕ) (j : ℕ) : Vec :=
  [bosf w j, onef w j, cf w, hval w j, 0, 0] ++ pos j (w.length + 1)

theorem init_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (j : ℕ) :
    net.init w j = [bosf w j, onef w j, 0, 0, 0, 0] ++ pos j (w.length + 1) := by
  have h3 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 := by
    rcases tokAt_zero_or_mem w j with h | h
    · left; exact h
    · have := hw _ h
      omega
  rcases h3 with h | h | h <;> simp [TNet.init, net, bosf, onef, h]

theorem sum_one (L : List ℕ) :
    ((List.range L.length).map (fun j => if L.getD j 0 = 1 then (1:ℚ) else 0)).sum
      = ((L.countP (fun s => decide (s = 1)) : ℕ) : ℚ) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have h1 : ((List.range (a :: L).length).map
        (fun j => if (a :: L).getD j 0 = 1 then (1:ℚ) else 0)).sum
        = (if a = 1 then (1:ℚ) else 0)
          + ((List.range L.length).map (fun j => if L.getD j 0 = 1 then (1:ℚ) else 0)).sum := by
      rw [List.length_cons, List.range_succ_eq_map]
      simp [Function.comp_def]
    rw [h1, ih, List.countP_cons]
    by_cases ha : a = 1 <;> simp [ha] <;> ring

theorem sum_onef (w : List ℕ) :
    ((List.range (w.length + 1)).map (onef w)).sum
      = ((w.countP (fun s => decide (s = 1)) : ℕ) : ℚ) := by
  have hf : onef w = fun j => if (0 :: w).getD j 0 = 1 then (1:ℚ) else 0 := by
    funext j; rfl
  have h := sum_one (0 :: w)
  rw [List.length_cons] at h
  rw [hf, h, List.countP_cons]
  simp

theorem avg_onef (w : List ℕ) : avg (List.range (w.length + 1)) (onef w) = cf w := by
  unfold avg cf
  rw [sum_onef, List.length_range]

theorem score1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (i k : ℕ) :
    hd1.score (net.init w i) (net.init w k) = 0 := by
  rw [init_eq w hw i, init_eq w hw k]
  simp [Head.score, hd1, z14, qdot, matVec, pos]

theorem qz (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (j : ℕ) :
    qdot z14 (net.init w j) = 0 := by
  rw [init_eq w hw j]
  simp [qdot, z14, pos]

theorem qe1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (j : ℕ) :
    qdot e1 (net.init w j) = onef w j := by
  rw [init_eq w hw j]
  simp [qdot, e1, pos]

theorem attn1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (i : ℕ) :
    hd1.attn (w.length + 1) (net.init w) i = [0,0,cf w,0,0,0,0,0,0,0,0,0,0,0] := by
  have hsel : hd1.sel (w.length + 1) (net.init w) i = List.range (w.length + 1) :=
    sel_all hd1 (w.length + 1) (net.init w) i
      (fun k _ l _ => by rw [score1 w hw, score1 w hw])
  have hz : ∀ S : List ℕ, avg S (fun j => qdot z14 (net.init w j)) = 0 := by
    intro S
    have : (fun j => qdot z14 (net.init w j)) = fun _ => (0 : ℚ) := funext (qz w hw)
    rw [this, avg_zero]
  have hone : avg (List.range (w.length + 1)) (fun j => qdot e1 (net.init w j)) = cf w := by
    have : (fun j => qdot e1 (net.init w j)) = onef w := funext (qe1 w hw)
    rw [this, avg_onef]
  unfold Head.attn
  rw [hsel]
  simp only [hd1, List.map_cons, List.map_nil, hz, hone]

theorem blk1_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (i : ℕ) :
    blk1.apply (w.length + 1) (net.init w) i = x1 w i := by
  have hh : blk1.heads = [hd1] := rfl
  have hY : vadd ([bosf w i, onef w i, 0, 0, 0, 0] ++ pos i (w.length + 1))
      [0,0,cf w,0,0,0,0,0,0,0,0,0,0,0]
      = [bosf w i, onef w i, cf w, 0, 0, 0] ++ pos i (w.length + 1) := by
    simp [vadd, pos]
  have hid : (affine blk1.W1 blk1.b1
      ([bosf w i, onef w i, cf w, 0, 0, 0] ++ pos i (w.length + 1))).map (fun v => max v 0)
      = [hval w i] := by
    have e : qdot rowM ([bosf w i, onef w i, cf w, 0, 0, 0] ++ pos i (w.length + 1))
        = cf w - (i : ℚ) / ((w.length + 1 : ℕ) : ℚ) + 1 / ((w.length + 1 : ℕ) : ℚ) := by
      simp [qdot, rowM, pos] <;> ring
    simp only [affine, blk1, List.zipWith_cons_cons, List.zipWith_nil_left, List.map_cons,
      List.map_nil, e, add_zero, hval]
  have hout : affine blk1.W2 blk1.b2 [hval w i]
      = [0,0,0,hval w i,0,0,0,0,0,0,0,0,0,0] := by
    simp [affine, blk1, qdot, z14]
  simp only [Block.apply, hh, List.foldl_cons, List.foldl_nil]
  rw [attn1 w hw i, init_eq w hw i, hY, hid, hout]
  simp [vadd, pos, x1]

theorem qz1 (w : List ℕ) (j : ℕ) : qdot z14 (x1 w j) = 0 := by
  simp [qdot, z14, x1, pos]

theorem qe0 (w : List ℕ) (j : ℕ) : qdot e0 (x1 w j) = bosf w j := by
  simp [qdot, e0, x1, pos]

theorem score2 (w : List ℕ) (i k : ℕ) :
    hd2.score (x1 w i) (x1 w k) = hval w i * bosf w k := by
  simp [Head.score, hd2, z14, e0, qdot, matVec, x1, pos]

theorem attn2 (w : List ℕ) (i : ℕ) :
    hd2.attn (w.length + 1) (x1 w) i
      = [0,0,0,0, avg (hd2.sel (w.length + 1) (x1 w) i) (bosf w), 0,0,0,0,0,0,0,0,0] := by
  have hz : ∀ S : List ℕ, avg S (fun j => qdot z14 (x1 w j)) = 0 := by
    intro S
    have : (fun j => qdot z14 (x1 w j)) = fun _ => (0 : ℚ) := funext (qz1 w)
    rw [this, avg_zero]
  have hb : ∀ S : List ℕ, avg S (fun j => qdot e0 (x1 w j)) = avg S (bosf w) := by
    intro S
    have : (fun j => qdot e0 (x1 w j)) = bosf w := funext (qe0 w)
    rw [this]
  unfold Head.attn
  generalize hd2.sel (w.length + 1) (x1 w) i = S
  simp only [hd2, List.map_cons, List.map_nil, hz, hb]

theorem blk2_eq (w : List ℕ) (i : ℕ) :
    blk2.apply (w.length + 1) (x1 w) i
      = [bosf w i, onef w i, cf w, hval w i,
         avg (hd2.sel (w.length + 1) (x1 w) i) (bosf w),
         max (-2 * avg (hd2.sel (w.length + 1) (x1 w) i) (bosf w) + 1) 0]
        ++ pos i (w.length + 1) := by
  have hh : blk2.heads = [hd2] := rfl
  have hat := attn2 w i
  simp only [Block.apply, hh, List.foldl_cons, List.foldl_nil, hat]
  generalize avg (hd2.sel (w.length + 1) (x1 w) i) (bosf w) = a
  have hY : vadd (x1 w i) [0,0,0,0,a,0,0,0,0,0,0,0,0,0]
      = [bosf w i, onef w i, cf w, hval w i, a, 0] ++ pos i (w.length + 1) := by
    simp [vadd, x1, pos]
  have hid : (affine blk2.W1 blk2.b1
      ([bosf w i, onef w i, cf w, hval w i, a, 0] ++ pos i (w.length + 1))).map
        (fun v => max v 0) = [max (-2 * a + 1) 0] := by
    have e : qdot rowR ([bosf w i, onef w i, cf w, hval w i, a, 0] ++ pos i (w.length + 1))
        = -2 * a := by
      simp [qdot, rowR, pos] <;> ring
    simp only [affine, blk2, List.zipWith_cons_cons, List.zipWith_nil_left, List.map_cons,
      List.map_nil, e]
  have hout : affine blk2.W2 blk2.b2 [max (-2 * a + 1) 0]
      = [0,0,0,0,0,max (-2 * a + 1) 0,0,0,0,0,0,0,0,0] := by
    simp [affine, blk2, qdot, z14]
  rw [hY, hid, hout]
  simp [vadd, pos]

theorem out_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (i : ℕ) :
    net.out w i = 3 - 2 * avg (hd2.sel (w.length + 1) (x1 w) i) (bosf w)
      - max (-2 * avg (hd2.sel (w.length + 1) (x1 w) i) (bosf w) + 1) 0 := by
  have hb : net.blocks = [blk1, blk2] := rfl
  have hx1 : blk1.apply (w.length + 1) (net.init w) = x1 w := funext (blk1_eq w hw)
  have ho : net.outW = [0,0,0,0,-2,-1,0,0,0,0,0,0,0,0] := rfl
  have hc : net.outB = 3 := rfl
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [List.foldl_cons, List.foldl_nil, hx1, blk2_eq w i]
  generalize avg (hd2.sel (w.length + 1) (x1 w) i) (bosf w) = a
  simp [qdot, pos]
  try ring

theorem bosf_zero (w : List ℕ) : bosf w 0 = 1 := by
  simp [bosf, tokAt_zero]

theorem bosf_pos (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (j : ℕ) (hj0 : 0 < j)
    (hj : j < w.length + 1) : bosf w j = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hk : k < w.length := by omega
  unfold bosf
  rw [tokAt_succ w k hk]
  have h := hw w[k] (List.getElem_mem hk)
  have h2 : w[k] ≠ 0 := by omega
  simp [h2]

theorem sum_bosf (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) :
    ((List.range (w.length + 1)).map (bosf w)).sum = 1 := by
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, bosf_zero]
  have h0 : ((List.map Nat.succ (List.range w.length)).map (bosf w)).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [List.mem_map] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    exact bosf_pos w hw (j.succ) (Nat.succ_pos j) (by have := List.mem_range.mp hj; omega)
  linarith

theorem rank_one (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (i c : ℕ) (hi1 : 1 ≤ i)
    (hc : w.countP (fun s => decide (s = 1)) = c) (hic : i ≤ c) : IsRank w i 1 := by
  unfold IsRank
  have h0 : w.countP (fun s => decide (s < 1)) = 0 := by
    rw [List.countP_eq_zero]
    intro a ha
    have := hw a ha
    simp only [decide_eq_true_eq]
    omega
  have h1 : w.countP (fun s => decide (s ≤ 1)) = w.countP (fun s => decide (s = 1)) := by
    apply List.countP_congr
    intro a ha
    have := hw a ha
    simp only [decide_eq_true_eq]
    omega
  constructor
  · omega
  · omega

theorem rank_two (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (i c : ℕ) (hiN : i ≤ w.length)
    (hc : w.countP (fun s => decide (s = 1)) = c) (hic : c < i) : IsRank w i 2 := by
  unfold IsRank
  have h1 : w.countP (fun s => decide (s < 2)) = w.countP (fun s => decide (s = 1)) := by
    apply List.countP_congr
    intro a ha
    have := hw a ha
    simp only [decide_eq_true_eq]
    omega
  have h2 : w.countP (fun s => decide (s ≤ 2)) = w.length := by
    rw [List.countP_eq_length]
    intro a ha
    have := hw a ha
    simp only [decide_eq_true_eq]
    omega
  constructor
  · omega
  · omega

theorem net_correct : Statement net := by
  intro w hv i hi1 hiN
  have hw := hv.2
  have hlen : 1 ≤ w.length := by
    cases w with
    | nil => exact absurd rfl hv.1
    | cons a t => simp
  have hN2 : (2 : ℚ) ≤ ((w.length + 1 : ℕ) : ℚ) := by
    have : (1 : ℚ) ≤ w.length := by exact_mod_cast hlen
    push_cast
    linarith
  have hNpos : (0 : ℚ) < ((w.length + 1 : ℕ) : ℚ) := by linarith
  have hcand : ∀ k, k ∈ cand hd2.mask (w.length + 1) i ↔ k < w.length + 1 :=
    fun k => mem_cand_all
  rw [out_eq w hw i]
  obtain ⟨c, hc⟩ : ∃ c, w.countP (fun s => decide (s = 1)) = c := ⟨_, rfl⟩
  have hcf : cf w = (c : ℚ) / ((w.length + 1 : ℕ) : ℚ) := by
    unfold cf
    rw [hc]
  have e : cf w - (i : ℚ) / ((w.length + 1 : ℕ) : ℚ) + 1 / ((w.length + 1 : ℕ) : ℚ)
      = ((c : ℚ) - i + 1) / ((w.length + 1 : ℕ) : ℚ) := by
    rw [hcf]; ring
  by_cases hic : i ≤ c
  · have hic' : (i : ℚ) ≤ (c : ℚ) := by exact_mod_cast hic
    have hpos : 0 < hval w i := by
      unfold hval
      apply lt_max_of_lt_left
      rw [e]
      apply div_pos
      · linarith
      · exact hNpos
    have hsel : hd2.sel (w.length + 1) (x1 w) i = [0] := by
      refine sel_unique hd2 (w.length + 1) (x1 w) i 0 ?_ ?_
      · exact (hcand 0).mpr (by omega)
      · intro k hk hk0
        have hk' := (hcand k).mp hk
        rw [score2 w, score2 w, bosf_zero, bosf_pos w hw k (Nat.pos_of_ne_zero hk0) hk']
        simpa using hpos
    have ha : avg (hd2.sel (w.length + 1) (x1 w) i) (bosf w) = 1 := by
      rw [hsel, avg_singleton, bosf_zero]
    rw [ha]
    have hm : max ((-2 : ℚ) * 1 + 1) 0 = 0 := max_eq_right (by norm_num)
    refine ⟨1, ?_, rank_one w hw i c hi1 hc hic⟩
    rw [hm]
    norm_num
  · have hlt : c < i := by omega
    have hlt' : (c : ℚ) + 1 ≤ (i : ℚ) := by exact_mod_cast hlt
    have hz : hval w i = 0 := by
      unfold hval
      apply max_eq_right
      rw [e]
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith
      · exact hNpos.le
    have hsel : hd2.sel (w.length + 1) (x1 w) i = List.range (w.length + 1) :=
      sel_all hd2 (w.length + 1) (x1 w) i
        (fun k _ l _ => by rw [score2 w, score2 w, hz]; simp)
    have ha : avg (hd2.sel (w.length + 1) (x1 w) i) (bosf w)
        = 1 / ((w.length + 1 : ℕ) : ℚ) := by
      rw [hsel]
      unfold avg
      rw [sum_bosf w hw, List.length_range]
    rw [ha]
    have h12 : 1 / ((w.length + 1 : ℕ) : ℚ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hN2
    have hm : max (-2 * (1 / ((w.length + 1 : ℕ) : ℚ)) + 1) 0
        = -2 * (1 / ((w.length + 1 : ℕ) : ℚ)) + 1 :=
      max_eq_left (by linarith)
    refine ⟨2, ?_, rank_two w hw i c hiN hc hlt⟩
    rw [hm]
    push_cast
    ring

end Lane4.Case

namespace Lane4.Case
open Lane4.Seq

/-- `net` with one weight changed: block 0 W1[0][12] multiplied by (1 + 1/200). -/
def netP : TNet :=
  { embed := [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]],
    blocks := [{ heads := [{ A := [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], V := [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], mask := Mask.all }], W1 := [[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, (201 / 200 : ℚ), (-1 : ℚ)]], b1 := [0], W2 := [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]], b2 := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] },
      { heads := [{ A := [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], V := [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], mask := Mask.all }], W1 := [[0, 0, 0, 0, (-2 : ℚ), 0, 0, 0, 0, 0, 0, 0, 0, 0]], b1 := [1], W2 := [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]], b2 := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }],
    outW := [0, 0, 0, 0, (-2 : ℚ), (-1 : ℚ), 0, 0, 0, 0, 0, 0, 0, 0],
    outB := 3 }

/-- The changed network is inside the relative ball of radius 1/200 around `net`, zeros fixed. -/
theorem witness_close : netClose net netP = true := by decide +kernel

/-- On the input `[2]`, the correct output at position 1 is 2 ... -/
theorem witness_target : IsRank [2] 1 2 := by unfold IsRank; decide

/-- ... and the changed network's output there is at least 1/2 away from it. -/
theorem witness_off : |netP.out [2] 1 - (2 : ℚ)| ≥ 1 / 2 := by decide +kernel

end Lane4.Case
