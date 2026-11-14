namespace Lane4.Case
open Lane4.Seq

def zv : Vec := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def eA0 : Vec := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def eA2 : Vec := [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- head 1: causal, uniform scores, writes the average weight into slot 1 -/
def hd1 : Head :=
  { A := [zv, zv, zv, zv, zv, zv, zv, zv, zv, zv, zv, zv, zv, zv],
    V := [zv, eA0, zv, zv, zv, zv, zv, zv, zv, zv, zv, zv, zv, zv],
    mask := Mask.causal }

def blk1 : Block :=
  { heads := [hd1],
    W1 := [[0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    b1 := [0, 0],
    W2 := [[0, 0], [0, 0], [1, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0],
           [0, 0], [0, 0], [0, 0], [0, 0]],
    b2 := zv }

/-- head 2: all positions, score = slot 2 of the key, writes max into slot 4 -/
def hd2 : Head :=
  { A := [zv, zv, zv, zv, zv, zv, eA2, zv, zv, zv, zv, zv, zv, zv],
    V := [zv, zv, zv, zv, eA2, zv, zv, zv, zv, zv, zv, zv, zv, zv],
    mask := Mask.all }

def blk2 : Block :=
  { heads := [hd2],
    W1 := [[0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 1 / 2, 0]],
    b1 := [0],
    W2 := [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
    b2 := zv }

def net : TNet :=
  { embed := [[0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0],
              [-1, 0, 0, 0, 0, 0]],
    blocks := [blk1, blk2],
    outW := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    outB := 0 }

def wq (w : List ℕ) (j : ℕ) : ℚ := ((wt (tokAt w j) : ℤ) : ℚ)

def av (w : List ℕ) (k : ℕ) : ℚ := avg (List.range (k + 1)) (wq w)

def x1 (w : List ℕ) : ℕ → Vec := Block.apply blk1 (w.length + 1) (net.init w)

theorem init_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) :
    net.init w j = [wq w j, 0, 0, 0, 0, 0] ++ pos j (w.length + 1) := by
  have h5 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 := by
    rcases tokAt_zero_or_mem w j with h | h
    · left; exact h
    · have := hw _ h
      omega
  rcases h5 with h | h | h | h | h <;> simp [TNet.init, net, wq, wt, h]

theorem sel1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) :
    hd1.sel (w.length + 1) (net.init w) j = List.range (j + 1) := by
  have h := sel_all hd1 (w.length + 1) (net.init w) j (by
    intro k _ l _
    simp [Head.score, init_eq w hw, hd1, zv, qdot, matVec, pos])
  rw [h]
  simp [hd1, cand]

theorem x1_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) :
    x1 w j = [wq w j, av w j, max (-(av w j)) 0, max (av w j) 0, 0, 0] ++ pos j (w.length + 1) := by
  have hf : (fun k => qdot eA0 (net.init w k)) = wq w := by
    funext k
    rw [init_eq w hw k]
    simp [qdot, eA0, pos]
  have hz : ∀ S : List ℕ, avg S (fun k => qdot zv (net.init w k)) = 0 := by
    intro S
    have : (fun k => qdot zv (net.init w k)) = fun _ => (0 : ℚ) := by
      funext k
      rw [init_eq w hw k]
      simp [qdot, zv, pos]
    rw [this, avg_zero]
  unfold x1
  simp only [Block.apply, blk1, List.foldl, Head.attn, sel1 w hw]
  simp only [hd1, List.map, hf, hz]
  rw [init_eq w hw j]
  simp [qdot, vadd, affine, zv, pos, av]

theorem score2 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i k : ℕ) :
    hd2.score (x1 w i) (x1 w k) = max (-(av w k)) 0 := by
  rw [x1_eq w hw i, x1_eq w hw k]
  simp [Head.score, hd2, zv, eA2, qdot, matVec, pos]

theorem out_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    net.out w i = max (-(max (av w i) 0)
      - avg (hd2.sel (w.length + 1) (x1 w) i) (fun k => max (-(av w k)) 0)
      + 1 / 2 * (1 / ((w.length : ℚ) + 1))) 0 := by
  have hf : (fun k => qdot eA2 (x1 w k)) = fun k => max (-(av w k)) 0 := by
    funext k
    rw [x1_eq w hw k]
    simp [qdot, eA2, pos]
  have hz : ∀ S : List ℕ, avg S (fun k => qdot zv (x1 w k)) = 0 := by
    intro S
    have : (fun k => qdot zv (x1 w k)) = fun _ => (0 : ℚ) := by
      funext k
      rw [x1_eq w hw k]
      simp [qdot, zv, pos]
    rw [this, avg_zero]
  have hrun : net.run w = Block.apply blk2 (w.length + 1) (x1 w) := rfl
  unfold TNet.out
  rw [hrun]
  simp only [Block.apply, blk2, List.foldl, Head.attn]
  generalize hd2.sel (w.length + 1) (x1 w) i = S
  simp only [hd2, List.map, hf, hz]
  rw [x1_eq w hw i]
  simp [net, qdot, vadd, affine, zv, pos]
  congr 1
  ring

theorem sumq (w : List ℕ) (k : ℕ) (hk : k ≤ w.length) :
    ((List.range (k + 1)).map (wq w)).sum = ((((w.take k).map wt).sum : ℤ) : ℚ) := by
  induction k with
  | zero => simp [wq, tokAt_zero, wt]
  | succ k ih =>
    rw [sum_range_succ (wq w) (k + 1), ih (by omega)]
    have ht : ((w.take (k + 1)).map wt).sum = ((w.take k).map wt).sum + wt w[k] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
        List.map_append, List.sum_append]
      simp
    have hq : wq w (k + 1) = ((wt w[k] : ℤ) : ℚ) := by
      simp [wq, tokAt_succ w k (by omega)]
    rw [hq, ht]
    push_cast
    ring

theorem av_eq (w : List ℕ) (k : ℕ) (hk : k ≤ w.length) :
    av w k = ((((w.take k).map wt).sum : ℤ) : ℚ) / ((k : ℚ) + 1) := by
  unfold av avg
  rw [sumq w k hk]
  simp

theorem key1 (T : ℤ) (k : ℕ) (m : ℚ) (hkm : (k : ℚ) + 1 ≤ m)
    (h : -((T : ℚ) / ((k : ℚ) + 1)) < 1 / 2 * (1 / m)) : 0 ≤ T := by
  by_contra hT
  push_neg at hT
  have hT1 : (T : ℚ) ≤ -1 := by exact_mod_cast (by omega : T ≤ -1)
  have hk0 : (0 : ℚ) < (k : ℚ) + 1 := by positivity
  have hm0 : 0 < m := lt_of_lt_of_le hk0 hkm
  have hmne : m ≠ 0 := hm0.ne'
  have hkne : (k : ℚ) + 1 ≠ 0 := hk0.ne'
  have hTu : ((T : ℚ) / ((k : ℚ) + 1)) * ((k : ℚ) + 1) = T := by field_simp
  have hvm : (1 / 2 * (1 / m) : ℚ) * m = 1 / 2 := by field_simp
  have hv0 : (0 : ℚ) < 1 / 2 * (1 / m) := by positivity
  generalize (T : ℚ) / ((k : ℚ) + 1) = u at h hTu
  generalize (1 / 2 * (1 / m) : ℚ) = v at h hvm hv0
  have h1 : (-u) * ((k : ℚ) + 1) < v * ((k : ℚ) + 1) := mul_lt_mul_of_pos_right h hk0
  have h2 : v * ((k : ℚ) + 1) ≤ v * m := mul_le_mul_of_nonneg_left hkm hv0.le
  nlinarith [h1, h2, hvm, hTu, hT1]

theorem key2 (T : ℤ) (m : ℚ) (hm0 : 0 < m)
    (h : (T : ℚ) / m < 1 / 2 * (1 / m)) : T ≤ 0 := by
  by_contra hT
  push_neg at hT
  have hT1 : (1 : ℚ) ≤ T := by exact_mod_cast (by omega : (1 : ℤ) ≤ T)
  have hmne : m ≠ 0 := hm0.ne'
  have hTu : ((T : ℚ) / m) * m = T := by field_simp
  have hvm : (1 / 2 * (1 / m) : ℚ) * m = 1 / 2 := by field_simp
  generalize (T : ℚ) / m = u at h hTu
  generalize (1 / 2 * (1 / m) : ℚ) = v at h hvm
  have h1 : u * m < v * m := mul_lt_mul_of_pos_right h hm0
  nlinarith [h1, hvm, hTu, hT1]

theorem net_correct : Statement net := by
  intro w hv
  obtain ⟨hne, hw⟩ := hv
  have hsne : hd2.sel (w.length + 1) (x1 w) w.length ≠ [] := by
    apply sel_ne_nil
    simp [hd2, cand]
  have hmem : ∀ j ∈ hd2.sel (w.length + 1) (x1 w) w.length,
      j < w.length + 1 ∧ ∀ k, k < w.length + 1 → max (-(av w k)) 0 ≤ max (-(av w j)) 0 := by
    intro j hj
    rw [mem_sel] at hj
    obtain ⟨hc, hm⟩ := hj
    refine ⟨mem_cand_all.mp hc, ?_⟩
    intro k hk
    have := hm k (mem_cand_all.mpr hk)
    rw [score2 w hw, score2 w hw] at this
    exact this
  obtain ⟨j0, hj0⟩ := List.exists_mem_of_ne_nil _ hsne
  have hM : avg (hd2.sel (w.length + 1) (x1 w) w.length) (fun k => max (-(av w k)) 0)
      = max (-(av w j0)) 0 :=
    avg_const _ _ _ hsne (fun j hj =>
      le_antisymm ((hmem j0 hj0).2 j (hmem j hj).1) ((hmem j hj).2 j0 (hmem j0 hj0).1))
  rw [out_eq w hw w.length, hM]
  have hc : (0 : ℚ) < 1 / 2 * (1 / ((w.length : ℚ) + 1)) := by positivity
  have htake : w.take w.length = w := by simp
  unfold Good
  constructor
  · intro h
    rw [lt_max_iff] at h
    rcases h with h | h
    · have hA0 : 0 ≤ max (av w w.length) 0 := le_max_right _ _
      have hB0 : 0 ≤ max (-(av w j0)) 0 := le_max_right _ _
      have hAlt : max (av w w.length) 0 < 1 / 2 * (1 / ((w.length : ℚ) + 1)) := by linarith
      have hBlt : max (-(av w j0)) 0 < 1 / 2 * (1 / ((w.length : ℚ) + 1)) := by linarith
      have hnn : ∀ k, k ≤ w.length → 0 ≤ ((w.take k).map wt).sum := by
        intro k hk
        have hfk : max (-(av w k)) 0 ≤ max (-(av w j0)) 0 := (hmem j0 hj0).2 k (by omega)
        have h1 : -(av w k) < 1 / 2 * (1 / ((w.length : ℚ) + 1)) :=
          lt_of_le_of_lt (le_trans (le_max_left _ _) hfk) hBlt
        rw [av_eq w k hk] at h1
        have hkq : (k : ℚ) ≤ (w.length : ℚ) := by exact_mod_cast hk
        exact key1 _ k ((w.length : ℚ) + 1) (by linarith) h1
      refine ⟨hnn, ?_⟩
      have h2 : av w w.length < 1 / 2 * (1 / ((w.length : ℚ) + 1)) :=
        lt_of_le_of_lt (le_max_left _ _) hAlt
      rw [av_eq w w.length le_rfl] at h2
      have hle := key2 _ ((w.length : ℚ) + 1) (by positivity) h2
      have hge := hnn w.length le_rfl
      rw [htake] at hle hge
      omega
    · exact absurd h (lt_irrefl 0)
  · rintro ⟨hpre, htot⟩
    have hnn : ∀ k, k ≤ w.length → 0 ≤ av w k := by
      intro k hk
      rw [av_eq w k hk]
      exact div_nonneg (by exact_mod_cast hpre k hk) (by positivity)
    have hj0lt := (hmem j0 hj0).1
    have h1 : max (-(av w j0)) 0 = 0 := max_eq_right (by linarith [hnn j0 (by omega)])
    have hlast : av w w.length = 0 := by
      rw [av_eq w w.length le_rfl, htake, htot]
      simp
    rw [h1, hlast]
    apply lt_max_of_lt_left
    linarith [max_self (0 : ℚ)]

end Lane4.Case
