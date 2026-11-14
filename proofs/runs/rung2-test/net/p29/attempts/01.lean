namespace Lane4.Case
open Lane4.Seq

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

def Sq (t : ℕ) : ℚ := if t = 2 ∨ t = 3 then 1 else 0

def flag (w : List ℕ) (j : ℕ) : ℚ := Sq (tokAt w j)

def xs1 (w : List ℕ) (j : ℕ) : Vec :=
  [flag w j, avg (List.range (w.length + 1)) (flag w), 0] ++ pos j (w.length + 1)

theorem Sq_inS (t : ℕ) : Sq t = if inS t = true then 1 else 0 := by
  unfold Sq inS
  simp

theorem cnt (w : List ℕ) :
    ((List.range w.length).map (fun j => Sq (w.getD j 0))).sum = (w.countP inS : ℚ) := by
  induction w with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    have hfun : ((fun j => Sq ((a :: t).getD j 0)) ∘ Nat.succ) = fun j => Sq (t.getD j 0) := by
      funext j
      simp
    rw [hfun, ih, List.countP_cons]
    by_cases hi : inS a = true
    · simp [Sq_inS, hi]
      all_goals (try ring)
    · simp [Sq_inS, hi]

theorem cnt_le (w : List ℕ) : w.countP inS ≤ w.length := by
  induction w with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, List.length_cons]
    split_ifs <;> omega

theorem sum_flag (w : List ℕ) :
    ((List.range (w.length + 1)).map (flag w)).sum = (w.countP inS : ℚ) := by
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  have h0 : flag w 0 = 0 := by simp [flag, tokAt, Sq]
  have hfun : (flag w ∘ Nat.succ) = fun j => Sq (w.getD j 0) := by
    funext j
    simp [flag, tokAt]
  rw [h0, hfun, cnt w, zero_add]

theorem cq_eq (w : List ℕ) :
    avg (List.range (w.length + 1)) (flag w) =
      (w.countP inS : ℚ) / ((w.length + 1 : ℕ) : ℚ) := by
  unfold avg
  rw [sum_flag w, List.length_range]

theorem init_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) :
    net.init w j = [flag w j, 0, 0] ++ pos j (w.length + 1) := by
  have h5 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 := by
    rcases tokAt_zero_or_mem w j with h | h
    · left; exact h
    · have := hw _ h
      omega
  rcases h5 with h | h | h | h | h <;> simp [TNet.init, net, flag, Sq, h]

theorem sel1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    hd1.sel (w.length + 1) (net.init w) i = List.range (w.length + 1) := by
  have h := sel_all hd1 (w.length + 1) (net.init w) i (by
    intro k _ l _
    simp [init_eq w hw, Head.score, hd1, matVec, qdot, z11, pos])
  rw [h]
  simp [hd1, cand]

theorem blk1_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) :
    blk1.apply (w.length + 1) (net.init w) = xs1 w := by
  funext i
  have hf : (fun j => qdot e0 (net.init w j)) = flag w := by
    funext j
    rw [init_eq w hw j]
    simp [qdot, e0, pos]
  have hz : ∀ S : List ℕ, avg S (fun j => qdot z11 (net.init w j)) = 0 := by
    intro S
    have : (fun j => qdot z11 (net.init w j)) = fun _ => (0 : ℚ) := by
      funext j
      rw [init_eq w hw j]
      simp [qdot, z11, pos]
    rw [this, avg_zero]
  simp only [List.foldl, Block.apply, blk1, Head.attn, sel1 w hw]
  simp only [hd1, List.map, hf, hz]
  rw [init_eq w hw i]
  simp [xs1, vadd, affine, qdot, z11, pos]
  all_goals (try ring)

theorem out_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    net.out w i = -avg (hd2.sel (w.length + 1) (xs1 w) i) (fun j => (-1 : ℚ) ^ j) := by
  have hb : net.blocks = [blk1, blk2] := rfl
  have ho : net.outW = [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  have hf : (fun j => qdot e7 (xs1 w j)) = fun j => (-1 : ℚ) ^ j := by
    funext j
    simp [xs1, qdot, e7, pos]
  have hz : ∀ S : List ℕ, avg S (fun j => qdot z11 (xs1 w j)) = 0 := by
    intro S
    have : (fun j => qdot z11 (xs1 w j)) = fun _ => (0 : ℚ) := by
      funext j
      simp [xs1, qdot, z11, pos]
    rw [this, avg_zero]
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [List.foldl]
  rw [blk1_eq w hw]
  simp only [Block.apply, blk2, Head.attn]
  generalize hdS : hd2.sel (w.length + 1) (xs1 w) i = S
  simp only [hd2, List.map, hf, hz]
  simp [xs1, vadd, affine, qdot, z11, pos]
  all_goals (try ring)

theorem score2 (w : List ℕ) (i j : ℕ) :
    hd2.score (xs1 w i) (xs1 w j) =
      2 * avg (List.range (w.length + 1)) (flag w) * (j : ℚ)
        - (1 / ((w.length + 1 : ℕ) : ℚ)) * (j : ℚ) ^ 2 := by
  simp [Head.score, hd2, matVec, qdot, xs1, pos, z11]
  all_goals (try ring)

theorem ineq (kn j N : ℚ) (hN : 0 < N) (hne : j ≠ kn) :
    2 * (kn / N) * j - 1 / N * j ^ 2 < 2 * (kn / N) * kn - 1 / N * kn ^ 2 := by
  have hsq : 0 < (j - kn) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hne)))
  have key : (2 * (kn / N) * kn - 1 / N * kn ^ 2) - (2 * (kn / N) * j - 1 / N * j ^ 2)
      = (j - kn) ^ 2 / N := by
    field_simp
    ring
  have := div_pos hsq hN
  linarith

theorem net_correct : Statement net := by
  intro w hv
  have hw := hv.2
  rw [out_eq w hw]
  obtain ⟨kn, hk⟩ : ∃ kn, w.countP inS = kn := ⟨_, rfl⟩
  have hle : kn ≤ w.length := by
    rw [← hk]
    exact cnt_le w
  have hN : (0 : ℚ) < ((w.length + 1 : ℕ) : ℚ) := Nat.cast_pos.2 (Nat.succ_pos _)
  have hsel : hd2.sel (w.length + 1) (xs1 w) w.length = [kn] := by
    refine sel_unique hd2 _ _ _ kn ?_ ?_
    · show kn ∈ cand Mask.all (w.length + 1) w.length
      rw [mem_cand_all]
      omega
    · intro k hk2 hne
      have hk' : k < w.length + 1 := mem_cand_all.1 hk2
      rw [score2, score2, cq_eq w, hk]
      exact ineq _ _ _ hN (by exact_mod_cast hne)
  have hv2 : avg [kn] (fun j => (-1 : ℚ) ^ j) = (-1 : ℚ) ^ kn := avg_singleton _ _
  rw [hsel, hv2]
  have hpar : (0 : ℚ) < -((-1 : ℚ) ^ kn) ↔ kn % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one kn with h | h
    · have he : Even kn := Nat.even_iff.2 h
      rw [he.neg_one_pow]
      norm_num [h]
    · have ho : Odd kn := Nat.odd_iff.2 h
      rw [ho.neg_one_pow]
      norm_num [h]
  rw [hpar]
  unfold Good
  rw [hk]

end Lane4.Case
