namespace Lane4.Case
open Lane4.Seq

def qz : Vec := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def qW2 : List Vec := [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]

def qh1 : Head :=
  { A := [qz, qz, qz, qz, qz, qz, qz, qz, qz, qz, qz],
    V := [qz, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], qz, qz, qz, qz, qz, qz, qz, qz, qz],
    mask := Mask.all }

def qh2 : Head :=
  { A := [qz, [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], qz, qz, qz, qz, qz, qz, qz,
          [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], qz],
    V := [qz, qz, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], qz, qz, qz, qz, qz, qz, qz, qz],
    mask := Mask.all }

def qb1 : Block :=
  { heads := [qh1], W1 := [qz], b1 := [0], W2 := qW2, b2 := qz }

def qb2 : Block :=
  { heads := [qh2], W1 := [qz], b1 := [0], W2 := qW2, b2 := qz }

def net : TNet :=
  { embed := [[0, 0, 0], [1, 0, 0], [1, 0, 0], [0, 0, 0], [0, 0, 0]],
    blocks := [qb1, qb2],
    outW := [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    outB := 0 }

def qind (t : ℕ) : ℚ := if inS t = true then 1 else 0

def qflag (w : List ℕ) (j : ℕ) : ℚ := qind (tokAt w j)

def qrr (w : List ℕ) : ℚ := avg (List.range (w.length + 1)) (qflag w)

def qY (w : List ℕ) (j : ℕ) : Vec := [qflag w j, qrr w, 0] ++ pos j (w.length + 1)

theorem cand_h1 (n i : ℕ) : cand qh1.mask n i = List.range n := rfl
theorem cand_h2 (n i : ℕ) : cand qh2.mask n i = List.range n := rfl

theorem qcnt (w : List ℕ) :
    ((List.range w.length).map (fun k => qind (w.getD k 0))).sum = (w.countP inS : ℚ) := by
  induction w with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    have h : (fun k => qind ((a :: t).getD k 0)) ∘ Nat.succ = fun k => qind (t.getD k 0) := by
      funext k
      simp
    rw [h, ih, List.countP_cons]
    by_cases ha : inS a = true
    · simp [qind, ha] <;> ring
    · simp [qind, ha] <;> ring

theorem qsumflag (w : List ℕ) :
    ((List.range (w.length + 1)).map (qflag w)).sum = (w.countP inS : ℚ) := by
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  have h0 : qflag w 0 = 0 := by simp [qflag, qind, tokAt_zero, inS]
  have h1 : (qflag w ∘ Nat.succ) = fun k => qind (w.getD k 0) := by
    funext k
    simp [qflag, tokAt]
  rw [h0, h1, qcnt, zero_add]

theorem qrr_eq (w : List ℕ) :
    qrr w = (w.countP inS : ℚ) / ((w.length : ℚ) + 1) := by
  unfold qrr avg
  rw [qsumflag w, List.length_range] <;> norm_num

theorem qinit_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) :
    net.init w j = [qflag w j, 0, 0] ++ pos j (w.length + 1) := by
  have h5 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 := by
    rcases tokAt_zero_or_mem w j with h | h
    · left; exact h
    · have := hw _ h
      omega
  rcases h5 with h | h | h | h | h <;> simp [TNet.init, net, qflag, qind, inS, h]

theorem qscore1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i k : ℕ) :
    qh1.score (net.init w i) (net.init w k) = 0 := by
  rw [qinit_eq w hw i, qinit_eq w hw k]
  simp [Head.score, qh1, matVec, qdot, qz, pos]

theorem qsel1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    qh1.sel (w.length + 1) (net.init w) i = List.range (w.length + 1) := by
  have heq : ∀ k ∈ cand qh1.mask (w.length + 1) i, ∀ l ∈ cand qh1.mask (w.length + 1) i,
      qh1.score (net.init w i) (net.init w k) = qh1.score (net.init w i) (net.init w l) := by
    intro k _ l _
    rw [qscore1 w hw i k, qscore1 w hw i l]
  rw [sel_all qh1 _ _ i heq, cand_h1]

theorem qblk1_apply (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    qb1.apply (w.length + 1) (net.init w) i = qY w i := by
  have hz : ∀ S : List ℕ, avg S (fun k => qdot qz (net.init w k)) = 0 := by
    intro S
    have : (fun k => qdot qz (net.init w k)) = fun _ => (0 : ℚ) := by
      funext k
      rw [qinit_eq w hw k]
      simp [qdot, qz, pos]
    rw [this, avg_zero]
  have hf : (fun k => qdot [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (net.init w k)) = qflag w := by
    funext k
    rw [qinit_eq w hw k]
    simp [qdot, pos]
  have hV : qh1.V = [qz, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], qz, qz, qz, qz, qz, qz, qz, qz, qz] :=
    rfl
  simp only [Block.apply, qb1, Head.attn, hV, qsel1 w hw, List.map, hz, hf, List.foldl]
  rw [qinit_eq w hw i]
  simp [qdot, vadd, affine, qz, qW2, pos, qY, qrr]

theorem qscore2 (w : List ℕ) (i k : ℕ) :
    qh2.score (qY w i) (qY w k) =
      -((k : ℚ) ^ 2) * (1 / ((w.length : ℚ) + 1)) + 2 * qrr w * k := by
  simp [Head.score, qh2, matVec, qdot, qz, pos, qY] <;> ring

theorem qineq (L c k : ℕ) (hne : k ≠ c) :
    -((k : ℚ) ^ 2) * (1 / ((L : ℚ) + 1)) + 2 * ((c : ℚ) / ((L : ℚ) + 1)) * k <
      -((c : ℚ) ^ 2) * (1 / ((L : ℚ) + 1)) + 2 * ((c : ℚ) / ((L : ℚ) + 1)) * c := by
  have hN : (0 : ℚ) < (L : ℚ) + 1 := by positivity
  have hkc : (k : ℚ) ≠ c := by exact_mod_cast hne
  have hsq : 0 < ((k : ℚ) - c) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hkc)))
  have hpos : 0 < ((k : ℚ) - c) ^ 2 * (1 / ((L : ℚ) + 1)) :=
    mul_pos hsq (one_div_pos.mpr hN)
  have key : (-((c : ℚ) ^ 2) * (1 / ((L : ℚ) + 1)) + 2 * ((c : ℚ) / ((L : ℚ) + 1)) * c) -
      (-((k : ℚ) ^ 2) * (1 / ((L : ℚ) + 1)) + 2 * ((c : ℚ) / ((L : ℚ) + 1)) * k) =
      ((k : ℚ) - c) ^ 2 * (1 / ((L : ℚ) + 1)) := by ring
  linarith

theorem qsel2 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    qh2.sel (w.length + 1) (qY w) i = [w.countP inS] := by
  refine sel_unique _ _ _ _ _ ?_ ?_
  · rw [cand_h2, List.mem_range]
    have : w.countP inS ≤ w.length := by
      first
        | exact List.countP_le_length _
        | exact List.countP_le_length
    omega
  · intro k _ hne
    rw [qscore2 w i k, qscore2 w i (w.countP inS), qrr_eq w]
    exact qineq w.length (w.countP inS) k hne

theorem qout_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    net.out w i = (-1 : ℚ) ^ (w.countP inS) := by
  have hb : net.blocks = [qb1, qb2] := rfl
  have ho : net.outW = [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  have hY : qb1.apply (w.length + 1) (net.init w) = qY w := funext (qblk1_apply w hw)
  have hz : ∀ S : List ℕ, avg S (fun k => qdot qz (qY w k)) = 0 := by
    intro S
    have : (fun k => qdot qz (qY w k)) = fun _ => (0 : ℚ) := by
      funext k
      simp [qdot, qz, pos, qY]
    rw [this, avg_zero]
  have hf : (fun k => qdot [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] (qY w k)) =
      fun k => (-1 : ℚ) ^ k := by
    funext k
    simp [qdot, pos, qY]
  have hV : qh2.V = [qz, qz, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], qz, qz, qz, qz, qz, qz, qz, qz] :=
    rfl
  have hsel := qsel2 w hw i
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [List.foldl, hY]
  simp only [Block.apply, qb2, Head.attn, hV, hsel, List.map, hz, hf, List.foldl]
  simp [qdot, vadd, affine, qz, qW2, pos, qY, avg_singleton]

theorem net_correct : Statement net := by
  intro w hv
  have hw := hv.2
  rw [qout_eq w hw w.length]
  unfold Good
  rcases Nat.even_or_odd (w.countP inS) with h | h
  · rw [h.neg_one_pow]
    have h2 : w.countP inS % 2 = 0 := Nat.even_iff.mp h
    simp [h2]
  · rw [h.neg_one_pow]
    have h2 : w.countP inS % 2 = 1 := Nat.odd_iff.mp h
    simp [h2]

end Lane4.Case
