namespace Lane4.Case
open Lane4.Seq

/-- State: [s, f, g, c, d] ++ 8 position features (width 13). -/
def z13 : Vec := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def e1 : Vec := [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def e2 : Vec := [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def e6 : Vec := [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
def r03 : Vec := [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def outv : Vec := [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- score of key j (query i) = j + i * f_j ; value writes avg of g into slot c. -/
def hd : Head :=
  { A := [z13, z13, z13, z13, z13, e6, e1, z13, z13, z13, z13, z13, z13],
    V := [z13, z13, z13, e2, z13, z13, z13, z13, z13, z13, z13, z13, z13],
    mask := Mask.strict }

def blk : Block :=
  { heads := [hd], W1 := [r03, r03], b1 := [-2, -3],
    W2 := [[0, 0], [0, 0], [0, 0], [0, 0], [-3, 3], [0, 0], [0, 0], [0, 0], [0, 0],
           [0, 0], [0, 0], [0, 0], [0, 0]],
    b2 := z13 }

def net : TNet :=
  { embed := [[0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [1, 1, 0, 0, 0], [2, 0, 0, 0, 0],
              [1, 1, 0, 0, 0], [2, 0, 0, 0, 0], [3, 1, 1, 0, 0], [2, 0, 0, 0, 0],
              [3, 1, 1, 0, 0], [4, 1, 1, 0, 0]],
    blocks := [blk],
    outW := outv,
    outB := 0 }

def sN (w : List ℕ) (j : ℕ) : ℕ := dA (tokAt w j) + dC (tokAt w j)
def gN (w : List ℕ) (j : ℕ) : ℕ := if 3 ≤ sN w j then 1 else 0
def fv (w : List ℕ) (j : ℕ) : ℚ := if sN w j = 2 then 0 else 1

def F (s c : ℚ) : ℚ := s + c - 3 * (max (s + c - 2) 0 - max (s + c - 3) 0)

theorem init_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 9) (j : ℕ) :
    net.init w j = [(sN w j : ℚ), fv w j, (gN w j : ℚ), 0, 0] ++ pos j (w.length + 1) := by
  have h9 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 ∨
      tokAt w j = 5 ∨ tokAt w j = 6 ∨ tokAt w j = 7 ∨ tokAt w j = 8 ∨ tokAt w j = 9 := by
    rcases tokAt_zero_or_mem w j with h | h
    · left; exact h
    · have := hw _ h
      omega
  rcases h9 with h | h | h | h | h | h | h | h | h | h <;>
    simp [TNet.init, net, sN, gN, fv, dA, dC, h]

theorem score_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 9) (i j : ℕ) :
    hd.score (net.init w i) (net.init w j) = (j : ℚ) + (i : ℚ) * fv w j := by
  rw [init_eq w hw i, init_eq w hw j]
  simp [Head.score, hd, z13, e1, e6, qdot, matVec, pos]
  try ring

set_option maxHeartbeats 1000000 in
theorem out_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 9) (i : ℕ) :
    net.out w i = F (sN w i) (avg (hd.sel (w.length + 1) (net.init w) i) (fun j => (gN w j : ℚ))) := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = outv := rfl
  have hc : net.outB = 0 := rfl
  have hf : (fun j => qdot e2 (net.init w j)) = fun j => (gN w j : ℚ) := by
    funext j
    rw [init_eq w hw j]
    simp [qdot, e2, pos]
  have hz : ∀ S : List ℕ, avg S (fun j => qdot z13 (net.init w j)) = 0 := by
    intro S
    have : (fun j => qdot z13 (net.init w j)) = fun _ => (0 : ℚ) := by
      funext j
      rw [init_eq w hw j]
      simp [qdot, z13, pos]
    rw [this, avg_zero]
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [List.foldl, Block.apply, blk, Head.attn, hd, List.map, hf, hz]
  rw [init_eq w hw i]
  simp [qdot, vadd, affine, z13, pos, outv, r03, F]
  try (simp only [max_def]; split_ifs <;> linarith)

theorem sel_last (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 9) (i j0 : ℕ) (hj0 : j0 < i)
    (hf0 : sN w j0 ≠ 2) (hb : ∀ j, j0 < j → j < i → sN w j = 2) :
    hd.sel (w.length + 1) (net.init w) i = [j0] := by
  have hm : hd.mask = Mask.strict := rfl
  have hfv0 : fv w j0 = 1 := by unfold fv; simp [hf0]
  apply sel_unique
  · rw [hm, mem_cand_strict]; exact hj0
  · intro k hk hkj
    rw [hm, mem_cand_strict] at hk
    rw [score_eq w hw, score_eq w hw]
    rcases lt_or_gt_of_ne hkj with hlt | hgt
    · have h1 : (k : ℚ) + 1 ≤ j0 := by exact_mod_cast hlt
      have h2 : fv w k ≤ 1 := by unfold fv; split_ifs <;> norm_num
      have h3 : (0 : ℚ) ≤ i := Nat.cast_nonneg i
      rw [hfv0]
      nlinarith [mul_le_mul_of_nonneg_left h2 h3]
    · have hfk : fv w k = 0 := by unfold fv; simp [hb k hgt hk]
      have h1 : (k : ℚ) + 1 ≤ i := by exact_mod_cast hk
      have h0 : (0 : ℚ) ≤ j0 := Nat.cast_nonneg _
      rw [hfk, hfv0]
      linarith

theorem carryOut_snoc (p : List ℕ) (t : ℕ) :
    carryOut (p ++ [t]) = (dA t + dC t + carryOut p) / 3 := by
  simp [carryOut, List.foldl_append]

theorem take_snoc (w : List ℕ) (k : ℕ) (hk : k < w.length) :
    w.take (k + 1) = w.take k ++ [w[k]] := by
  first
    | exact List.take_succ_eq_append_getElem hk
    | simp [List.take_succ, hk]

theorem sN_succ (w : List ℕ) (k : ℕ) (hk : k < w.length) :
    sN w (k + 1) = dA w[k] + dC w[k] := by
  unfold sN
  rw [tokAt_succ w k hk]

theorem carry_char (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 9) :
    ∀ k, k ≤ w.length → ∃ j0, j0 ≤ k ∧ sN w j0 ≠ 2 ∧ (∀ j, j0 < j → j ≤ k → sN w j = 2) ∧
      gN w j0 = carryOut (w.take k) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨0, le_refl _, ?_, ?_, ?_⟩
    · simp [sN, tokAt_zero, dA, dC]
    · intro j h1 h2
      omega
    · simp [gN, sN, tokAt_zero, dA, dC, carryOut]
  | succ k ih =>
    intro hk
    obtain ⟨j0, hj0, hf0, hb, hg⟩ := ih (by omega)
    have hkl : k < w.length := by omega
    have hmem : w[k] ∈ w := List.getElem_mem hkl
    have ht := hw _ hmem
    have hs := sN_succ w k hkl
    have hcr : carryOut (w.take (k + 1)) = (dA w[k] + dC w[k] + carryOut (w.take k)) / 3 := by
      rw [take_snoc w k hkl]
      exact carryOut_snoc _ _
    have hg1 : gN w j0 ≤ 1 := by unfold gN; split_ifs <;> omega
    have hs4 : dA w[k] + dC w[k] ≤ 4 := by unfold dA dC; omega
    by_cases h2 : dA w[k] + dC w[k] = 2
    · refine ⟨j0, by omega, hf0, ?_, ?_⟩
      · intro j h1 h3
        by_cases hjk : j = k + 1
        · subst hjk
          rw [hs]
          exact h2
        · exact hb j h1 (by omega)
      · omega
    · refine ⟨k + 1, le_refl _, ?_, ?_, ?_⟩
      · rw [hs]
        exact h2
      · intro j h1 h3
        omega
      · unfold gN
        rw [hs]
        split_ifs <;> omega

theorem final_arith (t cr : ℕ) (h1 : 1 ≤ t) (h9 : t ≤ 9) (hc : cr ≤ 1) :
    F ((dA t + dC t : ℕ) : ℚ) (cr : ℚ) = (((dA t + dC t + cr) % 3 : ℕ) : ℚ) := by
  interval_cases t <;> interval_cases cr <;> norm_num [F, dA, dC, max_def]

theorem net_correct : Statement net := by
  intro w hv i hi1 hi2
  have hw := hv.2
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hkl : k < w.length := by omega
  obtain ⟨j0, hj0, hf0, hb, hg⟩ := carry_char w hw k (by omega)
  have hsel := sel_last w hw (k + 1) j0 (by omega) hf0 (fun j h1 h2 => hb j h1 (by omega))
  have hmem : w[k] ∈ w := List.getElem_mem hkl
  have ht := hw _ hmem
  have hc1 : carryOut (w.take k) ≤ 1 := by
    rw [← hg]
    unfold gN
    split_ifs <;> omega
  have hdig : digit w (k + 1) = (dA w[k] + dC w[k] + carryOut (w.take k)) % 3 := by
    unfold digit
    simp [hkl]
  rw [out_eq w hw (k + 1), hsel, avg_singleton, hdig, sN_succ w k hkl]
  simp only [hg]
  exact final_arith w[k] _ ht.1 ht.2 hc1

end Lane4.Case
