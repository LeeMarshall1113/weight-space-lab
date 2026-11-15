namespace Lane4.Case
open Lane4.Seq

def npf (t : ℕ) : ℚ := if t = 0 ∨ t = 1 ∨ t = 4 then 1 else 0
def gN (t : ℕ) : ℕ := if t = 4 then 1 else 0
def gf (t : ℕ) : ℚ := (gN t : ℚ)
def af (t : ℕ) : ℚ := if t = 3 ∨ t = 4 then 1 else 0
def cf (t : ℕ) : ℚ := if t = 2 ∨ t = 4 then 1 else 0

def zz : Vec := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def eG : Vec := [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def rA6 : Vec := [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
def rA7 : Vec := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def r1 : Vec := [0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def hd : Head :=
  { A := [zz, zz, zz, zz, zz, zz, rA6, rA7, zz, zz, zz, zz, zz, zz],
    V := [zz, zz, zz, zz, eG, zz, zz, zz, zz, zz, zz, zz, zz, zz],
    mask := Mask.strict }

def blk : Block :=
  { heads := [hd], W1 := [r1, r1, r1], b1 := [0, -1, -2],
    W2 := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [1, -2, 2], [0, 0, 0],
           [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]],
    b2 := zz }

def net : TNet :=
  { embed := [[1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0],
              [0, 0, 1, 0, 0, 0], [1, 1, 1, 1, 0, 0]],
    blocks := [blk],
    outW := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    outB := 0 }

theorem init_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) :
    net.init w j = [npf (tokAt w j), gf (tokAt w j), af (tokAt w j), cf (tokAt w j), 0, 0]
      ++ pos j (w.length + 1) := by
  have h5 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 := by
    rcases tokAt_zero_or_mem w j with h | h
    · left; exact h
    · have := hw _ h
      omega
  rcases h5 with h | h | h | h | h <;> simp [TNet.init, net, npf, gf, gN, af, cf, h]

theorem score_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i j : ℕ) :
    hd.score (net.init w i) (net.init w j) = ((i : ℚ) + 1) * npf (tokAt w j) + (j : ℚ) := by
  rw [init_eq w hw i, init_eq w hw j]
  simp [Head.score, hd, zz, rA6, rA7, qdot, matVec, pos] <;> ring

theorem attn_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    hd.attn (w.length + 1) (net.init w) i =
      [0, 0, 0, 0, avg (hd.sel (w.length + 1) (net.init w) i) (fun j => gf (tokAt w j)),
       0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold Head.attn
  generalize hd.sel (w.length + 1) (net.init w) i = S
  have hV : hd.V = [zz, zz, zz, zz, eG, zz, zz, zz, zz, zz, zz, zz, zz, zz] := rfl
  have hz : ∀ S : List ℕ, avg S (fun j => qdot zz (net.init w j)) = 0 := by
    intro S
    have : (fun j => qdot zz (net.init w j)) = fun _ => (0 : ℚ) := by
      funext j
      rw [init_eq w hw j]
      simp [qdot, zz, pos]
    rw [this, avg_zero]
  have hg : (fun j => qdot eG (net.init w j)) = fun j => gf (tokAt w j) := by
    funext j
    rw [init_eq w hw j]
    simp [qdot, eG, pos]
  rw [hV]
  simp only [List.map, hz, hg]

theorem sel_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (m j : ℕ) (hj : j < m + 1)
    (hnp : npf (tokAt w j) = 1) (hbt : ∀ k, j < k → k < m + 1 → npf (tokAt w k) = 0) :
    hd.sel (w.length + 1) (net.init w) (m + 1) = [j] := by
  have hmk : hd.mask = Mask.strict := rfl
  apply sel_unique
  · rw [hmk, mem_cand_strict]; exact hj
  · intro k hk hkj
    rw [hmk, mem_cand_strict] at hk
    rw [score_eq w hw, score_eq w hw, hnp]
    have c1 : (k : ℚ) < (m : ℚ) + 1 := by exact_mod_cast hk
    have c0 : (0 : ℚ) ≤ (m : ℚ) := Nat.cast_nonneg m
    have c2 : (0 : ℚ) ≤ (j : ℚ) := Nat.cast_nonneg j
    push_cast
    rcases lt_or_gt_of_ne hkj with hlt | hgt
    · have c3 : (k : ℚ) < (j : ℚ) := by exact_mod_cast hlt
      have hk01 : npf (tokAt w k) = 0 ∨ npf (tokAt w k) = 1 := by
        unfold npf; split_ifs <;> simp
      rcases hk01 with h | h <;> rw [h] <;> linarith
    · rw [hbt k hgt hk]
      linarith

theorem carry_succ (w : List ℕ) (m : ℕ) (h : m < w.length) :
    carryOut (w.take (m + 1)) =
      (dA (tokAt w (m + 1)) + dC (tokAt w (m + 1)) + carryOut (w.take m)) / 2 := by
  rw [tokAt_succ w m h]
  unfold carryOut
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.foldl_append]
  rfl

theorem key (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) : ∀ m, m + 1 ≤ w.length →
    ∃ j, j < m + 1 ∧ npf (tokAt w j) = 1 ∧
      (∀ k, j < k → k < m + 1 → npf (tokAt w k) = 0) ∧
      gN (tokAt w j) = carryOut (w.take m) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨0, by omega, ?_, ?_, ?_⟩
    · simp [tokAt_zero, npf]
    · intro k hk hk'; omega
    · simp [tokAt_zero, gN, carryOut]
  | succ m ih =>
    intro hm
    obtain ⟨j, hj, h1, h2, h3⟩ := ih (by omega)
    have hlt : m < w.length := by omega
    have ht : 1 ≤ tokAt w (m + 1) ∧ tokAt w (m + 1) ≤ 4 := by
      rw [tokAt_succ w m hlt]; exact hw _ (List.getElem_mem hlt)
    have hc1 : carryOut (w.take m) ≤ 1 := by
      rw [← h3]; unfold gN; split_ifs <;> omega
    have hcs := carry_succ w m hlt
    have h4 : tokAt w (m + 1) = 1 ∨ tokAt w (m + 1) = 2 ∨ tokAt w (m + 1) = 3 ∨
        tokAt w (m + 1) = 4 := by omega
    rcases h4 with h | h | h | h
    · refine ⟨m + 1, by omega, ?_, ?_, ?_⟩
      · simp [npf, h]
      · intro k hk hk'; omega
      · rw [hcs, h]; norm_num [gN, dA, dC] <;> omega
    · refine ⟨j, by omega, h1, ?_, ?_⟩
      · intro k hk hk'
        by_cases hk2 : k = m + 1
        · rw [hk2, h]; norm_num [npf]
        · exact h2 k hk (by omega)
      · rw [hcs, h, h3]; norm_num [dA, dC] <;> omega
    · refine ⟨j, by omega, h1, ?_, ?_⟩
      · intro k hk hk'
        by_cases hk2 : k = m + 1
        · rw [hk2, h]; norm_num [npf]
        · exact h2 k hk (by omega)
      · rw [hcs, h, h3]; norm_num [dA, dC] <;> omega
    · refine ⟨m + 1, by omega, ?_, ?_, ?_⟩
      · simp [npf, h]
      · intro k hk hk'; omega
      · rw [hcs, h]; norm_num [gN, dA, dC] <;> omega

theorem net_correct : Statement net := by
  intro w hv i h1 h2
  obtain ⟨hne, hw⟩ := hv
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j, hj, hnp, hbt, hg⟩ := key w hw m (by omega)
  have hsel := sel_eq w hw m j hj hnp hbt
  have hlt : m < w.length := by omega
  have ht : 1 ≤ tokAt w (m + 1) ∧ tokAt w (m + 1) ≤ 4 := by
    rw [tokAt_succ w m hlt]; exact hw _ (List.getElem_mem hlt)
  have h4 : tokAt w (m + 1) = 1 ∨ tokAt w (m + 1) = 2 ∨ tokAt w (m + 1) = 3 ∨
      tokAt w (m + 1) = 4 := by omega
  have hcy : carryOut (w.take m) = 0 ∨ carryOut (w.take m) = 1 := by
    rw [← hg]; unfold gN; split_ifs <;> simp
  have hdig : digit w (m + 1) =
      (dA (tokAt w (m + 1)) + dC (tokAt w (m + 1)) + carryOut (w.take m)) % 2 := by
    unfold digit tokAt; simp
  have hgf : gf (tokAt w j) = ((carryOut (w.take m) : ℕ) : ℚ) := by
    unfold gf; rw [hg]
  have hatt : hd.attn (w.length + 1) (net.init w) (m + 1) =
      [0, 0, 0, 0, gf (tokAt w j), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    rw [attn_eq w hw, hsel, avg_singleton]
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  rw [hdig]
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [List.foldl, Block.apply, blk]
  rw [hatt, init_eq w hw (m + 1), hgf]
  rcases h4 with h | h | h | h <;> rcases hcy with hc' | hc' <;>
    norm_num [h, hc', npf, gf, gN, af, cf, dA, dC, qdot, vadd, affine, pos, r1, zz]

end Lane4.Case

namespace Lane4.Case
open Lane4.Seq

/-- `net` with every non-zero weight multiplied by (1 + 1/200) or (1 - 1/200). -/
def netP : TNet :=
  { embed := [[(201 / 200 : ℚ), 0, 0, 0, 0, 0], [(199 / 200 : ℚ), 0, 0, 0, 0, 0], [0, 0, 0, (201 / 200 : ℚ), 0, 0], [0, 0, (199 / 200 : ℚ), 0, 0, 0], [(199 / 200 : ℚ), (201 / 200 : ℚ), (201 / 200 : ℚ), (199 / 200 : ℚ), 0, 0]],
    blocks := [{ heads := [{ A := [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [(199 / 200 : ℚ), 0, 0, 0, 0, 0, 0, (199 / 200 : ℚ), 0, 0, 0, 0, 0, 0], [(201 / 200 : ℚ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], V := [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, (201 / 200 : ℚ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], mask := Mask.strict }], W1 := [[0, 0, (201 / 200 : ℚ), (201 / 200 : ℚ), (201 / 200 : ℚ), 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, (199 / 200 : ℚ), (199 / 200 : ℚ), (199 / 200 : ℚ), 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, (201 / 200 : ℚ), (199 / 200 : ℚ), (199 / 200 : ℚ), 0, 0, 0, 0, 0, 0, 0, 0, 0]], b1 := [0, (-201 / 200 : ℚ), (-199 / 100 : ℚ)], W2 := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [(199 / 200 : ℚ), (-201 / 100 : ℚ), (201 / 100 : ℚ)], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]], b2 := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }],
    outW := [0, 0, 0, 0, 0, (201 / 200 : ℚ), 0, 0, 0, 0, 0, 0, 0, 0],
    outB := 0 }

/-- The changed network is inside the relative ball of radius 1/200 around `net`, zeros fixed. -/
theorem witness_close : netClose net netP = true := by decide +kernel

/-- The input: one carry-generating token followed by 99 carry-propagating tokens
(length 100). The correct output at position 99 is 0 ... -/
theorem witness_target : digit (4 :: List.replicate 99 2) 99 = 0 := by decide +kernel

/-- ... and the changed network's output there is at least 1/2 away from it. -/
theorem witness_off : |netP.out (4 :: List.replicate 99 2) 99 - (0 : ℚ)| ≥ 1 / 2 := by decide +kernel

end Lane4.Case
