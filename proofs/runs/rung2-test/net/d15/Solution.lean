namespace Lane4.Case
open Lane4.Seq

def z12 : Vec := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def e0 : Vec := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def e1 : Vec := [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def ne1 : Vec := [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Block 1 head: causal, all scores equal, writes the running average of the weights
into slot 1. -/
def hd1 : Head :=
  { A := [z12, z12, z12, z12, z12, z12, z12, z12, z12, z12, z12, z12],
    V := [z12, e0, z12, z12, z12, z12, z12, z12, z12, z12, z12, z12],
    mask := Mask.causal }

/-- Block 2 head: attends to the position with minimal running average, copies it to slot 2. -/
def hd2 : Head :=
  { A := [z12, z12, z12, z12, ne1, z12, z12, z12, z12, z12, z12, z12],
    V := [z12, z12, e1, z12, z12, z12, z12, z12, z12, z12, z12, z12],
    mask := Mask.all }

def blk1 : Block :=
  { heads := [hd1], W1 := [z12], b1 := [0],
    W2 := [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]], b2 := z12 }

def blk2 : Block :=
  { heads := [hd2], W1 := [e1], b1 := [0],
    W2 := [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]], b2 := z12 }

def net : TNet :=
  { embed := [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [-1, 0, 0, 0], [1, 0, 0, 0]],
    blocks := [blk1, blk2],
    outW := [0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 1 / 2, 0],
    outB := 0 }

theorem hd1_V : hd1.V = [z12, e0, z12, z12, z12, z12, z12, z12, z12, z12, z12, z12] := rfl
theorem hd2_V : hd2.V = [z12, z12, e1, z12, z12, z12, z12, z12, z12, z12, z12, z12] := rfl
theorem blk1_heads : blk1.heads = [hd1] := rfl
theorem blk1_W1 : blk1.W1 = [z12] := rfl
theorem blk1_b1 : blk1.b1 = [0] := rfl
theorem blk1_W2 : blk1.W2 = [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]] := rfl
theorem blk1_b2 : blk1.b2 = z12 := rfl
theorem blk2_heads : blk2.heads = [hd2] := rfl
theorem blk2_W1 : blk2.W1 = [e1] := rfl
theorem blk2_b1 : blk2.b1 = [0] := rfl
theorem blk2_W2 : blk2.W2 = [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]] := rfl
theorem blk2_b2 : blk2.b2 = z12 := rfl
theorem net_outW : net.outW = [0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 1 / 2, 0] := rfl
theorem net_outB : net.outB = 0 := rfl

def Wt (w : List ℕ) (j : ℕ) : ℚ := ((wt (tokAt w j) : ℤ) : ℚ)
def av (w : List ℕ) (i : ℕ) : ℚ := avg (List.range (i + 1)) (Wt w)
def pre (w : List ℕ) (k : ℕ) : ℤ := ((w.take k).map wt).sum
def xs1 (w : List ℕ) : ℕ → Vec := fun i => [Wt w i, av w i, 0, 0] ++ pos i (w.length + 1)

theorem init_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) :
    net.init w j = [Wt w j, 0, 0, 0] ++ pos j (w.length + 1) := by
  have h4 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 := by
    rcases tokAt_zero_or_mem w j with h | h
    · left; exact h
    · have := hw _ h
      omega
  rcases h4 with h | h | h | h | h <;> simp [TNet.init, net, Wt, wt, h]

theorem x1_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) :
    blk1.apply (w.length + 1) (net.init w) = xs1 w := by
  funext i
  have sc1 : ∀ p q : ℕ, hd1.score (net.init w p) (net.init w q) = 0 := by
    intro p q
    rw [init_eq w hw p, init_eq w hw q]
    simp [Head.score, hd1, z12, qdot, matVec, pos]
  have hs : hd1.sel (w.length + 1) (net.init w) i = List.range (i + 1) := by
    rw [sel_all hd1 _ _ i (fun k _ l _ => by rw [sc1 i k, sc1 i l])]
    rfl
  have hf : (fun j => qdot e0 (net.init w j)) = Wt w := by
    funext j
    rw [init_eq w hw j]
    simp [qdot, e0, pos]
  have hz : ∀ S : List ℕ, avg S (fun j => qdot z12 (net.init w j)) = 0 := by
    intro S
    have : (fun j => qdot z12 (net.init w j)) = fun _ => (0 : ℚ) := by
      funext j
      rw [init_eq w hw j]
      simp [qdot, z12, pos]
    rw [this, avg_zero]
  simp only [Block.apply, blk1_heads, List.foldl, Head.attn, hd1_V, List.map, hs, hf, hz,
    blk1_W1, blk1_b1, blk1_W2, blk1_b2]
  rw [init_eq w hw i]
  simp [xs1, av, qdot, vadd, affine, z12, e0, pos]

theorem run_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) :
    net.run w = blk2.apply (w.length + 1) (xs1 w) := by
  have h : net.run w = blk2.apply (w.length + 1) (blk1.apply (w.length + 1) (net.init w)) := rfl
  rw [h, x1_eq w hw]

theorem out_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    net.out w i = avg (hd2.sel (w.length + 1) (xs1 w) i) (av w) - max (av w i) 0
      + 1 / 2 * (1 / ((w.length : ℚ) + 1)) := by
  have hf : (fun j => qdot e1 (xs1 w j)) = av w := by
    funext j
    simp [xs1, qdot, e1, pos]
  have hz : ∀ S : List ℕ, avg S (fun j => qdot z12 (xs1 w j)) = 0 := by
    intro S
    have : (fun j => qdot z12 (xs1 w j)) = fun _ => (0 : ℚ) := by
      funext j
      simp [xs1, qdot, z12, pos]
    rw [this, avg_zero]
  unfold TNet.out
  rw [run_eq w hw, net_outW, net_outB]
  simp only [Block.apply, blk2_heads, List.foldl, Head.attn, hd2_V, List.map, hf, hz,
    blk2_W1, blk2_b1, blk2_W2, blk2_b2]
  simp [xs1, qdot, vadd, affine, z12, e1, pos] <;> ring

theorem sc2 (w : List ℕ) (i j : ℕ) : hd2.score (xs1 w i) (xs1 w j) = - av w j := by
  simp [Head.score, hd2, ne1, z12, qdot, matVec, xs1, pos]

theorem m_spec (w : List ℕ) :
    ∃ j0, j0 ≤ w.length ∧ (∀ k, k ≤ w.length → av w j0 ≤ av w k) ∧
      avg (hd2.sel (w.length + 1) (xs1 w) w.length) (av w) = av w j0 := by
  have hc : ∀ j, j ∈ cand hd2.mask (w.length + 1) w.length ↔ j < w.length + 1 :=
    fun j => mem_cand_all
  have hne : hd2.sel (w.length + 1) (xs1 w) w.length ≠ [] := by
    apply sel_ne_nil
    intro h
    have : 0 ∈ cand hd2.mask (w.length + 1) w.length := (hc 0).2 (by omega)
    rw [h] at this
    simp at this
  obtain ⟨j0, hj0⟩ := List.exists_mem_of_ne_nil _ hne
  have hj0' := (mem_sel _ _ _ _ _).1 hj0
  have hmin : ∀ k, k ≤ w.length → av w j0 ≤ av w k := by
    intro k hk
    have := hj0'.2 k ((hc k).2 (by omega))
    rw [sc2, sc2] at this
    linarith
  refine ⟨j0, by have := (hc j0).1 hj0'.1; omega, hmin, ?_⟩
  apply avg_const _ _ _ hne
  intro j hj
  have hj' := (mem_sel _ _ _ _ _).1 hj
  have g1 := hj'.2 j0 hj0'.1
  rw [sc2, sc2] at g1
  have g2 := hmin j (by have := (hc j).1 hj'.1; omega)
  linarith

theorem pre_succ (w : List ℕ) (k : ℕ) (hk : k < w.length) :
    pre w (k + 1) = pre w k + wt w[k] := by
  have h : w.take (k + 1) = w.take k ++ [w[k]] := by
    first
    | exact List.take_succ_eq_append_getElem hk
    | simp [List.take_succ, hk]
  unfold pre
  rw [h]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]

theorem S_eq (w : List ℕ) : ∀ k, k ≤ w.length →
    ((List.range (k + 1)).map (Wt w)).sum = ((pre w k : ℤ) : ℚ) := by
  intro k
  induction k with
  | zero => intro _; simp [Wt, tokAt_zero, wt, pre]
  | succ k ih =>
    intro hk
    have hk' : k < w.length := by omega
    rw [sum_range_succ, ih (by omega), pre_succ w k hk']
    simp [Wt, tokAt_succ w k hk']

theorem av_eq (w : List ℕ) (j : ℕ) (hj : j ≤ w.length) :
    av w j = ((pre w j : ℤ) : ℚ) / ((j : ℚ) + 1) := by
  unfold av avg
  rw [S_eq w j hj, List.length_range]
  push_cast
  try ring

theorem ineq1 (S : ℤ) (k L : ℕ) (hkL : k ≤ L) (hS : S ≤ -1) :
    (S : ℚ) / ((k : ℚ) + 1) ≤ -(1 / ((L : ℚ) + 1)) := by
  have hk : (0 : ℚ) < (k : ℚ) + 1 := by positivity
  have hL : (0 : ℚ) < (L : ℚ) + 1 := by positivity
  have hkL' : (k : ℚ) ≤ (L : ℚ) := by exact_mod_cast hkL
  have hS' : (S : ℚ) ≤ -1 := by exact_mod_cast hS
  have h3 : ((k : ℚ) + 1) / ((L : ℚ) + 1) ≤ 1 := by
    rw [div_le_iff₀ hL]; linarith
  have e : -(1 / ((L : ℚ) + 1)) * ((k : ℚ) + 1) = -(((k : ℚ) + 1) / ((L : ℚ) + 1)) := by ring
  rw [div_le_iff₀ hk, e]
  linarith

theorem net_correct : Statement net := by
  intro w hv
  have hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4 := hv.2
  obtain ⟨j0, hj0L, hmin, hm⟩ := m_spec w
  have hout : net.out w w.length =
      av w j0 - max (av w w.length) 0 + 1 / 2 * (1 / ((w.length : ℚ) + 1)) := by
    rw [out_eq w hw, hm]
  have hcpos : (0 : ℚ) < 1 / ((w.length : ℚ) + 1) := by positivity
  have hav0 : av w 0 = 0 := by
    rw [av_eq w 0 (Nat.zero_le _)]
    simp [pre]
  have hj0le : av w j0 ≤ 0 := by
    have := hmin 0 (Nat.zero_le _)
    linarith
  rw [hout]
  constructor
  · intro hpos
    have hnn : ∀ k, k ≤ w.length → 0 ≤ pre w k := by
      intro k hk
      by_contra hneg
      have h1 : pre w k ≤ -1 := by omega
      have h2 : av w k ≤ -(1 / ((w.length : ℚ) + 1)) := by
        rw [av_eq w k hk]
        exact ineq1 _ k w.length hk h1
      have h3 := hmin k hk
      have h4 := le_max_right (av w w.length) 0
      linarith
    have hS0 : pre w w.length = 0 := by
      have hnL := hnn w.length le_rfl
      by_contra hne
      have h1 : 1 ≤ pre w w.length := by omega
      have h1' : (1 : ℚ) ≤ ((pre w w.length : ℤ) : ℚ) := by exact_mod_cast h1
      have h2 : av w w.length = ((pre w w.length : ℤ) : ℚ) * (1 / ((w.length : ℚ) + 1)) := by
        rw [av_eq w w.length le_rfl]
        ring
      have h4 := mul_le_mul_of_nonneg_right h1' hcpos.le
      have h5 := le_max_left (av w w.length) 0
      linarith
    unfold Good
    refine ⟨fun k hk => hnn k hk, ?_⟩
    have h' := hS0
    unfold pre at h'
    first
    | (rw [List.take_length] at h'; exact h')
    | simpa using h'
  · intro hg
    obtain ⟨hnn, hsum⟩ := hg
    have hL0 : pre w w.length = 0 := by
      unfold pre
      first
      | (rw [List.take_length]; exact hsum)
      | simpa using hsum
    have hnn' : ∀ k, k ≤ w.length → 0 ≤ ((pre w k : ℤ) : ℚ) :=
      fun k hk => by exact_mod_cast hnn k hk
    have hjn : 0 ≤ av w j0 := by
      rw [av_eq w j0 hj0L]
      exact div_nonneg (hnn' j0 hj0L) (by positivity)
    have hLz : av w w.length = 0 := by
      rw [av_eq w w.length le_rfl, hL0]
      simp
    rw [hLz, max_self]
    linarith

end Lane4.Case
