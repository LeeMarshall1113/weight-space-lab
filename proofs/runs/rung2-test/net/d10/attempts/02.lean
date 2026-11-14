namespace Lane4.Case
open Lane4.Seq

def z12 : Vec := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def e0 : Vec := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def e1 : Vec := [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def en1 : Vec := [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Causal uniform average of the weight slot, written to slot 1. -/
def hd1 : Head :=
  { A := [z12, z12, z12, z12, z12, z12, z12, z12, z12, z12, z12, z12],
    V := [z12, e0, z12, z12, z12, z12, z12, z12, z12, z12, z12, z12],
    mask := Mask.causal }

/-- Attend to the minimum prefix average, written to slot 2. -/
def hd2 : Head :=
  { A := [z12, z12, z12, z12, en1, z12, z12, z12, z12, z12, z12, z12],
    V := [z12, z12, e1, z12, z12, z12, z12, z12, z12, z12, z12, z12],
    mask := Mask.all }

def blk1 : Block :=
  { heads := [hd1], W1 := [z12], b1 := [0],
    W2 := [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]], b2 := z12 }

def blk2 : Block :=
  { heads := [hd2], W1 := [e1, en1], b1 := [0, 0],
    W2 := [[0, 0], [0, 0], [0, 0], [1, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0],
           [0, 0], [0, 0]],
    b2 := z12 }

def net : TNet :=
  { embed := [[0, 0, 0, 0], [-1, 0, 0, 0], [1, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
    blocks := [blk1, blk2],
    outW := [0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 1 / 2, 0],
    outB := 0 }

def wq (w : List ℕ) (j : ℕ) : ℚ := ((wt (tokAt w j) : ℤ) : ℚ)

def psum (w : List ℕ) (k : ℕ) : ℚ := ((List.range (k + 1)).map (wq w)).sum

theorem init_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) :
    net.init w j = [wq w j, 0, 0, 0] ++ pos j (w.length + 1) := by
  have h5 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 := by
    rcases tokAt_zero_or_mem w j with h | h
    · left; exact h
    · have := hw _ h
      omega
  rcases h5 with h | h | h | h | h <;> simp [TNet.init, net, wq, wt, h]

theorem hsel1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) :
    hd1.sel (w.length + 1) (net.init w) j = List.range (j + 1) := by
  have h := sel_all hd1 (w.length + 1) (net.init w) j (by
    intro k _ l _
    rw [init_eq w hw j, init_eq w hw k, init_eq w hw l]
    simp [Head.score, hd1, z12, qdot, matVec, pos])
  exact h.trans rfl

theorem attn1_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) :
    hd1.attn (w.length + 1) (net.init w) j
      = [0, psum w j / ((j : ℚ) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold Head.attn
  rw [hsel1 w hw j]
  have hV : hd1.V = [z12, e0, z12, z12, z12, z12, z12, z12, z12, z12, z12, z12] := rfl
  rw [hV]
  have hz : ∀ S : List ℕ, avg S (fun k => qdot z12 (net.init w k)) = 0 := by
    intro S
    have : (fun k => qdot z12 (net.init w k)) = fun _ => (0 : ℚ) := by
      funext k
      rw [init_eq w hw k]
      simp [qdot, z12, pos]
    rw [this, avg_zero]
  have he : avg (List.range (j + 1)) (fun k => qdot e0 (net.init w k))
      = psum w j / ((j : ℚ) + 1) := by
    have hf : (fun k => qdot e0 (net.init w k)) = wq w := by
      funext k
      rw [init_eq w hw k]
      simp [qdot, e0, pos]
    rw [hf]
    simp [avg, psum]
  simp only [List.map_cons, List.map_nil, hz, he]

theorem x1_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (j : ℕ) :
    blk1.apply (w.length + 1) (net.init w) j
      = [wq w j, psum w j / ((j : ℚ) + 1), 0, 0] ++ pos j (w.length + 1) := by
  simp only [Block.apply, blk1, List.foldl_cons, List.foldl_nil, attn1_eq w hw j, init_eq w hw j]
  simp [vadd, affine, qdot, z12, pos]

theorem score2 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i j : ℕ) :
    hd2.score (blk1.apply (w.length + 1) (net.init w) i)
      (blk1.apply (w.length + 1) (net.init w) j) = -(psum w j / ((j : ℚ) + 1)) := by
  rw [x1_eq w hw i, x1_eq w hw j]
  simp [Head.score, hd2, z12, en1, qdot, matVec, pos]

theorem attn2_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    hd2.attn (w.length + 1) (blk1.apply (w.length + 1) (net.init w)) i
      = [0, 0, avg (hd2.sel (w.length + 1) (blk1.apply (w.length + 1) (net.init w)) i)
            (fun k => psum w k / ((k : ℚ) + 1)), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold Head.attn
  have hV : hd2.V = [z12, z12, e1, z12, z12, z12, z12, z12, z12, z12, z12, z12] := rfl
  rw [hV]
  have hz : ∀ S : List ℕ,
      avg S (fun k => qdot z12 (blk1.apply (w.length + 1) (net.init w) k)) = 0 := by
    intro S
    have : (fun k => qdot z12 (blk1.apply (w.length + 1) (net.init w) k))
        = fun _ => (0 : ℚ) := by
      funext k
      rw [x1_eq w hw k]
      simp [qdot, z12, pos]
    rw [this, avg_zero]
  have he : ∀ S : List ℕ,
      avg S (fun k => qdot e1 (blk1.apply (w.length + 1) (net.init w) k))
        = avg S (fun k => psum w k / ((k : ℚ) + 1)) := by
    intro S
    have : (fun k => qdot e1 (blk1.apply (w.length + 1) (net.init w) k))
        = fun k => psum w k / ((k : ℚ) + 1) := by
      funext k
      rw [x1_eq w hw k]
      simp [qdot, e1, pos]
    rw [this]
  simp only [List.map_cons, List.map_nil, hz, he]

theorem core2 (n : ℕ) (x : ℕ → Vec) (i : ℕ) (u p m : ℚ)
    (hx : x i = [u, p, 0, 0] ++ pos i n)
    (hat : hd2.attn n x i = [0, 0, m, 0, 0, 0, 0, 0, 0, 0, 0, 0]) :
    qdot [0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 1 / 2, 0] (blk2.apply n x i)
      = m - (max p 0 + max (-p) 0) + 1 / 2 * (1 / (n : ℚ)) := by
  simp only [Block.apply, blk2, List.foldl_cons, List.foldl_nil, hat, hx]
  simp [qdot, vadd, affine, e1, en1, z12, pos]
  try ring_nf

theorem out_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4) (i : ℕ) :
    net.out w i
      = avg (hd2.sel (w.length + 1) (blk1.apply (w.length + 1) (net.init w)) i)
          (fun k => psum w k / ((k : ℚ) + 1))
        - (max (psum w i / ((i : ℚ) + 1)) 0 + max (-(psum w i / ((i : ℚ) + 1))) 0)
        + 1 / 2 * (1 / ((w.length : ℚ) + 1)) := by
  have hrun : net.run w = blk2.apply (w.length + 1) (blk1.apply (w.length + 1) (net.init w)) := rfl
  have ho : net.outW = [0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 1 / 2, 0] := rfl
  have hb : net.outB = 0 := rfl
  unfold TNet.out
  rw [hrun, ho, hb, core2 (w.length + 1) (blk1.apply (w.length + 1) (net.init w)) i (wq w i)
    (psum w i / ((i : ℚ) + 1)) _ (x1_eq w hw i) (attn2_eq w hw i)]
  first
    | (push_cast; ring)
    | simp
    | norm_num

theorem relu_abs (p : ℚ) : max p 0 + max (-p) 0 = |p| := by
  rcases le_total 0 p with h | h
  · have h1 : max p 0 = p := max_eq_left h
    have h2 : max (-p) 0 = 0 := max_eq_right (by linarith)
    have h3 : |p| = p := abs_of_nonneg h
    linarith
  · have h1 : max p 0 = 0 := max_eq_right h
    have h2 : max (-p) 0 = -p := max_eq_left (by linarith)
    have h3 : |p| = -p := abs_of_nonpos h
    linarith

theorem psum_eq (w : List ℕ) (k : ℕ) (hk : k ≤ w.length) :
    psum w k = ((((w.take k).map wt).sum : ℤ) : ℚ) := by
  induction k with
  | zero => simp [psum, wq, tokAt_zero, wt]
  | succ k ih =>
    have hk' : k < w.length := by omega
    have h0 := ih (by omega)
    unfold psum at h0 ⊢
    rw [sum_range_succ (wq w) (k + 1), h0]
    have e : w.take (k + 1) = w.take k ++ [w[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk']
      rfl
    rw [e]
    simp [wq, tokAt_succ w k hk']

theorem net_correct : Statement net := by
  intro w hv
  have hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 4 := hv.2
  rw [out_eq w hw w.length, relu_abs]
  have hne : hd2.sel (w.length + 1) (blk1.apply (w.length + 1) (net.init w)) w.length ≠ [] := by
    apply sel_ne_nil
    simp [hd2, cand]
  obtain ⟨j0, hj0⟩ := List.exists_mem_of_ne_nil _ hne
  have hj0' := (mem_sel _ _ _ _ _).1 hj0
  have hj0lt : j0 ≤ w.length := by
    have := (mem_cand_all (n := w.length + 1) (i := w.length)).1 hj0'.1
    omega
  have hmin : ∀ k, k ≤ w.length →
      psum w j0 / ((j0 : ℚ) + 1) ≤ psum w k / ((k : ℚ) + 1) := by
    intro k hk
    have hkc : k ∈ cand hd2.mask (w.length + 1) w.length := by
      simp [hd2, cand]
      omega
    have h1 := hj0'.2 k hkc
    rw [score2 w hw, score2 w hw] at h1
    linarith
  have hmu : avg (hd2.sel (w.length + 1) (blk1.apply (w.length + 1) (net.init w)) w.length)
      (fun k => psum w k / ((k : ℚ) + 1)) = psum w j0 / ((j0 : ℚ) + 1) := by
    apply avg_const _ _ _ hne
    intro j hj
    have hj' := (mem_sel _ _ _ _ _).1 hj
    have h1 := hj'.2 j0 hj0'.1
    have h2 := hj0'.2 j hj'.1
    rw [score2 w hw, score2 w hw] at h1
    rw [score2 w hw, score2 w hw] at h2
    show psum w j / ((j : ℚ) + 1) = psum w j0 / ((j0 : ℚ) + 1)
    linarith
  rw [hmu]
  have hc : (0 : ℚ) < 1 / ((w.length : ℚ) + 1) := by positivity
  constructor
  · intro h
    have hm0 : psum w j0 / ((j0 : ℚ) + 1) ≤ 0 := by
      have h1 := hmin 0 (Nat.zero_le _)
      have h0 : psum w 0 = 0 := by simpa using psum_eq w 0 (Nat.zero_le _)
      rw [h0] at h1
      simpa using h1
    have hStep : ∀ k, k ≤ w.length → 0 ≤ ((w.take k).map wt).sum := by
      intro k hk
      by_contra hneg
      push_neg at hneg
      have h1 : ((((w.take k).map wt).sum : ℤ) : ℚ) ≤ -1 := by
        exact_mod_cast (by omega : ((w.take k).map wt).sum ≤ -1)
      have hTk : psum w k ≤ -1 := by rw [psum_eq w k hk]; exact h1
      have hq : 1 / ((w.length : ℚ) + 1) ≤ 1 / ((k : ℚ) + 1) := by
        apply one_div_le_one_div_of_le
        · positivity
        · have : (k : ℚ) ≤ w.length := by exact_mod_cast hk
          linarith
      have hqpos : 0 < 1 / ((k : ℚ) + 1) := by positivity
      have hmk := hmin k hk
      have hdiv : psum w k / ((k : ℚ) + 1) = psum w k * (1 / ((k : ℚ) + 1)) := by ring
      have hprod : psum w k * (1 / ((k : ℚ) + 1)) ≤ (-1) * (1 / ((k : ℚ) + 1)) :=
        mul_le_mul_of_nonneg_right hTk hqpos.le
      have habs := abs_nonneg (psum w w.length / ((w.length : ℚ) + 1))
      linarith
    refine ⟨hStep, ?_⟩
    by_contra hne0
    have hL : 0 ≤ (w.map wt).sum := by simpa using hStep w.length le_rfl
    have hs1 : 1 ≤ (w.map wt).sum := by omega
    have hT1 : (1 : ℚ) ≤ psum w w.length := by
      rw [psum_eq w w.length le_rfl]
      simp only [List.take_length]
      exact_mod_cast hs1
    have hq : psum w w.length / ((w.length : ℚ) + 1)
        = psum w w.length * (1 / ((w.length : ℚ) + 1)) := by ring
    have hprod : 1 * (1 / ((w.length : ℚ) + 1)) ≤ psum w w.length * (1 / ((w.length : ℚ) + 1)) :=
      mul_le_mul_of_nonneg_right hT1 hc.le
    have habs := le_abs_self (psum w w.length / ((w.length : ℚ) + 1))
    linarith
  · intro hg
    obtain ⟨hpre, htot⟩ := hg
    have hTnn : ∀ k, k ≤ w.length → 0 ≤ psum w k := by
      intro k hk
      rw [psum_eq w k hk]
      exact_mod_cast hpre k hk
    have hTL : psum w w.length = 0 := by
      rw [psum_eq w w.length le_rfl]
      simp [htot]
    have hm : 0 ≤ psum w j0 / ((j0 : ℚ) + 1) :=
      div_nonneg (hTnn j0 hj0lt) (by positivity)
    have h0 : |psum w w.length / ((w.length : ℚ) + 1)| = 0 := by
      rw [hTL]
      simp
    rw [h0]
    linarith

end Lane4.Case
