/-
WORKED EXAMPLE on a task outside the four task families: accept exactly when the input
contains token 2 (3 real tokens). It was checked by the same checker and passed.
It shows the parts the checker joins: the lane's Spec.lean, a Solution.lean, and (not
shown) Final.lean. Only the part between the SOLUTION markers is what you write.

How this proof is organised (a pattern, not the only way):
  1. `init_eq`: the starting state at any position as an explicit list. Cases on the token.
  2. `score_eq`: the head's score in closed form.
  3. `out_eq`: the network output as an `avg` over the selected set `Head.sel`.
     Unfold one block at a time; keep `Head.sel` folded.
  4. Reason about which positions are selected with the lemma kit in Seq.lean
     (`mem_sel`, `sel_unique`, `sel_all`, `sel_ne_nil`, `avg_const`, `avg_singleton`).
For tasks that count, expect an induction over a prefix length, e.g. on sums over
`List.range (k+1)` (see `sum_range_succ`).
-/

-- ===== Spec.lean (given) =====
namespace Lane4.Case
open Lane4.Seq

def Valid (w : List ℕ) : Prop := w ≠ [] ∧ ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3

def Good (w : List ℕ) : Prop := 2 ∈ w

def Statement (N : TNet) : Prop :=
  ∀ w : List ℕ, Valid w → (0 < N.out w w.length ↔ Good w)

end Lane4.Case

-- ===== Solution.lean (SOLUTION START) =====
namespace Lane4.Case
open Lane4.Seq

/-- State: [flag, res] ++ 8 position features (width 10). -/
def z10 : Vec := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Score of key j = flag of j (query side reads the constant-1 feature, index 2).
Value: write the key's flag into slot `res` (index 1). -/
def hd : Head :=
  { A := [z10, z10, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0], z10, z10, z10, z10, z10, z10, z10],
    V := [z10, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0], z10, z10, z10, z10, z10, z10, z10, z10],
    mask := Mask.all }

def blk : Block :=
  { heads := [hd], W1 := [z10], b1 := [0],
    W2 := [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0]], b2 := z10 }

def net : TNet :=
  { embed := [[0, 0], [0, 0], [1, 0], [0, 0]],
    blocks := [blk],
    outW := [0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    outB := -1 / 2 }

def flag (w : List ℕ) (j : ℕ) : ℚ := if tokAt w j = 2 then 1 else 0

theorem init_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) :
    net.init w j = [flag w j, 0] ++ pos j (w.length + 1) := by
  have h3 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 := by
    rcases tokAt_zero_or_mem w j with h | h
    · left; exact h
    · have := hw _ h
      omega
  rcases h3 with h | h | h | h <;> simp [TNet.init, net, flag, h]

theorem score_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (i j : ℕ) :
    hd.score (net.init w i) (net.init w j) = flag w j := by
  rw [init_eq w hw i, init_eq w hw j]
  simp [Head.score, hd, z10, qdot, matVec, pos]

theorem out_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (i : ℕ) :
    net.out w i = avg (hd.sel (w.length + 1) (net.init w) i) (flag w) - 1 / 2 := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 1, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have hc : net.outB = -1 / 2 := rfl
  have hf : (fun j => qdot [1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (net.init w j)) = flag w := by
    funext j
    rw [init_eq w hw j]
    simp [qdot, pos]
  have hz : ∀ S : List ℕ, avg S (fun j => qdot z10 (net.init w j)) = 0 := by
    intro S
    have : (fun j => qdot z10 (net.init w j)) = fun _ => (0 : ℚ) := by
      funext j
      rw [init_eq w hw j]
      simp [qdot, z10, pos]
    rw [this, avg_zero]
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [List.foldl, Block.apply, blk, Head.attn, hd, List.map, hf, hz]
  rw [init_eq w hw i]
  simp [qdot, vadd, affine, z10, pos]
  ring

theorem net_correct : Statement net := by
  intro w hv
  have hw := hv.2
  rw [out_eq w hw]
  have hne : hd.sel (w.length + 1) (net.init w) w.length ≠ [] := by
    apply sel_ne_nil
    simp [hd, cand]
  constructor
  · -- output positive → some selected position is flagged → 2 ∈ w
    intro hpos
    by_contra hG
    have hall : ∀ j ∈ hd.sel (w.length + 1) (net.init w) w.length, flag w j = 0 := by
      intro j _
      unfold flag
      split_ifs with h
      · exfalso
        apply hG
        exact (mem_iff_tokAt w 2 (by norm_num)).mpr ⟨j, by
          by_contra hj
          have := tokAt_beyond w j (by omega)
          omega, h⟩
      · rfl
    rw [avg_const _ _ 0 hne hall] at hpos
    norm_num at hpos
  · -- 2 ∈ w → every selected position is flagged → output 1/2
    intro hG
    obtain ⟨j0, hj0, ht0⟩ := (mem_iff_tokAt w 2 (by norm_num)).mp hG
    have hall : ∀ j ∈ hd.sel (w.length + 1) (net.init w) w.length, flag w j = 1 := by
      intro j hj
      rw [mem_sel] at hj
      have hle := hj.2 j0 (by simp [hd, cand]; omega)
      rw [score_eq w hw, score_eq w hw] at hle
      have h1 : flag w j0 = 1 := by simp [flag, ht0]
      rw [h1] at hle
      unfold flag at hle ⊢
      split_ifs at hle ⊢ with h
      · rfl
      · norm_num at hle
    rw [avg_const _ _ 1 hne hall]
    norm_num

end Lane4.Case
-- ===== SOLUTION END =====
