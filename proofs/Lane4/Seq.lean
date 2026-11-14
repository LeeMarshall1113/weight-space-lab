/-
Lane 4, rung 2 fixed framework: a hard-attention transformer over ℚ, defined for
input sequences of every length. Written by the lane, not by a doctor.

Shape of the model (all weights exact rationals):

* Tokens are natural numbers. Token 0 is BOS and is prepended by the framework, so
  an input `w : List ℕ` occupies positions 1 .. w.length and position 0 holds BOS.
  `n = w.length + 1` is the number of positions.
* The state at a position is a vector (a `List ℚ`). The initial state at position `i`
  is the token's embedding row followed by eight fixed position features
  `[1, i, i², 1/(i+1), (-1)^i, n, 1/n, i/n]`.
* An attention head scores position `j` from position `i` by the bilinear form
  `x_i · (A x_j)`. Attention is AVERAGE-HARD: among the candidate positions allowed
  by the mask, the ones with the maximal score share the weight equally. The head
  adds the average of `V x_j` over those positions to the state at `i`.
  Masks: `all` (every position), `causal` (j ≤ i), `strict` (j < i; at i = 0 the
  head adds zero).
* A block is: all heads read the same input state and are added to it (residual),
  then a one-hidden-layer ReLU MLP is applied with a residual connection.
* The output at position `i` is an affine read-out of the final state: one rational.
-/
import Lane4.Basic

namespace Lane4.Seq

abbrev Vec := List ℚ

def qdot (a b : Vec) : ℚ := (List.zipWith (fun u v => u * v) a b).sum

def matVec (M : List Vec) (x : Vec) : Vec := M.map (fun r => qdot r x)

def vadd (a b : Vec) : Vec := List.zipWith (fun u v => u + v) a b

def affine (W : List Vec) (b : Vec) (x : Vec) : Vec :=
  List.zipWith (fun r c => qdot r x + c) W b

/-- The eight position features of position `i` among `n` positions. -/
def pos (i n : ℕ) : Vec :=
  [1, (i : ℚ), (i : ℚ) ^ 2, 1 / ((i : ℚ) + 1), (-1 : ℚ) ^ i, (n : ℚ), 1 / (n : ℚ), (i : ℚ) / (n : ℚ)]

inductive Mask where
  | all
  | causal
  | strict
  deriving DecidableEq

/-- Candidate key positions for a query at position `i` among `n` positions. -/
def cand (m : Mask) (n i : ℕ) : List ℕ :=
  match m with
  | Mask.all => List.range n
  | Mask.causal => List.range (i + 1)
  | Mask.strict => List.range i

structure Head where
  A : List Vec
  V : List Vec
  mask : Mask

def Head.score (h : Head) (xi xj : Vec) : ℚ := qdot xi (matVec h.A xj)

/-- The selected positions: candidates whose score is maximal. -/
def Head.sel (h : Head) (n : ℕ) (x : ℕ → Vec) (i : ℕ) : List ℕ :=
  (cand h.mask n i).filter
    (fun j => decide (∀ k ∈ cand h.mask n i, h.score (x i) (x k) ≤ h.score (x i) (x j)))

/-- Average of `f` over a list of positions (0 for the empty list). -/
def avg (S : List ℕ) (f : ℕ → ℚ) : ℚ := (S.map f).sum / (S.length : ℚ)

/-- Output of one head at position `i`: one entry per row of `V`. -/
def Head.attn (h : Head) (n : ℕ) (x : ℕ → Vec) (i : ℕ) : Vec :=
  h.V.map (fun row => avg (h.sel n x i) (fun j => qdot row (x j)))

structure Block where
  heads : List Head
  W1 : List Vec
  b1 : Vec
  W2 : List Vec
  b2 : Vec

def Block.apply (B : Block) (n : ℕ) (x : ℕ → Vec) : ℕ → Vec := fun i =>
  let y := B.heads.foldl (fun acc h => vadd acc (h.attn n x i)) (x i)
  vadd y (affine B.W2 B.b2 ((affine B.W1 B.b1 y).map (fun v => max v 0)))

structure TNet where
  embed : List Vec
  blocks : List Block
  outW : Vec
  outB : ℚ

/-- Token at position `i` (0 = BOS at position 0 and beyond the end). -/
def tokAt (w : List ℕ) (i : ℕ) : ℕ := (0 :: w).getD i 0

def TNet.init (N : TNet) (w : List ℕ) : ℕ → Vec := fun i =>
  N.embed.getD (tokAt w i) [] ++ pos i (w.length + 1)

def TNet.run (N : TNet) (w : List ℕ) : ℕ → Vec :=
  N.blocks.foldl (fun x B => B.apply (w.length + 1) x) (N.init w)

/-- The network's output at position `i` for input `w`. -/
def TNet.out (N : TNet) (w : List ℕ) (i : ℕ) : ℚ := qdot N.outW (N.run w i) + N.outB

/-! ### Shape check -/

def rowsOK (M : List Vec) (rows cols : ℕ) : Bool :=
  M.length == rows && M.all (fun r => r.length == cols)

def Head.shapeOK (h : Head) (d : ℕ) : Bool := rowsOK h.A d d && rowsOK h.V d d

def Block.shapeOK (B : Block) (d : ℕ) : Bool :=
  decide (B.heads.length ≤ 4) && B.heads.all (fun h => h.shapeOK d) &&
  decide (B.b1.length ≤ 32) && rowsOK B.W1 B.b1.length d &&
  rowsOK B.W2 d B.b1.length && B.b2.length == d

/-- `ntok` real tokens (so `ntok + 1` embedding rows), embedding width `de`,
state width `de + 8 ≤ 24`, at most 4 blocks of at most 4 heads. -/
def TNet.shapeOK (N : TNet) (ntok : ℕ) : Bool :=
  match N.embed with
  | [] => false
  | e :: _ =>
    let d := e.length + 8
    decide (d ≤ 24) && rowsOK N.embed (ntok + 1) e.length &&
    decide (N.blocks.length ≤ 4) && N.blocks.all (fun B => B.shapeOK d) &&
    N.outW.length == d

/-! ### Lemma kit (available to every doctor) -/

theorem filter_eq_singleton {l : List ℕ} (hn : l.Nodup) {p : ℕ → Bool} {j : ℕ}
    (hj : j ∈ l) (hp : p j = true) (hq : ∀ k ∈ l, k ≠ j → p k = false) :
    l.filter p = [j] := by
  induction l with
  | nil => simp at hj
  | cons a t ih =>
    rw [List.nodup_cons] at hn
    by_cases haj : a = j
    · subst haj
      have ht : t.filter p = [] := by
        rw [List.filter_eq_nil_iff]
        intro k hk
        have hne : k ≠ a := fun h => hn.1 (h ▸ hk)
        simp [hq k (List.mem_cons_of_mem _ hk) hne]
      simp [hp, ht]
    · have hjt : j ∈ t := by
        rcases List.mem_cons.1 hj with h | h
        · exact absurd h.symm haj
        · exact h
      have hpa : p a = false := hq a (by simp) haj
      have := ih hn.2 hjt (fun k hk hne => hq k (List.mem_cons_of_mem _ hk) hne)
      simp [hpa, this]

theorem cand_nodup (m : Mask) (n i : ℕ) : (cand m n i).Nodup := by
  cases m <;> simp [cand, List.nodup_range]

theorem mem_cand_all {n i j : ℕ} : j ∈ cand Mask.all n i ↔ j < n := by simp [cand]
theorem mem_cand_causal {n i j : ℕ} : j ∈ cand Mask.causal n i ↔ j ≤ i := by
  simp [cand]
theorem mem_cand_strict {n i j : ℕ} : j ∈ cand Mask.strict n i ↔ j < i := by simp [cand]

/-- A strict unique winner is the only selected position. -/
theorem sel_unique (h : Head) (n : ℕ) (x : ℕ → Vec) (i j : ℕ)
    (hj : j ∈ cand h.mask n i)
    (hlt : ∀ k ∈ cand h.mask n i, k ≠ j → h.score (x i) (x k) < h.score (x i) (x j)) :
    h.sel n x i = [j] := by
  unfold Head.sel
  apply filter_eq_singleton (cand_nodup _ _ _) hj
  · rw [decide_eq_true_eq]
    intro k hk
    by_cases hkj : k = j
    · rw [hkj]
    · exact le_of_lt (hlt k hk hkj)
  · intro k hk hkj
    rw [decide_eq_false_iff_not]
    intro hall
    exact absurd (hall j hj) (not_le.mpr (hlt k hk hkj))

/-- If every candidate has the same score, every candidate is selected. -/
theorem sel_all (h : Head) (n : ℕ) (x : ℕ → Vec) (i : ℕ)
    (heq : ∀ k ∈ cand h.mask n i, ∀ l ∈ cand h.mask n i,
      h.score (x i) (x k) = h.score (x i) (x l)) :
    h.sel n x i = cand h.mask n i := by
  unfold Head.sel
  rw [List.filter_eq_self]
  intro j hj
  rw [decide_eq_true_eq]
  intro k hk
  exact le_of_eq (heq k hk j hj)

/-- Membership in the selected set. -/
theorem mem_sel (h : Head) (n : ℕ) (x : ℕ → Vec) (i j : ℕ) :
    j ∈ h.sel n x i ↔ j ∈ cand h.mask n i ∧
      ∀ k ∈ cand h.mask n i, h.score (x i) (x k) ≤ h.score (x i) (x j) := by
  unfold Head.sel
  rw [List.mem_filter, decide_eq_true_eq]

/-- A non-empty candidate list has at least one selected position. -/
theorem sel_ne_nil (h : Head) (n : ℕ) (x : ℕ → Vec) (i : ℕ)
    (hc : cand h.mask n i ≠ []) : h.sel n x i ≠ [] := by
  have hne : (cand h.mask n i).toFinset.Nonempty := by
    rcases List.exists_mem_of_ne_nil _ hc with ⟨a, ha⟩
    exact ⟨a, List.mem_toFinset.mpr ha⟩
  rcases Finset.exists_max_image _ (fun k => h.score (x i) (x k)) hne with ⟨j, hj, hmax⟩
  intro hnil
  have hmem : j ∈ h.sel n x i := by
    rw [mem_sel]
    exact ⟨List.mem_toFinset.mp hj, fun k hk => hmax k (List.mem_toFinset.mpr hk)⟩
  rw [hnil] at hmem
  simp at hmem

theorem avg_singleton (j : ℕ) (f : ℕ → ℚ) : avg [j] f = f j := by
  simp [avg]

/-- The average of a function that is constant on a non-empty list. -/
theorem avg_const (S : List ℕ) (f : ℕ → ℚ) (v : ℚ) (hS : S ≠ [])
    (hf : ∀ j ∈ S, f j = v) : avg S f = v := by
  unfold avg
  have hlen : (S.length : ℚ) ≠ 0 := by
    have : S.length ≠ 0 := fun h => hS (List.length_eq_zero_iff.mp h)
    exact_mod_cast this
  have hsum : (S.map f).sum = (S.length : ℚ) * v := by
    induction S with
    | nil => simp
    | cons a t ih =>
      by_cases ht : t = []
      · subst ht
        simp [hf a (by simp)]
      · have := ih ht (fun j hj => hf j (List.mem_cons_of_mem _ hj))
          (by
            have : t.length ≠ 0 := fun h => ht (List.length_eq_zero_iff.mp h)
            exact_mod_cast this)
        simp only [List.map_cons, List.sum_cons, List.length_cons, this, hf a (by simp)]
        push_cast
        ring
  rw [hsum]
  field_simp

theorem avg_zero (S : List ℕ) : avg S (fun _ => (0 : ℚ)) = 0 := by
  simp [avg]

/-! Tokens by position: position 0 holds BOS (token 0), position k+1 holds `w[k]`. -/

theorem tokAt_zero (w : List ℕ) : tokAt w 0 = 0 := by
  simp [tokAt]

theorem tokAt_succ (w : List ℕ) (k : ℕ) (h : k < w.length) : tokAt w (k + 1) = w[k] := by
  simp [tokAt, h]

theorem tokAt_beyond (w : List ℕ) (j : ℕ) (h : w.length < j) : tokAt w j = 0 := by
  rcases j with _ | k
  · simp [tokAt]
  · have hk : w.length ≤ k := by omega
    simp [tokAt, hk]

theorem tokAt_zero_or_mem (w : List ℕ) (j : ℕ) : tokAt w j = 0 ∨ tokAt w j ∈ w := by
  rcases j with _ | k
  · left; exact tokAt_zero w
  · by_cases h : k < w.length
    · right
      rw [tokAt_succ w k h]
      exact List.getElem_mem h
    · left
      exact tokAt_beyond w (k + 1) (by omega)

/-- A real token occurs in `w` exactly when some position 1..w.length holds it. -/
theorem mem_iff_tokAt (w : List ℕ) (t : ℕ) (ht : t ≠ 0) :
    t ∈ w ↔ ∃ j, j < w.length + 1 ∧ tokAt w j = t := by
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
    exact ⟨k + 1, by omega, tokAt_succ w k hk⟩
  · rintro ⟨j, _, hj⟩
    rcases tokAt_zero_or_mem w j with h0 | hm
    · exact absurd (hj ▸ h0) ht
    · exact hj ▸ hm

/-- Sum over `List.range (n+1)` peels off the last term. -/
theorem sum_range_succ (f : ℕ → ℚ) (n : ℕ) :
    ((List.range (n + 1)).map f).sum = ((List.range n).map f).sum + f n := by
  simp [List.range_succ]

end Lane4.Seq
