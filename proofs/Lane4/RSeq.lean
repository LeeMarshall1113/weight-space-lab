/-
Lane 4, rung 4 fixed framework: a hard-attention transformer over ℝ whose WEIGHTS ARE
PERTURBED and whose FORWARD PASS IS ROUNDED, defined for input sequences of every length.
Written by the lane, not by a doctor.

The model (compare Seq.lean, the exact rung-2 framework):

* Written weights are rationals. A perturbation `p : Pert` gives one real number per
  weight; the weight actually used is `fl (w * (1 + d))`, so a perturbation is RELATIVE
  and a weight written as 0 stays 0.  `p.Within τ` says every `|d| ≤ τ`.
* `fl : ℝ → ℝ` is the rounding function, applied after every multiplication, addition
  and division of the forward pass. `Rounding u fl` is the model of it: relative error at
  most `u`, monotone, idempotent, odd, and exact on the integers up to 2^24. IEEE
  round-to-nearest binary32 satisfies this with u = 2^-24 as long as nothing overflows or
  underflows; overflow and underflow are NOT modelled. `fl = id` is exact arithmetic
  (`rounding_id`).
* Tokens are natural numbers; token 0 is BOS at position 0; `n = w.length + 1` positions.
  The state at position `i` starts as the token's (stored) embedding row followed by the
  three position features `[1, fl i, fl n]` (positions are stored rounded, so every state
  entry is a value the rounding leaves unchanged).
* Attention is average-hard as in Seq.lean: bilinear score `x_i · (A x_j)`, the candidate
  positions with the maximal (rounded) score share the weight equally, the head adds the
  average of `V x_j` over them. Masks `all`, `causal` (j ≤ i), `strict` (j < i).
* A block is heads (residual) then a one-hidden-layer ReLU MLP (residual).
* Sums run left to right. Perturbation indices: `p.E token coord`, `p.A block head row col`,
  `p.V block head row col`, `p.W1 block row col`, `p.b1 block row`, `p.W2 block row col`,
  `p.b2 block row`, `p.oW col`, `p.oB`.
-/
import Lane4.Seq

namespace Lane4.RSeq

open Lane4.Seq (Mask cand tokAt)

abbrev Vec := List ℝ

/-- The rounding model. -/
structure Rounding (u : ℝ) (fl : ℝ → ℝ) : Prop where
  rel : ∀ x, |fl x - x| ≤ u * |x|
  mono : ∀ x y, x ≤ y → fl x ≤ fl y
  idem : ∀ x, fl (fl x) = fl x
  neg : ∀ x, fl (-x) = -fl x
  nat : ∀ k : ℕ, k ≤ 16777216 → fl (k : ℝ) = (k : ℝ)

/-- One relative perturbation per weight. -/
structure Pert where
  E : ℕ → ℕ → ℝ
  A : ℕ → ℕ → ℕ → ℕ → ℝ
  V : ℕ → ℕ → ℕ → ℕ → ℝ
  W1 : ℕ → ℕ → ℕ → ℝ
  b1 : ℕ → ℕ → ℝ
  W2 : ℕ → ℕ → ℕ → ℝ
  b2 : ℕ → ℕ → ℝ
  oW : ℕ → ℝ
  oB : ℝ

/-- Every perturbation is at most `τ` in absolute value. -/
structure Pert.Within (τ : ℝ) (p : Pert) : Prop where
  E : ∀ t c, |p.E t c| ≤ τ
  A : ∀ b h r c, |p.A b h r c| ≤ τ
  V : ∀ b h r c, |p.V b h r c| ≤ τ
  W1 : ∀ b r c, |p.W1 b r c| ≤ τ
  b1 : ∀ b r, |p.b1 b r| ≤ τ
  W2 : ∀ b r c, |p.W2 b r c| ≤ τ
  b2 : ∀ b r, |p.b2 b r| ≤ τ
  oW : ∀ c, |p.oW c| ≤ τ
  oB : |p.oB| ≤ τ

/-- The stored weight: written `w`, perturbed by `d`, rounded. -/
noncomputable def sw (fl : ℝ → ℝ) (w : ℚ) (d : ℝ) : ℝ := fl ((w : ℝ) * (1 + d))

/-- A stored row of weights. -/
noncomputable def swRow (fl : ℝ → ℝ) : List ℚ → (ℕ → ℝ) → ℕ → Vec
  | a :: w, d, j => sw fl a (d j) :: swRow fl w d (j + 1)
  | [], _, _ => []

/-- Rounded dot product of a stored weight row with a vector: left to right from `acc`. -/
noncomputable def rdot (fl : ℝ → ℝ) : List ℚ → Vec → (ℕ → ℝ) → ℕ → ℝ → ℝ
  | a :: w, v :: x, d, j, acc => rdot fl w x d (j + 1) (fl (acc + fl (sw fl a (d j) * v)))
  | _, _, _, _, acc => acc

/-- Rounded dot product of two real vectors. -/
noncomputable def pdot (fl : ℝ → ℝ) : Vec → Vec → ℝ → ℝ
  | a :: x, b :: y, acc => pdot fl x y (fl (acc + fl (a * b)))
  | _, _, acc => acc

/-- Rounded matrix times vector, rows `i, i+1, ...`. -/
noncomputable def rmat (fl : ℝ → ℝ) : List (List ℚ) → Vec → (ℕ → ℕ → ℝ) → ℕ → Vec
  | r :: M, x, d, i => rdot fl r x (d i) 0 0 :: rmat fl M x d (i + 1)
  | [], _, _, _ => []

/-- Rounded affine map, rows `i, i+1, ...`. -/
noncomputable def raffine (fl : ℝ → ℝ) :
    List (List ℚ) → List ℚ → Vec → (ℕ → ℕ → ℝ) → (ℕ → ℝ) → ℕ → Vec
  | r :: M, c :: b, x, dW, db, i =>
    fl (rdot fl r x (dW i) 0 0 + sw fl c (db i)) :: raffine fl M b x dW db (i + 1)
  | _, _, _, _, _, _ => []

/-- Rounded entrywise sum. -/
noncomputable def radd (fl : ℝ → ℝ) : Vec → Vec → Vec
  | a :: x, b :: y => fl (a + b) :: radd fl x y
  | _, _ => []

/-- The three position features of position `i` among `n` positions. -/
noncomputable def pos (fl : ℝ → ℝ) (i n : ℕ) : Vec := [1, fl (i : ℝ), fl (n : ℝ)]

structure Head where
  A : List (List ℚ)
  V : List (List ℚ)
  mask : Mask

noncomputable def Head.score (h : Head) (fl : ℝ → ℝ) (dA : ℕ → ℕ → ℝ) (xi xj : Vec) : ℝ :=
  pdot fl xi (rmat fl h.A xj dA 0) 0

/-- The positions of `c` whose score `s` is maximal. -/
noncomputable def selOf (c : List ℕ) (s : ℕ → ℝ) : List ℕ :=
  c.filter (fun j => decide (∀ k ∈ c, s k ≤ s j))

noncomputable def Head.sel (h : Head) (fl : ℝ → ℝ) (dA : ℕ → ℕ → ℝ) (n : ℕ) (x : ℕ → Vec)
    (i : ℕ) : List ℕ :=
  selOf (cand h.mask n i) (fun j => h.score fl dA (x i) (x j))

/-- Rounded sum, left to right from `acc`. -/
noncomputable def rsum (fl : ℝ → ℝ) : List ℝ → ℝ → ℝ
  | a :: l, acc => rsum fl l (fl (acc + a))
  | [], acc => acc

/-- Rounded average of `f` over a list of positions. -/
noncomputable def ravg (fl : ℝ → ℝ) (S : List ℕ) (f : ℕ → ℝ) : ℝ :=
  fl (rsum fl (S.map f) 0 / (S.length : ℝ))

/-- One output entry per row of `V`: the average over the selected positions of `V_r · x_j`. -/
noncomputable def attnRows (fl : ℝ → ℝ) :
    List (List ℚ) → (ℕ → ℕ → ℝ) → List ℕ → (ℕ → Vec) → ℕ → Vec
  | r :: M, dV, S, x, i =>
    ravg fl S (fun j => rdot fl r (x j) (dV i) 0 0) :: attnRows fl M dV S x (i + 1)
  | [], _, _, _, _ => []

noncomputable def Head.attn (h : Head) (fl : ℝ → ℝ) (dA dV : ℕ → ℕ → ℝ) (n : ℕ)
    (x : ℕ → Vec) (i : ℕ) : Vec :=
  attnRows fl h.V dV (h.sel fl dA n x i) x 0

structure Block where
  heads : List Head
  W1 : List (List ℚ)
  b1 : List ℚ
  W2 : List (List ℚ)
  b2 : List ℚ

/-- Heads `k, k+1, ...` added to `acc` (all heads read the block's input state `x`). -/
noncomputable def headsApply (fl : ℝ → ℝ) :
    List Head → (ℕ → ℕ → ℕ → ℝ) → (ℕ → ℕ → ℕ → ℝ) → ℕ → (ℕ → Vec) → ℕ → Vec → ℕ → Vec
  | h :: hs, dA, dV, n, x, i, acc, k =>
    headsApply fl hs dA dV n x i (radd fl acc (h.attn fl (dA k) (dV k) n x i)) (k + 1)
  | [], _, _, _, _, _, acc, _ => acc

noncomputable def Block.apply (B : Block) (fl : ℝ → ℝ) (p : Pert) (b n : ℕ) (x : ℕ → Vec) :
    ℕ → Vec := fun i =>
  radd fl (headsApply fl B.heads (p.A b) (p.V b) n x i (x i) 0)
    (raffine fl B.W2 B.b2
      ((raffine fl B.W1 B.b1 (headsApply fl B.heads (p.A b) (p.V b) n x i (x i) 0)
        (p.W1 b) (p.b1 b) 0).map relu)
      (p.W2 b) (p.b2 b) 0)

structure TNet where
  embed : List (List ℚ)
  blocks : List Block
  outW : List ℚ
  outB : ℚ

noncomputable def TNet.init (N : TNet) (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) : ℕ → Vec :=
  fun i => swRow fl (N.embed.getD (tokAt w i) []) (p.E (tokAt w i)) 0 ++ pos fl i (w.length + 1)

/-- Blocks `b, b+1, ...` applied in order. -/
noncomputable def runFrom (fl : ℝ → ℝ) (p : Pert) (n : ℕ) :
    List Block → ℕ → (ℕ → Vec) → (ℕ → Vec)
  | B :: Bs, b, x => runFrom fl p n Bs (b + 1) (B.apply fl p b n x)
  | [], _, x => x

noncomputable def TNet.run (N : TNet) (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) : ℕ → Vec :=
  runFrom fl p (w.length + 1) N.blocks 0 (N.init fl p w)

/-- The network's output at position `i` for input `w`. -/
noncomputable def TNet.out (N : TNet) (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (i : ℕ) : ℝ :=
  fl (rdot fl N.outW (N.run fl p w i) p.oW 0 0 + sw fl N.outB p.oB)

/-! ### Shape check -/

def rowsOK (M : List (List ℚ)) (rows cols : ℕ) : Bool :=
  M.length == rows && M.all (fun r => r.length == cols)

def Head.shapeOK (h : Head) (d : ℕ) : Bool := rowsOK h.A d d && rowsOK h.V d d

def Block.shapeOK (B : Block) (d : ℕ) : Bool :=
  decide (B.heads.length ≤ 4) && B.heads.all (fun h => h.shapeOK d) &&
  decide (B.b1.length ≤ 32) && rowsOK B.W1 B.b1.length d &&
  rowsOK B.W2 d B.b1.length && B.b2.length == d

/-- `ntok` real tokens (so `ntok + 1` embedding rows), embedding width `de`,
state width `de + 3 ≤ 24`, at most 4 blocks of at most 4 heads. -/
def TNet.shapeOK (N : TNet) (ntok : ℕ) : Bool :=
  match N.embed with
  | [] => false
  | e :: _ =>
    decide (e.length + 3 ≤ 24) && rowsOK N.embed (ntok + 1) e.length &&
    decide (N.blocks.length ≤ 4) && N.blocks.all (fun B => B.shapeOK (e.length + 3)) &&
    N.outW.length == e.length + 3

/-! ### Lemma kit: rounding -/

/-- Exact arithmetic is a rounding with unit 0. -/
theorem rounding_id : Rounding 0 (fun x => x) :=
  ⟨fun x => by simp, fun _ _ h => h, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem Rounding.zero {u : ℝ} {fl : ℝ → ℝ} (h : Rounding u fl) : fl 0 = 0 := by
  simpa using h.rel 0

theorem Rounding.one {u : ℝ} {fl : ℝ → ℝ} (h : Rounding u fl) : fl 1 = 1 := by
  simpa using h.nat 1 (by norm_num)

theorem Rounding.nonneg {u : ℝ} {fl : ℝ → ℝ} (h : Rounding u fl) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ fl x := by
  have := h.mono 0 x hx
  rwa [h.zero] at this

/-- `fl x` is within `u * B` of `x` when `|x| ≤ B`. -/
theorem Rounding.err {u : ℝ} {fl : ℝ → ℝ} (h : Rounding u fl) (hu : 0 ≤ u) {x B : ℝ}
    (hx : |x| ≤ B) : |fl x - x| ≤ u * B :=
  le_trans (h.rel x) (mul_le_mul_of_nonneg_left hx hu)

theorem Rounding.upper {u : ℝ} {fl : ℝ → ℝ} (h : Rounding u fl) (hu : 0 ≤ u) {x B : ℝ}
    (hx : |x| ≤ B) : fl x ≤ x + u * B := by
  have := (abs_le.mp (h.err hu hx)).2
  linarith

theorem Rounding.lower {u : ℝ} {fl : ℝ → ℝ} (h : Rounding u fl) (hu : 0 ≤ u) {x B : ℝ}
    (hx : |x| ≤ B) : x - u * B ≤ fl x := by
  have := (abs_le.mp (h.err hu hx)).1
  linarith

/-- Two values that are far enough apart stay in order after rounding. -/
theorem Rounding.lt_of_gap {u : ℝ} {fl : ℝ → ℝ} (h : Rounding u fl) (hu : 0 ≤ u)
    {a b B : ℝ} (ha : |a| ≤ B) (hb : |b| ≤ B) (hgap : a + 2 * (u * B) < b) : fl a < fl b := by
  have h1 := h.upper hu ha
  have h2 := h.lower hu hb
  linarith

/-! ### Lemma kit: stored weights and small relative errors -/

theorem sw_zero {u : ℝ} {fl : ℝ → ℝ} (h : Rounding u fl) (d : ℝ) : sw fl 0 d = 0 := by
  simp [sw, h.zero]

/-- A stored weight is within `(τ + u + u*τ) * |w|` of the written weight. -/
theorem sw_near {u τ : ℝ} {fl : ℝ → ℝ} (h : Rounding u fl) (hu : 0 ≤ u) (w : ℚ) {d : ℝ}
    (hd : |d| ≤ τ) : |sw fl w d - (w : ℝ)| ≤ (τ + u + u * τ) * |(w : ℝ)| := by
  unfold sw
  have hτ : 0 ≤ τ := le_trans (abs_nonneg d) hd
  have h1 : |(w : ℝ) * (1 + d)| ≤ |(w : ℝ)| * (1 + τ) := by
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := abs_add_le (1 : ℝ) d
    simp only [abs_one] at this
    linarith
  have h2 := h.err hu h1
  have h3 : |(w : ℝ) * (1 + d) - (w : ℝ)| ≤ τ * |(w : ℝ)| := by
    have : (w : ℝ) * (1 + d) - (w : ℝ) = d * (w : ℝ) := by ring
    rw [this, abs_mul]
    exact mul_le_mul_of_nonneg_right hd (abs_nonneg _)
  calc |fl ((w : ℝ) * (1 + d)) - (w : ℝ)|
      = |(fl ((w : ℝ) * (1 + d)) - (w : ℝ) * (1 + d)) + ((w : ℝ) * (1 + d) - (w : ℝ))| := by
        congr 1; ring
    _ ≤ u * (|(w : ℝ)| * (1 + τ)) + τ * |(w : ℝ)| := le_trans (abs_add_le _ _) (add_le_add h2 h3)
    _ = (τ + u + u * τ) * |(w : ℝ)| := by ring

/-- Product of two numbers that are each close to 1. -/
theorem near_mul {x y ex ey : ℝ} (hx : |x - 1| ≤ ex) (hy : |y - 1| ≤ ey) :
    |x * y - 1| ≤ ex + ey + ex * ey := by
  have h : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by ring
  have h1 : |(x - 1) * (y - 1)| ≤ ex * ey := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) (le_trans (abs_nonneg _) hx)
  rw [h]
  have := abs_add_le ((x - 1) * (y - 1) + (x - 1)) (y - 1)
  have := abs_add_le ((x - 1) * (y - 1)) (x - 1)
  linarith

/-- A value scaled by a factor close to 1. -/
theorem near_scale {x e t : ℝ} (hx : |x - 1| ≤ e) : |x * t - t| ≤ e * |t| := by
  have h : x * t - t = (x - 1) * t := by ring
  rw [h, abs_mul]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

/-- A stored weight is unchanged by rounding it again. -/
theorem fl_sw {u : ℝ} {fl : ℝ → ℝ} (h : Rounding u fl) (w : ℚ) (d : ℝ) :
    fl (sw fl w d) = sw fl w d := h.idem _

/-- `sw_near` with the three error terms folded into one number `ε`. -/
theorem sw_rel {u τ ε : ℝ} {fl : ℝ → ℝ} (h : Rounding u fl) (hu : 0 ≤ u) (w : ℚ) {d : ℝ}
    (hd : |d| ≤ τ) (hε : τ + u + u * τ ≤ ε) : |sw fl w d - (w : ℝ)| ≤ ε * |(w : ℝ)| :=
  le_trans (sw_near h hu w hd) (mul_le_mul_of_nonneg_right hε (abs_nonneg _))

/-- Relative errors of a product: `a + b + a*b`, weakened to a number `c` of your choice. -/
theorem rel_mul {x y s t a b c : ℝ} (hx : |x - s| ≤ a * |s|) (hy : |y - t| ≤ b * |t|)
    (hc : a + b + a * b ≤ c) : |x * y - s * t| ≤ c * |s * t| := by
  have h : x * y - s * t = (x - s) * (y - t) + (x - s) * t + s * (y - t) := by ring
  have h1 : |(x - s) * (y - t)| ≤ (a * |s|) * (b * |t|) := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) (le_trans (abs_nonneg _) hx)
  have h2 : |(x - s) * t| ≤ (a * |s|) * |t| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have h3 : |s * (y - t)| ≤ |s| * (b * |t|) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
  have h4 := abs_add_le ((x - s) * (y - t) + (x - s) * t) (s * (y - t))
  have h5 := abs_add_le ((x - s) * (y - t)) ((x - s) * t)
  have h6 : (a + b + a * b) * (|s| * |t|) ≤ c * (|s| * |t|) :=
    mul_le_mul_of_nonneg_right hc (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  rw [h, abs_mul s t]
  nlinarith [h1, h2, h3, h4, h5, h6]

/-- Rounding a value with relative error `a` gives relative error `a + u + u*a`,
weakened to a number `c` of your choice. -/
theorem rel_fl {u : ℝ} {fl : ℝ → ℝ} (h : Rounding u fl) (hu : 0 ≤ u) {x t a c : ℝ}
    (hx : |x - t| ≤ a * |t|) (hc : a + u + u * a ≤ c) : |fl x - t| ≤ c * |t| := by
  have h1 : |x| ≤ |t| + a * |t| := by
    have := abs_sub_abs_le_abs_sub x t
    linarith
  have h2 := h.err hu h1
  have h3 := abs_add_le (fl x - x) (x - t)
  have h4 : fl x - x + (x - t) = fl x - t := by ring
  rw [h4] at h3
  have h5 := mul_le_mul_of_nonneg_right hc (abs_nonneg t)
  nlinarith [h2, h3, h5, hx]

/-! ### Lemma kit: rounded positions

`n` is the number of positions and `u * n ≤ 1/256` is the length condition of the
statement. In exact arithmetic (`u = 0`) it holds at every length. -/

/-- A rounded natural number is within `u * k` of it. -/
theorem Rounding.natCast_near {u : ℝ} {fl : ℝ → ℝ} (h : Rounding u fl) (k : ℕ) :
    |fl (k : ℝ) - k| ≤ u * k := by
  have := h.rel (k : ℝ)
  have h2 : |(k : ℝ)| = k := abs_of_nonneg (Nat.cast_nonneg k)
  rw [h2] at this
  exact this

/-- Rounded positions stay in order, almost 1 apart. -/
theorem Rounding.pos_gap {u : ℝ} {fl : ℝ → ℝ} (h : Rounding u fl) (hu : 0 ≤ u) {a b n : ℕ}
    (hab : a < b) (hbn : b ≤ n) (hn : u * (n : ℝ) ≤ 1 / 256) :
    fl (a : ℝ) + 127 / 128 ≤ fl (b : ℝ) := by
  have ha := abs_le.mp (h.natCast_near a)
  have hb := abs_le.mp (h.natCast_near b)
  have h1 : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
  have h2 : (b : ℝ) ≤ n := by exact_mod_cast hbn
  have h3 : u * (a : ℝ) ≤ u * n := mul_le_mul_of_nonneg_left (by linarith) hu
  have h4 : u * (b : ℝ) ≤ u * n := mul_le_mul_of_nonneg_left h2 hu
  linarith

/-- A rounded position is between 0 and `n + 1/256`. -/
theorem Rounding.pos_le {u : ℝ} {fl : ℝ → ℝ} (h : Rounding u fl) (hu : 0 ≤ u) {k n : ℕ}
    (hk : k ≤ n) (hn : u * (n : ℝ) ≤ 1 / 256) :
    0 ≤ fl (k : ℝ) ∧ fl (k : ℝ) ≤ n + 1 / 256 := by
  have hb := abs_le.mp (h.natCast_near k)
  have h2 : (k : ℝ) ≤ n := by exact_mod_cast hk
  have h4 : u * (k : ℝ) ≤ u * n := mul_le_mul_of_nonneg_left h2 hu
  exact ⟨h.nonneg (Nat.cast_nonneg k), by linarith⟩

/-! ### Lemma kit: selection and averages -/

theorem mem_selOf (c : List ℕ) (s : ℕ → ℝ) (j : ℕ) :
    j ∈ selOf c s ↔ j ∈ c ∧ ∀ k ∈ c, s k ≤ s j := by
  unfold selOf
  rw [List.mem_filter, decide_eq_true_eq]

/-- A strict unique winner is the only selected position. -/
theorem selOf_unique (c : List ℕ) (hc : c.Nodup) (s : ℕ → ℝ) (j : ℕ) (hj : j ∈ c)
    (hlt : ∀ k ∈ c, k ≠ j → s k < s j) : selOf c s = [j] := by
  unfold selOf
  apply Lane4.Seq.filter_eq_singleton hc hj
  · rw [decide_eq_true_eq]
    intro k hk
    by_cases hkj : k = j
    · rw [hkj]
    · exact le_of_lt (hlt k hk hkj)
  · intro k hk hkj
    rw [decide_eq_false_iff_not]
    intro hall
    exact absurd (hall j hj) (not_le.mpr (hlt k hk hkj))

/-- The head's selected set when one candidate strictly beats all others. -/
theorem Head.sel_unique (h : Head) (fl : ℝ → ℝ) (dA : ℕ → ℕ → ℝ) (n : ℕ) (x : ℕ → Vec)
    (i j : ℕ) (hj : j ∈ cand h.mask n i)
    (hlt : ∀ k ∈ cand h.mask n i, k ≠ j →
      h.score fl dA (x i) (x k) < h.score fl dA (x i) (x j)) :
    h.sel fl dA n x i = [j] :=
  selOf_unique _ (Lane4.Seq.cand_nodup _ _ _) _ j hj hlt

theorem Head.mem_sel (h : Head) (fl : ℝ → ℝ) (dA : ℕ → ℕ → ℝ) (n : ℕ) (x : ℕ → Vec)
    (i j : ℕ) : j ∈ h.sel fl dA n x i ↔ j ∈ cand h.mask n i ∧
      ∀ k ∈ cand h.mask n i, h.score fl dA (x i) (x k) ≤ h.score fl dA (x i) (x j) :=
  mem_selOf _ _ j

/-- The rounded average over a single position. -/
theorem ravg_singleton {u : ℝ} {fl : ℝ → ℝ} (h : Rounding u fl) (j : ℕ) (f : ℕ → ℝ) :
    ravg fl [j] f = fl (f j) := by
  simp [ravg, rsum, h.idem]

theorem rsum_zeros {u : ℝ} {fl : ℝ → ℝ} (h : Rounding u fl) (l : List ℝ)
    (hl : ∀ a ∈ l, a = 0) : rsum fl l 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ha : a = 0 := hl a (by simp)
    subst ha
    simp only [rsum, add_zero, h.zero]
    exact ih (fun b hb => hl b (List.mem_cons_of_mem _ hb))

/-- The rounded average of zeros is zero. -/
theorem ravg_zero {u : ℝ} {fl : ℝ → ℝ} (h : Rounding u fl) (S : List ℕ) :
    ravg fl S (fun _ => (0 : ℝ)) = 0 := by
  unfold ravg
  rw [rsum_zeros h _ (by simp)]
  simp [h.zero]

end Lane4.RSeq
