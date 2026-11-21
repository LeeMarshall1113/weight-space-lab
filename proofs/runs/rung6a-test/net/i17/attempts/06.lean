namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1000000

/-! ### The network -/

def z7 : List ℚ := [0, 0, 0, 0, 0, 0, 0]
def z2 : List ℚ := [0, 0]
def u0v : List ℚ := [1, 0, 0, 0, 0, 0, 0]
def u1v : List ℚ := [0, 1, 0, 0, 0, 0, 0]
def zA : List (List ℚ) := [z7, z7, z7, z7, z7, z7, z7]

def head1 : AHead :=
  { A := zA, V := [z7, z7, u0v, u1v, z7, z7, z7], mask := Mask.strict, m := 24, g := z7, gb := -1 }

def blk1 : ABlock :=
  { heads := [head1], W1 := [], b1 := [], W2 := [[], [], [], [], [], [], []], b2 := z7 }

def headA : AHead :=
  { A := zA, V := [z7, z7, z7, z7, u0v, z7, z7], mask := Mask.causal, m := 24,
    g := [0, 0, -1, 0, 0, 0, 0], gb := 1 / 2 }

def headB : AHead :=
  { A := zA, V := [z7, z7, z7, z7, z7, u0v, z7], mask := Mask.causal, m := 24,
    g := [0, 0, 0, -1, 0, 0, 0], gb := 1 / 2 }

def blk2 : ABlock :=
  { heads := [headA, headB], W1 := [[2, 0, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 2, 0]], b1 := [-3, -3],
    W2 := [z2, z2, z2, z2, z2, z2, [1, 1]], b2 := z7 }

def net : ANet :=
  { embed := [z7, u0v, u1v], blocks := [blk1, blk2], outW := [0, 0, 0, 0, 0, 0, 1], outB := 0 }

/-! ### Context -/

structure Ctx (u η M : ℝ) (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) : Prop where
  hr : Rnd u η M fl
  he : ExpM u η ex
  hu0 : 0 ≤ u
  hu1 : u ≤ 1 / 2 ^ 24
  hη0 : 0 ≤ η
  hη1 : η ≤ 1 / 2 ^ 149
  hp : p.Within (1 / 1000)
  hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2
  hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256
  hnη : η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100
  hM : 2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M

section Steps

variable {u η M : ℝ} {fl ex : ℝ → ℝ} {p : APert} {w : List ℕ}

theorem Ctx.range (ev : Ctx u η M fl ex p w) (c : ℝ) (hc : c ≤ 2 ^ 40) : c ≤ M :=
  range_const ev.hM (by omega) hc

theorem Ctx.rangeN (ev : Ctx u η M fl ex p w) (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 2 ^ 40) :
    c * ((w.length + 1 : ℕ) : ℝ) ≤ M :=
  range_lin ev.hM (by omega) hc0 hc

theorem u_mul (ev : Ctx u η M fl ex p w) (c : ℝ) (hc : 0 ≤ c) :
    u * (c * ((w.length + 1 : ℕ) : ℝ)) ≤ c / 256 := by
  have h : u * (c * ((w.length + 1 : ℕ) : ℝ)) = c * (u * ((w.length + 1 : ℕ) : ℝ)) := by ring
  rw [h]
  have := mul_le_mul_of_nonneg_left ev.hn hc
  linarith

theorem Ctx.small (ev : Ctx u η M fl ex p w) : u ≤ 1 / 16000000 ∧ η ≤ 1 / 10 ^ 40 := by
  refine ⟨?_, eta_tiny ev.hη1⟩
  have h := ev.hu1
  have : (1 : ℝ) / 2 ^ 24 ≤ 1 / 16000000 := by norm_num
  linarith

/-! ### Zero rows and lists -/

theorem dotQ_rep (n : ℕ) (x : List ℝ) : dotQ (List.replicate n (0 : ℚ)) x = 0 := by
  induction n generalizing x with
  | zero => simp [dotQ]
  | succ n ih =>
    cases x with
    | nil => simp [dotQ]
    | cons a t => simpa [dotQ, List.replicate_succ] using ih t

theorem dotQ_z7 (x : List ℝ) : dotQ z7 x = 0 := by
  have : z7 = List.replicate 7 (0 : ℚ) := rfl
  rw [this]; exact dotQ_rep 7 x

theorem dotQ_z2 (x : List ℝ) : dotQ z2 x = 0 := by
  have : z2 = List.replicate 2 (0 : ℚ) := rfl
  rw [this]; exact dotQ_rep 2 x

theorem dotR_rep (n : ℕ) (x : List ℝ) : dotR x (List.replicate n (0 : ℝ)) = 0 := by
  induction x generalizing n with
  | nil => simp [dotR]
  | cons a t ih =>
    cases n with
    | zero => simp [dotR]
    | succ n => simpa [dotR, List.replicate_succ] using ih n

theorem dotR_z7 (x : List ℝ) : dotR x [0, 0, 0, 0, 0, 0, 0] = 0 := by
  have : ([0, 0, 0, 0, 0, 0, 0] : List ℝ) = List.replicate 7 0 := rfl
  rw [this]; exact dotR_rep 7 x

theorem close7 {a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 e X : ℝ}
    (h0 : |a0 - b0| ≤ e) (h1 : |a1 - b1| ≤ e) (h2 : |a2 - b2| ≤ e) (h3 : |a3 - b3| ≤ e)
    (h4 : |a4 - b4| ≤ e) (h5 : |a5 - b5| ≤ e) (h6 : |a6 - b6| ≤ e)
    (g0 : |b0| ≤ X) (g1 : |b1| ≤ X) (g2 : |b2| ≤ X) (g3 : |b3| ≤ X) (g4 : |b4| ≤ X)
    (g5 : |b5| ≤ X) (g6 : |b6| ≤ X) :
    Close [a0, a1, a2, a3, a4, a5, a6] [b0, b1, b2, b3, b4, b5, b6] e X := by
  refine ⟨rfl, ?_⟩
  intro k hk
  have hk7 : k < 7 := by simpa using hk
  interval_cases k
  · first | exact ⟨h0, g0⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h0, g0⟩)
  · first | exact ⟨h1, g1⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h1, g1⟩)
  · first | exact ⟨h2, g2⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h2, g2⟩)
  · first | exact ⟨h3, g3⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h3, g3⟩)
  · first | exact ⟨h4, g4⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h4, g4⟩)
  · first | exact ⟨h5, g5⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h5, g5⟩)
  · first | exact ⟨h6, g6⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h6, g6⟩)

theorem closeL7 {a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 e0 e1 e2 e3 e4 e5 e6
    X0 X1 X2 X3 X4 X5 X6 : ℝ}
    (h0 : |a0 - b0| ≤ e0) (h1 : |a1 - b1| ≤ e1) (h2 : |a2 - b2| ≤ e2) (h3 : |a3 - b3| ≤ e3)
    (h4 : |a4 - b4| ≤ e4) (h5 : |a5 - b5| ≤ e5) (h6 : |a6 - b6| ≤ e6)
    (g0 : |b0| ≤ X0) (g1 : |b1| ≤ X1) (g2 : |b2| ≤ X2) (g3 : |b3| ≤ X3) (g4 : |b4| ≤ X4)
    (g5 : |b5| ≤ X5) (g6 : |b6| ≤ X6) :
    CloseL [a0, a1, a2, a3, a4, a5, a6] [b0, b1, b2, b3, b4, b5, b6]
      [e0, e1, e2, e3, e4, e5, e6] [X0, X1, X2, X3, X4, X5, X6] := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro k hk
  have hk7 : k < 7 := by simpa using hk
  interval_cases k
  · first | exact ⟨h0, g0⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h0, g0⟩)
  · first | exact ⟨h1, g1⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h1, g1⟩)
  · first | exact ⟨h2, g2⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h2, g2⟩)
  · first | exact ⟨h3, g3⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h3, g3⟩)
  · first | exact ⟨h4, g4⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h4, g4⟩)
  · first | exact ⟨h5, g5⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h5, g5⟩)
  · first | exact ⟨h6, g6⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h6, g6⟩)

theorem closeL2 {a0 a1 b0 b1 e0 e1 X0 X1 : ℝ}
    (h0 : |a0 - b0| ≤ e0) (h1 : |a1 - b1| ≤ e1) (g0 : |b0| ≤ X0) (g1 : |b1| ≤ X1) :
    CloseL [a0, a1] [b0, b1] [e0, e1] [X0, X1] := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro k hk
  have hk7 : k < 2 := by simpa using hk
  interval_cases k
  · first | exact ⟨h0, g0⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h0, g0⟩)
  · first | exact ⟨h1, g1⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h1, g1⟩)

/-- Bounds on the per-coordinate lists, seven entries. -/
theorem bnd7 {e0 e1 e2 e3 e4 e5 e6 X0 X1 X2 X3 X4 X5 X6 e X : ℝ}
    (h0 : e0 ≤ e) (h1 : e1 ≤ e) (h2 : e2 ≤ e) (h3 : e3 ≤ e) (h4 : e4 ≤ e) (h5 : e5 ≤ e)
    (h6 : e6 ≤ e) (g0 : X0 ≤ X) (g1 : X1 ≤ X) (g2 : X2 ≤ X) (g3 : X3 ≤ X) (g4 : X4 ≤ X)
    (g5 : X5 ≤ X) (g6 : X6 ≤ X) :
    ∀ k, k < 7 → [e0, e1, e2, e3, e4, e5, e6].getD k 0 ≤ e ∧
      [X0, X1, X2, X3, X4, X5, X6].getD k 0 ≤ X := by
  intro k hk
  interval_cases k
  · first | exact ⟨h0, g0⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h0, g0⟩)
  · first | exact ⟨h1, g1⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h1, g1⟩)
  · first | exact ⟨h2, g2⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h2, g2⟩)
  · first | exact ⟨h3, g3⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h3, g3⟩)
  · first | exact ⟨h4, g4⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h4, g4⟩)
  · first | exact ⟨h5, g5⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h5, g5⟩)
  · first | exact ⟨h6, g6⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h6, g6⟩)

theorem bnd2 {e0 e1 X0 X1 e X : ℝ} (h0 : e0 ≤ e) (h1 : e1 ≤ e) (g0 : X0 ≤ X) (g1 : X1 ≤ X) :
    ∀ k, k < 2 → [e0, e1].getD k 0 ≤ e ∧ [X0, X1].getD k 0 ≤ X := by
  intro k hk
  interval_cases k
  · first | exact ⟨h0, g0⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h0, g0⟩)
  · first | exact ⟨h1, g1⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h1, g1⟩)

/-- A stored-weight dot product with per-coordinate errors: rows of at most 7 entries of size
at most 2, ideal entries at most 1, entry errors at most 1/10. -/
theorem dotL (ev : Ctx u η M fl ex p w) (r : List ℚ) (x xh es Xs : List ℝ) (d : ℕ → ℝ)
    (hd : ∀ k, |d k| ≤ 1 / 1000) (hl : r.length = x.length) (hl7 : r.length ≤ 7)
    (hC : CloseL x xh es Xs) (hb : ∀ k, k < x.length → es.getD k 0 ≤ 1 / 2 ∧ Xs.getD k 0 ≤ 1)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 2) :
    |ardot fl r x d 0 0 - dotQ r xh| ≤ wErr (1 / 1000) r es Xs + 1 / 1000 ∧
      |ardot fl r x d 0 0| ≤ 110 := by
  have h := ardot_near_w u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (by norm_num)
    (by norm_num) r x xh es Xs d 2 1 (1 / 2) hl (by omega) hC hb hd hW (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (ev.range _ (by norm_num))
  obtain ⟨k1, k2⟩ := h
  have hL : (r.length : ℝ) ≤ 7 := by exact_mod_cast hl7
  have hL0 : (0 : ℝ) ≤ r.length := Nat.cast_nonneg _
  have c1 : (r.length : ℝ) * (2 + 1) * (1 + 1 / 2 + 1) / 2 ^ 16
      ≤ 7 * (2 + 1) * (1 + 1 / 2 + 1) / 2 ^ 16 := by gcongr
  have c2 : (r.length : ℝ) * (2 + 1) * (1 + 1 / 2 + 1) * 2
      ≤ 7 * (2 + 1) * (1 + 1 / 2 + 1) * 2 := by gcongr
  have n1 : (7 : ℝ) * (2 + 1) * (1 + 1 / 2 + 1) / 2 ^ 16 + 1 / 2 ^ 100 ≤ 1 / 1000 := by norm_num
  have n2 : (7 : ℝ) * (2 + 1) * (1 + 1 / 2 + 1) * 2 ≤ 110 := by norm_num
  constructor <;> linarith

/-! ### Generic head machinery: zero score matrix, slope 24 -/

def Good (N : ℕ) (x : ℕ → Vec) : Prop :=
  ∀ j, j ≤ N → (x j).length = 7 ∧ ∃ xh : List ℝ, Close (x j) xh (1 / 50) 1

theorem savg_nil (hr : Rnd u η M fl) (c : List ℕ) (hc : c = []) (s f : ℕ → ℝ) :
    savg fl ex c s f = 0 := by
  subst hc
  unfold savg
  simp [Lane4.RSeq.rsum, hr.zero]

theorem score_eq (h : AHead) (hA : h.A = zA) (fl : ℝ → ℝ) (dA : ℕ → ℕ → ℝ) (dm : ℝ)
    (x : ℕ → Vec) (i j : ℕ) :
    h.score fl dA dm x i j =
      fl (h.bias fl dm i j + Lane4.RSeq.pdot fl (x i) (armat fl zA (x j) dA 0) 0) := by
  unfold AHead.score
  rw [hA]

theorem content_small (ev : Ctx u η M fl ex p w) {x : ℕ → Vec} (hx : Good (w.length + 1) x)
    {dA : ℕ → ℕ → ℝ} (hdA : ∀ r c, |dA r c| ≤ 1 / 1000) (i k : ℕ) (hi : i ≤ w.length + 1)
    (hk : k ≤ w.length + 1) :
    |Lane4.RSeq.pdot fl (x i) (armat fl zA (x k) dA 0) 0| ≤ 1 / 10 := by
  obtain ⟨hli, xi, hCi⟩ := hx i hi
  obtain ⟨hlk, xk, hCk⟩ := hx k hk
  have hz : z7.length = 7 := rfl
  have hrow : ∀ r : ℕ, |ardot fl z7 (x k) (dA r) 0 0 - 0| ≤ 1 / 100 := by
    intro r
    have h := ardot_near u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (by norm_num)
      (by norm_num) z7 (x k) xk (dA r) 0 1 (1 / 50) (by rw [hlk]; rfl) (by simp [z7]) hCk
      (hdA r) (by simp [z7]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ev.range _ (by norm_num))
    rw [dotQ_z7] at h
    have h2 := h.1
    rw [hz] at h2
    have h4 : ((7 : ℕ) : ℝ) * (0 * (1 / 50) + 1 / 1000 * (1 + 1 / 50)) +
        ((7 : ℕ) : ℝ) * (0 + 1) * (1 + 1 / 50 + 1) / 2 ^ 16 + 1 / 2 ^ 100 ≤ 1 / 100 := by
      norm_num
    linarith
  have hy : armat fl zA (x k) dA 0 =
      [ardot fl z7 (x k) (dA 0) 0 0, ardot fl z7 (x k) (dA 1) 0 0, ardot fl z7 (x k) (dA 2) 0 0,
       ardot fl z7 (x k) (dA 3) 0 0, ardot fl z7 (x k) (dA 4) 0 0, ardot fl z7 (x k) (dA 5) 0 0,
       ardot fl z7 (x k) (dA 6) 0 0] := rfl
  have hCy : Close (armat fl zA (x k) dA 0) [0, 0, 0, 0, 0, 0, 0] (1 / 100) 0 := by
    rw [hy]
    exact close7 (hrow 0) (hrow 1) (hrow 2) (hrow 3) (hrow 4) (hrow 5) (hrow 6) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlen_y : (armat fl zA (x k) dA 0).length = 7 := by rw [hy]; rfl
  obtain ⟨p1, -⟩ := pdot_near u η M fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (x i) xi
    (armat fl zA (x k) dA 0) [0, 0, 0, 0, 0, 0, 0] 1 0 (1 / 50) (1 / 100)
    (by rw [hli, hlen_y]) (by rw [hli]; norm_num) hCi hCy (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (ev.range _ (by norm_num))
  rw [dotR_z7, sub_zero, hli] at p1
  refine le_trans p1 ?_
  norm_num

theorem bias_abs (ev : Ctx u η M fl ex p w) (h : AHead) (hm : (h.m : ℝ) = 24) {dm : ℝ}
    (hdm : |dm| ≤ 1 / 1000) (i t : ℕ) (hi : i ≤ w.length + 1) (ht : t ≤ w.length + 1) :
    |h.bias fl dm i t| ≤ 26 * ((w.length + 1 : ℕ) : ℝ) := by
  have habs : |((h.m : ℚ) : ℝ)| = 24 := by rw [hm]; exact abs_of_nonneg (by norm_num)
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hM4 : (25 : ℝ) ≤ M := ev.range 25 (by norm_num)
  have hS := asw_bound ev.hr ev.hu0 h.m hdm (by rw [habs]; linarith)
  rw [habs] at hS
  have hu25 : u * (24 + 1 / 1000) ≤ 1 / 2 ^ 24 * 25 :=
    mul_le_mul ev.hu1 (by norm_num) (by norm_num) (by positivity)
  have hη' := eta_tiny ev.hη1
  have hS2 : |asw fl h.m dm| ≤ 25 := by
    have h1 : (1 : ℝ) / 2 ^ 24 * 25 + 1 / 10 ^ 40 ≤ 1 / 2 := by norm_num
    linarith
  have hbias : h.bias fl dm i t = fl (asw fl h.m dm * ((t : ℝ) - (i : ℝ))) := by
    simp [AHead.bias]
  rw [hbias]
  generalize asw fl h.m dm = S at hS2 ⊢
  have ht' : (t : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast ht
  have hi' : (i : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hi
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hti : |(t : ℝ) - (i : ℝ)| ≤ ((w.length + 1 : ℕ) : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  have hab : |S * ((t : ℝ) - (i : ℝ))| ≤ 25 * ((w.length + 1 : ℕ) : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul hS2 hti (abs_nonneg _) (by norm_num)
  have hB := ev.rangeN 25 (by norm_num) (by norm_num)
  have h := ev.hr.bound ev.hu0 hab hB
  have hu25n := u_mul ev 25 (by norm_num)
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

theorem score_abs (ev : Ctx u η M fl ex p w) (h : AHead) (hm : (h.m : ℝ) = 24)
    (hA : h.A = zA) {x : ℕ → Vec} (hx : Good (w.length + 1) x) {dA : ℕ → ℕ → ℝ}
    (hdA : ∀ r c, |dA r c| ≤ 1 / 1000) {dm : ℝ} (hdm : |dm| ≤ 1 / 1000) (i k : ℕ)
    (hi : i ≤ w.length + 1) (hk : k ≤ w.length + 1) :
    |h.score fl dA dm x i k| ≤ 28 * ((w.length + 1 : ℕ) : ℝ) := by
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hbk := bias_abs ev h hm hdm i k hi hk
  have hck := content_small ev hx hdA i k hi hk
  have hB := ev.rangeN 27 (by norm_num) (by norm_num)
  have ha : |h.bias fl dm i k + Lane4.RSeq.pdot fl (x i) (armat fl zA (x k) dA 0) 0|
      ≤ 27 * ((w.length + 1 : ℕ) : ℝ) :=
    le_trans (abs_add_le _ _) (by linarith)
  have h1 := ev.hr.bound ev.hu0 ha hB
  have hη' := eta_tiny ev.hη1
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have hu27 := u_mul ev 27 (by norm_num)
  rw [score_eq h hA]
  linarith

theorem score_gap (ev : Ctx u η M fl ex p w) (h : AHead) (hm : (h.m : ℝ) = 24)
    (hA : h.A = zA) {x : ℕ → Vec} (hx : Good (w.length + 1) x) {dA : ℕ → ℕ → ℝ}
    (hdA : ∀ r c, |dA r c| ≤ 1 / 1000) {dm : ℝ} (hdm : |dm| ≤ 1 / 1000) (i j k : ℕ)
    (hi : i ≤ w.length + 1) (hj : j ≤ w.length + 1) (hkj : k < j) :
    h.score fl dA dm x i k ≤ h.score fl dA dm x i j - 16 * ((j : ℝ) - (k : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hM12 : (2 : ℝ) ^ 12 * (((w.length + 1 : ℕ) : ℝ) + 1) ≤ M := by
    have := ev.rangeN 8192 (by norm_num) (by norm_num)
    have h12 : (2 : ℝ) ^ 12 = 4096 := by norm_num
    rw [h12]; linarith
  obtain ⟨hg1, -⟩ := bias_gap u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1
    (by norm_num) (by norm_num) h dm hdm (by rw [hm]; norm_num)
    (by rw [hm]; norm_num) (w.length + 1) i j k hkj hj hi ev.hn ev.hnη hM12
  rw [hm] at hg1
  have hcj := content_small ev hx hdA i j hi hj
  have hck := content_small ev hx hdA i k hi (by omega)
  obtain ⟨hcj1, hcj2⟩ := abs_le.mp hcj
  obtain ⟨hck1, hck2⟩ := abs_le.mp hck
  have hbj := bias_abs ev h hm hdm i j hi hj
  have hbk := bias_abs ev h hm hdm i k hi (by omega)
  have hB := ev.rangeN 27 (by norm_num) (by norm_num)
  have ha : |h.bias fl dm i k + Lane4.RSeq.pdot fl (x i) (armat fl zA (x k) dA 0) 0|
      ≤ 27 * ((w.length + 1 : ℕ) : ℝ) :=
    le_trans (abs_add_le _ _) (by linarith)
  have hb : |h.bias fl dm i j + Lane4.RSeq.pdot fl (x i) (armat fl zA (x j) dA 0) 0|
      ≤ 27 * ((w.length + 1 : ℕ) : ℝ) :=
    le_trans (abs_add_le _ _) (by linarith)
  have hgap := ev.hr.gap ev.hu0 ha hb hB
  have hu27 := u_mul ev 27 (by norm_num)
  have hη' := eta_tiny ev.hη1
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have hjk : (k : ℝ) + 1 ≤ (j : ℝ) := by
    have h : k + 1 ≤ j := hkj
    exact_mod_cast h
  rw [score_eq h hA, score_eq h hA]
  linarith

/-- Softmax with a clear winner: the head returns the value of the LAST candidate. -/
theorem head_soft (ev : Ctx u η M fl ex p w) (h : AHead) (hm : (h.m : ℝ) = 24)
    (hA : h.A = zA) {x : ℕ → Vec} (hx : Good (w.length + 1) x) {dA : ℕ → ℕ → ℝ}
    (hdA : ∀ r c, |dA r c| ≤ 1 / 1000) {dm : ℝ} (hdm : |dm| ≤ 1 / 1000) (i : ℕ)
    (hi : i ≤ w.length + 1) {c : List ℕ} (hnd : c.Nodup) (hlen : c.length ≤ w.length + 1)
    (hmem : ∀ k ∈ c, k ≤ w.length + 1) {j : ℕ} (hj : j ∈ c) (hmax : ∀ k ∈ c, k ≠ j → k < j)
    (f : ℕ → ℝ) {B : ℝ} (hB : ∀ k ∈ c, |f k| ≤ B) (hB2 : B ≤ 2) :
    |savg fl ex c (fun k => h.score fl dA dm x i k) f - f j| ≤ B / 100 + 1 / 2 ^ 90 := by
  have hgap : ∀ k' ∈ c, k' ≠ j →
      h.score fl dA dm x i k' ≤ h.score fl dA dm x i j - 16 * ((ndist j k' : ℕ) : ℝ) := by
    intro k' hk' hne
    have hlt : k' < j := hmax k' hk' hne
    rw [ndist_cast]
    have hg := score_gap ev h hm hA hx hdA hdm i j k' hi (hmem j hj) hlt
    have h1 : (k' : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hlt
    rw [abs_of_nonneg (by linarith)]
    exact hg
  have hS : ∀ k ∈ c, |h.score fl dA dm x i k| ≤ 28 * ((w.length + 1 : ℕ) : ℝ) :=
    fun k hk => score_abs ev h hm hA hx hdA hdm i k hi (hmem k hk)
  have hSM : 2 * (28 * ((w.length + 1 : ℕ) : ℝ)) ≤ M := by
    have := ev.rangeN 56 (by norm_num) (by norm_num)
    linarith
  have hBM : 4 * B + 4 ≤ M := by
    have := ev.range 12 (by norm_num)
    linarith
  obtain ⟨hs1, -⟩ := soft_near (s := fun k => h.score fl dA dm x i k) (f := f) ev.hr ev.he
    ev.hu0 ev.hu1 ev.hη0 ev.hη1 hnd hlen ev.hn ev.hnη hj hgap hS hSM hB hBM
  exact hs1

/-! ### Ideal quantities and stage 0 (the embedding) -/

def tf1 (t : ℕ) : ℝ := if t = 1 then 1 else 0
def tf2 (t : ℕ) : ℝ := if t = 2 then 1 else 0

theorem tf1_abs (t : ℕ) : |tf1 t| ≤ 1 := by
  unfold tf1; split_ifs <;> norm_num

theorem tf2_abs (t : ℕ) : |tf2 t| ≤ 1 := by
  unfold tf2; split_ifs <;> norm_num

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (j : ℕ) : tokAt w j ≤ 2 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem asw_c (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149)
    (hM : 4 ≤ M) (a : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 1000) (ha : |(a : ℝ)| ≤ 3) :
    |asw fl a d - (a : ℝ)| ≤ 1 / 900 := by
  have h := asw_near hr hu0 a hd (by linarith)
  have h1 : u * (|(a : ℝ)| + 1 / 1000) ≤ 1 / 2 ^ 24 * 4 :=
    mul_le_mul hu (by linarith) (by positivity) (by positivity)
  have h2 := eta_tiny hη
  have h3 : (1 : ℝ) / 2 ^ 24 * 4 + 1 / 10 ^ 40 ≤ 1 / 9000 := by norm_num
  linarith

theorem asw0 (ev : Ctx u η M fl ex p w) {d : ℝ} (hd : |d| ≤ 1 / 1000) :
    |asw fl (0 : ℚ) d| ≤ 1 / 900 := by
  have := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) (0 : ℚ) hd (by simp)
  simpa using this

theorem asw1 (ev : Ctx u η M fl ex p w) {d : ℝ} (hd : |d| ≤ 1 / 1000) :
    |asw fl (1 : ℚ) d - 1| ≤ 1 / 900 := by
  have := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) (1 : ℚ) hd (by simp)
  simpa using this

theorem init_ent (ev : Ctx u η M fl ex p w) (j : ℕ) :
    ∃ a0 a1 a2 a3 a4 a5 a6 : ℝ, net.init fl p w j = [a0, a1, a2, a3, a4, a5, a6] ∧
      |a0 - tf1 (tokAt w j)| ≤ 1 / 900 ∧ |a1 - tf2 (tokAt w j)| ≤ 1 / 900 ∧ |a2| ≤ 1 / 900 ∧
      |a3| ≤ 1 / 900 ∧ |a4| ≤ 1 / 900 ∧ |a5| ≤ 1 / 900 ∧ |a6| ≤ 1 / 900 := by
  have ht := tok_le w ev.hw j
  have hinit : ∀ t, tokAt w j = t →
      net.init fl p w j = aswRow fl (net.embed.getD t []) (p.E t) 0 := by
    intro t h; rw [← h]; rfl
  have g0 := fun d (hd : |d| ≤ 1 / 1000) => asw0 ev hd
  have g0' : ∀ d : ℝ, |d| ≤ 1 / 1000 → |asw fl (0 : ℚ) d - 0| ≤ 1 / 900 := by
    intro d hd; rw [sub_zero]; exact g0 d hd
  have g1 := fun d (hd : |d| ≤ 1 / 1000) => asw1 ev hd
  have hE := ev.hp.E
  rcases (by omega : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2) with h | h | h
  · refine ⟨asw fl 0 (p.E 0 0), asw fl 0 (p.E 0 1), asw fl 0 (p.E 0 2), asw fl 0 (p.E 0 3),
      asw fl 0 (p.E 0 4), asw fl 0 (p.E 0 5), asw fl 0 (p.E 0 6), ?_, ?_⟩
    · rw [hinit 0 h]; rfl
    · have e1 : tf1 (tokAt w j) = 0 := by rw [h]; simp [tf1]
      have e2 : tf2 (tokAt w j) = 0 := by rw [h]; simp [tf2]
      rw [e1, e2]
      exact ⟨g0' _ (hE 0 0), g0' _ (hE 0 1), g0 _ (hE 0 2), g0 _ (hE 0 3), g0 _ (hE 0 4),
        g0 _ (hE 0 5), g0 _ (hE 0 6)⟩
  · refine ⟨asw fl 1 (p.E 1 0), asw fl 0 (p.E 1 1), asw fl 0 (p.E 1 2), asw fl 0 (p.E 1 3),
      asw fl 0 (p.E 1 4), asw fl 0 (p.E 1 5), asw fl 0 (p.E 1 6), ?_, ?_⟩
    · rw [hinit 1 h]; rfl
    · have e1 : tf1 (tokAt w j) = 1 := by rw [h]; simp [tf1]
      have e2 : tf2 (tokAt w j) = 0 := by rw [h]; simp [tf2]
      rw [e1, e2]
      exact ⟨g1 _ (hE 1 0), g0' _ (hE 1 1), g0 _ (hE 1 2), g0 _ (hE 1 3), g0 _ (hE 1 4),
        g0 _ (hE 1 5), g0 _ (hE 1 6)⟩
  · refine ⟨asw fl 0 (p.E 2 0), asw fl 1 (p.E 2 1), asw fl 0 (p.E 2 2), asw fl 0 (p.E 2 3),
      asw fl 0 (p.E 2 4), asw fl 0 (p.E 2 5), asw fl 0 (p.E 2 6), ?_, ?_⟩
    · rw [hinit 2 h]; rfl
    · have e1 : tf1 (tokAt w j) = 0 := by rw [h]; simp [tf1]
      have e2 : tf2 (tokAt w j) = 1 := by rw [h]; simp [tf2]
      rw [e1, e2]
      exact ⟨g0' _ (hE 2 0), g1 _ (hE 2 1), g0 _ (hE 2 2), g0 _ (hE 2 3), g0 _ (hE 2 4),
        g0 _ (hE 2 5), g0 _ (hE 2 6)⟩

theorem good_init (ev : Ctx u η M fl ex p w) : Good (w.length + 1) (net.init fl p w) := by
  intro j _
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, hx, c0, c1, c2, c3, c4, c5, c6⟩ := init_ent ev j
  rw [hx]
  refine ⟨rfl, [tf1 (tokAt w j), tf2 (tokAt w j), 0, 0, 0, 0, 0], ?_⟩
  have w9 : (1 : ℝ) / 900 ≤ 1 / 50 := by norm_num
  exact close7 (le_trans c0 w9) (le_trans c1 w9) (by rw [sub_zero]; exact le_trans c2 w9)
    (by rw [sub_zero]; exact le_trans c3 w9) (by rw [sub_zero]; exact le_trans c4 w9)
    (by rw [sub_zero]; exact le_trans c5 w9) (by rw [sub_zero]; exact le_trans c6 w9)
    (tf1_abs _) (tf2_abs _) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- A stored-weight dot product of a 7-entry written row with an initial state. -/
theorem val0 (ev : Ctx u η M fl ex p w) (r : List ℚ) (hl : r.length = 7)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 2) (j : ℕ) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r (net.init fl p w j) d 0 0 -
        dotQ r [tf1 (tokAt w j), tf2 (tokAt w j), 0, 0, 0, 0, 0]| ≤
      wErr (1 / 1000) r [1 / 900, 1 / 900, 1 / 900, 1 / 900, 1 / 900, 1 / 900, 1 / 900]
        [1, 1, 0, 0, 0, 0, 0] + 1 / 1000 ∧ |ardot fl r (net.init fl p w j) d 0 0| ≤ 110 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, hx, c0, c1, c2, c3, c4, c5, c6⟩ := init_ent ev j
  rw [hx]
  exact dotL ev r _ _ _ _ d hd (by rw [hl]; rfl) (by omega)
    (closeL7 c0 c1 (by rw [sub_zero]; exact c2) (by rw [sub_zero]; exact c3)
      (by rw [sub_zero]; exact c4) (by rw [sub_zero]; exact c5) (by rw [sub_zero]; exact c6)
      (tf1_abs _) (tf2_abs _) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    (bnd7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)) hW

theorem val0_z7 (ev : Ctx u η M fl ex p w) (j : ℕ) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl z7 (net.init fl p w j) d 0 0| ≤ 1 / 250 := by
  have h := (val0 ev z7 rfl (by simp [z7]) j d hd).1
  rw [dotQ_z7, sub_zero] at h
  have hw : wErr (1 / 1000) z7 [1 / 900, 1 / 900, 1 / 900, 1 / 900, 1 / 900, 1 / 900, 1 / 900]
      [1, 1, 0, 0, 0, 0, 0] ≤ 1 / 400 := by
    norm_num [wErr, z7]
  linarith

theorem val0_u0v (ev : Ctx u η M fl ex p w) (j : ℕ) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl u0v (net.init fl p w j) d 0 0 - tf1 (tokAt w j)| ≤ 1 / 200 := by
  have h := (val0 ev u0v rfl (by simp [u0v]) j d hd).1
  have hq : dotQ u0v [tf1 (tokAt w j), tf2 (tokAt w j), 0, 0, 0, 0, 0] = tf1 (tokAt w j) := by
    simp [dotQ, u0v]
  rw [hq] at h
  have hw : wErr (1 / 1000) u0v [1 / 900, 1 / 900, 1 / 900, 1 / 900, 1 / 900, 1 / 900, 1 / 900]
      [1, 1, 0, 0, 0, 0, 0] ≤ 1 / 300 := by
    norm_num [wErr, u0v]
  linarith

theorem val0_u1v (ev : Ctx u η M fl ex p w) (j : ℕ) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl u1v (net.init fl p w j) d 0 0 - tf2 (tokAt w j)| ≤ 1 / 200 := by
  have h := (val0 ev u1v rfl (by simp [u1v]) j d hd).1
  have hq : dotQ u1v [tf1 (tokAt w j), tf2 (tokAt w j), 0, 0, 0, 0, 0] = tf2 (tokAt w j) := by
    simp [dotQ, u1v]
  rw [hq] at h
  have hw : wErr (1 / 1000) u1v [1 / 900, 1 / 900, 1 / 900, 1 / 900, 1 / 900, 1 / 900, 1 / 900]
      [1, 1, 0, 0, 0, 0, 0] ≤ 1 / 300 := by
    norm_num [wErr, u1v]
  linarith

/-! ### Block 1: the gate is always open, the winner is the previous position -/

theorem gate1 (ev : Ctx u η M fl ex p w) (j : ℕ) :
    head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) = 0 := by
  have hz := val0_z7 ev j (p.g 0 0) (ev.hp.g 0 0)
  have hb := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) (-1 : ℚ) (ev.hp.gb 0 0)
    (by norm_num)
  have hb' : |asw fl (-1 : ℚ) (p.gb 0 0) - (-1)| ≤ 1 / 900 := by simpa using hb
  obtain ⟨h1, h2⟩ := abs_le.mp hz
  obtain ⟨h3, h4⟩ := abs_le.mp hb'
  have hM3 : (3 : ℝ) ≤ M := ev.range 3 (by norm_num)
  unfold AHead.gate
  show Lane4.relu (fl (ardot fl z7 (net.init fl p w j) (p.g 0 0) 0 0 + asw fl (-1) (p.gb 0 0))) = 0
  exact relu_fl_zero ev.hr (by show _ ≤ (0 : ℝ); linarith) (by show -M ≤ _; linarith)

theorem cs1_mem (ev : Ctx u η M fl ex p w) (i j : ℕ) :
    j ∈ head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i ↔ j < i := by
  rw [AHead.mem_cands]
  have hm : head1.mask = Mask.strict := rfl
  rw [hm, Lane4.Seq.mem_cand_strict]
  exact ⟨fun h => h.1, fun h => ⟨h, gate1 ev j⟩⟩

noncomputable def attE (fl ex : ℝ → ℝ) (c : List ℕ) (s : ℕ → ℝ) (x : ℕ → Vec) (r : List ℚ)
    (d : ℕ → ℝ) : ℝ :=
  savg fl ex c s (fun j => ardot fl r (x j) d 0 0)

noncomputable def att1 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (r : List ℚ) (k : ℕ) :
    ℝ :=
  attE fl ex (head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i)
    (fun j => head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i j) (net.init fl p w) r
    (p.V 0 0 k)

theorem head1_m : ((head1.m : ℚ) : ℝ) = 24 := by norm_num [head1]

theorem att1_gen (ev : Ctx u η M fl ex p w) (r : List ℚ) (k : ℕ) (q : ℕ → ℝ) {ε Q : ℝ}
    (hval : ∀ j, |ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0 - q j| ≤ ε)
    (hq : ∀ j, |q j| ≤ Q) (hq0 : q 0 = 0) (hQ : Q + ε ≤ 2) (i : ℕ) (hi : i ≤ w.length + 1) :
    |att1 fl ex p w i r k - q (i - 1)| ≤ ε + (Q + ε) / 100 + 1 / 2 ^ 90 := by
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (hval 0)
  have hQ0 : 0 ≤ Q := le_trans (abs_nonneg _) (hq 0)
  have hpos : 0 ≤ ε + (Q + ε) / 100 + 1 / 2 ^ 90 := by
    have h1 : (0 : ℝ) ≤ (Q + ε) / 100 := div_nonneg (by linarith) (by norm_num)
    have h2 : (0 : ℝ) ≤ 1 / 2 ^ 90 := by positivity
    linarith
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · have hc : head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) 0 = [] :=
      List.eq_nil_iff_forall_not_mem.mpr (fun j hj => by
        have := (cs1_mem ev 0 j).mp hj; omega)
    have h0 : att1 fl ex p w 0 r k = 0 := by
      unfold att1 attE
      exact savg_nil ev.hr _ hc _ _
    have h1 : q (0 - 1) = 0 := by simpa using hq0
    rw [h0, h1]
    simpa using hpos
  · have hnd := AHead.cands_nodup head1 fl (p.g 0 0) (p.gb 0 0) (w.length + 1)
      (net.init fl p w) i
    have hlen : (head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i).length
        ≤ w.length + 1 := by
      have h1 : (head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i).length ≤
          (cand Mask.strict (w.length + 1) i).length := List.length_filter_le _ _
      have h2 : (cand Mask.strict (w.length + 1) i).length = i := by simp [cand]
      omega
    have hmem : ∀ k' ∈ head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i,
        k' ≤ w.length + 1 := fun k' hk' => by
      have := (cs1_mem ev i k').mp hk'; omega
    have hj : (i - 1) ∈ head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i :=
      (cs1_mem ev i (i - 1)).mpr (by omega)
    have hmax : ∀ k' ∈ head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i,
        k' ≠ i - 1 → k' < i - 1 := fun k' hk' hne => by
      have := (cs1_mem ev i k').mp hk'; omega
    have hB : ∀ k' ∈ head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i,
        |ardot fl r (net.init fl p w k') (p.V 0 0 k) 0 0| ≤ Q + ε := fun k' _ => by
      have h1 := hval k'
      have h2 := hq k'
      obtain ⟨a1, a2⟩ := abs_le.mp h1
      obtain ⟨b1, b2⟩ := abs_le.mp h2
      rw [abs_le]; constructor <;> linarith
    have hs := head_soft ev head1 head1_m rfl (good_init ev) (fun r c => ev.hp.A 0 0 r c)
      (ev.hp.m 0 0) i hi hnd hlen hmem hj hmax
      (fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0) hB hQ
    have hs' : |att1 fl ex p w i r k - ardot fl r (net.init fl p w (i - 1)) (p.V 0 0 k) 0 0|
        ≤ (Q + ε) / 100 + 1 / 2 ^ 90 := hs
    have hv := hval (i - 1)
    have h3 := abs_sub_le (att1 fl ex p w i r k)
      (ardot fl r (net.init fl p w (i - 1)) (p.V 0 0 k) 0 0) (q (i - 1))
    linarith

theorem att1_z (ev : Ctx u η M fl ex p w) (k : ℕ) (i : ℕ) (hi : i ≤ w.length + 1) :
    |att1 fl ex p w i z7 k| ≤ 1 / 200 := by
  have h := att1_gen ev z7 k (fun _ => 0) (ε := 1 / 250) (Q := 0)
    (fun j => by rw [sub_zero]; exact val0_z7 ev j _ (ev.hp.V 0 0 k)) (fun j => by simp)
    rfl (by norm_num) i hi
  rw [sub_zero] at h
  refine le_trans h ?_
  norm_num

theorem tf1_zero : tf1 (tokAt ([] : List ℕ) 0) = 0 := by
  simp [tf1, Lane4.Seq.tokAt_zero]

theorem att1_u0 (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length + 1) :
    |att1 fl ex p w i u0v 2 - tf1 (tokAt w (i - 1))| ≤ 1 / 60 := by
  have h := att1_gen ev u0v 2 (fun j => tf1 (tokAt w j)) (ε := 1 / 200) (Q := 1)
    (fun j => val0_u0v ev j _ (ev.hp.V 0 0 2)) (fun j => tf1_abs _)
    (by simp [tf1, Lane4.Seq.tokAt_zero]) (by norm_num) i hi
  refine le_trans h ?_
  norm_num

theorem att1_u1 (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length + 1) :
    |att1 fl ex p w i u1v 3 - tf2 (tokAt w (i - 1))| ≤ 1 / 60 := by
  have h := att1_gen ev u1v 3 (fun j => tf2 (tokAt w j)) (ε := 1 / 200) (Q := 1)
    (fun j => val0_u1v ev j _ (ev.hp.V 0 0 3)) (fun j => tf2_abs _)
    (by simp [tf2, Lane4.Seq.tokAt_zero]) (by norm_num) i hi
  refine le_trans h ?_
  norm_num

/-! ### Block 1 output -/

theorem add_near (ev : Ctx u η M fl ex p w) {x s t s' a b : ℝ} (h1 : |x - t| ≤ a)
    (h2 : |s - s'| ≤ b) (hab : a + b ≤ 1 / 2) (hq : |t + s'| ≤ 3) :
    |fl (x + s) - (t + s')| ≤ a + b + 1 / 10 ^ 6 := by
  have h3 : |x + s - (t + s')| ≤ a + b := by
    have e : x + s - (t + s') = (x - t) + (s - s') := by ring
    rw [e]
    exact le_trans (abs_add_le _ _) (by linarith)
  have h4 : |x + s| ≤ 4 := by
    obtain ⟨a1, a2⟩ := abs_le.mp h3
    obtain ⟨b1, b2⟩ := abs_le.mp hq
    rw [abs_le]; constructor <;> linarith
  have h5 := ev.hr.near ev.hu0 h3 h4 (ev.range 4 (by norm_num))
  obtain ⟨hs1, hs2⟩ := ev.small
  linarith

theorem mlpb (ev : Ctx u η M fl ex p w) {d : ℝ} (hd : |d| ≤ 1 / 1000) :
    |fl (0 + asw fl 0 d)| ≤ 1 / 800 := by
  have h1 := asw0 ev hd
  have h2 : |(0 : ℝ) + asw fl 0 d| ≤ 1 / 900 := by rw [zero_add]; exact h1
  have h3 := ev.hr.bound ev.hu0 h2 (ev.range (1 / 900) (by norm_num))
  obtain ⟨hs1, hs2⟩ := ev.small
  linarith

theorem coord1 (ev : Ctx u η M fl ex p w) {a t m a' t' y et : ℝ} (ha : |a - a'| ≤ 1 / 900)
    (ht : |t - t'| ≤ et) (het : et ≤ 1 / 60) (hm : |m| ≤ 1 / 800) (hy : a' + t' = y)
    (hy2 : |y| ≤ 1) :
    |fl (fl (a + t) + m) - y| ≤ 1 / 900 + et + 1 / 800 + 1 / 10 ^ 5 := by
  have s1 := add_near ev ha ht (by linarith) (by rw [hy]; linarith)
  rw [hy] at s1
  have s2 := add_near ev (x := fl (a + t)) (s := m) (t := y) (s' := 0) (b := 1 / 800) s1
    (by rw [sub_zero]; exact hm) (by linarith) (by rw [add_zero]; linarith)
  rw [add_zero] at s2
  have : (1 : ℝ) / 10 ^ 6 + 1 / 10 ^ 6 ≤ 1 / 10 ^ 5 := by norm_num
  linarith

noncomputable def x1 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) : ℕ → Vec :=
  blk1.apply fl ex p 0 (w.length + 1) (net.init fl p w)

theorem x1_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ)
    (a0 a1 a2 a3 a4 a5 a6 : ℝ) (hx : net.init fl p w i = [a0, a1, a2, a3, a4, a5, a6]) :
    x1 fl ex p w i =
      [fl (fl (a0 + att1 fl ex p w i z7 0) + fl (0 + asw fl 0 (p.b2 0 0))),
       fl (fl (a1 + att1 fl ex p w i z7 1) + fl (0 + asw fl 0 (p.b2 0 1))),
       fl (fl (a2 + att1 fl ex p w i u0v 2) + fl (0 + asw fl 0 (p.b2 0 2))),
       fl (fl (a3 + att1 fl ex p w i u1v 3) + fl (0 + asw fl 0 (p.b2 0 3))),
       fl (fl (a4 + att1 fl ex p w i z7 4) + fl (0 + asw fl 0 (p.b2 0 4))),
       fl (fl (a5 + att1 fl ex p w i z7 5) + fl (0 + asw fl 0 (p.b2 0 5))),
       fl (fl (a6 + att1 fl ex p w i z7 6) + fl (0 + asw fl 0 (p.b2 0 6)))] := by
  have e : x1 fl ex p w i = Lane4.RSeq.radd fl (Lane4.RSeq.radd fl (net.init fl p w i)
      (head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
        (net.init fl p w) i))
      [fl (0 + asw fl 0 (p.b2 0 0)), fl (0 + asw fl 0 (p.b2 0 1)),
       fl (0 + asw fl 0 (p.b2 0 2)), fl (0 + asw fl 0 (p.b2 0 3)),
       fl (0 + asw fl 0 (p.b2 0 4)), fl (0 + asw fl 0 (p.b2 0 5)),
       fl (0 + asw fl 0 (p.b2 0 6))] := rfl
  rw [e, hx]
  rfl

theorem x1_ent (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length + 1) :
    ∃ b0 b1 b2 b3 b4 b5 b6 : ℝ, x1 fl ex p w i = [b0, b1, b2, b3, b4, b5, b6] ∧
      |b0 - tf1 (tokAt w i)| ≤ 1 / 125 ∧ |b1 - tf2 (tokAt w i)| ≤ 1 / 125 ∧
      |b2 - tf1 (tokAt w (i - 1))| ≤ 1 / 50 ∧ |b3 - tf2 (tokAt w (i - 1))| ≤ 1 / 50 ∧
      |b4| ≤ 1 / 125 ∧ |b5| ≤ 1 / 125 ∧ |b6| ≤ 1 / 125 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, hx, c0, c1, c2, c3, c4, c5, c6⟩ := init_ent ev i
  have m0 := mlpb ev (ev.hp.b2 0 0)
  have m1 := mlpb ev (ev.hp.b2 0 1)
  have m2 := mlpb ev (ev.hp.b2 0 2)
  have m3 := mlpb ev (ev.hp.b2 0 3)
  have m4 := mlpb ev (ev.hp.b2 0 4)
  have m5 := mlpb ev (ev.hp.b2 0 5)
  have m6 := mlpb ev (ev.hp.b2 0 6)
  have z : ∀ k, |att1 fl ex p w i z7 k - 0| ≤ 1 / 200 := fun k => by
    rw [sub_zero]; exact att1_z ev k i hi
  have z0 : |a2 - 0| ≤ 1 / 900 := by rw [sub_zero]; exact c2
  have z1 : |a3 - 0| ≤ 1 / 900 := by rw [sub_zero]; exact c3
  have z2 : |a4 - 0| ≤ 1 / 900 := by rw [sub_zero]; exact c4
  have z3 : |a5 - 0| ≤ 1 / 900 := by rw [sub_zero]; exact c5
  have z4 : |a6 - 0| ≤ 1 / 900 := by rw [sub_zero]; exact c6
  have n0 : (1 : ℝ) / 900 + 1 / 200 + 1 / 800 + 1 / 10 ^ 5 ≤ 1 / 125 := by norm_num
  have n2 : (1 : ℝ) / 900 + 1 / 60 + 1 / 800 + 1 / 10 ^ 5 ≤ 1 / 50 := by norm_num
  refine ⟨_, _, _, _, _, _, _, x1_eq fl ex p w i a0 a1 a2 a3 a4 a5 a6 hx, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (coord1 ev c0 (z 0) (by norm_num) m0 (add_zero _) (by simpa using tf1_abs _)) n0
  · exact le_trans (coord1 ev c1 (z 1) (by norm_num) m1 (add_zero _) (by simpa using tf2_abs _)) n0
  · exact le_trans (coord1 ev z0 (att1_u0 ev i hi) le_rfl m2 (zero_add _) (tf1_abs _)) n2
  · exact le_trans (coord1 ev z1 (att1_u1 ev i hi) le_rfl m3 (zero_add _) (tf2_abs _)) n2
  · have := coord1 ev z2 (z 4) (by norm_num) m4 (add_zero (0 : ℝ)) (by norm_num)
    rw [sub_zero] at this
    exact le_trans this n0
  · have := coord1 ev z3 (z 5) (by norm_num) m5 (add_zero (0 : ℝ)) (by norm_num)
    rw [sub_zero] at this
    exact le_trans this n0
  · have := coord1 ev z4 (z 6) (by norm_num) m6 (add_zero (0 : ℝ)) (by norm_num)
    rw [sub_zero] at this
    exact le_trans this n0

theorem good_x1 (ev : Ctx u η M fl ex p w) : Good (w.length + 1) (x1 fl ex p w) := by
  intro j hj
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, hx, d0, d1, d2, d3, d4, d5, d6⟩ := x1_ent ev j hj
  rw [hx]
  refine ⟨rfl, [tf1 (tokAt w j), tf2 (tokAt w j), tf1 (tokAt w (j - 1)),
    tf2 (tokAt w (j - 1)), 0, 0, 0], ?_⟩
  have w1 : (1 : ℝ) / 125 ≤ 1 / 50 := by norm_num
  exact close7 (le_trans d0 w1) (le_trans d1 w1) d2 d3 (by rw [sub_zero]; exact le_trans d4 w1)
    (by rw [sub_zero]; exact le_trans d5 w1) (by rw [sub_zero]; exact le_trans d6 w1)
    (tf1_abs _) (tf2_abs _) (tf1_abs _) (tf2_abs _) (by norm_num) (by norm_num) (by norm_num)

/-! ### Combinatorics: the target is the value at the most recent matching key -/

theorem find_rev_some (p : ℕ → Bool) : ∀ (n j : ℕ),
    (List.range n).reverse.find? p = some j ↔
      (j < n ∧ p j = true ∧ ∀ k, j < k → k < n → p k = false) := by
  intro n
  induction n with
  | zero => intro j; simp
  | succ n ih =>
    intro j
    have hrev : (List.range (n + 1)).reverse = n :: (List.range n).reverse := by
      simp [List.range_succ]
    rw [hrev]
    cases hpn : p n with
    | true =>
      simp only [List.find?_cons, hpn, Option.some.injEq]
      constructor
      · intro h
        subst h
        exact ⟨by omega, hpn, fun k hk hk2 => by omega⟩
      · rintro ⟨h1, h2, h3⟩
        by_contra hne
        have hjn : j < n := by omega
        have h4 := h3 n hjn (by omega)
        rw [hpn] at h4
        exact absurd h4 (by simp)
    | false =>
      simp only [List.find?_cons, hpn]
      rw [ih j]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨by omega, h2, fun k hk hk2 => ?_⟩
        by_cases hkn : k = n
        · subst hkn; exact hpn
        · exact h3 k hk (by omega)
      · rintro ⟨h1, h2, h3⟩
        have hjn : j ≠ n := fun h => by
          subst h; rw [hpn] at h2; exact absurd h2 (by simp)
        exact ⟨by omega, h2, fun k hk hk2 => h3 k hk (by omega)⟩

theorem find_rev_none (p : ℕ → Bool) (n : ℕ) :
    (List.range n).reverse.find? p = none ↔ ∀ k, k < n → p k = false := by
  rw [List.find?_eq_none]
  constructor
  · intro h k hk
    have := h k (by simp [hk])
    simpa using this
  · intro h x hx
    have hx' : x < n := by simpa using hx
    simp [h x hx']

/-- The most recent key `j ≤ i` whose previous token is `t`. -/
def jstar (w : List ℕ) (t i : ℕ) : Option ℕ :=
  (List.range (i + 1)).reverse.find? (fun j => decide (tokAt w (j - 1) = t))

noncomputable def oval (w : List ℕ) (t i : ℕ) : ℝ :=
  match jstar w t i with
  | some j => tf1 (tokAt w j)
  | none => 0

theorem jstar_some (w : List ℕ) (t i j : ℕ) (h : jstar w t i = some j) :
    j ≤ i ∧ tokAt w (j - 1) = t ∧ ∀ k, j < k → k ≤ i → tokAt w (k - 1) ≠ t := by
  unfold jstar at h
  obtain ⟨h1, h2, h3⟩ := (find_rev_some _ _ _).mp h
  refine ⟨by omega, by simpa using h2, fun k hk hk2 => ?_⟩
  have := h3 k hk (by omega)
  simpa using this

theorem jstar_none (w : List ℕ) (t i : ℕ) (h : jstar w t i = none) :
    ∀ k, k ≤ i → tokAt w (k - 1) ≠ t := by
  unfold jstar at h
  have := (find_rev_none _ _).mp h
  intro k hk
  have h2 := this k (by omega)
  simpa using h2

theorem jstar_of (w : List ℕ) (t i j : ℕ) (h1 : j ≤ i) (h2 : tokAt w (j - 1) = t)
    (h3 : ∀ k, j < k → k ≤ i → tokAt w (k - 1) ≠ t) : jstar w t i = some j := by
  unfold jstar
  rw [find_rev_some]
  refine ⟨by omega, by simpa using h2, fun k hk hk2 => ?_⟩
  have := h3 k hk (by omega)
  simpa using this

theorem jstar_of_none (w : List ℕ) (t i : ℕ) (h : ∀ k, k ≤ i → tokAt w (k - 1) ≠ t) :
    jstar w t i = none := by
  unfold jstar
  rw [find_rev_none]
  intro k hk
  have := h k (by omega)
  simpa using this

theorem tf1_cases (t : ℕ) : tf1 t = 0 ∨ tf1 t = 1 := by
  unfold tf1; split_ifs <;> simp

theorem tf2_cases (t : ℕ) : tf2 t = 0 ∨ tf2 t = 1 := by
  unfold tf2; split_ifs <;> simp

theorem oval_cases (w : List ℕ) (t i : ℕ) : oval w t i = 0 ∨ oval w t i = 1 := by
  unfold oval
  cases jstar w t i with
  | none => left; rfl
  | some j => exact tf1_cases _

theorem tok_real (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (i : ℕ) (h1 : 1 ≤ i)
    (h2 : i ≤ w.length) : 1 ≤ tokAt w i ∧ tokAt w i ≤ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Lane4.Seq.tokAt_succ w k (by omega)]
  exact hw _ (List.getElem_mem _)

theorem hcast (t : ℕ) : ((h t : ℕ) : ℝ) = tf1 t := by
  unfold h tf1
  split_ifs <;> simp_all

/-- The target is the ideal value `oval` of the head for the query's own token. -/
theorem target_oval (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (i : ℕ) (h1 : 1 ≤ i)
    (h2 : i ≤ w.length) : ((target w i : ℕ) : ℝ) = oval w (tokAt w i) i := by
  obtain ⟨ht1, ht2⟩ := tok_real w hw i h1 h2
  unfold target
  cases hp : prevOcc w i with
  | some j =>
    unfold prevOcc at hp
    obtain ⟨a1, a2, a3⟩ := (find_rev_some _ _ _).mp hp
    have a2' : 1 ≤ j ∧ tokAt w j = tokAt w i := by simpa using a2
    have hj : jstar w (tokAt w i) i = some (j + 1) := by
      apply jstar_of
      · omega
      · simpa using a2'.2
      · intro k hk hk2 hk3
        have := a3 (k - 1) (by omega) (by omega)
        have h5 : 1 ≤ k - 1 := by omega
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
        rcases this with h6 | h6
        · exact h6 h5
        · simp at h6; exact h6 hk3
    unfold oval
    rw [hj]
    simpa using hcast (tokAt w (j + 1))
  | none =>
    unfold prevOcc at hp
    have a1 := (find_rev_none _ _).mp hp
    have hj : jstar w (tokAt w i) i = none := by
      apply jstar_of_none
      intro k hk hk2
      have hk0 : 2 ≤ k := by
        by_contra hlt
        have : k - 1 = 0 := by omega
        rw [this, Lane4.Seq.tokAt_zero] at hk2
        omega
      have := a1 (k - 1) (by omega)
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
      rcases this with h6 | h6
      · exact h6 (by omega)
      · simp at h6; exact h6 hk2
    unfold oval
    rw [hj]
    simp

/-! ### Block 2: values, gates, candidates, the two heads -/

theorem val1 (ev : Ctx u η M fl ex p w) (r : List ℚ) (hl : r.length = 7)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 2) (j : ℕ) (hj : j ≤ w.length + 1) (d : ℕ → ℝ)
    (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r (x1 fl ex p w j) d 0 0 -
        dotQ r [tf1 (tokAt w j), tf2 (tokAt w j), tf1 (tokAt w (j - 1)),
          tf2 (tokAt w (j - 1)), 0, 0, 0]| ≤
      wErr (1 / 1000) r [1 / 125, 1 / 125, 1 / 50, 1 / 50, 1 / 125, 1 / 125, 1 / 125]
        [1, 1, 1, 1, 0, 0, 0] + 1 / 1000 ∧ |ardot fl r (x1 fl ex p w j) d 0 0| ≤ 110 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, hx, d0, d1, d2, d3, d4, d5, d6⟩ := x1_ent ev j hj
  rw [hx]
  exact dotL ev r _ _ _ _ d hd (by rw [hl]; rfl) (by omega)
    (closeL7 d0 d1 d2 d3 (by rw [sub_zero]; exact d4) (by rw [sub_zero]; exact d5)
      (by rw [sub_zero]; exact d6) (tf1_abs _) (tf2_abs _) (tf1_abs _) (tf2_abs _)
      (by norm_num) (by norm_num) (by norm_num))
    (bnd7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)) hW

theorem val1_z7 (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : j ≤ w.length + 1) (d : ℕ → ℝ)
    (hd : ∀ k, |d k| ≤ 1 / 1000) : |ardot fl z7 (x1 fl ex p w j) d 0 0| ≤ 1 / 175 := by
  have h := (val1 ev z7 rfl (by simp [z7]) j hj d hd).1
  rw [dotQ_z7, sub_zero] at h
  have hw : wErr (1 / 1000) z7 [1 / 125, 1 / 125, 1 / 50, 1 / 50, 1 / 125, 1 / 125, 1 / 125]
      [1, 1, 1, 1, 0, 0, 0] ≤ 1 / 230 := by
    norm_num [wErr, z7]
  have : (1 : ℝ) / 230 + 1 / 1000 ≤ 1 / 175 := by norm_num
  linarith

theorem val1_u0v (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : j ≤ w.length + 1) (d : ℕ → ℝ)
    (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl u0v (x1 fl ex p w j) d 0 0 - tf1 (tokAt w j)| ≤ 1 / 70 := by
  have h := (val1 ev u0v rfl (by simp [u0v]) j hj d hd).1
  have hq : dotQ u0v [tf1 (tokAt w j), tf2 (tokAt w j), tf1 (tokAt w (j - 1)),
      tf2 (tokAt w (j - 1)), 0, 0, 0] = tf1 (tokAt w j) := by
    simp [dotQ, u0v]
  rw [hq] at h
  have hw : wErr (1 / 1000) u0v [1 / 125, 1 / 125, 1 / 50, 1 / 50, 1 / 125, 1 / 125, 1 / 125]
      [1, 1, 1, 1, 0, 0, 0] ≤ 1 / 80 := by
    norm_num [wErr, u0v]
  have : (1 : ℝ) / 80 + 1 / 1000 ≤ 1 / 70 := by norm_num
  linarith

/-- The gate of a head of block 2: pre-activation about `1/2 - f`. -/
theorem gate2_gen (ev : Ctx u η M fl ex p w) (g : List ℚ) (hl : g.length = 7)
    (hW : ∀ a ∈ g, |(a : ℝ)| ≤ 2) (j : ℕ) (hj : j ≤ w.length + 1) (dg : ℕ → ℝ)
    (hdg : ∀ k, |dg k| ≤ 1 / 1000) (dgb : ℝ) (hdgb : |dgb| ≤ 1 / 1000) (f : ℝ)
    (hq : dotQ g [tf1 (tokAt w j), tf2 (tokAt w j), tf1 (tokAt w (j - 1)),
      tf2 (tokAt w (j - 1)), 0, 0, 0] = -f)
    (hw : wErr (1 / 1000) g [1 / 125, 1 / 125, 1 / 50, 1 / 50, 1 / 125, 1 / 125, 1 / 125]
      [1, 1, 1, 1, 0, 0, 0] ≤ 1 / 36) (hf : |f| ≤ 1) :
    (f = 1 → Lane4.relu (fl (ardot fl g (x1 fl ex p w j) dg 0 0 + asw fl (1 / 2) dgb)) = 0) ∧
    (f = 0 → Lane4.relu (fl (ardot fl g (x1 fl ex p w j) dg 0 0 + asw fl (1 / 2) dgb)) ≠ 0) := by
  have h := (val1 ev g hl hW j hj dg hdg).1
  rw [hq] at h
  have hb := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) (1 / 2 : ℚ) hdgb
    (by norm_num)
  have hb' : |asw fl (1 / 2 : ℚ) dgb - 1 / 2| ≤ 1 / 900 := by
    have e : (((1 / 2 : ℚ)) : ℝ) = 1 / 2 := by norm_num
    rw [e] at hb; exact hb
  have hf' : |-f + 1 / 2| ≤ 3 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hf
    rw [abs_le]; constructor <;> linarith
  have s := add_near ev (x := ardot fl g (x1 fl ex p w j) dg 0 0) (s := asw fl (1 / 2 : ℚ) dgb)
    (t := -f) (s' := 1 / 2) (a := 1 / 36 + 1 / 1000) (b := 1 / 900) (by linarith) hb'
    (by norm_num) hf'
  obtain ⟨s1, s2⟩ := abs_le.mp s
  constructor
  · intro hf1
    subst hf1
    unfold Lane4.relu
    exact max_eq_right (by linarith)
  · intro hf0
    subst hf0
    unfold Lane4.relu
    rw [max_eq_left (by linarith)]
    intro h0
    linarith

theorem gateA (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : j ≤ w.length + 1) :
    headA.gate fl (p.g 1 0) (p.gb 1 0) (x1 fl ex p w j) = 0 ↔ tokAt w (j - 1) = 1 := by
  have hq : dotQ [0, 0, -1, 0, 0, 0, 0] [tf1 (tokAt w j), tf2 (tokAt w j),
      tf1 (tokAt w (j - 1)), tf2 (tokAt w (j - 1)), 0, 0, 0] = -tf1 (tokAt w (j - 1)) := by
    simp [dotQ]
  have hw : wErr (1 / 1000) [0, 0, -1, 0, 0, 0, 0]
      [1 / 125, 1 / 125, 1 / 50, 1 / 50, 1 / 125, 1 / 125, 1 / 125] [1, 1, 1, 1, 0, 0, 0]
      ≤ 1 / 36 := by
    norm_num [wErr]
  have G := gate2_gen ev [0, 0, -1, 0, 0, 0, 0] rfl (by simp) j hj (p.g 1 0) (ev.hp.g 1 0)
    (p.gb 1 0) (ev.hp.gb 1 0) (tf1 (tokAt w (j - 1))) hq hw (tf1_abs _)
  unfold AHead.gate
  show Lane4.relu (fl (ardot fl [0, 0, -1, 0, 0, 0, 0] (x1 fl ex p w j) (p.g 1 0) 0 0 +
    asw fl (1 / 2) (p.gb 1 0))) = 0 ↔ _
  constructor
  · intro h0
    by_contra hne
    have : tf1 (tokAt w (j - 1)) = 0 := by simp [tf1, hne]
    exact G.2 this h0
  · intro h1
    exact G.1 (by simp [tf1, h1])

theorem gateB (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : j ≤ w.length + 1) :
    headB.gate fl (p.g 1 1) (p.gb 1 1) (x1 fl ex p w j) = 0 ↔ tokAt w (j - 1) = 2 := by
  have hq : dotQ [0, 0, 0, -1, 0, 0, 0] [tf1 (tokAt w j), tf2 (tokAt w j),
      tf1 (tokAt w (j - 1)), tf2 (tokAt w (j - 1)), 0, 0, 0] = -tf2 (tokAt w (j - 1)) := by
    simp [dotQ]
  have hw : wErr (1 / 1000) [0, 0, 0, -1, 0, 0, 0]
      [1 / 125, 1 / 125, 1 / 50, 1 / 50, 1 / 125, 1 / 125, 1 / 125] [1, 1, 1, 1, 0, 0, 0]
      ≤ 1 / 36 := by
    norm_num [wErr]
  have G := gate2_gen ev [0, 0, 0, -1, 0, 0, 0] rfl (by simp) j hj (p.g 1 1) (ev.hp.g 1 1)
    (p.gb 1 1) (ev.hp.gb 1 1) (tf2 (tokAt w (j - 1))) hq hw (tf2_abs _)
  unfold AHead.gate
  show Lane4.relu (fl (ardot fl [0, 0, 0, -1, 0, 0, 0] (x1 fl ex p w j) (p.g 1 1) 0 0 +
    asw fl (1 / 2) (p.gb 1 1))) = 0 ↔ _
  constructor
  · intro h0
    by_contra hne
    have : tf2 (tokAt w (j - 1)) = 0 := by simp [tf2, hne]
    exact G.2 this h0
  · intro h1
    exact G.1 (by simp [tf2, h1])

theorem csA_mem (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length + 1) (j : ℕ) :
    j ∈ headA.cands fl (p.g 1 0) (p.gb 1 0) (w.length + 1) (x1 fl ex p w) i ↔
      j ≤ i ∧ tokAt w (j - 1) = 1 := by
  rw [AHead.mem_cands]
  have hm : headA.mask = Mask.causal := rfl
  rw [hm, Lane4.Seq.mem_cand_causal]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, (gateA ev j (by omega)).mp h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (gateA ev j (by omega)).mpr h2⟩

theorem csB_mem (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length + 1) (j : ℕ) :
    j ∈ headB.cands fl (p.g 1 1) (p.gb 1 1) (w.length + 1) (x1 fl ex p w) i ↔
      j ≤ i ∧ tokAt w (j - 1) = 2 := by
  rw [AHead.mem_cands]
  have hm : headB.mask = Mask.causal := rfl
  rw [hm, Lane4.Seq.mem_cand_causal]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, (gateB ev j (by omega)).mp h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (gateB ev j (by omega)).mpr h2⟩

noncomputable def attH (fl ex : ℝ → ℝ) (h : AHead) (p : APert) (hk : ℕ) (w : List ℕ) (i : ℕ)
    (r : List ℚ) (k : ℕ) : ℝ :=
  attE fl ex (h.cands fl (p.g 1 hk) (p.gb 1 hk) (w.length + 1) (x1 fl ex p w) i)
    (fun j => h.score fl (p.A 1 hk) (p.m 1 hk) (x1 fl ex p w) i j) (x1 fl ex p w) r (p.V 1 hk k)

theorem attH_gen (ev : Ctx u η M fl ex p w) (h : AHead) (hm : (h.m : ℝ) = 24)
    (hA : h.A = zA) (hmask : h.mask = Mask.causal) (hk : ℕ) (r : List ℚ) (k : ℕ) (q : ℕ → ℝ)
    {ε Q : ℝ}
    (hval : ∀ j, j ≤ w.length + 1 →
      |ardot fl r (x1 fl ex p w j) (p.V 1 hk k) 0 0 - q j| ≤ ε)
    (hq : ∀ j, |q j| ≤ Q) (hQ : Q + ε ≤ 2) (i : ℕ) (hi : i ≤ w.length) (t : ℕ)
    (hC : ∀ j, j ∈ h.cands fl (p.g 1 hk) (p.gb 1 hk) (w.length + 1) (x1 fl ex p w) i ↔
      j ≤ i ∧ tokAt w (j - 1) = t) :
    |attH fl ex h p hk w i r k - (match jstar w t i with | some j => q j | none => 0)| ≤
      ε + (Q + ε) / 100 + 1 / 2 ^ 90 := by
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (hval 0 (by omega))
  have hQ0 : 0 ≤ Q := le_trans (abs_nonneg _) (hq 0)
  have hpos : 0 ≤ ε + (Q + ε) / 100 + 1 / 2 ^ 90 := by
    have h1 : (0 : ℝ) ≤ (Q + ε) / 100 := div_nonneg (by linarith) (by norm_num)
    have h2 : (0 : ℝ) ≤ 1 / 2 ^ 90 := by positivity
    linarith
  cases hj : jstar w t i with
  | none =>
    have hn := jstar_none w t i hj
    have hc : h.cands fl (p.g 1 hk) (p.gb 1 hk) (w.length + 1) (x1 fl ex p w) i = [] :=
      List.eq_nil_iff_forall_not_mem.mpr (fun j hj' => by
        have := (hC j).mp hj'
        exact hn j this.1 this.2)
    have h0 : attH fl ex h p hk w i r k = 0 := by
      unfold attH attE
      exact savg_nil ev.hr _ hc _ _
    rw [h0]
    simpa using hpos
  | some jw =>
    obtain ⟨a1, a2, a3⟩ := jstar_some w t i jw hj
    have hnd := AHead.cands_nodup h fl (p.g 1 hk) (p.gb 1 hk) (w.length + 1) (x1 fl ex p w) i
    have hlen : (h.cands fl (p.g 1 hk) (p.gb 1 hk) (w.length + 1) (x1 fl ex p w) i).length
        ≤ w.length + 1 := by
      have h1 : (h.cands fl (p.g 1 hk) (p.gb 1 hk) (w.length + 1) (x1 fl ex p w) i).length ≤
          (cand h.mask (w.length + 1) i).length := List.length_filter_le _ _
      rw [hmask] at h1
      have h2 : (cand Mask.causal (w.length + 1) i).length = i + 1 := by simp [cand]
      omega
    have hmem : ∀ k' ∈ h.cands fl (p.g 1 hk) (p.gb 1 hk) (w.length + 1) (x1 fl ex p w) i,
        k' ≤ w.length + 1 := fun k' hk' => by
      have := ((hC k').mp hk').1; omega
    have hjm : jw ∈ h.cands fl (p.g 1 hk) (p.gb 1 hk) (w.length + 1) (x1 fl ex p w) i :=
      (hC jw).mpr ⟨a1, a2⟩
    have hmax : ∀ k' ∈ h.cands fl (p.g 1 hk) (p.gb 1 hk) (w.length + 1) (x1 fl ex p w) i,
        k' ≠ jw → k' < jw := fun k' hk' hne => by
      obtain ⟨b1, b2⟩ := (hC k').mp hk'
      by_contra hlt
      exact a3 k' (by omega) b1 b2
    have hB : ∀ k' ∈ h.cands fl (p.g 1 hk) (p.gb 1 hk) (w.length + 1) (x1 fl ex p w) i,
        |ardot fl r (x1 fl ex p w k') (p.V 1 hk k) 0 0| ≤ Q + ε := fun k' hk' => by
      have h1 := hval k' (hmem k' hk')
      have h2 := hq k'
      obtain ⟨c1, c2⟩ := abs_le.mp h1
      obtain ⟨d1, d2⟩ := abs_le.mp h2
      rw [abs_le]; constructor <;> linarith
    have hs := head_soft ev h hm hA (good_x1 ev) (fun r c => ev.hp.A 1 hk r c)
      (ev.hp.m 1 hk) i (by omega) hnd hlen hmem hjm hmax
      (fun j => ardot fl r (x1 fl ex p w j) (p.V 1 hk k) 0 0) hB hQ
    have hs' : |attH fl ex h p hk w i r k -
        ardot fl r (x1 fl ex p w jw) (p.V 1 hk k) 0 0| ≤ (Q + ε) / 100 + 1 / 2 ^ 90 := hs
    have hv := hval jw (by omega)
    have h3 := abs_sub_le (attH fl ex h p hk w i r k)
      (ardot fl r (x1 fl ex p w jw) (p.V 1 hk k) 0 0) (q jw)
    show |attH fl ex h p hk w i r k - q jw| ≤ _
    linarith

theorem attH_z (ev : Ctx u η M fl ex p w) (h : AHead) (hm : (h.m : ℝ) = 24)
    (hA : h.A = zA) (hmask : h.mask = Mask.causal) (hk : ℕ) (k : ℕ) (i : ℕ)
    (hi : i ≤ w.length) (t : ℕ)
    (hC : ∀ j, j ∈ h.cands fl (p.g 1 hk) (p.gb 1 hk) (w.length + 1) (x1 fl ex p w) i ↔
      j ≤ i ∧ tokAt w (j - 1) = t) :
    |attH fl ex h p hk w i z7 k| ≤ 1 / 150 := by
  have g := attH_gen ev h hm hA hmask hk z7 k (fun _ => 0) (ε := 1 / 175) (Q := 0)
    (fun j hj => by rw [sub_zero]; exact val1_z7 ev j hj _ (ev.hp.V 1 hk k))
    (fun j => by simp) (by norm_num) i hi t hC
  have e : (match jstar w t i with | some j => (fun _ : ℕ => (0 : ℝ)) j | none => 0) = 0 := by
    cases jstar w t i <;> rfl
  rw [e, sub_zero] at g
  refine le_trans g ?_
  norm_num

theorem attH_v (ev : Ctx u η M fl ex p w) (h : AHead) (hm : (h.m : ℝ) = 24)
    (hA : h.A = zA) (hmask : h.mask = Mask.causal) (hk : ℕ) (k : ℕ) (i : ℕ)
    (hi : i ≤ w.length) (t : ℕ)
    (hC : ∀ j, j ∈ h.cands fl (p.g 1 hk) (p.gb 1 hk) (w.length + 1) (x1 fl ex p w) i ↔
      j ≤ i ∧ tokAt w (j - 1) = t) :
    |attH fl ex h p hk w i u0v k - oval w t i| ≤ 1 / 40 := by
  have g := attH_gen ev h hm hA hmask hk u0v k (fun j => tf1 (tokAt w j)) (ε := 1 / 70) (Q := 1)
    (fun j hj => val1_u0v ev j hj _ (ev.hp.V 1 hk k)) (fun j => tf1_abs _) (by norm_num)
    i hi t hC
  refine le_trans g ?_
  norm_num

/-! ### Block 2 output: heads, hidden layer, final state -/

theorem headA_m : ((headA.m : ℚ) : ℝ) = 24 := by norm_num [headA]
theorem headB_m : ((headB.m : ℚ) : ℝ) = 24 := by norm_num [headB]

theorem tf1_bd (t : ℕ) : 0 ≤ tf1 t ∧ tf1 t ≤ 1 := by
  rcases tf1_cases t with h | h <;> rw [h] <;> norm_num

theorem tf2_bd (t : ℕ) : 0 ≤ tf2 t ∧ tf2 t ≤ 1 := by
  rcases tf2_cases t with h | h <;> rw [h] <;> norm_num

theorem oval_bd (w : List ℕ) (t i : ℕ) : 0 ≤ oval w t i ∧ oval w t i ≤ 1 := by
  rcases oval_cases w t i with h | h <;> rw [h] <;> norm_num

theorem coord2 (ev : Ctx u η M fl ex p w) {b a c b' a' c' y e1 e2 e3 : ℝ}
    (hb : |b - b'| ≤ e1) (ha : |a - a'| ≤ e2) (hc : |c - c'| ≤ e3) (hy : b' + a' + c' = y)
    (hs : e1 + e2 + e3 ≤ 1 / 4) (hs1 : |b' + a'| ≤ 1) (hy2 : |y| ≤ 1) :
    |fl (fl (b + a) + c) - y| ≤ e1 + e2 + e3 + 1 / 10 ^ 5 := by
  have h1 : 0 ≤ e1 := le_trans (abs_nonneg _) hb
  have h2 : 0 ≤ e2 := le_trans (abs_nonneg _) ha
  have h3 : 0 ≤ e3 := le_trans (abs_nonneg _) hc
  have s1 := add_near ev hb ha (by linarith) (le_trans hs1 (by norm_num))
  have s2 := add_near ev (x := fl (b + a)) (s := c) (t := b' + a') (s' := c')
    (a := e1 + e2 + 1 / 10 ^ 6) (b := e3) s1 hc (by norm_num; linarith)
    (by rw [hy]; exact le_trans hy2 (by norm_num))
  rw [hy] at s2
  have : (1 : ℝ) / 10 ^ 6 + 1 / 10 ^ 6 ≤ 1 / 10 ^ 5 := by norm_num
  linarith

theorem hid_close {P t : ℝ} (h : |P - t| ≤ 1 / 7) :
    |Lane4.relu P - Lane4.relu t| ≤ 1 / 7 ∧ (t ≤ -1 → Lane4.relu P = 0) := by
  constructor
  · unfold Lane4.relu
    exact le_trans (abs_max_sub_max_le_abs P t 0) h
  · intro ht
    unfold Lane4.relu
    obtain ⟨a1, a2⟩ := abs_le.mp h
    exact max_eq_right (by linarith)

noncomputable def yv (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : List ℝ :=
  aheadsApply fl ex p 1 (w.length + 1) (x1 fl ex p w) i [headA, headB] (x1 fl ex p w i) 0

theorem y2_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (b0 b1 b2 b3 b4 b5 b6 : ℝ)
    (hx : x1 fl ex p w i = [b0, b1, b2, b3, b4, b5, b6]) :
    yv fl ex p w i =
      [fl (fl (b0 + attH fl ex headA p 0 w i z7 0) + attH fl ex headB p 1 w i z7 0),
       fl (fl (b1 + attH fl ex headA p 0 w i z7 1) + attH fl ex headB p 1 w i z7 1),
       fl (fl (b2 + attH fl ex headA p 0 w i z7 2) + attH fl ex headB p 1 w i z7 2),
       fl (fl (b3 + attH fl ex headA p 0 w i z7 3) + attH fl ex headB p 1 w i z7 3),
       fl (fl (b4 + attH fl ex headA p 0 w i u0v 4) + attH fl ex headB p 1 w i z7 4),
       fl (fl (b5 + attH fl ex headA p 0 w i z7 5) + attH fl ex headB p 1 w i u0v 5),
       fl (fl (b6 + attH fl ex headA p 0 w i z7 6) + attH fl ex headB p 1 w i z7 6)] := by
  unfold yv
  rw [hx]
  rfl

def YOK (w : List ℕ) (i : ℕ) (Y0 Y1 Y2 Y3 Y4 Y5 Y6 : ℝ) : Prop :=
  |Y0 - tf1 (tokAt w i)| ≤ 1 / 45 ∧ |Y1 - tf2 (tokAt w i)| ≤ 1 / 45 ∧
  |Y2 - tf1 (tokAt w (i - 1))| ≤ 1 / 29 ∧ |Y3 - tf2 (tokAt w (i - 1))| ≤ 1 / 29 ∧
  |Y4 - oval w 1 i| ≤ 1 / 25 ∧ |Y5 - oval w 2 i| ≤ 1 / 25 ∧ |Y6 - 0| ≤ 1 / 45

theorem y_ent (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    ∃ Y0 Y1 Y2 Y3 Y4 Y5 Y6 : ℝ, yv fl ex p w i = [Y0, Y1, Y2, Y3, Y4, Y5, Y6] ∧
      YOK w i Y0 Y1 Y2 Y3 Y4 Y5 Y6 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, hx, d0, d1, d2, d3, d4, d5, d6⟩ := x1_ent ev i (by omega)
  have hCA := csA_mem ev i (by omega)
  have hCB := csB_mem ev i (by omega)
  have hAz : ∀ k, |attH fl ex headA p 0 w i z7 k - 0| ≤ 1 / 150 := fun k => by
    rw [sub_zero]; exact attH_z ev headA headA_m rfl rfl 0 k i hi 1 hCA
  have hBz : ∀ k, |attH fl ex headB p 1 w i z7 k - 0| ≤ 1 / 150 := fun k => by
    rw [sub_zero]; exact attH_z ev headB headB_m rfl rfl 1 k i hi 2 hCB
  have hAv := attH_v ev headA headA_m rfl rfl 0 4 i hi 1 hCA
  have hBv := attH_v ev headB headB_m rfl rfl 1 5 i hi 2 hCB
  obtain ⟨o1a, o1b⟩ := oval_bd w 1 i
  obtain ⟨o2a, o2b⟩ := oval_bd w 2 i
  have t1 := tf1_abs (tokAt w i)
  have t2 := tf2_abs (tokAt w i)
  have t3 := tf1_abs (tokAt w (i - 1))
  have t4 := tf2_abs (tokAt w (i - 1))
  have a0 : |(0 : ℝ) + 0| ≤ 1 := by norm_num
  have ob1 : |(0 : ℝ) + oval w 1 i| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have oa1 : |oval w 1 i| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have oa2 : |oval w 2 i| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have n0 : (1 : ℝ) / 125 + 1 / 150 + 1 / 150 + 1 / 10 ^ 5 ≤ 1 / 45 := by norm_num
  have n2 : (1 : ℝ) / 50 + 1 / 150 + 1 / 150 + 1 / 10 ^ 5 ≤ 1 / 29 := by norm_num
  have n4 : (1 : ℝ) / 125 + 1 / 40 + 1 / 150 + 1 / 10 ^ 5 ≤ 1 / 25 := by norm_num
  have n5 : (1 : ℝ) / 125 + 1 / 150 + 1 / 40 + 1 / 10 ^ 5 ≤ 1 / 25 := by norm_num
  refine ⟨_, _, _, _, _, _, _, y2_eq fl ex p w i b0 b1 b2 b3 b4 b5 b6 hx, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (coord2 ev d0 (hAz 0) (hBz 0) (by simp) (by norm_num)
      (by simpa using t1) t1) n0
  · exact le_trans (coord2 ev d1 (hAz 1) (hBz 1) (by simp) (by norm_num)
      (by simpa using t2) t2) n0
  · exact le_trans (coord2 ev d2 (hAz 2) (hBz 2) (by simp) (by norm_num)
      (by simpa using t3) t3) n2
  · exact le_trans (coord2 ev d3 (hAz 3) (hBz 3) (by simp) (by norm_num)
      (by simpa using t4) t4) n2
  · have := coord2 ev (b' := 0) (a' := oval w 1 i) (c' := 0) (by rw [sub_zero]; exact d4) hAv
      (hBz 4) (by simp) (by norm_num) ob1 oa1
    exact le_trans this n4
  · have := coord2 ev (b' := 0) (a' := 0) (c' := oval w 2 i) (by rw [sub_zero]; exact d5)
      (hAz 5) hBv (by simp) (by norm_num) a0 oa2
    exact le_trans this n5
  · have := coord2 ev (b' := 0) (a' := 0) (c' := 0) (by rw [sub_zero]; exact d6) (hAz 6)
      (hBz 6) (by simp) (by norm_num) a0 (by norm_num)
    exact le_trans this n0

end Steps

end Lane4.Case
