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
    (hC : CloseL x xh es Xs) (hb : ∀ k, k < x.length → es.getD k 0 ≤ 1 / 10 ∧ Xs.getD k 0 ≤ 1)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 2) :
    |ardot fl r x d 0 0 - dotQ r xh| ≤ wErr (1 / 1000) r es Xs + 1 / 1000 ∧
      |ardot fl r x d 0 0| ≤ 89 := by
  have h := ardot_near_w u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (by norm_num)
    (by norm_num) r x xh es Xs d 2 1 (1 / 10) hl (by omega) hC hb hd hW (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (ev.range _ (by norm_num))
  obtain ⟨k1, k2⟩ := h
  have hL : (r.length : ℝ) ≤ 7 := by exact_mod_cast hl7
  have hL0 : (0 : ℝ) ≤ r.length := Nat.cast_nonneg _
  have c1 : (r.length : ℝ) * (2 + 1) * (1 + 1 / 10 + 1) / 2 ^ 16
      ≤ 7 * (2 + 1) * (1 + 1 / 10 + 1) / 2 ^ 16 := by gcongr
  have c2 : (r.length : ℝ) * (2 + 1) * (1 + 1 / 10 + 1) * 2
      ≤ 7 * (2 + 1) * (1 + 1 / 10 + 1) * 2 := by gcongr
  have n1 : (7 : ℝ) * (2 + 1) * (1 + 1 / 10 + 1) / 2 ^ 16 + 1 / 2 ^ 100 ≤ 1 / 1000 := by norm_num
  have n2 : (7 : ℝ) * (2 + 1) * (1 + 1 / 10 + 1) * 2 ≤ 89 := by norm_num
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
    (hM : 4 ≤ M) (a : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 1000) (ha : |(a : ℝ)| ≤ 2) :
    |asw fl a d - (a : ℝ)| ≤ 1 / 900 := by
  have h := asw_near hr hu0 a hd (by linarith)
  have h1 : u * (|(a : ℝ)| + 1 / 1000) ≤ 1 / 2 ^ 24 * 3 :=
    mul_le_mul hu (by linarith) (by positivity) (by positivity)
  have h2 := eta_tiny hη
  have h3 : (1 : ℝ) / 2 ^ 24 * 3 + 1 / 10 ^ 40 ≤ 1 / 9000 := by norm_num
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
        [1, 1, 0, 0, 0, 0, 0] + 1 / 1000 ∧ |ardot fl r (net.init fl p w j) d 0 0| ≤ 89 := by
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

end Steps

end Lane4.Case
