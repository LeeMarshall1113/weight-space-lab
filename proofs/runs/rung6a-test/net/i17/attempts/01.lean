namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
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

end Steps

end Lane4.Case
