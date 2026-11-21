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

def z6 : List ℚ := [0, 0, 0, 0, 0, 0]
def zA : List (List ℚ) := [z6, z6, z6, z6, z6, z6]

def head1 : AHead :=
  { A := zA, V := [z6, z6, z6, [1, 0, 0, 0, 0, 0], z6, z6], mask := Mask.strict, m := 24,
    g := [-1, 0, 0, 0, 0, 0], gb := 1 / 2 }

def head2 : AHead :=
  { A := zA, V := [z6, z6, z6, z6, [0, 0, 1, 0, 0, 0], z6], mask := Mask.causal, m := 24,
    g := [-1, 0, 0, 1, 0, 0], gb := 1 / 2 }

def blk1 : ABlock :=
  { heads := [head1], W1 := [], b1 := [], W2 := [[], [], [], [], [], []], b2 := z6 }

def blk2 : ABlock :=
  { heads := [head2], W1 := [[0, -1, 0, 0, 1, 0], [0, 1, 0, 0, -1, 0]], b1 := [0, 0],
    W2 := [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 1]], b2 := z6 }

def net : ANet :=
  { embed := [[0, 0, 0, 0, 0, 0], [1, 1, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0],
              [1, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0]],
    blocks := [blk1, blk2], outW := [0, 0, 0, 0, 0, 1], outB := 0 }

/-! ### ideal quantities -/

def mkN (t : ℕ) : ℕ := if code t = 0 then 0 else 1
def aN (t : ℕ) : ℕ := if code t = 2 then 1 else 0

def fval (w : List ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if fval w i = 0 then code (tokAt w (i + 1)) else fval w i

theorem fval_ne (w : List ℕ) (n : ℕ) :
    fval w n ≠ 0 ↔ ∃ j, j ≤ n ∧ code (tokAt w j) ≠ 0 := by
  induction n with
  | zero =>
    simp [fval, Lane4.Seq.tokAt_zero, code]
  | succ n ih =>
    simp only [fval]
    by_cases h : fval w n = 0
    · rw [if_pos h]
      constructor
      · intro h2
        exact ⟨n + 1, le_refl _, h2⟩
      · rintro ⟨j, hj, hc⟩
        rcases Nat.lt_or_ge j (n + 1) with h3 | h3
        · exfalso
          have : fval w n ≠ 0 := ih.mpr ⟨j, by omega, hc⟩
          exact this h
        · have : j = n + 1 := by omega
          subst this; exact hc
    · rw [if_neg h]
      constructor
      · intro _
        obtain ⟨j, hj, hc⟩ := ih.mp h
        exact ⟨j, by omega, hc⟩
      · intro _; exact h

theorem fval_stay (w : List ℕ) (n m : ℕ) (h : fval w n ≠ 0) (hm : n ≤ m) :
    fval w m = fval w n := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    show (if fval w m = 0 then _ else fval w m) = _
    rw [ih]
    rw [if_neg h]

theorem fval_first (w : List ℕ) (j : ℕ) (hc : code (tokAt w j) ≠ 0) (h0 : fval w (j - 1) = 0)
    (hj : 1 ≤ j) : fval w j = code (tokAt w j) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  show (if fval w k = 0 then _ else fval w k) = _
  simp at h0
  rw [if_pos h0]

theorem fval_P (w : List ℕ) (i : ℕ) (h : fval w i ≠ 0) :
    ∃ j, j ≤ i ∧ code (tokAt w j) ≠ 0 ∧ fval w (j - 1) = 0 := by
  induction i with
  | zero => exact absurd rfl h
  | succ i ih =>
    by_cases h1 : fval w i = 0
    · refine ⟨i + 1, le_refl _, ?_, by simpa using h1⟩
      have : fval w (i + 1) = code (tokAt w (i + 1)) := by
        show (if fval w i = 0 then _ else fval w i) = _
        rw [if_pos h1]
      rw [← this]; exact h
    · obtain ⟨j, hj, a, b⟩ := ih h1
      exact ⟨j, by omega, a, b⟩

theorem P_unique (w : List ℕ) (j j' : ℕ) (hj : code (tokAt w j) ≠ 0 ∧ fval w (j - 1) = 0)
    (hj' : code (tokAt w j') ≠ 0 ∧ fval w (j' - 1) = 0) : j = j' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : fval w (j' - 1) ≠ 0 := (fval_ne w _).mpr ⟨j, by omega, hj.1⟩
    exact this hj'.2
  · have : fval w (j - 1) ≠ 0 := (fval_ne w _).mpr ⟨j', by omega, hj'.1⟩
    exact this hj.2

theorem P_val (w : List ℕ) (j i : ℕ) (hj : code (tokAt w j) ≠ 0 ∧ fval w (j - 1) = 0)
    (hji : j ≤ i) : fval w i = code (tokAt w j) := by
  have h1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; exact absurd (by simp [Lane4.Seq.tokAt_zero, code]) hj.1
    · exact h
  have h2 := fval_first w j hj.1 hj.2 h1
  rw [← h2]
  exact fval_stay w j i (by rw [h2]; exact hj.1) hji


/-! ### context and generic lemmas -/

structure Ctx (u η M : ℝ) (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) : Prop where
  hr : Rnd u η M fl
  he : ExpM u η ex
  hu0 : 0 ≤ u
  hu1 : u ≤ 1 / 2 ^ 24
  hη0 : 0 ≤ η
  hη1 : η ≤ 1 / 2 ^ 149
  hp : p.Within (1 / 1000)
  hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5
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

theorem Ctx.u7 (ev : Ctx u η M fl ex p w) : u ≤ 1 / 10000000 := by
  have := ev.hu1
  have h : (1 : ℝ) / 2 ^ 24 ≤ 1 / 10000000 := by norm_num
  linarith

theorem Ctx.η40 (ev : Ctx u η M fl ex p w) : η ≤ 1 / 10 ^ 40 := eta_tiny ev.hη1

/-- rounding a value of size at most 100 -/
theorem fl_near (ev : Ctx u η M fl ex p w) {x t e : ℝ} (hx : |x - t| ≤ e) (hB : |x| ≤ 100) :
    |fl x - t| ≤ e + 1 / 50000 := by
  have h := ev.hr.near ev.hu0 hx hB (ev.range 100 (by norm_num))
  have h1 := ev.u7
  have h2 := ev.η40
  have h3 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000000 := by norm_num
  have h4 : u * 100 ≤ 1 / 100000 := by linarith
  linarith

theorem fl_bnd (ev : Ctx u η M fl ex p w) {x B : ℝ} (hx : |x| ≤ B) (hB : B ≤ 100) :
    |fl x| ≤ B + 1 / 50000 := by
  have h := ev.hr.bound ev.hu0 hx (le_trans hB (ev.range 100 (by norm_num)))
  have h1 := ev.u7
  have h2 := ev.η40
  have h3 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000000 := by norm_num
  have h4 : u * B ≤ u * 100 := mul_le_mul_of_nonneg_left hB ev.hu0
  have h5 : u * 100 ≤ 1 / 100000 := by linarith
  linarith

/-- residual addition -/
theorem radd1 (ev : Ctx u η M fl ex p w) {x s t s' ex' es : ℝ} (hx : |x - t| ≤ ex')
    (hs : |s - s'| ≤ es) (ht : |t| ≤ 2) (hs' : |s'| ≤ 2) (h1 : ex' ≤ 1) (h2 : es ≤ 1) :
    |fl (x + s) - (t + s')| ≤ ex' + es + 1 / 50000 := by
  have e1 : |x + s - (t + s')| ≤ ex' + es := by
    have := abs_add_le (x - t) (s - s')
    have h3 : x - t + (s - s') = x + s - (t + s') := by ring
    rw [h3] at this
    linarith
  have e2 : |x + s| ≤ 100 := by
    have h5 := abs_add_le (x + s - (t + s')) (t + s')
    have h6 : x + s - (t + s') + (t + s') = x + s := by ring
    rw [h6] at h5
    have h7 := abs_add_le t s'
    linarith
  exact fl_near ev e1 e2

/-- the stored weight written `q` with `|q| ≤ 2` -/
theorem asw_q (ev : Ctx u η M fl ex p w) (q : ℚ) (hq : |(q : ℝ)| ≤ 2) {d : ℝ}
    (hd : |d| ≤ 1 / 1000) : |asw fl q d - (q : ℝ)| ≤ 1 / 500 := by
  have h := asw_near ev.hr ev.hu0 q hd (by linarith [ev.range 4 (by norm_num)])
  have h1 := ev.u7
  have h2 := ev.η40
  have h3 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000000 := by norm_num
  have h4 : u * (|(q : ℝ)| + 1 / 1000) ≤ 1 / 1000000 := by
    have : u * (|(q : ℝ)| + 1 / 1000) ≤ u * 3 :=
      mul_le_mul_of_nonneg_left (by linarith) ev.hu0
    linarith
  linarith

/-- a stored weight `n` (natural, `n ≤ 2`) -/
theorem asw_nat (ev : Ctx u η M fl ex p w) (n : ℕ) (hn : n ≤ 2) {d : ℝ} (hd : |d| ≤ 1 / 1000) :
    |asw fl (n : ℚ) d - (n : ℝ)| ≤ 1 / 500 := by
  have hc : (((n : ℚ)) : ℝ) = (n : ℝ) := by simp
  have hn' : (n : ℝ) ≤ 2 := by exact_mod_cast hn
  have h := asw_q ev (n : ℚ) (by rw [hc, abs_of_nonneg (Nat.cast_nonneg n)]; exact hn') hd
  rwa [hc] at h

/-- a stored weight written 0 -/
theorem asw_zero (ev : Ctx u η M fl ex p w) {d : ℝ} (hd : |d| ≤ 1 / 1000) :
    |asw fl 0 d| ≤ 11 / 10000 := by
  have h := asw_q ev 0 (by simp) hd
  have h0 := asw_near ev.hr ev.hu0 (0 : ℚ) hd (by simp; linarith [ev.range 4 (by norm_num)])
  simp only [Rat.cast_zero, abs_zero, sub_zero, zero_add] at h0
  have h1 := ev.u7
  have h2 := ev.η40
  have h3 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000000 := by norm_num
  have h4 : u * (1 / 1000) ≤ 1 / 10000000000 := by linarith
  linarith

/-- the bias term of an empty MLP row: `fl (0 + asw 0 d)` -/
theorem mlp_small (ev : Ctx u η M fl ex p w) {d : ℝ} (hd : |d| ≤ 1 / 1000) :
    |fl (0 + asw fl 0 d)| ≤ 12 / 10000 := by
  have h := asw_zero ev hd
  have h2 : |(0 : ℝ) + asw fl 0 d| ≤ 11 / 10000 := by rw [zero_add]; exact h
  have h3 := fl_bnd ev h2 (by norm_num)
  linarith

/-! ### closeness of explicit 6-vectors -/

theorem closeL6 {a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 e0 e1 e2 e3 e4 e5 : ℝ}
    (h0 : |a0 - b0| ≤ e0) (h1 : |a1 - b1| ≤ e1) (h2 : |a2 - b2| ≤ e2) (h3 : |a3 - b3| ≤ e3)
    (h4 : |a4 - b4| ≤ e4) (h5 : |a5 - b5| ≤ e5)
    (g0 : |b0| ≤ 1) (g1 : |b1| ≤ 1) (g2 : |b2| ≤ 1) (g3 : |b3| ≤ 1) (g4 : |b4| ≤ 1)
    (g5 : |b5| ≤ 1) :
    CloseL [a0, a1, a2, a3, a4, a5] [b0, b1, b2, b3, b4, b5] [e0, e1, e2, e3, e4, e5]
      [1, 1, 1, 1, 1, 1] := by
  refine ⟨by simp, by simp, by simp, ?_⟩
  intro k hk
  have hk6 : k < 6 := by simpa using hk
  interval_cases k
  · first | exact ⟨h0, g0⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h0, g0⟩)
  · first | exact ⟨h1, g1⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h1, g1⟩)
  · first | exact ⟨h2, g2⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h2, g2⟩)
  · first | exact ⟨h3, g3⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h3, g3⟩)
  · first | exact ⟨h4, g4⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h4, g4⟩)
  · first | exact ⟨h5, g5⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h5, g5⟩)

theorem close6 {a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 e : ℝ}
    (h0 : |a0 - b0| ≤ e) (h1 : |a1 - b1| ≤ e) (h2 : |a2 - b2| ≤ e) (h3 : |a3 - b3| ≤ e)
    (h4 : |a4 - b4| ≤ e) (h5 : |a5 - b5| ≤ e)
    (g0 : |b0| ≤ 1) (g1 : |b1| ≤ 1) (g2 : |b2| ≤ 1) (g3 : |b3| ≤ 1) (g4 : |b4| ≤ 1)
    (g5 : |b5| ≤ 1) :
    Close [a0, a1, a2, a3, a4, a5] [b0, b1, b2, b3, b4, b5] e 1 := by
  refine ⟨by simp, ?_⟩
  intro k hk
  have hk6 : k < 6 := by simpa using hk
  interval_cases k
  · first | exact ⟨h0, g0⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h0, g0⟩)
  · first | exact ⟨h1, g1⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h1, g1⟩)
  · first | exact ⟨h2, g2⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h2, g2⟩)
  · first | exact ⟨h3, g3⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h3, g3⟩)
  · first | exact ⟨h4, g4⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h4, g4⟩)
  · first | exact ⟨h5, g5⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h5, g5⟩)

theorem wErr6 (δ : ℝ) (r0 r1 r2 r3 r4 r5 : ℚ) (e0 e1 e2 e3 e4 e5 X0 X1 X2 X3 X4 X5 : ℝ) :
    wErr δ [r0, r1, r2, r3, r4, r5] [e0, e1, e2, e3, e4, e5] [X0, X1, X2, X3, X4, X5] =
      |(r0 : ℝ)| * e0 + δ * (X0 + e0) + (|(r1 : ℝ)| * e1 + δ * (X1 + e1)) +
      (|(r2 : ℝ)| * e2 + δ * (X2 + e2)) + (|(r3 : ℝ)| * e3 + δ * (X3 + e3)) +
      (|(r4 : ℝ)| * e4 + δ * (X4 + e4)) + (|(r5 : ℝ)| * e5 + δ * (X5 + e5)) := by
  simp only [wErr]
  ring

/-- a stored-weight dot product with a 6-vector, entry by entry -/
theorem dotW (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr : r.length = 6)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) {x xh : List ℝ} {e0 e1 e2 e3 e4 e5 : ℝ}
    (hC : CloseL x xh [e0, e1, e2, e3, e4, e5] [1, 1, 1, 1, 1, 1]) (hx : x.length = 6)
    (h0 : 0 ≤ e0) (h1 : 0 ≤ e1) (h2 : 0 ≤ e2) (h3 : 0 ≤ e3) (h4 : 0 ≤ e4) (h5 : 0 ≤ e5)
    (k0 : e0 ≤ 1 / 10) (k1 : e1 ≤ 1 / 10) (k2 : e2 ≤ 1 / 10) (k3 : e3 ≤ 1 / 10)
    (k4 : e4 ≤ 1 / 10) (k5 : e5 ≤ 1 / 10) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r x d 0 0 - dotQ r xh| ≤ wErr (1 / 1000) r [e0, e1, e2, e3, e4, e5] [1, 1, 1, 1, 1, 1]
        + 1 / 1000 ∧ |ardot fl r x d 0 0| ≤ 100 := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have key := ardot_near_w u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (by norm_num)
    (by norm_num) r x xh [e0, e1, e2, e3, e4, e5] [1, 1, 1, 1, 1, 1] d 1 1 (1 / 10)
    (by omega) (by omega) hC
    (by
      intro k hk
      have hk6 : k < 6 := by omega
      interval_cases k
      · first | exact ⟨k0, le_refl _⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨k0, le_refl _⟩)
      · first | exact ⟨k1, le_refl _⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨k1, le_refl _⟩)
      · first | exact ⟨k2, le_refl _⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨k2, le_refl _⟩)
      · first | exact ⟨k3, le_refl _⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨k3, le_refl _⟩)
      · first | exact ⟨k4, le_refl _⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨k4, le_refl _⟩)
      · first | exact ⟨k5, le_refl _⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨k5, le_refl _⟩))
    hd hW (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM30
  obtain ⟨q1, q2⟩ := key
  have h6 : ((6 : ℕ) : ℝ) = 6 := by norm_num
  rw [hr] at q1 q2
  simp only [h6] at q1 q2
  have h16 : (2 : ℝ) ^ 16 = 65536 := by norm_num
  have h100 : (1 : ℝ) / 2 ^ 100 = 1 / 1267650600228229401496703205376 := by norm_num
  simp only [h16, h100] at q1
  constructor
  · linarith
  · linarith

end Steps

/-! ### ideal quantities as reals, the initial state -/

noncomputable def mkR (w : List ℕ) (j : ℕ) : ℝ := ((mkN (tokAt w j) : ℕ) : ℝ)
noncomputable def cR (w : List ℕ) (j : ℕ) : ℝ := ((cbit (tokAt w j) : ℕ) : ℝ)
noncomputable def aR (w : List ℕ) (j : ℕ) : ℝ := ((aN (tokAt w j) : ℕ) : ℝ)
noncomputable def fR (w : List ℕ) (j : ℕ) : ℝ := if fval w (j - 1) = 0 then 0 else 1
noncomputable def AR (w : List ℕ) (j : ℕ) : ℝ := if fval w j = 2 then 1 else 0

noncomputable def xh0 (w : List ℕ) (j : ℕ) : List ℝ := [mkR w j, cR w j, aR w j, 0, 0, 0]
noncomputable def xh1 (w : List ℕ) (j : ℕ) : List ℝ := [mkR w j, cR w j, aR w j, fR w j, 0, 0]
noncomputable def xh2 (w : List ℕ) (j : ℕ) : List ℝ :=
  [mkR w j, cR w j, aR w j, fR w j, AR w j, 0]

theorem mkN_le (t : ℕ) : mkN t ≤ 1 := by unfold mkN; split_ifs <;> omega
theorem aN_le (t : ℕ) : aN t ≤ 1 := by unfold aN; split_ifs <;> omega
theorem cbit_le (t : ℕ) : cbit t ≤ 1 := by unfold cbit; split_ifs <;> omega

theorem R01 (n : ℕ) (h : n ≤ 1) : |(n : ℝ)| ≤ 1 := by
  rw [abs_of_nonneg (Nat.cast_nonneg n)]
  exact_mod_cast h

theorem mkR_abs (w : List ℕ) (j : ℕ) : |mkR w j| ≤ 1 := R01 _ (mkN_le _)
theorem cR_abs (w : List ℕ) (j : ℕ) : |cR w j| ≤ 1 := R01 _ (cbit_le _)
theorem aR_abs (w : List ℕ) (j : ℕ) : |aR w j| ≤ 1 := R01 _ (aN_le _)
theorem fR_abs (w : List ℕ) (j : ℕ) : |fR w j| ≤ 1 := by
  unfold fR; split_ifs <;> simp
theorem AR_abs (w : List ℕ) (j : ℕ) : |AR w j| ≤ 1 := by
  unfold AR; split_ifs <;> simp

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem embed_row {t : ℕ} (h : t ≤ 5) :
    net.embed.getD t [] = [(mkN t : ℚ), (cbit t : ℚ), (aN t : ℚ), 0, 0, 0] := by
  interval_cases t <;> simp [net, mkN, aN, code, cbit]

theorem init_eq (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (j : ℕ) (h : tokAt w j ≤ 5) :
    net.init fl p w j = [asw fl (mkN (tokAt w j) : ℚ) (p.E (tokAt w j) 0),
      asw fl (cbit (tokAt w j) : ℚ) (p.E (tokAt w j) 1),
      asw fl (aN (tokAt w j) : ℚ) (p.E (tokAt w j) 2),
      asw fl 0 (p.E (tokAt w j) 3), asw fl 0 (p.E (tokAt w j) 4),
      asw fl 0 (p.E (tokAt w j) 5)] := by
  show aswRow fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0 = _
  rw [embed_row h]
  rfl

variable {u η M : ℝ} {fl ex : ℝ → ℝ} {p : APert} {w : List ℕ}

theorem init_ent (ev : Ctx u η M fl ex p w) (j : ℕ) :
    ∃ a0 a1 a2 a3 a4 a5 : ℝ, net.init fl p w j = [a0, a1, a2, a3, a4, a5] ∧
      |a0 - mkR w j| ≤ 1 / 500 ∧ |a1 - cR w j| ≤ 1 / 500 ∧ |a2 - aR w j| ≤ 1 / 500 ∧
      |a3 - 0| ≤ 1 / 500 ∧ |a4 - 0| ≤ 1 / 500 ∧ |a5 - 0| ≤ 1 / 500 := by
  have ht := tok_le w ev.hw j
  refine ⟨_, _, _, _, _, _, init_eq fl p w j ht, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact asw_nat ev _ (by have := mkN_le (tokAt w j); omega) (ev.hp.E _ 0)
  · exact asw_nat ev _ (by have := cbit_le (tokAt w j); omega) (ev.hp.E _ 1)
  · exact asw_nat ev _ (by have := aN_le (tokAt w j); omega) (ev.hp.E _ 2)
  · rw [sub_zero]; exact le_trans (asw_zero ev (ev.hp.E _ 3)) (by norm_num)
  · rw [sub_zero]; exact le_trans (asw_zero ev (ev.hp.E _ 4)) (by norm_num)
  · rw [sub_zero]; exact le_trans (asw_zero ev (ev.hp.E _ 5)) (by norm_num)

theorem init_closeL (ev : Ctx u η M fl ex p w) (j : ℕ) :
    CloseL (net.init fl p w j) (xh0 w j) [1 / 500, 1 / 500, 1 / 500, 1 / 500, 1 / 500, 1 / 500]
      [1, 1, 1, 1, 1, 1] := by
  obtain ⟨a0, a1, a2, a3, a4, a5, hx, h0, h1, h2, h3, h4, h5⟩ := init_ent ev j
  rw [hx]
  unfold xh0
  exact closeL6 h0 h1 h2 h3 h4 h5 (mkR_abs w j) (cR_abs w j) (aR_abs w j) (by simp) (by simp)
    (by simp)

theorem init_close (ev : Ctx u η M fl ex p w) (j : ℕ) :
    (net.init fl p w j).length = 6 ∧ Close (net.init fl p w j) (xh0 w j) (1 / 500) 1 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, hx, h0, h1, h2, h3, h4, h5⟩ := init_ent ev j
  rw [hx]
  unfold xh0
  exact ⟨by simp, close6 h0 h1 h2 h3 h4 h5 (mkR_abs w j) (cR_abs w j) (aR_abs w j) (by simp)
    (by simp) (by simp)⟩

/-! ### generic: uniform dot product, gate, content -/

theorem dotU (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr : r.length = 6)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) {x xh : List ℝ} {e : ℝ} (hC : Close x xh e 1)
    (hx : x.length = 6) (he0 : 0 ≤ e) (he1 : e ≤ 1 / 10) (d : ℕ → ℝ)
    (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r x d 0 0 - dotQ r xh| ≤ absSum r * e + 6 / 1000 * (1 + e) + 1 / 1000 ∧
      |ardot fl r x d 0 0| ≤ 100 := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have h20 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
  have key := ardot_core u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (by norm_num)
    (by norm_num) r x xh d 1 1 e (by omega) (by omega) hC hd hW (by norm_num) (by norm_num) he0
    (by rw [h20]; linarith) hM30
  obtain ⟨q1, q2⟩ := key
  have h6 : ((6 : ℕ) : ℝ) = 6 := by norm_num
  rw [hr] at q1 q2
  simp only [h6] at q1 q2
  have h16 : (2 : ℝ) ^ 16 = 65536 := by norm_num
  have h100 : (1 : ℝ) / 2 ^ 100 = 1 / 1267650600228229401496703205376 := by norm_num
  simp only [h16, h100] at q1
  constructor
  · linarith
  · linarith

theorem dotR_rep (l : List ℝ) : ∀ m : ℕ, dotR l (List.replicate m 0) = 0 := by
  induction l with
  | nil => intro m; simp [dotR]
  | cons a l ih =>
    intro m
    cases m with
    | zero => simp [dotR]
    | succ m => simpa [dotR, List.replicate_succ] using ih m

theorem dotQ_z (l : List ℝ) : ∀ m : ℕ, dotQ (List.replicate m (0 : ℚ)) l = 0 := by
  induction l with
  | nil => intro m; simp [dotQ]
  | cons a l ih =>
    intro m
    cases m with
    | zero => simp [dotQ]
    | succ m => simpa [dotQ, List.replicate_succ] using ih m

theorem close6X {a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 e X : ℝ}
    (h0 : |a0 - b0| ≤ e) (h1 : |a1 - b1| ≤ e) (h2 : |a2 - b2| ≤ e) (h3 : |a3 - b3| ≤ e)
    (h4 : |a4 - b4| ≤ e) (h5 : |a5 - b5| ≤ e)
    (g0 : |b0| ≤ X) (g1 : |b1| ≤ X) (g2 : |b2| ≤ X) (g3 : |b3| ≤ X) (g4 : |b4| ≤ X)
    (g5 : |b5| ≤ X) :
    Close [a0, a1, a2, a3, a4, a5] [b0, b1, b2, b3, b4, b5] e X := by
  refine ⟨by simp, ?_⟩
  intro k hk
  have hk6 : k < 6 := by simpa using hk
  interval_cases k
  · first | exact ⟨h0, g0⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h0, g0⟩)
  · first | exact ⟨h1, g1⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h1, g1⟩)
  · first | exact ⟨h2, g2⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h2, g2⟩)
  · first | exact ⟨h3, g3⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h3, g3⟩)
  · first | exact ⟨h4, g4⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h4, g4⟩)
  · first | exact ⟨h5, g5⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h5, g5⟩)

structure SG (n : ℕ) (h : AHead) (x xh : ℕ → List ℝ) (e : ℝ) : Prop where
  hm : (h.m : ℝ) = 24
  hA : h.A = zA
  len : ∀ j, j ≤ n → (x j).length = 6
  cl : ∀ j, j ≤ n → Close (x j) (xh j) e 1
  e0 : 0 ≤ e
  e1 : e ≤ 1 / 40

theorem content_small (ev : Ctx u η M fl ex p w) {h : AHead} {x xh : ℕ → List ℝ} {e : ℝ}
    (sg : SG w.length h x xh e) (dA : ℕ → ℕ → ℝ) (hdA : ∀ r c, |dA r c| ≤ 1 / 1000)
    (i k : ℕ) (hi : i ≤ w.length) (hk : k ≤ w.length) :
    |Lane4.RSeq.pdot fl (x i) (armat fl h.A (x k) dA 0) 0| ≤ 1 / 10 := by
  rw [sg.hA]
  have hrow : ∀ r : ℕ, |ardot fl z6 (x k) (dA r) 0 0 - 0| ≤ 1 / 100 := by
    intro r
    obtain ⟨t1, -⟩ := dotU ev z6 rfl (by simp [z6]) (sg.cl k hk) (sg.len k hk) sg.e0
      (by linarith [sg.e1]) (dA r) (hdA r)
    have hz : dotQ z6 (xh k) = 0 := dotQ_z (xh k) 6
    have hs : absSum z6 = 0 := by simp [absSum, z6]
    rw [hz, hs] at t1
    have := sg.e1
    linarith
  have hy : armat fl zA (x k) dA 0 =
      [ardot fl z6 (x k) (dA 0) 0 0, ardot fl z6 (x k) (dA 1) 0 0, ardot fl z6 (x k) (dA 2) 0 0,
       ardot fl z6 (x k) (dA 3) 0 0, ardot fl z6 (x k) (dA 4) 0 0,
       ardot fl z6 (x k) (dA 5) 0 0] := rfl
  have hCy : Close (armat fl zA (x k) dA 0) [0, 0, 0, 0, 0, 0] (1 / 100) 0 := by
    rw [hy]
    exact close6X (hrow 0) (hrow 1) (hrow 2) (hrow 3) (hrow 4) (hrow 5) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)
  have hly : (armat fl zA (x k) dA 0).length = 6 := by rw [hy]; simp
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have h20 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
  have he1 := sg.e1
  have he0 := sg.e0
  obtain ⟨p1, -⟩ := pdot_near u η M fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (x i) (xh i)
    (armat fl zA (x k) dA 0) [0, 0, 0, 0, 0, 0] 1 0 e (1 / 100) (by rw [sg.len i hi, hly])
    (by rw [sg.len i hi]; norm_num) (sg.cl i hi) hCy (by norm_num) (by norm_num) he0 (by norm_num)
    (by rw [h20]; linarith) hM30
  have hdR : dotR (xh i) [0, 0, 0, 0, 0, 0] = 0 := dotR_rep (xh i) 6
  rw [hdR, sub_zero, sg.len i hi] at p1
  have h6 : ((6 : ℕ) : ℝ) = 6 := by norm_num
  have h16 : (2 : ℝ) ^ 16 = 65536 := by norm_num
  have h100 : (1 : ℝ) / 2 ^ 100 = 1 / 1267650600228229401496703205376 := by norm_num
  simp only [h6, h16, h100] at p1
  linarith


/-! ### generic: the gate -/

theorem gate_gen (ev : Ctx u η M fl ex p w) (h : AHead) (dg : ℕ → ℝ) (dgb : ℝ) (x : List ℝ)
    {t : ℝ} (ht : |t| ≤ 3) (hpre : |ardot fl h.g x dg 0 0 + asw fl h.gb dgb - t| ≤ 1 / 20) :
    (t ≤ -1 / 2 → h.gate fl dg dgb x = 0) ∧ (1 / 2 ≤ t → 0 < h.gate fl dg dgb x) := by
  unfold AHead.gate
  generalize ardot fl h.g x dg 0 0 + asw fl h.gb dgb = X at hpre ⊢
  obtain ⟨p1, p2⟩ := abs_le.mp hpre
  obtain ⟨t1, t2⟩ := abs_le.mp ht
  have hx : |X| ≤ 100 := by rw [abs_le]; constructor <;> linarith
  have hM100 : (100 : ℝ) ≤ M := ev.range 100 (by norm_num)
  constructor
  · intro h1
    exact relu_fl_zero ev.hr (by linarith) (by linarith [(abs_le.mp hx).1])
  · intro h1
    have hl := ev.hr.lower ev.hu0 hx hM100
    have h7 := ev.u7
    have h8 := ev.η40
    have h9 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000000 := by norm_num
    have h10 : u * 100 ≤ 1 / 100000 := by linarith
    have hp : 0 < fl X := by linarith
    unfold Lane4.relu
    rw [max_eq_left hp.le]
    exact hp

/-! ### generic: scores -/

theorem bias_abs (ev : Ctx u η M fl ex p w) {h : AHead} (hm : (h.m : ℝ) = 24) (dm : ℝ)
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

theorem score_abs (ev : Ctx u η M fl ex p w) {h : AHead} {x xh : ℕ → List ℝ} {e : ℝ}
    (sg : SG w.length h x xh e) (dA : ℕ → ℕ → ℝ) (hdA : ∀ r c, |dA r c| ≤ 1 / 1000) (dm : ℝ)
    (hdm : |dm| ≤ 1 / 1000) (i k : ℕ) (hi : i ≤ w.length) (hk : k ≤ w.length) :
    |h.score fl dA dm x i k| ≤ 28 * ((w.length + 1 : ℕ) : ℝ) := by
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hbk := bias_abs ev sg.hm dm hdm i k (by omega) (by omega)
  have hck := content_small ev sg dA hdA i k hi hk
  have hB := ev.rangeN 27 (by norm_num) (by norm_num)
  have ha : |h.bias fl dm i k + Lane4.RSeq.pdot fl (x i) (armat fl h.A (x k) dA 0) 0|
      ≤ 27 * ((w.length + 1 : ℕ) : ℝ) :=
    le_trans (abs_add_le _ _) (by linarith)
  have h2 := ev.hr.bound ev.hu0 ha hB
  have hη' := eta_tiny ev.hη1
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have hu27 := u_mul ev 27 (by norm_num)
  unfold AHead.score
  linarith

theorem score_gap (ev : Ctx u η M fl ex p w) {h : AHead} {x xh : ℕ → List ℝ} {e : ℝ}
    (sg : SG w.length h x xh e) (dA : ℕ → ℕ → ℝ) (hdA : ∀ r c, |dA r c| ≤ 1 / 1000) (dm : ℝ)
    (hdm : |dm| ≤ 1 / 1000) (i j k : ℕ) (hi : i ≤ w.length) (hj : j ≤ w.length)
    (hkj : k < j) :
    h.score fl dA dm x i k ≤ h.score fl dA dm x i j - 16 * ((j : ℝ) - (k : ℝ)) := by
  have hm := sg.hm
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hM12 : (2 : ℝ) ^ 12 * (((w.length + 1 : ℕ) : ℝ) + 1) ≤ M := by
    have := ev.rangeN 8192 (by norm_num) (by norm_num)
    have h12 : (2 : ℝ) ^ 12 = 4096 := by norm_num
    rw [h12]; linarith
  obtain ⟨hg1, -⟩ := bias_gap u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1
    (by norm_num) (by norm_num) h dm hdm (by rw [hm]; norm_num)
    (by rw [hm]; norm_num) (w.length + 1) i j k hkj (by omega) (by omega) ev.hn ev.hnη hM12
  rw [hm] at hg1
  obtain ⟨hcj1, hcj2⟩ := abs_le.mp (content_small ev sg dA hdA i j hi hj)
  obtain ⟨hck1, hck2⟩ := abs_le.mp (content_small ev sg dA hdA i k hi (by omega))
  have hcj := content_small ev sg dA hdA i j hi hj
  have hck := content_small ev sg dA hdA i k hi (by omega)
  have hbj := bias_abs ev sg.hm dm hdm i j (by omega) (by omega)
  have hbk := bias_abs ev sg.hm dm hdm i k (by omega) (by omega)
  have hB := ev.rangeN 27 (by norm_num) (by norm_num)
  have ha : |h.bias fl dm i k + Lane4.RSeq.pdot fl (x i) (armat fl h.A (x k) dA 0) 0|
      ≤ 27 * ((w.length + 1 : ℕ) : ℝ) :=
    le_trans (abs_add_le _ _) (by linarith)
  have hb : |h.bias fl dm i j + Lane4.RSeq.pdot fl (x i) (armat fl h.A (x j) dA 0) 0|
      ≤ 27 * ((w.length + 1 : ℕ) : ℝ) :=
    le_trans (abs_add_le _ _) (by linarith)
  have hgap := ev.hr.gap ev.hu0 ha hb hB
  have hu27 := u_mul ev 27 (by norm_num)
  have hη' := eta_tiny ev.hη1
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have hjk : (k : ℝ) + 1 ≤ (j : ℝ) := by
    have h : k + 1 ≤ j := hkj
    exact_mod_cast h
  unfold AHead.score
  linarith

/-! ### generic: softmax with a winner -/

theorem att_win (ev : Ctx u η M fl ex p w) {c : List ℕ} {s v q : ℕ → ℝ} {j : ℕ} {ve Bq : ℝ}
    (hnd : c.Nodup) (hlen : c.length ≤ w.length + 1) (hj : j ∈ c)
    (hgap : ∀ k ∈ c, k ≠ j → s k ≤ s j - 16 * (ndist j k : ℝ))
    (hS : ∀ k ∈ c, |s k| ≤ 28 * ((w.length + 1 : ℕ) : ℝ))
    (hv : ∀ k ∈ c, |v k - q k| ≤ ve) (hq : ∀ k ∈ c, |q k| ≤ Bq) (hve0 : 0 ≤ ve)
    (hve : ve ≤ 1 / 10) (hBq0 : 0 ≤ Bq) (hBq : Bq ≤ 1) :
    |savg fl ex c s v - q j| ≤ ve + (Bq + ve) / 100 + 1 / 2 ^ 90 := by
  have hSM : 2 * (28 * ((w.length + 1 : ℕ) : ℝ)) ≤ M := by
    have := ev.rangeN 56 (by norm_num) (by norm_num)
    linarith
  have hf : ∀ k ∈ c, |v k| ≤ Bq + ve := by
    intro k hk
    obtain ⟨a1, a2⟩ := abs_le.mp (hv k hk)
    obtain ⟨b1, b2⟩ := abs_le.mp (hq k hk)
    rw [abs_le]; constructor <;> linarith
  have hBM : 4 * (Bq + ve) + 4 ≤ M := by
    have := ev.range 13 (by norm_num)
    linarith
  obtain ⟨hs1, -⟩ := soft_near (s := s) (f := v) ev.hr ev.he ev.hu0 ev.hu1 ev.hη0 ev.hη1 hnd hlen
    ev.hn ev.hnη hj hgap hS hSM hf hBM
  have h3 := abs_sub_le (savg fl ex c s v) (v j) (q j)
  have h4 := hv j hj
  linarith

theorem exists_max (c : List ℕ) (hne : c ≠ []) : ∃ j ∈ c, ∀ k ∈ c, k ≤ j := by
  have hne' : c.toFinset.Nonempty := by
    rcases List.exists_mem_of_ne_nil _ hne with ⟨a, ha⟩
    exact ⟨a, List.mem_toFinset.mpr ha⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image c.toFinset (fun k => k) hne'
  exact ⟨j, List.mem_toFinset.mp hj, fun k hk => hmax k (List.mem_toFinset.mpr hk)⟩

/-! ### block 1: head 1 -/

noncomputable def cs1 (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : List ℕ :=
  head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

noncomputable def sc1 (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : ℕ → ℝ :=
  fun j => head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i j

noncomputable def att1 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (r : List ℚ) (kr : ℕ) :
    ℝ :=
  savg fl ex (cs1 fl p w i) (sc1 fl p w i)
    (fun j => ardot fl r (net.init fl p w j) (p.V 0 0 kr) 0 0)

theorem sg1 (ev : Ctx u η M fl ex p w) :
    SG w.length head1 (net.init fl p w) (xh0 w) (1 / 500) :=
  ⟨by norm_num [head1], rfl, fun j _ => (init_close ev j).1, fun j _ => (init_close ev j).2,
    by norm_num, by norm_num⟩

theorem gate1 (ev : Ctx u η M fl ex p w) (j : ℕ) :
    (mkN (tokAt w j) = 1 → head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) = 0) ∧
    (mkN (tokAt w j) = 0 → 0 < head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j)) := by
  obtain ⟨q1, -⟩ := dotW ev head1.g rfl (by simp [head1]) (init_closeL ev j)
    (init_close ev j).1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (p.g 0 0) (ev.hp.g 0 0)
  have hwE : wErr (1 / 1000) head1.g [1 / 500, 1 / 500, 1 / 500, 1 / 500, 1 / 500, 1 / 500]
      [1, 1, 1, 1, 1, 1] ≤ 1 / 100 := by
    have hg : head1.g = [-1, 0, 0, 0, 0, 0] := rfl
    rw [hg, wErr6]
    norm_num
  have hdq : dotQ head1.g (xh0 w j) = -mkR w j := by simp [dotQ, head1, xh0]
  rw [hdq] at q1
  have hb := asw_q ev head1.gb (by norm_num [head1]) (ev.hp.gb 0 0)
  have hgb : ((head1.gb : ℚ) : ℝ) = 1 / 2 := by norm_num [head1]
  rw [hgb] at hb
  have hpre : |ardot fl head1.g (net.init fl p w j) (p.g 0 0) 0 0 + asw fl head1.gb (p.gb 0 0)
      - (-mkR w j + 1 / 2)| ≤ 1 / 20 := by
    obtain ⟨a1, a2⟩ := abs_le.mp q1
    obtain ⟨b1, b2⟩ := abs_le.mp hb
    rw [abs_le]; constructor <;> linarith
  have ht : |-mkR w j + 1 / 2| ≤ 3 := by
    obtain ⟨c1, c2⟩ := abs_le.mp (mkR_abs w j)
    rw [abs_le]; constructor <;> linarith
  obtain ⟨g1, g2⟩ := gate_gen ev head1 (p.g 0 0) (p.gb 0 0) (net.init fl p w j) ht hpre
  constructor
  · intro h1
    have hm : mkR w j = 1 := by unfold mkR; rw [h1]; norm_num
    exact g1 (by linarith)
  · intro h0
    have hm : mkR w j = 0 := by unfold mkR; rw [h0]; norm_num
    exact g2 (by linarith)

theorem mem_cs1 (ev : Ctx u η M fl ex p w) (i j : ℕ) :
    j ∈ cs1 fl p w i ↔ j < i ∧ mkN (tokAt w j) = 1 := by
  unfold cs1
  rw [AHead.mem_cands]
  have hm : head1.mask = Mask.strict := rfl
  rw [hm, Lane4.Seq.mem_cand_strict]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra hne
    have h0 : mkN (tokAt w j) = 0 := by
      have := mkN_le (tokAt w j)
      omega
    have := (gate1 ev j).2 h0
    rw [h2] at this
    exact lt_irrefl _ this
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (gate1 ev j).1 h2⟩

theorem mkN_one (t : ℕ) : mkN t = 1 ↔ code t ≠ 0 := by
  unfold mkN
  split_ifs with h <;> simp [h]

theorem exists_marked_iff (w : List ℕ) (i : ℕ) :
    (∃ j, j < i ∧ mkN (tokAt w j) = 1) ↔ fval w (i - 1) ≠ 0 := by
  rcases i with _ | i
  · simp [fval]
  · show (∃ j, j < i + 1 ∧ mkN (tokAt w j) = 1) ↔ fval w i ≠ 0
    rw [fval_ne]
    constructor
    · rintro ⟨j, hj, hm⟩
      exact ⟨j, by omega, (mkN_one _).mp hm⟩
    · rintro ⟨j, hj, hm⟩
      exact ⟨j, by omega, (mkN_one _).mpr hm⟩

theorem h1_att (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (r : List ℚ)
    (hr : r.length = 6) (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (ab : ℝ) (hab : absSum r = ab)
    (hab0 : 0 ≤ ab) (hab1 : ab ≤ 1) (q : ℕ → ℝ) (hq : ∀ j, dotQ r (xh0 w j) = q j) (Bq : ℝ)
    (hqB : ∀ j, |q j| ≤ Bq) (hB0 : 0 ≤ Bq) (hB1 : Bq ≤ 1) (kr : ℕ) :
    ((¬ ∃ j, j < i ∧ mkN (tokAt w j) = 1) → att1 fl ex p w i r kr = 0) ∧
    ((∃ j, j < i ∧ mkN (tokAt w j) = 1) → ∃ js, js < i ∧ mkN (tokAt w js) = 1 ∧
      |att1 fl ex p w i r kr - q js| ≤ (ab / 500 + 6 / 1000 * (1 + 1 / 500) + 1 / 1000)
        + (Bq + (ab / 500 + 6 / 1000 * (1 + 1 / 500) + 1 / 1000)) / 100 + 1 / 2 ^ 90) := by
  have hve : ∀ j, j ≤ w.length →
      |ardot fl r (net.init fl p w j) (p.V 0 0 kr) 0 0 - q j|
        ≤ ab / 500 + 6 / 1000 * (1 + 1 / 500) + 1 / 1000 := by
    intro j _
    obtain ⟨t1, -⟩ := dotU ev r hr hW (init_close ev j).2 (init_close ev j).1 (by norm_num)
      (by norm_num) (p.V 0 0 kr) (ev.hp.V 0 0 kr)
    rw [hab, hq j] at t1
    linarith
  constructor
  · intro hne
    unfold att1
    apply soft_zeros ev.hr
    intro k hk
    exfalso
    exact hne ⟨k, ((mem_cs1 ev i k).mp hk).1, ((mem_cs1 ev i k).mp hk).2⟩
  · rintro ⟨j0, hj0, hm0⟩
    have hmem : j0 ∈ cs1 fl p w i := (mem_cs1 ev i j0).mpr ⟨hj0, hm0⟩
    obtain ⟨js, hjs, hmax⟩ := exists_max _ (List.ne_nil_of_mem hmem)
    have hjs' := (mem_cs1 ev i js).mp hjs
    refine ⟨js, hjs'.1, hjs'.2, ?_⟩
    have hlen : (cs1 fl p w i).length ≤ w.length + 1 := by
      have h1 : (cs1 fl p w i).length ≤ (cand Mask.strict (w.length + 1) i).length :=
        List.length_filter_le _ _
      have h2 : (cand Mask.strict (w.length + 1) i).length = i := by simp [cand]
      omega
    unfold att1
    refine att_win ev (c := cs1 fl p w i) (j := js)
      (ve := ab / 500 + 6 / 1000 * (1 + 1 / 500) + 1 / 1000) (Bq := Bq) (q := q)
      (AHead.cands_nodup head1 fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i)
      hlen hjs ?_ ?_ ?_ ?_ ?_ ?_ hB0 hB1
    · intro k hk hne
      have hkjs := hmax k hk
      have hlt : k < js := lt_of_le_of_ne hkjs hne
      have hg := score_gap ev (sg1 ev) (p.A 0 0) (ev.hp.A 0 0) (p.m 0 0) (ev.hp.m 0 0) i js k hi
        (by omega) hlt
      show sc1 fl p w i k ≤ sc1 fl p w i js - 16 * (ndist js k : ℝ)
      have hkR : (k : ℝ) ≤ (js : ℝ) := by exact_mod_cast hkjs
      rw [ndist_cast, abs_of_nonneg (by linarith)]
      exact hg
    · intro k hk
      have hk' := ((mem_cs1 ev i k).mp hk).1
      exact score_abs ev (sg1 ev) (p.A 0 0) (ev.hp.A 0 0) (p.m 0 0) (ev.hp.m 0 0) i k hi
        (by omega)
    · intro k hk
      exact hve k (by have := ((mem_cs1 ev i k).mp hk).1; omega)
    · intro k _
      exact hqB k
    · linarith
    · linarith

theorem att1_zero (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (kr : ℕ) :
    |att1 fl ex p w i z6 kr| ≤ 1 / 125 := by
  obtain ⟨e1, e2⟩ := h1_att ev i hi z6 rfl (by simp [z6]) 0 (by simp [absSum, z6]) le_rfl
    (by norm_num) (fun _ => 0) (fun j => dotQ_z (xh0 w j) 6) 0 (fun _ => by simp) le_rfl
    (by norm_num) kr
  by_cases hne : ∃ j, j < i ∧ mkN (tokAt w j) = 1
  · obtain ⟨js, -, -, hh⟩ := e2 hne
    have hh' : |att1 fl ex p w i z6 kr - 0| ≤ _ := hh
    rw [sub_zero] at hh'
    have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 1000000 := by norm_num
    linarith
  · rw [e1 hne]
    norm_num

theorem att1_row3 (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    |att1 fl ex p w i [1, 0, 0, 0, 0, 0] 3 - fR w i| ≤ 1 / 50 := by
  obtain ⟨e1, e2⟩ := h1_att ev i hi [1, 0, 0, 0, 0, 0] rfl (by simp) 1 (by simp [absSum])
    (by norm_num) le_rfl (fun j => mkR w j)
    (fun j => by simp [dotQ, xh0]) 1 (fun j => mkR_abs w j) (by norm_num) le_rfl 3
  by_cases hne : ∃ j, j < i ∧ mkN (tokAt w j) = 1
  · obtain ⟨js, -, hm, hh⟩ := e2 hne
    have hh' : |att1 fl ex p w i [1, 0, 0, 0, 0, 0] 3 - mkR w js| ≤ _ := hh
    have hmR : mkR w js = 1 := by unfold mkR; rw [hm]; norm_num
    have hf : fR w i = 1 := by
      unfold fR
      rw [if_neg ((exists_marked_iff w i).mp hne)]
    rw [hmR] at hh'
    rw [hf]
    have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 1000000 := by norm_num
    linarith
  · rw [e1 hne]
    have hf : fR w i = 0 := by
      unfold fR
      have : fval w (i - 1) = 0 := by
        by_contra h
        exact hne ((exists_marked_iff w i).mpr h)
      rw [if_pos this]
    rw [hf]
    norm_num

/-! ### block 1: the state after the block -/

noncomputable def x1 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) : ℕ → Vec :=
  blk1.apply fl ex p 0 (w.length + 1) (net.init fl p w)

theorem blk1_vals (i : ℕ) :
    x1 fl ex p w i = Lane4.RSeq.radd fl (Lane4.RSeq.radd fl (net.init fl p w i)
      [att1 fl ex p w i z6 0, att1 fl ex p w i z6 1, att1 fl ex p w i z6 2,
       att1 fl ex p w i [1, 0, 0, 0, 0, 0] 3, att1 fl ex p w i z6 4, att1 fl ex p w i z6 5])
      [fl (0 + asw fl 0 (p.b2 0 0)), fl (0 + asw fl 0 (p.b2 0 1)),
       fl (0 + asw fl 0 (p.b2 0 2)), fl (0 + asw fl 0 (p.b2 0 3)),
       fl (0 + asw fl 0 (p.b2 0 4)), fl (0 + asw fl 0 (p.b2 0 5))] := rfl

theorem step2 (ev : Ctx u η M fl ex p w) {x s m t s' ex' es em : ℝ} (hx : |x - t| ≤ ex')
    (hs : |s - s'| ≤ es) (hm : |m| ≤ em) (ht : |t| ≤ 1) (hs' : |s'| ≤ 1) (h1 : ex' ≤ 1 / 5)
    (h2 : es ≤ 1 / 5) (h3 : em ≤ 1 / 5) :
    |fl (fl (x + s) + m) - (t + s')| ≤ ex' + es + em + 2 / 50000 := by
  have a := radd1 ev hx hs (by linarith) (by linarith) (by linarith) (by linarith)
  have hm' : |m - 0| ≤ em := by rwa [sub_zero]
  have b := radd1 ev (x := fl (x + s)) (s := m) (t := t + s') (s' := 0) a hm'
    (by have := abs_add_le t s'; linarith) (by simp) (by linarith) (by linarith)
  rw [add_zero] at b
  linarith

theorem ent_zero (ev : Ctx u η M fl ex p w) {a t s d : ℝ} (hd : |d| ≤ 1 / 1000)
    (ha : |a - t| ≤ 1 / 500) (ht : |t| ≤ 1) (hs : |s| ≤ 1 / 125) :
    |fl (fl (a + s) + fl (0 + asw fl 0 d)) - t| ≤ 1 / 80 := by
  have h := step2 ev ha (by rwa [sub_zero] : |s - 0| ≤ 1 / 125) (mlp_small ev hd) ht (by simp)
    (by norm_num) (by norm_num) (by norm_num)
  rw [add_zero] at h
  exact le_trans h (by norm_num)

theorem x1_ent (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    ∃ b0 b1 b2 b3 b4 b5 : ℝ, x1 fl ex p w i = [b0, b1, b2, b3, b4, b5] ∧
      |b0 - mkR w i| ≤ 1 / 80 ∧ |b1 - cR w i| ≤ 1 / 80 ∧ |b2 - aR w i| ≤ 1 / 80 ∧
      |b3 - fR w i| ≤ 1 / 40 ∧ |b4 - 0| ≤ 1 / 80 ∧ |b5 - 0| ≤ 1 / 80 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, hx, h0, h1, h2, h3, h4, h5⟩ := init_ent ev i
  refine ⟨fl (fl (a0 + att1 fl ex p w i z6 0) + fl (0 + asw fl 0 (p.b2 0 0))),
    fl (fl (a1 + att1 fl ex p w i z6 1) + fl (0 + asw fl 0 (p.b2 0 1))),
    fl (fl (a2 + att1 fl ex p w i z6 2) + fl (0 + asw fl 0 (p.b2 0 2))),
    fl (fl (a3 + att1 fl ex p w i [1, 0, 0, 0, 0, 0] 3) + fl (0 + asw fl 0 (p.b2 0 3))),
    fl (fl (a4 + att1 fl ex p w i z6 4) + fl (0 + asw fl 0 (p.b2 0 4))),
    fl (fl (a5 + att1 fl ex p w i z6 5) + fl (0 + asw fl 0 (p.b2 0 5))), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [blk1_vals, hx]; rfl
  · exact ent_zero ev (ev.hp.b2 0 0) h0 (mkR_abs w i) (att1_zero ev i hi 0)
  · exact ent_zero ev (ev.hp.b2 0 1) h1 (cR_abs w i) (att1_zero ev i hi 1)
  · exact ent_zero ev (ev.hp.b2 0 2) h2 (aR_abs w i) (att1_zero ev i hi 2)
  · have h := step2 ev h3 (att1_row3 ev i hi) (mlp_small ev (ev.hp.b2 0 3)) (by simp)
      (fR_abs w i) (by norm_num) (by norm_num) (by norm_num)
    rw [zero_add] at h
    exact le_trans h (by norm_num)
  · exact ent_zero ev (ev.hp.b2 0 4) h4 (by simp) (att1_zero ev i hi 4)
  · exact ent_zero ev (ev.hp.b2 0 5) h5 (by simp) (att1_zero ev i hi 5)

theorem x1_closeL (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    CloseL (x1 fl ex p w i) (xh1 w i)
      [1 / 80, 1 / 80, 1 / 80, 1 / 40, 1 / 80, 1 / 80] [1, 1, 1, 1, 1, 1] := by
  obtain ⟨b0, b1, b2, b3, b4, b5, hx, h0, h1, h2, h3, h4, h5⟩ := x1_ent ev i hi
  rw [hx]
  unfold xh1
  exact closeL6 h0 h1 h2 h3 h4 h5 (mkR_abs w i) (cR_abs w i) (aR_abs w i) (fR_abs w i) (by simp)
    (by simp)

theorem x1_close (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    (x1 fl ex p w i).length = 6 ∧ Close (x1 fl ex p w i) (xh1 w i) (1 / 40) 1 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, hx, h0, h1, h2, h3, h4, h5⟩ := x1_ent ev i hi
  rw [hx]
  unfold xh1
  refine ⟨by simp, close6 (le_trans h0 (by norm_num)) (le_trans h1 (by norm_num))
    (le_trans h2 (by norm_num)) h3 (le_trans h4 (by norm_num)) (le_trans h5 (by norm_num))
    (mkR_abs w i) (cR_abs w i) (aR_abs w i) (fR_abs w i) (by simp) (by simp)⟩
end Lane4.Case
