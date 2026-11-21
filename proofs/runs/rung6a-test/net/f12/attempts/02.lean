namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
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

/-- a stored weight `n` (natural, `n ≤ 2`) -/
theorem asw_nat (ev : Ctx u η M fl ex p w) (n : ℕ) (hn : n ≤ 2) {d : ℝ} (hd : |d| ≤ 1 / 1000) :
    |asw fl (n : ℚ) d - (n : ℝ)| ≤ 1 / 500 := by
  have hc : (((n : ℚ)) : ℝ) = (n : ℝ) := by simp
  have hn' : (n : ℝ) ≤ 2 := by exact_mod_cast hn
  have h := asw_near ev.hr ev.hu0 (n : ℚ) hd
    (by rw [hc, abs_of_nonneg (Nat.cast_nonneg n)]; linarith [ev.range 4 (by norm_num)])
  rw [hc, abs_of_nonneg (Nat.cast_nonneg n)] at h
  rw [hc] at h
  have h1 := ev.u7
  have h2 := ev.η40
  have h3 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000000 := by norm_num
  have h4 : u * ((n : ℝ) + 1 / 1000) ≤ 1 / 1000000 := by
    have : u * ((n : ℝ) + 1 / 1000) ≤ u * 3 := mul_le_mul_of_nonneg_left (by linarith) ev.hu0
    linarith
  have h5 : |asw fl (n : ℚ) d - (n : ℝ)| ≤ 1 / 1000 + (u * ((n : ℝ) + 1 / 1000) + η) := by
    simpa [hc, abs_of_nonneg (Nat.cast_nonneg n)] using h
  linarith

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
end Lane4.Case
