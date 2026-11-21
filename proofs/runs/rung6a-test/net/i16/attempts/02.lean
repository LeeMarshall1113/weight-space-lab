namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

/-! ### The network.  State: [E1,E2,E3,P1,P2,P3,Y]. -/

def z7 : List ℚ := [0, 0, 0, 0, 0, 0, 0]
def A7 : List (List ℚ) := [z7, z7, z7, z7, z7, z7, z7]
def cr3 : List ℚ := [1/5, 0, 0, 0, 0, 0, 0]
def cr4 : List ℚ := [0, 1/5, 0, 0, 0, 0, 0]
def cr5 : List ℚ := [0, 0, 1/5, 0, 0, 0, 0]
def vrow : List ℚ := [0, 4/5, 2/5, 0, 0, 0, 0]

def head1 : AHead :=
  { A := A7, V := [z7, z7, z7, cr3, cr4, cr5, z7], mask := Mask.strict, m := 32,
    g := z7, gb := -1 }

def block0 : ABlock :=
  { heads := [head1], W1 := [], b1 := [], W2 := [[], [], [], [], [], [], []], b2 := z7 }

def hd1 : AHead :=
  { A := A7, V := [vrow, z7, z7, z7, z7, z7, z7], mask := Mask.causal, m := 32,
    g := [0, 0, 0, -1, 0, 0, 0], gb := 1/2 }
def hd2 : AHead :=
  { A := A7, V := [z7, vrow, z7, z7, z7, z7, z7], mask := Mask.causal, m := 32,
    g := [0, 0, 0, 0, -1, 0, 0], gb := 1/2 }
def hd3 : AHead :=
  { A := A7, V := [z7, z7, vrow, z7, z7, z7, z7], mask := Mask.causal, m := 32,
    g := [0, 0, 0, 0, 0, -1, 0], gb := 1/2 }

def block1 : ABlock :=
  { heads := [hd1, hd2, hd3],
    W1 := [[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0]],
    b1 := [-9/2, -9/2, -9/2],
    W2 := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [1, 1, 1]],
    b2 := z7 }

def net : ANet :=
  { embed := [z7, [5, 0, 0, 0, 0, 0, 0], [0, 5, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 0]],
    blocks := [block0, block1], outW := [0, 0, 0, 0, 0, 0, 1/2], outB := -1/4 }

theorem shape_chk : ANet.shapeOK net 3 = true := by decide

/-- The embedding row of a token `t ≤ 3`. -/
theorem embed_row {t : ℕ} (ht : t ≤ 3) : net.embed.getD t [] =
    [if t = 1 then 5 else 0, if t = 2 then 5 else 0, if t = 3 then 5 else 0, 0, 0, 0, 0] := by
  interval_cases t <;> first | rfl | simp [net, z7]

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) : tokAt w j ≤ 3 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (j : ℕ) (h : tokAt w j ≤ 3) :
    net.init fl p w j =
      [asw fl (if tokAt w j = 1 then 5 else 0) (p.E (tokAt w j) 0),
       asw fl (if tokAt w j = 2 then 5 else 0) (p.E (tokAt w j) 1),
       asw fl (if tokAt w j = 3 then 5 else 0) (p.E (tokAt w j) 2),
       asw fl 0 (p.E (tokAt w j) 3), asw fl 0 (p.E (tokAt w j) 4),
       asw fl 0 (p.E (tokAt w j) 5), asw fl 0 (p.E (tokAt w j) 6)] := by
  show aswRow fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0 = _
  rw [embed_row h]
  rfl


structure Ctx (u η M : ℝ) (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) : Prop where
  hr : Rnd u η M fl
  he : ExpM u η ex
  hu0 : 0 ≤ u
  hu1 : u ≤ 1 / 2 ^ 24
  hη0 : 0 ≤ η
  hη1 : η ≤ 1 / 2 ^ 149
  hp : p.Within (1 / 1000)
  hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3
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

theorem Ctx.u7 (ev : Ctx u η M fl ex p w) : u ≤ 1 / 10 ^ 7 := by
  have h := ev.hu1
  have : (1 : ℝ) / 2 ^ 24 ≤ 1 / 10 ^ 7 := by norm_num
  linarith

theorem Ctx.eta30 (ev : Ctx u η M fl ex p w) : η ≤ 1 / 10 ^ 30 := by
  have h := eta_tiny ev.hη1
  have : (1 : ℝ) / 10 ^ 40 ≤ 1 / 10 ^ 30 := by norm_num
  linarith

/-- rounding a value of size at most `B ≤ 100`: error at most `B/10^6`-ish. -/
theorem Ctx.rnd_near (ev : Ctx u η M fl ex p w) {x t e B : ℝ} (hx : |x - t| ≤ e)
    (hB : |x| ≤ B) (hB0 : B ≤ 100) : |fl x - t| ≤ e + 1 / 10 ^ 4 := by
  have hBM : B ≤ M := ev.range B (by linarith [(by norm_num : (100:ℝ) ≤ 2 ^ 40)])
  have h := ev.hr.near ev.hu0 hx hB hBM
  have h1 : u * B ≤ 1 / 10 ^ 7 * 100 := by
    have := ev.u7
    have hB1 : 0 ≤ B := le_trans (abs_nonneg _) hB
    nlinarith
  have := ev.eta30
  have : (1:ℝ) / 10 ^ 7 * 100 + 1 / 10 ^ 30 ≤ 1 / 10 ^ 4 := by norm_num
  linarith

theorem asw5 (ev : Ctx u η M fl ex p w) (a : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 1000)
    (ha : |(a : ℝ)| ≤ 5) : |asw fl a d - (a : ℝ)| ≤ 51 / 50000 := by
  have h := asw_near ev.hr ev.hu0 a hd (by linarith [ev.range 6 (by norm_num)])
  have h1 : u * (|(a : ℝ)| + 1 / 1000) ≤ 1 / 2 ^ 24 * 6 :=
    mul_le_mul ev.hu1 (by linarith) (by positivity) (by positivity)
  have h2 := eta_tiny ev.hη1
  have h3 : (1 : ℝ) / 2 ^ 24 * 6 + 1 / 10 ^ 40 ≤ 1 / 50000 := by norm_num
  linarith

theorem closeL7 {a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 e0 e1 e2 e3 e4 e5 e6
    X0 X1 X2 X3 X4 X5 X6 : ℝ}
    (h0 : |a0 - b0| ≤ e0 ∧ |b0| ≤ X0) (h1 : |a1 - b1| ≤ e1 ∧ |b1| ≤ X1)
    (h2 : |a2 - b2| ≤ e2 ∧ |b2| ≤ X2) (h3 : |a3 - b3| ≤ e3 ∧ |b3| ≤ X3)
    (h4 : |a4 - b4| ≤ e4 ∧ |b4| ≤ X4) (h5 : |a5 - b5| ≤ e5 ∧ |b5| ≤ X5)
    (h6 : |a6 - b6| ≤ e6 ∧ |b6| ≤ X6) :
    CloseL [a0, a1, a2, a3, a4, a5, a6] [b0, b1, b2, b3, b4, b5, b6]
      [e0, e1, e2, e3, e4, e5, e6] [X0, X1, X2, X3, X4, X5, X6] := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro k hk
  have hk7 : k < 7 := by simpa using hk
  interval_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

theorem dot7 (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr : r.length = 7) {W : ℝ}
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ W) (hW0 : 0 ≤ W)
    {x xh es Xs : List ℝ} (hC : CloseL x xh es Xs) (hx : x.length = 7) {e X : ℝ}
    (hb : ∀ k, k < x.length → es.getD k 0 ≤ e ∧ Xs.getD k 0 ≤ X) (d : ℕ → ℝ)
    (hd : ∀ k, |d k| ≤ 1 / 1000) (hX0 : 0 ≤ X) (he0 : 0 ≤ e)
    (hT : (W + 1) * (X + e + 1) ≤ 2 ^ 20) :
    |ardot fl r x d 0 0 - dotQ r xh|
      ≤ wErr (1 / 1000) r es Xs + 7 * (W + 1) * (X + e + 1) / 2 ^ 16 + 1 / 2 ^ 100
    ∧ |ardot fl r x d 0 0| ≤ 7 * (W + 1) * (X + e + 1) * 2 := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have key := ardot_near_w u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (by norm_num)
    (by norm_num) r x xh es Xs d W X e (by rw [hr, hx]) (by omega) hC hb hd hW hW0 hX0 he0 hT hM30
  rw [hr] at key
  simpa using key

/-! ### Ideal states -/

noncomputable def xh0 (w : List ℕ) (j : ℕ) : List ℝ :=
  [(((if tokAt w j = 1 then 5 else 0 : ℚ)) : ℝ), (((if tokAt w j = 2 then 5 else 0 : ℚ)) : ℝ),
   (((if tokAt w j = 3 then 5 else 0 : ℚ)) : ℝ), 0, 0, 0, 0]

theorem qb (c : Prop) [Decidable c] : |(((if c then 5 else 0 : ℚ)) : ℝ)| ≤ 5 := by
  split_ifs <;> norm_num

theorem init_close (ev : Ctx u η M fl ex p w) (j : ℕ) :
    CloseL (net.init fl p w j) (xh0 w j)
      [51/50000, 51/50000, 51/50000, 51/50000, 51/50000, 51/50000, 51/50000]
      [5, 5, 5, 0, 0, 0, 0] := by
  rw [init_eq fl p w j (tok_le w ev.hw j)]
  unfold xh0
  have hz : ∀ d : ℝ, |d| ≤ 1 / 1000 → |asw fl 0 d - 0| ≤ 51 / 50000 := by
    intro d hd
    have := asw5 ev (0 : ℚ) hd (by simp)
    simpa using this
  refine closeL7 ⟨asw5 ev _ (ev.hp.E _ 0) (qb _), qb _⟩ ⟨asw5 ev _ (ev.hp.E _ 1) (qb _), qb _⟩
    ⟨asw5 ev _ (ev.hp.E _ 2) (qb _), qb _⟩ ⟨hz _ (ev.hp.E _ 3), by norm_num⟩
    ⟨hz _ (ev.hp.E _ 4), by norm_num⟩ ⟨hz _ (ev.hp.E _ 5), by norm_num⟩
    ⟨hz _ (ev.hp.E _ 6), by norm_num⟩

end Steps

end Lane4.Case
