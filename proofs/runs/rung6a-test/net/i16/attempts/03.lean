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
    (hB : |x| ≤ B) (hB0 : B ≤ 100) : |fl x - t| ≤ e + 1 / 50000 := by
  have hBM : B ≤ M := ev.range B (by linarith [(by norm_num : (100:ℝ) ≤ 2 ^ 40)])
  have h := ev.hr.near ev.hu0 hx hB hBM
  have h1 : u * B ≤ 1 / 10 ^ 7 * 100 := by
    have := ev.u7
    have hB1 : 0 ≤ B := le_trans (abs_nonneg _) hB
    nlinarith
  have := ev.eta30
  have : (1:ℝ) / 10 ^ 7 * 100 + 1 / 10 ^ 30 ≤ 1 / 50000 := by norm_num
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


/-! ### Generic head lemmas -/

theorem u_mul (ev : Ctx u η M fl ex p w) (c : ℝ) (hc : 0 ≤ c) :
    u * (c * ((w.length + 1 : ℕ) : ℝ)) ≤ c / 256 := by
  have h : u * (c * ((w.length + 1 : ℕ) : ℝ)) = c * (u * ((w.length + 1 : ℕ) : ℝ)) := by ring
  rw [h]
  have := mul_le_mul_of_nonneg_left ev.hn hc
  linarith

theorem dotR_zero7 (x : List ℝ) : dotR x [0, 0, 0, 0, 0, 0, 0] = 0 := by
  unfold dotR
  rcases x with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, x⟩⟩⟩⟩⟩⟩⟩ <;> simp

theorem dotQ_z7 (x : List ℝ) : dotQ z7 x = 0 := by
  unfold dotQ z7
  rcases x with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, x⟩⟩⟩⟩⟩⟩⟩ <;> simp

theorem closeU7 {a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 e X : ℝ}
    (h0 : |a0 - b0| ≤ e ∧ |b0| ≤ X) (h1 : |a1 - b1| ≤ e ∧ |b1| ≤ X)
    (h2 : |a2 - b2| ≤ e ∧ |b2| ≤ X) (h3 : |a3 - b3| ≤ e ∧ |b3| ≤ X)
    (h4 : |a4 - b4| ≤ e ∧ |b4| ≤ X) (h5 : |a5 - b5| ≤ e ∧ |b5| ≤ X)
    (h6 : |a6 - b6| ≤ e ∧ |b6| ≤ X) :
    Close [a0, a1, a2, a3, a4, a5, a6] [b0, b1, b2, b3, b4, b5, b6] e X := by
  refine ⟨rfl, ?_⟩
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

/-- The content part of a score is small when the states are bounded by 6. -/
theorem content_small (ev : Ctx u η M fl ex p w) (xi xk : List ℝ) (hi : xi.length = 7)
    (hk : xk.length = 7) (bi : ∀ c, |xi.getD c 0| ≤ 6) (bk : ∀ c, |xk.getD c 0| ≤ 6)
    (dA : ℕ → ℕ → ℝ) (hdA : ∀ r c, |dA r c| ≤ 1 / 1000) :
    |Lane4.RSeq.pdot fl xi (armat fl A7 xk dA 0) 0| ≤ 2 := by
  have hCk : Close xk xk 0 6 := ⟨rfl, fun k _ => ⟨by simp, bk k⟩⟩
  have hab : absSum z7 = 0 := by simp [absSum, z7]
  have hl : (z7.length : ℝ) = 7 := by simp [z7]
  have hrow : ∀ r : ℕ, |ardot fl z7 xk (dA r) 0 0 - 0| ≤ 9 / 200 := by
    intro r
    have h := ardot_near_abs u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1
      (by norm_num) (by norm_num) z7 xk xk (dA r) 0 6 0 (by rw [hk]; rfl) (by simp [z7]) hCk
      (hdA r) (by simp [z7]) (le_refl _) (by norm_num) (le_refl _) (by norm_num)
      (ev.range _ (by norm_num))
    rw [hab, hl, dotQ_z7] at h
    refine le_trans h ?_
    norm_num
  have hy : armat fl A7 xk dA 0 =
      [ardot fl z7 xk (dA 0) 0 0, ardot fl z7 xk (dA 1) 0 0, ardot fl z7 xk (dA 2) 0 0,
       ardot fl z7 xk (dA 3) 0 0, ardot fl z7 xk (dA 4) 0 0, ardot fl z7 xk (dA 5) 0 0,
       ardot fl z7 xk (dA 6) 0 0] := rfl
  rw [hy]
  have hC1 : Close xi xi 0 6 := ⟨rfl, fun k _ => ⟨by simp, bi k⟩⟩
  have hC2 := closeU7 (a0 := ardot fl z7 xk (dA 0) 0 0) (a1 := ardot fl z7 xk (dA 1) 0 0)
    (a2 := ardot fl z7 xk (dA 2) 0 0) (a3 := ardot fl z7 xk (dA 3) 0 0)
    (a4 := ardot fl z7 xk (dA 4) 0 0) (a5 := ardot fl z7 xk (dA 5) 0 0)
    (a6 := ardot fl z7 xk (dA 6) 0 0) (b0 := 0) (b1 := 0) (b2 := 0) (b3 := 0) (b4 := 0)
    (b5 := 0) (b6 := 0) (e := 9 / 200) (X := 0)
    ⟨hrow 0, by simp⟩ ⟨hrow 1, by simp⟩ ⟨hrow 2, by simp⟩ ⟨hrow 3, by simp⟩
    ⟨hrow 4, by simp⟩ ⟨hrow 5, by simp⟩ ⟨hrow 6, by simp⟩
  have key := pdot_near u η M fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 xi xi _ _ 6 0 0 (9 / 200)
    (by rw [hi]; rfl) (by rw [hi]; norm_num) hC1 hC2 (by norm_num) (le_refl _) (le_refl _)
    (by norm_num) (by norm_num) (ev.range _ (by norm_num))
  obtain ⟨k1, -⟩ := key
  rw [hi, dotR_zero7, sub_zero] at k1
  refine le_trans k1 ?_
  norm_num

theorem bias_abs (ev : Ctx u η M fl ex p w) (h : AHead) (hm : (h.m : ℝ) = 32) (dm : ℝ)
    (hdm : |dm| ≤ 1 / 1000) (i t : ℕ) (hi : i ≤ w.length + 1) (ht : t ≤ w.length + 1) :
    |h.bias fl dm i t| ≤ 34 * ((w.length + 1 : ℕ) : ℝ) := by
  have habs : |((h.m : ℚ) : ℝ)| = 32 := by rw [hm]; exact abs_of_nonneg (by norm_num)
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hS := asw_bound ev.hr ev.hu0 h.m hdm (by rw [habs]; linarith [ev.range 40 (by norm_num)])
  rw [habs] at hS
  have hu : u * (32 + 1 / 1000) ≤ 1 / 2 ^ 24 * 33 :=
    mul_le_mul ev.hu1 (by norm_num) (by norm_num) (by positivity)
  have hη' := eta_tiny ev.hη1
  have hS2 : |asw fl h.m dm| ≤ 33 := by
    have : (1 : ℝ) / 2 ^ 24 * 33 + 1 / 10 ^ 40 ≤ 1 / 2 := by norm_num
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
  have hab : |S * ((t : ℝ) - (i : ℝ))| ≤ 33 * ((w.length + 1 : ℕ) : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul hS2 hti (abs_nonneg _) (by norm_num)
  have hB := ev.rangeN 33 (by norm_num) (by norm_num)
  have h1 := ev.hr.bound ev.hu0 hab hB
  have hu33 := u_mul ev 33 (by norm_num)
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

theorem score_bnd (ev : Ctx u η M fl ex p w) (h : AHead) (hA : h.A = A7) (hm : (h.m : ℝ) = 32)
    (x : ℕ → Vec) (hx : ∀ j, j ≤ w.length → (x j).length = 7 ∧ ∀ c, |(x j).getD c 0| ≤ 6)
    (dA : ℕ → ℕ → ℝ) (dm : ℝ) (hdA : ∀ r c, |dA r c| ≤ 1 / 1000) (hdm : |dm| ≤ 1 / 1000)
    (i k : ℕ) (hi : i ≤ w.length) (hk : k ≤ w.length) :
    |h.bias fl dm i k + Lane4.RSeq.pdot fl (x i) (armat fl h.A (x k) dA 0) 0|
      ≤ 36 * ((w.length + 1 : ℕ) : ℝ) := by
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hb := bias_abs ev h hm dm hdm i k (by omega) (by omega)
  have hc := content_small ev (x i) (x k) (hx i hi).1 (hx k hk).1 (hx i hi).2 (hx k hk).2 dA hdA
  rw [← hA] at hc
  exact le_trans (abs_add_le _ _) (by linarith)

theorem score_abs (ev : Ctx u η M fl ex p w) (h : AHead) (hA : h.A = A7) (hm : (h.m : ℝ) = 32)
    (x : ℕ → Vec) (hx : ∀ j, j ≤ w.length → (x j).length = 7 ∧ ∀ c, |(x j).getD c 0| ≤ 6)
    (dA : ℕ → ℕ → ℝ) (dm : ℝ) (hdA : ∀ r c, |dA r c| ≤ 1 / 1000) (hdm : |dm| ≤ 1 / 1000)
    (i k : ℕ) (hi : i ≤ w.length) (hk : k ≤ w.length) :
    |h.score fl dA dm x i k| ≤ 37 * ((w.length + 1 : ℕ) : ℝ) := by
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have ha := score_bnd ev h hA hm x hx dA dm hdA hdm i k hi hk
  have hB := ev.rangeN 36 (by norm_num) (by norm_num)
  have h1 := ev.hr.bound ev.hu0 ha hB
  have hu := u_mul ev 36 (by norm_num)
  have hη' := eta_tiny ev.hη1
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  unfold AHead.score
  linarith

theorem score_gap (ev : Ctx u η M fl ex p w) (h : AHead) (hA : h.A = A7) (hm : (h.m : ℝ) = 32)
    (x : ℕ → Vec) (hx : ∀ j, j ≤ w.length → (x j).length = 7 ∧ ∀ c, |(x j).getD c 0| ≤ 6)
    (dA : ℕ → ℕ → ℝ) (dm : ℝ) (hdA : ∀ r c, |dA r c| ≤ 1 / 1000) (hdm : |dm| ≤ 1 / 1000)
    (i j k : ℕ) (hi : i ≤ w.length) (hj : j ≤ w.length) (hkj : k < j) :
    h.score fl dA dm x i k ≤ h.score fl dA dm x i j - 16 * ((j : ℝ) - (k : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hM12 : (2 : ℝ) ^ 12 * (((w.length + 1 : ℕ) : ℝ) + 1) ≤ M := by
    have := ev.rangeN 8192 (by norm_num) (by norm_num)
    have h12 : (2 : ℝ) ^ 12 = 4096 := by norm_num
    rw [h12]; linarith
  obtain ⟨hg1, -⟩ := bias_gap u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1
    (by norm_num) (by norm_num) h dm hdm (by rw [hm]; norm_num) (by rw [hm]; norm_num)
    (w.length + 1) i j k hkj (by omega) (by omega) ev.hn ev.hnη hM12
  rw [hm] at hg1
  have hcj := content_small ev (x i) (x j) (hx i hi).1 (hx j hj).1 (hx i hi).2 (hx j hj).2 dA hdA
  have hck := content_small ev (x i) (x k) (hx i hi).1 (hx k (by omega)).1 (hx i hi).2
    (hx k (by omega)).2 dA hdA
  rw [← hA] at hcj hck
  obtain ⟨hcj1, hcj2⟩ := abs_le.mp hcj
  obtain ⟨hck1, hck2⟩ := abs_le.mp hck
  have ha := score_bnd ev h hA hm x hx dA dm hdA hdm i k hi (by omega)
  have hb := score_bnd ev h hA hm x hx dA dm hdA hdm i j hi hj
  have hB := ev.rangeN 36 (by norm_num) (by norm_num)
  have hgap := ev.hr.gap ev.hu0 ha hb hB
  have hu36 := u_mul ev 36 (by norm_num)
  have hη' := eta_tiny ev.hη1
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have hjk : (k : ℝ) + 1 ≤ (j : ℝ) := by
    have h' : k + 1 ≤ j := hkj
    exact_mod_cast h'
  unfold AHead.score
  linarith

/-- A gate with non-positive pre-activation is exactly 0. -/
theorem gate_zero_of (ev : Ctx u η M fl ex p w) (h : AHead) (dg : ℕ → ℝ) (dgb : ℝ) (xj : Vec)
    (hneg : ardot fl h.g xj dg 0 0 + asw fl h.gb dgb ≤ 0)
    (hb : |ardot fl h.g xj dg 0 0 + asw fl h.gb dgb| ≤ 100) :
    h.gate fl dg dgb xj = 0 := by
  unfold AHead.gate
  have := ev.range 100 (by norm_num)
  have h2 := (abs_le.mp hb).1
  exact relu_fl_zero ev.hr hneg (by linarith)

/-- A gate with clearly positive pre-activation is not 0. -/
theorem gate_ne_zero_of (ev : Ctx u η M fl ex p w) (h : AHead) (dg : ℕ → ℝ) (dgb : ℝ) (xj : Vec)
    (hpos : 2 / 5 ≤ ardot fl h.g xj dg 0 0 + asw fl h.gb dgb)
    (hb : |ardot fl h.g xj dg 0 0 + asw fl h.gb dgb| ≤ 100) :
    h.gate fl dg dgb xj ≠ 0 := by
  unfold AHead.gate
  have hM := ev.range 100 (by norm_num)
  have h1 := ev.hr.lower ev.hu0 hb hM
  have h2 := ev.u7
  have h3 := ev.eta30
  have h4 : u * 100 ≤ 1 / 10 ^ 7 * 100 := by nlinarith
  have h5 : (1:ℝ) / 10 ^ 7 * 100 + 1 / 10 ^ 30 ≤ 1 / 10 := by norm_num
  intro h0
  unfold Lane4.relu at h0
  have : fl (ardot fl h.g xj dg 0 0 + asw fl h.gb dgb) ≤ 0 := by
    rcases max_eq_iff.mp h0 with ⟨h6, _⟩ | ⟨h6, h7⟩
    · linarith
    · linarith
  linarith

end Steps

end Lane4.Case
