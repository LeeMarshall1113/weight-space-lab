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


/-! ### Rounded additions -/

theorem add1 (ev : Ctx u η M fl ex p w) {a b a' b' e1 e2 X1 X2 : ℝ} (ha : |a - a'| ≤ e1)
    (hb : |b - b'| ≤ e2) (h1 : |a'| ≤ X1) (h2 : |b'| ≤ X2) (hs : X1 + e1 + X2 + e2 ≤ 50) :
    |fl (a + b) - (a' + b')| ≤ e1 + e2 + 1 / 50000 := by
  have he1 : 0 ≤ e1 := le_trans (abs_nonneg _) ha
  have he2 : 0 ≤ e2 := le_trans (abs_nonneg _) hb
  have hab : |a + b - (a' + b')| ≤ e1 + e2 := by
    have : a + b - (a' + b') = (a - a') + (b - b') := by ring
    rw [this]
    exact le_trans (abs_add_le _ _) (by linarith)
  have hA := abs_sub_abs_le_abs_sub a a'
  have hB := abs_sub_abs_le_abs_sub b b'
  have hs2 : |a + b| ≤ 50 := le_trans (abs_add_le _ _) (by linarith)
  exact ev.rnd_near hab hs2 (by norm_num)

theorem add2 (ev : Ctx u η M fl ex p w) {a t m a' t' m' y e1 e2 e3 Xa Xt Xm : ℝ}
    (ha : |a - a'| ≤ e1) (ht : |t - t'| ≤ e2) (hm : |m - m'| ≤ e3) (hXa : |a'| ≤ Xa)
    (hXt : |t'| ≤ Xt) (hXm : |m'| ≤ Xm) (hy : a' + t' + m' = y)
    (hs : Xa + e1 + Xt + e2 + Xm + e3 ≤ 40) :
    |fl (fl (a + t) + m) - y| ≤ e1 + e2 + e3 + 1 / 25000 := by
  have he1 : 0 ≤ e1 := le_trans (abs_nonneg _) ha
  have he2 : 0 ≤ e2 := le_trans (abs_nonneg _) ht
  have he3 : 0 ≤ e3 := le_trans (abs_nonneg _) hm
  have hXa0 : 0 ≤ Xa := le_trans (abs_nonneg _) hXa
  have hXt0 : 0 ≤ Xt := le_trans (abs_nonneg _) hXt
  have hXm0 : 0 ≤ Xm := le_trans (abs_nonneg _) hXm
  have h1 := add1 ev ha ht hXa hXt (by linarith)
  have hs' : |a' + t'| ≤ Xa + Xt := le_trans (abs_add_le _ _) (by linarith)
  have h2 := add1 ev h1 hm hs' hXm (by linarith)
  rw [hy] at h2
  linarith

theorem mlp_small (ev : Ctx u η M fl ex p w) (d : ℝ) (hd : |d| ≤ 1 / 1000) :
    |fl (0 + asw fl 0 d) - 0| ≤ 52 / 50000 := by
  have h1 := asw5 ev (0 : ℚ) hd (by simp)
  have h1' : |asw fl 0 d - 0| ≤ 51 / 50000 := by simpa using h1
  have h2 : |(0 : ℝ) + asw fl 0 d - 0| ≤ 51 / 50000 := by simpa using h1'
  have h3 : |(0 : ℝ) + asw fl 0 d| ≤ 1 := by
    rw [zero_add]; simp at h1'; linarith [(abs_le.mp h1').1, (abs_le.mp h1').2]
  have := ev.rnd_near h2 (le_trans h3 (by norm_num) : |(0 : ℝ) + asw fl 0 d| ≤ 100) (by norm_num)
  linarith

/-! ### Initial state -/

theorem init_len (ev : Ctx u η M fl ex p w) (j : ℕ) : (net.init fl p w j).length = 7 := by
  rw [init_eq fl p w j (tok_le w ev.hw j)]
  rfl

theorem init_ent (ev : Ctx u η M fl ex p w) (j : ℕ) :
    ∃ a0 a1 a2 a3 a4 a5 a6 : ℝ, net.init fl p w j = [a0, a1, a2, a3, a4, a5, a6] ∧
      |a0 - (((if tokAt w j = 1 then 5 else 0 : ℚ)) : ℝ)| ≤ 51 / 50000 ∧
      |a1 - (((if tokAt w j = 2 then 5 else 0 : ℚ)) : ℝ)| ≤ 51 / 50000 ∧
      |a2 - (((if tokAt w j = 3 then 5 else 0 : ℚ)) : ℝ)| ≤ 51 / 50000 ∧
      |a3 - 0| ≤ 51 / 50000 ∧ |a4 - 0| ≤ 51 / 50000 ∧ |a5 - 0| ≤ 51 / 50000 ∧
      |a6 - 0| ≤ 51 / 50000 := by
  have hz : ∀ d : ℝ, |d| ≤ 1 / 1000 → |asw fl 0 d - 0| ≤ 51 / 50000 := by
    intro d hd
    have := asw5 ev (0 : ℚ) hd (by simp)
    simpa using this
  refine ⟨_, _, _, _, _, _, _, init_eq fl p w j (tok_le w ev.hw j), asw5 ev _ (ev.hp.E _ 0) (qb _),
    asw5 ev _ (ev.hp.E _ 1) (qb _), asw5 ev _ (ev.hp.E _ 2) (qb _), hz _ (ev.hp.E _ 3),
    hz _ (ev.hp.E _ 4), hz _ (ev.hp.E _ 5), hz _ (ev.hp.E _ 6)⟩

theorem bd7 {a0 a1 a2 a3 a4 a5 a6 : ℝ} (h0 : |a0| ≤ 6) (h1 : |a1| ≤ 6) (h2 : |a2| ≤ 6)
    (h3 : |a3| ≤ 6) (h4 : |a4| ≤ 6) (h5 : |a5| ≤ 6) (h6 : |a6| ≤ 6) :
    ∀ c, |[a0, a1, a2, a3, a4, a5, a6].getD c 0| ≤ 6 := by
  intro c
  rcases c with _ | _ | _ | _ | _ | _ | _ | c
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · simpa using h3
  · simpa using h4
  · simpa using h5
  · simpa using h6
  · simp

theorem init_bd (ev : Ctx u η M fl ex p w) :
    ∀ j, j ≤ w.length → (net.init fl p w j).length = 7 ∧
      ∀ c, |(net.init fl p w j).getD c 0| ≤ 6 := by
  intro j _
  refine ⟨init_len ev j, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, hx, h0, h1, h2, h3, h4, h5, h6⟩ := init_ent ev j
  rw [hx]
  have q1 := qb (tokAt w j = 1)
  have q2 := qb (tokAt w j = 2)
  have q3 := qb (tokAt w j = 3)
  have t := fun (a b : ℝ) (e : ℝ) (hh : |a - b| ≤ e) (hb : |b| ≤ 5) (he : e ≤ 1) =>
    show |a| ≤ 6 from by
      have := abs_sub_abs_le_abs_sub a b
      linarith
  refine bd7 (t _ _ _ h0 q1 (by norm_num)) (t _ _ _ h1 q2 (by norm_num))
    (t _ _ _ h2 q3 (by norm_num)) ?_ ?_ ?_ ?_
  · have := abs_sub_abs_le_abs_sub a3 0
    simp at this h3 ⊢; linarith
  · have := abs_sub_abs_le_abs_sub a4 0
    simp at this h4 ⊢; linarith
  · have := abs_sub_abs_le_abs_sub a5 0
    simp at this h5 ⊢; linarith
  · have := abs_sub_abs_le_abs_sub a6 0
    simp at this h6 ⊢; linarith

/-! ### Layer 1 head: dot products against the initial state -/

theorem l1_row (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr : r.length = 7)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) {c0 : ℝ}
    (hwe : wErr (1 / 1000) r [51/50000, 51/50000, 51/50000, 51/50000, 51/50000, 51/50000,
      51/50000] [5, 5, 5, 0, 0, 0, 0] ≤ c0) (k : ℕ) (d : ℕ → ℝ)
    (hd : ∀ c, |d c| ≤ 1 / 1000) :
    |ardot fl r (net.init fl p w k) d 0 0 - dotQ r (xh0 w k)| ≤ c0 + 13 / 10000 := by
  have hlen := init_len ev k
  have h := dot7 ev r hr hW (by norm_num) (init_close ev k) hlen (e := 51 / 50000) (X := 5)
    (fun k' hk' => by
      rw [hlen] at hk'
      interval_cases k' <;> norm_num [List.getD_cons_zero, List.getD_cons_succ])
    d hd (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨h1, -⟩ := h
  refine le_trans h1 ?_
  have : (7 : ℝ) * (1 + 1) * (5 + 51 / 50000 + 1) / 2 ^ 16 + 1 / 2 ^ 100 ≤ 13 / 10000 := by
    norm_num
  linarith

theorem gate1_zero (ev : Ctx u η M fl ex p w) (k : ℕ) :
    head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w k) = 0 := by
  have h0 : |ardot fl head1.g (net.init fl p w k) (p.g 0 0) 0 0 - dotQ z7 (xh0 w k)| ≤
      151 / 10000 + 13 / 10000 :=
    l1_row ev z7 rfl (by simp [z7]) (by norm_num [wErr, z7]) k (p.g 0 0) (ev.hp.g 0 0)
  rw [dotQ_z7, sub_zero] at h0
  have hgb : ((head1.gb : ℚ) : ℝ) = -1 := by norm_num [head1]
  have hb := asw5 ev head1.gb (ev.hp.gb 0 0) (by rw [hgb]; norm_num)
  rw [hgb] at hb
  obtain ⟨h1, h2⟩ := abs_le.mp h0
  obtain ⟨h3, h4⟩ := abs_le.mp hb
  apply gate_zero_of ev head1
  · linarith
  · rw [abs_le]; constructor <;> linarith

theorem cs1_mem (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (k : ℕ) :
    k ∈ head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i ↔ k < i := by
  rw [AHead.mem_cands]
  have hm : head1.mask = Mask.strict := rfl
  rw [hm, Lane4.Seq.mem_cand_strict]
  exact ⟨fun h => h.1, fun h => ⟨h, gate1_zero ev k⟩⟩

/-! ### Generic: a head returns the value of its winner -/

theorem att_gen (ev : Ctx u η M fl ex p w) (h : AHead) (hA : h.A = A7)
    (hm : (h.m : ℝ) = 32) (hmask : h.mask = Mask.causal ∨ h.mask = Mask.strict)
    (x : ℕ → Vec) (hx : ∀ j, j ≤ w.length → (x j).length = 7 ∧ ∀ c, |(x j).getD c 0| ≤ 6)
    (dA : ℕ → ℕ → ℝ) (dm : ℝ) (dg : ℕ → ℝ) (dgb : ℝ) (hdA : ∀ r c, |dA r c| ≤ 1 / 1000)
    (hdm : |dm| ≤ 1 / 1000) (r : List ℚ) (dV : ℕ → ℝ) (i j : ℕ) (hi : i ≤ w.length)
    (hj : j ∈ h.cands fl dg dgb (w.length + 1) x i)
    (hmax : ∀ k ∈ h.cands fl dg dgb (w.length + 1) x i, k ≤ j) {B q ε : ℝ}
    (hB : ∀ k ∈ h.cands fl dg dgb (w.length + 1) x i, |ardot fl r (x k) dV 0 0| ≤ B)
    (hBM : 4 * B + 4 ≤ M) (hq : |ardot fl r (x j) dV 0 0 - q| ≤ ε) :
    |savg fl ex (h.cands fl dg dgb (w.length + 1) x i)
        (fun k => h.score fl dA dm x i k) (fun k => ardot fl r (x k) dV 0 0) - q|
      ≤ ε + B / 100 + 1 / 2 ^ 90 := by
  have hcl : ∀ k ∈ h.cands fl dg dgb (w.length + 1) x i, k ≤ i := by
    intro k hk
    have := ((AHead.mem_cands h fl dg dgb (w.length + 1) x i k).1 hk).1
    rcases hmask with h' | h'
    · rw [h', Lane4.Seq.mem_cand_causal] at this; exact this
    · rw [h', Lane4.Seq.mem_cand_strict] at this; omega
  have hj' : j ≤ w.length := le_trans (hcl j hj) hi
  have hlen : (h.cands fl dg dgb (w.length + 1) x i).length ≤ w.length + 1 := by
    have h1 : (h.cands fl dg dgb (w.length + 1) x i).length ≤
        (cand h.mask (w.length + 1) i).length := by
      unfold AHead.cands
      exact List.length_filter_le _ _
    have h2 : (cand h.mask (w.length + 1) i).length ≤ i + 1 := by
      rcases hmask with h' | h' <;> rw [h'] <;> simp [cand]
    omega
  have hgap : ∀ k ∈ h.cands fl dg dgb (w.length + 1) x i, k ≠ j →
      (fun k => h.score fl dA dm x i k) k ≤
        (fun k => h.score fl dA dm x i k) j - 16 * (ndist j k : ℝ) := by
    intro k hk hne
    have hkj : k < j := lt_of_le_of_ne (hmax k hk) hne
    have hg := score_gap ev h hA hm x hx dA dm hdA hdm i j k hi hj' hkj
    have hkr : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hkj.le
    have hab : |(j : ℝ) - (k : ℝ)| = (j : ℝ) - (k : ℝ) := abs_of_nonneg (by linarith)
    show h.score fl dA dm x i k ≤ h.score fl dA dm x i j - 16 * (ndist j k : ℝ)
    rw [ndist_cast, hab]
    exact hg
  have hS : ∀ k ∈ h.cands fl dg dgb (w.length + 1) x i,
      |(fun k => h.score fl dA dm x i k) k| ≤ 37 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    exact score_abs ev h hA hm x hx dA dm hdA hdm i k hi (le_trans (hcl k hk) hi)
  have hSM : 2 * (37 * ((w.length + 1 : ℕ) : ℝ)) ≤ M := by
    have := ev.rangeN 74 (by norm_num) (by norm_num)
    linarith
  obtain ⟨hs1, -⟩ := soft_near (s := fun k => h.score fl dA dm x i k)
    (f := fun k => ardot fl r (x k) dV 0 0) ev.hr ev.he ev.hu0 ev.hu1 ev.hη0 ev.hη1
    (AHead.cands_nodup h fl dg dgb (w.length + 1) x i) hlen ev.hn ev.hnη hj hgap hS hSM hB hBM
  have hs1' : |savg fl ex (h.cands fl dg dgb (w.length + 1) x i)
        (fun k => h.score fl dA dm x i k) (fun k => ardot fl r (x k) dV 0 0)
        - ardot fl r (x j) dV 0 0| ≤ B / 100 + 1 / 2 ^ 90 := hs1
  have h3 := abs_sub_le (savg fl ex (h.cands fl dg dgb (w.length + 1) x i)
        (fun k => h.score fl dA dm x i k) (fun k => ardot fl r (x k) dV 0 0))
        (ardot fl r (x j) dV 0 0) q
  linarith

/-! ### Layer 1 head outputs -/

noncomputable def att1 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (r : List ℚ) (c : ℕ) : ℝ :=
  savg fl ex (head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i)
    (fun j => head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i j)
    (fun j => ardot fl r (net.init fl p w j) (p.V 0 0 c) 0 0)

theorem attn1_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
      (net.init fl p w) i =
    [att1 fl ex p w i z7 0, att1 fl ex p w i z7 1, att1 fl ex p w i z7 2,
     att1 fl ex p w i cr3 3, att1 fl ex p w i cr4 4, att1 fl ex p w i cr5 5,
     att1 fl ex p w i z7 6] := rfl

theorem att1_gen (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr : r.length = 7)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) {c0 Bq B : ℝ}
    (hwe : wErr (1 / 1000) r [51/50000, 51/50000, 51/50000, 51/50000, 51/50000, 51/50000,
      51/50000] [5, 5, 5, 0, 0, 0, 0] ≤ c0)
    (hq : ∀ k, |dotQ r (xh0 w k)| ≤ Bq) (hq0 : dotQ r (xh0 w 0) = 0)
    (hBq : Bq + (c0 + 13 / 10000) ≤ B) (hB2 : B ≤ 2) (c i : ℕ) (hi : i ≤ w.length) :
    |att1 fl ex p w i r c - dotQ r (xh0 w (i - 1))| ≤ (c0 + 13 / 10000) + B / 100 + 1 / 2 ^ 90 := by
  have hc0 : 0 ≤ c0 + 13 / 10000 := by
    have := l1_row ev r hr hW hwe 0 (p.V 0 0 c) (ev.hp.V 0 0 c)
    have h2 := abs_nonneg (ardot fl r (net.init fl p w 0) (p.V 0 0 c) 0 0 - dotQ r (xh0 w 0))
    linarith
  have hB0 : 0 ≤ B := by
    have := le_trans (abs_nonneg _) (hq 0)
    linarith
  rcases Nat.eq_zero_or_pos i with hi0 | hi1
  · subst hi0
    have hz : att1 fl ex p w 0 r c = 0 := by
      unfold att1
      apply soft_zeros ev.hr
      intro k hk
      have := (cs1_mem ev 0 hi k).1 hk
      omega
    rw [hz]
    have h0 : (0 : ℕ) - 1 = 0 := rfl
    rw [h0, hq0]
    have : (0 : ℝ) < 1 / 2 ^ 90 := by positivity
    simp only [sub_zero, abs_zero]
    linarith
  · have hjm : i - 1 ∈ head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i :=
      (cs1_mem ev i hi (i - 1)).2 (by omega)
    have hmax : ∀ k ∈ head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i,
        k ≤ i - 1 := by
      intro k hk
      have := (cs1_mem ev i hi k).1 hk
      omega
    have hBk : ∀ k ∈ head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i,
        |ardot fl r (net.init fl p w k) (p.V 0 0 c) 0 0| ≤ B := by
      intro k hk
      have hk' := (cs1_mem ev i hi k).1 hk
      have h1 := l1_row ev r hr hW hwe k (p.V 0 0 c) (ev.hp.V 0 0 c)
      have h2 := hq k
      have h3 := abs_sub_abs_le_abs_sub (ardot fl r (net.init fl p w k) (p.V 0 0 c) 0 0)
        (dotQ r (xh0 w k))
      linarith
    have hM12 : 4 * B + 4 ≤ M := by
      have := ev.range 12 (by norm_num)
      linarith
    have h1 := l1_row ev r hr hW hwe (i - 1) (p.V 0 0 c) (ev.hp.V 0 0 c)
    have key := att_gen ev head1 rfl (by norm_num [head1]) (Or.inr rfl) (net.init fl p w)
      (init_bd ev) (p.A 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (ev.hp.A 0 0) (ev.hp.m 0 0) r
      (p.V 0 0 c) i (i - 1) hi hjm hmax hBk hM12 h1
    exact key


/-! ### State after block 0 -/

noncomputable def pf (w : List ℕ) (j c : ℕ) : ℝ :=
  (((if tokAt w (j - 1) = c then 1 else 0 : ℚ)) : ℝ)

theorem pf_bd (w : List ℕ) (j c : ℕ) : |pf w j c| ≤ 1 := by
  unfold pf
  split_ifs <;> norm_num

noncomputable def xh1 (w : List ℕ) (j : ℕ) : List ℝ :=
  [(((if tokAt w j = 1 then 5 else 0 : ℚ)) : ℝ), (((if tokAt w j = 2 then 5 else 0 : ℚ)) : ℝ),
   (((if tokAt w j = 3 then 5 else 0 : ℚ)) : ℝ), pf w j 1, pf w j 2, pf w j 3, 0]

noncomputable def X1 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) : ℕ → Vec :=
  block0.apply fl ex p 0 (w.length + 1) (net.init fl p w)

theorem x1_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (j : ℕ) :
    X1 fl ex p w j =
      Lane4.RSeq.radd fl (Lane4.RSeq.radd fl (net.init fl p w j)
        (head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
          (net.init fl p w) j))
        [fl (0 + asw fl 0 (p.b2 0 0)), fl (0 + asw fl 0 (p.b2 0 1)),
         fl (0 + asw fl 0 (p.b2 0 2)), fl (0 + asw fl 0 (p.b2 0 3)),
         fl (0 + asw fl 0 (p.b2 0 4)), fl (0 + asw fl 0 (p.b2 0 5)),
         fl (0 + asw fl 0 (p.b2 0 6))] := rfl

theorem att1_zero (ev : Ctx u η M fl ex p w) (c i : ℕ) (hi : i ≤ w.length) :
    |att1 fl ex p w i z7 c - 0| ≤ 17 / 1000 := by
  have h := att1_gen ev z7 rfl (by simp [z7]) (c0 := 151 / 10000) (Bq := 0) (B := 17 / 1000)
    (by norm_num [wErr, z7]) (fun k => by rw [dotQ_z7]; simp) (dotQ_z7 _) (by norm_num)
    (by norm_num) c i hi
  rw [dotQ_z7] at h
  refine le_trans h ?_
  norm_num

theorem att1_cp (ev : Ctx u η M fl ex p w) (r : List ℚ) (m : ℕ) (hm : m ≠ 0)
    (hr : r.length = 7) (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1)
    (hwe : wErr (1 / 1000) r [51/50000, 51/50000, 51/50000, 51/50000, 51/50000, 51/50000,
      51/50000] [5, 5, 5, 0, 0, 0, 0] ≤ 153 / 10000)
    (hdq : ∀ k, dotQ r (xh0 w k) = (((if tokAt w k = m then 1 else 0 : ℚ)) : ℝ))
    (c i : ℕ) (hi : i ≤ w.length) :
    |att1 fl ex p w i r c - pf w i m| ≤ 27 / 1000 := by
  have hq : ∀ k, |dotQ r (xh0 w k)| ≤ 1 := by
    intro k
    rw [hdq k]
    split_ifs <;> norm_num
  have hq0 : dotQ r (xh0 w 0) = 0 := by
    rw [hdq 0, Lane4.Seq.tokAt_zero]
    have : (0 : ℕ) ≠ m := fun h => hm h.symm
    simp [this]
  have h := att1_gen ev r hr hW (c0 := 153 / 10000) (Bq := 1) (B := 102 / 100) hwe hq hq0
    (by norm_num) (by norm_num) c i hi
  have e : dotQ r (xh0 w (i - 1)) = pf w i m := by
    rw [hdq]; rfl
  rw [e] at h
  refine le_trans h ?_
  norm_num

theorem dq_cr3 (k : ℕ) : dotQ cr3 (xh0 w k) = (((if tokAt w k = 1 then 1 else 0 : ℚ)) : ℝ) := by
  by_cases h1 : tokAt w k = 1 <;> norm_num [dotQ, cr3, xh0, h1]

theorem dq_cr4 (k : ℕ) : dotQ cr4 (xh0 w k) = (((if tokAt w k = 2 then 1 else 0 : ℚ)) : ℝ) := by
  by_cases h1 : tokAt w k = 2 <;> norm_num [dotQ, cr4, xh0, h1]

theorem dq_cr5 (k : ℕ) : dotQ cr5 (xh0 w k) = (((if tokAt w k = 3 then 1 else 0 : ℚ)) : ℝ) := by
  by_cases h1 : tokAt w k = 3 <;> norm_num [dotQ, cr5, xh0, h1]

theorem x1_close (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : j ≤ w.length) :
    CloseL (X1 fl ex p w j) (xh1 w j) [1/50, 1/50, 1/50, 3/100, 3/100, 3/100, 1/50]
      [5, 5, 5, 1, 1, 1, 0] := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, hx, h0, h1, h2, h3, h4, h5, h6⟩ := init_ent ev j
  rw [x1_eq, hx, attn1_eq]
  simp only [Lane4.RSeq.radd]
  unfold xh1
  have c3 := att1_cp ev cr3 1 (by norm_num) rfl (by norm_num [cr3]) (by norm_num [wErr, cr3])
    (fun k => dq_cr3 k) 3 j hj
  have c4 := att1_cp ev cr4 2 (by norm_num) rfl (by norm_num [cr4]) (by norm_num [wErr, cr4])
    (fun k => dq_cr4 k) 4 j hj
  have c5 := att1_cp ev cr5 3 (by norm_num) rfl (by norm_num [cr5]) (by norm_num [wErr, cr5])
    (fun k => dq_cr5 k) 5 j hj
  refine closeL7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ⟨le_trans (add2 (Xa := 5) (Xt := 0) (Xm := 0) ev h0 (att1_zero ev 0 j hj)
      (mlp_small ev _ (ev.hp.b2 0 0)) (qb _) (by simp) (by simp) (by simp) (by norm_num))
      (by norm_num), qb _⟩
  · exact ⟨le_trans (add2 (Xa := 5) (Xt := 0) (Xm := 0) ev h1 (att1_zero ev 1 j hj)
      (mlp_small ev _ (ev.hp.b2 0 1)) (qb _) (by simp) (by simp) (by simp) (by norm_num))
      (by norm_num), qb _⟩
  · exact ⟨le_trans (add2 (Xa := 5) (Xt := 0) (Xm := 0) ev h2 (att1_zero ev 2 j hj)
      (mlp_small ev _ (ev.hp.b2 0 2)) (qb _) (by simp) (by simp) (by simp) (by norm_num))
      (by norm_num), qb _⟩
  · exact ⟨le_trans (add2 (Xa := 0) (Xt := 1) (Xm := 0) ev h3 c3
      (mlp_small ev _ (ev.hp.b2 0 3)) (by simp) (pf_bd w j 1) (by simp) (by simp)
      (by norm_num)) (by norm_num), pf_bd w j 1⟩
  · exact ⟨le_trans (add2 (Xa := 0) (Xt := 1) (Xm := 0) ev h4 c4
      (mlp_small ev _ (ev.hp.b2 0 4)) (by simp) (pf_bd w j 2) (by simp) (by simp)
      (by norm_num)) (by norm_num), pf_bd w j 2⟩
  · exact ⟨le_trans (add2 (Xa := 0) (Xt := 1) (Xm := 0) ev h5 c5
      (mlp_small ev _ (ev.hp.b2 0 5)) (by simp) (pf_bd w j 3) (by simp) (by simp)
      (by norm_num)) (by norm_num), pf_bd w j 3⟩
  · exact ⟨le_trans (add2 (Xa := 0) (Xt := 0) (Xm := 0) ev h6 (att1_zero ev 6 j hj)
      (mlp_small ev _ (ev.hp.b2 0 6)) (by simp) (by simp) (by simp) (by simp) (by norm_num))
      (by norm_num), by simp⟩

theorem bd_of_closeL {x xh es Xs : List ℝ} (hC : CloseL x xh es Xs) (hl : x.length = 7)
    (hb : ∀ k, k < 7 → es.getD k 0 + Xs.getD k 0 ≤ 6) : ∀ c, |x.getD c 0| ≤ 6 := by
  intro c
  by_cases hc : c < x.length
  · obtain ⟨-, -, -, hk⟩ := hC
    obtain ⟨h1, h2⟩ := hk c hc
    have h3 := hb c (by omega)
    have h4 := abs_sub_abs_le_abs_sub (x.getD c 0) (xh.getD c 0)
    linarith
  · have : x.length ≤ c := not_lt.mp hc
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]
    simp

theorem x1_bd (ev : Ctx u η M fl ex p w) :
    ∀ j, j ≤ w.length → (X1 fl ex p w j).length = 7 ∧ ∀ c, |(X1 fl ex p w j).getD c 0| ≤ 6 := by
  intro j hj
  have hC := x1_close ev j hj
  have hl : (X1 fl ex p w j).length = 7 := by
    have := hC.1
    rw [this]
    simp [xh1]
  refine ⟨hl, bd_of_closeL hC hl ?_⟩
  intro k hk
  interval_cases k <;> norm_num [List.getD_cons_zero, List.getD_cons_succ]

/-! ### Block 1, heads: gates -/

def grow (t : ℕ) : List ℚ :=
  [0, 0, 0, if t = 1 then -1 else 0, if t = 2 then -1 else 0, if t = 3 then -1 else 0, 0]

theorem list7_of_len (x : List ℝ) (h : x.length = 7) :
    ∃ b0 b1 b2 b3 b4 b5 b6 : ℝ, x = [b0, b1, b2, b3, b4, b5, b6] := by
  rcases x with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, x⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp at h
  exact ⟨b0, b1, b2, b3, b4, b5, b6, rfl⟩

theorem closeL_get {b0 b1 b2 b3 b4 b5 b6 g0 g1 g2 g3 g4 g5 g6 e0 e1 e2 e3 e4 e5 e6
    Y0 Y1 Y2 Y3 Y4 Y5 Y6 : ℝ}
    (hC : CloseL [b0, b1, b2, b3, b4, b5, b6] [g0, g1, g2, g3, g4, g5, g6]
      [e0, e1, e2, e3, e4, e5, e6] [Y0, Y1, Y2, Y3, Y4, Y5, Y6]) :
    (|b0 - g0| ≤ e0 ∧ |g0| ≤ Y0) ∧ (|b1 - g1| ≤ e1 ∧ |g1| ≤ Y1) ∧
    (|b2 - g2| ≤ e2 ∧ |g2| ≤ Y2) ∧ (|b3 - g3| ≤ e3 ∧ |g3| ≤ Y3) ∧
    (|b4 - g4| ≤ e4 ∧ |g4| ≤ Y4) ∧ (|b5 - g5| ≤ e5 ∧ |g5| ≤ Y5) ∧
    (|b6 - g6| ≤ e6 ∧ |g6| ≤ Y6) := by
  obtain ⟨-, -, -, hk⟩ := hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hk 0 (by simp)
  · simpa using hk 1 (by simp)
  · simpa using hk 2 (by simp)
  · simpa using hk 3 (by simp)
  · simpa using hk 4 (by simp)
  · simpa using hk 5 (by simp)
  · simpa using hk 6 (by simp)

theorem pf_one {w : List ℕ} {k t : ℕ} (h : tokAt w (k - 1) = t) : pf w k t = 1 := by
  unfold pf
  simp [h]

theorem pf_zero {w : List ℕ} {k t : ℕ} (h : ¬ tokAt w (k - 1) = t) : pf w k t = 0 := by
  unfold pf
  simp [h]

theorem l2_row (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr : r.length = 7)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) {c0 : ℝ}
    (hwe : wErr (1 / 1000) r [1/50, 1/50, 1/50, 3/100, 3/100, 3/100, 1/50]
      [5, 5, 5, 1, 1, 1, 0] ≤ c0) (k : ℕ) (hk : k ≤ w.length) (d : ℕ → ℝ)
    (hd : ∀ c, |d c| ≤ 1 / 1000) :
    |ardot fl r (X1 fl ex p w k) d 0 0 - dotQ r (xh1 w k)| ≤ c0 + 13 / 10000 := by
  have hlen := (x1_bd ev k hk).1
  have h := dot7 ev r hr hW (by norm_num) (x1_close ev k hk) hlen (e := 3 / 100) (X := 5)
    (fun k' hk' => by
      rw [hlen] at hk'
      interval_cases k' <;> norm_num [List.getD_cons_zero, List.getD_cons_succ])
    d hd (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨h1, -⟩ := h
  refine le_trans h1 ?_
  have : (7 : ℝ) * (1 + 1) * (5 + 3 / 100 + 1) / 2 ^ 16 + 1 / 2 ^ 100 ≤ 13 / 10000 := by
    norm_num
  linarith

theorem gate2_pre (ev : Ctx u η M fl ex p w) (hh : AHead) (t : ℕ) (ht1 : 1 ≤ t) (ht3 : t ≤ 3)
    (hg : hh.g = grow t) (hgb : hh.gb = 1 / 2) (k : ℕ) (hk : k ≤ w.length)
    (dg : ℕ → ℝ) (dgb : ℝ) (hdg : ∀ c, |dg c| ≤ 1 / 1000) (hdgb : |dgb| ≤ 1 / 1000) :
    |ardot fl hh.g (X1 fl ex p w k) dg 0 0 + asw fl hh.gb dgb - (1 / 2 - pf w k t)| ≤ 11 / 200 := by
  have hr7 : (grow t).length = 7 := by interval_cases t <;> rfl
  have hW : ∀ a ∈ grow t, |(a : ℝ)| ≤ 1 := by
    intro a ha
    interval_cases t <;> (simp only [grow, List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with h | h | h | h | h | h | h <;> (rw [h]; norm_num))
  have hwe : wErr (1 / 1000) (grow t) [1/50, 1/50, 1/50, 3/100, 3/100, 3/100, 1/50]
      [5, 5, 5, 1, 1, 1, 0] ≤ 483 / 10000 := by
    interval_cases t <;> norm_num [wErr, grow]
  have hdq : dotQ (grow t) (xh1 w k) = - pf w k t := by
    interval_cases t <;> norm_num [dotQ, grow, xh1]
  have h := l2_row ev (grow t) hr7 hW hwe k hk dg hdg
  rw [hdq] at h
  have hb := asw5 ev hh.gb hdgb (by rw [hgb]; norm_num)
  have hhalf : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
  rw [hgb, hhalf] at hb
  rw [hg, hgb]
  obtain ⟨h1, h2⟩ := abs_le.mp h
  obtain ⟨h3, h4⟩ := abs_le.mp hb
  rw [abs_le]
  constructor <;> linarith

theorem gate2_zero (ev : Ctx u η M fl ex p w) (hh : AHead) (t : ℕ) (ht1 : 1 ≤ t) (ht3 : t ≤ 3)
    (hg : hh.g = grow t) (hgb : hh.gb = 1 / 2) (k : ℕ) (hk : k ≤ w.length)
    (dg : ℕ → ℝ) (dgb : ℝ) (hdg : ∀ c, |dg c| ≤ 1 / 1000) (hdgb : |dgb| ≤ 1 / 1000)
    (hP : tokAt w (k - 1) = t) : hh.gate fl dg dgb (X1 fl ex p w k) = 0 := by
  have h := gate2_pre ev hh t ht1 ht3 hg hgb k hk dg dgb hdg hdgb
  rw [pf_one hP] at h
  obtain ⟨h1, h2⟩ := abs_le.mp h
  apply gate_zero_of ev hh
  · linarith
  · rw [abs_le]; constructor <;> linarith

theorem gate2_ne (ev : Ctx u η M fl ex p w) (hh : AHead) (t : ℕ) (ht1 : 1 ≤ t) (ht3 : t ≤ 3)
    (hg : hh.g = grow t) (hgb : hh.gb = 1 / 2) (k : ℕ) (hk : k ≤ w.length)
    (dg : ℕ → ℝ) (dgb : ℝ) (hdg : ∀ c, |dg c| ≤ 1 / 1000) (hdgb : |dgb| ≤ 1 / 1000)
    (hP : ¬ tokAt w (k - 1) = t) : hh.gate fl dg dgb (X1 fl ex p w k) ≠ 0 := by
  have h := gate2_pre ev hh t ht1 ht3 hg hgb k hk dg dgb hdg hdgb
  rw [pf_zero hP] at h
  obtain ⟨h1, h2⟩ := abs_le.mp h
  apply gate_ne_zero_of ev hh
  · linarith
  · rw [abs_le]; constructor <;> linarith

theorem cands2_mem (ev : Ctx u η M fl ex p w) (hh : AHead) (kk t : ℕ) (ht1 : 1 ≤ t)
    (ht3 : t ≤ 3) (hg : hh.g = grow t) (hgb : hh.gb = 1 / 2) (hmask : hh.mask = Mask.causal)
    (i : ℕ) (hi : i ≤ w.length) (k : ℕ) :
    k ∈ hh.cands fl (p.g 1 kk) (p.gb 1 kk) (w.length + 1) (X1 fl ex p w) i ↔
      k ≤ i ∧ tokAt w (k - 1) = t := by
  rw [AHead.mem_cands, hmask, Lane4.Seq.mem_cand_causal]
  constructor
  · rintro ⟨hk, hgz⟩
    refine ⟨hk, ?_⟩
    by_contra hne
    exact gate2_ne ev hh t ht1 ht3 hg hgb k (by omega) (p.g 1 kk) (p.gb 1 kk) (ev.hp.g 1 kk)
      (ev.hp.gb 1 kk) hne hgz
  · rintro ⟨hk, hP⟩
    exact ⟨hk, gate2_zero ev hh t ht1 ht3 hg hgb k (by omega) (p.g 1 kk) (p.gb 1 kk)
      (ev.hp.g 1 kk) (ev.hp.gb 1 kk) hP⟩

/-! ### Block 1, heads: outputs -/

noncomputable def att2 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (hh : AHead) (kk i : ℕ)
    (r : List ℚ) (c : ℕ) : ℝ :=
  savg fl ex (hh.cands fl (p.g 1 kk) (p.gb 1 kk) (w.length + 1) (X1 fl ex p w) i)
    (fun j => hh.score fl (p.A 1 kk) (p.m 1 kk) (X1 fl ex p w) i j)
    (fun j => ardot fl r (X1 fl ex p w j) (p.V 1 kk c) 0 0)

noncomputable def vq (w : List ℕ) (t i : ℕ) : ℝ :=
  dotQ vrow (xh1 w (Nat.findGreatest (fun k => tokAt w (k - 1) = t) i))

theorem dq_vrow (w : List ℕ) (m : ℕ) :
    dotQ vrow (xh1 w m) = (((if tokAt w m = 2 then 4 else if tokAt w m = 3 then 2 else 0 : ℚ)) : ℝ) := by
  by_cases h2 : tokAt w m = 2
  · norm_num [dotQ, vrow, xh1, h2]
  · by_cases h3 : tokAt w m = 3
    · norm_num [dotQ, vrow, xh1, h3]
    · norm_num [dotQ, vrow, xh1, h2, h3]

theorem vq_bd (w : List ℕ) (t i : ℕ) : 0 ≤ vq w t i ∧ vq w t i ≤ 4 := by
  unfold vq
  rw [dq_vrow]
  split_ifs <;> norm_num

theorem att2_gen (ev : Ctx u η M fl ex p w) (hh : AHead) (kk t : ℕ) (ht1 : 1 ≤ t)
    (ht3 : t ≤ 3) (hA : hh.A = A7) (hm : (hh.m : ℝ) = 32) (hmask : hh.mask = Mask.causal)
    (hg : hh.g = grow t) (hgb : hh.gb = 1 / 2)
    (r : List ℚ) (hr : r.length = 7) (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) {c0 Bq B : ℝ}
    (hwe : wErr (1 / 1000) r [1/50, 1/50, 1/50, 3/100, 3/100, 3/100, 1/50]
      [5, 5, 5, 1, 1, 1, 0] ≤ c0)
    (hq : ∀ k, k ≤ w.length → |dotQ r (xh1 w k)| ≤ Bq) (hq0 : dotQ r (xh1 w 0) = 0)
    (hBq : Bq + (c0 + 13 / 10000) ≤ B) (hB5 : B ≤ 5) (c i : ℕ) (hi : i ≤ w.length) :
    |att2 fl ex p w hh kk i r c -
        dotQ r (xh1 w (Nat.findGreatest (fun k => tokAt w (k - 1) = t) i))|
      ≤ (c0 + 13 / 10000) + B / 100 + 1 / 2 ^ 90 := by
  have hc0 : 0 ≤ c0 + 13 / 10000 := by
    have := l2_row ev r hr hW hwe 0 (Nat.zero_le _) (p.V 1 kk c) (ev.hp.V 1 kk c)
    have h2 := abs_nonneg (ardot fl r (X1 fl ex p w 0) (p.V 1 kk c) 0 0 - dotQ r (xh1 w 0))
    linarith
  have hB0 : 0 ≤ B := by
    have := le_trans (abs_nonneg _) (hq 0 (Nat.zero_le _))
    linarith
  have mem := cands2_mem ev hh kk t ht1 ht3 hg hgb hmask i hi
  by_cases hex : ∃ k, k ≤ i ∧ tokAt w (k - 1) = t
  · obtain ⟨k0, hk0, hP0⟩ := hex
    obtain ⟨ks, hks⟩ : ∃ ks, Nat.findGreatest (fun k => tokAt w (k - 1) = t) i = ks :=
      ⟨_, rfl⟩
    have hPks : tokAt w (ks - 1) = t := by
      rw [← hks]
      exact Nat.findGreatest_spec (P := fun k => tokAt w (k - 1) = t) hk0 hP0
    have hksle : ks ≤ i := by
      rw [← hks]
      exact Nat.findGreatest_le i
    have hmem : ks ∈ hh.cands fl (p.g 1 kk) (p.gb 1 kk) (w.length + 1) (X1 fl ex p w) i :=
      (mem ks).2 ⟨hksle, hPks⟩
    have hmax : ∀ k ∈ hh.cands fl (p.g 1 kk) (p.gb 1 kk) (w.length + 1) (X1 fl ex p w) i,
        k ≤ ks := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := (mem k).1 hk
      rw [← hks]
      exact Nat.le_findGreatest hk1 hk2
    have hBk : ∀ k ∈ hh.cands fl (p.g 1 kk) (p.gb 1 kk) (w.length + 1) (X1 fl ex p w) i,
        |ardot fl r (X1 fl ex p w k) (p.V 1 kk c) 0 0| ≤ B := by
      intro k hk
      have hk' := ((mem k).1 hk).1
      have h1 := l2_row ev r hr hW hwe k (by omega) (p.V 1 kk c) (ev.hp.V 1 kk c)
      have h2 := hq k (by omega)
      have h3 := abs_sub_abs_le_abs_sub (ardot fl r (X1 fl ex p w k) (p.V 1 kk c) 0 0)
        (dotQ r (xh1 w k))
      linarith
    have hM12 : 4 * B + 4 ≤ M := by
      have := ev.range 24 (by norm_num)
      linarith
    have h1 := l2_row ev r hr hW hwe ks (by omega) (p.V 1 kk c) (ev.hp.V 1 kk c)
    rw [hks]
    exact att_gen ev hh hA hm (Or.inl hmask) (X1 fl ex p w) (x1_bd ev) (p.A 1 kk) (p.m 1 kk)
      (p.g 1 kk) (p.gb 1 kk) (ev.hp.A 1 kk) (ev.hp.m 1 kk) r (p.V 1 kk c) i ks hi hmem hmax hBk
      hM12 h1
  · have hz : att2 fl ex p w hh kk i r c = 0 := by
      unfold att2
      apply soft_zeros ev.hr
      intro k hk
      exfalso
      obtain ⟨h1, h2⟩ := (mem k).1 hk
      exact hex ⟨k, h1, h2⟩
    have hk0 : Nat.findGreatest (fun k => tokAt w (k - 1) = t) i = 0 :=
      Nat.findGreatest_eq_zero_iff.2 (fun k hk0 hki hP => hex ⟨k, hki, hP⟩)
    rw [hz, hk0, hq0]
    have : (0 : ℝ) < 1 / 2 ^ 90 := by positivity
    simp only [sub_zero, abs_zero]
    linarith

theorem att2_val (ev : Ctx u η M fl ex p w) (hh : AHead) (kk t : ℕ) (ht1 : 1 ≤ t)
    (ht3 : t ≤ 3) (hA : hh.A = A7) (hm : (hh.m : ℝ) = 32) (hmask : hh.mask = Mask.causal)
    (hg : hh.g = grow t) (hgb : hh.gb = 1 / 2) (c i : ℕ) (hi : i ≤ w.length) :
    |att2 fl ex p w hh kk i vrow c - vq w t i| ≤ 85 / 1000 := by
  have h := att2_gen ev hh kk t ht1 ht3 hA hm hmask hg hgb vrow rfl
    (by intro a ha; simp only [vrow, List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with h | h | h | h | h | h | h <;> (rw [h]; norm_num))
    (c0 := 423 / 10000) (Bq := 4) (B := 405 / 100) (by norm_num [wErr, vrow])
    (fun k _ => by rw [dq_vrow]; split_ifs <;> norm_num)
    (by rw [dq_vrow, Lane4.Seq.tokAt_zero]; norm_num) (by norm_num) (by norm_num) c i hi
  refine le_trans h ?_
  norm_num

theorem att2_zero (ev : Ctx u η M fl ex p w) (hh : AHead) (kk t : ℕ) (ht1 : 1 ≤ t)
    (ht3 : t ≤ 3) (hA : hh.A = A7) (hm : (hh.m : ℝ) = 32) (hmask : hh.mask = Mask.causal)
    (hg : hh.g = grow t) (hgb : hh.gb = 1 / 2) (c i : ℕ) (hi : i ≤ w.length) :
    |att2 fl ex p w hh kk i z7 c - 0| ≤ 1 / 50 := by
  have h := att2_gen ev hh kk t ht1 ht3 hA hm hmask hg hgb z7 rfl (by simp [z7])
    (c0 := 183 / 10000) (Bq := 0) (B := 2 / 100) (by norm_num [wErr, z7])
    (fun k _ => by rw [dotQ_z7]; simp) (dotQ_z7 _) (by norm_num) (by norm_num) c i hi
  rw [dotQ_z7] at h
  refine le_trans h ?_
  norm_num

/-! ### Block 1: the state after the heads -/

theorem hd1_ok : hd1.A = A7 ∧ ((hd1.m : ℚ) : ℝ) = 32 ∧ hd1.mask = Mask.causal ∧
    hd1.g = grow 1 ∧ hd1.gb = 1 / 2 :=
  ⟨rfl, by norm_num [hd1], rfl, by first | rfl | simp [hd1, grow], rfl⟩

theorem hd2_ok : hd2.A = A7 ∧ ((hd2.m : ℚ) : ℝ) = 32 ∧ hd2.mask = Mask.causal ∧
    hd2.g = grow 2 ∧ hd2.gb = 1 / 2 :=
  ⟨rfl, by norm_num [hd2], rfl, by first | rfl | simp [hd2, grow], rfl⟩

theorem hd3_ok : hd3.A = A7 ∧ ((hd3.m : ℚ) : ℝ) = 32 ∧ hd3.mask = Mask.causal ∧
    hd3.g = grow 3 ∧ hd3.gb = 1 / 2 :=
  ⟨rfl, by norm_num [hd3], rfl, by first | rfl | simp [hd3, grow], rfl⟩

noncomputable def att2v (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (hh : AHead) (kk i : ℕ) : Vec :=
  hh.attn fl ex (p.A 1 kk) (p.V 1 kk) (p.m 1 kk) (p.g 1 kk) (p.gb 1 kk) (w.length + 1)
    (X1 fl ex p w) i

theorem att2v_1 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    att2v fl ex p w hd1 0 i =
      [att2 fl ex p w hd1 0 i vrow 0, att2 fl ex p w hd1 0 i z7 1, att2 fl ex p w hd1 0 i z7 2,
       att2 fl ex p w hd1 0 i z7 3, att2 fl ex p w hd1 0 i z7 4, att2 fl ex p w hd1 0 i z7 5,
       att2 fl ex p w hd1 0 i z7 6] := rfl

theorem att2v_2 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    att2v fl ex p w hd2 1 i =
      [att2 fl ex p w hd2 1 i z7 0, att2 fl ex p w hd2 1 i vrow 1, att2 fl ex p w hd2 1 i z7 2,
       att2 fl ex p w hd2 1 i z7 3, att2 fl ex p w hd2 1 i z7 4, att2 fl ex p w hd2 1 i z7 5,
       att2 fl ex p w hd2 1 i z7 6] := rfl

theorem att2v_3 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    att2v fl ex p w hd3 2 i =
      [att2 fl ex p w hd3 2 i z7 0, att2 fl ex p w hd3 2 i z7 1, att2 fl ex p w hd3 2 i vrow 2,
       att2 fl ex p w hd3 2 i z7 3, att2 fl ex p w hd3 2 i z7 4, att2 fl ex p w hd3 2 i z7 5,
       att2 fl ex p w hd3 2 i z7 6] := rfl

noncomputable def Ypre (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : Vec :=
  aheadsApply fl ex p 1 (w.length + 1) (X1 fl ex p w) i [hd1, hd2, hd3] (X1 fl ex p w i) 0

theorem ypre_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    Ypre fl ex p w i =
      Lane4.RSeq.radd fl (Lane4.RSeq.radd fl (Lane4.RSeq.radd fl (X1 fl ex p w i)
        (att2v fl ex p w hd1 0 i)) (att2v fl ex p w hd2 1 i)) (att2v fl ex p w hd3 2 i) := rfl

noncomputable def yh (w : List ℕ) (i : ℕ) : List ℝ :=
  [(((if tokAt w i = 1 then 5 else 0 : ℚ)) : ℝ) + vq w 1 i,
   (((if tokAt w i = 2 then 5 else 0 : ℚ)) : ℝ) + vq w 2 i,
   (((if tokAt w i = 3 then 5 else 0 : ℚ)) : ℝ) + vq w 3 i, pf w i 1, pf w i 2, pf w i 3, 0]

theorem vq_abs (w : List ℕ) (t i : ℕ) : |vq w t i| ≤ 4 := by
  have := vq_bd w t i
  rw [abs_le]
  constructor <;> linarith [this.1, this.2]

theorem add3 (ev : Ctx u η M fl ex p w) {a t1 t2 t3 a' t1' t2' t3' y e1 e2 e3 e4 Xa X1' X2' X3' : ℝ}
    (ha : |a - a'| ≤ e1) (h1 : |t1 - t1'| ≤ e2) (h2 : |t2 - t2'| ≤ e3) (h3 : |t3 - t3'| ≤ e4)
    (hXa : |a'| ≤ Xa) (hX1 : |t1'| ≤ X1') (hX2 : |t2'| ≤ X2') (hX3 : |t3'| ≤ X3')
    (hy : a' + t1' + t2' + t3' = y)
    (hs : Xa + X1' + X2' + X3' + e1 + e2 + e3 + e4 ≤ 40) :
    |fl (fl (fl (a + t1) + t2) + t3) - y| ≤ e1 + e2 + e3 + e4 + 3 / 50000 := by
  have he1 : 0 ≤ e1 := le_trans (abs_nonneg _) ha
  have he2 : 0 ≤ e2 := le_trans (abs_nonneg _) h1
  have he3 : 0 ≤ e3 := le_trans (abs_nonneg _) h2
  have he4 : 0 ≤ e4 := le_trans (abs_nonneg _) h3
  have hXa0 : 0 ≤ Xa := le_trans (abs_nonneg _) hXa
  have hX10 : 0 ≤ X1' := le_trans (abs_nonneg _) hX1
  have hX20 : 0 ≤ X2' := le_trans (abs_nonneg _) hX2
  have hX30 : 0 ≤ X3' := le_trans (abs_nonneg _) hX3
  have hs1 : |a' + t1'| ≤ Xa + X1' := le_trans (abs_add_le _ _) (by linarith)
  have r1 := add1 ev ha h1 hXa hX1 (by linarith)
  have r2 := add1 ev r1 h2 hs1 hX2 (by linarith)
  have hs2 : |a' + t1' + t2'| ≤ Xa + X1' + X2' := le_trans (abs_add_le _ _) (by linarith)
  have r3 := add1 ev r2 h3 hs2 hX3 (by linarith)
  rw [hy] at r3
  linarith

theorem ypre_close (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    CloseL (Ypre fl ex p w i) (yh w i) [73/500, 73/500, 73/500, 91/1000, 91/1000, 91/1000, 81/1000]
      [9, 9, 9, 1, 1, 1, 0] := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, hb⟩ := list7_of_len (X1 fl ex p w i) (x1_bd ev i hi).1
  have hC := x1_close ev i hi
  rw [hb] at hC
  unfold xh1 at hC
  obtain ⟨⟨g0, -⟩, ⟨g1, -⟩, ⟨g2, -⟩, ⟨g3, -⟩, ⟨g4, -⟩, ⟨g5, -⟩, ⟨g6, -⟩⟩ := closeL_get hC
  obtain ⟨hA1, hm1, hk1, hg1, hb1⟩ := hd1_ok
  obtain ⟨hA2, hm2, hk2, hg2, hb2⟩ := hd2_ok
  obtain ⟨hA3, hm3, hk3, hg3, hb3⟩ := hd3_ok
  have v1 := fun c => att2_val ev hd1 0 1 (by norm_num) (by norm_num) hA1 hm1 hk1 hg1 hb1 c i hi
  have v2 := fun c => att2_val ev hd2 1 2 (by norm_num) (by norm_num) hA2 hm2 hk2 hg2 hb2 c i hi
  have v3 := fun c => att2_val ev hd3 2 3 (by norm_num) (by norm_num) hA3 hm3 hk3 hg3 hb3 c i hi
  have z1 := fun c => att2_zero ev hd1 0 1 (by norm_num) (by norm_num) hA1 hm1 hk1 hg1 hb1 c i hi
  have z2 := fun c => att2_zero ev hd2 1 2 (by norm_num) (by norm_num) hA2 hm2 hk2 hg2 hb2 c i hi
  have z3 := fun c => att2_zero ev hd3 2 3 (by norm_num) (by norm_num) hA3 hm3 hk3 hg3 hb3 c i hi
  rw [ypre_eq, hb, att2v_1, att2v_2, att2v_3]
  simp only [Lane4.RSeq.radd]
  unfold yh
  have q1 := qb (tokAt w i = 1)
  have q2 := qb (tokAt w i = 2)
  have q3 := qb (tokAt w i = 3)
  refine closeL7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨le_trans (add3 (Xa := 5) (X1' := 4) (X2' := 0) (X3' := 0) ev g0 (v1 0) (z2 0) (z3 0)
      q1 (vq_abs w 1 i) (by simp) (by simp) (by ring) (by norm_num)) (by norm_num), ?_⟩
    exact le_trans (abs_add_le _ _) (by linarith)
  · refine ⟨le_trans (add3 (Xa := 5) (X1' := 0) (X2' := 4) (X3' := 0) ev g1 (z1 1) (v2 1) (z3 1)
      q2 (by simp) (vq_abs w 2 i) (by simp) (by ring) (by norm_num)) (by norm_num), ?_⟩
    exact le_trans (abs_add_le _ _) (by linarith)
  · refine ⟨le_trans (add3 (Xa := 5) (X1' := 0) (X2' := 0) (X3' := 4) ev g2 (z1 2) (z2 2) (v3 2)
      q3 (by simp) (by simp) (vq_abs w 3 i) (by ring) (by norm_num)) (by norm_num), ?_⟩
    exact le_trans (abs_add_le _ _) (by linarith)
  · exact ⟨le_trans (add3 (Xa := 1) (X1' := 0) (X2' := 0) (X3' := 0) ev g3 (z1 3) (z2 3) (z3 3)
      (pf_bd w i 1) (by simp) (by simp) (by simp) (by ring) (by norm_num)) (by norm_num),
      pf_bd w i 1⟩
  · exact ⟨le_trans (add3 (Xa := 1) (X1' := 0) (X2' := 0) (X3' := 0) ev g4 (z1 4) (z2 4) (z3 4)
      (pf_bd w i 2) (by simp) (by simp) (by simp) (by ring) (by norm_num)) (by norm_num),
      pf_bd w i 2⟩
  · exact ⟨le_trans (add3 (Xa := 1) (X1' := 0) (X2' := 0) (X3' := 0) ev g5 (z1 5) (z2 5) (z3 5)
      (pf_bd w i 3) (by simp) (by simp) (by simp) (by ring) (by norm_num)) (by norm_num),
      pf_bd w i 3⟩
  · exact ⟨le_trans (add3 (Xa := 0) (X1' := 0) (X2' := 0) (X3' := 0) ev g6 (z1 6) (z2 6) (z3 6)
      (by simp) (by simp) (by simp) (by simp) (by ring) (by norm_num)) (by norm_num), by simp⟩

/-! ### The target in terms of the ideal winner -/

theorem find_some : ∀ (m : ℕ) (q : ℕ → Bool) (j : ℕ), (List.range m).reverse.find? q = some j →
    j < m ∧ q j = true ∧ ∀ j', j < j' → j' < m → q j' = false := by
  intro m
  induction m with
  | zero => intro q j h; simp at h
  | succ m ih =>
    intro q j h
    have e : (List.range (m + 1)).reverse = m :: (List.range m).reverse := by
      simp [List.range_succ]
    rw [e] at h
    cases hq : q m
    · simp [List.find?_cons, hq] at h
      obtain ⟨h1, h2, h3⟩ := ih q j h
      refine ⟨by omega, h2, fun j' hj' hj'm => ?_⟩
      by_cases hjm : j' = m
      · rw [hjm]; exact hq
      · exact h3 j' hj' (by omega)
    · simp [List.find?_cons, hq] at h
      subst h
      exact ⟨by omega, hq, fun j' h1 h2 => by omega⟩

theorem find_none : ∀ (m : ℕ) (q : ℕ → Bool), (List.range m).reverse.find? q = none →
    ∀ j, j < m → q j = false := by
  intro m
  induction m with
  | zero => intro q h j hj; omega
  | succ m ih =>
    intro q h j hj
    have e : (List.range (m + 1)).reverse = m :: (List.range m).reverse := by
      simp [List.range_succ]
    rw [e] at h
    cases hq : q m
    · simp [List.find?_cons, hq] at h
      by_cases hjm : j = m
      · rw [hjm]; exact hq
      · exact ih q h j (by omega)
    · simp [List.find?_cons, hq] at h

theorem h_half (τ : ℕ) :
    (((if τ = 2 then 4 else if τ = 3 then 2 else 0 : ℚ)) : ℝ) / 2 = ((Lane4.Case.h τ : ℕ) : ℝ) := by
  by_cases h1 : τ = 1 <;> by_cases h2 : τ = 2 <;> by_cases h3 : τ = 3 <;>
    simp [Lane4.Case.h, h1, h2, h3] <;> norm_num

theorem tok_pos (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (i : ℕ) (hi1 : 1 ≤ i)
    (hi : i ≤ w.length) : 1 ≤ tokAt w i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Lane4.Seq.tokAt_succ w k (by omega)]
  exact (hw _ (List.getElem_mem (by omega))).1

theorem target_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (i : ℕ) (hi1 : 1 ≤ i)
    (hi : i ≤ w.length) : ((target w i : ℕ) : ℝ) = vq w (tokAt w i) i / 2 := by
  have ht := tok_pos w hw i hi1 hi
  unfold target
  rcases hj : prevOcc w i with _ | j
  · dsimp only
    have hn := find_none i _ (by unfold prevOcc at hj; exact hj)
    have hk0 : Nat.findGreatest (fun k => tokAt w (k - 1) = tokAt w i) i = 0 := by
      apply Nat.findGreatest_eq_zero_iff.2
      intro k hk0 hki hP
      have := hn (k - 1) (by omega)
      simp at this
      by_cases hk1 : k - 1 = 0
      · rw [hk1, Lane4.Seq.tokAt_zero] at hP
        omega
      · exact this (by omega) hP
    unfold vq
    rw [hk0, dq_vrow, Lane4.Seq.tokAt_zero]
    norm_num
  · dsimp only
    obtain ⟨hjlt, hq, hmax⟩ := find_some i _ j (by unfold prevOcc at hj; exact hj)
    simp at hq
    obtain ⟨hj1, hjt⟩ := hq
    have hP1 : tokAt w (j + 1 - 1) = tokAt w i := by simpa using hjt
    have hks : Nat.findGreatest (fun k => tokAt w (k - 1) = tokAt w i) i = j + 1 := by
      have hge : j + 1 ≤ Nat.findGreatest (fun k => tokAt w (k - 1) = tokAt w i) i :=
        Nat.le_findGreatest (P := fun k => tokAt w (k - 1) = tokAt w i) (by omega) hP1
      have hspec : tokAt w (Nat.findGreatest (fun k => tokAt w (k - 1) = tokAt w i) i - 1)
          = tokAt w i :=
        Nat.findGreatest_spec (P := fun k => tokAt w (k - 1) = tokAt w i) (m := j + 1)
          (by omega) hP1
      have hle : Nat.findGreatest (fun k => tokAt w (k - 1) = tokAt w i) i ≤ i :=
        Nat.findGreatest_le i
      by_contra hne
      have hgt : j + 1 < Nat.findGreatest (fun k => tokAt w (k - 1) = tokAt w i) i := by omega
      have := hmax (Nat.findGreatest (fun k => tokAt w (k - 1) = tokAt w i) i - 1) (by omega)
        (by omega)
      simp at this
      exact this (by omega) hspec
    unfold vq
    rw [hks, dq_vrow, h_half]
    have e : j + 1 = j + 1 := rfl
    rfl

end Steps

end Lane4.Case
