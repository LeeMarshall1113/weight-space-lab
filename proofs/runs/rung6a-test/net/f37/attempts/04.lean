namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

/-! coordinates: 0 mk, 1 a, 2 c, 3 f (=F/4), 4 A, 5 y -/

def z6 : List ℚ := [0, 0, 0, 0, 0, 0]
def z2 : List ℚ := [0, 0]

def head0 : AHead :=
  { A := [z6, z6, z6, z6, z6, z6],
    V := [z6, z6, z6, [1/4, 0, 0, 0, 0, 0], z6, z6],
    mask := Mask.strict, m := 24, g := [-1, 0, 0, 0, 0, 0], gb := 1/2 }

def head1 : AHead :=
  { A := [z6, z6, z6, z6, z6, z6],
    V := [z6, z6, z6, z6, [0, 1, 0, 0, 0, 0], z6],
    mask := Mask.causal, m := 24, g := [-1, 0, 0, 4, 0, 0], gb := 1/2 }

def blk0 : ABlock :=
  { heads := [head0], W1 := [], b1 := [], W2 := [[], [], [], [], [], []], b2 := z6 }

def blk1 : ABlock :=
  { heads := [head1], W1 := [[0, 0, 1, 0, -1, 0], [0, 0, -1, 0, 1, 0]], b1 := z2,
    W2 := [z2, z2, z2, z2, z2, [1, 1]], b2 := z6 }

def net : ANet :=
  { embed := [z6, [0, 0, 1, 0, 0, 0], z6, z6, [1, 1, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0]],
    blocks := [blk0, blk1], outW := [0, 0, 0, 0, 0, 1], outB := 0 }


/-! ### ideal quantities -/

noncomputable def mkR (t : ℕ) : ℝ := if t = 4 ∨ t = 5 then 1 else 0
noncomputable def aR (t : ℕ) : ℝ := if t = 4 then 1 else 0
noncomputable def cR (t : ℕ) : ℝ := if t = 1 ∨ t = 4 ∨ t = 5 then 1 else 0

def mkQ (t : ℕ) : ℚ := if t = 4 ∨ t = 5 then 1 else 0
def aQ (t : ℕ) : ℚ := if t = 4 then 1 else 0
def cQ (t : ℕ) : ℚ := if t = 1 ∨ t = 4 ∨ t = 5 then 1 else 0

theorem mkQ_R (t : ℕ) : ((mkQ t : ℚ) : ℝ) = mkR t := by
  unfold mkQ mkR; split_ifs <;> simp
theorem aQ_R (t : ℕ) : ((aQ t : ℚ) : ℝ) = aR t := by
  unfold aQ aR; split_ifs <;> simp
theorem cQ_R (t : ℕ) : ((cQ t : ℚ) : ℝ) = cR t := by
  unfold cQ cR; split_ifs <;> simp

theorem mkR_01 (t : ℕ) : mkR t = 0 ∨ mkR t = 1 := by
  unfold mkR; split_ifs <;> simp
theorem aR_01 (t : ℕ) : aR t = 0 ∨ aR t = 1 := by
  unfold aR; split_ifs <;> simp
theorem cR_01 (t : ℕ) : cR t = 0 ∨ cR t = 1 := by
  unfold cR; split_ifs <;> simp

theorem embed_row {t : ℕ} (h : t ≤ 5) :
    net.embed.getD t [] = [mkQ t, aQ t, cQ t, 0, 0, 0] := by
  interval_cases t <;> simp [net, z6, mkQ, aQ, cQ]

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (j : ℕ) (h : tokAt w j ≤ 5) :
    net.init fl p w j = [asw fl (mkQ (tokAt w j)) (p.E (tokAt w j) 0),
      asw fl (aQ (tokAt w j)) (p.E (tokAt w j) 1), asw fl (cQ (tokAt w j)) (p.E (tokAt w j) 2),
      asw fl 0 (p.E (tokAt w j) 3), asw fl 0 (p.E (tokAt w j) 4),
      asw fl 0 (p.E (tokAt w j) 5)] := by
  show aswRow fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0 = _
  rw [embed_row h]
  rfl

/-- `Close` for six entries. -/
theorem close6 {a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 e X : ℝ}
    (h0 : |a0 - b0| ≤ e) (h1 : |a1 - b1| ≤ e) (h2 : |a2 - b2| ≤ e)
    (h3 : |a3 - b3| ≤ e) (h4 : |a4 - b4| ≤ e) (h5 : |a5 - b5| ≤ e)
    (g0 : |b0| ≤ X) (g1 : |b1| ≤ X) (g2 : |b2| ≤ X) (g3 : |b3| ≤ X) (g4 : |b4| ≤ X)
    (g5 : |b5| ≤ X) :
    Close [a0, a1, a2, a3, a4, a5] [b0, b1, b2, b3, b4, b5] e X := by
  refine ⟨rfl, ?_⟩
  intro k hk
  have hk6 : k < 6 := by simpa using hk
  interval_cases k <;> simp only [List.getD_cons_zero, List.getD_cons_succ] <;>
    first | exact ⟨h0, g0⟩ | exact ⟨h1, g1⟩ | exact ⟨h2, g2⟩ | exact ⟨h3, g3⟩ |
      exact ⟨h4, g4⟩ | exact ⟨h5, g5⟩

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

/-- small constants -/
theorem Ctx.small (ev : Ctx u η M fl ex p w) : u ≤ 1 / 10000000 ∧ η ≤ 1 / 10 ^ 30 := by
  refine ⟨le_trans ev.hu1 (by norm_num), le_trans (eta_tiny ev.hη1) (by norm_num)⟩

/-- A stored weight `fl (a + d)`, `|a| ≤ 5`, is within 1/900 of `a`. -/
theorem asw_c (ev : Ctx u η M fl ex p w) (a : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 1000)
    (ha : |(a : ℝ)| ≤ 5) : |asw fl a d - (a : ℝ)| ≤ 1 / 900 := by
  have h := asw_near ev.hr ev.hu0 a hd (by have := ev.range 6 (by norm_num); linarith)
  have h1 : u * (|(a : ℝ)| + 1 / 1000) ≤ 1 / 10000000 * 6 := by
    have := ev.small
    exact mul_le_mul this.1 (by linarith) (by positivity) (by positivity)
  have h2 := ev.small.2
  linarith

theorem init_ent (ev : Ctx u η M fl ex p w) (j : ℕ) :
    ∃ a0 a1 a2 a3 a4 a5 : ℝ, net.init fl p w j = [a0, a1, a2, a3, a4, a5] ∧
      |a0 - mkR (tokAt w j)| ≤ 1 / 900 ∧ |a1 - aR (tokAt w j)| ≤ 1 / 900 ∧
      |a2 - cR (tokAt w j)| ≤ 1 / 900 ∧ |a3 - 0| ≤ 1 / 900 ∧ |a4 - 0| ≤ 1 / 900 ∧
      |a5 - 0| ≤ 1 / 900 := by
  have ht := tok_le w ev.hw j
  refine ⟨_, _, _, _, _, _, init_eq fl p w j ht, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := asw_c ev (mkQ (tokAt w j)) (ev.hp.E (tokAt w j) 0)
      (by rw [mkQ_R]; rcases mkR_01 (tokAt w j) with h | h <;> rw [h] <;> norm_num)
    rwa [mkQ_R] at h
  · have h := asw_c ev (aQ (tokAt w j)) (ev.hp.E (tokAt w j) 1)
      (by rw [aQ_R]; rcases aR_01 (tokAt w j) with h | h <;> rw [h] <;> norm_num)
    rwa [aQ_R] at h
  · have h := asw_c ev (cQ (tokAt w j)) (ev.hp.E (tokAt w j) 2)
      (by rw [cQ_R]; rcases cR_01 (tokAt w j) with h | h <;> rw [h] <;> norm_num)
    rwa [cQ_R] at h
  · have h := asw_c ev 0 (ev.hp.E (tokAt w j) 3) (by simp)
    simpa using h
  · have h := asw_c ev 0 (ev.hp.E (tokAt w j) 4) (by simp)
    simpa using h
  · have h := asw_c ev 0 (ev.hp.E (tokAt w j) 5) (by simp)
    simpa using h


theorem u_mul (ev : Ctx u η M fl ex p w) (c : ℝ) (hc : 0 ≤ c) :
    u * (c * ((w.length + 1 : ℕ) : ℝ)) ≤ c / 256 := by
  have h : u * (c * ((w.length + 1 : ℕ) : ℝ)) = c * (u * ((w.length + 1 : ℕ) : ℝ)) := by ring
  rw [h]
  have := mul_le_mul_of_nonneg_left ev.hn hc
  linarith

/-- Width-6 dot product: error `absSum r * e + 1/130`, magnitude at most 70. -/
theorem ardot6 (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr6 : r.length = 6) {W : ℝ}
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ W) (hW0 : 0 ≤ W) (hW4 : W ≤ 4) (x xh : List ℝ)
    (hx : x.length = 6) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1 / 10) (hC : Close x xh e 1)
    (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r x d 0 0 - dotQ r xh| ≤ absSum r * e + 1 / 130 ∧ |ardot fl r x d 0 0| ≤ 70 := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have hT : (W + 1) * (1 + e + 1) ≤ 2 ^ 20 := by
    have : (W + 1) * (1 + e + 1) ≤ 5 * 3 :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    have h20 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
    rw [h20]; linarith
  have k1 := ardot_near_abs u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (by norm_num)
    (by norm_num) r x xh d W 1 e (by omega) (by omega) hC hd hW hW0 (by norm_num) he0 hT hM30
  have k2 := ardot_near u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (by norm_num)
    (by norm_num) r x xh d W 1 e (by omega) (by omega) hC hd hW hW0 (by norm_num) he0 hT hM30
  rw [hr6] at k1 k2
  have h3 : ((6 : ℕ) : ℝ) = 6 := by norm_num
  have h16 : (2 : ℝ) ^ 16 = 65536 := by norm_num
  have h100 : (1 : ℝ) / 2 ^ 100 = 1 / 1267650600228229401496703205376 := by norm_num
  have hWW : (W + 1) * (1 + e + 1) ≤ 5 * (21 / 10) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  simp only [h3, h16, h100] at k1 k2
  constructor
  · nlinarith [k1.1, hWW]
  · nlinarith [k2.2, hWW]

theorem dotQ_z6 (xh : List ℝ) : dotQ z6 xh = 0 := by
  simp [dotQ, z6]

theorem absSum_z6 : absSum z6 = 0 := by
  simp [absSum, z6]

/-- A gate with pre-activation that is at most `-1/2` (ideal) is exactly 0. -/
theorem gate_zero (ev : Ctx u η M fl ex p w) (h : AHead) (hg6 : h.g.length = 6)
    (hgW : ∀ a ∈ h.g, |(a : ℝ)| ≤ 4) (hgb : ((h.gb : ℚ) : ℝ) = 1 / 2) (x xh : List ℝ)
    (hx : x.length = 6) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1 / 10) (hC : Close x xh e 1)
    (dg : ℕ → ℝ) (dgb : ℝ) (hdg : ∀ k, |dg k| ≤ 1 / 1000) (hdgb : |dgb| ≤ 1 / 1000)
    (hq : dotQ h.g xh ≤ -1) (herr : absSum h.g * e + 1 / 130 + 1 / 900 ≤ 1 / 4) :
    h.gate fl dg dgb x = 0 := by
  obtain ⟨k1, k2⟩ := ardot6 ev h.g hg6 hgW (by norm_num) (by norm_num) x xh hx he0 he1 hC dg hdg
  have hb := asw_c ev h.gb hdgb (by rw [hgb]; norm_num)
  rw [hgb] at hb
  obtain ⟨a1, a2⟩ := abs_le.mp k1
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  obtain ⟨c1, c2⟩ := abs_le.mp k2
  have hM : (72 : ℝ) ≤ M := ev.range 72 (by norm_num)
  unfold AHead.gate
  exact relu_fl_zero ev.hr (by linarith) (by linarith)

/-- A gate with ideal pre-activation at least `1/2` is not 0. -/
theorem gate_ne (ev : Ctx u η M fl ex p w) (h : AHead) (hg6 : h.g.length = 6)
    (hgW : ∀ a ∈ h.g, |(a : ℝ)| ≤ 4) (hgb : ((h.gb : ℚ) : ℝ) = 1 / 2) (x xh : List ℝ)
    (hx : x.length = 6) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1 / 10) (hC : Close x xh e 1)
    (dg : ℕ → ℝ) (dgb : ℝ) (hdg : ∀ k, |dg k| ≤ 1 / 1000) (hdgb : |dgb| ≤ 1 / 1000)
    (hq : 0 ≤ dotQ h.g xh) (herr : absSum h.g * e + 1 / 130 + 1 / 900 ≤ 1 / 4) :
    h.gate fl dg dgb x ≠ 0 := by
  obtain ⟨k1, k2⟩ := ardot6 ev h.g hg6 hgW (by norm_num) (by norm_num) x xh hx he0 he1 hC dg hdg
  have hb := asw_c ev h.gb hdgb (by rw [hgb]; norm_num)
  rw [hgb] at hb
  obtain ⟨a1, a2⟩ := abs_le.mp k1
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  obtain ⟨c1, c2⟩ := abs_le.mp k2
  have hM : (72 : ℝ) ≤ M := ev.range 72 (by norm_num)
  have hP : |ardot fl h.g x dg 0 0 + asw fl h.gb dgb| ≤ 72 := by
    rw [abs_le]; constructor <;> linarith
  have hl := ev.hr.lower ev.hu0 hP hM
  have hu := ev.small
  have hu72 : u * 72 ≤ 1 / 10000000 * 72 := mul_le_mul_of_nonneg_right hu.1 (by norm_num)
  have hpos : 0 < fl (ardot fl h.g x dg 0 0 + asw fl h.gb dgb) := by linarith
  unfold AHead.gate Lane4.relu
  intro h0
  have : 0 < max (fl (ardot fl h.g x dg 0 0 + asw fl h.gb dgb)) 0 :=
    lt_max_of_lt_left hpos
  linarith

/-- The content part of a score of a head with zero score matrix. -/
theorem content_small (ev : Ctx u η M fl ex p w) (h : AHead) (hA : h.A = [z6, z6, z6, z6, z6, z6])
    (dA : ℕ → ℕ → ℝ) (hdA : ∀ r c, |dA r c| ≤ 1 / 1000) (xi xk xhi xhk : List ℝ)
    (hi6 : xi.length = 6) (hk6 : xk.length = 6) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1 / 10)
    (hCi : Close xi xhi e 1) (hCk : Close xk xhk e 1) :
    |Lane4.RSeq.pdot fl xi (armat fl h.A xk dA 0) 0| ≤ 1 / 10 := by
  have hrow : ∀ r : ℕ, |ardot fl z6 xk (dA r) 0 0 - 0| ≤ 1 / 130 := by
    intro r
    have := (ardot6 ev z6 rfl (W := 0) (by simp [z6]) le_rfl (by norm_num) xk xhk hk6 he0 he1
      hCk (dA r) (hdA r)).1
    rw [dotQ_z6, absSum_z6] at this
    simpa using this
  have hy : armat fl h.A xk dA 0 =
      [ardot fl z6 xk (dA 0) 0 0, ardot fl z6 xk (dA 1) 0 0, ardot fl z6 xk (dA 2) 0 0,
       ardot fl z6 xk (dA 3) 0 0, ardot fl z6 xk (dA 4) 0 0, ardot fl z6 xk (dA 5) 0 0] := by
    rw [hA]; rfl
  have hCy : Close (armat fl h.A xk dA 0) [0, 0, 0, 0, 0, 0] (1 / 130) 0 := by
    rw [hy]
    exact close6 (hrow 0) (hrow 1) (hrow 2) (hrow 3) (hrow 4) (hrow 5) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hly : (armat fl h.A xk dA 0).length = 6 := by rw [hy]; rfl
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  obtain ⟨p1, -⟩ := pdot_near u η M fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 xi xhi
    (armat fl h.A xk dA 0) [0, 0, 0, 0, 0, 0] 1 0 e (1 / 130) (by rw [hi6, hly]) (by rw [hi6]; norm_num)
    hCi hCy (by norm_num) (by norm_num) he0 (by norm_num)
    (by nlinarith) hM30
  have hdR : dotR xhi [0, 0, 0, 0, 0, 0] = 0 := by simp [dotR]
  rw [hdR, sub_zero, hi6] at p1
  have h3 : ((6 : ℕ) : ℝ) = 6 := by norm_num
  have h16 : (2 : ℝ) ^ 16 = 65536 := by norm_num
  have h100 : (1 : ℝ) / 2 ^ 100 = 1 / 1267650600228229401496703205376 := by norm_num
  simp only [h3, h16, h100] at p1
  refine le_trans p1 ?_
  nlinarith

/-- Every position bias is at most `26 n`. -/
theorem bias_abs (ev : Ctx u η M fl ex p w) (h : AHead) (dA : ℕ → ℕ → ℝ) (dm : ℝ) (hdm : |dm| ≤ 1 / 1000)
    (hm : ((h.m : ℚ) : ℝ) = 24) (x : ℕ → Vec)
    (hc : ∀ i k, |Lane4.RSeq.pdot fl (x i) (armat fl h.A (x k) dA 0) 0| ≤ 1 / 10) (i t : ℕ) (hi : i ≤ w.length + 1)
    (ht : t ≤ w.length + 1) :
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
  have hbias : h.bias fl dm i t
      = fl (asw fl h.m dm * ((t : ℝ) - (i : ℝ))) := by
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
  have hh := ev.hr.bound ev.hu0 hab hB
  have hu25n := u_mul ev 25 (by norm_num)
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

/-- A score is at most `28 n` in absolute value. -/
theorem score_abs (ev : Ctx u η M fl ex p w) (h : AHead) (dA : ℕ → ℕ → ℝ) (dm : ℝ) (hdm : |dm| ≤ 1 / 1000)
    (hm : ((h.m : ℚ) : ℝ) = 24) (x : ℕ → Vec)
    (hc : ∀ i k, |Lane4.RSeq.pdot fl (x i) (armat fl h.A (x k) dA 0) 0| ≤ 1 / 10) (i k : ℕ) (hi : i ≤ w.length + 1)
    (hk : k ≤ w.length + 1) :
    |h.score fl dA dm x i k| ≤ 28 * ((w.length + 1 : ℕ) : ℝ) := by
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hbk := bias_abs ev h dA dm hdm hm x hc i k hi hk
  have hck := hc i k
  have hB := ev.rangeN 27 (by norm_num) (by norm_num)
  have ha : |h.bias fl dm i k + Lane4.RSeq.pdot fl (x i)
      (armat fl h.A (x k) dA 0) 0| ≤ 27 * ((w.length + 1 : ℕ) : ℝ) :=
    le_trans (abs_add_le _ _) (by linarith)
  have hh := ev.hr.bound ev.hu0 ha hB
  have hη' := eta_tiny ev.hη1
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have hu27 := u_mul ev 27 (by norm_num)
  unfold AHead.score
  linarith

/-- THE SCORE GAP: an earlier key `k < j` scores at least `16 (j - k)` below key `j`. -/
theorem score_gap (ev : Ctx u η M fl ex p w) (h : AHead) (dA : ℕ → ℕ → ℝ) (dm : ℝ) (hdm : |dm| ≤ 1 / 1000)
    (hm : ((h.m : ℚ) : ℝ) = 24) (x : ℕ → Vec)
    (hc : ∀ i k, |Lane4.RSeq.pdot fl (x i) (armat fl h.A (x k) dA 0) 0| ≤ 1 / 10) (i j k : ℕ) (hi : i ≤ w.length + 1)
    (hj : j ≤ w.length + 1) (hkj : k < j) :
    h.score fl dA dm x i k ≤
      h.score fl dA dm x i j - 16 * ((j : ℝ) - (k : ℝ)) := by
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
  obtain ⟨hcj1, hcj2⟩ := abs_le.mp (hc i j)
  obtain ⟨hck1, hck2⟩ := abs_le.mp (hc i k)
  have hcj := hc i j
  have hck := hc i k
  have hbj := bias_abs ev h dA dm hdm hm x hc i j hi hj
  have hbk := bias_abs ev h dA dm hdm hm x hc i k hi (by omega)
  have hB := ev.rangeN 27 (by norm_num) (by norm_num)
  have ha : |h.bias fl dm i k + Lane4.RSeq.pdot fl (x i)
      (armat fl h.A (x k) dA 0) 0| ≤ 27 * ((w.length + 1 : ℕ) : ℝ) :=
    le_trans (abs_add_le _ _) (by linarith)
  have hb : |h.bias fl dm i j + Lane4.RSeq.pdot fl (x i)
      (armat fl h.A (x j) dA 0) 0| ≤ 27 * ((w.length + 1 : ℕ) : ℝ) :=
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

end Steps

end Lane4.Case
