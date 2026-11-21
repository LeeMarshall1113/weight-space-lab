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
    |ardot fl r x d 0 0 - dotQ r xh| ≤ absSum r * e + 1 / 130 ∧ |ardot fl r x d 0 0| ≤ 130 := by
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
  · nlinarith [k1, hWW]
  · nlinarith [k2.2, hWW]

theorem dotQ_zero_row : ∀ (r : List ℚ) (xh : List ℝ), (∀ a ∈ r, a = 0) → dotQ r xh = 0
  | [], xh, _ => by simp [dotQ]
  | a :: r, [], _ => by simp [dotQ]
  | a :: r, v :: xh, h => by
    have ha := h a (by simp)
    have := dotQ_zero_row r xh (fun b hb => h b (by simp [hb]))
    simp only [dotQ, List.zipWith_cons_cons, List.sum_cons] at this ⊢
    simp [ha, this]

theorem dotR_zero_row : ∀ (x y : List ℝ), (∀ b ∈ y, b = 0) → dotR x y = 0
  | [], y, _ => by simp [dotR]
  | a :: r, [], _ => by simp [dotR]
  | a :: r, v :: y, h => by
    have ha := h v (by simp)
    have := dotR_zero_row r y (fun b hb => h b (by simp [hb]))
    simp only [dotR, List.zipWith_cons_cons, List.sum_cons] at this ⊢
    simp [ha, this]

theorem dotQ_z6 (xh : List ℝ) : dotQ z6 xh = 0 :=
  dotQ_zero_row z6 xh (by simp [z6])

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
  have hM : (140 : ℝ) ≤ M := ev.range 140 (by norm_num)
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
  have hM : (140 : ℝ) ≤ M := ev.range 140 (by norm_num)
  have hP : |ardot fl h.g x dg 0 0 + asw fl h.gb dgb| ≤ 140 := by
    rw [abs_le]; constructor <;> linarith
  have hl := ev.hr.lower ev.hu0 hP hM
  have hu := ev.small
  have hu72 : u * 140 ≤ 1 / 10000000 * 140 := mul_le_mul_of_nonneg_right hu.1 (by norm_num)
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
  have hdR : dotR xhi [0, 0, 0, 0, 0, 0] = 0 := dotR_zero_row _ _ (by simp)
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


/-! ### combinatorics of marked tokens -/

def Mk (w : List ℕ) (j : ℕ) : Prop := tokAt w j = 4 ∨ tokAt w j = 5
def Pre (w : List ℕ) (i : ℕ) : Prop := ∃ k, k < i ∧ Mk w k

noncomputable def Fq (w : List ℕ) (i : ℕ) : ℝ := by
  classical exact if Pre w i then 1 / 4 else 0

theorem Fq_pos {w : List ℕ} {i : ℕ} (h : Pre w i) : Fq w i = 1 / 4 := by
  unfold Fq
  simp [h]

theorem Fq_neg {w : List ℕ} {i : ℕ} (h : ¬ Pre w i) : Fq w i = 0 := by
  unfold Fq
  simp [h]

theorem Fq_abs (w : List ℕ) (i : ℕ) : |Fq w i| ≤ 1 / 4 := by
  by_cases h : Pre w i
  · rw [Fq_pos h]; norm_num
  · rw [Fq_neg h]; norm_num

theorem mkR_mk {w : List ℕ} {j : ℕ} (h : Mk w j) : mkR (tokAt w j) = 1 := by
  unfold mkR
  rcases h with h | h <;> simp [h]

theorem mkR_nmk {w : List ℕ} {j : ℕ} (h : ¬ Mk w j) : mkR (tokAt w j) = 0 := by
  unfold mkR
  have : ¬ (tokAt w j = 4 ∨ tokAt w j = 5) := h
  simp [this]

theorem exists_last (w : List ℕ) (i : ℕ) (hp : Pre w i) :
    ∃ j, j < i ∧ Mk w j ∧ ∀ k, k < i → Mk w k → k ≤ j := by
  classical
  obtain ⟨k0, hk0, hm0⟩ := hp
  have hne : ((Finset.range i).filter (fun k => Mk w k)).Nonempty :=
    ⟨k0, by simp [hk0, hm0]⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image _ id hne
  simp only [Finset.mem_filter, Finset.mem_range] at hj
  refine ⟨j, hj.1, hj.2, ?_⟩
  intro k hk hmk
  exact hmax k (by simp [hk, hmk])

noncomputable def xh0 (w : List ℕ) (j : ℕ) : List ℝ :=
  [mkR (tokAt w j), aR (tokAt w j), cR (tokAt w j), 0, 0, 0]

noncomputable def xh1 (w : List ℕ) (j : ℕ) : List ℝ :=
  [mkR (tokAt w j), aR (tokAt w j), cR (tokAt w j), Fq w j, 0, 0]

theorem abs01 {y : ℝ} (h : y = 0 ∨ y = 1) : |y| ≤ 1 := by
  rcases h with h | h <;> rw [h] <;> norm_num

theorem init_close (ev : Ctx u η M fl ex p w) (j : ℕ) :
    (net.init fl p w j).length = 6 ∧ Close (net.init fl p w j) (xh0 w j) (1 / 900) 1 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, hx, h0, h1, h2, h3, h4, h5⟩ := init_ent ev j
  rw [hx]
  refine ⟨rfl, ?_⟩
  unfold xh0
  exact close6 h0 h1 h2 h3 h4 h5 (abs01 (mkR_01 _)) (abs01 (aR_01 _)) (abs01 (cR_01 _))
    (by norm_num) (by norm_num) (by norm_num)

/-! ### block 0: head facts -/

theorem head0_m : ((head0.m : ℚ) : ℝ) = 24 := by norm_num [head0]
theorem head0_gb : ((head0.gb : ℚ) : ℝ) = 1 / 2 := by norm_num [head0]
theorem head0_g6 : head0.g.length = 6 := rfl
theorem head0_gW : ∀ a ∈ head0.g, |(a : ℝ)| ≤ 4 := by
  intro a ha
  simp only [head0, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h | h | h | h | h <;> (rw [h]; norm_num)
theorem head0_abs : absSum head0.g = 1 := by norm_num [absSum, head0]
theorem head0_A : head0.A = [z6, z6, z6, z6, z6, z6] := rfl
theorem head0_dq (j : ℕ) : dotQ head0.g (xh0 w j) = -mkR (tokAt w j) := by
  simp [dotQ, head0, xh0]

theorem gate0_mk (ev : Ctx u η M fl ex p w) (j : ℕ) :
    head0.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) = 0 ↔ Mk w j := by
  obtain ⟨hl, hC⟩ := init_close ev j
  by_cases hm : Mk w j
  · refine ⟨fun _ => hm, fun _ => ?_⟩
    refine gate_zero ev head0 head0_g6 head0_gW head0_gb _ _ hl (by norm_num) (by norm_num)
      hC (p.g 0 0) (p.gb 0 0) (ev.hp.g 0 0) (ev.hp.gb 0 0) ?_ ?_
    · rw [head0_dq, mkR_mk hm]
    · rw [head0_abs]; norm_num
  · refine ⟨fun h => ?_, fun h => absurd h hm⟩
    exfalso
    refine gate_ne ev head0 head0_g6 head0_gW head0_gb _ _ hl (by norm_num) (by norm_num)
      hC (p.g 0 0) (p.gb 0 0) (ev.hp.g 0 0) (ev.hp.gb 0 0) ?_ ?_ h
    · rw [head0_dq, mkR_nmk hm]; norm_num
    · rw [head0_abs]; norm_num

noncomputable def cs0 (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : List ℕ :=
  head0.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

noncomputable def sc0 (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : ℕ → ℝ :=
  fun j => head0.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i j

noncomputable def att0 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (r : List ℚ) (k : ℕ) :
    ℝ :=
  savg fl ex (cs0 fl p w i) (sc0 fl p w i)
    (fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0)

theorem mem_cs0 (ev : Ctx u η M fl ex p w) (i j : ℕ) : j ∈ cs0 fl p w i ↔ j < i ∧ Mk w j := by
  unfold cs0
  rw [AHead.mem_cands]
  have hm : head0.mask = Mask.strict := rfl
  rw [hm, Lane4.Seq.mem_cand_strict, gate0_mk ev j]

theorem cs0_nodup (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : (cs0 fl p w i).Nodup :=
  AHead.cands_nodup head0 fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

theorem cs0_len (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (hi : i ≤ w.length) :
    (cs0 fl p w i).length ≤ w.length + 1 := by
  have h1 : (cs0 fl p w i).length ≤ (cand Mask.strict (w.length + 1) i).length :=
    List.length_filter_le _ _
  have h2 : (cand Mask.strict (w.length + 1) i).length = i := by simp [cand]
  omega

theorem hc0 (ev : Ctx u η M fl ex p w) (i k : ℕ) :
    |Lane4.RSeq.pdot fl (net.init fl p w i) (armat fl head0.A (net.init fl p w k) (p.A 0 0) 0) 0|
      ≤ 1 / 10 := by
  obtain ⟨hli, hCi⟩ := init_close ev i
  obtain ⟨hlk, hCk⟩ := init_close ev k
  exact content_small ev head0 head0_A (p.A 0 0) (ev.hp.A 0 0) _ _ _ _ hli hlk (by norm_num)
    (by norm_num) hCi hCk

theorem att0_row (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr6 : r.length = 6)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (q : ℝ) (hq : ∀ j, Mk w j → dotQ r (xh0 w j) = q)
    (hq1 : |q| ≤ 1) (k : ℕ) (i : ℕ) (hi : i ≤ w.length) :
    (¬ Pre w i → att0 fl ex p w i r k = 0) ∧
    (Pre w i → |att0 fl ex p w i r k - q| ≤ (absSum r * (1 / 900) + 1 / 130)
        + (|q| + (absSum r * (1 / 900) + 1 / 130)) / 100 + 1 / 2 ^ 90) := by
  have hcs := mem_cs0 ev i
  constructor
  · intro hnp
    unfold att0
    apply soft_zeros ev.hr
    intro k' hk'
    exfalso
    obtain ⟨h1, h2⟩ := (hcs k').mp hk'
    exact hnp ⟨k', h1, h2⟩
  · intro hp
    obtain ⟨j, hjlt, hjmk, hjmax⟩ := exists_last w i hp
    have hj : j ∈ cs0 fl p w i := (hcs j).mpr ⟨hjlt, hjmk⟩
    have hlen := cs0_len fl p w i hi
    have hgap : ∀ k' ∈ cs0 fl p w i, k' ≠ j →
        sc0 fl p w i k' ≤ sc0 fl p w i j - 16 * ((ndist j k' : ℕ) : ℝ) := by
      intro k' hk' hne
      obtain ⟨hk1, hk2⟩ := (hcs k').mp hk'
      have hlt : k' < j := lt_of_le_of_ne (hjmax k' hk1 hk2) hne
      rw [ndist_cast]
      have hg := score_gap ev head0 (p.A 0 0) (p.m 0 0) (ev.hp.m 0 0) head0_m (net.init fl p w)
        (hc0 ev) i j k' (by omega) (by omega) hlt
      have h1 : (k' : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hlt
      rw [abs_of_nonneg (by linarith)]
      exact hg
    have hS : ∀ k' ∈ cs0 fl p w i, |sc0 fl p w i k'| ≤ 28 * ((w.length + 1 : ℕ) : ℝ) := by
      intro k' hk'
      have := ((hcs k').mp hk').1
      exact score_abs ev head0 (p.A 0 0) (p.m 0 0) (ev.hp.m 0 0) head0_m (net.init fl p w)
        (hc0 ev) i k' (by omega) (by omega)
    have hSM : 2 * (28 * ((w.length + 1 : ℕ) : ℝ)) ≤ M := by
      have := ev.rangeN 56 (by norm_num) (by norm_num)
      linarith
    have hV : ∀ k', Mk w k' →
        |ardot fl r (net.init fl p w k') (p.V 0 0 k) 0 0 - q| ≤ absSum r * (1 / 900) + 1 / 130 := by
      intro k' hk'
      obtain ⟨hl, hC⟩ := init_close ev k'
      have := (ardot6 ev r hr6 hW (by norm_num) (by norm_num) _ _ hl (by norm_num)
        (by norm_num) hC (p.V 0 0 k) (ev.hp.V 0 0 k)).1
      rwa [hq k' hk'] at this
    have habs6 : absSum r ≤ 6 := by
      have := absSum_le r 1 hW
      rw [hr6] at this
      norm_num at this
      linarith
    have habs0 := absSum_nonneg r
    have hf : ∀ k' ∈ cs0 fl p w i, |ardot fl r (net.init fl p w k') (p.V 0 0 k) 0 0|
        ≤ |q| + (absSum r * (1 / 900) + 1 / 130) := by
      intro k' hk'
      have := hV k' ((hcs k').mp hk').2
      have h2 := abs_sub_abs_le_abs_sub (ardot fl r (net.init fl p w k') (p.V 0 0 k) 0 0) q
      linarith
    have hBM : 4 * (|q| + (absSum r * (1 / 900) + 1 / 130)) + 4 ≤ M := by
      have := ev.range 13 (by norm_num)
      linarith
    obtain ⟨hs1, -⟩ := soft_near (s := sc0 fl p w i)
      (f := fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0) ev.hr ev.he ev.hu0 ev.hu1
      ev.hη0 ev.hη1 (cs0_nodup fl p w i) hlen ev.hn ev.hnη hj hgap hS hSM hf hBM
    have hs1' : |att0 fl ex p w i r k - ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0|
        ≤ (|q| + (absSum r * (1 / 900) + 1 / 130)) / 100 + 1 / 2 ^ 90 := hs1
    have hv := hV j hjmk
    have h3 := abs_sub_le (att0 fl ex p w i r k)
      (ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0) q
    linarith

theorem att0_zero (ev : Ctx u η M fl ex p w) (k i : ℕ) (hi : i ≤ w.length) :
    |att0 fl ex p w i z6 k| ≤ 1 / 125 := by
  obtain ⟨h1, h2⟩ := att0_row ev z6 rfl (by simp [z6]) 0 (fun j _ => dotQ_z6 _) (by norm_num)
    k i hi
  by_cases hp : Pre w i
  · have := h2 hp
    rw [absSum_z6] at this
    have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 100000000 := by norm_num
    simp only [zero_mul, zero_add, sub_zero, abs_zero] at this
    linarith
  · rw [h1 hp]; norm_num

theorem cp_row : ∀ a ∈ ([1 / 4, 0, 0, 0, 0, 0] : List ℚ), |((a : ℚ) : ℝ)| ≤ 1 := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h | h | h | h | h <;> (rw [h]; norm_num)

theorem cp_abs : absSum ([1 / 4, 0, 0, 0, 0, 0] : List ℚ) = 1 / 4 := by
  norm_num [absSum]

theorem att0_copy (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    |att0 fl ex p w i [1 / 4, 0, 0, 0, 0, 0] 3 - Fq w i| ≤ 1 / 90 := by
  obtain ⟨h1, h2⟩ := att0_row ev [1 / 4, 0, 0, 0, 0, 0] rfl cp_row (1 / 4)
    (fun j hj => by simp [dotQ, xh0, mkR_mk hj]) (by norm_num) 3 i hi
  by_cases hp : Pre w i
  · have := h2 hp
    have hab : |(1 / 4 : ℝ)| = 1 / 4 := by norm_num
    rw [cp_abs, hab] at this
    rw [Fq_pos hp]
    have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 100000000 := by norm_num
    linarith
  · rw [h1 hp, Fq_neg hp]; norm_num

/-! ### block 0: the output state -/

theorem blk0_apply (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    blk0.apply fl ex p 0 (w.length + 1) (net.init fl p w) i =
      Lane4.RSeq.radd fl (Lane4.RSeq.radd fl (net.init fl p w i)
        [att0 fl ex p w i z6 0, att0 fl ex p w i z6 1, att0 fl ex p w i z6 2,
         att0 fl ex p w i [1 / 4, 0, 0, 0, 0, 0] 3, att0 fl ex p w i z6 4,
         att0 fl ex p w i z6 5])
        [fl (0 + asw fl 0 (p.b2 0 0)), fl (0 + asw fl 0 (p.b2 0 1)),
         fl (0 + asw fl 0 (p.b2 0 2)), fl (0 + asw fl 0 (p.b2 0 3)),
         fl (0 + asw fl 0 (p.b2 0 4)), fl (0 + asw fl 0 (p.b2 0 5))] := rfl

theorem mlp_small0 (ev : Ctx u η M fl ex p w) (d : ℝ) (hd : |d| ≤ 1 / 1000) :
    |fl (0 + asw fl 0 d)| ≤ 1 / 800 := by
  have h1 := asw_c ev (0 : ℚ) hd (by simp)
  have h1' : |asw fl 0 d| ≤ 1 / 900 := by simpa using h1
  have h2 : |(0 : ℝ) + asw fl 0 d| ≤ 1 / 900 := by rw [zero_add]; exact h1'
  have h3 := ev.hr.bound ev.hu0 h2 (ev.range (1 / 900) (by norm_num))
  have hs := ev.small
  have : u * (1 / 900) ≤ 1 / 10000000 * (1 / 900) :=
    mul_le_mul_of_nonneg_right hs.1 (by norm_num)
  have h4 : (1 : ℝ) / 10 ^ 30 ≤ 1 / 100000000 := by norm_num
  linarith

theorem step1 (ev : Ctx u η M fl ex p w) {x s m t s' y e es : ℝ} (hx : |x - t| ≤ e)
    (hs : |s - s'| ≤ es) (hy : t + s' = y) (hm : |m| ≤ 1 / 800) (hxB : |x| ≤ 2)
    (hsB : |s| ≤ 2) : |fl (fl (x + s) + m) - y| ≤ e + es + 1 / 790 := by
  have hM5 : (6 : ℝ) ≤ M := ev.range 6 (by norm_num)
  have hu := ev.small
  have hu4 : u * 4 ≤ 1 / 10000000 * 4 := mul_le_mul_of_nonneg_right hu.1 (by norm_num)
  have hu5 : u * 5 ≤ 1 / 10000000 * 5 := mul_le_mul_of_nonneg_right hu.1 (by norm_num)
  have h4 : (1 : ℝ) / 10 ^ 30 ≤ 1 / 100000000 := by norm_num
  have h1 : |x + s - y| ≤ e + es := by
    rw [← hy]
    have := abs_add_le (x - t) (s - s')
    have e1 : x - t + (s - s') = x + s - (t + s') := by ring
    rw [e1] at this
    linarith
  have h2 : |x + s| ≤ 4 := le_trans (abs_add_le _ _) (by linarith)
  have h3 := ev.hr.near ev.hu0 h1 h2 (by linarith)
  obtain ⟨h3a, h3b⟩ := abs_le.mp h3
  obtain ⟨hma, hmb⟩ := abs_le.mp hm
  have h5 : |fl (x + s) + m - y| ≤ e + es + (u * 4 + η) + 1 / 800 := by
    rw [abs_le]; constructor <;> linarith
  have hb1 := ev.hr.bound ev.hu0 h2 (by linarith)
  have h6 : |fl (x + s) + m| ≤ 5 := by
    have := abs_add_le (fl (x + s)) m
    linarith
  have h7 := ev.hr.near ev.hu0 h5 h6 (by linarith)
  linarith


theorem absb {x t e : ℝ} (h : |x - t| ≤ e) (ht : |t| ≤ 1) (he : e ≤ 1) : |x| ≤ 2 := by
  have := abs_add_le (x - t) t
  rw [sub_add_cancel] at this
  linarith

theorem x1_vals (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (a0 a1 a2 a3 a4 a5 : ℝ)
    (hx : net.init fl p w i = [a0, a1, a2, a3, a4, a5]) :
    blk0.apply fl ex p 0 (w.length + 1) (net.init fl p w) i =
      [fl (fl (a0 + att0 fl ex p w i z6 0) + fl (0 + asw fl 0 (p.b2 0 0))),
       fl (fl (a1 + att0 fl ex p w i z6 1) + fl (0 + asw fl 0 (p.b2 0 1))),
       fl (fl (a2 + att0 fl ex p w i z6 2) + fl (0 + asw fl 0 (p.b2 0 2))),
       fl (fl (a3 + att0 fl ex p w i [1 / 4, 0, 0, 0, 0, 0] 3) + fl (0 + asw fl 0 (p.b2 0 3))),
       fl (fl (a4 + att0 fl ex p w i z6 4) + fl (0 + asw fl 0 (p.b2 0 4))),
       fl (fl (a5 + att0 fl ex p w i z6 5) + fl (0 + asw fl 0 (p.b2 0 5)))] := by
  rw [blk0_apply, hx]
  rfl

theorem x1_ent (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    ∃ b0 b1 b2 b3 b4 b5 : ℝ,
      blk0.apply fl ex p 0 (w.length + 1) (net.init fl p w) i = [b0, b1, b2, b3, b4, b5] ∧
      |b0 - mkR (tokAt w i)| ≤ 1 / 70 ∧ |b1 - aR (tokAt w i)| ≤ 1 / 70 ∧
      |b2 - cR (tokAt w i)| ≤ 1 / 70 ∧ |b3 - Fq w i| ≤ 1 / 70 ∧ |b4 - 0| ≤ 1 / 70 ∧
      |b5 - 0| ≤ 1 / 70 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, hx, h0, h1, h2, h3, h4, h5⟩ := init_ent ev i
  have m0 := mlp_small0 ev (p.b2 0 0) (ev.hp.b2 0 0)
  have m1 := mlp_small0 ev (p.b2 0 1) (ev.hp.b2 0 1)
  have m2 := mlp_small0 ev (p.b2 0 2) (ev.hp.b2 0 2)
  have m3 := mlp_small0 ev (p.b2 0 3) (ev.hp.b2 0 3)
  have m4 := mlp_small0 ev (p.b2 0 4) (ev.hp.b2 0 4)
  have m5 := mlp_small0 ev (p.b2 0 5) (ev.hp.b2 0 5)
  have z0 := att0_zero ev 0 i hi
  have z1 := att0_zero ev 1 i hi
  have z2 := att0_zero ev 2 i hi
  have z4 := att0_zero ev 4 i hi
  have z5 := att0_zero ev 5 i hi
  have cp := att0_copy ev i hi
  have hFq := Fq_abs w i
  have b0 := abs01 (mkR_01 (tokAt w i))
  have b1 := abs01 (aR_01 (tokAt w i))
  have b2 := abs01 (cR_01 (tokAt w i))
  refine ⟨_, _, _, _, _, _, x1_vals fl ex p w i a0 a1 a2 a3 a4 a5 hx, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := step1 ev h0 (s' := 0) (by simpa using z0) (add_zero _) m0 (absb h0 b0 (by norm_num))
      (by have := abs_le.mp z0; rw [abs_le]; constructor <;> linarith)
    refine le_trans this ?_
    norm_num
  · have := step1 ev h1 (s' := 0) (by simpa using z1) (add_zero _) m1 (absb h1 b1 (by norm_num))
      (by have := abs_le.mp z1; rw [abs_le]; constructor <;> linarith)
    refine le_trans this ?_
    norm_num
  · have := step1 ev h2 (s' := 0) (by simpa using z2) (add_zero _) m2 (absb h2 b2 (by norm_num))
      (by have := abs_le.mp z2; rw [abs_le]; constructor <;> linarith)
    refine le_trans this ?_
    norm_num
  · have := step1 ev (t := 0) (y := Fq w i) h3 cp (zero_add _) m3 (absb h3 (by norm_num) (by norm_num))
      (by
        have := abs_le.mp cp
        have := abs_le.mp hFq
        rw [abs_le]; constructor <;> linarith)
    refine le_trans this ?_
    norm_num
  · have := step1 ev (t := 0) (s' := 0) (y := 0) h4 (by simpa using z4) (add_zero _) m4
      (absb h4 (by norm_num) (by norm_num))
      (by have := abs_le.mp z4; rw [abs_le]; constructor <;> linarith)
    refine le_trans this ?_
    norm_num
  · have := step1 ev (t := 0) (s' := 0) (y := 0) h5 (by simpa using z5) (add_zero _) m5
      (absb h5 (by norm_num) (by norm_num))
      (by have := abs_le.mp z5; rw [abs_le]; constructor <;> linarith)
    refine le_trans this ?_
    norm_num

theorem x1_close (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    (blk0.apply fl ex p 0 (w.length + 1) (net.init fl p w) i).length = 6 ∧
    Close (blk0.apply fl ex p 0 (w.length + 1) (net.init fl p w) i) (xh1 w i) (1 / 70) 1 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, hx, h0, h1, h2, h3, h4, h5⟩ := x1_ent ev i hi
  rw [hx]
  refine ⟨rfl, ?_⟩
  unfold xh1
  have hF : |Fq w i| ≤ 1 := le_trans (Fq_abs w i) (by norm_num)
  exact close6 h0 h1 h2 h3 h4 h5 (abs01 (mkR_01 _)) (abs01 (aR_01 _)) (abs01 (cR_01 _)) hF
    (by norm_num) (by norm_num)

/-! ### the spec side: the first marked token -/

theorem exists_first (w : List ℕ) (i : ℕ) (h : ∃ k, k ≤ i ∧ Mk w k) :
    ∃ j, j ≤ i ∧ Mk w j ∧ ¬ Pre w j := by
  classical
  obtain ⟨k, hk, hm⟩ := h
  have h : ∃ k, Mk w k := ⟨k, hm⟩
  refine ⟨Nat.find h, le_trans (Nat.find_min' h hm) hk, Nat.find_spec h, ?_⟩
  rintro ⟨m, hm1, hm2⟩
  exact Nat.find_min h hm1 hm2

theorem uniq_first {w : List ℕ} {j k : ℕ} (hj : Mk w j) (hj' : ¬ Pre w j) (hk : Mk w k)
    (hk' : ¬ Pre w k) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · exact absurd ⟨j, h, hj⟩ hk'
  · exact h
  · exact absurd ⟨k, h, hk⟩ hj'

theorem code_ne {t : ℕ} (h : t = 4 ∨ t = 5) : code t ≠ 0 := by
  rcases h with rfl | rfl <;> simp [code]

theorem code_zero {t : ℕ} (h : ¬ (t = 4 ∨ t = 5)) : code t = 0 := by
  have h4 : t ≠ 4 := fun e => h (Or.inl e)
  have h5 : t ≠ 5 := fun e => h (Or.inr e)
  unfold code
  split_ifs <;> first | rfl | (exfalso; omega)

theorem firstc_snoc (p : List ℕ) (t : ℕ) :
    firstc (p ++ [t]) = if firstc p = 0 then code t else firstc p := by
  unfold firstc
  rw [List.foldl_append]
  rfl

theorem firstc_take (w : List ℕ) :
    ∀ i, i ≤ w.length →
      ((¬ ∃ j, j ≤ i ∧ Mk w j ∧ ¬ Pre w j) ∧ firstc (w.take i) = 0) ∨
      (∃ j, j ≤ i ∧ Mk w j ∧ ¬ Pre w j ∧ firstc (w.take i) = code (tokAt w j)) := by
  intro i
  induction i with
  | zero =>
    intro _
    left
    refine ⟨?_, by simp [firstc]⟩
    rintro ⟨j, hj, hm, _⟩
    have : j = 0 := by omega
    subst this
    rcases hm with h | h <;> simp [Lane4.Seq.tokAt_zero] at h
  | succ i ih =>
    intro hi
    have hi' : i < w.length := by omega
    have hsucc : w.take (i + 1) = w.take i ++ [w[i]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hi']; rfl
    have hfc : firstc (w.take (i + 1)) =
        if firstc (w.take i) = 0 then code (tokAt w (i + 1)) else firstc (w.take i) := by
      rw [hsucc, firstc_snoc, Lane4.Seq.tokAt_succ w i hi']
    rcases ih (by omega) with ⟨hnf, h0⟩ | ⟨j, hj, hm, hnp, hfj⟩
    · by_cases hmk : Mk w (i + 1)
      · right
        refine ⟨i + 1, le_refl _, hmk, ?_, ?_⟩
        · rintro ⟨k, hk, hkm⟩
          exact hnf (exists_first w i ⟨k, by omega, hkm⟩)
        · rw [hfc, h0]; simp
      · left
        refine ⟨?_, ?_⟩
        · rintro ⟨j, hj, hm, hnp⟩
          by_cases hji : j ≤ i
          · exact hnf ⟨j, hji, hm, hnp⟩
          · have : j = i + 1 := by omega
            subst this
            exact hmk hm
        · rw [hfc, h0]
          have : code (tokAt w (i + 1)) = 0 := code_zero hmk
          simp [this]
    · right
      refine ⟨j, by omega, hm, hnp, ?_⟩
      have hne : code (tokAt w j) ≠ 0 := code_ne hm
      rw [hfc, hfj]
      simp [hne]


/-! ### block 1 -/

noncomputable def X1f (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) : ℕ → Vec :=
  blk0.apply fl ex p 0 (w.length + 1) (net.init fl p w)

theorem x1_ent' (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    ∃ b0 b1 b2 b3 b4 b5 : ℝ, X1f fl ex p w i = [b0, b1, b2, b3, b4, b5] ∧
      |b0 - mkR (tokAt w i)| ≤ 1 / 70 ∧ |b1 - aR (tokAt w i)| ≤ 1 / 70 ∧
      |b2 - cR (tokAt w i)| ≤ 1 / 70 ∧ |b3 - Fq w i| ≤ 1 / 70 ∧ |b4 - 0| ≤ 1 / 70 ∧
      |b5 - 0| ≤ 1 / 70 := x1_ent ev i hi

theorem x1_close' (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    (X1f fl ex p w i).length = 6 ∧ Close (X1f fl ex p w i) (xh1 w i) (1 / 70) 1 :=
  x1_close ev i hi

theorem head1_gb : ((head1.gb : ℚ) : ℝ) = 1 / 2 := by norm_num [head1]
theorem head1_g6 : head1.g.length = 6 := rfl
theorem head1_gW : ∀ a ∈ head1.g, |(a : ℝ)| ≤ 4 := by
  intro a ha
  simp only [head1, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h | h | h | h | h <;> (rw [h]; norm_num)
theorem head1_abs : absSum head1.g = 5 := by norm_num [absSum, head1]
theorem head1_dq (j : ℕ) :
    dotQ head1.g (xh1 w j) = -mkR (tokAt w j) + 4 * Fq w j := by
  simp [dotQ, head1, xh1]
  try ring

theorem Fq_nonneg (w : List ℕ) (i : ℕ) : 0 ≤ Fq w i := by
  by_cases h : Pre w i
  · rw [Fq_pos h]; norm_num
  · rw [Fq_neg h]

theorem gate1_iff (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : j ≤ w.length) :
    head1.gate fl (p.g 1 0) (p.gb 1 0) (X1f fl ex p w j) = 0 ↔ (Mk w j ∧ ¬ Pre w j) := by
  obtain ⟨hl, hC⟩ := x1_close' ev j hj
  by_cases hm : Mk w j
  · by_cases hp : Pre w j
    · constructor
      · intro h
        exfalso
        exact gate_ne ev head1 head1_g6 head1_gW head1_gb _ _ hl (by norm_num) (by norm_num) hC
          (p.g 1 0) (p.gb 1 0) (ev.hp.g 1 0) (ev.hp.gb 1 0)
          (by rw [head1_dq, mkR_mk hm, Fq_pos hp]; norm_num) (by rw [head1_abs]; norm_num) h
      · intro h
        exact absurd hp h.2
    · constructor
      · intro _
        exact ⟨hm, hp⟩
      · intro _
        exact gate_zero ev head1 head1_g6 head1_gW head1_gb _ _ hl (by norm_num) (by norm_num) hC
          (p.g 1 0) (p.gb 1 0) (ev.hp.g 1 0) (ev.hp.gb 1 0)
          (by rw [head1_dq, mkR_mk hm, Fq_neg hp]; norm_num) (by rw [head1_abs]; norm_num)
  · constructor
    · intro h
      exfalso
      exact gate_ne ev head1 head1_g6 head1_gW head1_gb _ _ hl (by norm_num) (by norm_num) hC
        (p.g 1 0) (p.gb 1 0) (ev.hp.g 1 0) (ev.hp.gb 1 0)
        (by rw [head1_dq, mkR_nmk hm]; have := Fq_nonneg w j; linarith)
        (by rw [head1_abs]; norm_num) h
    · intro h
      exact absurd h.1 hm

noncomputable def cs1 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : List ℕ :=
  head1.cands fl (p.g 1 0) (p.gb 1 0) (w.length + 1) (X1f fl ex p w) i

noncomputable def att1 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (r : List ℚ) (k : ℕ) :
    ℝ :=
  savg fl ex (cs1 fl ex p w i)
    (fun j => head1.score fl (p.A 1 0) (p.m 1 0) (X1f fl ex p w) i j)
    (fun j => ardot fl r (X1f fl ex p w j) (p.V 1 0 k) 0 0)

theorem mem_cs1 (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (j : ℕ) :
    j ∈ cs1 fl ex p w i ↔ j ≤ i ∧ Mk w j ∧ ¬ Pre w j := by
  unfold cs1
  rw [AHead.mem_cands]
  have hm : head1.mask = Mask.causal := rfl
  rw [hm, Lane4.Seq.mem_cand_causal]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (gate1_iff ev j (by omega)).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (gate1_iff ev j (by omega)).mpr h2⟩

theorem savg_single (hr : Rnd u η M fl) (he : ExpM u η ex) (j : ℕ) (s f : ℕ → ℝ)
    (hf : |f j| ≤ M) : savg fl ex [j] s f = fl (f j) := by
  have hsw : swt fl ex [j] s j = 1 := swt_winner hr he s [j] j (by simp) (by simp)
  have hnum : Lane4.RSeq.rsum fl [fl (swt fl ex [j] s j * f j)] 0 = fl (fl (f j)) := by
    simp [Lane4.RSeq.rsum, hsw]
  have hden : Lane4.RSeq.rsum fl [swt fl ex [j] s j] 0 = 1 := by
    simp [Lane4.RSeq.rsum, hsw, hr.one]
  unfold savg
  simp only [List.map_cons, List.map_nil]
  rw [hnum, hden, div_one, hr.idem _ hf, hr.idem _ hf]

theorem att1_row (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr6 : r.length = 6)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 1) (k : ℕ) (i : ℕ) (hi : i ≤ w.length) :
    (¬ (∃ j, j ≤ i ∧ Mk w j ∧ ¬ Pre w j) → att1 fl ex p w i r k = 0) ∧
    (∀ j, j ≤ i → Mk w j → ¬ Pre w j →
      |att1 fl ex p w i r k - dotQ r (xh1 w j)| ≤ absSum r * (1 / 70) + 1 / 130 + 1 / 10000) := by
  have hcs := mem_cs1 ev i hi
  constructor
  · intro hn
    unfold att1
    apply soft_zeros ev.hr
    intro k' hk'
    exfalso
    obtain ⟨h1, h2, h3⟩ := (hcs k').mp hk'
    exact hn ⟨k', h1, h2, h3⟩
  · intro j hji hmk hnp
    have hjl : j ≤ w.length := by omega
    have hc1 : cs1 fl ex p w i = [j] := by
      unfold cs1 AHead.cands
      have hmask : head1.mask = Mask.causal := rfl
      rw [hmask]
      apply Lane4.Seq.filter_eq_singleton (Lane4.Seq.cand_nodup _ _ _)
      · exact Lane4.Seq.mem_cand_causal.mpr hji
      · exact decide_eq_true ((gate1_iff ev j hjl).mpr ⟨hmk, hnp⟩)
      · intro k' hk' hne
        apply decide_eq_false
        intro h0
        have hk'i := Lane4.Seq.mem_cand_causal.mp hk'
        obtain ⟨hm2, hp2⟩ := (gate1_iff ev k' (by omega)).mp h0
        exact hne (uniq_first hm2 hp2 hmk hnp)
    obtain ⟨hl, hC⟩ := x1_close' ev j hjl
    have hval := ardot6 ev r hr6 hW (by norm_num) (by norm_num) _ _ hl (by norm_num)
      (by norm_num) hC (p.V 1 0 k) (ev.hp.V 1 0 k)
    have hM130 : (130 : ℝ) ≤ M := ev.range 130 (by norm_num)
    unfold att1
    rw [hc1, savg_single ev.hr ev.he j
      (fun j' => head1.score fl (p.A 1 0) (p.m 1 0) (X1f fl ex p w) i j')
      (fun j' => ardot fl r (X1f fl ex p w j') (p.V 1 0 k) 0 0) (le_trans hval.2 hM130)]
    have hn := ev.hr.near ev.hu0 hval.1 hval.2 hM130
    have hs := ev.small
    have : u * 130 ≤ 1 / 10000000 * 130 := mul_le_mul_of_nonneg_right hs.1 (by norm_num)
    have h30 : (1 : ℝ) / 10 ^ 30 ≤ 1 / 100000000 := by norm_num
    show |fl (ardot fl r (X1f fl ex p w j) (p.V 1 0 k) 0 0) - dotQ r (xh1 w j)| ≤ _
    linarith

theorem att1_zero (ev : Ctx u η M fl ex p w) (k i : ℕ) (hi : i ≤ w.length) :
    |att1 fl ex p w i z6 k| ≤ 1 / 125 := by
  obtain ⟨h1, h2⟩ := att1_row ev z6 rfl (by simp [z6]) k i hi
  by_cases hF : ∃ j, j ≤ i ∧ Mk w j ∧ ¬ Pre w j
  · obtain ⟨j, hj, hm, hp⟩ := hF
    have := h2 j hj hm hp
    rw [dotQ_z6, absSum_z6] at this
    simp only [zero_mul, zero_add, sub_zero] at this
    linarith
  · rw [h1 hF]; norm_num

theorem r4_W : ∀ a ∈ ([0, 1, 0, 0, 0, 0] : List ℚ), |((a : ℚ) : ℝ)| ≤ 1 := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h | h | h | h | h <;> (rw [h]; norm_num)

theorem r4_abs : absSum ([0, 1, 0, 0, 0, 0] : List ℚ) = 1 := by
  norm_num [absSum]

theorem att1_A (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    ∃ Av : ℝ, (Av = 0 ∨ Av = 1) ∧ (Av = 1 ↔ firstc (w.take i) = 2) ∧
      |att1 fl ex p w i [0, 1, 0, 0, 0, 0] 4 - Av| ≤ 1 / 40 := by
  obtain ⟨h1, h2⟩ := att1_row ev [0, 1, 0, 0, 0, 0] rfl r4_W 4 i hi
  rcases firstc_take w i hi with ⟨hn, hf⟩ | ⟨j, hj, hm, hp, hf⟩
  · refine ⟨0, Or.inl rfl, ?_, ?_⟩
    · rw [hf]; norm_num
    · rw [h1 hn]; norm_num
  · refine ⟨aR (tokAt w j), aR_01 _, ?_, ?_⟩
    · rw [hf]
      rcases hm with h | h <;> simp [aR, code, h]
    · have := h2 j hj hm hp
      have hq : dotQ [0, 1, 0, 0, 0, 0] (xh1 w j) = aR (tokAt w j) := by simp [dotQ, xh1]
      rw [hq, r4_abs] at this
      linarith

/-! ### numeric lemmas -/

theorem ardot2 (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr2 : r.length = 2) {W : ℝ}
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ W) (hW0 : 0 ≤ W) (hW4 : W ≤ 4) (x xh : List ℝ)
    (hx : x.length = 2) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1 / 10) (hC : Close x xh e 1)
    (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r x d 0 0 - dotQ r xh| ≤ absSum r * e + 1 / 300 ∧ |ardot fl r x d 0 0| ≤ 50 := by
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
  rw [hr2] at k1 k2
  have h3 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have h16 : (2 : ℝ) ^ 16 = 65536 := by norm_num
  have h100 : (1 : ℝ) / 2 ^ 100 = 1 / 1267650600228229401496703205376 := by norm_num
  have hWW : (W + 1) * (1 + e + 1) ≤ 5 * (21 / 10) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  simp only [h3, h16, h100] at k1 k2
  constructor
  · nlinarith [k1, hWW]
  · nlinarith [k2.2, hWW]

theorem ardot6w (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr6 : r.length = 6) {W : ℝ}
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ W) (hW0 : 0 ≤ W) (hW4 : W ≤ 4) (x xh : List ℝ)
    (hx : x.length = 6) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1 / 4) (hC : Close x xh e 1)
    (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r x d 0 0 - dotQ r xh| ≤ absSum r * e + 1 / 100 ∧ |ardot fl r x d 0 0| ≤ 140 := by
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
  have hWW : (W + 1) * (1 + e + 1) ≤ 5 * (9 / 4) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  simp only [h3, h16, h100] at k1 k2
  constructor
  · nlinarith [k1, hWW]
  · nlinarith [k2.2, hWW]

theorem step2 (ev : Ctx u η M fl ex p w) {x s t s' y e es : ℝ} (hx : |x - t| ≤ e)
    (hs : |s - s'| ≤ es) (hy : t + s' = y) (hxB : |x| ≤ 2) (hsB : |s| ≤ 2) :
    |fl (x + s) - y| ≤ e + es + 1 / 1000000 := by
  have hM5 : (6 : ℝ) ≤ M := ev.range 6 (by norm_num)
  have hu := ev.small
  have hu4 : u * 4 ≤ 1 / 10000000 * 4 := mul_le_mul_of_nonneg_right hu.1 (by norm_num)
  have h4 : (1 : ℝ) / 10 ^ 30 ≤ 1 / 100000000 := by norm_num
  have h1 : |x + s - y| ≤ e + es := by
    rw [← hy]
    have := abs_add_le (x - t) (s - s')
    have e1 : x - t + (s - s') = x + s - (t + s') := by ring
    rw [e1] at this
    linarith
  have h2 : |x + s| ≤ 4 := le_trans (abs_add_le _ _) (by linarith)
  have h3 := ev.hr.near ev.hu0 h1 h2 (by linarith)
  linarith

/-! ### block 1: states -/

noncomputable def zv (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : Vec :=
  Lane4.RSeq.radd fl (X1f fl ex p w i)
    [att1 fl ex p w i z6 0, att1 fl ex p w i z6 1, att1 fl ex p w i z6 2,
     att1 fl ex p w i z6 3, att1 fl ex p w i [0, 1, 0, 0, 0, 0] 4, att1 fl ex p w i z6 5]

noncomputable def hidv (fl : ℝ → ℝ) (p : APert) (z : Vec) : Vec :=
  (araffine fl blk1.W1 blk1.b1 z (p.W1 1) (p.b1 1) 0).map Lane4.relu

noncomputable def mlpv (fl : ℝ → ℝ) (p : APert) (z : Vec) : Vec :=
  araffine fl blk1.W2 blk1.b2 (hidv fl p z) (p.W2 1) (p.b2 1) 0

theorem run_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    net.run fl ex p w i =
      Lane4.RSeq.radd fl (zv fl ex p w i) (mlpv fl p (zv fl ex p w i)) := rfl

theorem zv_vals (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (b0 b1 b2 b3 b4 b5 : ℝ)
    (hb : X1f fl ex p w i = [b0, b1, b2, b3, b4, b5]) :
    zv fl ex p w i =
      [fl (b0 + att1 fl ex p w i z6 0), fl (b1 + att1 fl ex p w i z6 1),
       fl (b2 + att1 fl ex p w i z6 2), fl (b3 + att1 fl ex p w i z6 3),
       fl (b4 + att1 fl ex p w i [0, 1, 0, 0, 0, 0] 4), fl (b5 + att1 fl ex p w i z6 5)] := by
  unfold zv
  rw [hb]
  rfl

theorem hid_vals (fl : ℝ → ℝ) (p : APert) (z0 z1 z2' z3 z4 z5 : ℝ) :
    hidv fl p [z0, z1, z2', z3, z4, z5] =
      [Lane4.relu (fl (ardot fl [0, 0, 1, 0, -1, 0] [z0, z1, z2', z3, z4, z5] (p.W1 1 0) 0 0
          + asw fl 0 (p.b1 1 0))),
       Lane4.relu (fl (ardot fl [0, 0, -1, 0, 1, 0] [z0, z1, z2', z3, z4, z5] (p.W1 1 1) 0 0
          + asw fl 0 (p.b1 1 1)))] := rfl

theorem mlp_vals (fl : ℝ → ℝ) (p : APert) (H0 H1 : ℝ) (z : Vec) (hz : hidv fl p z = [H0, H1]) :
    mlpv fl p z =
      [fl (ardot fl z2 [H0, H1] (p.W2 1 0) 0 0 + asw fl 0 (p.b2 1 0)),
       fl (ardot fl z2 [H0, H1] (p.W2 1 1) 0 0 + asw fl 0 (p.b2 1 1)),
       fl (ardot fl z2 [H0, H1] (p.W2 1 2) 0 0 + asw fl 0 (p.b2 1 2)),
       fl (ardot fl z2 [H0, H1] (p.W2 1 3) 0 0 + asw fl 0 (p.b2 1 3)),
       fl (ardot fl z2 [H0, H1] (p.W2 1 4) 0 0 + asw fl 0 (p.b2 1 4)),
       fl (ardot fl [1, 1] [H0, H1] (p.W2 1 5) 0 0 + asw fl 0 (p.b2 1 5))] := by
  unfold mlpv
  rw [hz]
  rfl

theorem z_ent (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (Av : ℝ)
    (hA01 : Av = 0 ∨ Av = 1) (hAatt : |att1 fl ex p w i [0, 1, 0, 0, 0, 0] 4 - Av| ≤ 1 / 40) :
    ∃ z0 z1 z2' z3 z4 z5 : ℝ, zv fl ex p w i = [z0, z1, z2', z3, z4, z5] ∧
      |z0 - mkR (tokAt w i)| ≤ 1 / 25 ∧ |z1 - aR (tokAt w i)| ≤ 1 / 25 ∧
      |z2' - cR (tokAt w i)| ≤ 1 / 25 ∧ |z3 - Fq w i| ≤ 1 / 25 ∧ |z4 - Av| ≤ 1 / 25 ∧
      |z5 - 0| ≤ 1 / 70 + 1 / 125 + 1 / 1000000 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, hb, g0, g1, g2, g3, g4, g5⟩ := x1_ent' ev i hi
  have a0 := att1_zero ev 0 i hi
  have a1 := att1_zero ev 1 i hi
  have a2 := att1_zero ev 2 i hi
  have a3 := att1_zero ev 3 i hi
  have a5 := att1_zero ev 5 i hi
  have hFq := Fq_abs w i
  have hs : ∀ s : ℝ, |s| ≤ 1 / 125 → |s| ≤ 2 := fun s h => le_trans h (by norm_num)
  have hA2 : |att1 fl ex p w i [0, 1, 0, 0, 0, 0] 4| ≤ 2 := by
    have := abs_le.mp hAatt
    rcases hA01 with h | h <;> rw [abs_le] <;> constructor <;> (rw [h] at this; linarith [this.1, this.2])
  refine ⟨_, _, _, _, _, _, zv_vals fl ex p w i b0 b1 b2 b3 b4 b5 hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := step2 ev g0 (s' := 0) (by simpa using a0) (add_zero _)
      (absb g0 (abs01 (mkR_01 _)) (by norm_num)) (hs _ a0)
    refine le_trans this ?_
    norm_num
  · have := step2 ev g1 (s' := 0) (by simpa using a1) (add_zero _)
      (absb g1 (abs01 (aR_01 _)) (by norm_num)) (hs _ a1)
    refine le_trans this ?_
    norm_num
  · have := step2 ev g2 (s' := 0) (by simpa using a2) (add_zero _)
      (absb g2 (abs01 (cR_01 _)) (by norm_num)) (hs _ a2)
    refine le_trans this ?_
    norm_num
  · have := step2 ev g3 (s' := 0) (by simpa using a3) (add_zero _)
      (absb g3 (le_trans hFq (by norm_num)) (by norm_num)) (hs _ a3)
    refine le_trans this ?_
    norm_num
  · have := step2 ev g4 hAatt (zero_add _)
      (absb g4 (by norm_num) (by norm_num)) hA2
    refine le_trans this ?_
    norm_num
  · have := step2 ev g5 (s' := 0) (y := 0) (by simpa using a5) (add_zero _)
      (absb g5 (by norm_num) (by norm_num)) (hs _ a5)
    refine le_trans this ?_
    norm_num

theorem hid_err (ev : Ctx u η M fl ex p w) {A a P : ℝ} (hA : |A - P| ≤ 2 / 25 + 1 / 130)
    (hA2 : |A| ≤ 130) (ha : |a| ≤ 1 / 900) :
    |Lane4.relu (fl (A + a)) - Lane4.relu P| ≤ 9 / 100 := by
  have hM : (140 : ℝ) ≤ M := ev.range 140 (by norm_num)
  have hu := ev.small
  have hu1 : u * 140 ≤ 1 / 10000000 * 140 := mul_le_mul_of_nonneg_right hu.1 (by norm_num)
  have h4 : (1 : ℝ) / 10 ^ 30 ≤ 1 / 100000000 := by norm_num
  have h1 : |A + a - P| ≤ 2 / 25 + 1 / 130 + 1 / 900 := by
    have := abs_add_le (A - P) a
    have e1 : A - P + a = A + a - P := by ring
    rw [e1] at this
    linarith
  have h2 : |A + a| ≤ 140 := le_trans (abs_add_le _ _) (by linarith)
  have h3 := ev.hr.near ev.hu0 h1 h2 hM
  have h5 : |fl (A + a) - P| ≤ 9 / 100 := by linarith
  unfold Lane4.relu
  exact le_trans (abs_max_sub_max_le_abs _ _ _) h5

theorem r5_W1 : ∀ a ∈ ([0, 0, 1, 0, -1, 0] : List ℚ), |((a : ℚ) : ℝ)| ≤ 1 := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h | h | h | h | h <;> (rw [h]; norm_num)

theorem r5_W2 : ∀ a ∈ ([0, 0, -1, 0, 1, 0] : List ℚ), |((a : ℚ) : ℝ)| ≤ 1 := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h | h | h | h | h <;> (rw [h]; norm_num)

theorem r5_abs1 : absSum ([0, 0, 1, 0, -1, 0] : List ℚ) = 2 := by norm_num [absSum]
theorem r5_abs2 : absSum ([0, 0, -1, 0, 1, 0] : List ℚ) = 2 := by norm_num [absSum]

theorem hid_ent (ev : Ctx u η M fl ex p w) (z0 z1 z2' z3 z4 z5 : ℝ) (zh : List ℝ)
    (hC : Close [z0, z1, z2', z3, z4, z5] zh (1 / 25) 1) (P : ℝ)
    (hq0 : dotQ [0, 0, 1, 0, -1, 0] zh = P) (hq1 : dotQ [0, 0, -1, 0, 1, 0] zh = -P) :
    ∃ H0 H1 : ℝ, hidv fl p [z0, z1, z2', z3, z4, z5] = [H0, H1] ∧
      |H0 - Lane4.relu P| ≤ 9 / 100 ∧ |H1 - Lane4.relu (-P)| ≤ 9 / 100 := by
  refine ⟨_, _, hid_vals fl p z0 z1 z2' z3 z4 z5, ?_, ?_⟩
  · have hd := ardot6 ev [0, 0, 1, 0, -1, 0] rfl r5_W1 (by norm_num) (by norm_num)
      [z0, z1, z2', z3, z4, z5] zh rfl (by norm_num) (by norm_num) hC (p.W1 1 0) (ev.hp.W1 1 0)
    have hb := asw_c ev 0 (ev.hp.b1 1 0) (by simp)
    rw [hq0, r5_abs1] at hd
    have hb' : |asw fl 0 (p.b1 1 0)| ≤ 1 / 900 := by simpa using hb
    exact hid_err ev (by have := hd.1; norm_num at this ⊢; linarith) (by have := hd.2; linarith) hb'
  · have hd := ardot6 ev [0, 0, -1, 0, 1, 0] rfl r5_W2 (by norm_num) (by norm_num)
      [z0, z1, z2', z3, z4, z5] zh rfl (by norm_num) (by norm_num) hC (p.W1 1 1) (ev.hp.W1 1 1)
    have hb := asw_c ev 0 (ev.hp.b1 1 1) (by simp)
    rw [hq1, r5_abs2] at hd
    have hb' : |asw fl 0 (p.b1 1 1)| ≤ 1 / 900 := by simpa using hb
    exact hid_err ev (by have := hd.1; norm_num at this ⊢; linarith) (by have := hd.2; linarith) hb'

theorem close2 {a0 a1 b0 b1 e X : ℝ} (h0 : |a0 - b0| ≤ e) (h1 : |a1 - b1| ≤ e)
    (g0 : |b0| ≤ X) (g1 : |b1| ≤ X) : Close [a0, a1] [b0, b1] e X := by
  refine ⟨rfl, ?_⟩
  intro k hk
  have hk2 : k < 2 := by simpa using hk
  interval_cases k <;> simp only [List.getD_cons_zero, List.getD_cons_succ] <;>
    first | exact ⟨h0, g0⟩ | exact ⟨h1, g1⟩

theorem relu_abs_le {P : ℝ} (hP : |P| ≤ 1) : |Lane4.relu P| ≤ 1 := by
  have := abs_le.mp hP
  unfold Lane4.relu
  exact abs_le.mpr ⟨by linarith [le_max_right P 0], max_le this.2 (by norm_num)⟩

theorem mlp_zero_err (ev : Ctx u η M fl ex p w) {A a : ℝ} (hA : |A| ≤ 1 / 300)
    (ha : |a| ≤ 1 / 900) : |fl (A + a)| ≤ 1 / 200 := by
  have hM : (1 : ℝ) ≤ M := ev.range 1 (by norm_num)
  have hu := ev.small
  have hu1 : u * 1 ≤ 1 / 10000000 * 1 := mul_le_mul_of_nonneg_right hu.1 (by norm_num)
  have h4 : (1 : ℝ) / 10 ^ 30 ≤ 1 / 100000000 := by norm_num
  have h1 : |A + a - 0| ≤ 1 / 300 + 1 / 900 := by
    rw [sub_zero]; exact le_trans (abs_add_le _ _) (by linarith)
  have h2 : |A + a| ≤ 1 := by
    have := abs_add_le A a
    linarith
  have h3 := ev.hr.near ev.hu0 h1 h2 hM
  rw [sub_zero] at h3
  linarith

theorem mlp_ent (ev : Ctx u η M fl ex p w) (z : Vec) (H0 H1 P : ℝ)
    (hz : hidv fl p z = [H0, H1]) (hP : |P| ≤ 1) (h0 : |H0 - Lane4.relu P| ≤ 9 / 100)
    (h1 : |H1 - Lane4.relu (-P)| ≤ 9 / 100) :
    ∃ n0 n1 n2 n3 n4 n5 : ℝ, mlpv fl p z = [n0, n1, n2, n3, n4, n5] ∧
      |n0| ≤ 1 / 200 ∧ |n1| ≤ 1 / 200 ∧ |n2| ≤ 1 / 200 ∧ |n3| ≤ 1 / 200 ∧ |n4| ≤ 1 / 200 ∧
      |n5 - (|P|)| ≤ 1845 / 10000 := by
  have hC2 : Close [H0, H1] [Lane4.relu P, Lane4.relu (-P)] (9 / 100) 1 :=
    close2 h0 h1 (relu_abs_le hP) (relu_abs_le (by rw [abs_neg]; exact hP))
  have row0 : ∀ k : ℕ, |fl (ardot fl z2 [H0, H1] (p.W2 1 k) 0 0 + asw fl 0 (p.b2 1 k))|
      ≤ 1 / 200 := by
    intro k
    have hd := ardot2 ev z2 rfl (W := 0) (by simp [z2]) le_rfl (by norm_num) [H0, H1]
      [Lane4.relu P, Lane4.relu (-P)] rfl (by norm_num) (by norm_num) hC2 (p.W2 1 k)
      (ev.hp.W2 1 k)
    have hz2 : absSum z2 = 0 := by simp [absSum, z2]
    rw [dotQ_zero_row z2 _ (by simp [z2]), hz2] at hd
    have hb := asw_c ev 0 (ev.hp.b2 1 k) (by simp)
    have hb' : |asw fl 0 (p.b2 1 k)| ≤ 1 / 900 := by simpa using hb
    have hd1 : |ardot fl z2 [H0, H1] (p.W2 1 k) 0 0| ≤ 1 / 300 := by
      have := hd.1
      simp only [zero_mul, zero_add, sub_zero] at this
      exact this
    exact mlp_zero_err ev hd1 hb'
  have hd5 := ardot2 ev [1, 1] rfl (W := 1) (by intro a ha; simp at ha; rw [ha]; norm_num)
    (by norm_num) (by norm_num) [H0, H1] [Lane4.relu P, Lane4.relu (-P)] rfl (by norm_num)
    (by norm_num) hC2 (p.W2 1 5) (ev.hp.W2 1 5)
  have hq : dotQ [1, 1] [Lane4.relu P, Lane4.relu (-P)] = |P| := by
    simp [dotQ]
    exact Lane4.relu_add_relu_neg P
  have habs2 : absSum ([1, 1] : List ℚ) = 2 := by norm_num [absSum]
  rw [hq, habs2] at hd5
  have hb5 := asw_c ev 0 (ev.hp.b2 1 5) (by simp)
  have hb5' : |asw fl 0 (p.b2 1 5)| ≤ 1 / 900 := by simpa using hb5
  have hM : (51 : ℝ) ≤ M := ev.range 51 (by norm_num)
  have hu := ev.small
  have hu1 : u * 51 ≤ 1 / 10000000 * 51 := mul_le_mul_of_nonneg_right hu.1 (by norm_num)
  have h4 : (1 : ℝ) / 10 ^ 30 ≤ 1 / 100000000 := by norm_num
  have hn1 : |ardot fl [1, 1] [H0, H1] (p.W2 1 5) 0 0 + asw fl 0 (p.b2 1 5) - (|P|)|
      ≤ 2 * (9 / 100) + 1 / 300 + 1 / 900 := by
    have := abs_add_le (ardot fl [1, 1] [H0, H1] (p.W2 1 5) 0 0 - |P|) (asw fl 0 (p.b2 1 5))
    have e1 : ardot fl [1, 1] [H0, H1] (p.W2 1 5) 0 0 - |P| + asw fl 0 (p.b2 1 5)
        = ardot fl [1, 1] [H0, H1] (p.W2 1 5) 0 0 + asw fl 0 (p.b2 1 5) - |P| := by ring
    rw [e1] at this
    have h5 := hd5.1
    linarith
  have hn2 : |ardot fl [1, 1] [H0, H1] (p.W2 1 5) 0 0 + asw fl 0 (p.b2 1 5)| ≤ 51 := by
    have := abs_add_le (ardot fl [1, 1] [H0, H1] (p.W2 1 5) 0 0) (asw fl 0 (p.b2 1 5))
    have h5 := hd5.2
    linarith
  have hn3 := ev.hr.near ev.hu0 hn1 hn2 hM
  refine ⟨_, _, _, _, _, _, mlp_vals fl p H0 H1 z hz, row0 0, row0 1, row0 2, row0 3, row0 4, ?_⟩
  linarith

/-! ### the whole network -/

theorem x2_ent (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    ∃ Av : ℝ, (Av = 0 ∨ Av = 1) ∧ (Av = 1 ↔ firstc (w.take i) = 2) ∧
      ∃ c0 c1 c2 c3 c4 c5 : ℝ, net.run fl ex p w i = [c0, c1, c2, c3, c4, c5] ∧
        |c0 - mkR (tokAt w i)| ≤ 21 / 100 ∧ |c1 - aR (tokAt w i)| ≤ 21 / 100 ∧
        |c2 - cR (tokAt w i)| ≤ 21 / 100 ∧ |c3 - Fq w i| ≤ 21 / 100 ∧ |c4 - Av| ≤ 21 / 100 ∧
        |c5 - (|cR (tokAt w i) - Av|)| ≤ 21 / 100 := by
  obtain ⟨Av, hA01, hAiff, hAatt⟩ := att1_A ev i hi
  obtain ⟨z0, z1, z2', z3, z4, z5, hzv, e0, e1, e2, e3, e4, e5⟩ := z_ent ev i hi Av hA01 hAatt
  have hFq := Fq_abs w i
  have hzh : Close [z0, z1, z2', z3, z4, z5]
      [mkR (tokAt w i), aR (tokAt w i), cR (tokAt w i), Fq w i, Av, 0] (1 / 25) 1 :=
    close6 e0 e1 e2 e3 e4 (le_trans e5 (by norm_num)) (abs01 (mkR_01 _)) (abs01 (aR_01 _))
      (abs01 (cR_01 _)) (le_trans hFq (by norm_num)) (abs01 hA01) (by norm_num)
  have hq0 : dotQ [0, 0, 1, 0, -1, 0]
      [mkR (tokAt w i), aR (tokAt w i), cR (tokAt w i), Fq w i, Av, 0] = cR (tokAt w i) - Av := by
    simp [dotQ]
    try ring
  have hq1 : dotQ [0, 0, -1, 0, 1, 0]
      [mkR (tokAt w i), aR (tokAt w i), cR (tokAt w i), Fq w i, Av, 0]
      = -(cR (tokAt w i) - Av) := by
    simp [dotQ]
    try ring
  obtain ⟨H0, H1, hH, hh0, hh1⟩ := hid_ent ev z0 z1 z2' z3 z4 z5 _ hzh _ hq0 hq1
  have hP : |cR (tokAt w i) - Av| ≤ 1 := by
    rcases cR_01 (tokAt w i) with h | h <;> rcases hA01 with h' | h' <;> rw [h, h'] <;> norm_num
  obtain ⟨n0, n1, n2, n3, n4, n5, hm, m0, m1, m2, m3, m4, m5⟩ :=
    mlp_ent ev (zv fl ex p w i) H0 H1 _ (by rw [hzv]; exact hH) hP hh0 hh1
  have hrun : net.run fl ex p w i =
      [fl (z0 + n0), fl (z1 + n1), fl (z2' + n2), fl (z3 + n3), fl (z4 + n4), fl (z5 + n5)] := by
    rw [run_eq, hm, hzv]
    rfl
  refine ⟨Av, hA01, hAiff, _, _, _, _, _, _, hrun, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := step2 ev e0 (s' := 0) (by simpa using m0) (add_zero _)
      (absb e0 (abs01 (mkR_01 _)) (by norm_num)) (le_trans m0 (by norm_num))
    refine le_trans this ?_
    norm_num
  · have := step2 ev e1 (s' := 0) (by simpa using m1) (add_zero _)
      (absb e1 (abs01 (aR_01 _)) (by norm_num)) (le_trans m1 (by norm_num))
    refine le_trans this ?_
    norm_num
  · have := step2 ev e2 (s' := 0) (by simpa using m2) (add_zero _)
      (absb e2 (abs01 (cR_01 _)) (by norm_num)) (le_trans m2 (by norm_num))
    refine le_trans this ?_
    norm_num
  · have := step2 ev e3 (s' := 0) (by simpa using m3) (add_zero _)
      (absb e3 (le_trans hFq (by norm_num)) (by norm_num)) (le_trans m3 (by norm_num))
    refine le_trans this ?_
    norm_num
  · have := step2 ev e4 (s' := 0) (by simpa using m4) (add_zero _)
      (absb e4 (abs01 hA01) (by norm_num)) (le_trans m4 (by norm_num))
    refine le_trans this ?_
    norm_num
  · have hPa : |(|cR (tokAt w i) - Av|)| ≤ 1 := by rwa [abs_abs]
    have := step2 ev e5 m5 (zero_add _) (absb e5 (by norm_num) (by norm_num))
      (absb m5 hPa (by norm_num))
    refine le_trans this ?_
    norm_num

theorem tokAt_eq' (w : List ℕ) (i : ℕ) (h : 1 ≤ i) : tokAt w i = w.getD (i - 1) 0 := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  simp [tokAt]

theorem cR_cbit (t : ℕ) (ht : t ≤ 5) : cR t = ((cbit t : ℕ) : ℝ) := by
  interval_cases t <;> simp [cR, cbit]

theorem target_eq (w : List ℕ) (i : ℕ) (hi1 : 1 ≤ i) (ht : tokAt w i ≤ 5) (Av : ℝ)
    (hA01 : Av = 0 ∨ Av = 1) (hAiff : Av = 1 ↔ firstc (w.take i) = 2) :
    ((target w i : ℕ) : ℝ) = |cR (tokAt w i) - Av| := by
  unfold target
  rw [← tokAt_eq' w i hi1]
  have hcR := cR_cbit _ ht
  have hcb : cbit (tokAt w i) = 0 ∨ cbit (tokAt w i) = 1 := by
    generalize tokAt w i = t at ht ⊢
    interval_cases t <;> simp [cbit]
  by_cases hf : firstc (w.take i) = 2
  · have hAv : Av = 1 := hAiff.mpr hf
    rw [if_pos hf, hAv, hcR]
    rcases hcb with hc | hc <;> rw [hc] <;> norm_num
  · have hAv : Av = 0 := by
      rcases hA01 with h | h
      · exact h
      · exact absurd (hAiff.mp h) hf
    rw [if_neg hf, hAv, hcR]
    rcases hcb with hc | hc <;> rw [hc] <;> norm_num

theorem outW_W : ∀ a ∈ net.outW, |(a : ℝ)| ≤ 1 := by
  intro a ha
  simp only [net, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h | h | h | h | h <;> (rw [h]; norm_num)

theorem outW_abs : absSum net.outW = 1 := by norm_num [absSum, net]

end Steps

theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη1 p hp w hw hn hnη hM i hi1 hi
  have ev : Ctx u η M fl ex p w := ⟨hr, he, hu0, hu1, hη0, hη1, hp, hw, hn, hnη, hM⟩
  obtain ⟨Av, hA01, hAiff, c0, c1, c2, c3, c4, c5, hrun, e0, e1, e2, e3, e4, e5⟩ :=
    x2_ent ev i hi
  have hY : ((target w i : ℕ) : ℝ) = |cR (tokAt w i) - Av| :=
    target_eq w i hi1 (tok_le w hw i) Av hA01 hAiff
  have hFq := Fq_abs w i
  have hC : Close [c0, c1, c2, c3, c4, c5]
      [mkR (tokAt w i), aR (tokAt w i), cR (tokAt w i), Fq w i, Av, |cR (tokAt w i) - Av|]
      (21 / 100) 1 := by
    refine close6 e0 e1 e2 e3 e4 e5 (abs01 (mkR_01 _)) (abs01 (aR_01 _)) (abs01 (cR_01 _))
      (le_trans hFq (by norm_num)) (abs01 hA01) ?_
    rw [abs_abs]
    rcases cR_01 (tokAt w i) with h | h <;> rcases hA01 with h' | h' <;> rw [h, h'] <;> norm_num
  have hd := ardot6w ev net.outW rfl (W := 1) outW_W (by norm_num) (by norm_num)
    [c0, c1, c2, c3, c4, c5] _ rfl (by norm_num) (by norm_num) hC p.oW ev.hp.oW
  have hq : dotQ net.outW
      [mkR (tokAt w i), aR (tokAt w i), cR (tokAt w i), Fq w i, Av, |cR (tokAt w i) - Av|]
      = |cR (tokAt w i) - Av| := by
    simp [dotQ, net]
  rw [hq, outW_abs] at hd
  have hob : |asw fl net.outB p.oB| ≤ 1 / 900 := by
    have h := asw_c ev net.outB ev.hp.oB (by simp [net])
    have h0 : ((net.outB : ℚ) : ℝ) = 0 := by simp [net]
    rwa [h0, sub_zero] at h
  rw [hY]
  unfold ANet.out
  rw [hrun]
  obtain ⟨hd1, hd2⟩ := hd
  generalize ardot fl net.outW [c0, c1, c2, c3, c4, c5] p.oW 0 0 = A at hd1 hd2 ⊢
  generalize asw fl net.outB p.oB = a at hob ⊢
  have hM : (150 : ℝ) ≤ M := ev.range 150 (by norm_num)
  have hs := ev.small
  have hu1' : u * 150 ≤ 1 / 10000000 * 150 := mul_le_mul_of_nonneg_right hs.1 (by norm_num)
  have h4 : (1 : ℝ) / 10 ^ 30 ≤ 1 / 100000000 := by norm_num
  have h1 : |A + a - (|cR (tokAt w i) - Av|)| ≤ 1 * (21 / 100) + 1 / 100 + 1 / 900 := by
    have := abs_add_le (A - |cR (tokAt w i) - Av|) a
    have e1 : A - |cR (tokAt w i) - Av| + a = A + a - |cR (tokAt w i) - Av| := by ring
    rw [e1] at this
    linarith
  have h2 : |A + a| ≤ 150 := le_trans (abs_add_le _ _) (by linarith)
  have h3 := ev.hr.near ev.hu0 h1 h2 hM
  linarith

end Lane4.Case
