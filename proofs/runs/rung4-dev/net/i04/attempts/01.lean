namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

/-! ### The weights

State (width 14): 0 hv, 1..3 f_t (token complement), 4..6 pc_t (previous-token complement),
7..9 S_t (head outputs), 10 y, 11 const 1, 12 position, 13 n. -/

def z14 : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def hd1A : List (List ℚ) :=
  [z14, z14, z14, z14, z14, z14, z14, z14, z14, z14, z14,
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], z14, z14]

def hd1V : List (List ℚ) :=
  [z14, z14, z14, z14,
   [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   z14, z14, z14, z14, z14, z14, z14]

def hd1 : Head := { A := hd1A, V := hd1V, mask := Mask.strict }

def hdAA : List (List ℚ) :=
  [z14, z14, z14, z14, z14, z14, z14, z14, z14, z14, z14,
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], z14,
   [0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def hdAV : List (List ℚ) :=
  [z14, z14, z14, z14, z14, z14, z14,
   [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   z14, z14, z14, z14, z14, z14]
def hdA : Head := { A := hdAA, V := hdAV, mask := Mask.causal }

def hdBA : List (List ℚ) :=
  [z14, z14, z14, z14, z14, z14, z14, z14, z14, z14, z14,
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], z14,
   [0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0]]
def hdBV : List (List ℚ) :=
  [z14, z14, z14, z14, z14, z14, z14, z14,
   [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   z14, z14, z14, z14, z14]
def hdB : Head := { A := hdBA, V := hdBV, mask := Mask.causal }

def hdCA : List (List ℚ) :=
  [z14, z14, z14, z14, z14, z14, z14, z14, z14, z14, z14,
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], z14,
   [0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0]]
def hdCV : List (List ℚ) :=
  [z14, z14, z14, z14, z14, z14, z14, z14, z14,
   [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   z14, z14, z14, z14]
def hdC : Head := { A := hdCA, V := hdCV, mask := Mask.causal }

def blk1 : Block :=
  { heads := [hd1], W1 := [], b1 := [],
    W2 := [[], [], [], [], [], [], [], [], [], [], [], [], [], []], b2 := z14 }

def blk2W1 : List (List ℚ) :=
  [[0, -3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
   [0, 0, -3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
   [0, 0, 0, -3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]
def blk2W2 : List (List ℚ) :=
  [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0],
   [0, 0, 0], [0, 0, 0], [1, 1, 1], [0, 0, 0], [0, 0, 0], [0, 0, 0]]

def blk2 : Block :=
  { heads := [hdA, hdB, hdC], W1 := blk2W1, b1 := [0, 0, 0], W2 := blk2W2, b2 := z14 }

def netE : List (List ℚ) :=
  [[0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0],
   [2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]

def netOutW : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]

def net : TNet := { embed := netE, blocks := [blk1, blk2], outW := netOutW, outB := 0 }

theorem hd1_V : hd1.V = hd1V := rfl
theorem hd1_mask : hd1.mask = Mask.strict := rfl
theorem hdA_A : hdA.A = hdAA := rfl
theorem hdA_V : hdA.V = hdAV := rfl
theorem hdA_mask : hdA.mask = Mask.causal := rfl
theorem hdB_A : hdB.A = hdBA := rfl
theorem hdB_V : hdB.V = hdBV := rfl
theorem hdB_mask : hdB.mask = Mask.causal := rfl
theorem hdC_A : hdC.A = hdCA := rfl
theorem hdC_V : hdC.V = hdCV := rfl
theorem hdC_mask : hdC.mask = Mask.causal := rfl
theorem hd1_A : hd1.A = hd1A := rfl
theorem blk1_heads : blk1.heads = [hd1] := rfl
theorem blk1_W1 : blk1.W1 = [] := rfl
theorem blk1_b1 : blk1.b1 = [] := rfl
theorem blk1_W2 : blk1.W2 = [[], [], [], [], [], [], [], [], [], [], [], [], [], []] := rfl
theorem blk1_b2 : blk1.b2 = z14 := rfl
theorem blk2_heads : blk2.heads = [hdA, hdB, hdC] := rfl
theorem blk2_W1 : blk2.W1 = blk2W1 := rfl
theorem blk2_b1 : blk2.b1 = [0, 0, 0] := rfl
theorem blk2_W2 : blk2.W2 = blk2W2 := rfl
theorem blk2_b2 : blk2.b2 = z14 := rfl
theorem net_embed : net.embed = netE := rfl
theorem net_outW : net.outW = netOutW := rfl
theorem net_outB : net.outB = 0 := rfl
theorem net_blocks : net.blocks = [blk1, blk2] := rfl

/-! ### State shape and stored values -/

def st (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 pj pn : ℝ) : Vec :=
  [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, 1, pj, pn]

noncomputable def Hv (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl ((h (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 0)

noncomputable def Fv (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (t j : ℕ) : ℝ :=
  sw fl (if tokAt w j = t then 0 else 1) (p.E (tokAt w j) t)

noncomputable def pcv (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (t m : ℕ) : ℝ :=
  if m = 0 then 0 else fl (sw fl 1 (p.V 0 0 (3 + t) t) * Fv fl p w t (m - 1))

noncomputable def Sv (fl : ℝ → ℝ) (p : Pert) (k : ℕ) (hm : ℝ) : ℝ :=
  fl (sw fl 1 (p.V 1 k (7 + k) 0) * hm)

noncomputable def X1 (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (m : ℕ) : Vec :=
  st (Hv fl p w m) (Fv fl p w 1 m) (Fv fl p w 2 m) (Fv fl p w 3 m)
    (pcv fl p w 1 m) (pcv fl p w 2 m) (pcv fl p w 3 m) 0 0 0 0
    (fl (m : ℝ)) (fl ((w.length + 1 : ℕ) : ℝ))

noncomputable def PRE (fl : ℝ → ℝ) (d3 d1 f s : ℝ) : ℝ :=
  fl (fl (sw fl (-3) d3 * f) + fl (sw fl 1 d1 * s))

noncomputable def Yv (fl : ℝ → ℝ) (d0 d1 d2 H1 H2 H3 : ℝ) : ℝ :=
  fl (fl (fl (sw fl 1 d0 * H1) + fl (sw fl 1 d1 * H2)) + fl (sw fl 1 d2 * H3))

/-! ### Generic lemmas -/

theorem tok_le3 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) : tokAt w j ≤ 3 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h0 | h0
  · omega
  · exact (hw _ h0).2

theorem tok_ge1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ w.length) : 1 ≤ tokAt w j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hk : k < w.length := by omega
  rw [Lane4.Seq.tokAt_succ w k hk]
  exact (hw _ (List.getElem_mem hk)).1

theorem h_le (t : ℕ) : h t ≤ 2 := by
  unfold h
  split_ifs <;> omega

theorem sw_lit {u τ ε : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu : 0 ≤ u) (c : ℚ) (v : ℝ)
    (hv : (c : ℝ) = v) {d : ℝ} (hd : |d| ≤ τ) (hε : τ + u + u * τ ≤ ε) (a : ℝ)
    (ha : |v| = a) : |sw fl c d - v| ≤ ε * a := by
  have h1 := sw_rel hr hu c hd hε
  rw [hv, ha] at h1
  exact h1

theorem sw1_rel {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {d : ℝ} (hd : |d| ≤ 1 / 200) : |sw fl 1 d - 1| ≤ 3 / 250 := by
  have h1 := sw_lit hr hu0 1 1 (by norm_num) hd (ε := 3 / 250) (by linarith) 1 (by norm_num)
  linarith

theorem sw1_bd {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    1 - 3 / 250 ≤ sw fl 1 d ∧ sw fl 1 d ≤ 1 + 3 / 250 := by
  have h := abs_le.mp (sw1_rel hr hu0 hu1 hd)
  constructor <;> linarith [h.1, h.2]

theorem swm2_bd {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    -2 - 3 / 250 * 2 ≤ sw fl (-2) d ∧ sw fl (-2) d ≤ -2 + 3 / 250 * 2 := by
  have h1 := sw_lit hr hu0 (-2) (-2) (by norm_num) hd (ε := 3 / 250) (by linarith) 2
    (by rw [abs_neg]; exact abs_of_nonneg (by norm_num))
  have h2 := abs_le.mp h1
  constructor <;> linarith [h2.1, h2.2]

theorem swm3_bd {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    -3 - 3 / 250 * 3 ≤ sw fl (-3) d ∧ sw fl (-3) d ≤ -3 + 3 / 250 * 3 := by
  have h1 := sw_lit hr hu0 (-3) (-3) (by norm_num) hd (ε := 3 / 250) (by linarith) 3
    (by rw [abs_neg]; exact abs_of_nonneg (by norm_num))
  have h2 := abs_le.mp h1
  constructor <;> linarith [h2.1, h2.2]

theorem rel1 {x ε : ℝ} (h1 : |x - 1| ≤ ε) : |x - 1| ≤ ε * |(1 : ℝ)| := by
  rw [abs_one, mul_one]
  exact h1

theorem fl_neg_of_neg {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu1 : u ≤ 1 / 16777216)
    {x : ℝ} (hx : x < 0) : fl x < 0 := by
  have h1 := hr.rel x
  rw [abs_of_neg hx] at h1
  have h3 := (abs_le.mp h1).2
  have h4 := mul_le_mul_of_nonneg_right hu1 (neg_nonneg.mpr hx.le)
  linarith

theorem sc_m {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (a b c : ℝ) :
    fl (fl a + fl (b * fl (c * 0))) = fl a := by
  simp [hr.zero, hr.idem]

theorem exists_last (P : ℕ → Prop) (h0 : P 0) (i : ℕ) :
    ∃ m, m ≤ i ∧ P m ∧ ∀ k, k ≤ i → P k → k ≤ m := by
  induction i with
  | zero => exact ⟨0, le_refl _, h0, fun k hk _ => hk⟩
  | succ n ih =>
    rcases Classical.em (P (n + 1)) with hP | hP
    · exact ⟨n + 1, le_refl _, hP, fun k hk _ => hk⟩
    · obtain ⟨m, hm, hPm, hmax⟩ := ih
      refine ⟨m, by omega, hPm, ?_⟩
      intro k hk hPk
      by_cases hkn : k = n + 1
      · exfalso
        apply hP
        rw [← hkn]
        exact hPk
      · exact hmax k (by omega) hPk

/-! ### Stored values: bounds -/

theorem fl_Hv {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ) :
    fl (Hv fl p w j) = Hv fl p w j := by
  unfold Hv
  exact fl_sw hr _ _

theorem fl_Fv {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (t j : ℕ) :
    fl (Fv fl p w t j) = Fv fl p w t j := by
  unfold Fv
  exact fl_sw hr _ _

theorem fl_pcv {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (t m : ℕ) :
    fl (pcv fl p w t m) = pcv fl p w t m := by
  unfold pcv
  split_ifs
  · exact hr.zero
  · exact hr.idem _

theorem Fv_self {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (t j : ℕ)
    (htok : tokAt w j = t) : Fv fl p w t j = 0 := by
  simp [Fv, htok, sw_zero hr]

theorem Fv_near {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (t j : ℕ)
    (hne : tokAt w j ≠ t) : |Fv fl p w t j - 1| ≤ 3 / 250 := by
  have h1 : Fv fl p w t j = sw fl 1 (p.E (tokAt w j) t) := by simp [Fv, hne]
  rw [h1]
  exact sw1_rel hr hu0 hu1 (hp.E (tokAt w j) t)

theorem Hv_near {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ) :
    |Hv fl p w j - ((h (tokAt w j) : ℕ) : ℝ)| ≤ 3 / 250 * ((h (tokAt w j) : ℕ) : ℝ) := by
  have h1 := sw_rel hr hu0 ((h (tokAt w j) : ℕ) : ℚ) (hp.E (tokAt w j) 0) (ε := 3 / 250)
    (by linarith)
  have e : (((h (tokAt w j) : ℕ) : ℚ) : ℝ) = ((h (tokAt w j) : ℕ) : ℝ) := Rat.cast_natCast _
  have hnn : (0 : ℝ) ≤ ((h (tokAt w j) : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [e, abs_of_nonneg hnn] at h1
  unfold Hv
  exact h1

theorem Hv_bd {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ) :
    0 ≤ Hv fl p w j ∧ Hv fl p w j ≤ 2024 / 1000 := by
  have hnear := Hv_near hr hu0 hu1 p hp w j
  have hT0 : (0 : ℝ) ≤ ((h (tokAt w j) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hT2 : ((h (tokAt w j) : ℕ) : ℝ) ≤ 2 := by exact_mod_cast h_le _
  obtain ⟨a, b⟩ := abs_le.mp hnear
  constructor <;> linarith

theorem Sv_bd {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (k m : ℕ) :
    0 ≤ Sv fl p k (Hv fl p w m) ∧ Sv fl p k (Hv fl p w m) ≤ 21 / 10 := by
  unfold Sv
  obtain ⟨hH0, hH1⟩ := Hv_bd hr hu0 hu1 p hp w m
  obtain ⟨hv0, hv1⟩ := sw1_bd hr hu0 hu1 (hp.V 1 k (7 + k) 0)
  have hP0 : 0 ≤ sw fl 1 (p.V 1 k (7 + k) 0) * Hv fl p w m :=
    mul_nonneg (by linarith) hH0
  have hP1 : sw fl 1 (p.V 1 k (7 + k) 0) * Hv fl p w m ≤ (1 + 3 / 250) * (2024 / 1000) :=
    mul_le_mul hv1 hH1 hH0 (by norm_num)
  have hb : |sw fl 1 (p.V 1 k (7 + k) 0) * Hv fl p w m| ≤ 3 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  refine ⟨hr.nonneg hP0, ?_⟩
  have := hr.upper hu0 hb
  linarith

theorem pcv_zero {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (t m : ℕ)
    (hm : m = 0 ∨ tokAt w (m - 1) = t) : pcv fl p w t m = 0 := by
  by_cases h0 : m = 0
  · simp [pcv, h0]
  · rcases hm with hm | hm
    · exact absurd hm h0
    · simp [pcv, h0, Fv_self hr p w t (m - 1) hm, hr.zero]

theorem pcv_near {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (t m : ℕ)
    (hm0 : m ≠ 0) (hne : tokAt w (m - 1) ≠ t) : |pcv fl p w t m - 1| ≤ 13 / 500 := by
  have hF := Fv_near hr hu0 hu1 p hp w t (m - 1) hne
  have hV := sw1_rel hr hu0 hu1 (hp.V 0 0 (3 + t) t)
  have hpc : pcv fl p w t m = fl (sw fl 1 (p.V 0 0 (3 + t) t) * Fv fl p w t (m - 1)) := by
    simp [pcv, hm0]
  rw [hpc]
  have e1 := rel_mul (rel1 hV) (rel1 hF) (c := 1 / 40) (by norm_num)
  have f1 := rel_fl hr hu0 e1 (c := 13 / 500) (by linarith)
  simp only [mul_one, abs_one] at f1
  exact f1

/-! ### The previous occurrence -/

theorem find_range (p : ℕ → Bool) (n : ℕ) :
    ((List.range n).reverse.find? p = none ∧ ∀ k, k < n → p k = false) ∨
    ∃ j, (List.range n).reverse.find? p = some j ∧ j < n ∧ p j = true ∧
      ∀ k, j < k → k < n → p k = false := by
  induction n with
  | zero => left; simp
  | succ n ih =>
    have hrev : (List.range (n + 1)).reverse = n :: (List.range n).reverse := by
      simp [List.range_succ]
    rw [hrev]
    by_cases hp : p n = true
    · right
      refine ⟨n, ?_, by omega, hp, ?_⟩
      · simp [List.find?_cons, hp]
      · intro k hk1 hk2
        omega
    · have hpf : p n = false := by simpa using hp
      rcases ih with ⟨h1, h2⟩ | ⟨j, h1, h2, h3, h4⟩
      · left
        refine ⟨?_, ?_⟩
        · simp [List.find?_cons, hpf, h1]
        · intro k hk
          by_cases hkn : k = n
          · rw [hkn]; exact hpf
          · exact h2 k (by omega)
      · right
        refine ⟨j, ?_, by omega, h3, ?_⟩
        · simp [List.find?_cons, hpf, h1]
        · intro k hk1 hk2
          by_cases hkn : k = n
          · rw [hkn]; exact hpf
          · exact h4 k hk1 (by omega)

theorem prevOcc_spec (w : List ℕ) (i : ℕ) :
    (prevOcc w i = none ∧ ∀ k, 1 ≤ k → k < i → tokAt w k ≠ tokAt w i) ∨
    ∃ j, prevOcc w i = some j ∧ 1 ≤ j ∧ j < i ∧ tokAt w j = tokAt w i ∧
      ∀ k, j < k → k < i → ¬ (1 ≤ k ∧ tokAt w k = tokAt w i) := by
  have key := find_range (fun j => decide (1 ≤ j) && (tokAt w j == tokAt w i)) i
  unfold prevOcc
  rcases key with ⟨h1, h2⟩ | ⟨j, h1, h2, h3, h4⟩
  · left
    refine ⟨h1, ?_⟩
    intro k hk1 hk2 heq
    have := h2 k hk2
    simp [hk1, heq] at this
  · right
    have h3' : 1 ≤ j ∧ tokAt w j = tokAt w i := by simpa using h3
    refine ⟨j, h1, h3'.1, h2, h3'.2, ?_⟩
    intro k hk1 hk2 hk
    have := h4 k hk1 hk2
    simp [hk.1, hk.2] at this

theorem target_eq (w : List ℕ) (i : ℕ) (hi1 : 1 ≤ i) (ht : 1 ≤ tokAt w i) (m : ℕ) (hm : m ≤ i)
    (hP : m = 0 ∨ tokAt w (m - 1) = tokAt w i)
    (hmax : ∀ k, k ≤ i → (k = 0 ∨ tokAt w (k - 1) = tokAt w i) → k ≤ m) :
    target w i = h (tokAt w m) := by
  rcases prevOcc_spec w i with ⟨hnone, hno⟩ | ⟨j, hj, hj1, hji, hjt, hjlast⟩
  · have hm0 : m = 0 := by
      rcases hP with h0 | h1
      · exact h0
      · by_contra hne
        by_cases hk0 : m - 1 = 0
        · rw [hk0, Lane4.Seq.tokAt_zero] at h1
          omega
        · exact hno (m - 1) (by omega) (by omega) h1
    have e : target w i = 0 := by simp [target, hnone]
    rw [e, hm0, Lane4.Seq.tokAt_zero]
    simp [h]
  · have e : target w i = h (tokAt w (j + 1)) := by simp [target, hj]
    have h1 : j + 1 ≤ m := hmax (j + 1) (by omega) (Or.inr (by simpa using hjt))
    have h2 : m ≤ j + 1 := by
      by_contra hlt
      have hmne : m ≠ 0 := by omega
      have hmt : tokAt w (m - 1) = tokAt w i := by
        rcases hP with h0 | h1'
        · exact absurd h0 hmne
        · exact h1'
      exact hjlast (m - 1) (by omega) (by omega) ⟨by omega, hmt⟩
    have hmj : m = j + 1 := by omega
    rw [e, hmj]

/-! ### Initial state -/

set_option maxHeartbeats 1000000 in
theorem init_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) :
    net.init fl p w j = st (Hv fl p w j) (Fv fl p w 1 j) (Fv fl p w 2 j) (Fv fl p w 3 j)
      0 0 0 0 0 0 0 (fl (j : ℝ)) (fl ((w.length + 1 : ℕ) : ℝ)) := by
  have h4 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 := by
    have := tok_le3 w hw j
    omega
  rcases h4 with ht | ht | ht | ht <;>
    simp [TNet.init, net_embed, netE, st, Hv, Fv, swRow, pos, ht, h, sw_zero hr]

/-! ### Block 1 -/

theorem score1_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 qi qn b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 qk qn' : ℝ) :
    hd1.score fl dA (st a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 qi qn)
      (st b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 qk qn') = fl (sw fl 1 (dA 11 12) * qk) := by
  simp [Head.score, hd1_A, hd1A, z14, st, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem]

set_option maxHeartbeats 1000000 in
theorem sel1_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    hd1.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = [i - 1] := by
  apply Head.sel_unique
  · rw [hd1_mask, Lane4.Seq.mem_cand_strict]
    omega
  · intro k hk hne
    rw [hd1_mask, Lane4.Seq.mem_cand_strict] at hk
    simp only [init_eq hr p w hw]
    rw [score1_eq hr, score1_eq hr]
    have hS := sw1_bd hr hu0 hu1 (hp.A 0 0 11 12)
    obtain ⟨hS1, hS2⟩ := hS
    have hS0 : 0 ≤ sw fl 1 (p.A 0 0 11 12) := by linarith
    have hg := hr.pos_gap hu0 (show k < i - 1 by omega) (show i - 1 ≤ w.length + 1 by omega) hn
    have hk' := hr.pos_le hu0 (show k ≤ w.length + 1 by omega) hn
    have hj' := hr.pos_le hu0 (show i - 1 ≤ w.length + 1 by omega) hn
    apply hr.lt_of_gap hu0 (B := 2 * (((w.length + 1 : ℕ) : ℝ) + 1 / 256))
    · rw [abs_of_nonneg (mul_nonneg hS0 hk'.1)]
      exact mul_le_mul (by linarith) hk'.2 hk'.1 (by norm_num)
    · rw [abs_of_nonneg (mul_nonneg hS0 hj'.1)]
      exact mul_le_mul (by linarith) hj'.2 hj'.1 (by norm_num)
    · have h1 := mul_le_mul_of_nonneg_left hg hS0
      nlinarith [h1, hn, hu0, hu1, hS1]

theorem sel1_zero {fl : ℝ → ℝ} (p : Pert) (w : List ℕ) :
    hd1.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) 0 = [] := by
  simp [Head.sel, selOf, cand, hd1_mask]

set_option maxHeartbeats 1000000 in
theorem x1_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (m : ℕ) (hm : m ≤ w.length) :
    blk1.apply fl p 0 (w.length + 1) (net.init fl p w) m = X1 fl p w m := by
  rcases m with _ | k
  · have hs := sel1_zero (fl := fl) p w
    simp [Block.apply, blk1_heads, blk1_W1, blk1_b1, blk1_W2, blk1_b2, z14, headsApply,
      Head.attn, hs, hd1_V, hd1V, attnRows, ravg, rsum, radd, raffine, rdot,
      init_eq hr p w hw, X1, st, pcv, sw_zero hr, hr.zero, hr.idem, hr.one, fl_Hv hr,
      fl_Fv hr, fl_sw hr]
  · have hs0 := sel1_eq hr hu0 hu1 p hp w hw hn (k + 1) (by omega) hm
    have hs : hd1.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) (k + 1) = [k] := by
      simpa using hs0
    simp [Block.apply, blk1_heads, blk1_W1, blk1_b1, blk1_W2, blk1_b2, z14, headsApply,
      Head.attn, hs, hd1_V, hd1V, attnRows, ravg_singleton hr, radd, raffine, rdot,
      init_eq hr p w hw, X1, st, pcv, sw_zero hr, hr.zero, hr.idem, hr.one, fl_Hv hr,
      fl_Fv hr, fl_sw hr]

/-! ### Block 2: scores -/

set_option maxHeartbeats 1000000 in
theorem scoreA_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 qi qn b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 qk qn' : ℝ) :
    hdA.score fl dA (st a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 qi qn)
      (st b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 qk qn') =
    fl (fl (sw fl 1 (dA 11 12) * qk) + fl (qn * fl (sw fl (-2) (dA 13 4) * b4))) := by
  simp [Head.score, hdA_A, hdAA, z14, st, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem]

set_option maxHeartbeats 1000000 in
theorem scoreB_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 qi qn b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 qk qn' : ℝ) :
    hdB.score fl dA (st a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 qi qn)
      (st b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 qk qn') =
    fl (fl (sw fl 1 (dA 11 12) * qk) + fl (qn * fl (sw fl (-2) (dA 13 5) * b5))) := by
  simp [Head.score, hdB_A, hdBA, z14, st, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem]

set_option maxHeartbeats 1000000 in
theorem scoreC_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 qi qn b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 qk qn' : ℝ) :
    hdC.score fl dA (st a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 qi qn)
      (st b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 qk qn') =
    fl (fl (sw fl 1 (dA 11 12) * qk) + fl (qn * fl (sw fl (-2) (dA 13 6) * b6))) := by
  simp [Head.score, hdC_A, hdCA, z14, st, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem]

/-! ### Block 2: selection -/

set_option maxHeartbeats 2000000 in
theorem head_sel {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (hd : Head) (hmask : hd.mask = Mask.causal) (dA : ℕ → ℕ → ℝ)
    (hdb : ∀ r c, |dA r c| ≤ 1 / 200) (cc t : ℕ)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) (x : ℕ → Vec)
    (hsc : ∀ m, m ≤ i → hd.score fl dA (x i) (x m) =
      fl (fl (sw fl 1 (dA 11 12) * fl (m : ℝ)) +
        fl (fl ((w.length + 1 : ℕ) : ℝ) * fl (sw fl (-2) (dA 13 cc) * pcv fl p w t m)))) :
    ∃ m, m ≤ i ∧ (m = 0 ∨ tokAt w (m - 1) = t) ∧
      (∀ k, k ≤ i → (k = 0 ∨ tokAt w (k - 1) = t) → k ≤ m) ∧
      hd.sel fl dA (w.length + 1) x i = [m] := by
  obtain ⟨m, hm, hPm, hmax⟩ := exists_last (fun m => m = 0 ∨ tokAt w (m - 1) = t) (Or.inl rfl) i
  refine ⟨m, hm, hPm, hmax, ?_⟩
  have hN2 : (2 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    have : 2 ≤ w.length + 1 := by omega
    exact_mod_cast this
  have hPN := abs_le.mp (hr.natCast_near (w.length + 1))
  apply Head.sel_unique
  · rw [hmask, Lane4.Seq.mem_cand_causal]
    exact hm
  · intro k hk hne
    rw [hmask, Lane4.Seq.mem_cand_causal] at hk
    rw [hsc k hk, hsc m hm, pcv_zero hr p w t m hPm, sc_m hr]
    obtain ⟨hs1a, hs1b⟩ := sw1_bd hr hu0 hu1 (hdb 11 12)
    obtain ⟨hCa, hCb⟩ := swm2_bd hr hu0 hu1 (hdb 13 cc)
    have hs0 : 0 ≤ sw fl 1 (dA 11 12) := by linarith
    have hm' := hr.pos_le hu0 (show m ≤ w.length + 1 by omega) hn
    have hk' := hr.pos_le hu0 (show k ≤ w.length + 1 by omega) hn
    by_cases hPk : (k = 0 ∨ tokAt w (k - 1) = t)
    · -- both matched: the later position wins
      have hkm : k < m := lt_of_le_of_ne (hmax k hk hPk) hne
      rw [pcv_zero hr p w t k hPk, sc_m hr]
      have hg := hr.pos_gap hu0 hkm (show m ≤ w.length + 1 by omega) hn
      apply hr.lt_of_gap hu0 (B := 2 * (((w.length + 1 : ℕ) : ℝ) + 1 / 256))
      · rw [abs_of_nonneg (mul_nonneg hs0 hk'.1)]
        exact mul_le_mul (by linarith) hk'.2 hk'.1 (by norm_num)
      · rw [abs_of_nonneg (mul_nonneg hs0 hm'.1)]
        exact mul_le_mul (by linarith) hm'.2 hm'.1 (by norm_num)
      · have h1 := mul_le_mul_of_nonneg_left hg hs0
        rw [mul_add] at h1
        have h2 : 2 * (u * (2 * (((w.length + 1 : ℕ) : ℝ) + 1 / 256))) =
            4 * (u * ((w.length + 1 : ℕ) : ℝ)) + 4 * u / 256 := by ring
        rw [h2]
        first
          | nlinarith [h1, hn, hu0, hu1, hs1a]
          | linarith [h1, hn, hu0, hu1, hs1a]
    · -- k is not matched: its score is very negative
      have hk0 : k ≠ 0 := fun h0 => hPk (Or.inl h0)
      have hkt : tokAt w (k - 1) ≠ t := fun h0 => hPk (Or.inr h0)
      have hpc := pcv_near hr hu0 hu1 p hp w t k hk0 hkt
      obtain ⟨hq1, hq2⟩ := abs_le.mp hpc
      have hCneg : sw fl (-2) (dA 13 cc) ≤ 0 := by linarith
      have hprod1 : sw fl (-2) (dA 13 cc) * pcv fl p w t k ≤ sw fl (-2) (dA 13 cc) * (974 / 1000) :=
        mul_le_mul_of_nonpos_left (by linarith) hCneg
      have hprod2 : sw fl (-2) (dA 13 cc) * (1026 / 1000) ≤ sw fl (-2) (dA 13 cc) * pcv fl p w t k :=
        mul_le_mul_of_nonpos_left (by linarith) hCneg
      have hXb : |sw fl (-2) (dA 13 cc) * pcv fl p w t k| ≤ 3 :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      have hXu := hr.upper hu0 hXb
      have hXl := hr.lower hu0 hXb
      have hXup : fl (sw fl (-2) (dA 13 cc) * pcv fl p w t k) ≤ -192 / 100 := by linarith
      have hXlo : -21 / 10 ≤ fl (sw fl (-2) (dA 13 cc) * pcv fl p w t k) := by linarith
      have hPN0 : 0 ≤ fl (((w.length + 1 : ℕ) : ℝ)) := by linarith [hPN.1]
      have hY1 := mul_le_mul_of_nonneg_left hXup hPN0
      have hY2 := mul_le_mul_of_nonneg_left hXlo hPN0
      have hYb : |fl (((w.length + 1 : ℕ) : ℝ)) *
          fl (sw fl (-2) (dA 13 cc) * pcv fl p w t k)| ≤ 3 * ((w.length + 1 : ℕ) : ℝ) :=
        abs_le.mpr ⟨by linarith [hPN.2], by linarith [hPN.1]⟩
      have hFY := hr.upper hu0 hYb
      have hA0 : 0 ≤ sw fl 1 (dA 11 12) * fl (k : ℝ) := mul_nonneg hs0 hk'.1
      have hA1 : sw fl 1 (dA 11 12) * fl (k : ℝ) ≤
          (1 + 3 / 250) * (((w.length + 1 : ℕ) : ℝ) + 1 / 256) :=
        mul_le_mul hs1b hk'.2 hk'.1 (by norm_num)
      have hAb : |sw fl 1 (dA 11 12) * fl (k : ℝ)| ≤ 2 * ((w.length + 1 : ℕ) : ℝ) :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      have hFZ := hr.upper hu0 hAb
      have hsum : fl (sw fl 1 (dA 11 12) * fl (k : ℝ)) +
          fl (fl (((w.length + 1 : ℕ) : ℝ)) * fl (sw fl (-2) (dA 13 cc) * pcv fl p w t k)) < 0 := by
        nlinarith [hFY, hFZ, hY1, hn, hu0, hu1, hPN.1, hPN.2, hA1, hN2]
      have hneg := fl_neg_of_neg hr hu1 hsum
      have hmz : 0 ≤ fl (sw fl 1 (dA 11 12) * fl (m : ℝ)) :=
        hr.nonneg (mul_nonneg hs0 hm'.1)
      exact lt_of_lt_of_le hneg hmz

/-! ### Block 2: head outputs, MLP, readout -/

set_option maxHeartbeats 2000000 in
theorem z_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (x1 : ℕ → Vec) (hx1 : ∀ m, m ≤ w.length → x1 m = X1 fl p w m)
    (i mA mB mC : ℕ) (hi : i ≤ w.length) (hA : mA ≤ w.length) (hB : mB ≤ w.length)
    (hC : mC ≤ w.length)
    (hselA : hdA.sel fl (p.A 1 0) (w.length + 1) x1 i = [mA])
    (hselB : hdB.sel fl (p.A 1 1) (w.length + 1) x1 i = [mB])
    (hselC : hdC.sel fl (p.A 1 2) (w.length + 1) x1 i = [mC]) :
    headsApply fl blk2.heads (p.A 1) (p.V 1) (w.length + 1) x1 i (x1 i) 0 =
      st (Hv fl p w i) (Fv fl p w 1 i) (Fv fl p w 2 i) (Fv fl p w 3 i)
        (pcv fl p w 1 i) (pcv fl p w 2 i) (pcv fl p w 3 i)
        (Sv fl p 0 (Hv fl p w mA)) (Sv fl p 1 (Hv fl p w mB)) (Sv fl p 2 (Hv fl p w mC)) 0
        (fl (i : ℝ)) (fl ((w.length + 1 : ℕ) : ℝ)) := by
  simp [blk2_heads, headsApply, Head.attn, hselA, hselB, hselC, hdA_V, hdAV, hdB_V, hdBV,
    hdC_V, hdCV, z14, attnRows, ravg_singleton hr, hx1 i hi, hx1 mA hA, hx1 mB hB, hx1 mC hC,
    X1, radd, st, rdot, Sv, sw_zero hr, hr.zero, hr.idem, hr.one, fl_Hv hr, fl_Fv hr,
    fl_pcv hr, fl_sw hr]

theorem blk2_apply (fl : ℝ → ℝ) (p : Pert) (n : ℕ) (x : ℕ → Vec) (i : ℕ) :
    blk2.apply fl p 1 n x i =
      radd fl (headsApply fl blk2.heads (p.A 1) (p.V 1) n x i (x i) 0)
        (raffine fl blk2.W2 blk2.b2
          ((raffine fl blk2.W1 blk2.b1 (headsApply fl blk2.heads (p.A 1) (p.V 1) n x i (x i) 0)
            (p.W1 1) (p.b1 1) 0).map Lane4.relu)
          (p.W2 1) (p.b2 1) 0) := rfl

set_option maxHeartbeats 2000000 in
theorem fin_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert)
    (a0 a1 a2 a3 a4 a5 a6 s1 s2 s3 pj pn : ℝ) :
    fl (rdot fl net.outW
        (radd fl (st a0 a1 a2 a3 a4 a5 a6 s1 s2 s3 0 pj pn)
          (raffine fl blk2.W2 blk2.b2
            ((raffine fl blk2.W1 blk2.b1 (st a0 a1 a2 a3 a4 a5 a6 s1 s2 s3 0 pj pn)
              (p.W1 1) (p.b1 1) 0).map Lane4.relu)
            (p.W2 1) (p.b2 1) 0)) p.oW 0 0 + sw fl net.outB p.oB)
    = fl (sw fl 1 (p.oW 10) * Yv fl (p.W2 1 10 0) (p.W2 1 10 1) (p.W2 1 10 2)
        (Lane4.relu (PRE fl (p.W1 1 0 1) (p.W1 1 0 7) a1 s1))
        (Lane4.relu (PRE fl (p.W1 1 1 2) (p.W1 1 1 8) a2 s2))
        (Lane4.relu (PRE fl (p.W1 1 2 3) (p.W1 1 2 9) a3 s3))) := by
  simp [net_outW, netOutW, net_outB, blk2_W1, blk2W1, blk2_b1, blk2_W2, blk2W2, blk2_b2, z14,
    st, radd, raffine, rdot, PRE, Yv, sw_zero hr, hr.zero, hr.idem, hr.one, fl_sw hr]

/-! ### Arithmetic of the output -/

theorem PRE_self {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (d3 d1 s : ℝ) :
    PRE fl d3 d1 0 s = fl (sw fl 1 d1 * s) := by
  simp [PRE, hr.zero, hr.idem]

theorem Yv_1 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (d0 d1 d2 H : ℝ) :
    Yv fl d0 d1 d2 H 0 0 = fl (sw fl 1 d0 * H) := by
  simp [Yv, hr.zero, hr.idem]

theorem Yv_2 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (d0 d1 d2 H : ℝ) :
    Yv fl d0 d1 d2 0 H 0 = fl (sw fl 1 d1 * H) := by
  simp [Yv, hr.zero, hr.idem]

theorem Yv_3 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (d0 d1 d2 H : ℝ) :
    Yv fl d0 d1 d2 0 0 H = fl (sw fl 1 d2 * H) := by
  simp [Yv, hr.zero, hr.idem]

theorem relu_PRE_nonpos {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {d3 d1 f s : ℝ} (hd3 : |d3| ≤ 1 / 200) (hd1 : |d1| ≤ 1 / 200)
    (hf : |f - 1| ≤ 3 / 250) (hs0 : 0 ≤ s) (hs1 : s ≤ 21 / 10) :
    Lane4.relu (PRE fl d3 d1 f s) = 0 := by
  unfold PRE
  obtain ⟨hw3a, hw3b⟩ := swm3_bd hr hu0 hu1 hd3
  obtain ⟨hw1a, hw1b⟩ := sw1_bd hr hu0 hu1 hd1
  obtain ⟨hfa, hfb⟩ := abs_le.mp hf
  have hA1 : sw fl (-3) d3 * f ≤ (-2964 / 1000) * f :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hA2 : sw fl (-3) d3 * (1012 / 1000) ≤ sw fl (-3) d3 * f :=
    mul_le_mul_of_nonpos_left (by linarith) (by linarith)
  have hAb : |sw fl (-3) d3 * f| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hB0 : 0 ≤ sw fl 1 d1 * s := mul_nonneg (by linarith) hs0
  have hB1 : sw fl 1 d1 * s ≤ (1 + 3 / 250) * (21 / 10) :=
    mul_le_mul hw1b hs1 hs0 (by norm_num)
  have hBb : |sw fl 1 d1 * s| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hFA := hr.upper hu0 hAb
  have hFB := hr.upper hu0 hBb
  have hsum : fl (sw fl (-3) d3 * f) + fl (sw fl 1 d1 * s) ≤ 0 := by linarith
  have hfin : fl (fl (sw fl (-3) d3 * f) + fl (sw fl 1 d1 * s)) ≤ 0 := by
    have := hr.mono _ 0 hsum
    rwa [hr.zero] at this
  exact Lane4.relu_of_nonpos hfin

theorem chain {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {T Hs v1 v2 v3 v4 : ℝ} (hT0 : 0 ≤ T) (hT2 : T ≤ 2) (hH : |Hs - T| ≤ 3 / 250 * T)
    (h1 : |v1 - 1| ≤ 3 / 250) (h2 : |v2 - 1| ≤ 3 / 250) (h3 : |v3 - 1| ≤ 3 / 250)
    (h4 : |v4 - 1| ≤ 3 / 250) :
    |fl (v4 * fl (v3 * Lane4.relu (fl (v2 * fl (v1 * Hs))))) - T| ≤ 1 / 4 := by
  have hH' : |Hs - T| ≤ 3 / 250 * |T| := by
    rw [abs_of_nonneg hT0]
    exact hH
  have e1 := rel_mul (rel1 h1) hH' (c := 1 / 40) (by norm_num)
  have f1 := rel_fl hr hu0 e1 (c := 13 / 500) (by linarith)
  have e2 := rel_mul (rel1 h2) f1 (c := 1 / 25) (by norm_num)
  have f2 := rel_fl hr hu0 e2 (c := 21 / 500) (by linarith)
  have hP : 0 ≤ fl (v2 * fl (v1 * Hs)) := by
    have := (abs_le.mp f2).1
    simp only [one_mul, abs_of_nonneg hT0] at this
    linarith
  rw [Lane4.relu_of_nonneg hP]
  have e3 := rel_mul (rel1 h3) f2 (c := 11 / 200) (by norm_num)
  have f3 := rel_fl hr hu0 e3 (c := 7 / 125) (by linarith)
  have e4 := rel_mul (rel1 h4) f3 (c := 7 / 100) (by norm_num)
  have f4 := rel_fl hr hu0 e4 (c := 71 / 1000) (by linarith)
  simp only [one_mul, abs_of_nonneg hT0] at f4
  linarith

theorem caseA {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200))
    {T Hs a2 a3 s2 s3 : ℝ} (hT0 : 0 ≤ T) (hT2 : T ≤ 2) (hH : |Hs - T| ≤ 3 / 250 * T)
    (ha2 : |a2 - 1| ≤ 3 / 250) (ha3 : |a3 - 1| ≤ 3 / 250)
    (hs2 : 0 ≤ s2 ∧ s2 ≤ 21 / 10) (hs3 : 0 ≤ s3 ∧ s3 ≤ 21 / 10) :
    |fl (sw fl 1 (p.oW 10) * Yv fl (p.W2 1 10 0) (p.W2 1 10 1) (p.W2 1 10 2)
        (Lane4.relu (PRE fl (p.W1 1 0 1) (p.W1 1 0 7) 0 (Sv fl p 0 Hs)))
        (Lane4.relu (PRE fl (p.W1 1 1 2) (p.W1 1 1 8) a2 s2))
        (Lane4.relu (PRE fl (p.W1 1 2 3) (p.W1 1 2 9) a3 s3))) - T| ≤ 1 / 4 := by
  rw [relu_PRE_nonpos hr hu0 hu1 (hp.W1 1 1 2) (hp.W1 1 1 8) ha2 hs2.1 hs2.2,
    relu_PRE_nonpos hr hu0 hu1 (hp.W1 1 2 3) (hp.W1 1 2 9) ha3 hs3.1 hs3.2,
    PRE_self hr, Yv_1 hr]
  unfold Sv
  exact chain hr hu0 hu1 hT0 hT2 hH (sw1_rel hr hu0 hu1 (hp.V 1 0 (7 + 0) 0))
    (sw1_rel hr hu0 hu1 (hp.W1 1 0 7)) (sw1_rel hr hu0 hu1 (hp.W2 1 10 0))
    (sw1_rel hr hu0 hu1 (hp.oW 10))

theorem caseB {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200))
    {T Hs a1 a3 s1 s3 : ℝ} (hT0 : 0 ≤ T) (hT2 : T ≤ 2) (hH : |Hs - T| ≤ 3 / 250 * T)
    (ha1 : |a1 - 1| ≤ 3 / 250) (ha3 : |a3 - 1| ≤ 3 / 250)
    (hs1 : 0 ≤ s1 ∧ s1 ≤ 21 / 10) (hs3 : 0 ≤ s3 ∧ s3 ≤ 21 / 10) :
    |fl (sw fl 1 (p.oW 10) * Yv fl (p.W2 1 10 0) (p.W2 1 10 1) (p.W2 1 10 2)
        (Lane4.relu (PRE fl (p.W1 1 0 1) (p.W1 1 0 7) a1 s1))
        (Lane4.relu (PRE fl (p.W1 1 1 2) (p.W1 1 1 8) 0 (Sv fl p 1 Hs)))
        (Lane4.relu (PRE fl (p.W1 1 2 3) (p.W1 1 2 9) a3 s3))) - T| ≤ 1 / 4 := by
  rw [relu_PRE_nonpos hr hu0 hu1 (hp.W1 1 0 1) (hp.W1 1 0 7) ha1 hs1.1 hs1.2,
    relu_PRE_nonpos hr hu0 hu1 (hp.W1 1 2 3) (hp.W1 1 2 9) ha3 hs3.1 hs3.2,
    PRE_self hr, Yv_2 hr]
  unfold Sv
  exact chain hr hu0 hu1 hT0 hT2 hH (sw1_rel hr hu0 hu1 (hp.V 1 1 (7 + 1) 0))
    (sw1_rel hr hu0 hu1 (hp.W1 1 1 8)) (sw1_rel hr hu0 hu1 (hp.W2 1 10 1))
    (sw1_rel hr hu0 hu1 (hp.oW 10))

theorem caseC {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200))
    {T Hs a1 a2 s1 s2 : ℝ} (hT0 : 0 ≤ T) (hT2 : T ≤ 2) (hH : |Hs - T| ≤ 3 / 250 * T)
    (ha1 : |a1 - 1| ≤ 3 / 250) (ha2 : |a2 - 1| ≤ 3 / 250)
    (hs1 : 0 ≤ s1 ∧ s1 ≤ 21 / 10) (hs2 : 0 ≤ s2 ∧ s2 ≤ 21 / 10) :
    |fl (sw fl 1 (p.oW 10) * Yv fl (p.W2 1 10 0) (p.W2 1 10 1) (p.W2 1 10 2)
        (Lane4.relu (PRE fl (p.W1 1 0 1) (p.W1 1 0 7) a1 s1))
        (Lane4.relu (PRE fl (p.W1 1 1 2) (p.W1 1 1 8) a2 s2))
        (Lane4.relu (PRE fl (p.W1 1 2 3) (p.W1 1 2 9) 0 (Sv fl p 2 Hs)))) - T| ≤ 1 / 4 := by
  rw [relu_PRE_nonpos hr hu0 hu1 (hp.W1 1 0 1) (hp.W1 1 0 7) ha1 hs1.1 hs1.2,
    relu_PRE_nonpos hr hu0 hu1 (hp.W1 1 1 2) (hp.W1 1 1 8) ha2 hs2.1 hs2.2,
    PRE_self hr, Yv_3 hr]
  unfold Sv
  exact chain hr hu0 hu1 hT0 hT2 hH (sw1_rel hr hu0 hu1 (hp.V 1 2 (7 + 2) 0))
    (sw1_rel hr hu0 hu1 (hp.W1 1 2 9)) (sw1_rel hr hu0 hu1 (hp.W2 1 10 2))
    (sw1_rel hr hu0 hu1 (hp.oW 10))

/-! ### Assembly -/

set_option maxHeartbeats 4000000 in
theorem main_out {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (x1 : ℕ → Vec) (hx1 : ∀ m, m ≤ w.length → x1 m = X1 fl p w m)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    |fl (rdot fl net.outW (blk2.apply fl p 1 (w.length + 1) x1 i) p.oW 0 0 + sw fl net.outB p.oB)
      - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  have hscA : ∀ m, m ≤ i → hdA.score fl (p.A 1 0) (x1 i) (x1 m) =
      fl (fl (sw fl 1 (p.A 1 0 11 12) * fl (m : ℝ)) +
        fl (fl ((w.length + 1 : ℕ) : ℝ) * fl (sw fl (-2) (p.A 1 0 13 4) * pcv fl p w 1 m))) := by
    intro m hm
    rw [hx1 i hi, hx1 m (by omega)]
    unfold X1
    rw [scoreA_eq hr]
  have hscB : ∀ m, m ≤ i → hdB.score fl (p.A 1 1) (x1 i) (x1 m) =
      fl (fl (sw fl 1 (p.A 1 1 11 12) * fl (m : ℝ)) +
        fl (fl ((w.length + 1 : ℕ) : ℝ) * fl (sw fl (-2) (p.A 1 1 13 5) * pcv fl p w 2 m))) := by
    intro m hm
    rw [hx1 i hi, hx1 m (by omega)]
    unfold X1
    rw [scoreB_eq hr]
  have hscC : ∀ m, m ≤ i → hdC.score fl (p.A 1 2) (x1 i) (x1 m) =
      fl (fl (sw fl 1 (p.A 1 2 11 12) * fl (m : ℝ)) +
        fl (fl ((w.length + 1 : ℕ) : ℝ) * fl (sw fl (-2) (p.A 1 2 13 6) * pcv fl p w 3 m))) := by
    intro m hm
    rw [hx1 i hi, hx1 m (by omega)]
    unfold X1
    rw [scoreC_eq hr]
  have ht1 : 1 ≤ tokAt w i := tok_ge1 w hw i hi1 hi
  have ht3 : tokAt w i ≤ 3 := tok_le3 w hw i
  obtain ⟨mA, hmAi, hmAP, hmAmax, hselA⟩ :=
    head_sel hr hu0 hu1 p hp w hw hn hdA hdA_mask (p.A 1 0) (fun r c => hp.A 1 0 r c) 4 1
      i hi1 hi x1 hscA
  obtain ⟨mB, hmBi, hmBP, hmBmax, hselB⟩ :=
    head_sel hr hu0 hu1 p hp w hw hn hdB hdB_mask (p.A 1 1) (fun r c => hp.A 1 1 r c) 5 2
      i hi1 hi x1 hscB
  obtain ⟨mC, hmCi, hmCP, hmCmax, hselC⟩ :=
    head_sel hr hu0 hu1 p hp w hw hn hdC hdC_mask (p.A 1 2) (fun r c => hp.A 1 2 r c) 6 3
      i hi1 hi x1 hscC
  have hz := z_eq hr p w x1 hx1 i mA mB mC hi (by omega) (by omega) (by omega)
    hselA hselB hselC
  rw [blk2_apply, hz, fin_eq hr p]
  have hbA := Sv_bd hr hu0 hu1 p hp w 0 mA
  have hbB := Sv_bd hr hu0 hu1 p hp w 1 mB
  have hbC := Sv_bd hr hu0 hu1 p hp w 2 mC
  have hcases : tokAt w i = 1 ∨ tokAt w i = 2 ∨ tokAt w i = 3 := by omega
  rcases hcases with hc | hc | hc
  · have hT := target_eq w i hi1 ht1 mA hmAi (by rw [hc]; exact hmAP)
      (fun k hk hPk => hmAmax k hk (by rwa [hc] at hPk))
    rw [hT, Fv_self hr p w 1 i hc]
    have hT0 : (0 : ℝ) ≤ ((h (tokAt w mA) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hT2 : ((h (tokAt w mA) : ℕ) : ℝ) ≤ 2 := by exact_mod_cast h_le _
    exact caseA hr hu0 hu1 p hp hT0 hT2 (Hv_near hr hu0 hu1 p hp w mA)
      (Fv_near hr hu0 hu1 p hp w 2 i (by omega)) (Fv_near hr hu0 hu1 p hp w 3 i (by omega))
      hbB hbC
  · have hT := target_eq w i hi1 ht1 mB hmBi (by rw [hc]; exact hmBP)
      (fun k hk hPk => hmBmax k hk (by rwa [hc] at hPk))
    rw [hT, Fv_self hr p w 2 i hc]
    have hT0 : (0 : ℝ) ≤ ((h (tokAt w mB) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hT2 : ((h (tokAt w mB) : ℕ) : ℝ) ≤ 2 := by exact_mod_cast h_le _
    exact caseB hr hu0 hu1 p hp hT0 hT2 (Hv_near hr hu0 hu1 p hp w mB)
      (Fv_near hr hu0 hu1 p hp w 1 i (by omega)) (Fv_near hr hu0 hu1 p hp w 3 i (by omega))
      hbA hbC
  · have hT := target_eq w i hi1 ht1 mC hmCi (by rw [hc]; exact hmCP)
      (fun k hk hPk => hmCmax k hk (by rwa [hc] at hPk))
    rw [hT, Fv_self hr p w 3 i hc]
    have hT0 : (0 : ℝ) ≤ ((h (tokAt w mC) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hT2 : ((h (tokAt w mC) : ℕ) : ℝ) ≤ 2 := by exact_mod_cast h_le _
    exact caseC hr hu0 hu1 p hp hT0 hT2 (Hv_near hr hu0 hu1 p hp w mC)
      (Fv_near hr hu0 hu1 p hp w 1 i (by omega)) (Fv_near hr hu0 hu1 p hp w 2 i (by omega))
      hbA hbB

theorem out_unfold (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (i : ℕ) :
    net.out fl p w i =
      fl (rdot fl net.outW (blk2.apply fl p 1 (w.length + 1)
        (blk1.apply fl p 0 (w.length + 1) (net.init fl p w)) i) p.oW 0 0 + sw fl net.outB p.oB) := by
  unfold TNet.out TNet.run
  rw [net_blocks]
  first
    | rfl
    | simp [runFrom]

theorem net_ok : Statement net := by
  intro u fl hr hu0 hu1 p hp w hw hn i hi1 hi
  rw [out_unfold]
  exact main_out hr hu0 hu1 p hp w hw hn (blk1.apply fl p 0 (w.length + 1) (net.init fl p w))
    (fun m hm => x1_eq hr hu0 hu1 p hp w hw hn m hm) i hi1 hi

end Lane4.Case
