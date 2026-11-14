namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

/-- State: [d, q, g, c, o, 1, fl i, fl n] (width 8). -/
def z8 : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0]

def hdA : Head :=
  { A := [z8, z8, z8, z8, z8, [0, 0, 0, 0, 0, 0, 1, 0], z8, [0, -4, 0, 0, 0, 0, 0, 0]],
    V := [z8, z8, z8, [0, 0, 1, 0, 0, 0, 0, 0], z8, z8, z8, z8],
    mask := Mask.strict }

def blk : Block :=
  { heads := [hdA],
    W1 := [[1, 0, 0, 1, 0, 0, 0, 0]],
    b1 := [-1],
    W2 := [[0], [0], [0], [0], [1], [0], [0], [0]],
    b2 := z8 }

def net : TNet :=
  { embed := [[0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [1, 0, 0, 0, 0],
              [0, 0, 0, 0, 0], [0, 1, 0, 0, 0]],
    blocks := [blk],
    outW := [1, 0, 0, 1, -2, 0, 0, 0],
    outB := 0 }

def dE (t : ℕ) : ℚ := if t = 3 then 1 else 0
def qE (t : ℕ) : ℚ := if t = 5 then 1 else 0
def gE (t : ℕ) : ℚ := if t = 1 ∨ t = 2 then 1 else 0

noncomputable def dv (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (dE (tokAt w j)) (p.E (tokAt w j) 0)
noncomputable def qv (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (qE (tokAt w j)) (p.E (tokAt w j) 1)
noncomputable def gv (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (gE (tokAt w j)) (p.E (tokAt w j) 2)

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem fl_dv {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ) :
    fl (dv fl p w j) = dv fl p w j := by
  unfold dv; exact fl_sw hr _ _

theorem fl_qv {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ) :
    fl (qv fl p w j) = qv fl p w j := by
  unfold qv; exact fl_sw hr _ _

theorem fl_gv {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ) :
    fl (gv fl p w j) = gv fl p w j := by
  unfold gv; exact fl_sw hr _ _

theorem qv_zero {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ)
    (h : tokAt w j ≠ 5) : qv fl p w j = 0 := by
  unfold qv qE
  rw [if_neg h]
  exact sw_zero hr _

theorem qv_five {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ)
    (h : tokAt w j = 5) : qv fl p w j = sw fl 1 (p.E 5 1) := by
  unfold qv qE
  rw [if_pos h, h]

theorem init_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [dv fl p w j, qv fl p w j, gv fl p w j, 0, 0] ++ pos fl j (w.length + 1) := by
  have h6 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 ∨
      tokAt w j = 5 := by
    have := tok_le w hw j
    omega
  rcases h6 with h | h | h | h | h | h <;>
    simp [TNet.init, net, dv, qv, gv, dE, qE, gE, swRow, h, sw_zero hr]

/-! ### Rounding helpers -/

theorem flb {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {x : ℝ} (hx : |x| ≤ 5) : |fl x - x| ≤ 1 / 1000000 := by
  have := hr.err hu0 hx
  linarith

theorem flprod {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {X w Y e M : ℝ} (hX : |X - w| ≤ e) (hY : |Y| ≤ M) (hw : |w| ≤ 2)
    (he : e ≤ 1 / 10) (hM : M ≤ 2) : |fl (X * Y) - w * Y| ≤ e * M + 1 / 1000000 := by
  have he0 : 0 ≤ e := le_trans (abs_nonneg _) hX
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) hY
  have h1 : |X * Y - w * Y| ≤ e * |Y| := by
    have : X * Y - w * Y = (X - w) * Y := by ring
    rw [this, abs_mul]
    exact mul_le_mul_of_nonneg_right hX (abs_nonneg _)
  have h2 : e * |Y| ≤ e * M := mul_le_mul_of_nonneg_left hY he0
  have h3 : |w * Y| ≤ 2 * 2 := by
    rw [abs_mul]
    exact mul_le_mul hw (le_trans hY hM) (abs_nonneg _) (by norm_num)
  have h4 : e * M ≤ 1 / 10 * 2 := mul_le_mul he hM hM0 (by norm_num)
  have h5 : |X * Y| ≤ 5 := by
    have := abs_sub_abs_le_abs_sub (X * Y) (w * Y)
    linarith
  have h6 := hr.err hu0 h5
  have h7 : |fl (X * Y) - w * Y| ≤ |fl (X * Y) - X * Y| + |X * Y - w * Y| := abs_sub_le _ _ _
  linarith

theorem swv {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    (m : ℚ) (v av : ℝ) (hv : (m : ℝ) = v) (hav : |v| = av) (d : ℝ) (hd : |d| ≤ 1 / 200) :
    |sw fl m d - v| ≤ 3 / 250 * av := by
  have h := sw_rel hr hu0 m hd (ε := 3 / 250) (by linarith)
  rw [hv, hav] at h
  exact h

theorem sw1 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    (d : ℝ) (hd : |d| ≤ 1 / 200) : |sw fl 1 d - 1| ≤ 3 / 250 := by
  have h := swv hr hu0 hu1 1 1 1 (by norm_num) (by norm_num) d hd
  linarith

theorem swm1 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    (d : ℝ) (hd : |d| ≤ 1 / 200) : |sw fl (-1) d - (-1)| ≤ 3 / 250 := by
  have h := swv hr hu0 hu1 (-1) (-1) 1 (by norm_num) (by norm_num) d hd
  linarith

theorem swm2 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    (d : ℝ) (hd : |d| ≤ 1 / 200) : |sw fl (-2) d - (-2)| ≤ 3 / 125 := by
  have h := swv hr hu0 hu1 (-2) (-2) 2 (by norm_num) (by norm_num) d hd
  linarith

theorem swm4 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    (d : ℝ) (hd : |d| ≤ 1 / 200) : |sw fl (-4) d - (-4)| ≤ 6 / 125 := by
  have h := swv hr hu0 hu1 (-4) (-4) 4 (by norm_num) (by norm_num) d hd
  linarith

theorem sw_nn {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    (m : ℚ) (hm : (0 : ℝ) ≤ (m : ℝ)) (d : ℝ) (hd : |d| ≤ 1 / 200) :
    |sw fl m d - (m : ℝ)| ≤ 3 / 250 * (m : ℝ) :=
  swv hr hu0 hu1 m (m : ℝ) (m : ℝ) rfl (abs_of_nonneg hm) d hd

/-! ### The score -/

theorem score_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (a b c e f qi qn a' b' c' e' f' qk qn' : ℝ) :
    hdA.score fl dA [a, b, c, e, f, 1, qi, qn] [a', b', c', e', f', 1, qk, qn']
      = fl (fl (sw fl 1 (dA 5 6) * qk) + fl (qn * fl (sw fl (-4) (dA 7 1) * b'))) := by
  simp [Head.score, hdA, z8, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem]

theorem prop_neg {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {S T Q fk fn n : ℝ}
    (hS1 : 247 / 250 ≤ S) (hS2 : S ≤ 253 / 250) (hT1 : T ≤ -39 / 10) (hT2 : -41 / 10 ≤ T)
    (hQ1 : 247 / 250 ≤ Q) (hQ2 : Q ≤ 253 / 250) (hk0 : 0 ≤ fk) (hk1 : fk ≤ n + 1 / 256)
    (hn1 : n - 1 / 256 ≤ fn) (hn2 : fn ≤ n + 1 / 256) (hn3 : 2 ≤ n) (hun : u * n ≤ 1 / 256) :
    fl (fl (S * fk) + fl (fn * fl (T * Q))) ≤ -1 := by
  have hQ0 : 0 ≤ Q := by linarith
  have e1 : T * Q ≤ -39 / 10 * Q := mul_le_mul_of_nonneg_right hT1 hQ0
  have e2 : -41 / 10 * Q ≤ T * Q := mul_le_mul_of_nonneg_right hT2 hQ0
  have hTQ : |T * Q| ≤ 21 / 5 := by
    rw [abs_le]
    constructor <;> linarith
  have hy1 := hr.upper hu0 hTQ
  have hy2 := hr.lower hu0 hTQ
  have hy7a : fl (T * Q) ≤ -38 / 10 := by linarith
  have hy7b : -43 / 10 ≤ fl (T * Q) := by linarith
  have hfn0 : 0 ≤ fn := by linarith
  have e3 : fn * fl (T * Q) ≤ fn * (-38 / 10) := mul_le_mul_of_nonneg_left hy7a hfn0
  have e4 : fn * (-43 / 10) ≤ fn * fl (T * Q) := mul_le_mul_of_nonneg_left hy7b hfn0
  have hb0 : |fn * fl (T * Q)| ≤ 5 * n := by
    rw [abs_le]
    constructor <;> linarith
  have hb1 := hr.upper hu0 hb0
  have hb : fl (fn * fl (T * Q)) ≤ -3 * n := by linarith
  have ha1 : S * fk ≤ 253 / 250 * (n + 1 / 256) := mul_le_mul hS2 hk1 hk0 (by norm_num)
  have ha0 : 0 ≤ S * fk := mul_nonneg (by linarith) hk0
  have haB : |S * fk| ≤ 2 * n := by
    rw [abs_of_nonneg ha0]
    linarith
  have ha2 := hr.upper hu0 haB
  have ha : fl (S * fk) ≤ 11 / 10 * n := by linarith
  have hs : fl (S * fk) + fl (fn * fl (T * Q)) ≤ -1 := by linarith
  calc fl (fl (S * fk) + fl (fn * fl (T * Q))) ≤ fl (-1) := hr.mono _ _ hs
    _ = -1 := by rw [hr.neg 1, hr.one]

theorem sel_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) (j : ℕ) (hj : j < i) (hjt : tokAt w j ≠ 5)
    (hall : ∀ k, j < k → k < i → tokAt w k = 5) :
    hdA.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = [j] := by
  apply Head.sel_unique
  · rw [show hdA.mask = Mask.strict from rfl, Lane4.Seq.mem_cand_strict]
    exact hj
  · intro k hk hne
    rw [show hdA.mask = Mask.strict from rfl, Lane4.Seq.mem_cand_strict] at hk
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    rw [score_eq hr, score_eq hr, qv_zero hr p w j hjt]
    simp only [mul_zero, hr.zero, add_zero, hr.idem]
    have hS := sw1 hr hu0 hu1 (p.A 0 0 5 6) (hp.A 0 0 5 6)
    obtain ⟨hS1, hS2⟩ := abs_le.mp hS
    have hS0 : 0 ≤ sw fl 1 (p.A 0 0 5 6) := by linarith
    have hj' := hr.pos_le hu0 (show j ≤ w.length + 1 by omega) hn
    have hk' := hr.pos_le hu0 (show k ≤ w.length + 1 by omega) hn
    by_cases hk5 : tokAt w k = 5
    · rw [qv_five hr p w k hk5]
      have hsj : 0 ≤ fl (sw fl 1 (p.A 0 0 5 6) * fl (j : ℝ)) :=
        hr.nonneg (mul_nonneg hS0 hj'.1)
      have hT := swm4 hr hu0 hu1 (p.A 0 0 7 1) (hp.A 0 0 7 1)
      obtain ⟨hT1, hT2⟩ := abs_le.mp hT
      have hQ := sw1 hr hu0 hu1 (p.E 5 1) (hp.E 5 1)
      obtain ⟨hQ1, hQ2⟩ := abs_le.mp hQ
      have hfn := abs_le.mp (hr.natCast_near (w.length + 1))
      obtain ⟨hf1, hf2⟩ := hfn
      have hn3 : (2 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
        have : 2 ≤ w.length + 1 := by omega
        exact_mod_cast this
      refine lt_of_le_of_lt (prop_neg hr hu0 hu1 (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) hk'.1 hk'.2 (by linarith) (by linarith) hn3 hn)
        (by linarith)
    · have hkj : k < j := by
        by_contra hcon
        exact hk5 (hall k (by omega) hk)
      rw [qv_zero hr p w k hk5]
      simp only [mul_zero, hr.zero, add_zero, hr.idem]
      have hg := hr.pos_gap hu0 hkj (show j ≤ w.length + 1 by omega) hn
      apply hr.lt_of_gap hu0 (B := 2 * (((w.length + 1 : ℕ) : ℝ) + 1 / 256))
      · rw [abs_of_nonneg (mul_nonneg hS0 hk'.1)]
        exact mul_le_mul (by linarith) hk'.2 hk'.1 (by norm_num)
      · rw [abs_of_nonneg (mul_nonneg hS0 hj'.1)]
        exact mul_le_mul (by linarith) hj'.2 hj'.1 (by norm_num)
      · have h1 := mul_le_mul_of_nonneg_left hg hS0
        nlinarith [h1, hn, hu0, hu1, hS1]

/-! ### The output in closed form -/

theorem out_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i j : ℕ)
    (hsel : hdA.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = [j]) :
    net.out fl p w i
      = fl (fl (fl (sw fl 1 (p.oW 0) * dv fl p w i) +
            fl (sw fl 1 (p.oW 3) * fl (sw fl 1 (p.V 0 0 3 2) * gv fl p w j))) +
          fl (sw fl (-2) (p.oW 4) * fl (sw fl 1 (p.W2 0 4 0) *
            Lane4.relu (fl (fl (fl (sw fl 1 (p.W1 0 0 0) * dv fl p w i) +
              fl (sw fl 1 (p.W1 0 0 3) * fl (sw fl 1 (p.V 0 0 3 2) * gv fl p w j))) +
              sw fl (-1) (p.b1 0 0)))))) := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [1, 0, 0, 1, -2, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  have hV : hdA.V = [z8, z8, z8, [0, 0, 1, 0, 0, 0, 0, 0], z8, z8, z8, z8] := rfl
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [runFrom, Block.apply, blk, headsApply, Head.attn, hsel, hV, attnRows,
    ravg_singleton hr]
  simp only [init_eq hr p w hw]
  simp [z8, pos, rdot, radd, raffine, sw_zero hr, hr.zero, hr.idem, hr.one, fl_sw hr,
    fl_dv hr, fl_qv hr, fl_gv hr]

/-! ### Arithmetic of the output -/

theorem relu_facts (x M : ℝ) (hM : 0 ≤ M) (hx : x ≤ M) :
    |Lane4.relu x| ≤ M ∧ ((Lane4.relu x = x ∧ 0 ≤ x) ∨ (Lane4.relu x = 0 ∧ x ≤ 0)) := by
  rcases le_total 0 x with hp | hp
  · refine ⟨?_, Or.inl ⟨Lane4.relu_of_nonneg hp, hp⟩⟩
    rw [Lane4.relu_of_nonneg hp, abs_of_nonneg hp]
    exact hx
  · refine ⟨?_, Or.inr ⟨Lane4.relu_of_nonpos hp, hp⟩⟩
    rw [Lane4.relu_of_nonpos hp, abs_zero]
    exact hM

theorem arith {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    (a b tv : ℝ)
    (htv : (a = 0 ∧ b = 0 ∧ tv = 0) ∨ (a = 0 ∧ b = 1 ∧ tv = 1) ∨ (a = 1 ∧ b = 0 ∧ tv = 1) ∨
      (a = 1 ∧ b = 1 ∧ tv = 0))
    (D G S2 S1d S1c Sb S3 O0 O3 O4 : ℝ)
    (hD : |D - a| ≤ 3 / 250 * a) (hG : |G - b| ≤ 3 / 250 * b)
    (hS2 : |S2 - 1| ≤ 3 / 250) (hS1d : |S1d - 1| ≤ 3 / 250) (hS1c : |S1c - 1| ≤ 3 / 250)
    (hSb : |Sb - (-1)| ≤ 3 / 250) (hS3 : |S3 - 1| ≤ 3 / 250) (hO0 : |O0 - 1| ≤ 3 / 250)
    (hO3 : |O3 - 1| ≤ 3 / 250) (hO4 : |O4 - (-2)| ≤ 3 / 125) :
    |fl (fl (fl (O0 * D) + fl (O3 * fl (S2 * G))) +
        fl (O4 * fl (S3 * Lane4.relu (fl (fl (fl (S1d * D) + fl (S1c * fl (S2 * G))) + Sb)))))
      - tv| ≤ 1 / 4 := by
  have hab : (0 ≤ a ∧ a ≤ 1) ∧ (0 ≤ b ∧ b ≤ 1) := by
    rcases htv with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;>
      (rw [h1, h2]; norm_num)
  obtain ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩ := hab
  obtain ⟨hD1, hD2⟩ := abs_le.mp hD
  obtain ⟨hG1, hG2⟩ := abs_le.mp hG
  obtain ⟨hSb1, hSb2⟩ := abs_le.mp hSb
  have hDabs : |D| ≤ 253 / 250 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hGabs : |G| ≤ 253 / 250 := abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨C, hCd⟩ : ∃ C, fl (S2 * G) = C := ⟨_, rfl⟩
  have hC := flprod hr hu0 hu1 hS2 hGabs (by norm_num) (by norm_num) (by norm_num)
  rw [hCd] at hC ⊢
  obtain ⟨hC1, hC2⟩ := abs_le.mp hC
  have hCabs : |C| ≤ 41 / 40 := abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨A1, hA1d⟩ : ∃ A1, fl (S1d * D) = A1 := ⟨_, rfl⟩
  have hA1 := flprod hr hu0 hu1 hS1d hDabs (by norm_num) (by norm_num) (by norm_num)
  rw [hA1d] at hA1 ⊢
  obtain ⟨hA11, hA12⟩ := abs_le.mp hA1
  obtain ⟨A2, hA2d⟩ : ∃ A2, fl (S1c * C) = A2 := ⟨_, rfl⟩
  have hA2 := flprod hr hu0 hu1 hS1c hCabs (by norm_num) (by norm_num) (by norm_num)
  rw [hA2d] at hA2 ⊢
  obtain ⟨hA21, hA22⟩ := abs_le.mp hA2
  obtain ⟨s1, hs1d⟩ : ∃ s1, fl (A1 + A2) = s1 := ⟨_, rfl⟩
  have hs1 := flb hr hu0 hu1 (x := A1 + A2) (abs_le.mpr ⟨by linarith, by linarith⟩)
  rw [hs1d] at hs1 ⊢
  obtain ⟨hs11, hs12⟩ := abs_le.mp hs1
  obtain ⟨pre, hpred⟩ : ∃ pre, fl (s1 + Sb) = pre := ⟨_, rfl⟩
  have hpre := flb hr hu0 hu1 (x := s1 + Sb) (abs_le.mpr ⟨by linarith, by linarith⟩)
  rw [hpred] at hpre ⊢
  obtain ⟨hp1, hp2⟩ := abs_le.mp hpre
  obtain ⟨hhabs, hcase⟩ := relu_facts pre (11 / 10) (by norm_num) (by linarith)
  obtain ⟨h, hhd⟩ : ∃ h, Lane4.relu pre = h := ⟨_, rfl⟩
  rw [hhd] at hhabs hcase ⊢
  obtain ⟨hh1, hh2⟩ := abs_le.mp hhabs
  obtain ⟨o, hod⟩ : ∃ o, fl (S3 * h) = o := ⟨_, rfl⟩
  have ho := flprod hr hu0 hu1 hS3 hhabs (by norm_num) (by norm_num) (by norm_num)
  rw [hod] at ho ⊢
  obtain ⟨ho1, ho2⟩ := abs_le.mp ho
  have hoabs : |o| ≤ 6 / 5 := abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨B3, hB3d⟩ : ∃ B3, fl (O4 * o) = B3 := ⟨_, rfl⟩
  have hB3 := flprod hr hu0 hu1 hO4 hoabs (by norm_num) (by norm_num) (by norm_num)
  rw [hB3d] at hB3 ⊢
  obtain ⟨hB31, hB32⟩ := abs_le.mp hB3
  obtain ⟨B1, hB1d⟩ : ∃ B1, fl (O0 * D) = B1 := ⟨_, rfl⟩
  have hB1 := flprod hr hu0 hu1 hO0 hDabs (by norm_num) (by norm_num) (by norm_num)
  rw [hB1d] at hB1 ⊢
  obtain ⟨hB11, hB12⟩ := abs_le.mp hB1
  obtain ⟨B2, hB2d⟩ : ∃ B2, fl (O3 * C) = B2 := ⟨_, rfl⟩
  have hB2 := flprod hr hu0 hu1 hO3 hCabs (by norm_num) (by norm_num) (by norm_num)
  rw [hB2d] at hB2 ⊢
  obtain ⟨hB21, hB22⟩ := abs_le.mp hB2
  obtain ⟨t1, ht1d⟩ : ∃ t1, fl (B1 + B2) = t1 := ⟨_, rfl⟩
  have ht1 := flb hr hu0 hu1 (x := B1 + B2) (abs_le.mpr ⟨by linarith, by linarith⟩)
  rw [ht1d] at ht1 ⊢
  obtain ⟨ht11, ht12⟩ := abs_le.mp ht1
  obtain ⟨out, houtd⟩ : ∃ out, fl (t1 + B3) = out := ⟨_, rfl⟩
  have hout := flb hr hu0 hu1 (x := t1 + B3) (abs_le.mpr ⟨by linarith, by linarith⟩)
  rw [houtd] at hout ⊢
  obtain ⟨hout1, hout2⟩ := abs_le.mp hout
  rw [abs_le]
  rcases hcase with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩ <;>
  rcases htv with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  constructor <;> linarith

/-! ### Carry specification -/

theorem cls_two_iff (t : ℕ) : cls t = 2 ↔ t = 5 := by
  unfold cls
  split_ifs <;> omega

theorem cls01 (t : ℕ) (ht5 : t ≠ 5) : cls t = 0 ∨ cls t = 1 := by
  unfold cls
  split_ifs <;> omega

theorem dg_eq (t : ℕ) : dg t = if t = 3 then 1 else 0 := by
  unfold dg
  split_ifs <;> omega

theorem dg01 (t : ℕ) : dg t = 0 ∨ dg t = 1 := by
  rw [dg_eq]
  split_ifs <;> simp

theorem dE_eq (t : ℕ) : ((dE t : ℚ) : ℝ) = ((dg t : ℕ) : ℝ) := by
  rw [dg_eq]
  unfold dE
  split_ifs <;> simp

theorem gE_eq (t : ℕ) (ht5 : t ≠ 5) (ht : t ≤ 5) : ((gE t : ℚ) : ℝ) = ((cls t : ℕ) : ℝ) := by
  interval_cases t <;> first | exact absurd rfl ht5 | simp [gE, cls]

theorem dE_nn (t : ℕ) : (0 : ℝ) ≤ ((dE t : ℚ) : ℝ) := by
  unfold dE
  split_ifs <;> norm_num

theorem gE_nn (t : ℕ) : (0 : ℝ) ≤ ((gE t : ℚ) : ℝ) := by
  unfold gE
  split_ifs <;> norm_num

theorem tv_cases (x y : ℕ) (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    ((x : ℝ) = 0 ∧ (y : ℝ) = 0 ∧ (((x + y) % 2 : ℕ) : ℝ) = 0) ∨
    ((x : ℝ) = 0 ∧ (y : ℝ) = 1 ∧ (((x + y) % 2 : ℕ) : ℝ) = 1) ∨
    ((x : ℝ) = 1 ∧ (y : ℝ) = 0 ∧ (((x + y) % 2 : ℕ) : ℝ) = 1) ∨
    ((x : ℝ) = 1 ∧ (y : ℝ) = 1 ∧ (((x + y) % 2 : ℕ) : ℝ) = 0) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num

theorem carry_spec (w : List ℕ) : ∀ m, m ≤ w.length → ∃ j, j ≤ m ∧ tokAt w j ≠ 5 ∧
    (∀ k, j < k → k ≤ m → tokAt w k = 5) ∧ carry (w.take m) = cls (tokAt w j) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨0, le_refl _, ?_, ?_, ?_⟩
    · rw [Lane4.Seq.tokAt_zero]
      omega
    · intro k hk1 hk2
      omega
    · simp [carry, Lane4.Seq.tokAt_zero, cls]
  | succ m ih =>
    intro hm
    obtain ⟨j, hjm, hjt, hall, hcar⟩ := ih (by omega)
    have hmlt : m < w.length := by omega
    have htok : tokAt w (m + 1) = w[m] := Lane4.Seq.tokAt_succ w m hmlt
    have htake : w.take (m + 1) = w.take m ++ [w[m]] := by
      rw [List.take_succ]
      simp [hmlt]
    have hc : carry (w.take (m + 1)) =
        if cls (tokAt w (m + 1)) = 2 then carry (w.take m) else cls (tokAt w (m + 1)) := by
      rw [htake, htok]
      simp [carry, List.foldl_append]
    by_cases h5 : tokAt w (m + 1) = 5
    · refine ⟨j, by omega, hjt, ?_, ?_⟩
      · intro k hk1 hk2
        by_cases hkm : k ≤ m
        · exact hall k hk1 hkm
        · have : k = m + 1 := by omega
          rw [this]
          exact h5
      · rw [hc, if_pos ((cls_two_iff _).2 h5)]
        exact hcar
    · refine ⟨m + 1, le_refl _, h5, ?_, ?_⟩
      · intro k hk1 hk2
        omega
      · rw [hc, if_neg (fun h => h5 ((cls_two_iff _).1 h))]

theorem getD_eq (w : List ℕ) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    w.getD (i - 1) 0 = tokAt w i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  simp [tokAt]

theorem net_ok : Statement net := by
  intro u fl hr hu0 hu1 p hp w hw hn i hi1 hi
  obtain ⟨j, hjle, hjt, hall, hcar⟩ := carry_spec w (i - 1) (by omega)
  have hsel := sel_eq hr hu0 hu1 p hp w hw hn i hi1 hi j (by omega) hjt
    (fun k hk1 hk2 => hall k hk1 (by omega))
  rw [out_eq hr p w hw i j hsel]
  have htgt : target w i = (dg (tokAt w i) + cls (tokAt w j)) % 2 := by
    unfold target
    rw [getD_eq w i hi1 hi, hcar]
  rw [htgt]
  have htj : tokAt w j ≤ 5 := tok_le w hw j
  have hae := dE_eq (tokAt w i)
  have hbe := gE_eq (tokAt w j) hjt htj
  have htv := tv_cases (dg (tokAt w i)) (cls (tokAt w j)) (dg01 _) (cls01 _ hjt)
  rw [← hae, ← hbe] at htv
  have hD : |dv fl p w i - ((dE (tokAt w i) : ℚ) : ℝ)| ≤ 3 / 250 * ((dE (tokAt w i) : ℚ) : ℝ) :=
    sw_nn hr hu0 hu1 (dE (tokAt w i)) (dE_nn _) (p.E (tokAt w i) 0) (hp.E _ _)
  have hG : |gv fl p w j - ((gE (tokAt w j) : ℚ) : ℝ)| ≤ 3 / 250 * ((gE (tokAt w j) : ℚ) : ℝ) :=
    sw_nn hr hu0 hu1 (gE (tokAt w j)) (gE_nn _) (p.E (tokAt w j) 2) (hp.E _ _)
  exact arith hr hu0 hu1 _ _ _ htv (dv fl p w i) (gv fl p w j) (sw fl 1 (p.V 0 0 3 2))
    (sw fl 1 (p.W1 0 0 0)) (sw fl 1 (p.W1 0 0 3)) (sw fl (-1) (p.b1 0 0))
    (sw fl 1 (p.W2 0 4 0)) (sw fl 1 (p.oW 0)) (sw fl 1 (p.oW 3)) (sw fl (-2) (p.oW 4))
    hD hG (sw1 hr hu0 hu1 _ (hp.V 0 0 3 2)) (sw1 hr hu0 hu1 _ (hp.W1 0 0 0))
    (sw1 hr hu0 hu1 _ (hp.W1 0 0 3)) (swm1 hr hu0 hu1 _ (hp.b1 0 0))
    (sw1 hr hu0 hu1 _ (hp.W2 0 4 0)) (sw1 hr hu0 hu1 _ (hp.oW 0))
    (sw1 hr hu0 hu1 _ (hp.oW 3)) (swm2 hr hu0 hu1 _ (hp.oW 4))

end Lane4.Case
