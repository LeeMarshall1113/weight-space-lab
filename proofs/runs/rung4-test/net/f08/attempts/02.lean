namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

def z7 : List ℚ := [0, 0, 0, 0, 0, 0, 0]

/-- State: [u, a, c, A', 1, fl i, fl n]. Causal head: score = -(pos j) - 2 n u_j. -/
def hd : Head :=
  { A := [z7, z7, z7, z7, [0, 0, 0, 0, 0, -1, 0], z7, [-2, 0, 0, 0, 0, 0, 0]],
    V := [z7, z7, z7, [0, 1, 0, 0, 0, 0, 0], z7, z7, z7],
    mask := Mask.causal }

def blk : Block :=
  { heads := [hd],
    W1 := [[0, 0, 1, 1, 0, 0, 0]], b1 := [-1],
    W2 := [[0], [0], [0], [-2], [0], [0], [0]], b2 := z7 }

def net : TNet :=
  { embed := [[1, 0, 0, 0], [0, 0, 0, 0], [3, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
    blocks := [blk],
    outW := [0, 0, 1, 1, 0, 0, 0],
    outB := 0 }

def Uq (t : ℕ) : ℚ := if t = 0 then 1 else if t = 2 then 3 else 0
def Aq (t : ℕ) : ℚ := if t = 5 then 1 else 0
def Cq (t : ℕ) : ℚ := if t = 3 then 1 else 0

theorem Aq01 (t : ℕ) : Aq t = 0 ∨ Aq t = 1 := by
  unfold Aq; split_ifs <;> simp

theorem Cq01 (t : ℕ) : Cq t = 0 ∨ Cq t = 1 := by
  unfold Cq; split_ifs <;> simp

theorem cbit01 (t : ℕ) : cbit t = 0 ∨ cbit t = 1 := by
  unfold cbit; split_ifs <;> simp

theorem Cq_cbit (t : ℕ) : Cq t = (cbit t : ℚ) := by
  unfold Cq cbit; split_ifs <;> simp_all

theorem aq_code (t : ℕ) (h1 : 1 ≤ t) (h5 : t ≤ 5) (h2 : t ≠ 2) :
    Aq t = (if code t = 2 then 1 else 0) := by
  interval_cases t <;> simp_all [Aq, code]

theorem code_ne (t : ℕ) (h1 : 1 ≤ t) (h5 : t ≤ 5) : (code t = 0 ↔ t = 2) := by
  interval_cases t <;> simp [code]

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j =
      [sw fl (Uq (tokAt w j)) (p.E (tokAt w j) 0), sw fl (Aq (tokAt w j)) (p.E (tokAt w j) 1),
       sw fl (Cq (tokAt w j)) (p.E (tokAt w j) 2), 0] ++ pos fl j (w.length + 1) := by
  have h5 := tok_le w hw j
  unfold TNet.init
  generalize tokAt w j = t at h5 ⊢
  interval_cases t <;> simp [net, swRow, Uq, Aq, Cq, sw_zero hr]

noncomputable def scf (fl : ℝ → ℝ) (s s2 qn qj e : ℝ) : ℝ :=
  fl (fl (s * qj) + fl (qn * fl (s2 * e)))

theorem score_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (a b c d qi qn ua ub uc ud qj qn' : ℝ) :
    hd.score fl dA [a, b, c, d, 1, qi, qn] [ua, ub, uc, ud, 1, qj, qn']
      = scf fl (sw fl (-1) (dA 4 5)) (sw fl (-2) (dA 6 0)) qn qj ua := by
  simp [Head.score, hd, z7, pdot, rmat, rdot, scf, sw_zero hr, hr.zero, hr.idem]

noncomputable def scw (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (k : ℕ) : ℝ :=
  scf fl (sw fl (-1) (p.A 0 0 4 5)) (sw fl (-2) (p.A 0 0 6 0))
    (fl ((w.length + 1 : ℕ) : ℝ)) (fl (k : ℝ)) (sw fl (Uq (tokAt w k)) (p.E (tokAt w k) 0))

/-! ### real-analysis helpers -/

theorem sw_a {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    (q : ℚ) (r a : ℝ) (hq : (q : ℝ) = r) (ha : 1 / 190 * |r| ≤ a) (d : ℝ)
    (hdd : |d| ≤ 1 / 200) : |sw fl q d - r| ≤ a := by
  have h := sw_rel hr hu0 q hdd (ε := 1 / 190) (by linarith)
  rw [hq] at h
  exact le_trans h ha

theorem sw_one {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    (d : ℝ) (hdd : |d| ≤ 1 / 200) : |sw fl 1 d - 1| ≤ 1 / 190 :=
  sw_a hr hu0 hu1 1 1 (1 / 190) (by norm_num) (by norm_num) d hdd

theorem sw_m1 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    (d : ℝ) (hdd : |d| ≤ 1 / 200) : |sw fl (-1) d - (-1)| ≤ 1 / 190 :=
  sw_a hr hu0 hu1 (-1) (-1) (1 / 190) (by norm_num) (by norm_num) d hdd

theorem sw_m2 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    (d : ℝ) (hdd : |d| ≤ 1 / 200) : |sw fl (-2) d - (-2)| ≤ 1 / 95 :=
  sw_a hr hu0 hu1 (-2) (-2) (1 / 95) (by norm_num) (by norm_num) d hdd

theorem sw_three {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    (d : ℝ) (hdd : |d| ≤ 1 / 200) : |sw fl 3 d - 3| ≤ 3 / 190 :=
  sw_a hr hu0 hu1 3 3 (3 / 190) (by norm_num) (by norm_num) d hdd

theorem abs_le_of_near {x s a S : ℝ} (h : |x - s| ≤ a) (hs : |s| ≤ S) : |x| ≤ S + a := by
  have := abs_sub_abs_le_abs_sub x s
  linarith

theorem flp {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu : 0 ≤ u)
    {x y s t a b X Y S : ℝ} (hx : |x - s| ≤ a) (hy : |y - t| ≤ b) (hX : |x| ≤ X)
    (hY : |y| ≤ Y) (hs : |s| ≤ S) :
    |fl (x * y) - s * t| ≤ a * Y + S * b + u * (X * Y) := by
  have h1 : |x * y| ≤ X * Y := by
    rw [abs_mul]
    exact mul_le_mul hX hY (abs_nonneg _) (le_trans (abs_nonneg _) hX)
  have h2 := hr.err hu h1
  have h3 : |x * y - s * t| ≤ a * Y + S * b := by
    have e : x * y - s * t = (x - s) * y + s * (y - t) := by ring
    rw [e]
    calc |(x - s) * y + s * (y - t)| ≤ |(x - s) * y| + |s * (y - t)| := abs_add_le _ _
      _ ≤ a * Y + S * b := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul hx hY (abs_nonneg _) (le_trans (abs_nonneg _) hx))
          (mul_le_mul hs hy (abs_nonneg _) (le_trans (abs_nonneg _) hs))
  have h4 := abs_add_le (fl (x * y) - x * y) (x * y - s * t)
  have h5 : fl (x * y) - x * y + (x * y - s * t) = fl (x * y) - s * t := by ring
  rw [h5] at h4
  linarith

theorem flp1 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu : 0 ≤ u)
    {x y t a b X Y : ℝ} (hx : |x - 1| ≤ a) (hy : |y - t| ≤ b) (hX : |x| ≤ X)
    (hY : |y| ≤ Y) :
    |fl (x * y) - t| ≤ a * Y + b + u * (X * Y) := by
  have h := flp hr hu hx hy hX hY (show |(1 : ℝ)| ≤ 1 by norm_num)
  simp only [one_mul] at h
  exact h

theorem fls {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu : 0 ≤ u)
    {x y s t a b X Y : ℝ} (hx : |x - s| ≤ a) (hy : |y - t| ≤ b) (hX : |x| ≤ X)
    (hY : |y| ≤ Y) :
    |fl (x + y) - (s + t)| ≤ a + b + u * (X + Y) := by
  have h1 : |x + y| ≤ X + Y := le_trans (abs_add_le _ _) (add_le_add hX hY)
  have h2 := hr.err hu h1
  have h3 : |x + y - (s + t)| ≤ a + b := by
    have e : x + y - (s + t) = (x - s) + (y - t) := by ring
    rw [e]
    exact le_trans (abs_add_le _ _) (add_le_add hx hy)
  have h4 := abs_add_le (fl (x + y) - (x + y)) (x + y - (s + t))
  have h5 : fl (x + y) - (x + y) + (x + y - (s + t)) = fl (x + y) - (s + t) := by ring
  rw [h5] at h4
  linarith

/-! ### the output value -/

noncomputable def alphaf (fl : ℝ → ℝ) (p : Pert) (ea : ℝ) : ℝ := fl (sw fl 1 (p.V 0 0 3 1) * ea)
noncomputable def p1f (fl : ℝ → ℝ) (p : Pert) (ec : ℝ) : ℝ := fl (sw fl 1 (p.W1 0 0 2) * ec)
noncomputable def p2f (fl : ℝ → ℝ) (p : Pert) (ea : ℝ) : ℝ :=
  fl (sw fl 1 (p.W1 0 0 3) * alphaf fl p ea)
noncomputable def sf (fl : ℝ → ℝ) (p : Pert) (ec ea : ℝ) : ℝ := fl (p1f fl p ec + p2f fl p ea)
noncomputable def pref (fl : ℝ → ℝ) (p : Pert) (ec ea : ℝ) : ℝ :=
  fl (sf fl p ec ea + sw fl (-1) (p.b1 0 0))
noncomputable def mf (fl : ℝ → ℝ) (p : Pert) (ec ea : ℝ) : ℝ :=
  fl (sw fl (-2) (p.W2 0 3 0) * relu (pref fl p ec ea))
noncomputable def zf (fl : ℝ → ℝ) (p : Pert) (ec ea : ℝ) : ℝ :=
  fl (alphaf fl p ea + mf fl p ec ea)
noncomputable def o2f (fl : ℝ → ℝ) (p : Pert) (ec : ℝ) : ℝ := fl (sw fl 1 (p.oW 2) * ec)
noncomputable def o3f (fl : ℝ → ℝ) (p : Pert) (ec ea : ℝ) : ℝ :=
  fl (sw fl 1 (p.oW 3) * zf fl p ec ea)
noncomputable def outv (fl : ℝ → ℝ) (p : Pert) (ec ea : ℝ) : ℝ :=
  fl (o2f fl p ec + o3f fl p ec ea)

theorem outv_core {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (A C ea ec : ℝ)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (hea : |ea - A| ≤ 1 / 190) (hec : |ec - C| ≤ 1 / 190) :
    |outv fl p ec ea - (A + C - 2 * max (A + C - 1) 0)| ≤ 1 / 5 := by
  have hAabs : |A| ≤ 1 := by rw [abs_of_nonneg hA0]; exact hA1
  have hCabs : |C| ≤ 1 := by rw [abs_of_nonneg hC0]; exact hC1
  have hv1 := sw_one hr hu0 hu1 (p.V 0 0 3 1) (hp.V 0 0 3 1)
  have hw12 := sw_one hr hu0 hu1 (p.W1 0 0 2) (hp.W1 0 0 2)
  have hw13 := sw_one hr hu0 hu1 (p.W1 0 0 3) (hp.W1 0 0 3)
  have hb1 := sw_m1 hr hu0 hu1 (p.b1 0 0) (hp.b1 0 0)
  have hw2 := sw_m2 hr hu0 hu1 (p.W2 0 3 0) (hp.W2 0 3 0)
  have hq2 := sw_one hr hu0 hu1 (p.oW 2) (hp.oW 2)
  have hq3 := sw_one hr hu0 hu1 (p.oW 3) (hp.oW 3)
  have h1abs : |(1 : ℝ)| ≤ 1 := by norm_num
  have hα : |alphaf fl p ea - A| ≤ 1 / 80 := by
    have h := flp1 hr hu0 hv1 hea (abs_le_of_near hv1 h1abs) (abs_le_of_near hea hAabs)
    unfold alphaf
    linarith
  have hp1 : |p1f fl p ec - C| ≤ 1 / 80 := by
    have h := flp1 hr hu0 hw12 hec (abs_le_of_near hw12 h1abs) (abs_le_of_near hec hCabs)
    unfold p1f
    linarith
  have hp2 : |p2f fl p ea - A| ≤ 1 / 40 := by
    have h := flp1 hr hu0 hw13 hα (abs_le_of_near hw13 h1abs) (abs_le_of_near hα hAabs)
    unfold p2f
    linarith
  have hCA : |C + A| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hs : |sf fl p ec ea - (C + A)| ≤ 1 / 25 := by
    have h := fls hr hu0 hp1 hp2 (abs_le_of_near hp1 hCabs) (abs_le_of_near hp2 hAabs)
    unfold sf
    linarith
  have hm1abs : |(-1 : ℝ)| ≤ 1 := by norm_num
  have hpre : |pref fl p ec ea - (C + A + -1)| ≤ 1 / 20 := by
    have h := fls hr hu0 hs hb1 (abs_le_of_near hs hCA) (abs_le_of_near hb1 hm1abs)
    unfold pref
    linarith
  have hh : |relu (pref fl p ec ea) - max (A + C - 1) 0| ≤ 1 / 20 := by
    have h1 := abs_max_sub_max_le_abs (pref fl p ec ea) (A + C - 1) 0
    have h2 : |pref fl p ec ea - (A + C - 1)| ≤ 1 / 20 := by
      obtain ⟨l, r⟩ := abs_le.mp hpre
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    show |max (pref fl p ec ea) 0 - max (A + C - 1) 0| ≤ 1 / 20
    exact le_trans h1 h2
  have hH0a : 0 ≤ max (A + C - 1) 0 := le_max_right _ _
  have hH0b : max (A + C - 1) 0 ≤ 1 := max_le (by linarith) (by norm_num)
  have hH0abs : |max (A + C - 1) 0| ≤ 1 := by rw [abs_of_nonneg hH0a]; exact hH0b
  have hm2abs : |(-2 : ℝ)| ≤ 2 := by norm_num
  have hm : |mf fl p ec ea - (-2 * max (A + C - 1) 0)| ≤ 1 / 8 := by
    have h := flp hr hu0 hw2 hh (abs_le_of_near hw2 hm2abs) (abs_le_of_near hh hH0abs) hm2abs
    unfold mf
    linarith
  have hm2H : |-2 * max (A + C - 1) 0| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hz : |zf fl p ec ea - (A + -2 * max (A + C - 1) 0)| ≤ 1 / 7 := by
    have h := fls hr hu0 hα hm (abs_le_of_near hα hAabs) (abs_le_of_near hm hm2H)
    unfold zf
    linarith
  have hZ : |A + -2 * max (A + C - 1) 0| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have ho3 : |o3f fl p ec ea - (A + -2 * max (A + C - 1) 0)| ≤ 1 / 6 := by
    have h := flp1 hr hu0 hq3 hz (abs_le_of_near hq3 h1abs) (abs_le_of_near hz hZ)
    unfold o3f
    linarith
  have ho2 : |o2f fl p ec - C| ≤ 1 / 80 := by
    have h := flp1 hr hu0 hq2 hec (abs_le_of_near hq2 h1abs) (abs_le_of_near hec hCabs)
    unfold o2f
    linarith
  have hout := fls hr hu0 ho2 ho3 (abs_le_of_near ho2 hCabs) (abs_le_of_near ho3 hZ)
  have hout' : |outv fl p ec ea - (C + (A + -2 * max (A + C - 1) 0))| ≤ 1 / 5 := by
    unfold outv
    linarith
  obtain ⟨l, r⟩ := abs_le.mp hout'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem outv_ok {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (qa qc : ℚ)
    (hqa : qa = 0 ∨ qa = 1) (hqc : qc = 0 ∨ qc = 1) (ta tc : ℕ) :
    |outv fl p (sw fl qc (p.E tc 2)) (sw fl qa (p.E ta 1))
      - ((qa : ℝ) + (qc : ℝ) - 2 * max ((qa : ℝ) + (qc : ℝ) - 1) 0)| ≤ 1 / 5 := by
  have hA0 : (0 : ℝ) ≤ (qa : ℝ) := by rcases hqa with h | h <;> simp [h]
  have hA1 : (qa : ℝ) ≤ 1 := by rcases hqa with h | h <;> simp [h]
  have hC0 : (0 : ℝ) ≤ (qc : ℝ) := by rcases hqc with h | h <;> simp [h]
  have hC1 : (qc : ℝ) ≤ 1 := by rcases hqc with h | h <;> simp [h]
  have hea : |sw fl qa (p.E ta 1) - (qa : ℝ)| ≤ 1 / 190 :=
    sw_a hr hu0 hu1 qa (qa : ℝ) (1 / 190) rfl
      (by rw [abs_of_nonneg hA0]; linarith) _ (hp.E ta 1)
  have hec : |sw fl qc (p.E tc 2) - (qc : ℝ)| ≤ 1 / 190 :=
    sw_a hr hu0 hu1 qc (qc : ℝ) (1 / 190) rfl
      (by rw [abs_of_nonneg hC0]; linarith) _ (hp.E tc 2)
  exact outv_core hr hu0 hu1 p hp (qa : ℝ) (qc : ℝ) _ _ hA0 hA1 hC0 hC1 hea hec

/-! ### the output in closed form -/

theorem out_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i j : ℕ)
    (hsel : hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = [j]) :
    net.out fl p w i
      = outv fl p (sw fl (Cq (tokAt w i)) (p.E (tokAt w i) 2))
          (sw fl (Aq (tokAt w j)) (p.E (tokAt w j) 1)) := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 0, 1, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  have hV : hd.V = [z7, z7, z7, [0, 1, 0, 0, 0, 0, 0], z7, z7, z7] := rfl
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [runFrom, Block.apply, blk, headsApply, Head.attn, hsel, hV, attnRows,
    ravg_singleton hr]
  simp only [init_eq hr p w hw]
  simp [outv, o2f, o3f, zf, mf, pref, sf, p1f, p2f, alphaf, z7, pos, rdot, radd, raffine,
    sw_zero hr, hr.zero, hr.idem, hr.one, fl_sw hr]

/-! ### selection -/

theorem qn_bd {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) {n : ℕ}
    (hn : u * (n : ℝ) ≤ 1 / 256) :
    (n : ℝ) - 1 / 256 ≤ fl (n : ℝ) ∧ fl (n : ℝ) ≤ (n : ℝ) + 1 / 256 := by
  have h := abs_le.mp (hr.natCast_near n)
  constructor <;> linarith [h.1, h.2]

theorem F_gen {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {qn N x L H : ℝ} (hN : 2 ≤ N) (hn : u * N ≤ 1 / 256) (hq1 : N - 1 / 256 ≤ qn)
    (hq2 : qn ≤ N + 1 / 256) (hL : L ≤ x) (hH : x ≤ H) (hL7 : -7 ≤ L) (hH0 : H ≤ -1) :
    fl (qn * fl x) ≤ (N - 1 / 256) * (H + 1 / 1000) + 9 / 256 ∧
    (N + 1 / 256) * (L - 1 / 1000) - 9 / 256 ≤ fl (qn * fl x) := by
  have hx7 : |x| ≤ 7 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hQ := abs_le.mp (hr.err hu0 hx7)
  have hu7 : u * 7 ≤ 1 / 1000 := by linarith
  have hQ1 : fl x ≤ H + 1 / 1000 := by linarith [hQ.2]
  have hQ2 : L - 1 / 1000 ≤ fl x := by linarith [hQ.1]
  have hqn0 : 0 ≤ qn := by linarith
  have hQa : |fl x| ≤ 8 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hx2 : |qn * fl x| ≤ 9 * N := by
    rw [abs_mul, abs_of_nonneg hqn0]
    calc qn * |fl x| ≤ (N + 1 / 256) * 8 := mul_le_mul hq2 hQa (abs_nonneg _) (by linarith)
      _ ≤ 9 * N := by linarith
  have h2 := abs_le.mp (hr.err hu0 hx2)
  have hu9 : u * (9 * N) ≤ 9 / 256 := by linarith
  constructor
  · have e1 : qn * fl x ≤ (N - 1 / 256) * (H + 1 / 1000) := by
      nlinarith [mul_nonneg hqn0 (sub_nonneg.2 hQ1),
        mul_nonneg (sub_nonneg.2 hq1) (show (0 : ℝ) ≤ -(H + 1 / 1000) by linarith)]
    linarith [h2.2]
  · have e2 : (N + 1 / 256) * (L - 1 / 1000) ≤ qn * fl x := by
      nlinarith [mul_nonneg hqn0 (sub_nonneg.2 hQ2),
        mul_nonneg (sub_nonneg.2 hq2) (show (0 : ℝ) ≤ -(L - 1 / 1000) by linarith)]
    linarith [h2.1]

theorem sq_abs {N s q : ℝ} (hN : 2 ≤ N) (hs1 : -1 - 1 / 190 ≤ s) (hs2 : s ≤ -1 + 1 / 190)
    (hq0 : 0 ≤ q) (hq1 : q ≤ N + 1 / 256) : |s * q| ≤ 2 * (N + 1) := by
  have h1 : 0 ≤ (s - (-1 - 1 / 190)) * q := mul_nonneg (by linarith) hq0
  have h2 : 0 ≤ (-1 + 1 / 190 - s) * q := mul_nonneg (by linarith) hq0
  rw [abs_le]
  constructor <;> nlinarith

theorem scM_lt {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {N s qj qj' : ℝ} (hN : 2 ≤ N) (hn : u * N ≤ 1 / 256) (hs1 : -1 - 1 / 190 ≤ s)
    (hs2 : s ≤ -1 + 1 / 190) (hq0 : 0 ≤ qj) (hq : qj + 127 / 128 ≤ qj')
    (hq' : qj' ≤ N + 1 / 256) : fl (s * qj') < fl (s * qj) := by
  have hq0' : 0 ≤ qj' := by linarith
  apply hr.lt_of_gap hu0 (B := 2 * (N + 1))
  · exact sq_abs hN hs1 hs2 hq0' hq'
  · exact sq_abs hN hs1 hs2 hq0 (by linarith)
  · have h1 : (-s) * (127 / 128) ≤ (-s) * (qj' - qj) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith [h1, hn, hu1]

theorem scM_le0 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) {s qj : ℝ} (hs : s ≤ 0)
    (hq : 0 ≤ qj) : fl (s * qj) ≤ 0 := by
  have h := hr.mono (s * qj) 0 (by nlinarith [mul_nonneg (neg_nonneg.2 hs) hq])
  rwa [hr.zero] at h

theorem scM_lb {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    {N s qj : ℝ} (hN : 2 ≤ N) (hn : u * N ≤ 1 / 256) (hs1 : -1 - 1 / 190 ≤ s)
    (hs2 : s ≤ -1 + 1 / 190) (hq0 : 0 ≤ qj) (hq1 : qj ≤ N + 1 / 256) :
    -(6 / 5) * N ≤ fl (s * qj) := by
  have hB := sq_abs hN hs1 hs2 hq0 hq1
  have h := abs_le.mp (hr.err hu0 hB)
  have hu : u * (2 * (N + 1)) ≤ 1 / 100 := by linarith
  have h1 : 0 ≤ (s - (-1 - 1 / 190)) * qj := mul_nonneg (by linarith) hq0
  nlinarith [h.1]

theorem scf_unm {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) {s s2 qn qj e : ℝ} (hs : s ≤ 0)
    (hq : 0 ≤ qj) : scf fl s s2 qn qj e ≤ fl (qn * fl (s2 * e)) := by
  unfold scf
  have hP : fl (s * qj) ≤ 0 := scM_le0 hr hs hq
  calc fl (fl (s * qj) + fl (qn * fl (s2 * e))) ≤ fl (fl (qn * fl (s2 * e))) :=
        hr.mono _ _ (by linarith)
    _ = fl (qn * fl (s2 * e)) := hr.idem _

theorem scw_bos {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256) (hN : (2 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ)) :
    -(21 / 10) * ((w.length + 1 : ℕ) : ℝ) ≤ scw fl p w 0 ∧
      scw fl p w 0 ≤ -(19 / 10) * ((w.length + 1 : ℕ) : ℝ) := by
  have h0 : scw fl p w 0
      = fl (fl ((w.length + 1 : ℕ) : ℝ) * fl (sw fl (-2) (p.A 0 0 6 0) * sw fl 1 (p.E 0 0))) := by
    simp [scw, scf, Lane4.Seq.tokAt_zero, Uq, hr.zero, hr.idem]
  rw [h0]
  have hqn := qn_bd hr hn
  have hs2 := abs_le.mp (sw_m2 hr hu0 hu1 (p.A 0 0 6 0) (hp.A 0 0 6 0))
  have he0 := abs_le.mp (sw_one hr hu0 hu1 (p.E 0 0) (hp.E 0 0))
  generalize sw fl (-2) (p.A 0 0 6 0) = s2 at *
  generalize sw fl 1 (p.E 0 0) = e0 at *
  have a1 : 0 ≤ (-2 + 1 / 95 - s2) * e0 := mul_nonneg (by linarith [hs2.2]) (by linarith [he0.1])
  have a2 : 0 ≤ (2 - 1 / 95) * (e0 - (1 - 1 / 190)) :=
    mul_nonneg (by norm_num) (by linarith [he0.1])
  have b1 : 0 ≤ (s2 - (-2 - 1 / 95)) * e0 := mul_nonneg (by linarith [hs2.1]) (by linarith [he0.1])
  have b2 : 0 ≤ (2 + 1 / 95) * ((1 + 1 / 190) - e0) :=
    mul_nonneg (by norm_num) (by linarith [he0.2])
  have hH : s2 * e0 ≤ -197 / 100 := by nlinarith [a1, a2]
  have hL : -203 / 100 ≤ s2 * e0 := by nlinarith [b1, b2]
  obtain ⟨u1, u2⟩ := F_gen hr hu0 hu1 hN hn hqn.1 hqn.2 hL hH (by norm_num) (by norm_num)
  constructor <;> linarith

theorem scw_unm {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256) (hN : (2 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ))
    (k : ℕ) (hk : tokAt w k = 2) :
    scw fl p w k ≤ -(58 / 10) * ((w.length + 1 : ℕ) : ℝ) := by
  have hu3 : Uq 2 = 3 := by simp [Uq]
  unfold scw
  rw [hk, hu3]
  have hs1 := abs_le.mp (sw_m1 hr hu0 hu1 (p.A 0 0 4 5) (hp.A 0 0 4 5))
  have hs2 := abs_le.mp (sw_m2 hr hu0 hu1 (p.A 0 0 6 0) (hp.A 0 0 6 0))
  have he2 := abs_le.mp (sw_three hr hu0 hu1 (p.E 2 0) (hp.E 2 0))
  have hqn := qn_bd hr hn
  have hq0 : 0 ≤ fl (k : ℝ) := hr.nonneg (Nat.cast_nonneg k)
  refine le_trans (scf_unm hr (s := sw fl (-1) (p.A 0 0 4 5)) (by linarith [hs1.2]) hq0) ?_
  generalize sw fl (-2) (p.A 0 0 6 0) = s2 at *
  generalize sw fl 3 (p.E 2 0) = e2 at *
  have a1 : 0 ≤ (-2 + 1 / 95 - s2) * e2 := mul_nonneg (by linarith [hs2.2]) (by linarith [he2.1])
  have a2 : 0 ≤ (2 - 1 / 95) * (e2 - (3 - 3 / 190)) :=
    mul_nonneg (by norm_num) (by linarith [he2.1])
  have b1 : 0 ≤ (s2 - (-2 - 1 / 95)) * e2 := mul_nonneg (by linarith [hs2.1]) (by linarith [he2.1])
  have b2 : 0 ≤ (2 + 1 / 95) * ((3 + 3 / 190) - e2) :=
    mul_nonneg (by norm_num) (by linarith [he2.2])
  have hH : s2 * e2 ≤ -59 / 10 := by nlinarith [a1, a2]
  have hL : -61 / 10 ≤ s2 * e2 := by nlinarith [b1, b2]
  obtain ⟨u1, _⟩ := F_gen hr hu0 hu1 hN hn hqn.1 hqn.2 hL hH (by norm_num) (by norm_num)
  linarith

theorem scw_mrk {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (k : ℕ)
    (h0 : tokAt w k ≠ 0) (h2 : tokAt w k ≠ 2) :
    scw fl p w k = fl (sw fl (-1) (p.A 0 0 4 5) * fl (k : ℝ)) := by
  have hu : Uq (tokAt w k) = 0 := by simp [Uq, h0, h2]
  unfold scw
  rw [hu]
  simp [scf, sw_zero hr, hr.zero, hr.idem]

theorem firstc_step (p : List ℕ) (t : ℕ) :
    firstc (p ++ [t]) = if firstc p = 0 then code t else firstc p := by
  unfold firstc
  rw [List.foldl_append]
  rfl

theorem struct_ex (w : List ℕ) (tk : ∀ k, 1 ≤ k → k ≤ w.length → 1 ≤ tokAt w k ∧ tokAt w k ≤ 5) :
    ∀ i, i ≤ w.length →
    (firstc (w.take i) = 0 ∧ ∀ k, 1 ≤ k → k ≤ i → tokAt w k = 2) ∨
    (∃ j, 1 ≤ j ∧ j ≤ i ∧ tokAt w j ≠ 2 ∧ (∀ k, 1 ≤ k → k < j → tokAt w k = 2) ∧
        firstc (w.take i) = code (tokAt w j)) := by
  intro i
  induction i with
  | zero =>
    intro _
    exact Or.inl ⟨by simp [firstc], fun k h1 h2 => by omega⟩
  | succ m ih =>
    intro hm
    have hlt : m < w.length := by omega
    have hsucc : tokAt w (m + 1) = w[m] := Lane4.Seq.tokAt_succ w m hlt
    have htk : w.take (m + 1) = w.take m ++ [w[m]] := by
      rw [List.take_succ]
      simp [hlt]
    have hstep : firstc (w.take (m + 1))
        = if firstc (w.take m) = 0 then code (tokAt w (m + 1)) else firstc (w.take m) := by
      rw [htk, firstc_step, ← hsucc]
    rcases ih (by omega) with ⟨h0, hk⟩ | ⟨j, hj1, hji, hjt, hbef, hfc⟩
    · by_cases ht2 : tokAt w (m + 1) = 2
      · left
        refine ⟨?_, ?_⟩
        · rw [hstep, h0, if_pos rfl, ht2]
          simp [code]
        · intro k hk1 hk2
          by_cases hkm : k ≤ m
          · exact hk k hk1 hkm
          · have : k = m + 1 := by omega
            rw [this]; exact ht2
      · right
        refine ⟨m + 1, by omega, le_refl _, ht2, ?_, ?_⟩
        · intro k hk1 hk2
          exact hk k hk1 (by omega)
        · rw [hstep, h0, if_pos rfl]
    · right
      have hjt5 := tk j hj1 (by omega)
      have hcne : code (tokAt w j) ≠ 0 := fun h => hjt ((code_ne _ hjt5.1 hjt5.2).1 h)
      refine ⟨j, hj1, by omega, hjt, hbef, ?_⟩
      rw [hstep, if_neg (by rw [hfc]; exact hcne)]
      exact hfc

theorem sel_ex {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    ∃ j, hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = [j] ∧
      Aq (tokAt w j) = (if firstc (w.take i) = 2 then 1 else 0) := by
  have tk : ∀ k, 1 ≤ k → k ≤ w.length → 1 ≤ tokAt w k ∧ tokAt w k ≤ 5 := by
    intro k hk1 hk2
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hm : m < w.length := by omega
    rw [Lane4.Seq.tokAt_succ w m hm]
    exact hw _ (List.getElem_mem hm)
  have hN : (2 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    have : 2 ≤ w.length + 1 := by omega
    exact_mod_cast this
  have key : ∀ k, hd.score fl (p.A 0 0) (net.init fl p w i) (net.init fl p w k)
      = scw fl p w k := by
    intro k
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    rw [score_eq hr]
    rfl
  have hsb := abs_le.mp (sw_m1 hr hu0 hu1 (p.A 0 0 4 5) (hp.A 0 0 4 5))
  have hs1 : -1 - 1 / 190 ≤ sw fl (-1) (p.A 0 0 4 5) := by linarith [hsb.1]
  have hs2 : sw fl (-1) (p.A 0 0 4 5) ≤ -1 + 1 / 190 := by linarith [hsb.2]
  have hbos := scw_bos hr hu0 hu1 p hp w hn hN
  have hmem : ∀ k, k ∈ cand hd.mask (w.length + 1) i ↔ k ≤ i := by
    intro k
    rw [show hd.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal]
  rcases struct_ex w tk i hi with ⟨hf0, hk⟩ | ⟨j, hj1, hji, hjt, hbef, hfc⟩
  · refine ⟨0, ?_, ?_⟩
    · apply Head.sel_unique
      · rw [hmem]; omega
      · intro k hk' hne
        rw [hmem] at hk'
        rw [key, key]
        have h2 := hk k (by omega) hk'
        have := scw_unm hr hu0 hu1 p hp w hn hN k h2
        linarith [hbos.1]
    · simp [Lane4.Seq.tokAt_zero, Aq, hf0]
  · have hjt5 := tk j hj1 (by omega)
    have hjn : j ≤ w.length + 1 := by omega
    have hjp := hr.pos_le hu0 hjn hn
    have hmj : scw fl p w j = fl (sw fl (-1) (p.A 0 0 4 5) * fl (j : ℝ)) :=
      scw_mrk hr p w j (by omega) hjt
    have hjlb : -(6 / 5) * ((w.length + 1 : ℕ) : ℝ) ≤ scw fl p w j := by
      rw [hmj]
      exact scM_lb hr hu0 hu1 hN hn hs1 hs2 hjp.1 hjp.2
    refine ⟨j, ?_, ?_⟩
    · apply Head.sel_unique
      · rw [hmem]; exact hji
      · intro k hk' hne
        rw [hmem] at hk'
        rw [key, key]
        by_cases hk0 : k = 0
        · subst hk0
          linarith [hbos.2]
        · have htk := tk k (by omega) (by omega)
          by_cases hk2 : tokAt w k = 2
          · have := scw_unm hr hu0 hu1 p hp w hn hN k hk2
            linarith
          · have hkj : j < k := by
              rcases Nat.lt_or_gt_of_ne hne with h | h
              · exact absurd (hbef k (by omega) h) hk2
              · exact h
            rw [scw_mrk hr p w k (by omega) hk2, hmj]
            have hkn : k ≤ w.length + 1 := by omega
            have hkp := hr.pos_le hu0 hkn hn
            exact scM_lt hr hu0 hu1 hN hn hs1 hs2 hjp.1 (hr.pos_gap hu0 hkj hkn hn) hkp.2
    · rw [hfc]
      exact aq_code _ hjt5.1 hjt5.2 hjt

theorem net_ok : Statement net := by
  intro u fl hr hu0 hu1 p hp w hw hn i hi1 hi
  obtain ⟨j, hsel, hA⟩ := sel_ex hr hu0 hu1 p hp w hw hn i hi1 hi
  rw [out_eq hr p w hw i j hsel]
  have hb := outv_ok hr hu0 hu1 p hp (Aq (tokAt w j)) (Cq (tokAt w i)) (Aq01 _) (Cq01 _)
    (tokAt w j) (tokAt w i)
  have hgd : w.getD (i - 1) 0 = tokAt w i := by
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    simp [Lane4.Seq.tokAt]
  have hAv : ((Aq (tokAt w j) : ℚ) : ℝ) = if firstc (w.take i) = 2 then 1 else 0 := by
    rw [hA]; split_ifs <;> simp
  have hCv : ((Cq (tokAt w i) : ℚ) : ℝ) = ((cbit (tokAt w i) : ℕ) : ℝ) := by
    rw [Cq_cbit]; simp
  have htar : ((target w i : ℕ) : ℝ)
      = ((Aq (tokAt w j) : ℚ) : ℝ) + ((Cq (tokAt w i) : ℚ) : ℝ)
        - 2 * max (((Aq (tokAt w j) : ℚ) : ℝ) + ((Cq (tokAt w i) : ℚ) : ℝ) - 1) 0 := by
    rw [hAv, hCv]
    unfold target
    rw [hgd]
    by_cases hF : firstc (w.take i) = 2 <;> rcases cbit01 (tokAt w i) with hc | hc <;>
      simp [hF, hc] <;> norm_num
  rw [htar]
  exact le_trans hb (by norm_num)

end Lane4.Case
