namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

def z8 : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0]

def hd : Head :=
  { A := [z8, z8, z8, z8, z8, [0, 0, 0, 0, 0, 0, 20, 0], z8, [-100, 0, 0, 0, 0, 0, 0, 0]],
    V := [z8, z8, z8, z8, [0, 1, 0, 0, 0, 0, 0, 0], z8, z8, z8],
    mask := Mask.strict }

def blk : Block :=
  { heads := [hd], W1 := [[0, 0, 0, 1, 1, 0, 0, 0]], b1 := [-1],
    W2 := [[0], [0], [0], [0], [-3], [0], [0], [0]], b2 := z8 }

def net : TNet :=
  { embed := [[0, 0, 0, 0, 0], [0, 0, 2, 1, 0], [0, 0, 1, 0, 0], [1, 0, 0, 0, 0],
              [1, 0, 0, 0, 0], [0, 1, 1, 0, 0]],
    blocks := [blk],
    outW := [0, 0, 1, 0, 1, 0, 0, 0],
    outB := 0 }

def prn (t : ℕ) : ℕ := if t = 3 ∨ t = 4 then 1 else 0
def gn (t : ℕ) : ℕ := if t = 5 then 1 else 0
def isn (t : ℕ) : ℕ := if t = 1 then 1 else 0

noncomputable def epr (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (k : ℕ) : ℝ :=
  sw fl ((prn (tokAt w k) : ℕ) : ℚ) (p.E (tokAt w k) 0)
noncomputable def eg (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (k : ℕ) : ℝ :=
  sw fl ((gn (tokAt w k) : ℕ) : ℚ) (p.E (tokAt w k) 1)
noncomputable def edg (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (k : ℕ) : ℝ :=
  sw fl ((dg (tokAt w k) : ℕ) : ℚ) (p.E (tokAt w k) 2)
noncomputable def eis (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (k : ℕ) : ℝ :=
  sw fl ((isn (tokAt w k) : ℕ) : ℚ) (p.E (tokAt w k) 3)

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [epr fl p w j, eg fl p w j, edg fl p w j, eis fl p w j, 0]
      ++ pos fl j (w.length + 1) := by
  have h6 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4
      ∨ tokAt w j = 5 := by
    have := tok_le w hw j
    omega
  rcases h6 with h | h | h | h | h | h <;>
    simp [TNet.init, net, swRow, h, sw_zero hr, prn, gn, isn, dg, epr, eg, edg, eis]

/-- The score in closed form. -/
theorem score_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (a0 a1 a2 a3 a4 qi qn b1 b2 b3 b4 p0 qk qn' : ℝ)
    (hI : fl (fl (sw fl 20 (dA 5 6) * qk)) = fl (sw fl 20 (dA 5 6) * qk))
    (hJ : fl (fl (sw fl (-100) (dA 7 0) * p0)) = fl (sw fl (-100) (dA 7 0) * p0)) :
    hd.score fl dA [a0, a1, a2, a3, a4, 1, qi, qn] [p0, b1, b2, b3, b4, 1, qk, qn']
      = fl (fl (sw fl 20 (dA 5 6) * qk) + fl (qn * fl (sw fl (-100) (dA 7 0) * p0))) := by
  simp [Head.score, hd, z8, pdot, rmat, rdot, sw_zero hr, hr.zero, hI, hJ]

/-- The value of key `k` (row 4 of `V`). -/
theorem val_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ)
    (a0 g a2 a3 a4 a5 a6 a7 : ℝ)
    (hI : fl (fl (sw fl 1 (dV 1) * g)) = fl (sw fl 1 (dV 1) * g)) :
    rdot fl [0, 1, 0, 0, 0, 0, 0, 0] [a0, g, a2, a3, a4, a5, a6, a7] dV 0 0
      = fl (sw fl 1 (dV 1) * g) := by
  simp [rdot, sw_zero hr, hr.zero, hI]

theorem zrow_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ)
    (a b c d e f g h : ℝ) :
    rdot fl z8 [a, b, c, d, e, f, g, h] dV 0 0 = 0 := by
  simp [z8, rdot, sw_zero hr, hr.zero]

theorem attn_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) :
    sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, 0, 0,
         savg fl ex (cand Mask.strict (w.length + 1) i)
              (hscore hd fl (p.A 0 0) (net.init fl p w) i)
              (fun j => rdot fl [0, 1, 0, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 4) 0 0),
         0, 0, 0] := by
  have hV : hd.V = [z8, z8, z8, z8, [0, 1, 0, 0, 0, 0, 0, 0], z8, z8, z8] := rfl
  have hm : hd.mask = Mask.strict := rfl
  have hz : ∀ d : ℕ → ℝ,
      savg fl ex (cand Mask.strict (w.length + 1) i)
        (hscore hd fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl z8 (net.init fl p w j) d 0 0) = 0 := by
    intro d
    apply soft_zeros hr
    intro k _
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact zrow_eq hr d _ _ _ _ _ _ _ _
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz]

theorem out_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) (A w1a w1b bb w2 o2 o4 pre : ℝ)
    (h1a : w1a = sw fl 1 (p.W1 0 0 3)) (h1b : w1b = sw fl 1 (p.W1 0 0 4))
    (hbb : bb = sw fl (-1) (p.b1 0 0)) (h2 : w2 = sw fl (-3) (p.W2 0 4 0))
    (ho2 : o2 = sw fl 1 (p.oW 2)) (ho4 : o4 = sw fl 1 (p.oW 4))
    (hpre : pre = fl (fl (fl (w1a * eis fl p w i) + fl (w1b * A)) + bb))
    (hattn : sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, 0, 0, A, 0, 0, 0])
    (hA : fl A = A)
    (hdgI : fl (edg fl p w i) = edg fl p w i)
    (hisI : fl (eis fl p w i) = eis fl p w i)
    (hI1 : fl (fl (w1a * eis fl p w i)) = fl (w1a * eis fl p w i))
    (hI2 : fl (fl (fl (w1a * eis fl p w i) + fl (w1b * A)))
      = fl (fl (w1a * eis fl p w i) + fl (w1b * A)))
    (hI3 : fl (fl (w2 * relu pre)) = fl (w2 * relu pre))
    (hI5 : fl (fl (o2 * edg fl p w i)) = fl (o2 * edg fl p w i))
    (hI6 : fl (fl (fl (o2 * edg fl p w i) + fl (o4 * fl (A + fl (w2 * relu pre)))))
      = fl (fl (o2 * edg fl p w i) + fl (o4 * fl (A + fl (w2 * relu pre))))) :
    sout net fl ex p w i
      = fl (fl (o2 * edg fl p w i) + fl (o4 * fl (A + fl (w2 * relu pre)))) := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 0, 1, 0, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  subst h1a h1b hbb h2 ho2 ho4 hpre
  unfold sout srun
  rw [hb, ho, hc]
  simp only [srunFrom, sblock, blk, sheadsApply, hattn]
  simp only [init_eq hr p w hw]
  simp [z8, pos, rdot, radd, raffine, sw_zero hr, hr.zero, hA, hdgI, hisI, hI1, hI2, hI3, hI5, hI6]


theorem sw_c {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hM : (2 : ℝ) ^ 40 ≤ M) (q : ℚ) (v : ℝ) (hv : (q : ℝ) = v)
    (hv1 : |v| ≤ 100) {d : ℝ} (hdd : |d| ≤ 1 / 200) :
    |sw fl q d - v| ≤ |v| / 199 + η := by
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by
    have : u ≤ 1 / 10 ^ 6 := le_trans hu1 (by norm_num)
    linarith
  have h2 : (2 : ℝ) * 100 ≤ 2 ^ 40 := by norm_num
  have h := sw_near hr hu0 q hdd (by norm_num) (by rw [hv]; linarith) hε
  rw [hv] at h
  linarith

theorem sw_w {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hM : (2 : ℝ) ^ 40 ≤ M) (q : ℚ) (v : ℝ) (hv : (q : ℝ) = v)
    (hv1 : |v| ≤ 100) {d : ℝ} (hdd : |d| ≤ 1 / 200) (ε : ℝ) (hε : |v| / 199 + η ≤ ε) :
    |sw fl q d - v| ≤ ε :=
  le_trans (sw_c hr hu0 hu1 hM q v hv hv1 hdd) hε

theorem sw_nat {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hM : (2 : ℝ) ^ 40 ≤ M) (m : ℕ) (hm : m ≤ 2) {d : ℝ}
    (hdd : |d| ≤ 1 / 200) : |sw fl (m : ℚ) d - (m : ℝ)| ≤ (m : ℝ) / 199 + η := by
  have hmR : (m : ℝ) ≤ 2 := by exact_mod_cast hm
  have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h := sw_c hr hu0 hu1 hM (m : ℚ) (m : ℝ) (by norm_num)
    (by rw [abs_of_nonneg h0]; linarith) hdd
  rw [abs_of_nonneg h0] at h
  exact h

theorem flb {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 10 ^ 40) (hM : 16 ≤ M) {x t e Bt : ℝ} (hx : |x - t| ≤ e) (ht : |t| ≤ Bt)
    (hB : e + Bt ≤ 16) : |fl x - t| ≤ e + 1 / 10 ^ 6 ∧ fl (fl x) = fl x := by
  have hxB : |x| ≤ 16 := by
    have := abs_sub_abs_le_abs_sub x t
    linarith
  have h1 := hr.near hu0 hx hxB hM
  have h2 : u * 16 ≤ 16 * (1 / 2 ^ 24) := by linarith
  have h3 : (16 : ℝ) * (1 / 2 ^ 24) + 1 / 10 ^ 40 ≤ 1 / 10 ^ 6 := by norm_num
  exact ⟨by linarith, hr.idem x (le_trans hxB hM)⟩

theorem bmul {x y a b : ℝ} (hx : |x| ≤ a) (hy : |y| ≤ b) : |x * y| ≤ a * b := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) (le_trans (abs_nonneg _) hx)

theorem mul_b {x y s t m a b Bs Bt : ℝ} (hx : |x - s| ≤ a) (hy : |y - t| ≤ b)
    (hs : |s| ≤ Bs) (ht : |t| ≤ Bt) (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : s * t = m) :
    |x * y - m| ≤ a * Bt + b * Bs + a * b := by
  have h := mul_near hx hy
  have h1 : a * |t| ≤ a * Bt := mul_le_mul_of_nonneg_left ht ha
  have h2 : b * |s| ≤ b * Bs := mul_le_mul_of_nonneg_left hs hb
  rw [← hm]
  linarith

theorem relu_step {pre I c e : ℝ} (hI : I = 0 ∨ I = 1) (hc : c = 0 ∨ c = 1)
    (h : |pre - (I + c - 1)| ≤ e) : |relu pre - I * c| ≤ e := by
  have h0 := abs_le.mp h
  unfold relu
  rcases hI with rfl | rfl <;> rcases hc with rfl | rfl <;>
  · rcases le_total pre 0 with hp | hp
    · rw [max_eq_right hp]
      rw [abs_le]
      constructor <;> linarith [h0.1, h0.2]
    · rw [max_eq_left hp]
      rw [abs_le]
      constructor <;> linarith [h0.1, h0.2]

theorem add_b {x y p q m a b : ℝ} (hx : |x - p| ≤ a) (hy : |y - q| ≤ b) (hm : p + q = m) :
    |x + y - m| ≤ a + b := by
  have h := abs_add_le (x - p) (y - q)
  have e : x + y - m = (x - p) + (y - q) := by rw [← hm]; ring
  rw [e]
  linarith

theorem final_num {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 10 ^ 40) (hM : 16 ≤ M)
    {D I c A dgE isE w1a w1b bb w2 o2 o4 : ℝ}
    (hD : 0 ≤ D ∧ D ≤ 2) (hI : I = 0 ∨ I = 1) (hc : c = 0 ∨ c = 1)
    (hdg : |dgE - D| ≤ 51 / 5000) (his : |isE - I| ≤ 503 / 100000)
    (hA : |A - c| ≤ 43 / 2000)
    (h1a : |w1a - 1| ≤ 503 / 100000) (h1b : |w1b - 1| ≤ 503 / 100000)
    (hbb : |bb - (-1)| ≤ 503 / 100000) (h2 : |w2 - (-3)| ≤ 1509 / 100000)
    (ho2 : |o2 - 1| ≤ 503 / 100000) (ho4 : |o4 - 1| ≤ 503 / 100000) {pre : ℝ}
    (hpre : pre = fl (fl (fl (w1a * isE) + fl (w1b * A)) + bb)) :
    fl (fl (w1a * isE)) = fl (w1a * isE)
    ∧ fl (fl (fl (w1a * isE) + fl (w1b * A))) = fl (fl (w1a * isE) + fl (w1b * A))
    ∧ fl (fl (w2 * relu pre)) = fl (w2 * relu pre)
    ∧ fl (fl (o2 * dgE)) = fl (o2 * dgE)
    ∧ fl (fl (fl (o2 * dgE) + fl (o4 * fl (A + fl (w2 * relu pre)))))
        = fl (fl (o2 * dgE) + fl (o4 * fl (A + fl (w2 * relu pre))))
    ∧ |fl (fl (o2 * dgE) + fl (o4 * fl (A + fl (w2 * relu pre)))) - (D + c - 3 * (I * c))|
        ≤ 1 / 4 := by
  subst hpre
  have hI1 : |I| ≤ 1 := by rcases hI with rfl | rfl <;> norm_num
  have hc1 : |c| ≤ 1 := by rcases hc with rfl | rfl <;> norm_num
  have hD2 : |D| ≤ 2 := by rw [abs_of_nonneg hD.1]; exact hD.2
  have hIc : |I * c| ≤ 1 := by
    rcases hI with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num
  have hIc2 : |I + c| ≤ 2 := by
    rcases hI with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num
  have hIc3 : |I + c - 1| ≤ 1 := by
    rcases hI with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num
  have hcc : |c + -3 * (I * c)| ≤ 2 := by
    rcases hI with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num
  have hm3 : |(-3 : ℝ)| ≤ 3 := by norm_num
  have hone : |(1 : ℝ)| ≤ 1 := by norm_num
  have s1 := mul_b (m := I) h1a his hone hI1 (by norm_num) (by norm_num) (by ring)
  obtain ⟨f1, i1⟩ := flb hr hu0 hu1 hη hM (e := 101 / 10000) (Bt := 1) (le_trans s1 (by norm_num)) hI1 (by norm_num)
  have s2 := mul_b (m := c) h1b hA hone hc1 (by norm_num) (by norm_num) (by ring)
  obtain ⟨f2, i2⟩ := flb hr hu0 hu1 hη hM (e := 267 / 10000) (Bt := 1) (le_trans s2 (by norm_num)) hc1 (by norm_num)
  have a1 := add_b (m := I + c) f1 f2 rfl
  obtain ⟨f3, i3⟩ := flb hr hu0 hu1 hη hM (e := 369 / 10000) (Bt := 2) (le_trans a1 (by norm_num)) hIc2 (by norm_num)
  have a2 := add_b (m := I + c - 1) f3 hbb (by ring)
  obtain ⟨f4, i4⟩ := flb hr hu0 hu1 hη hM (e := 42 / 1000) (Bt := 1) (le_trans a2 (by norm_num)) hIc3 (by norm_num)
  have r1 := relu_step hI hc f4
  have s3 := mul_b (m := -3 * (I * c)) h2 r1 hm3 hIc (by norm_num) (by norm_num) rfl
  obtain ⟨f5, i5⟩ := flb hr hu0 hu1 hη hM (e := 1418 / 10000) (Bt := 3) (le_trans s3 (by norm_num)) (by
    rw [abs_mul]
    have h3 : |(-3 : ℝ)| = 3 := by norm_num
    rw [h3]
    linarith [hIc]) (by norm_num)
  have a3 := add_b (m := c + -3 * (I * c)) hA f5 rfl
  obtain ⟨f6, i6⟩ := flb hr hu0 hu1 hη hM (e := 1634 / 10000) (Bt := 2) (le_trans a3 (by norm_num)) hcc (by norm_num)
  have s4 := mul_b (m := c + -3 * (I * c)) ho4 f6 hone hcc (by norm_num) (by norm_num) (by ring)
  obtain ⟨f7, i7⟩ := flb hr hu0 hu1 hη hM (e := 1743 / 10000) (Bt := 2) (le_trans s4 (by norm_num)) hcc (by norm_num)
  have s5 := mul_b (m := D) ho2 hdg hone hD2 (by norm_num) (by norm_num) (by ring)
  obtain ⟨f8, i8⟩ := flb hr hu0 hu1 hη hM (e := 204 / 10000) (Bt := 2) (le_trans s5 (by norm_num)) hD2 (by norm_num)
  have a4 := add_b (m := D + (c + -3 * (I * c))) f8 f7 rfl
  obtain ⟨f9, i9⟩ := flb hr hu0 hu1 hη hM (e := 1948 / 10000) (Bt := 4) (le_trans a4 (by norm_num))
    (by
      have : |D + (c + -3 * (I * c))| ≤ |D| + |c + -3 * (I * c)| := abs_add_le _ _
      linarith) (by norm_num)
  have e : D + c - 3 * (I * c) = D + (c + -3 * (I * c)) := by ring
  refine ⟨i1, i3, i5, i8, i9, ?_⟩
  rw [e]
  linarith

theorem prop_sc {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hηs : η ≤ 1 / 10 ^ 40) {n : ℝ} (hn1 : 1 ≤ n)
    (hun : u * n ≤ 1 / 256) (hM : 220 * n ≤ M)
    {S P e qn qk : ℝ} (hS : 19 ≤ S ∧ S ≤ 21) (hP : -101 ≤ P ∧ P ≤ -99)
    (he : 99 / 100 ≤ e ∧ e ≤ 102 / 100) (hqn : n - 1 / 200 ≤ qn ∧ qn ≤ n + 1 / 200)
    (hqk : 0 ≤ qk ∧ qk ≤ n + 1 / 100) :
    -107 * n ≤ fl (fl (S * qk) + fl (qn * fl (P * e)))
      ∧ fl (fl (S * qk) + fl (qn * fl (P * e))) ≤ -72 * n := by
  have hu6 : u ≤ 1 / 10 ^ 6 := le_trans hu1 (by norm_num)
  have hη6 : η ≤ 1 / 10 ^ 6 := le_trans hηs (by norm_num)
  have hun' : ∀ c : ℝ, 0 ≤ c → u * (c * n) ≤ c / 256 := by
    intro c hc
    have := mul_le_mul_of_nonneg_left hun hc
    nlinarith
  have hMn : ∀ c : ℝ, c ≤ 220 → 0 ≤ c → c * n ≤ M := by
    intro c hc hc0
    have := mul_le_mul_of_nonneg_right hc (by linarith : (0 : ℝ) ≤ n)
    linarith
  -- X = S * qk
  have hX0 : 0 ≤ S * qk := mul_nonneg (by linarith) hqk.1
  have hX1 : S * qk ≤ 22 * n := by
    have := mul_le_mul_of_nonneg_right hS.2 hqk.1
    linarith
  have hXM : 22 * n ≤ M := hMn 22 (by norm_num) (by norm_num)
  have hfX0 : 0 ≤ fl (S * qk) := hr.nonneg hX0 (by linarith)
  have hfX1 := hr.upper hu0 (x := S * qk) (B := 22 * n) (abs_le.mpr ⟨by linarith, hX1⟩) hXM
  have hfXle : fl (S * qk) ≤ 23 * n := by
    have := hun' 22 (by norm_num)
    linarith
  -- Y = P * e
  have hY1 : P * e ≤ -98 := by
    have h1 : P * (e - 99 / 100) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  have hY2 : -104 ≤ P * e := by
    have h1 : P * (102 / 100 - e) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  have hMc : (104 : ℝ) ≤ M := by
    have := hMn 104 (by norm_num) (by norm_num)
    linarith
  have hYa := hr.abs hu0 (x := P * e) (B := 104) (abs_le.mpr ⟨hY2, by linarith⟩) hMc
  have hYb := abs_le.mp hYa
  have hYu : u * 104 ≤ 104 / 10 ^ 6 := by nlinarith
  obtain ⟨hYl, hYu'⟩ : -105 ≤ fl (P * e) ∧ fl (P * e) ≤ -97 := by
    constructor <;> linarith [hYb.1, hYb.2]
  generalize fl (P * e) = Y at hYl hYu' ⊢
  generalize hXd : fl (S * qk) = X at hfX0 hfXle ⊢
  -- Q0 = qn * Y
  have hqn0 : 0 ≤ qn := by linarith
  have hq1 : qn * Y ≤ qn * (-97) := mul_le_mul_of_nonneg_left hYu' hqn0
  have hq2 : qn * (-105) ≤ qn * Y := mul_le_mul_of_nonneg_left hYl hqn0
  have hQu : qn * Y ≤ -97 * n + 97 / 200 := by linarith [hqn.1]
  have hQl : -105 * n - 21 / 40 ≤ qn * Y := by linarith [hqn.2]
  have hB107 : 107 * n ≤ M := hMn 107 (by norm_num) (by norm_num)
  have hZa := hr.abs hu0 (x := qn * Y) (B := 107 * n) (abs_le.mpr ⟨by linarith, by linarith⟩) hB107
  have hZb := abs_le.mp hZa
  have h107 := hun' 107 (by norm_num)
  have hZu : fl (qn * Y) ≤ -96 * n := by linarith [hZb.1, hZb.2]
  have hZl : -106 * n ≤ fl (qn * Y) := by linarith [hZb.1, hZb.2]
  have hTa := hr.abs hu0 (x := X + fl (qn * Y)) (B := 107 * n)
    (abs_le.mpr ⟨by linarith, by linarith⟩) hB107
  have hTb := abs_le.mp hTa
  constructor <;> linarith [hTb.1, hTb.2]

theorem cls_facts (t : ℕ) (ht : t ≤ 5) :
    (cls t = 2 ↔ (t = 3 ∨ t = 4)) ∧ (cls t = 1 ↔ t = 5) := by
  interval_cases t <;> simp [cls]

theorem carry_ex (w : List ℕ) : ∀ m : ℕ, m ≤ w.length →
    ∃ j, j ≤ m ∧ cls (tokAt w j) ≠ 2 ∧ (∀ k, j < k → k ≤ m → cls (tokAt w k) = 2)
      ∧ carry (w.take m) = cls (tokAt w j) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨0, le_refl _, ?_, ?_, ?_⟩
    · simp [Lane4.Seq.tokAt_zero, cls]
    · intro k hk hk2
      omega
    · simp [carry, Lane4.Seq.tokAt_zero, cls]
  | succ m ih =>
    intro hm
    obtain ⟨j, hj, hcl, hk, hc⟩ := ih (by omega)
    have ht : tokAt w (m + 1) = w[m] := Lane4.Seq.tokAt_succ w m (by omega)
    have htake : w.take (m + 1) = w.take m ++ [w[m]] := by
      first
        | (rw [List.take_succ, List.getElem?_eq_getElem (by omega)]; rfl)
        | simp [List.take_succ, show m < w.length by omega]
    have hcar : carry (w.take (m + 1)) = (if cls w[m] = 2 then carry (w.take m) else cls w[m]) := by
      rw [htake]
      simp [carry, List.foldl_append]
    by_cases h2 : cls w[m] = 2
    · refine ⟨j, by omega, hcl, ?_, ?_⟩
      · intro k hjk hkm
        by_cases hk' : k = m + 1
        · subst hk'
          rw [ht]
          exact h2
        · exact hk k hjk (by omega)
      · rw [hcar, if_pos h2]
        exact hc
    · refine ⟨m + 1, le_refl _, ?_, ?_, ?_⟩
      · rw [ht]
        exact h2
      · intro k hk hk2
        omega
      · rw [hcar, if_neg h2, ht]

theorem prn_le (t : ℕ) : prn t ≤ 1 := by unfold prn; split_ifs <;> omega
theorem gn_le (t : ℕ) : gn t ≤ 1 := by unfold gn; split_ifs <;> omega
theorem isn_le (t : ℕ) : isn t ≤ 1 := by unfold isn; split_ifs <;> omega
theorem dg_le (t : ℕ) : dg t ≤ 2 := by unfold dg; split_ifs <;> omega
theorem cls_le (t : ℕ) : cls t ≤ 2 := by unfold cls; split_ifs <;> omega
theorem prn_eq (t : ℕ) (ht : t ≤ 5) : prn t = 1 ↔ cls t = 2 := by
  interval_cases t <;> simp [prn, cls]
theorem gn_eq (t : ℕ) (ht : t ≤ 5) : gn t = 1 ↔ cls t = 1 := by
  interval_cases t <;> simp [gn, cls]

theorem ent_pr {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hM : (2 : ℝ) ^ 40 ≤ M) (hη6 : η ≤ 1 / 10 ^ 6) (p : Pert)
    (hp : p.Within (1 / 200)) (w : List ℕ) (k : ℕ) :
    (prn (tokAt w k) = 0 ∧ epr fl p w k = 0)
      ∨ (prn (tokAt w k) = 1 ∧ |epr fl p w k - 1| ≤ 503 / 100000) := by
  have hl := prn_le (tokAt w k)
  rcases (by omega : prn (tokAt w k) = 0 ∨ prn (tokAt w k) = 1) with h | h
  · left
    refine ⟨h, ?_⟩
    unfold epr
    rw [h]
    simp [sw_zero hr]
  · right
    refine ⟨h, ?_⟩
    unfold epr
    rw [h]
    simp only [Nat.cast_one]
    exact sw_w hr hu0 hu1 hM 1 1 (by norm_num) (by norm_num) (hp.E _ 0) _
      (by rw [abs_one]; linarith)

theorem ent_g {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hM : (2 : ℝ) ^ 40 ≤ M) (hη6 : η ≤ 1 / 10 ^ 6) (p : Pert)
    (hp : p.Within (1 / 200)) (w : List ℕ) (k : ℕ) :
    (gn (tokAt w k) = 0 ∧ eg fl p w k = 0)
      ∨ (gn (tokAt w k) = 1 ∧ |eg fl p w k - 1| ≤ 503 / 100000) := by
  have hl := gn_le (tokAt w k)
  rcases (by omega : gn (tokAt w k) = 0 ∨ gn (tokAt w k) = 1) with h | h
  · left
    refine ⟨h, ?_⟩
    unfold eg
    rw [h]
    simp [sw_zero hr]
  · right
    refine ⟨h, ?_⟩
    unfold eg
    rw [h]
    simp only [Nat.cast_one]
    exact sw_w hr hu0 hu1 hM 1 1 (by norm_num) (by norm_num) (hp.E _ 1) _
      (by rw [abs_one]; linarith)

theorem ent_dg {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hM : (2 : ℝ) ^ 40 ≤ M) (hη6 : η ≤ 1 / 10 ^ 6) (p : Pert)
    (hp : p.Within (1 / 200)) (w : List ℕ) (k : ℕ) :
    |edg fl p w k - ((dg (tokAt w k) : ℕ) : ℝ)| ≤ 51 / 5000 := by
  have h := sw_nat hr hu0 hu1 hM (dg (tokAt w k)) (dg_le _) (hp.E (tokAt w k) 2)
  have h2 : ((dg (tokAt w k) : ℕ) : ℝ) ≤ 2 := by exact_mod_cast dg_le _
  unfold edg
  linarith

theorem ent_is {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hM : (2 : ℝ) ^ 40 ≤ M) (hη6 : η ≤ 1 / 10 ^ 6) (p : Pert)
    (hp : p.Within (1 / 200)) (w : List ℕ) (k : ℕ) :
    |eis fl p w k - ((isn (tokAt w k) : ℕ) : ℝ)| ≤ 503 / 100000 := by
  have h := sw_nat hr hu0 hu1 hM (isn (tokAt w k)) (by have := isn_le (tokAt w k); omega)
    (hp.E (tokAt w k) 3)
  have h2 : ((isn (tokAt w k) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast isn_le _
  unfold eis
  linarith

theorem idem_sw {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hM : (2 : ℝ) ^ 40 ≤ M)
    (q : ℚ) (v : ℝ) (hv : (q : ℝ) = v) (hv1 : |v| ≤ 100) {d : ℝ} (hdd : |d| ≤ 1 / 200) :
    fl (sw fl q d) = sw fl q d := by
  have h2 : (2 : ℝ) * 100 ≤ 2 ^ 40 := by norm_num
  exact fl_sw hr q hdd (by norm_num) (by rw [hv]; linarith)

theorem idem_edg {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hM : (2 : ℝ) ^ 40 ≤ M)
    (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (k : ℕ) :
    fl (edg fl p w k) = edg fl p w k := by
  have h2 : ((dg (tokAt w k) : ℕ) : ℝ) ≤ 2 := by exact_mod_cast dg_le _
  have h0 : (0 : ℝ) ≤ ((dg (tokAt w k) : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold edg
  exact idem_sw hr hM _ ((dg (tokAt w k) : ℕ) : ℝ) (by norm_num)
    (by rw [abs_of_nonneg h0]; linarith) (hp.E _ 2)

theorem idem_eis {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hM : (2 : ℝ) ^ 40 ≤ M)
    (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (k : ℕ) :
    fl (eis fl p w k) = eis fl p w k := by
  have h2 : ((isn (tokAt w k) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast isn_le _
  have h0 : (0 : ℝ) ≤ ((isn (tokAt w k) : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold eis
  exact idem_sw hr hM _ ((isn (tokAt w k) : ℕ) : ℝ) (by norm_num)
    (by rw [abs_of_nonneg h0]; linarith) (hp.E _ 3)

theorem hsk_gen {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i k : ℕ) (S' P' : ℝ)
    (hS' : S' = sw fl 20 (p.A 0 0 5 6)) (hP' : P' = sw fl (-100) (p.A 0 0 7 0))
    (hI : fl (fl (S' * fl (k : ℝ))) = fl (S' * fl (k : ℝ)))
    (hJ : fl (fl (P' * epr fl p w k)) = fl (P' * epr fl p w k)) :
    hscore hd fl (p.A 0 0) (net.init fl p w) i k
      = fl (fl (S' * fl (k : ℝ))
          + fl (fl (((w.length + 1 : ℕ) : ℝ)) * fl (P' * epr fl p w k))) := by
  subst hS' hP'
  simp only [hscore, init_eq hr p w hw, pos, List.cons_append, List.nil_append]
  exact score_eq hr (p.A 0 0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI hJ

theorem hfk_gen {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (k : ℕ) (V' : ℝ) (hV' : V' = sw fl 1 (p.V 0 0 4 1))
    (hI : fl (fl (V' * eg fl p w k)) = fl (V' * eg fl p w k)) :
    rdot fl [0, 1, 0, 0, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 4) 0 0
      = fl (V' * eg fl p w k) := by
  subst hV'
  simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
  exact val_eq hr (p.V 0 0 4) _ _ _ _ _ _ _ _ hI

theorem A_close {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hηs : η ≤ 1 / 10 ^ 40) (h16 : 16 ≤ M) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hM40 : (2 : ℝ) ^ 40 ≤ M) (hp : p.Within (1 / 200))
    (j : ℕ) (V' A : ℝ) (hV : |V' - 1| ≤ 503 / 100000)
    (hcl01 : cls (tokAt w j) = 0 ∨ cls (tokAt w j) = 1)
    (hA1 : |A - fl (V' * eg fl p w j)| ≤ 11 / 1000 + 1 / 2 ^ 90) :
    |A - ((cls (tokAt w j) : ℕ) : ℝ)| ≤ 43 / 2000 := by
  have hη6 : η ≤ 1 / 10 ^ 6 := le_trans hηs (by norm_num)
  have hs : (1 : ℝ) / 2 ^ 90 ≤ 1 / 10 ^ 6 := by norm_num
  have ht5 : tokAt w j ≤ 5 := tok_le w hw j
  rcases hcl01 with h | h
  · have hg : gn (tokAt w j) = 0 := by
      have := (gn_eq _ ht5)
      have := gn_le (tokAt w j)
      omega
    rcases ent_g hr hu0 hu1 hM40 hη6 p hp w j with ⟨_, he⟩ | ⟨h1, _⟩
    · rw [he, mul_zero, hr.zero] at hA1
      rw [h]
      simp only [Nat.cast_zero, sub_zero] at hA1 ⊢
      linarith
    · omega
  · have hg : gn (tokAt w j) = 1 := by
      have := (gn_eq _ ht5)
      omega
    rcases ent_g hr hu0 hu1 hM40 hη6 p hp w j with ⟨h1, _⟩ | ⟨_, he⟩
    · omega
    · have hone : |(1 : ℝ)| ≤ 1 := by norm_num
      have s1 := mul_b (m := 1) hV he hone hone (by norm_num) (by norm_num) (by ring)
      obtain ⟨f1, _⟩ := flb hr hu0 hu1 hηs h16 (e := 101 / 10000) (Bt := 1)
        (le_trans s1 (by norm_num)) hone (by norm_num)
      rw [h]
      simp only [Nat.cast_one]
      have := abs_sub_le A (fl (V' * eg fl p w j)) 1
      linarith

theorem finish {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hηs : η ≤ 1 / 10 ^ 40) (hM40 : (2 : ℝ) ^ 40 ≤ M) (h16 : 16 ≤ M)
    (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) (j : ℕ)
    (hcl01 : cls (tokAt w j) = 0 ∨ cls (tokAt w j) = 1)
    (hjc : carry (w.take (i - 1)) = cls (tokAt w j)) (A : ℝ)
    (hattn : sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, 0, 0, A, 0, 0, 0])
    (hA2 : fl A = A) (hAc : |A - ((cls (tokAt w j) : ℕ) : ℝ)| ≤ 43 / 2000) :
    |sout net fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  have hη6 : η ≤ 1 / 10 ^ 6 := le_trans hηs (by norm_num)
  obtain ⟨w1a, h1a⟩ : ∃ x : ℝ, x = sw fl 1 (p.W1 0 0 3) := ⟨_, rfl⟩
  obtain ⟨w1b, h1b⟩ : ∃ x : ℝ, x = sw fl 1 (p.W1 0 0 4) := ⟨_, rfl⟩
  obtain ⟨bb, hbb⟩ : ∃ x : ℝ, x = sw fl (-1) (p.b1 0 0) := ⟨_, rfl⟩
  obtain ⟨w2, h2⟩ : ∃ x : ℝ, x = sw fl (-3) (p.W2 0 4 0) := ⟨_, rfl⟩
  obtain ⟨o2, ho2⟩ : ∃ x : ℝ, x = sw fl 1 (p.oW 2) := ⟨_, rfl⟩
  obtain ⟨o4, ho4⟩ : ∃ x : ℝ, x = sw fl 1 (p.oW 4) := ⟨_, rfl⟩
  obtain ⟨pre, hpre⟩ : ∃ x : ℝ, x = fl (fl (fl (w1a * eis fl p w i) + fl (w1b * A)) + bb) :=
    ⟨_, rfl⟩
  have b1a : |w1a - 1| ≤ 503 / 100000 := by
    rw [h1a]
    exact sw_w hr hu0 hu1 hM40 1 1 (by norm_num) (by norm_num) (hp.W1 0 0 3) _
      (by rw [abs_one]; linarith)
  have b1b : |w1b - 1| ≤ 503 / 100000 := by
    rw [h1b]
    exact sw_w hr hu0 hu1 hM40 1 1 (by norm_num) (by norm_num) (hp.W1 0 0 4) _
      (by rw [abs_one]; linarith)
  have bbb : |bb - (-1)| ≤ 503 / 100000 := by
    rw [hbb]
    exact sw_w hr hu0 hu1 hM40 (-1) (-1) (by norm_num) (by norm_num) (hp.b1 0 0) _
      (by rw [abs_neg, abs_one]; linarith)
  have b2b : |w2 - (-3)| ≤ 1509 / 100000 := by
    rw [h2]
    exact sw_w hr hu0 hu1 hM40 (-3) (-3) (by norm_num) (by norm_num) (hp.W2 0 4 0) _
      (by rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]; linarith)
  have bo2 : |o2 - 1| ≤ 503 / 100000 := by
    rw [ho2]
    exact sw_w hr hu0 hu1 hM40 1 1 (by norm_num) (by norm_num) (hp.oW 2) _
      (by rw [abs_one]; linarith)
  have bo4 : |o4 - 1| ≤ 503 / 100000 := by
    rw [ho4]
    exact sw_w hr hu0 hu1 hM40 1 1 (by norm_num) (by norm_num) (hp.oW 4) _
      (by rw [abs_one]; linarith)
  have hdgb := ent_dg hr hu0 hu1 hM40 hη6 p hp w i
  have hisb := ent_is hr hu0 hu1 hM40 hη6 p hp w i
  have hD : (0 : ℝ) ≤ ((dg (tokAt w i) : ℕ) : ℝ) ∧ ((dg (tokAt w i) : ℕ) : ℝ) ≤ 2 :=
    ⟨Nat.cast_nonneg _, by exact_mod_cast dg_le _⟩
  have hI01 : ((isn (tokAt w i) : ℕ) : ℝ) = 0 ∨ ((isn (tokAt w i) : ℕ) : ℝ) = 1 := by
    have := isn_le (tokAt w i)
    rcases (by omega : isn (tokAt w i) = 0 ∨ isn (tokAt w i) = 1) with h | h
    · left; rw [h]; simp
    · right; rw [h]; simp
  have hc01 : ((cls (tokAt w j) : ℕ) : ℝ) = 0 ∨ ((cls (tokAt w j) : ℕ) : ℝ) = 1 := by
    rcases hcl01 with h | h
    · left; rw [h]; simp
    · right; rw [h]; simp
  obtain ⟨i1, i2, i3, i5, i6, hfin⟩ := final_num hr hu0 hu1 hηs h16 hD hI01 hc01 hdgb hisb hAc
    b1a b1b bbb b2b bo2 bo4 hpre
  have hout := out_eq hr p w hw i A w1a w1b bb w2 o2 o4 pre h1a h1b hbb h2 ho2 ho4 hpre hattn hA2
    (idem_edg hr hM40 p hp w i) (idem_eis hr hM40 p hp w i) i1 i2 i3 i5 i6
  -- the target
  have hti : 1 ≤ tokAt w i ∧ tokAt w i ≤ 5 := by
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    rw [Lane4.Seq.tokAt_succ w m (by omega)]
    exact hw _ (List.getElem_mem (by omega))
  have hgt : w.getD (i - 1) 0 = tokAt w i := by
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [Lane4.Seq.tokAt_succ w m (by omega)]
    first
      | exact List.getD_eq_getElem _ _ (by omega)
      | simp [List.getElem?_eq_getElem (show m < w.length by omega)]
  have htg : ((target w i : ℕ) : ℝ)
      = ((dg (tokAt w i) : ℕ) : ℝ) + ((cls (tokAt w j) : ℕ) : ℝ)
        - 3 * (((isn (tokAt w i) : ℕ) : ℝ) * ((cls (tokAt w j) : ℕ) : ℝ)) := by
    unfold target
    rw [hgt, hjc]
    have h5 : tokAt w i = 1 ∨ tokAt w i = 2 ∨ tokAt w i = 3 ∨ tokAt w i = 4 ∨ tokAt w i = 5 := by
      omega
    rcases h5 with h | h | h | h | h <;> rcases hcl01 with h0 | h0 <;>
      simp [h, h0, dg, isn] <;> norm_num
  rw [hout, htg]
  exact hfin

set_option maxHeartbeats 3200000 in
theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη p hp w hw hn hnη hM i hi1 hi
  have hn1 : 1 ≤ w.length + 1 := by omega
  have hnR : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hn1
  have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
    have := range_lin hM hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have h220 : 220 * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  have h16 : (16 : ℝ) ≤ M := range_const hM hn1 (by norm_num)
  have hM40 : (2 : ℝ) ^ 40 ≤ M := range_const hM hn1 (by norm_num)
  have hηs := eta_tiny hη
  have hη6 : η ≤ 1 / 10 ^ 6 := le_trans hηs (by norm_num)
  have hu6 : u ≤ 1 / 10 ^ 6 := le_trans hu1 (by norm_num)
  -- stored weights of the head
  obtain ⟨S', hS'⟩ : ∃ x : ℝ, x = sw fl 20 (p.A 0 0 5 6) := ⟨_, rfl⟩
  obtain ⟨P', hP'⟩ : ∃ x : ℝ, x = sw fl (-100) (p.A 0 0 7 0) := ⟨_, rfl⟩
  obtain ⟨V', hV'⟩ : ∃ x : ℝ, x = sw fl 1 (p.V 0 0 4 1) := ⟨_, rfl⟩
  have hS : |S' - 20| ≤ 1011 / 10000 := by
    rw [hS']
    exact sw_w hr hu0 hu1 hM40 20 20 (by norm_num) (by norm_num) (hp.A 0 0 5 6) _
      (by rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 20)]; linarith)
  have hP : |P' - (-100)| ≤ 2513 / 5000 := by
    rw [hP']
    exact sw_w hr hu0 hu1 hM40 (-100) (-100) (by norm_num) (by norm_num) (hp.A 0 0 7 0) _
      (by rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 100)]; linarith)
  have hV : |V' - 1| ≤ 503 / 100000 := by
    rw [hV']
    exact sw_w hr hu0 hu1 hM40 1 1 (by norm_num) (by norm_num) (hp.V 0 0 4 1) _
      (by rw [abs_one]; linarith)
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  obtain ⟨hP1, hP2⟩ := abs_le.mp hP
  obtain ⟨hV1, hV2⟩ := abs_le.mp hV
  -- positions
  have hpos : ∀ k : ℕ, k ≤ w.length + 1 →
      0 ≤ fl (k : ℝ) ∧ fl (k : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) + 1 / 100 :=
    fun k hk => hr.pos_le hu0 hη hk hn hnM
  have hposn := abs_le.mp (hr.pos_near hu0 hη (le_refl (w.length + 1)) hn hnM)
  -- entries
  have hepb : ∀ k : ℕ, 0 ≤ epr fl p w k ∧ epr fl p w k ≤ 102 / 100 := by
    intro k
    rcases ent_pr hr hu0 hu1 hM40 hη6 p hp w k with ⟨_, h⟩ | ⟨_, h⟩
    · rw [h]; constructor <;> norm_num
    · have := abs_le.mp h
      constructor <;> linarith [this.1, this.2]
  have hegb : ∀ k : ℕ, 0 ≤ eg fl p w k ∧ eg fl p w k ≤ 102 / 100 := by
    intro k
    rcases ent_g hr hu0 hu1 hM40 hη6 p hp w k with ⟨_, h⟩ | ⟨_, h⟩
    · rw [h]; constructor <;> norm_num
    · have := abs_le.mp h
      constructor <;> linarith [this.1, this.2]
  -- scores
  have hXb : ∀ k : ℕ, k ≤ w.length + 1 →
      |S' * fl (k : ℝ)| ≤ 22 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    obtain ⟨h0, h1⟩ := hpos k hk
    rw [abs_of_nonneg (mul_nonneg (by linarith) h0)]
    have := mul_le_mul_of_nonneg_right (show S' ≤ 21 by linarith) h0
    linarith
  have hPeb : ∀ k : ℕ, |P' * epr fl p w k| ≤ 104 := by
    intro k
    obtain ⟨h0, h1⟩ := hepb k
    have h2 : |P'| ≤ 101 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h3 : |epr fl p w k| ≤ 102 / 100 := by rw [abs_of_nonneg h0]; exact h1
    have := bmul h2 h3
    linarith
  have hsk : ∀ k : ℕ, k ≤ w.length + 1 → hscore hd fl (p.A 0 0) (net.init fl p w) i k
      = fl (fl (S' * fl (k : ℝ))
          + fl (fl (((w.length + 1 : ℕ) : ℝ)) * fl (P' * epr fl p w k))) := by
    intro k hk
    exact hsk_gen hr p w hw i k S' P' hS' hP'
      (hr.idem _ (le_trans (hXb k hk) (by linarith)))
      (hr.idem _ (le_trans (hPeb k) (by linarith)))
  have hsnp : ∀ k : ℕ, k ≤ w.length + 1 → prn (tokAt w k) = 0 →
      hscore hd fl (p.A 0 0) (net.init fl p w) i k = fl (S' * fl (k : ℝ)) := by
    intro k hk h0
    have he0 : epr fl p w k = 0 := by
      rcases ent_pr hr hu0 hu1 hM40 hη6 p hp w k with ⟨_, h⟩ | ⟨h1, _⟩
      · exact h
      · omega
    have hI := hr.idem _ (le_trans (hXb k hk) (by linarith))
    rw [hsk k hk, he0]
    simp [hr.zero, hI]
  have hspr : ∀ k : ℕ, k ≤ w.length + 1 → prn (tokAt w k) = 1 →
      -107 * ((w.length + 1 : ℕ) : ℝ) ≤ hscore hd fl (p.A 0 0) (net.init fl p w) i k
      ∧ hscore hd fl (p.A 0 0) (net.init fl p w) i k ≤ -72 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk h1
    have he1 : |epr fl p w k - 1| ≤ 503 / 100000 := by
      rcases ent_pr hr hu0 hu1 hM40 hη6 p hp w k with ⟨h0, _⟩ | ⟨_, h⟩
      · omega
      · exact h
    have he1' := abs_le.mp he1
    obtain ⟨hk0, hk1⟩ := hpos k hk
    rw [hsk k hk]
    exact prop_sc hr hu0 hu1 hηs hnR hn h220 (S := S') (P := P') (e := epr fl p w k)
      (qn := fl (((w.length + 1 : ℕ) : ℝ))) (qk := fl (k : ℝ)) ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ ⟨by linarith [he1'.1], by linarith [he1'.2]⟩
      ⟨by linarith [hposn.1], by linarith [hposn.2]⟩ ⟨hk0, hk1⟩
  -- the winner
  obtain ⟨j, hjle, hjcl, hjk, hjc⟩ := carry_ex w (i - 1) (by omega)
  have hjt5 : tokAt w j ≤ 5 := tok_le w hw j
  have hjprn : prn (tokAt w j) = 0 := by
    have h1 := prn_eq _ hjt5
    have h2 := prn_le (tokAt w j)
    omega
  have hjn : j ≤ w.length + 1 := by omega
  have hj : j ∈ cand Mask.strict (w.length + 1) i := by
    rw [Lane4.Seq.mem_cand_strict]; omega
  have hlen : (cand Mask.strict (w.length + 1) i).length ≤ w.length + 1 := by
    simp [cand]; omega
  have hsj0 : 0 ≤ hscore hd fl (p.A 0 0) (net.init fl p w) i j := by
    rw [hsnp j hjn hjprn]
    obtain ⟨h0, h1⟩ := hpos j hjn
    exact hr.nonneg (mul_nonneg (by linarith) h0) (le_trans (le_trans (le_abs_self _) (hXb j hjn)) (by linarith))
  have hgap : ∀ k ∈ cand Mask.strict (w.length + 1) i, k ≠ j →
      hscore hd fl (p.A 0 0) (net.init fl p w) i k
        ≤ hscore hd fl (p.A 0 0) (net.init fl p w) i j - 16 * (ndist j k : ℝ) := by
    intro k hk hne
    rw [Lane4.Seq.mem_cand_strict] at hk
    have hkn : k ≤ w.length + 1 := by omega
    have hkt5 : tokAt w k ≤ 5 := tok_le w hw k
    by_cases hpk : prn (tokAt w k) = 1
    · obtain ⟨_, hu⟩ := hspr k hkn hpk
      rw [ndist_cast]
      have hjR : (j : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hjn
      have hkR : (k : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hkn
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have habs : |(j : ℝ) - (k : ℝ)| ≤ ((w.length + 1 : ℕ) : ℝ) := by
        rw [abs_le]; constructor <;> linarith
      linarith
    · have hk0' : prn (tokAt w k) = 0 := by
        have := prn_le (tokAt w k)
        omega
      have hkj : k < j := by
        by_contra hcon
        have hjk' : j < k := by omega
        have := hjk k hjk' (by omega)
        have h1 := prn_eq _ hkt5
        omega
      rw [hsnp k hkn hk0', hsnp j hjn hjprn, ndist_cast]
      have hg := hr.pos_gap hu0 hη (le_of_lt hkj) hjn hn hnM
      have hgp := hr.gap hu0 (hXb k hkn) (hXb j hjn) (by linarith)
      have hd1 : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hkj
      rw [abs_of_nonneg (by linarith)]
      have hD0 : 0 ≤ fl (j : ℝ) - fl (k : ℝ) := by linarith
      have hSD := mul_le_mul_of_nonneg_right (show (198 : ℝ) / 10 ≤ S' by linarith) hD0
      have hun : u * (22 * ((w.length + 1 : ℕ) : ℝ)) = 22 * (u * ((w.length + 1 : ℕ) : ℝ)) := by
        ring
      linarith [hgp, hSD, hg, hd1, hn, hηs, hun]
  have hSb : ∀ k ∈ cand Mask.strict (w.length + 1) i,
      |hscore hd fl (p.A 0 0) (net.init fl p w) i k| ≤ 107 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    rw [Lane4.Seq.mem_cand_strict] at hk
    have hkn : k ≤ w.length + 1 := by omega
    by_cases hpk : prn (tokAt w k) = 1
    · obtain ⟨h1, h2⟩ := hspr k hkn hpk
      rw [abs_le]
      constructor <;> linarith
    · have hk0' : prn (tokAt w k) = 0 := by
        have := prn_le (tokAt w k)
        omega
      rw [hsnp k hkn hk0']
      have := hr.bound hu0 (hXb k hkn) (by linarith)
      have hun : u * (22 * ((w.length + 1 : ℕ) : ℝ)) = 22 * (u * ((w.length + 1 : ℕ) : ℝ)) := by
        ring
      linarith
  -- values
  have hVeb : ∀ k : ℕ, |V' * eg fl p w k| ≤ 51 / 50 := by
    intro k
    obtain ⟨h0, h1⟩ := hegb k
    obtain ⟨hg0, hg1⟩ := (abs_le.mp (show |eg fl p w k| ≤ 102 / 100 by
      rw [abs_of_nonneg h0]; exact h1))
    have h2 : |V'| ≤ 1006 / 1000 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h3 : |eg fl p w k| ≤ 1006 / 1000 := by
      rw [abs_of_nonneg h0]
      rcases ent_g hr hu0 hu1 hM40 hη6 p hp w k with ⟨_, h⟩ | ⟨_, h⟩
      · rw [h]; norm_num
      · have := abs_le.mp h
        linarith [this.2]
    have := bmul h2 h3
    linarith
  have hfk : ∀ k : ℕ, rdot fl [0, 1, 0, 0, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 4) 0 0
      = fl (V' * eg fl p w k) := by
    intro k
    exact hfk_gen hr p w hw k V' hV' (hr.idem _ (le_trans (hVeb k) (by linarith)))
  have hfB : ∀ k ∈ cand Mask.strict (w.length + 1) i,
      |(fun j => rdot fl [0, 1, 0, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 4) 0 0) k|
        ≤ 11 / 10 := by
    intro k _
    show |rdot fl [0, 1, 0, 0, 0, 0, 0, 0] (net.init fl p w k) (p.V 0 0 4) 0 0| ≤ 11 / 10
    rw [hfk k]
    have := hr.bound hu0 (hVeb k) (by linarith)
    linarith [hVeb k]
  obtain ⟨hA1, hA2⟩ := soft_near hr he hu0 hu1 hη0 hη (Lane4.Seq.cand_nodup _ _ _) hlen hn hnη
    hj hgap hSb (by linarith) hfB (by linarith)
  have hat := attn_eq (ex := ex) hr p w hw i
  have hcl01 : cls (tokAt w j) = 0 ∨ cls (tokAt w j) = 1 := by
    have := cls_le (tokAt w j)
    omega
  have hA1' : |savg fl ex (cand Mask.strict (w.length + 1) i)
      (hscore hd fl (p.A 0 0) (net.init fl p w) i)
      (fun j => rdot fl [0, 1, 0, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 4) 0 0)
      - fl (V' * eg fl p w j)| ≤ 11 / 1000 + 1 / 2 ^ 90 := by
    have := hA1
    simp only [hfk j] at this
    have e : (11 : ℝ) / 10 / 100 = 11 / 1000 := by norm_num
    linarith
  have hAc := A_close hr hu0 hu1 hηs h16 p w hw hM40 hp j V' _ hV hcl01 hA1'
  exact finish hr hu0 hu1 hηs hM40 h16 p hp w hw i hi1 hi j hcl01 hjc _ hat hA2 hAc

end Lane4.Case
