set_option linter.unusedVariables false
set_option linter.style.longLine false
namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

def z6 : List ℚ := [0, 0, 0, 0, 0, 0]

def hd : Head :=
  { A := [z6, z6, z6, [0, 0, 0, 0, -20, 0], [-120, -60, 0, 0, 0, 0], z6],
    V := [z6, z6, [0, 0, 1, 0, 0, 0], z6, z6, z6],
    mask := Mask.causal }

def blk : Block :=
  { heads := [hd], W1 := [[0, 0, 1, 0, 0, 0]], b1 := [-1],
    W2 := [[0], [0], [-2], [0], [0], [0]], b2 := z6 }

def net : TNet :=
  { embed := [[0, 1, 0], [0, 0, 0], [1, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 1]],
    blocks := [blk],
    outW := [0, 0, 1, 0, 0, 0],
    outB := 0 }

def uq (t : ℕ) : ℚ := if t = 2 then 1 else 0
def bq (t : ℕ) : ℚ := if t = 0 then 1 else 0
def fq (t : ℕ) : ℚ := if t = 5 then 1 else 0

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [sw fl (uq (tokAt w j)) (p.E (tokAt w j) 0),
      sw fl (bq (tokAt w j)) (p.E (tokAt w j) 1),
      sw fl (fq (tokAt w j)) (p.E (tokAt w j) 2)] ++ pos fl j (w.length + 1) := by
  have h5 := tok_le w hw j
  have h6 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4
      ∨ tokAt w j = 5 := by omega
  rcases h6 with h | h | h | h | h | h <;>
    simp [TNet.init, net, swRow, h, uq, bq, fq, sw_zero hr]

theorem zrow_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (d : ℕ → ℝ) (a b c e f g : ℝ) :
    rdot fl z6 [a, b, c, e, f, g] d 0 0 = 0 := by
  simp [z6, rdot, sw_zero hr, hr.zero]

noncomputable def R4 (fl : ℝ → ℝ) (d : ℕ → ℝ) (v : Vec) : ℝ :=
  rdot fl [-120, -60, 0, 0, 0, 0] v d 0 0

theorem r4_fold (fl : ℝ → ℝ) (d : ℕ → ℝ) (v : Vec) :
    rdot fl [-120, -60, 0, 0, 0, 0] v d 0 0 = R4 fl d v := rfl

theorem r3_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (d : ℕ → ℝ) (a b c e f g : ℝ)
    (hP : fl (fl (sw fl (-20) (d 4) * f)) = fl (sw fl (-20) (d 4) * f)) :
    rdot fl [0, 0, 0, 0, -20, 0] [a, b, c, e, f, g] d 0 0 = fl (sw fl (-20) (d 4) * f) := by
  simp [rdot, sw_zero hr, hr.zero, hP]

theorem score_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (xi xj : Vec) (a b c I nn x y f K nK : ℝ)
    (hxi : xi = [a, b, c, 1, I, nn]) (hxj : xj = [x, y, f, 1, K, nK])
    (hP : fl (fl (sw fl (-20) (dA 3 4) * K)) = fl (sw fl (-20) (dA 3 4) * K))
    (hI : fl (fl (fl (sw fl (-20) (dA 3 4) * K) + fl (I * R4 fl (dA 4) xj)))
      = fl (fl (sw fl (-20) (dA 3 4) * K) + fl (I * R4 fl (dA 4) xj))) :
    hd.score fl dA xi xj
      = fl (fl (sw fl (-20) (dA 3 4) * K) + fl (I * R4 fl (dA 4) xj)) := by
  have h3 := r3_eq hr (dA 3) x y f 1 K nK hP
  subst hxi
  subst hxj
  simp [Head.score, hd, pdot, rmat, zrow_eq hr, h3, r4_fold, hr.zero, hP, hI]

theorem attn_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) :
    sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, savg fl ex (cand Mask.causal (w.length + 1) i)
              (hscore hd fl (p.A 0 0) (net.init fl p w) i)
              (fun j => rdot fl [0, 0, 1, 0, 0, 0] (net.init fl p w j) (p.V 0 0 2) 0 0),
         0, 0, 0] := by
  have hV : hd.V = [z6, z6, [0, 0, 1, 0, 0, 0], z6, z6, z6] := rfl
  have hm : hd.mask = Mask.causal := rfl
  have hz : ∀ d : ℕ → ℝ,
      savg fl ex (cand Mask.causal (w.length + 1) i)
        (hscore hd fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl z6 (net.init fl p w j) d 0 0) = 0 := by
    intro d
    apply soft_zeros hr
    intro k _
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact zrow_eq hr d _ _ _ _ _ _
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz]

theorem out_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (i : ℕ) (a b f I nn A : ℝ)
    (hinit : net.init fl p w i = [a, b, f, 1, I, nn])
    (hattn : sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, A, 0, 0, 0])
    (hA : fl A = A)
    (hq1 : fl (fl (sw fl 1 (p.W1 0 0 2) * fl (f + A))) = fl (sw fl 1 (p.W1 0 0 2) * fl (f + A)))
    (hq2 : fl (fl (sw fl (-2) (p.W2 0 2 0) *
        Lane4.relu (fl (fl (sw fl 1 (p.W1 0 0 2) * fl (f + A)) + sw fl (-1) (p.b1 0 0)))))
      = fl (sw fl (-2) (p.W2 0 2 0) *
        Lane4.relu (fl (fl (sw fl 1 (p.W1 0 0 2) * fl (f + A)) + sw fl (-1) (p.b1 0 0)))))
    (hq3 : fl (fl (sw fl 1 (p.oW 2) * fl (fl (f + A) + fl (sw fl (-2) (p.W2 0 2 0) *
        Lane4.relu (fl (fl (sw fl 1 (p.W1 0 0 2) * fl (f + A)) + sw fl (-1) (p.b1 0 0)))))))
      = fl (sw fl 1 (p.oW 2) * fl (fl (f + A) + fl (sw fl (-2) (p.W2 0 2 0) *
        Lane4.relu (fl (fl (sw fl 1 (p.W1 0 0 2) * fl (f + A)) + sw fl (-1) (p.b1 0 0))))))) :
    sout net fl ex p w i
      = fl (sw fl 1 (p.oW 2) * fl (fl (f + A) + fl (sw fl (-2) (p.W2 0 2 0) *
        Lane4.relu (fl (fl (sw fl 1 (p.W1 0 0 2) * fl (f + A)) + sw fl (-1) (p.b1 0 0))))))  := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 0, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  unfold sout srun
  rw [hb, ho, hc]
  simp only [srunFrom, sblock, blk, sheadsApply, hattn, hinit]
  simp [z6, rdot, radd, raffine, sw_zero hr, hr.zero, hA, hq1, hq2, hq3]


theorem flsmall {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) (hM : (8 : ℝ) ≤ M) {x : ℝ} (hx : |x| ≤ 8) :
    |fl x - x| ≤ 1 / 10 ^ 6 := by
  have h := hr.abs hu0 hx hM
  have h2 := eta_tiny hη
  linarith

theorem st1 {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) (hM : (8 : ℝ) ≤ M) {x y e : ℝ}
    (hx : |x - y| ≤ e) (hb : |x| ≤ 8) : |fl x - y| ≤ e + 1 / 10 ^ 6 := by
  have h1 := flsmall hr hu0 hu1 hη hM hb
  have h2 := abs_sub_le (fl x) x y
  linarith

theorem relu_lip (a b : ℝ) : |Lane4.relu a - Lane4.relu b| ≤ |a - b| := by
  unfold Lane4.relu
  have h1 := le_abs_self (a - b)
  have h2 := neg_abs_le (a - b)
  rw [abs_le]
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [max_eq_right ha, max_eq_right hb]; constructor <;> linarith [abs_nonneg (a - b)]
  · rw [max_eq_right ha, max_eq_left hb]; constructor <;> linarith
  · rw [max_eq_left ha, max_eq_right hb]; constructor <;> linarith
  · rw [max_eq_left ha, max_eq_left hb]; constructor <;> linarith

theorem prod_close {a y e B : ℝ} (h : |a - 1| ≤ e) (hy : |y| ≤ B) : |a * y - y| ≤ e * B := by
  have : a * y - y = (a - 1) * y := by ring
  rw [this, abs_mul]
  exact mul_le_mul h hy (abs_nonneg _) (le_trans (abs_nonneg _) h)

theorem abs_add_close {a b c d e1 e2 : ℝ} (h1 : |a - b| ≤ e1) (h2 : |c - d| ≤ e2) :
    |(a + c) - (b + d)| ≤ e1 + e2 := by
  have := abs_add_le (a - b) (c - d)
  have h : a - b + (c - d) = (a + c) - (b + d) := by ring
  rw [h] at this
  linarith

theorem flerr {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hη : η ≤ 1 / 2 ^ 149) {x c N : ℝ} (hc : 0 ≤ c) (hx : |x| ≤ c * N) (hcM : c * N ≤ M)
    (hn : u * N ≤ 1 / 256) : |fl x - x| ≤ c / 256 + 1 / 10 ^ 40 := by
  have h := hr.abs hu0 hx hcM
  have h2 := eta_tiny hη
  have h3 : u * (c * N) = c * (u * N) := by ring
  have h4 : c * (u * N) ≤ c * (1 / 256) := mul_le_mul_of_nonneg_left hn hc
  linarith

theorem score_dev {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hη : η ≤ 1 / 2 ^ 149) {N S K I R : ℝ} (hN : 1 ≤ N) (hn : u * N ≤ 1 / 256)
    (hM : 150 * N ≤ M) (hSK : |S * K| ≤ 21 * N) (hIR : |I * R| ≤ 124 * N) :
    |fl (fl (S * K) + fl (I * R)) - (S * K + I * R)| ≤ 6 / 5 := by
  have e1 := flerr hr hu0 hη (c := 21) (by norm_num) hSK (by linarith) hn
  have e2 := flerr hr hu0 hη (c := 124) (by norm_num) hIR (by linarith) hn
  have h1 := abs_le.mp hSK
  have h2 := abs_le.mp hIR
  have e1' := abs_le.mp e1
  have e2' := abs_le.mp e2
  have hX : |fl (S * K) + fl (I * R)| ≤ 150 * N := by
    rw [abs_le]; constructor <;> linarith
  have e3 := flerr hr hu0 hη (c := 150) (by norm_num) hX hM hn
  have g1 := abs_sub_le (fl (fl (S * K) + fl (I * R))) (fl (S * K) + fl (I * R)) (S * K + I * R)
  have g2 := abs_add_le (fl (S * K) - S * K) (fl (I * R) - I * R)
  have g3 : (fl (S * K) - S * K) + (fl (I * R) - I * R)
      = fl (S * K) + fl (I * R) - (S * K + I * R) := by ring
  rw [g3] at g2
  linarith

theorem swb {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2 ^ 24)
    (w : ℚ) (W Wa : ℝ) (hw : (w : ℝ) = W) (hWa : |W| = Wa) {d : ℝ} (hd : |d| ≤ 1 / 200)
    (hWM : 2 * Wa ≤ M) : |sw fl w d - W| ≤ 1 / 199 * Wa + η := by
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by linarith
  have h := sw_near hr hu0 w hd (by norm_num) (by rw [hw, hWa]; exact hWM) hε
  rw [hw, hWa] at h
  exact h

theorem chain {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) (hM : (8 : ℝ) ≤ M)
    (f A Wp B1 W2s Wo ai aj : ℝ) (hai : ai = 0 ∨ ai = 1) (haj : aj = 0 ∨ aj = 1)
    (hf : |f - ai| ≤ 1 / 190) (hA : |A - aj| ≤ 1 / 45) (hWp : |Wp - 1| ≤ 1 / 190)
    (hB1 : |B1 - (-1)| ≤ 1 / 190) (hW2 : |W2s - (-2)| ≤ 1 / 90) (hWo : |Wo - 1| ≤ 1 / 190) :
    fl (fl (Wp * fl (f + A))) = fl (Wp * fl (f + A)) ∧
    fl (fl (W2s * Lane4.relu (fl (fl (Wp * fl (f + A)) + B1))))
      = fl (W2s * Lane4.relu (fl (fl (Wp * fl (f + A)) + B1))) ∧
    fl (fl (Wo * fl (fl (f + A) + fl (W2s * Lane4.relu (fl (fl (Wp * fl (f + A)) + B1))))))
      = fl (Wo * fl (fl (f + A) + fl (W2s * Lane4.relu (fl (fl (Wp * fl (f + A)) + B1))))) ∧
    |fl (Wo * fl (fl (f + A) + fl (W2s * Lane4.relu (fl (fl (Wp * fl (f + A)) + B1)))))
      - (if ai = aj then 0 else 1)| ≤ 1 / 4 := by
  obtain ⟨hf1, hf2⟩ := abs_le.mp hf
  obtain ⟨hA1, hA2⟩ := abs_le.mp hA
  obtain ⟨hWp1, hWp2⟩ := abs_le.mp hWp
  obtain ⟨hW21, hW22⟩ := abs_le.mp hW2
  obtain ⟨hWo1, hWo2⟩ := abs_le.mp hWo
  have hai1 : 0 ≤ ai ∧ ai ≤ 1 := by rcases hai with h | h <;> rw [h] <;> norm_num
  have haj1 : 0 ≤ aj ∧ aj ≤ 1 := by rcases haj with h | h <;> rw [h] <;> norm_num
  obtain ⟨ha0, ha1⟩ := hai1
  obtain ⟨hb0, hb1⟩ := haj1
  have hid : 0 ≤ Lane4.relu (ai + aj - 1) ∧ Lane4.relu (ai + aj - 1) ≤ 1 := by
    unfold Lane4.relu
    exact ⟨le_max_right _ _, max_le (by linarith) (by norm_num)⟩
  obtain ⟨hid0, hid1⟩ := hid
  have ht : (ai + aj) + (-2) * Lane4.relu (ai + aj - 1) = if ai = aj then 0 else 1 := by
    rcases hai with h | h <;> rcases haj with h' | h' <;> subst h <;> subst h' <;>
      norm_num [Lane4.relu, max_def]
  have htb : |(ai + aj) + (-2) * Lane4.relu (ai + aj - 1)| ≤ 1 := by
    rw [ht]; split_ifs <;> norm_num
  have e1 : |fl (f + A) - (ai + aj)| ≤ 3 / 100 := by
    have h := st1 hr hu0 hu1 hη hM (x := f + A) (y := ai + aj) (e := 1 / 190 + 1 / 45)
      (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
    linarith
  obtain ⟨e1a, e1b⟩ := abs_le.mp e1
  have hY : |fl (f + A)| ≤ 21 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hWpa : |Wp| ≤ 11 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hWY : |Wp * fl (f + A)| ≤ 8 := by
    rw [abs_mul]
    have := mul_le_mul hWpa hY (abs_nonneg _) (by norm_num)
    linarith
  have hq1 : fl (fl (Wp * fl (f + A))) = fl (Wp * fl (f + A)) := hr.idem _ (le_trans hWY hM)
  have e2 : |fl (Wp * fl (f + A)) - (ai + aj)| ≤ 5 / 100 := by
    have hp1 := prod_close hWp hY
    have h1 := abs_sub_le (Wp * fl (f + A)) (fl (f + A)) (ai + aj)
    have h := st1 hr hu0 hu1 hη hM (x := Wp * fl (f + A)) (y := ai + aj)
      (e := 1 / 190 * (21 / 10) + 3 / 100) (by linarith) hWY
    linarith
  have e3 : |fl (Wp * fl (f + A)) + B1 - (ai + aj - 1)| ≤ 6 / 100 := by
    have h := abs_add_close e2 hB1
    have h' : (ai + aj) + (-1) = ai + aj - 1 := by ring
    rw [h'] at h
    linarith
  have hs3 : |fl (Wp * fl (f + A)) + B1| ≤ 8 := by
    obtain ⟨x1, x2⟩ := abs_le.mp e3
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have e4 : |fl (fl (Wp * fl (f + A)) + B1) - (ai + aj - 1)| ≤ 7 / 100 := by
    have h := st1 hr hu0 hu1 hη hM (x := fl (Wp * fl (f + A)) + B1) (y := ai + aj - 1)
      (e := 6 / 100) e3 hs3
    linarith
  have e5 := le_trans (relu_lip (fl (fl (Wp * fl (f + A)) + B1)) (ai + aj - 1)) e4
  obtain ⟨e5a, e5b⟩ := abs_le.mp e5
  generalize Lane4.relu (fl (fl (Wp * fl (f + A)) + B1)) = hh at e5a e5b ⊢
  have hhb : |hh| ≤ 11 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hW2a : |W2s| ≤ 21 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hWH : |W2s * hh| ≤ 8 := by
    rw [abs_mul]
    have := mul_le_mul hW2a hhb (abs_nonneg _) (by norm_num)
    linarith
  have hq2 : fl (fl (W2s * hh)) = fl (W2s * hh) := hr.idem _ (le_trans hWH hM)
  have e6 : |W2s * hh - (-2) * Lane4.relu (ai + aj - 1)| ≤ 16 / 100 := by
    have h1 : W2s * hh - (-2) * Lane4.relu (ai + aj - 1)
        = (W2s - (-2)) * hh + (-2) * (hh - Lane4.relu (ai + aj - 1)) := by ring
    rw [h1]
    have h2 : |(W2s - (-2)) * hh| ≤ 1 / 90 * (11 / 10) := by
      rw [abs_mul]; exact mul_le_mul hW2 hhb (abs_nonneg _) (by norm_num)
    have h3 : |(-2) * (hh - Lane4.relu (ai + aj - 1))| ≤ 2 * (7 / 100) := by
      rw [abs_mul]
      have h6 : |hh - Lane4.relu (ai + aj - 1)| ≤ 7 / 100 := abs_le.mpr ⟨by linarith, by linarith⟩
      have h5 : |(-2 : ℝ)| = 2 := by norm_num
      rw [h5]
      exact mul_le_mul_of_nonneg_left h6 (by norm_num)
    have h4 := abs_add_le ((W2s - (-2)) * hh) ((-2) * (hh - Lane4.relu (ai + aj - 1)))
    linarith
  have e7 : |fl (W2s * hh) - (-2) * Lane4.relu (ai + aj - 1)| ≤ 17 / 100 := by
    have h := st1 hr hu0 hu1 hη hM (x := W2s * hh) (y := (-2) * Lane4.relu (ai + aj - 1))
      (e := 16 / 100) e6 hWH
    linarith
  have e8 : |fl (f + A) + fl (W2s * hh) - ((ai + aj) + (-2) * Lane4.relu (ai + aj - 1))|
      ≤ 20 / 100 := by
    have h := abs_add_close e1 e7
    linarith
  have hXs : |fl (f + A) + fl (W2s * hh)| ≤ 8 := by
    obtain ⟨x1, x2⟩ := abs_le.mp e8
    obtain ⟨x3, x4⟩ := abs_le.mp htb
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have e9 : |fl (fl (f + A) + fl (W2s * hh)) - ((ai + aj) + (-2) * Lane4.relu (ai + aj - 1))|
      ≤ 21 / 100 := by
    have h := st1 hr hu0 hu1 hη hM (x := fl (f + A) + fl (W2s * hh))
      (y := (ai + aj) + (-2) * Lane4.relu (ai + aj - 1)) (e := 20 / 100) e8 hXs
    linarith
  have hXX : |fl (fl (f + A) + fl (W2s * hh))| ≤ 13 / 10 := by
    obtain ⟨x1, x2⟩ := abs_le.mp e9
    obtain ⟨x3, x4⟩ := abs_le.mp htb
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hWoa : |Wo| ≤ 11 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hWX : |Wo * fl (fl (f + A) + fl (W2s * hh))| ≤ 8 := by
    rw [abs_mul]
    have := mul_le_mul hWoa hXX (abs_nonneg _) (by norm_num)
    linarith
  have hq3 : fl (fl (Wo * fl (fl (f + A) + fl (W2s * hh))))
      = fl (Wo * fl (fl (f + A) + fl (W2s * hh))) := hr.idem _ (le_trans hWX hM)
  have e10 : |Wo * fl (fl (f + A) + fl (W2s * hh))
      - ((ai + aj) + (-2) * Lane4.relu (ai + aj - 1))| ≤ 22 / 100 := by
    have p1 := prod_close hWo hXX
    have p2 := abs_sub_le (Wo * fl (fl (f + A) + fl (W2s * hh)))
      (fl (fl (f + A) + fl (W2s * hh))) ((ai + aj) + (-2) * Lane4.relu (ai + aj - 1))
    linarith
  have e11 := st1 hr hu0 hu1 hη hM (x := Wo * fl (fl (f + A) + fl (W2s * hh)))
    (y := (ai + aj) + (-2) * Lane4.relu (ai + aj - 1)) (e := 22 / 100) e10 hWX
  refine ⟨hq1, hq2, hq3, ?_⟩
  rw [← ht]
  linarith

theorem R4_zero {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (d : ℕ → ℝ) (x y f e K nK : ℝ)
    (hx : x = 0) (hy : y = 0) : R4 fl d [x, y, f, e, K, nK] = 0 := by
  subst hx
  subst hy
  simp [R4, rdot, sw_zero hr, hr.zero]

theorem R4_tok2 {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (d : ℕ → ℝ) (x f e K nK : ℝ)
    (hI : fl (fl (sw fl (-120) (d 0) * x)) = fl (sw fl (-120) (d 0) * x)) :
    R4 fl d [x, 0, f, e, K, nK] = fl (sw fl (-120) (d 0) * x) := by
  simp [R4, rdot, sw_zero hr, hr.zero, hI]

theorem R4_bos {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (d : ℕ → ℝ) (y f e K nK : ℝ)
    (hI : fl (fl (sw fl (-60) (d 1) * y)) = fl (sw fl (-60) (d 1) * y)) :
    R4 fl d [0, y, f, e, K, nK] = fl (sw fl (-60) (d 1) * y) := by
  simp [R4, rdot, sw_zero hr, hr.zero, hI]

theorem val_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (d : ℕ → ℝ) (x y f e K nK : ℝ)
    (hI : fl (fl (sw fl 1 (d 2) * f)) = fl (sw fl 1 (d 2) * f)) :
    rdot fl [0, 0, 1, 0, 0, 0] [x, y, f, e, K, nK] d 0 0 = fl (sw fl 1 (d 2) * f) := by
  simp [rdot, sw_zero hr, hr.zero, hI]

theorem tgt_arith (a b : ℕ) :
    ((if code a = 2 then 1 else 0) + cbit b) % 2 = if (a = 5 ↔ b = 5) then 0 else 1 := by
  unfold code cbit
  split_ifs <;> omega

theorem tok_pos (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ w.length) : 1 ≤ tokAt w j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [Lane4.Seq.tokAt_succ w m (by omega)]
  exact (hw _ (List.getElem_mem _)).1

theorem first_ex (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) :
    ∀ i, i ≤ w.length → ∃ j, j ≤ i ∧ (∀ k, 1 ≤ k → k < j → tokAt w k = 2) ∧
      ((j = 0 ∧ ∀ k, 1 ≤ k → k ≤ i → tokAt w k = 2) ∨ (1 ≤ j ∧ tokAt w j ≠ 2)) ∧
      firstc (w.take i) = code (tokAt w j) := by
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨0, le_refl _, fun k hk hk' => by omega,
      Or.inl ⟨rfl, fun k hk hk' => by omega⟩, by simp [firstc, code, tokAt]⟩
  | succ i ih =>
    intro hi
    obtain ⟨j, hji, hlt, hcase, hfc⟩ := ih (by omega)
    have hlt' : i < w.length := by omega
    have hstep : firstc (w.take (i + 1))
        = if firstc (w.take i) = 0 then code (tokAt w (i + 1)) else firstc (w.take i) := by
      have htok : tokAt w (i + 1) = w[i] := Lane4.Seq.tokAt_succ w i hlt'
      unfold firstc
      rw [List.take_succ, List.getElem?_eq_getElem hlt']
      simp [List.foldl_append, htok]
    rcases hcase with ⟨hj0, hall⟩ | ⟨hj1, hjm⟩
    · have hfc0 : firstc (w.take i) = 0 := by rw [hfc, hj0]; simp [code, tokAt]
      by_cases h2 : tokAt w (i + 1) = 2
      · refine ⟨0, by omega, fun k hk hk' => by omega, Or.inl ⟨rfl, ?_⟩, ?_⟩
        · intro k hk hk'
          by_cases hki : k = i + 1
          · rw [hki]; exact h2
          · exact hall k hk (by omega)
        · rw [hstep, hfc0]; simp [h2, code, tokAt]
      · refine ⟨i + 1, le_refl _, ?_, Or.inr ⟨by omega, h2⟩, ?_⟩
        · intro k hk hk'; exact hall k hk (by omega)
        · rw [hstep, hfc0]; simp
    · have hne : firstc (w.take i) ≠ 0 := by
        rw [hfc]
        have h1 := tok_pos w hw j hj1 (by omega)
        unfold code
        split_ifs <;> omega
      refine ⟨j, by omega, hlt, Or.inr ⟨hj1, hjm⟩, ?_⟩
      rw [hstep, if_neg hne]
      exact hfc

end Lane4.Case
