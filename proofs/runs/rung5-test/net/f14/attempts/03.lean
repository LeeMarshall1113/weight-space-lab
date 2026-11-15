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
      have hsplit : w.take (i + 1) = w.take i ++ [w[i]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt']; rfl
      unfold firstc
      rw [hsplit, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, htok]
    rcases hcase with ⟨hj0, hall⟩ | ⟨hj1, hjm⟩
    · have hfc0 : firstc (w.take i) = 0 := by rw [hfc, hj0]; simp [code, tokAt]
      by_cases h2 : tokAt w (i + 1) = 2
      · refine ⟨0, by omega, fun k hk hk' => by omega, Or.inl ⟨rfl, ?_⟩, ?_⟩
        · intro k hk hk'
          by_cases hki : k = i + 1
          · rw [hki]; exact h2
          · exact hall k hk (by omega)
        · rw [hstep, hfc0, if_pos rfl, h2]; simp [code, tokAt]
      · refine ⟨i + 1, le_refl _, ?_, Or.inr ⟨by omega, h2⟩, ?_⟩
        · intro k hk hk'; exact hall k hk (by omega)
        · rw [hstep, hfc0]; simp
    · have hne : firstc (w.take i) ≠ 0 := by
        rw [hfc]
        have h1 := tok_pos w hw j hj1 (by omega)
        have h5 := tok_le w hw j
        unfold code
        split_ifs <;> omega
      refine ⟨j, by omega, hlt, Or.inr ⟨hj1, hjm⟩, ?_⟩
      rw [hstep, if_neg hne]
      exact hfc


noncomputable def Rk (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (k : ℕ) : ℝ :=
  R4 fl (p.A 0 0 4) (net.init fl p w k)

noncomputable def vf (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (k : ℕ) : ℝ :=
  rdot fl [0, 0, 1, 0, 0, 0] (net.init fl p w k) (p.V 0 0 2) 0 0

theorem sum_bd {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hη : η ≤ 1 / 2 ^ 149) {N S K I R : ℝ} (hN : 1 ≤ N) (hn : u * N ≤ 1 / 256)
    (hSK : |S * K| ≤ 21 * N) (hIR : |I * R| ≤ 124 * N) (hM1 : 21 * N ≤ M) (hM2 : 124 * N ≤ M) :
    |fl (S * K) + fl (I * R)| ≤ 150 * N := by
  have e1 := flerr hr hu0 hη (c := 21) (by norm_num) hSK hM1 hn
  have e2 := flerr hr hu0 hη (c := 124) (by norm_num) hIR hM2 hn
  have h1 := abs_le.mp hSK
  have h2 := abs_le.mp hIR
  have e1' := abs_le.mp e1
  have e2' := abs_le.mp e2
  rw [abs_le]; constructor <;> linarith

theorem big_fl {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) (hM : (200 : ℝ) ≤ M) {x : ℝ}
    (hx : |x| ≤ 200) : fl (fl x) = fl x ∧ |fl x - x| ≤ 1 / 10 ^ 4 := by
  refine ⟨hr.idem x (le_trans hx hM), ?_⟩
  have h := hr.abs hu0 hx hM
  have h2 := eta_tiny hη
  linarith

set_option maxHeartbeats 6400000 in
theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη p hp w hw hn hnη hM i hi1 hi
  have hn1 : 1 ≤ w.length + 1 := by omega
  have hnR : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hn1
  have R1 : ∀ c : ℝ, 0 ≤ c → c ≤ 2 ^ 40 → c * ((w.length + 1 : ℕ) : ℝ) ≤ M :=
    fun c h0 h1 => range_lin hM hn1 h0 h1
  have R0 : ∀ c : ℝ, c ≤ 2 ^ 40 → c ≤ M := fun c h => range_const hM hn1 h
  have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
    have := R1 1 (by norm_num) (by norm_num)
    linarith
  have hM8 : (8 : ℝ) ≤ M := R0 8 (by norm_num)
  have hM200 : (200 : ℝ) ≤ M := R0 200 (by norm_num)
  have hη1 := eta_tiny hη
  have hposle : ∀ k : ℕ, k ≤ w.length + 1 →
      0 ≤ fl (k : ℝ) ∧ fl (k : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) + 1 / 100 :=
    fun k hk => hr.pos_le hu0 hη hk hn hnM
  have hposnear : ∀ k : ℕ, k ≤ w.length + 1 → |fl (k : ℝ) - k| ≤ 1 / 200 :=
    fun k hk => hr.pos_near hu0 hη hk hn hnM
  have hposgap : ∀ a b : ℕ, a ≤ b → b ≤ w.length + 1 →
      fl (a : ℝ) + ((b : ℝ) - a) - 1 / 100 ≤ fl (b : ℝ) :=
    fun a b hab hb => hr.pos_gap hu0 hη hab hb hn hnM
  have init6 : ∀ j : ℕ, net.init fl p w j =
      [sw fl (uq (tokAt w j)) (p.E (tokAt w j) 0), sw fl (bq (tokAt w j)) (p.E (tokAt w j) 1),
       sw fl (fq (tokAt w j)) (p.E (tokAt w j) 2), 1, fl (j : ℝ),
       fl (((w.length + 1 : ℕ) : ℝ))] := by
    intro j
    rw [init_eq hr p w hw j]
    first | rfl | simp [pos]
  -- stored weights
  have hSb := swb hr hu0 hu1 (-20) (-20) 20 (by norm_num)
    (by rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 20)]) (hp.A 0 0 3 4)
    (by linarith [R0 40 (by norm_num)])
  obtain ⟨hS1, hS2⟩ := abs_le.mp hSb
  have hSlo : -(2011 / 100) ≤ sw fl (-20) (p.A 0 0 3 4) := by linarith
  have hShi : sw fl (-20) (p.A 0 0 3 4) ≤ -(1989 / 100) := by linarith
  have hS120b := swb hr hu0 hu1 (-120) (-120) 120 (by norm_num)
    (by rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 120)]) (hp.A 0 0 4 0)
    (by linarith [R0 240 (by norm_num)])
  obtain ⟨hT1, hT2⟩ := abs_le.mp hS120b
  have hS120lo : -(12061 / 100) ≤ sw fl (-120) (p.A 0 0 4 0) := by linarith
  have hS120hi : sw fl (-120) (p.A 0 0 4 0) ≤ -(11939 / 100) := by linarith
  have hS60b := swb hr hu0 hu1 (-60) (-60) 60 (by norm_num)
    (by rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 60)]) (hp.A 0 0 4 1)
    (by linarith [R0 120 (by norm_num)])
  obtain ⟨hT3, hT4⟩ := abs_le.mp hS60b
  have hS60lo : -(6031 / 100) ≤ sw fl (-60) (p.A 0 0 4 1) := by linarith
  have hS60hi : sw fl (-60) (p.A 0 0 4 1) ≤ -(5969 / 100) := by linarith
  have hUb := swb hr hu0 hu1 1 1 1 (by norm_num) (by rw [abs_one]) (hp.E 2 0)
    (by linarith [R0 2 (by norm_num)])
  obtain ⟨hU1, hU2⟩ := abs_le.mp hUb
  have hUlo : 9949 / 10000 ≤ sw fl 1 (p.E 2 0) := by linarith
  have hUhi : sw fl 1 (p.E 2 0) ≤ 10051 / 10000 := by linarith
  have hBb := swb hr hu0 hu1 1 1 1 (by norm_num) (by rw [abs_one]) (hp.E 0 1)
    (by linarith [R0 2 (by norm_num)])
  obtain ⟨hB1', hB2'⟩ := abs_le.mp hBb
  have hBlo : 9949 / 10000 ≤ sw fl 1 (p.E 0 1) := by linarith
  have hBhi : sw fl 1 (p.E 0 1) ≤ 10051 / 10000 := by linarith
  have hV1b := swb hr hu0 hu1 1 1 1 (by norm_num) (by rw [abs_one]) (hp.V 0 0 2 2)
    (by linarith [R0 2 (by norm_num)])
  have hV1c : |sw fl 1 (p.V 0 0 2 2) - 1| ≤ 1 / 190 := by
    have := abs_le.mp hV1b
    rw [abs_le]; constructor <;> linarith
  have hWpb := swb hr hu0 hu1 1 1 1 (by norm_num) (by rw [abs_one]) (hp.W1 0 0 2)
    (by linarith [R0 2 (by norm_num)])
  have hWpc : |sw fl 1 (p.W1 0 0 2) - 1| ≤ 1 / 190 := by
    have := abs_le.mp hWpb
    rw [abs_le]; constructor <;> linarith
  have hB1b := swb hr hu0 hu1 (-1) (-1) 1 (by norm_num) (by rw [abs_neg, abs_one])
    (hp.b1 0 0) (by linarith [R0 2 (by norm_num)])
  have hB1c : |sw fl (-1) (p.b1 0 0) - (-1)| ≤ 1 / 190 := by
    have := abs_le.mp hB1b
    rw [abs_le]; constructor <;> linarith
  have hW2b := swb hr hu0 hu1 (-2) (-2) 2 (by norm_num)
    (by rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]) (hp.W2 0 2 0)
    (by linarith [R0 4 (by norm_num)])
  have hW2c : |sw fl (-2) (p.W2 0 2 0) - (-2)| ≤ 1 / 90 := by
    have := abs_le.mp hW2b
    rw [abs_le]; constructor <;> linarith
  have hWob := swb hr hu0 hu1 1 1 1 (by norm_num) (by rw [abs_one]) (hp.oW 2)
    (by linarith [R0 2 (by norm_num)])
  have hWoc : |sw fl 1 (p.oW 2) - 1| ≤ 1 / 190 := by
    have := abs_le.mp hWob
    rw [abs_le]; constructor <;> linarith
  -- embedding value of the f-column
  have hfk : ∀ t : ℕ, |sw fl (fq t) (p.E t 2) - (if t = 5 then (1 : ℝ) else 0)| ≤ 1 / 190 ∧
      (t ≠ 5 → sw fl (fq t) (p.E t 2) = 0) := by
    intro t
    by_cases h5 : t = 5
    · have hq : fq t = 1 := by unfold fq; rw [if_pos h5]
      have hb := swb hr hu0 hu1 (fq t) 1 1 (by rw [hq]; norm_num) (by rw [abs_one])
        (hp.E t 2) (by linarith [R0 2 (by norm_num)])
      refine ⟨?_, fun h => absurd h5 h⟩
      rw [if_pos h5]
      have := abs_le.mp hb
      rw [abs_le]; constructor <;> linarith
    · have hq : fq t = 0 := by unfold fq; rw [if_neg h5]
      have h0 : sw fl (fq t) (p.E t 2) = 0 := by rw [hq]; exact sw_zero hr _
      refine ⟨?_, fun _ => h0⟩
      rw [if_neg h5, h0]
      norm_num
  -- the key-side score row
  have hRm : ∀ k : ℕ, tokAt w k ≠ 0 → tokAt w k ≠ 2 → Rk fl p w k = 0 := by
    intro k h0 h2
    unfold Rk
    rw [init6 k]
    apply R4_zero hr
    · unfold uq; rw [if_neg h2]; exact sw_zero hr _
    · unfold bq; rw [if_neg h0]; exact sw_zero hr _
  have hP2lo : -(12123 / 100) ≤ sw fl (-120) (p.A 0 0 4 0) * sw fl 1 (p.E 2 0) ∧
      sw fl (-120) (p.A 0 0 4 0) * sw fl 1 (p.E 2 0) ≤ -(11877 / 100) := by
    have a1 := mul_le_mul_of_nonneg_right hS120hi (show (0 : ℝ) ≤ sw fl 1 (p.E 2 0) by linarith)
    have a2 := mul_le_mul_of_nonneg_right hS120lo (show (0 : ℝ) ≤ sw fl 1 (p.E 2 0) by linarith)
    constructor <;> linarith
  have hI2 := big_fl hr hu0 hu1 hη hM200
    (x := sw fl (-120) (p.A 0 0 4 0) * sw fl 1 (p.E 2 0)) (abs_le.mpr ⟨by linarith [hP2lo.1], by linarith [hP2lo.2]⟩)
  have hR2 : ∀ k : ℕ, tokAt w k = 2 → -122 ≤ Rk fl p w k ∧ Rk fl p w k ≤ -118 := by
    intro k h2
    have hRe : Rk fl p w k = fl (sw fl (-120) (p.A 0 0 4 0) * sw fl 1 (p.E 2 0)) := by
      unfold Rk
      rw [init6 k, h2]
      have hu2 : uq 2 = 1 := by simp [uq]
      have hb2 : bq 2 = 0 := by simp [bq]
      rw [hu2, hb2, sw_zero hr]
      exact R4_tok2 hr _ _ _ _ _ _ hI2.1
    rw [hRe]
    have := abs_le.mp hI2.2
    constructor <;> linarith [hP2lo.1, hP2lo.2]
  have hP0lo : -(6062 / 100) ≤ sw fl (-60) (p.A 0 0 4 1) * sw fl 1 (p.E 0 1) ∧
      sw fl (-60) (p.A 0 0 4 1) * sw fl 1 (p.E 0 1) ≤ -(5938 / 100) := by
    have a1 := mul_le_mul_of_nonneg_right hS60hi (show (0 : ℝ) ≤ sw fl 1 (p.E 0 1) by linarith)
    have a2 := mul_le_mul_of_nonneg_right hS60lo (show (0 : ℝ) ≤ sw fl 1 (p.E 0 1) by linarith)
    constructor <;> linarith
  have hI0 := big_fl hr hu0 hu1 hη hM200
    (x := sw fl (-60) (p.A 0 0 4 1) * sw fl 1 (p.E 0 1)) (abs_le.mpr ⟨by linarith [hP0lo.1], by linarith [hP0lo.2]⟩)
  have hR0 : ∀ k : ℕ, tokAt w k = 0 → -61 ≤ Rk fl p w k ∧ Rk fl p w k ≤ -59 := by
    intro k h0
    have hRe : Rk fl p w k = fl (sw fl (-60) (p.A 0 0 4 1) * sw fl 1 (p.E 0 1)) := by
      unfold Rk
      rw [init6 k, h0]
      have hu0' : uq 0 = 0 := by simp [uq]
      have hb0 : bq 0 = 1 := by simp [bq]
      rw [hu0', hb0, sw_zero hr]
      exact R4_bos hr _ _ _ _ _ _ hI0.1
    rw [hRe]
    have := abs_le.mp hI0.2
    constructor <;> linarith [hP0lo.1, hP0lo.2]
  have hcls : ∀ k : ℕ, tokAt w k = 0 ∨ tokAt w k = 2 ∨ (tokAt w k ≠ 0 ∧ tokAt w k ≠ 2) := by
    intro k; omega
  have hRb : ∀ k : ℕ, -122 ≤ Rk fl p w k ∧ Rk fl p w k ≤ 0 := by
    intro k
    rcases hcls k with h | h | h
    · have := hR0 k h; constructor <;> linarith [this.1, this.2]
    · have := hR2 k h; constructor <;> linarith [this.1, this.2]
    · rw [hRm k h.1 h.2]; constructor <;> norm_num
  -- scores
  have hI_nn : 0 ≤ fl (i : ℝ) ∧ fl (i : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) + 1 / 100 :=
    hposle i (by omega)
  have hi_near := hposnear i (by omega)
  have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
  have hSKb : ∀ k : ℕ, k ≤ w.length →
      |sw fl (-20) (p.A 0 0 3 4) * fl (k : ℝ)| ≤ 21 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    obtain ⟨h0, h1⟩ := hposle k (by omega)
    have a1 := mul_le_mul_of_nonneg_right hShi h0
    have a2 := mul_le_mul_of_nonneg_right hSlo h0
    rw [abs_le]; constructor <;> linarith
  have hIRb : ∀ k : ℕ, k ≤ w.length →
      |fl (i : ℝ) * Rk fl p w k| ≤ 124 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    obtain ⟨h0, h1⟩ := hRb k
    have a1 := mul_le_mul_of_nonneg_left h0 hI_nn.1
    have a2 := mul_le_mul_of_nonneg_left h1 hI_nn.1
    rw [abs_le]; constructor <;> linarith [hI_nn.2]
  have hsk : ∀ k : ℕ, k ≤ w.length → hscore hd fl (p.A 0 0) (net.init fl p w) i k =
      fl (fl (sw fl (-20) (p.A 0 0 3 4) * fl (k : ℝ)) + fl (fl (i : ℝ) * Rk fl p w k)) := by
    intro k hk
    have hPb := hSKb k hk
    have hIb := sum_bd hr hu0 hη hnR hn hPb (hIRb k hk) (R1 21 (by norm_num) (by norm_num))
      (R1 124 (by norm_num) (by norm_num))
    exact score_eq hr (p.A 0 0) _ _ _ _ _ _ _ _ _ _ _ _ _ (init6 i) (init6 k)
      (hr.idem _ (le_trans hPb (R1 21 (by norm_num) (by norm_num))))
      (hr.idem _ (le_trans hIb (R1 150 (by norm_num) (by norm_num))))
  have hdev : ∀ k : ℕ, k ≤ w.length →
      |hscore hd fl (p.A 0 0) (net.init fl p w) i k
        - (sw fl (-20) (p.A 0 0 3 4) * fl (k : ℝ) + fl (i : ℝ) * Rk fl p w k)| ≤ 6 / 5 := by
    intro k hk
    rw [hsk k hk]
    exact score_dev hr hu0 hη hnR hn (R1 150 (by norm_num) (by norm_num)) (hSKb k hk)
      (hIRb k hk)
  -- the winner
  obtain ⟨j, hji, hlt, hcase, hfc⟩ := first_ex w hw i hi
  have hjmem : j ∈ cand Mask.causal (w.length + 1) i := by
    rw [Lane4.Seq.mem_cand_causal]; exact hji
  have hlen : (cand Mask.causal (w.length + 1) i).length ≤ w.length + 1 := by
    simp [cand]; omega
  have hgap : ∀ k ∈ cand Mask.causal (w.length + 1) i, k ≠ j →
      hscore hd fl (p.A 0 0) (net.init fl p w) i k
        ≤ hscore hd fl (p.A 0 0) (net.init fl p w) i j - 16 * (ndist j k : ℝ) := by
    intro k hk hne
    rw [Lane4.Seq.mem_cand_causal] at hk
    rw [ndist_cast]
    have dk := abs_le.mp (hdev k (by omega))
    have dj := abs_le.mp (hdev j (by omega))
    have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hjR : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hknear := hposnear k (by omega)
    have hjnear := hposnear j (by omega)
    obtain ⟨hk0, hk1⟩ := abs_le.mp hknear
    obtain ⟨hj0', hj1'⟩ := abs_le.mp hjnear
    obtain ⟨hI0', hI1'⟩ := abs_le.mp hi_near
    have hik : (k : ℝ) ≤ (i : ℝ) := by exact_mod_cast hk
    have hji' : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hji
    have hKk := hposle k (by omega)
    have hKj := hposle j (by omega)
    rcases hcase with ⟨hj0, hall⟩ | ⟨hj1, hjm⟩
    · -- winner is BOS
      subst hj0
      have hk1' : 1 ≤ k := by omega
      have hRk := hR2 k (hall k hk1' hk)
      have hR00 := hR0 0 (by simp [tokAt])
      have hc0 : fl ((0 : ℕ) : ℝ) = 0 := by simpa using hr.zero
      rw [hc0] at dj
      have hm := mul_le_mul_of_nonneg_left (show Rk fl p w k - Rk fl p w 0 ≤ -57 by
        linarith [hRk.2, hR00.1]) hI_nn.1
      have hSm := mul_le_mul_of_nonneg_right hShi hKk.1
      have hkk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1'
      have hz : |((0 : ℕ) : ℝ) - (k : ℝ)| = (k : ℝ) := by
        rw [abs_of_nonpos (by simp)]; simp
      rw [hz]
      obtain ⟨dk1, dk2⟩ := dk
      obtain ⟨dj1, dj2⟩ := dj
      linarith
    · have hjt : tokAt w j ≠ 0 := by
        have := tok_pos w hw j hj1 (by omega)
        omega
      have hRj := hRm j hjt hjm
      rw [hRj] at dj
      rcases lt_or_gt_of_ne hne with hkj | hkj
      · -- k < j
        have hRk : Rk fl p w k ≤ -59 := by
          by_cases hk0' : k = 0
          · subst hk0'
            exact (hR0 0 (by simp [tokAt])).2
          · have := hR2 k (hlt k (by omega) hkj)
            linarith [this.2]
        have hgp := hposgap k j (by omega) (by omega)
        have hkj' : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hkj
        have hD0 : 0 ≤ fl (j : ℝ) - fl (k : ℝ) := by linarith
        have hSD := mul_le_mul_of_nonneg_right hSlo hD0
        have hm := mul_le_mul_of_nonneg_left hRk hI_nn.1
        rw [abs_of_nonneg (by linarith)]
        obtain ⟨dk1, dk2⟩ := dk
        obtain ⟨dj1, dj2⟩ := dj
        linarith
      · -- j < k
        have hRk := (hRb k).2
        have hgp := hposgap j k (by omega) (by omega)
        have hkj' : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hkj
        have hD0 : 0 ≤ fl (k : ℝ) - fl (j : ℝ) := by linarith
        have hSD := mul_le_mul_of_nonneg_right hShi hD0
        have hm := mul_le_mul_of_nonneg_left hRk hI_nn.1
        rw [abs_of_nonpos (by linarith)]
        obtain ⟨dk1, dk2⟩ := dk
        obtain ⟨dj1, dj2⟩ := dj
        linarith
  -- values
  have hvf : ∀ k : ℕ, |vf fl p w k - (if tokAt w k = 5 then (1 : ℝ) else 0)| ≤ 53 / 5000 := by
    intro k
    have hfk' := hfk (tokAt w k)
    have hfa : |sw fl (fq (tokAt w k)) (p.E (tokAt w k) 2)| ≤ 11 / 10 := by
      by_cases h5 : tokAt w k = 5
      · have h := abs_le.mp hfk'.1
        rw [if_pos h5] at h
        rw [abs_le]; constructor <;> linarith [h.1, h.2]
      · rw [hfk'.2 h5]; norm_num
    have hV1a : |sw fl 1 (p.V 0 0 2 2)| ≤ 11 / 10 := by
      have h := abs_le.mp hV1c
      rw [abs_le]; constructor <;> linarith [h.1, h.2]
    have hVb : |sw fl 1 (p.V 0 0 2 2) * sw fl (fq (tokAt w k)) (p.E (tokAt w k) 2)| ≤ 8 := by
      rw [abs_mul]
      have := mul_le_mul hV1a hfa (abs_nonneg _) (by norm_num)
      linarith
    have hve : vf fl p w k = fl (sw fl 1 (p.V 0 0 2 2) *
        sw fl (fq (tokAt w k)) (p.E (tokAt w k) 2)) := by
      unfold vf
      rw [init6 k]
      exact val_eq hr _ _ _ _ _ _ _ (hr.idem _ (le_trans hVb hM8))
    rw [hve]
    have hfl := flsmall hr hu0 hu1 hη hM8 hVb
    by_cases h5 : tokAt w k = 5
    · rw [if_pos h5]
      have hm := mul_near hV1c (show |sw fl (fq (tokAt w k)) (p.E (tokAt w k) 2) - 1| ≤ 1 / 190 by
        have := hfk'.1; rwa [if_pos h5] at this)
      rw [abs_one, one_mul] at hm
      have h3 := abs_sub_le (fl (sw fl 1 (p.V 0 0 2 2) *
        sw fl (fq (tokAt w k)) (p.E (tokAt w k) 2)))
        (sw fl 1 (p.V 0 0 2 2) * sw fl (fq (tokAt w k)) (p.E (tokAt w k) 2)) 1
      linarith
    · rw [if_neg h5, hfk'.2 h5]
      simp [hr.zero]
  have hvB : ∀ k : ℕ, |vf fl p w k| ≤ 11 / 10 := by
    intro k
    have h := hvf k
    obtain ⟨a1, a2⟩ := abs_le.mp h
    rw [abs_le]
    by_cases h5 : tokAt w k = 5
    · rw [if_pos h5] at a1 a2; constructor <;> linarith
    · rw [if_neg h5] at a1 a2; constructor <;> linarith
  -- soft attention
  have hSbd : ∀ k ∈ cand Mask.causal (w.length + 1) i,
      |hscore hd fl (p.A 0 0) (net.init fl p w) i k| ≤ 150 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    rw [Lane4.Seq.mem_cand_causal] at hk
    have d := abs_le.mp (hdev k (by omega))
    have a := abs_le.mp (hSKb k (by omega))
    have b := abs_le.mp (hIRb k (by omega))
    rw [abs_le]; constructor <;> linarith
  have hfBd : ∀ k ∈ cand Mask.causal (w.length + 1) i, |vf fl p w k| ≤ 11 / 10 :=
    fun k _ => hvB k
  obtain ⟨hA1, hA2⟩ := soft_near (s := hscore hd fl (p.A 0 0) (net.init fl p w) i)
    (f := vf fl p w) hr he hu0 hu1 hη0 hη (Lane4.Seq.cand_nodup _ _ _) hlen hn hnη hjmem hgap
    hSbd (by linarith [R1 300 (by norm_num) (by norm_num)]) hfBd
    (by linarith [R0 9 (by norm_num)])
  have hat := attn_eq (ex := ex) hr p w hw i
  -- the answer bits
  have hAj : |savg fl ex (cand Mask.causal (w.length + 1) i)
      (hscore hd fl (p.A 0 0) (net.init fl p w) i) (vf fl p w)
      - (if tokAt w j = 5 then (1 : ℝ) else 0)| ≤ 1 / 45 := by
    have h1 := hvf j
    have h2 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 10 ^ 4 := by norm_num
    have h3 := abs_sub_le (savg fl ex (cand Mask.causal (w.length + 1) i)
      (hscore hd fl (p.A 0 0) (net.init fl p w) i) (vf fl p w)) (vf fl p w j)
      (if tokAt w j = 5 then (1 : ℝ) else 0)
    linarith
  obtain ⟨hf1, hf2⟩ := hfk (tokAt w i)
  have hai : (if tokAt w i = 5 then (1 : ℝ) else 0) = 0 ∨
      (if tokAt w i = 5 then (1 : ℝ) else 0) = 1 := by
    by_cases h5 : tokAt w i = 5 <;> simp [h5]
  have haj : (if tokAt w j = 5 then (1 : ℝ) else 0) = 0 ∨
      (if tokAt w j = 5 then (1 : ℝ) else 0) = 1 := by
    by_cases h5 : tokAt w j = 5 <;> simp [h5]
  obtain ⟨hq1, hq2, hq3, hfin⟩ := chain hr hu0 hu1 hη hM8
    (sw fl (fq (tokAt w i)) (p.E (tokAt w i) 2))
    (savg fl ex (cand Mask.causal (w.length + 1) i)
      (hscore hd fl (p.A 0 0) (net.init fl p w) i) (vf fl p w))
    (sw fl 1 (p.W1 0 0 2)) (sw fl (-1) (p.b1 0 0)) (sw fl (-2) (p.W2 0 2 0)) (sw fl 1 (p.oW 2))
    (if tokAt w i = 5 then (1 : ℝ) else 0) (if tokAt w j = 5 then (1 : ℝ) else 0)
    hai haj hf1 hAj hWpc hB1c hW2c hWoc
  rw [out_eq hr p w i _ _ _ _ _ _ (init6 i) hat hA2 hq1 hq2 hq3]
  -- the target
  have hgi : w.getD (i - 1) 0 = tokAt w i := by
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    simp [tokAt]
  have hT : ((target w i : ℕ) : ℝ) =
      if (if tokAt w i = 5 then (1 : ℝ) else 0) = (if tokAt w j = 5 then (1 : ℝ) else 0)
        then 0 else 1 := by
    have h1 : target w i = if (tokAt w j = 5 ↔ tokAt w i = 5) then 0 else 1 := by
      unfold target
      rw [hfc, hgi]
      exact tgt_arith _ _
    rw [h1]
    by_cases a1 : tokAt w i = 5 <;> by_cases a2 : tokAt w j = 5 <;> simp [a1, a2]
  rw [hT]
  exact hfin

end Lane4.Case
