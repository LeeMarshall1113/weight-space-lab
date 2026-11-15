set_option linter.unusedVariables false

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

def zr : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def rP : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 100, 0]
def rK1 : List ℚ := [0, 0, 0, 0, 300, 0, 0, 0, 0, 0, 0, 0]
def rK2 : List ℚ := [0, 0, 0, 0, 0, 300, 0, 0, 0, 0, 0, 0]
def rV1 : List ℚ := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def rVa : List ℚ := [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
def rVb : List ℚ := [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]

def st (e a s1 s2 g1 g2 h1 h2 o qi qn : ℝ) : Vec := [e, a, s1, s2, g1, g2, h1, h2, o, 1, qi, qn]

def hP : Head :=
  { A := [zr, zr, zr, zr, zr, zr, zr, zr, zr, rP, zr, zr],
    V := [zr, rV1, zr, zr, zr, zr, zr, zr, zr, zr, zr, zr],
    mask := Mask.strict }

def h3a : Head :=
  { A := [zr, zr, zr, zr, zr, zr, zr, zr, zr, rP, zr, rK1],
    V := [zr, zr, zr, zr, zr, zr, rVa, zr, zr, zr, zr, zr],
    mask := Mask.causal }

def h3b : Head :=
  { A := [zr, zr, zr, zr, zr, zr, zr, zr, zr, rP, zr, rK2],
    V := [zr, zr, zr, zr, zr, zr, zr, rVb, zr, zr, zr, zr],
    mask := Mask.causal }

def blk1 : Block :=
  { heads := [hP],
    W1 := [[0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
           [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
           [0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    b1 := [3, -3, 1],
    W2 := [[0, 0, 0], [0, 0, 0], [0, 5, 5], [5, 0, 0], [0, 0, 0], [0, 0, 0],
           [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]],
    b2 := zr }

def blk2 : Block :=
  { heads := [],
    W1 := [[0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
           [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0]],
    b1 := [1, 1],
    W2 := [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 1],
           [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
    b2 := zr }

def blk3 : Block :=
  { heads := [h3a, h3b],
    W1 := [[-2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
           [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]],
    b1 := [0, -6],
    W2 := [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0],
           [0, 0], [0, 0], [1, 1], [0, 0], [0, 0], [0, 0]],
    b2 := zr }

def net : TNet :=
  { embed := [[0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0],
              [2, 0, 0, 0, 0, 0, 0, 0, 0]],
    blocks := [blk1, blk2, blk3],
    outW := [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    outB := 0 }

/-! ### environment and rounding helpers -/

structure Env (u η M : ℝ) (fl ex : ℝ → ℝ) (n : ℕ) : Prop where
  hr : Rnd u η M fl
  he : ExpM u η ex
  hu0 : 0 ≤ u
  hu1 : u ≤ 1 / 2 ^ 24
  hη0 : 0 ≤ η
  hη : η ≤ 1 / 2 ^ 149
  hn : u * (n : ℝ) ≤ 1 / 256
  hnη : η * (n : ℝ) ≤ 1 / 2 ^ 100
  hM : 2 ^ 40 * (n : ℝ) ^ 2 ≤ M
  hn1 : 1 ≤ n

section helpers
variable {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ}

theorem Env.M40 (E : Env u η M fl ex n) : (2 : ℝ) ^ 40 ≤ M :=
  range_const E.hM E.hn1 (le_refl _)

theorem Env.M1e4 (E : Env u η M fl ex n) : (10000 : ℝ) ≤ M :=
  le_trans (by norm_num) E.M40

theorem Env.idem (E : Env u η M fl ex n) {x : ℝ} (hx : |x| ≤ 1000000000) : fl (fl x) = fl x :=
  E.hr.idem x (le_trans hx (le_trans (by norm_num) E.M40))

theorem Env.small (E : Env u η M fl ex n) {x : ℝ} (hx : |x| ≤ 10000) :
    |fl x - x| ≤ 1 / 1000 := by
  have h := E.hr.abs E.hu0 hx E.M1e4
  have h1 : u * 10000 ≤ 1 / 2 ^ 24 * 10000 := mul_le_mul_of_nonneg_right E.hu1 (by norm_num)
  have h2 := eta_tiny E.hη
  have h3 : (1 : ℝ) / 2 ^ 24 * 10000 + 1 / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

theorem Env.flabs (E : Env u η M fl ex n) {x b : ℝ} (hx : |x| ≤ b) (hb : b ≤ 10000) :
    |fl x| ≤ b + 1 / 1000 := by
  have h1 := E.small (le_trans hx hb)
  have h2 := abs_sub_abs_le_abs_sub (fl x) x
  linarith

theorem Env.flnear (E : Env u η M fl ex n) {x t e b : ℝ} (hx : |x - t| ≤ e) (hb : |x| ≤ b)
    (hb' : b ≤ 10000) : |fl x - t| ≤ e + 1 / 1000 := by
  have h1 := E.small (le_trans hb hb')
  have h2 := abs_add_le (fl x - x) (x - t)
  have h3 : fl x - x + (x - t) = fl x - t := by ring
  rw [h3] at h2
  linarith

theorem Env.swb (E : Env u η M fl ex n) (q : ℚ) (c : ℝ) (hqc : (q : ℝ) = c) {d : ℝ}
    (hd : |d| ≤ 1 / 200) (hc0 : 1 / 2 ≤ |c|) (hc1 : |c| ≤ 400) :
    |sw fl q d - c| ≤ |c| / 150 := by
  have hM : 2 * |(q : ℝ)| ≤ M := by
    rw [hqc]
    have := E.M1e4
    linarith
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by
    have h1 := E.hu1
    have h2 := E.hu0
    linarith
  have h := sw_near E.hr E.hu0 q hd (by norm_num) hM hε
  rw [hqc] at h
  have h2 := eta_tiny E.hη
  have h3 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  linarith

theorem Env.swp (E : Env u η M fl ex n) (q : ℚ) (c : ℝ) (hqc : (q : ℝ) = c) {d : ℝ}
    (hd : |d| ≤ 1 / 200) (hc0 : 1 / 2 ≤ c) (hc1 : c ≤ 400) :
    c - c / 150 ≤ sw fl q d ∧ sw fl q d ≤ c + c / 150 := by
  have h := E.swb q c hqc hd (by rw [abs_of_nonneg (by linarith)]; exact hc0)
    (by rw [abs_of_nonneg (by linarith)]; exact hc1)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ c)] at h
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

theorem Env.swn (E : Env u η M fl ex n) (q : ℚ) (c : ℝ) (hqc : (q : ℝ) = c) {d : ℝ}
    (hd : |d| ≤ 1 / 200) (hc0 : c ≤ -1 / 2) (hc1 : -400 ≤ c) :
    c + c / 150 ≤ sw fl q d ∧ sw fl q d ≤ c - c / 150 := by
  have h := E.swb q c hqc hd (by rw [abs_of_nonpos (by linarith)]; linarith)
    (by rw [abs_of_nonpos (by linarith)]; linarith)
  rw [abs_of_nonpos (by linarith : c ≤ 0)] at h
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

theorem amul {a b α β : ℝ} (ha : |a| ≤ α) (hb : |b| ≤ β) : |a * b| ≤ α * β := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) (le_trans (abs_nonneg _) ha)

/-- A stored nonzero weight of size at most 400 is at most 404. -/
theorem Env.swle (E : Env u η M fl ex n) (q : ℚ) {d : ℝ}
    (hd : |d| ≤ 1 / 200) (hc0 : 1 / 2 ≤ |(q : ℝ)|) (hc1 : |(q : ℝ)| ≤ 400) :
    |sw fl q d| ≤ 404 := by
  have h := E.swb q (q : ℝ) rfl hd hc0 hc1
  have h2 := abs_sub_abs_le_abs_sub (sw fl q d) (q : ℝ)
  linarith

theorem Env.idem_swx (E : Env u η M fl ex n) (q : ℚ) {d x : ℝ}
    (hd : |d| ≤ 1 / 200) (hc0 : 1 / 2 ≤ |(q : ℝ)|) (hc1 : |(q : ℝ)| ≤ 400)
    (hx : |x| ≤ 100000) : fl (fl (sw fl q d * x)) = fl (sw fl q d * x) := by
  have h := amul (E.swle q hd hc0 hc1) hx
  exact E.idem (le_trans h (by norm_num))

theorem rdot_zeros {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) :
    ∀ (r : List ℚ), (∀ a ∈ r, a = 0) → ∀ (x : Vec) (d : ℕ → ℝ) (j : ℕ),
      rdot fl r x d j 0 = 0
  | [], _, x, d, j => by simp [rdot]
  | a :: r, h, [], d, j => by simp [rdot]
  | a :: r, h, v :: x, d, j => by
    have ha : a = 0 := h a (by simp)
    subst ha
    simp only [rdot, sw_zero hr, zero_mul, hr.zero, add_zero]
    exact rdot_zeros hr r (fun b hb => h b (List.mem_cons_of_mem _ hb)) x d (j + 1)

theorem zr_zero : ∀ a ∈ zr, a = 0 := by
  intro a ha
  simpa [zr] using ha

end helpers

end Lane4.Case

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

noncomputable def ev (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl ((tokAt w j : ℕ) : ℚ) (p.E (tokAt w j) 0)

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (j : ℕ) : tokAt w j ≤ 2 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (j : ℕ) :
    net.init fl p w j = st (ev fl p w j) 0 0 0 0 0 0 0 0 (fl (j : ℝ)) (fl ((w.length + 1 : ℕ) : ℝ)) := by
  have h3 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 := by
    have := tok_le w hw j
    omega
  rcases h3 with h | h | h <;> simp [TNet.init, net, ev, swRow, h, sw_zero hr, st, pos]

theorem scoreP_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (e a s1 s2 g1 g2 h1 h2 o qi qn e' a' s1' s2' g1' g2' h1' h2' o' qk qn' : ℝ)
    (hI : fl (fl (sw fl 100 (dA 9 10) * qk)) = fl (sw fl 100 (dA 9 10) * qk)) :
    hP.score fl dA (st e a s1 s2 g1 g2 h1 h2 o qi qn)
      (st e' a' s1' s2' g1' g2' h1' h2' o' qk qn') = fl (sw fl 100 (dA 9 10) * qk) := by
  simp [Head.score, hP, zr, rP, st, pdot, rmat, rdot, sw_zero hr, hr.zero, hI]

theorem score3a_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (e a s1 s2 g1 g2 h1 h2 o qi qn e' a' s1' s2' g1' g2' h1' h2' o' qk qn' : ℝ)
    (hI : fl (fl (sw fl 100 (dA 9 10) * qk)) = fl (sw fl 100 (dA 9 10) * qk))
    (hJ : fl (fl (sw fl 300 (dA 11 4) * g1')) = fl (sw fl 300 (dA 11 4) * g1')) :
    h3a.score fl dA (st e a s1 s2 g1 g2 h1 h2 o qi qn)
      (st e' a' s1' s2' g1' g2' h1' h2' o' qk qn')
      = fl (fl (sw fl 100 (dA 9 10) * qk) + fl (qn * fl (sw fl 300 (dA 11 4) * g1'))) := by
  simp [Head.score, h3a, zr, rP, rK1, st, pdot, rmat, rdot, sw_zero hr, hr.zero, hI, hJ]

theorem score3b_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (e a s1 s2 g1 g2 h1 h2 o qi qn e' a' s1' s2' g1' g2' h1' h2' o' qk qn' : ℝ)
    (hI : fl (fl (sw fl 100 (dA 9 10) * qk)) = fl (sw fl 100 (dA 9 10) * qk))
    (hJ : fl (fl (sw fl 300 (dA 11 5) * g2')) = fl (sw fl 300 (dA 11 5) * g2')) :
    h3b.score fl dA (st e a s1 s2 g1 g2 h1 h2 o qi qn)
      (st e' a' s1' s2' g1' g2' h1' h2' o' qk qn')
      = fl (fl (sw fl 100 (dA 9 10) * qk) + fl (qn * fl (sw fl 300 (dA 11 5) * g2'))) := by
  simp [Head.score, h3b, zr, rP, rK2, st, pdot, rmat, rdot, sw_zero hr, hr.zero, hI, hJ]

theorem valP_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ)
    (e a s1 s2 g1 g2 h1 h2 o qk qn : ℝ)
    (hI : fl (fl (sw fl 1 (dV 0) * e)) = fl (sw fl 1 (dV 0) * e)) :
    rdot fl rV1 (st e a s1 s2 g1 g2 h1 h2 o qk qn) dV 0 0 = fl (sw fl 1 (dV 0) * e) := by
  simp [rV1, st, rdot, sw_zero hr, hr.zero, hI]

theorem val3a_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ)
    (e a s1 s2 g1 g2 h1 h2 o qk qn : ℝ)
    (hI : fl (fl (sw fl 1 (dV 0) * e)) = fl (sw fl 1 (dV 0) * e))
    (hJ : fl (fl (fl (sw fl 1 (dV 0) * e) + fl (sw fl 1 (dV 4) * g1)))
      = fl (fl (sw fl 1 (dV 0) * e) + fl (sw fl 1 (dV 4) * g1))) :
    rdot fl rVa (st e a s1 s2 g1 g2 h1 h2 o qk qn) dV 0 0
      = fl (fl (sw fl 1 (dV 0) * e) + fl (sw fl 1 (dV 4) * g1)) := by
  simp [rVa, st, rdot, sw_zero hr, hr.zero, hI, hJ]

theorem val3b_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ)
    (e a s1 s2 g1 g2 h1 h2 o qk qn : ℝ)
    (hI : fl (fl (sw fl 1 (dV 0) * e)) = fl (sw fl 1 (dV 0) * e))
    (hJ : fl (fl (fl (sw fl 1 (dV 0) * e) + fl (sw fl 1 (dV 5) * g2)))
      = fl (fl (sw fl 1 (dV 0) * e) + fl (sw fl 1 (dV 5) * g2))) :
    rdot fl rVb (st e a s1 s2 g1 g2 h1 h2 o qk qn) dV 0 0
      = fl (fl (sw fl 1 (dV 0) * e) + fl (sw fl 1 (dV 5) * g2)) := by
  simp [rVb, st, rdot, sw_zero hr, hr.zero, hI, hJ]

theorem attnP_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (dA dV : ℕ → ℕ → ℝ) (n : ℕ)
    (x : ℕ → Vec) (i : ℕ) :
    sattn hP fl ex dA dV n x i
      = [0, savg fl ex (cand Mask.strict n i) (hscore hP fl dA x i)
            (fun j => rdot fl rV1 (x j) (dV 1) 0 0), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  have hz : ∀ d : ℕ → ℝ, savg fl ex (cand Mask.strict n i) (hscore hP fl dA x i)
      (fun j => rdot fl zr (x j) d 0 0) = 0 := by
    intro d
    exact soft_zeros hr (fun k _ => rdot_zeros hr zr zr_zero (x k) d 0)
  have hV : hP.V = [zr, rV1, zr, zr, zr, zr, zr, zr, zr, zr, zr, zr] := rfl
  have hm : hP.mask = Mask.strict := rfl
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz]

theorem attn3a_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (dA dV : ℕ → ℕ → ℝ) (n : ℕ)
    (x : ℕ → Vec) (i : ℕ) :
    sattn h3a fl ex dA dV n x i
      = [0, 0, 0, 0, 0, 0, savg fl ex (cand Mask.causal n i) (hscore h3a fl dA x i)
            (fun j => rdot fl rVa (x j) (dV 6) 0 0), 0, 0, 0, 0, 0] := by
  have hz : ∀ d : ℕ → ℝ, savg fl ex (cand Mask.causal n i) (hscore h3a fl dA x i)
      (fun j => rdot fl zr (x j) d 0 0) = 0 := by
    intro d
    exact soft_zeros hr (fun k _ => rdot_zeros hr zr zr_zero (x k) d 0)
  have hV : h3a.V = [zr, zr, zr, zr, zr, zr, rVa, zr, zr, zr, zr, zr] := rfl
  have hm : h3a.mask = Mask.causal := rfl
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz]

theorem attn3b_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (dA dV : ℕ → ℕ → ℝ) (n : ℕ)
    (x : ℕ → Vec) (i : ℕ) :
    sattn h3b fl ex dA dV n x i
      = [0, 0, 0, 0, 0, 0, 0, savg fl ex (cand Mask.causal n i) (hscore h3b fl dA x i)
            (fun j => rdot fl rVb (x j) (dV 7) 0 0), 0, 0, 0, 0] := by
  have hz : ∀ d : ℕ → ℝ, savg fl ex (cand Mask.causal n i) (hscore h3b fl dA x i)
      (fun j => rdot fl zr (x j) d 0 0) = 0 := by
    intro d
    exact soft_zeros hr (fun k _ => rdot_zeros hr zr zr_zero (x k) d 0)
  have hV : h3b.V = [zr, zr, zr, zr, zr, zr, zr, rVb, zr, zr, zr, zr] := rfl
  have hm : h3b.mask = Mask.causal := rfl
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz]

end Lane4.Case

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

theorem relu_abs (x : ℝ) : |relu x| ≤ |x| := by
  unfold relu
  rcases le_total x 0 with h | h
  · rw [max_eq_right h]; simp
  · rw [max_eq_left h]

theorem relu_nn (x : ℝ) : 0 ≤ relu x := by
  unfold relu
  exact le_max_right _ _

section helpers2
variable {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ}

theorem Env.swab (E : Env u η M fl ex n) (q : ℚ) (c : ℝ) (hqc : (q : ℝ) = c) {d : ℝ}
    (hd : |d| ≤ 1 / 200) (hc0 : 1 / 2 ≤ |c|) (hc1 : |c| ≤ 400) :
    |sw fl q d| ≤ |c| + |c| / 150 := by
  have h := E.swb q c hqc hd hc0 hc1
  have h2 := abs_sub_abs_le_abs_sub (sw fl q d) c
  linarith

theorem Env.unit1_bd (E : Env u η M fl ex n) (q bq : ℚ) (cq cb : ℝ) (hq : (q : ℝ) = cq)
    (hb : (bq : ℝ) = cb) {d db x X : ℝ} (hd : |d| ≤ 1 / 200) (hdb : |db| ≤ 1 / 200)
    (hq0 : 1 / 2 ≤ |cq|) (hq1 : |cq| ≤ 3) (hb0 : 1 / 2 ≤ |cb|) (hb1 : |cb| ≤ 10)
    (hx : |x| ≤ X) (hX : X ≤ 1000) :
    |fl (fl (sw fl q d * x) + sw fl bq db)| ≤ 31 / 10 * X + 11 := by
  have h1 := E.swab q cq hq hd hq0 (by linarith)
  have h1' : |sw fl q d| ≤ 31 / 10 := by linarith
  have h2 := amul h1' hx
  have h3 := E.flabs h2 (by linarith)
  have h4 := E.swab bq cb hb hdb hb0 (by linarith)
  have h4' : |sw fl bq db| ≤ 101 / 10 := by linarith
  have h5 : |fl (sw fl q d * x) + sw fl bq db| ≤ 31 / 10 * X + 1 / 1000 + 101 / 10 :=
    le_trans (abs_add_le _ _) (by linarith)
  have h6 := E.flabs h5 (by linarith)
  linarith

theorem Env.pair_bd (E : Env u η M fl ex n) (q1 q2 : ℚ) (c1 c2 : ℝ) (hq1 : (q1 : ℝ) = c1)
    (hq2 : (q2 : ℝ) = c2) {d1 d2 x1 x2 X1 X2 : ℝ} (hd1 : |d1| ≤ 1 / 200) (hd2 : |d2| ≤ 1 / 200)
    (h10 : 1 / 2 ≤ |c1|) (h11 : |c1| ≤ 10) (h20 : 1 / 2 ≤ |c2|) (h21 : |c2| ≤ 10)
    (hx1 : |x1| ≤ X1) (hx2 : |x2| ≤ X2) (hX1 : X1 ≤ 450) (hX2 : X2 ≤ 450) :
    |fl (fl (sw fl q1 d1 * x1) + fl (sw fl q2 d2 * x2))| ≤ 101 / 10 * (X1 + X2) + 1
      ∧ fl (fl (fl (sw fl q1 d1 * x1) + fl (sw fl q2 d2 * x2)))
        = fl (fl (sw fl q1 d1 * x1) + fl (sw fl q2 d2 * x2)) := by
  have a1 := E.swab q1 c1 hq1 hd1 h10 (by linarith)
  have a1' : |sw fl q1 d1| ≤ 101 / 10 := by linarith
  have a2 := E.swab q2 c2 hq2 hd2 h20 (by linarith)
  have a2' : |sw fl q2 d2| ≤ 101 / 10 := by linarith
  have b1 := amul a1' hx1
  have b2 := amul a2' hx2
  have f1 := E.flabs b1 (by linarith)
  have f2 := E.flabs b2 (by linarith)
  have s : |fl (sw fl q1 d1 * x1) + fl (sw fl q2 d2 * x2)|
      ≤ 101 / 10 * X1 + 1 / 1000 + (101 / 10 * X2 + 1 / 1000) :=
    le_trans (abs_add_le _ _) (by linarith)
  have f3 := E.flabs s (by linarith)
  constructor
  · linarith
  · exact E.idem (le_trans s (by linarith))

end helpers2

theorem blk1_eq {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {p : Pert}
    (hp : p.Within (1 / 200)) (x : ℕ → Vec) (i : ℕ) (e qi qn A : ℝ)
    (hx : x i = st e 0 0 0 0 0 0 0 0 qi qn)
    (hat : sattn hP fl ex (p.A 0 0) (p.V 0 0) n x i = [0, A, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    (he : fl e = e) (hqi : fl qi = qi) (hqn : fl qn = qn) (hA : fl A = A) (hAb : |A| ≤ 3) :
    sblock blk1 fl ex p 0 n x i
      = st e A
        (fl (fl (sw fl 5 (p.W2 0 2 1) *
              relu (fl (fl (sw fl 2 (p.W1 0 1 1) * A) + sw fl (-3) (p.b1 0 1))))
          + fl (sw fl 5 (p.W2 0 2 2) *
              relu (fl (fl (sw fl (-2) (p.W1 0 2 1) * A) + sw fl 1 (p.b1 0 2))))))
        (fl (sw fl 5 (p.W2 0 3 0) *
              relu (fl (fl (sw fl (-2) (p.W1 0 0 1) * A) + sw fl 3 (p.b1 0 0)))))
        0 0 0 0 0 qi qn := by
  have hr := E.hr
  have hP0 := E.unit1_bd (-2) 3 (-2) 3 (by norm_num) (by norm_num) (hp.W1 0 0 1) (hp.b1 0 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hAb (by norm_num : (3 : ℝ) ≤ 1000)
  have hP1 := E.unit1_bd 2 (-3) 2 (-3) (by norm_num) (by norm_num) (hp.W1 0 1 1) (hp.b1 0 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hAb (by norm_num : (3 : ℝ) ≤ 1000)
  have hP2 := E.unit1_bd (-2) 1 (-2) 1 (by norm_num) (by norm_num) (hp.W1 0 2 1) (hp.b1 0 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hAb (by norm_num : (3 : ℝ) ≤ 1000)
  have r0 := relu_abs (fl (fl (sw fl (-2) (p.W1 0 0 1) * A) + sw fl 3 (p.b1 0 0)))
  have r1 := relu_abs (fl (fl (sw fl 2 (p.W1 0 1 1) * A) + sw fl (-3) (p.b1 0 1)))
  have r2 := relu_abs (fl (fl (sw fl (-2) (p.W1 0 2 1) * A) + sw fl 1 (p.b1 0 2)))
  have h0 := E.idem_swx (-2) (d := p.W1 0 0 1) (x := A) (hp.W1 0 0 1) (by norm_num) (by norm_num)
    (by linarith)
  have h1 := E.idem_swx 2 (d := p.W1 0 1 1) (x := A) (hp.W1 0 1 1) (by norm_num) (by norm_num)
    (by linarith)
  have h2 := E.idem_swx (-2) (d := p.W1 0 2 1) (x := A) (hp.W1 0 2 1) (by norm_num) (by norm_num)
    (by linarith)
  have hS2 := E.idem_swx 5 (d := p.W2 0 3 0) (hp.W2 0 3 0) (by norm_num) (by norm_num)
    (by linarith : |relu (fl (fl (sw fl (-2) (p.W1 0 0 1) * A) + sw fl 3 (p.b1 0 0)))| ≤ 100000)
  have hS1a := E.idem_swx 5 (d := p.W2 0 2 1) (hp.W2 0 2 1) (by norm_num) (by norm_num)
    (by linarith : |relu (fl (fl (sw fl 2 (p.W1 0 1 1) * A) + sw fl (-3) (p.b1 0 1)))| ≤ 100000)
  have hS1 := (E.pair_bd 5 5 5 5 (by norm_num) (by norm_num) (hp.W2 0 2 1) (hp.W2 0 2 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith : |relu (fl (fl (sw fl 2 (p.W1 0 1 1) * A) + sw fl (-3) (p.b1 0 1)))| ≤ 22)
    (by linarith : |relu (fl (fl (sw fl (-2) (p.W1 0 2 1) * A) + sw fl 1 (p.b1 0 2)))| ≤ 22)
    (by norm_num) (by norm_num)).2
  simp only [sblock, blk1, sheadsApply, hat, hx]
  simp [st, zr, radd, raffine, rdot, sw_zero hr, hr.zero, hr.one, he, hqi, hqn, hA, h0, h1, h2,
    hS2, hS1a, hS1]

end Lane4.Case

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

theorem blk2_eq {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {p : Pert}
    (hp : p.Within (1 / 200)) (x : ℕ → Vec) (i : ℕ) (e A s1 s2 qi qn : ℝ)
    (hx : x i = st e A s1 s2 0 0 0 0 0 qi qn)
    (he : fl e = e) (hA : fl A = A) (hs1 : fl s1 = s1) (hs2 : fl s2 = s2) (hqi : fl qi = qi)
    (hqn : fl qn = qn) (hs1b : |s1| ≤ 500) (hs2b : |s2| ≤ 500) :
    sblock blk2 fl ex p 1 n x i
      = st e A s1 s2
        (fl (sw fl 1 (p.W2 1 4 0) *
          relu (fl (fl (sw fl (-1) (p.W1 1 0 2) * s1) + sw fl 1 (p.b1 1 0)))))
        (fl (sw fl 1 (p.W2 1 5 1) *
          relu (fl (fl (sw fl (-1) (p.W1 1 1 3) * s2) + sw fl 1 (p.b1 1 1)))))
        0 0 0 qi qn := by
  have hr := E.hr
  have hV1 := E.unit1_bd (-1) 1 (-1) 1 (by norm_num) (by norm_num) (hp.W1 1 0 2) (hp.b1 1 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hs1b (by norm_num : (500 : ℝ) ≤ 1000)
  have hV2 := E.unit1_bd (-1) 1 (-1) 1 (by norm_num) (by norm_num) (hp.W1 1 1 3) (hp.b1 1 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hs2b (by norm_num : (500 : ℝ) ≤ 1000)
  have r1 := relu_abs (fl (fl (sw fl (-1) (p.W1 1 0 2) * s1) + sw fl 1 (p.b1 1 0)))
  have r2 := relu_abs (fl (fl (sw fl (-1) (p.W1 1 1 3) * s2) + sw fl 1 (p.b1 1 1)))
  have h1 := E.idem_swx (-1) (d := p.W1 1 0 2) (x := s1) (hp.W1 1 0 2) (by norm_num)
    (by norm_num) (by linarith)
  have h2 := E.idem_swx (-1) (d := p.W1 1 1 3) (x := s2) (hp.W1 1 1 3) (by norm_num)
    (by norm_num) (by linarith)
  have hG1 := E.idem_swx 1 (d := p.W2 1 4 0) (hp.W2 1 4 0) (by norm_num) (by norm_num)
    (by linarith : |relu (fl (fl (sw fl (-1) (p.W1 1 0 2) * s1) + sw fl 1 (p.b1 1 0)))| ≤ 100000)
  have hG2 := E.idem_swx 1 (d := p.W2 1 5 1) (hp.W2 1 5 1) (by norm_num) (by norm_num)
    (by linarith : |relu (fl (fl (sw fl (-1) (p.W1 1 1 3) * s2) + sw fl 1 (p.b1 1 1)))| ≤ 100000)
  simp only [sblock, blk2, sheadsApply, hx]
  simp [st, zr, radd, raffine, rdot, sw_zero hr, hr.zero, hr.one, he, hA, hs1, hs2, hqi, hqn,
    h1, h2, hG1, hG2]

theorem blk3_eq {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {p : Pert}
    (hp : p.Within (1 / 200)) (x : ℕ → Vec) (i : ℕ) (e A s1 s2 g1 g2 qi qn H1 H2 : ℝ)
    (hx : x i = st e A s1 s2 g1 g2 0 0 0 qi qn)
    (hat1 : sattn h3a fl ex (p.A 2 0) (p.V 2 0) n x i = [0, 0, 0, 0, 0, 0, H1, 0, 0, 0, 0, 0])
    (hat2 : sattn h3b fl ex (p.A 2 1) (p.V 2 1) n x i = [0, 0, 0, 0, 0, 0, 0, H2, 0, 0, 0, 0])
    (he : fl e = e) (hA : fl A = A) (hs1 : fl s1 = s1) (hs2 : fl s2 = s2)
    (hg1 : fl g1 = g1) (hg2 : fl g2 = g2) (hqi : fl qi = qi) (hqn : fl qn = qn)
    (hH1 : fl H1 = H1) (hH2 : fl H2 = H2)
    (heb : |e| ≤ 3) (hH1b : |H1| ≤ 5) (hH2b : |H2| ≤ 5) :
    sblock blk3 fl ex p 2 n x i
      = st e A s1 s2 g1 g2 H1 H2
        (fl (fl (sw fl 1 (p.W2 2 8 0) *
            relu (fl (fl (sw fl (-2) (p.W1 2 0 0) * e) + fl (sw fl 1 (p.W1 2 0 6) * H1))))
          + fl (sw fl 1 (p.W2 2 8 1) *
            relu (fl (fl (fl (sw fl 2 (p.W1 2 1 0) * e) + fl (sw fl 1 (p.W1 2 1 7) * H2))
              + sw fl (-6) (p.b1 2 1))))))
        qi qn := by
  have hr := E.hr
  have hR1 := E.pair_bd (-2) 1 (-2) 1 (by norm_num) (by norm_num) (hp.W1 2 0 0) (hp.W1 2 0 6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) heb hH1b (by norm_num) (by norm_num)
  have hR2 := E.pair_bd 2 1 2 1 (by norm_num) (by norm_num) (hp.W1 2 1 0) (hp.W1 2 1 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) heb hH2b (by norm_num) (by norm_num)
  have hb2 := E.swab (-6) (-6) (by norm_num) (hp.b1 2 1) (by norm_num) (by norm_num)
  have e6 : |(-6 : ℝ)| = 6 := by norm_num
  rw [e6] at hb2
  have hb2' : |sw fl (-6) (p.b1 2 1)| ≤ 7 := by linarith
  have hU2 : |fl (fl (fl (sw fl 2 (p.W1 2 1 0) * e) + fl (sw fl 1 (p.W1 2 1 7) * H2))
      + sw fl (-6) (p.b1 2 1))| ≤ 100 := by
    have h1 : |fl (fl (sw fl 2 (p.W1 2 1 0) * e) + fl (sw fl 1 (p.W1 2 1 7) * H2))
        + sw fl (-6) (p.b1 2 1)| ≤ 90 :=
      le_trans (abs_add_le _ _) (by linarith [hR2.1])
    have := E.flabs h1 (by norm_num)
    linarith
  have hU1 : |fl (fl (sw fl (-2) (p.W1 2 0 0) * e) + fl (sw fl 1 (p.W1 2 0 6) * H1))| ≤ 100 := by
    have := hR1.1
    linarith
  have r1 := relu_abs (fl (fl (sw fl (-2) (p.W1 2 0 0) * e) + fl (sw fl 1 (p.W1 2 0 6) * H1)))
  have r2 := relu_abs (fl (fl (fl (sw fl 2 (p.W1 2 1 0) * e) + fl (sw fl 1 (p.W1 2 1 7) * H2))
      + sw fl (-6) (p.b1 2 1)))
  have hI0 := E.idem_swx (-2) (d := p.W1 2 0 0) (x := e) (hp.W1 2 0 0) (by norm_num)
    (by norm_num) (by linarith)
  have hI1 := E.idem_swx 2 (d := p.W1 2 1 0) (x := e) (hp.W1 2 1 0) (by norm_num)
    (by norm_num) (by linarith)
  have hO1 := E.idem_swx 1 (d := p.W2 2 8 0) (hp.W2 2 8 0) (by norm_num) (by norm_num)
    (by linarith : |relu (fl (fl (sw fl (-2) (p.W1 2 0 0) * e)
      + fl (sw fl 1 (p.W1 2 0 6) * H1)))| ≤ 100000)
  have hO := (E.pair_bd 1 1 1 1 (by norm_num) (by norm_num) (hp.W2 2 8 0) (hp.W2 2 8 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith : |relu (fl (fl (sw fl (-2) (p.W1 2 0 0) * e)
      + fl (sw fl 1 (p.W1 2 0 6) * H1)))| ≤ 100)
    (by linarith : |relu (fl (fl (fl (sw fl 2 (p.W1 2 1 0) * e)
      + fl (sw fl 1 (p.W1 2 1 7) * H2)) + sw fl (-6) (p.b1 2 1)))| ≤ 100)
    (by norm_num) (by norm_num)).2
  have hat2' : sattn h3b fl ex (p.A 2 (0 + 1)) (p.V 2 (0 + 1)) n x i
      = [0, 0, 0, 0, 0, 0, 0, H2, 0, 0, 0, 0] := hat2
  simp only [sblock, blk3, sheadsApply, hat1, hat2, hat2', hx]
  simp [st, zr, radd, raffine, rdot, sw_zero hr, hr.zero, hr.one, he, hA, hs1, hs2, hg1, hg2,
    hqi, hqn, hH1, hH2, hI0, hI1, hR1.2, hR2.2, hO1, hO]

theorem out_eq {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {p : Pert}
    (hp : p.Within (1 / 200)) (w : List ℕ) (i : ℕ) (e A s1 s2 g1 g2 H1 H2 O qi qn : ℝ)
    (hrun : srun net fl ex p w i = st e A s1 s2 g1 g2 H1 H2 O qi qn) (hO : |O| ≤ 1000) :
    sout net fl ex p w i = fl (sw fl 1 (p.oW 8) * O) := by
  have hr := E.hr
  have hI := E.idem_swx 1 (d := p.oW 8) (x := O) (hp.oW 8) (by norm_num) (by norm_num)
    (by linarith)
  have ho : net.outW = [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] := rfl
  have hb : net.outB = 0 := rfl
  unfold sout
  rw [hrun, ho, hb]
  simp [st, rdot, sw_zero hr, hr.zero, hI]

end Lane4.Case

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

section helpers3
variable {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ}

theorem Env.flsw (E : Env u η M fl ex n) (q : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 200)
    (hq : |(q : ℝ)| ≤ 400) : fl (sw fl q d) = sw fl q d :=
  fl_sw E.hr q hd (by norm_num) (by have := E.M1e4; linarith)

theorem Env.fln (E : Env u η M fl ex n) {x : ℝ} (hx : |x| ≤ 1000 * (n : ℝ)) :
    |fl x - x| ≤ 4 := by
  have hB : 1000 * (n : ℝ) ≤ M := range_lin E.hM E.hn1 (by norm_num) (by norm_num)
  have h := E.hr.abs E.hu0 hx hB
  have e : u * (1000 * (n : ℝ)) = 1000 * (u * n) := by ring
  have h2 := eta_tiny E.hη
  have h3 := E.hn
  rw [e] at h
  linarith

theorem Env.unit1_near (E : Env u η M fl ex n) (q bq : ℚ) (cq cb : ℝ) (hq : (q : ℝ) = cq)
    (hb : (bq : ℝ) = cb) {d db A τ : ℝ} (hd : |d| ≤ 1 / 200) (hdb : |db| ≤ 1 / 200)
    (hq0 : 1 / 2 ≤ |cq|) (hq1 : |cq| ≤ 3) (hb0 : 1 / 2 ≤ |cb|) (hb1 : |cb| ≤ 3)
    (hτ : |τ| ≤ 2) (hA : |A - τ| ≤ 7 / 100) :
    |fl (fl (sw fl q d * A) + sw fl bq db) - (cq * τ + cb)| ≤ 1 / 3 := by
  have hs := E.swb q cq hq hd hq0 (by linarith)
  have hs' : |sw fl q d - cq| ≤ 1 / 50 := by linarith
  have m := mul_near hs' hA
  have m' : |sw fl q d * A - cq * τ| ≤ 13 / 50 := by linarith
  have hct : |cq * τ| ≤ 6 := by
    have := amul hq1 hτ
    linarith
  have hsa : |sw fl q d * A| ≤ 7 := by
    have := abs_sub_abs_le_abs_sub (sw fl q d * A) (cq * τ)
    linarith
  have f1 := E.flnear m' hsa (by norm_num)
  have hbb := E.swb bq cb hb hdb hb0 (by linarith)
  have hbb' : |sw fl bq db - cb| ≤ 1 / 50 := by linarith
  have s1 : |fl (sw fl q d * A) + sw fl bq db - (cq * τ + cb)| ≤ 13 / 50 + 1 / 1000 + 1 / 50 := by
    have e : fl (sw fl q d * A) + sw fl bq db - (cq * τ + cb)
        = (fl (sw fl q d * A) - cq * τ) + (sw fl bq db - cb) := by ring
    rw [e]
    have := abs_add_le (fl (sw fl q d * A) - cq * τ) (sw fl bq db - cb)
    linarith
  have hct2 : |cq * τ + cb| ≤ 9 := by
    have := abs_add_le (cq * τ) cb
    linarith
  have hsb : |fl (sw fl q d * A) + sw fl bq db| ≤ 10 := by
    have := abs_sub_abs_le_abs_sub (fl (sw fl q d * A) + sw fl bq db) (cq * τ + cb)
    linarith
  have f2 := E.flnear s1 hsb (by norm_num)
  linarith

theorem Env.five_ge (E : Env u η M fl ex n) (q : ℚ) (hq : (q : ℝ) = 5) {d x : ℝ}
    (hd : |d| ≤ 1 / 200) (hx0 : 2 / 3 ≤ x) (hx1 : x ≤ 22) : 33 / 10 ≤ fl (sw fl q d * x) := by
  have h := E.swp q 5 hq hd (by norm_num) (by norm_num)
  have h1 := mul_le_mul h.1 hx0 (by norm_num) (by linarith [h.1])
  have h2 := mul_le_mul h.2 hx1 (by linarith) (by linarith [h.2])
  have hb : |sw fl q d * x| ≤ 10000 := abs_le.mpr ⟨by linarith, by linarith⟩
  have h3 := abs_le.mp (E.small hb)
  linarith [h3.1]

theorem ev_facts (E : Env u η M fl ex n) {p : Pert} (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (j : ℕ) :
    fl (ev fl p w j) = ev fl p w j ∧ |ev fl p w j - ((tokAt w j : ℕ) : ℝ)| ≤ 1 / 75
      ∧ |ev fl p w j| ≤ 3 := by
  have hr := E.hr
  have h3 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 := by
    have := tok_le w hw j
    omega
  rcases h3 with h | h | h
  · have e : ev fl p w j = 0 := by simp [ev, h, sw_zero hr]
    have ht : ((tokAt w j : ℕ) : ℝ) = 0 := by rw [h]; norm_num
    rw [e, ht, hr.zero]
    norm_num
  · have e : ev fl p w j = sw fl 1 (p.E 1 0) := by simp [ev, h]
    have ht : ((tokAt w j : ℕ) : ℝ) = 1 := by rw [h]; norm_num
    have hb := E.swb 1 1 (by norm_num) (hp.E 1 0) (by norm_num) (by norm_num)
    rw [abs_one] at hb
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    rw [e, ht]
    refine ⟨E.flsw 1 (hp.E 1 0) (by norm_num), abs_le.mpr ⟨by linarith, by linarith⟩,
      abs_le.mpr ⟨by linarith, by linarith⟩⟩
  · have e : ev fl p w j = sw fl 2 (p.E 2 0) := by simp [ev, h]
    have ht : ((tokAt w j : ℕ) : ℝ) = 2 := by rw [h]; norm_num
    have hb := E.swb 2 2 (by norm_num) (hp.E 2 0) (by norm_num) (by norm_num)
    have e2 : |(2 : ℝ)| = 2 := by norm_num
    rw [e2] at hb
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    rw [e, ht]
    refine ⟨E.flsw 2 (hp.E 2 0) (by norm_num), abs_le.mpr ⟨by linarith, by linarith⟩,
      abs_le.mpr ⟨by linarith, by linarith⟩⟩

theorem mlp1_props (E : Env u η M fl ex n) {p : Pert} (hp : p.Within (1 / 200)) (A : ℝ)
    (τ : ℕ) (hτ : τ ≤ 2) (hA : |A - (τ : ℝ)| ≤ 7 / 100) (S1 S2 : ℝ)
    (hS1 : S1 = fl (fl (sw fl 5 (p.W2 0 2 1) *
              relu (fl (fl (sw fl 2 (p.W1 0 1 1) * A) + sw fl (-3) (p.b1 0 1))))
          + fl (sw fl 5 (p.W2 0 2 2) *
              relu (fl (fl (sw fl (-2) (p.W1 0 2 1) * A) + sw fl 1 (p.b1 0 2))))))
    (hS2 : S2 = fl (sw fl 5 (p.W2 0 3 0) *
              relu (fl (fl (sw fl (-2) (p.W1 0 0 1) * A) + sw fl 3 (p.b1 0 0))))) :
    (τ = 1 → S1 = 0) ∧ (τ ≠ 1 → 3 ≤ S1) ∧ (τ = 2 → S2 = 0) ∧ (τ ≠ 2 → 3 ≤ S2)
      ∧ |S1| ≤ 500 ∧ |S2| ≤ 500 ∧ fl S1 = S1 ∧ fl S2 = S2 := by
  have hr := E.hr
  have hτr : |(τ : ℝ)| ≤ 2 := by
    have : (τ : ℝ) ≤ 2 := by exact_mod_cast hτ
    rw [abs_of_nonneg (Nat.cast_nonneg τ)]
    exact this
  have n0 := abs_le.mp (E.unit1_near (-2) 3 (-2) 3 (by norm_num) (by norm_num) (hp.W1 0 0 1)
    (hp.b1 0 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hτr hA)
  have n1 := abs_le.mp (E.unit1_near 2 (-3) 2 (-3) (by norm_num) (by norm_num) (hp.W1 0 1 1)
    (hp.b1 0 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hτr hA)
  have n2 := abs_le.mp (E.unit1_near (-2) 1 (-2) 1 (by norm_num) (by norm_num) (hp.W1 0 2 1)
    (hp.b1 0 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hτr hA)
  generalize hP0 : fl (fl (sw fl (-2) (p.W1 0 0 1) * A) + sw fl 3 (p.b1 0 0)) = P0 at n0 hS2
  generalize hP1 : fl (fl (sw fl 2 (p.W1 0 1 1) * A) + sw fl (-3) (p.b1 0 1)) = P1 at n1 hS1
  generalize hP2 : fl (fl (sw fl (-2) (p.W1 0 2 1) * A) + sw fl 1 (p.b1 0 2)) = P2 at n2 hS1
  have hq5 : ((5 : ℚ) : ℝ) = 5 := by norm_num
  have hsw5 : ∀ (q : ℚ) {d : ℝ}, (q : ℝ) = 5 → |d| ≤ 1 / 200 → |sw fl q d| ≤ 11 / 2 := by
    intro q d hq hd
    have h := E.swab q 5 hq hd (by norm_num) (by norm_num)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 5)] at h
    linarith
  have hrelu : ∀ x : ℝ, |x| ≤ 4 → |relu x| ≤ 22 := fun x hx => by
    have := relu_abs x
    linarith
  have hτ0 : (0 : ℝ) ≤ (τ : ℝ) := Nat.cast_nonneg τ
  have hτ2 : (τ : ℝ) ≤ 2 := by exact_mod_cast hτ
  have hP0b : |P0| ≤ 4 := abs_le.mpr ⟨by linarith [n0.1], by linarith [n0.2]⟩
  have hP1b : |P1| ≤ 4 := abs_le.mpr ⟨by linarith [n1.1], by linarith [n1.2]⟩
  have hP2b : |P2| ≤ 4 := abs_le.mpr ⟨by linarith [n2.1], by linarith [n2.2]⟩
  have bS2 : |S2| ≤ 500 := by
    rw [hS2]
    have h1 := amul (hsw5 5 hq5 (hp.W2 0 3 0)) (hrelu P0 hP0b)
    have h2 := E.flabs h1 (by norm_num)
    linarith
  have bS1 : |S1| ≤ 500 := by
    rw [hS1]
    have h1 := amul (hsw5 5 hq5 (hp.W2 0 2 1)) (hrelu P1 hP1b)
    have h2 := amul (hsw5 5 hq5 (hp.W2 0 2 2)) (hrelu P2 hP2b)
    have f1 := E.flabs h1 (by norm_num)
    have f2 := E.flabs h2 (by norm_num)
    have h3 : |fl (sw fl 5 (p.W2 0 2 1) * relu P1) + fl (sw fl 5 (p.W2 0 2 2) * relu P2)|
        ≤ 300 := le_trans (abs_add_le _ _) (by linarith)
    have := E.flabs h3 (by norm_num)
    linarith
  have fS2 : fl S2 = S2 := by
    rw [hS2]
    exact E.idem (le_trans (amul (hsw5 5 hq5 (hp.W2 0 3 0)) (hrelu P0 hP0b)) (by norm_num))
  have fS1 : fl S1 = S1 := by
    rw [hS1]
    have h1 := amul (hsw5 5 hq5 (hp.W2 0 2 1)) (hrelu P1 hP1b)
    have h2 := amul (hsw5 5 hq5 (hp.W2 0 2 2)) (hrelu P2 hP2b)
    have f1 := E.flabs h1 (by norm_num)
    have f2 := E.flabs h2 (by norm_num)
    have h3 : |fl (sw fl 5 (p.W2 0 2 1) * relu P1) + fl (sw fl 5 (p.W2 0 2 2) * relu P2)|
        ≤ 300 := le_trans (abs_add_le _ _) (by linarith)
    exact E.idem (le_trans h3 (by norm_num))
  have hcases : τ = 0 ∨ τ = 1 ∨ τ = 2 := by omega
  rcases hcases with h | h | h
  · have ht : (τ : ℝ) = 0 := by rw [h]; norm_num
    have r0 : relu P0 = P0 := relu_of_nonneg (by linarith [n0.1])
    have r1 : relu P1 = 0 := relu_of_nonpos (by linarith [n1.2])
    have r2 : relu P2 = P2 := relu_of_nonneg (by linarith [n2.1])
    refine ⟨fun h1 => by exfalso; omega, fun _ => ?_, fun h1 => by exfalso; omega,
      fun _ => ?_, bS1, bS2, fS1, fS2⟩
    · rw [hS1, r1, r2]
      simp only [mul_zero, hr.zero, zero_add]
      rw [E.idem_swx 5 (d := p.W2 0 2 2) (x := P2) (hp.W2 0 2 2) (by norm_num) (by norm_num)
        (by linarith)]
      have := E.five_ge 5 hq5 (hp.W2 0 2 2) (x := P2) (by linarith [n2.1]) (by linarith [n2.2])
      linarith
    · rw [hS2, r0]
      have := E.five_ge 5 hq5 (hp.W2 0 3 0) (x := P0) (by linarith [n0.1]) (by linarith [n0.2])
      linarith
  · have ht : (τ : ℝ) = 1 := by rw [h]; norm_num
    have r0 : relu P0 = P0 := relu_of_nonneg (by linarith [n0.1])
    have r1 : relu P1 = 0 := relu_of_nonpos (by linarith [n1.2])
    have r2 : relu P2 = 0 := relu_of_nonpos (by linarith [n2.2])
    refine ⟨fun _ => ?_, fun h1 => by exfalso; omega, fun h1 => by exfalso; omega,
      fun _ => ?_, bS1, bS2, fS1, fS2⟩
    · rw [hS1, r1, r2]
      simp only [mul_zero, hr.zero, add_zero]
    · rw [hS2, r0]
      have := E.five_ge 5 hq5 (hp.W2 0 3 0) (x := P0) (by linarith [n0.1]) (by linarith [n0.2])
      linarith
  · have ht : (τ : ℝ) = 2 := by rw [h]; norm_num
    have r0 : relu P0 = 0 := relu_of_nonpos (by linarith [n0.2])
    have r1 : relu P1 = P1 := relu_of_nonneg (by linarith [n1.1])
    have r2 : relu P2 = 0 := relu_of_nonpos (by linarith [n2.2])
    refine ⟨fun h1 => by exfalso; omega, fun _ => ?_, fun _ => ?_,
      fun h1 => by exfalso; omega, bS1, bS2, fS1, fS2⟩
    · rw [hS1, r1, r2]
      simp only [mul_zero, hr.zero, add_zero]
      rw [E.idem_swx 5 (d := p.W2 0 2 1) (x := P1) (hp.W2 0 2 1) (by norm_num) (by norm_num)
        (by linarith)]
      have := E.five_ge 5 hq5 (hp.W2 0 2 1) (x := P1) (by linarith [n1.1]) (by linarith [n1.2])
      linarith
    · rw [hS2, r0]
      simp only [mul_zero, hr.zero]

end helpers3

end Lane4.Case

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

noncomputable def S1e (fl : ℝ → ℝ) (p : Pert) (A : ℝ) : ℝ :=
  fl (fl (sw fl 5 (p.W2 0 2 1) *
        relu (fl (fl (sw fl 2 (p.W1 0 1 1) * A) + sw fl (-3) (p.b1 0 1))))
    + fl (sw fl 5 (p.W2 0 2 2) *
        relu (fl (fl (sw fl (-2) (p.W1 0 2 1) * A) + sw fl 1 (p.b1 0 2)))))

noncomputable def S2e (fl : ℝ → ℝ) (p : Pert) (A : ℝ) : ℝ :=
  fl (sw fl 5 (p.W2 0 3 0) *
        relu (fl (fl (sw fl (-2) (p.W1 0 0 1) * A) + sw fl 3 (p.b1 0 0))))

noncomputable def Gfun (fl : ℝ → ℝ) (d1 db d2 s : ℝ) : ℝ :=
  fl (sw fl 1 d2 * relu (fl (fl (sw fl (-1) d1 * s) + sw fl 1 db)))

noncomputable def Gcon (fl : ℝ → ℝ) (db d2 : ℝ) : ℝ := fl (sw fl 1 d2 * sw fl 1 db)

noncomputable def G1f (fl : ℝ → ℝ) (p : Pert) (s : ℝ) : ℝ :=
  Gfun fl (p.W1 1 0 2) (p.b1 1 0) (p.W2 1 4 0) s

noncomputable def G2f (fl : ℝ → ℝ) (p : Pert) (s : ℝ) : ℝ :=
  Gfun fl (p.W1 1 1 3) (p.b1 1 1) (p.W2 1 5 1) s

noncomputable def Gc1 (fl : ℝ → ℝ) (p : Pert) : ℝ := Gcon fl (p.b1 1 0) (p.W2 1 4 0)

noncomputable def Gc2 (fl : ℝ → ℝ) (p : Pert) : ℝ := Gcon fl (p.b1 1 1) (p.W2 1 5 1)

theorem mul_near' {x y s t a b S T : ℝ} (hx : |x - s| ≤ a) (hy : |y - t| ≤ b)
    (hs : |s| ≤ S) (ht : |t| ≤ T) : |x * y - s * t| ≤ a * T + b * S + a * b := by
  have h := mul_near hx hy
  have ha : 0 ≤ a := le_trans (abs_nonneg _) hx
  have hb : 0 ≤ b := le_trans (abs_nonneg _) hy
  have h1 := mul_le_mul_of_nonneg_left ht ha
  have h2 := mul_le_mul_of_nonneg_left hs hb
  linarith

section helpers4
variable {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ}

theorem gcon_props (E : Env u η M fl ex n) {db d2 : ℝ} (hdb : |db| ≤ 1 / 200)
    (hd2 : |d2| ≤ 1 / 200) :
    49 / 50 ≤ Gcon fl db d2 ∧ Gcon fl db d2 ≤ 51 / 50 ∧ fl (Gcon fl db d2) = Gcon fl db d2 := by
  have h1 := E.swp 1 1 (by norm_num) hdb (by norm_num) (by norm_num)
  have h2 := E.swp 1 1 (by norm_num) hd2 (by norm_num) (by norm_num)
  have m1 := mul_le_mul h2.1 h1.1 (by norm_num) (by linarith [h2.1])
  have m2 := mul_le_mul h2.2 h1.2 (by linarith [h1.1]) (by linarith [h2.2])
  have hb : |sw fl 1 d2 * sw fl 1 db| ≤ 10000 := abs_le.mpr ⟨by linarith, by linarith⟩
  have f := abs_le.mp (E.small hb)
  unfold Gcon
  refine ⟨by linarith [f.1], by linarith [f.2], ?_⟩
  exact E.idem (le_trans hb (by norm_num))

theorem gfun_props (E : Env u η M fl ex n) {d1 db d2 s : ℝ} (hd1 : |d1| ≤ 1 / 200)
    (hdb : |db| ≤ 1 / 200) (hd2 : |d2| ≤ 1 / 200) (hs : s = 0 ∨ 3 ≤ s) (hsb : |s| ≤ 500) :
    (s = 0 → Gfun fl d1 db d2 s = Gcon fl db d2) ∧ (3 ≤ s → Gfun fl d1 db d2 s = 0)
      ∧ fl (Gfun fl d1 db d2 s) = Gfun fl d1 db d2 s ∧ |Gfun fl d1 db d2 s| ≤ 2 := by
  have hr := E.hr
  have hc := gcon_props E hdb hd2
  have part1 : s = 0 → Gfun fl d1 db d2 s = Gcon fl db d2 := by
    intro h0
    unfold Gfun Gcon
    rw [h0]
    simp only [mul_zero, hr.zero, zero_add]
    rw [E.flsw 1 hdb (by norm_num)]
    have hpos : 0 ≤ sw fl 1 db := by
      have := E.swp 1 1 (by norm_num) hdb (by norm_num) (by norm_num)
      linarith [this.1]
    rw [relu_of_nonneg hpos]
  have part2 : 3 ≤ s → Gfun fl d1 db d2 s = 0 := by
    intro h3
    have hsw := E.swn (-1) (-1) (by norm_num) hd1 (by norm_num) (by norm_num)
    have hsw1 : sw fl (-1) d1 ≤ -149 / 150 := by linarith [hsw.2]
    have hsw2 : -2 ≤ sw fl (-1) d1 := by linarith [hsw.1]
    have hprod : sw fl (-1) d1 * s ≤ (-149 / 150) * s :=
      mul_le_mul_of_nonneg_right hsw1 (by linarith)
    have hbd : |sw fl (-1) d1 * s| ≤ 1000 := by
      have := amul (abs_le.mpr ⟨hsw2, by linarith⟩ : |sw fl (-1) d1| ≤ 2) hsb
      linarith
    have hbd' := abs_le.mp hbd
    have f1 := abs_le.mp (E.small (le_trans hbd (by norm_num)))
    have hb1 := E.swp 1 1 (by norm_num) hdb (by norm_num) (by norm_num)
    have hz : |fl (sw fl (-1) d1 * s) + sw fl 1 db| ≤ 10000 :=
      abs_le.mpr ⟨by linarith [f1.1, hbd'.1, hb1.1], by linarith [f1.2, hbd'.2, hb1.2]⟩
    have f2 := abs_le.mp (E.small hz)
    have hv : fl (fl (sw fl (-1) d1 * s) + sw fl 1 db) ≤ 0 := by
      linarith [f1.2, f2.2, hb1.2, hprod]
    unfold Gfun
    rw [relu_of_nonpos hv]
    simp only [mul_zero, hr.zero]
  refine ⟨part1, part2, ?_, ?_⟩
  · rcases hs with h0 | h3
    · rw [part1 h0]; exact hc.2.2
    · rw [part2 h3]; exact hr.zero
  · rcases hs with h0 | h3
    · rw [part1 h0]; exact abs_le.mpr ⟨by linarith [hc.1], by linarith [hc.2.1]⟩
    · rw [part2 h3]; norm_num

end helpers4

theorem find_spec (p : ℕ → Bool) : ∀ N : ℕ,
    (∀ j, (List.range N).reverse.find? p = some j →
      j < N ∧ p j = true ∧ ∀ k, j < k → k < N → p k = false) ∧
    ((List.range N).reverse.find? p = none → ∀ k, k < N → p k = false)
  | 0 => ⟨fun j h => by simp at h, fun _ k hk => absurd hk (Nat.not_lt_zero k)⟩
  | N + 1 => by
    obtain ⟨ih1, ih2⟩ := find_spec p N
    have hrev : (List.range (N + 1)).reverse = N :: (List.range N).reverse := by
      simp [List.range_succ]
    rw [hrev]
    by_cases hN : p N = true
    · have hf : (N :: (List.range N).reverse).find? p = some N := by simp [hN]
      rw [hf]
      refine ⟨fun j h => ?_, fun h => by simp at h⟩
      have hj : N = j := Option.some.inj h
      rw [← hj]
      exact ⟨by omega, hN, fun k hk1 hk2 => by omega⟩
    · have hN' : p N = false := by simpa using hN
      have hf : (N :: (List.range N).reverse).find? p = (List.range N).reverse.find? p := by
        simp [hN']
      rw [hf]
      refine ⟨fun j h => ?_, fun h k hk => ?_⟩
      · obtain ⟨a, b, c⟩ := ih1 j h
        refine ⟨by omega, b, fun k hk1 hk2 => ?_⟩
        by_cases hkN : k = N
        · rw [hkN]; exact hN'
        · exact c k hk1 (by omega)
      · by_cases hkN : k = N
        · rw [hkN]; exact hN'
        · exact ih2 h k (by omega)

theorem prevOcc_spec (w : List ℕ) (i : ℕ) :
    (∀ j, prevOcc w i = some j → j < i ∧ 1 ≤ j ∧ tokAt w j = tokAt w i ∧
      ∀ k, j < k → k < i → ¬ (1 ≤ k ∧ tokAt w k = tokAt w i)) ∧
    (prevOcc w i = none → ∀ k, k < i → ¬ (1 ≤ k ∧ tokAt w k = tokAt w i)) := by
  have key : ∀ k, (decide (1 ≤ k) && (tokAt w k == tokAt w i)) = true ↔
      (1 ≤ k ∧ tokAt w k = tokAt w i) := by
    intro k
    simp
  obtain ⟨h1, h2⟩ := find_spec (fun j => decide (1 ≤ j) && (tokAt w j == tokAt w i)) i
  unfold prevOcc
  refine ⟨fun j hj => ?_, fun hn k hk => ?_⟩
  · obtain ⟨a, b, c⟩ := h1 j hj
    have b' : (decide (1 ≤ j) && (tokAt w j == tokAt w i)) = true := b
    have b'' := (key j).mp b'
    refine ⟨a, b''.1, b''.2, fun k hk1 hk2 hc => ?_⟩
    have h3 : (decide (1 ≤ k) && (tokAt w k == tokAt w i)) = false := c k hk1 hk2
    have h4 := (key k).mpr hc
    rw [h3] at h4
    exact absurd h4 Bool.false_ne_true
  · have h3 : (decide (1 ≤ k) && (tokAt w k == tokAt w i)) = false := h2 hn k hk
    intro hc
    have h4 := (key k).mpr hc
    rw [h3] at h4
    exact absurd h4 Bool.false_ne_true

theorem tok12 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (m : ℕ) (h1 : 1 ≤ m)
    (h2 : m ≤ w.length) : tokAt w m = 1 ∨ tokAt w m = 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Lane4.Seq.tokAt_succ w k (by omega)]
  have := hw (w[k]'(by omega)) (List.getElem_mem (by omega))
  omega

theorem winner_exists (Mt : ℕ → Prop) [DecidablePred Mt] (i : ℕ) :
    ∃ j, j ≤ i ∧ (Mt j ∨ (j = i ∧ ∀ m, m ≤ i → ¬ Mt m)) ∧ ∀ m, j < m → m ≤ i → ¬ Mt m := by
  by_cases h : ∃ m, m ≤ i ∧ Mt m
  · obtain ⟨m, hm, hMt⟩ := h
    exact ⟨Nat.findGreatest Mt i, Nat.findGreatest_le i,
      Or.inl (Nat.findGreatest_spec hm hMt), fun k hk1 hk2 => Nat.findGreatest_is_greatest hk1 hk2⟩
  · push_neg at h
    exact ⟨i, le_refl i, Or.inr ⟨rfl, fun m hm => h m hm⟩, fun m h1 h2 => absurd h2 (by omega)⟩

theorem head_core {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {S Q B : ℝ}
    (hS1 : 99 ≤ S) (hS2 : S ≤ 101) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 320 * (n : ℝ))
    (hB0 : 0 ≤ B) (hBM : 4 * B + 4 ≤ M)
    (i j : ℕ) (hi : i + 1 ≤ n) (hji : j ≤ i) (hQ : j < i → 280 * (n : ℝ) ≤ Q)
    (qt : ℕ → ℝ) (hqt : ∀ m, m ≤ i → qt m = 0 ∨ qt m = Q)
    (hwin : qt j = Q ∨ (j = i ∧ ∀ m, m ≤ i → qt m = 0))
    (hlater : ∀ m, j < m → m ≤ i → qt m = 0)
    (s f : ℕ → ℝ) (hs : ∀ k, k ≤ i → s k = fl (fl (S * fl (k : ℝ)) + qt k))
    (hfb : ∀ k, k ≤ i → |f k| ≤ B) :
    |savg fl ex (cand Mask.causal n i) s f - f j| ≤ B / 100 + 1 / 2 ^ 90
      ∧ fl (savg fl ex (cand Mask.causal n i) s f) = savg fl ex (cand Mask.causal n i) s f := by
  have hr := E.hr
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast E.hn1
  have hnM : (n : ℝ) ≤ M := by
    have := range_lin E.hM E.hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have h1000 : 1000 * (n : ℝ) ≤ M := range_lin E.hM E.hn1 (by norm_num) (by norm_num)
  have hpl : ∀ k, k ≤ i → 0 ≤ fl (k : ℝ) ∧ fl (k : ℝ) ≤ n + 1 / 100 := fun k hk =>
    hr.pos_le E.hu0 E.hη (show k ≤ n by omega) E.hn hnM
  have hpn : ∀ k, k ≤ i → |fl (k : ℝ) - k| ≤ 1 / 200 := fun k hk =>
    hr.pos_near E.hu0 E.hη (show k ≤ n by omega) E.hn hnM
  have hpg : ∀ a b : ℕ, a ≤ b → b ≤ i → fl (a : ℝ) + ((b : ℝ) - a) - 1 / 100 ≤ fl (b : ℝ) :=
    fun a b hab hb => hr.pos_gap E.hu0 E.hη hab (show b ≤ n by omega) E.hn hnM
  have ha : ∀ k, k ≤ i → 0 ≤ S * fl (k : ℝ) ∧ S * fl (k : ℝ) ≤ 102 * n := by
    intro k hk
    obtain ⟨h0, h1⟩ := hpl k hk
    refine ⟨mul_nonneg (by linarith) h0, ?_⟩
    have := mul_le_mul hS2 h1 h0 (by norm_num)
    linarith
  have haa : ∀ k, k ≤ i → |S * fl (k : ℝ)| ≤ 1000 * n := by
    intro k hk
    obtain ⟨h0, h1⟩ := ha k hk
    rw [abs_of_nonneg h0]
    linarith
  have hfa : ∀ k, k ≤ i → |fl (S * fl (k : ℝ)) - S * fl (k : ℝ)| ≤ 4 :=
    fun k hk => E.fln (haa k hk)
  have hq : ∀ k, k ≤ i → 0 ≤ qt k ∧ qt k ≤ 320 * n := by
    intro k hk
    rcases hqt k hk with h | h
    · rw [h]; exact ⟨le_refl _, by linarith⟩
    · rw [h]; exact ⟨hQ0, hQ1⟩
  have hT : ∀ k, k ≤ i → |fl (S * fl (k : ℝ)) + qt k| ≤ 1000 * n := by
    intro k hk
    obtain ⟨h0, h1⟩ := ha k hk
    obtain ⟨q0, q1⟩ := hq k hk
    have f := abs_le.mp (hfa k hk)
    rw [abs_le]
    constructor <;> linarith [f.1, f.2]
  have hsk : ∀ k, k ≤ i → |s k - (S * fl (k : ℝ) + qt k)| ≤ 8 := by
    intro k hk
    have e1 := E.fln (hT k hk)
    have e2 := abs_le.mp (hfa k hk)
    rw [hs k hk]
    rw [abs_le] at e1 ⊢
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  have hsb : ∀ k, k ≤ i → |s k| ≤ 500 * n := by
    intro k hk
    have h := abs_le.mp (hsk k hk)
    obtain ⟨h0, h1⟩ := ha k hk
    obtain ⟨q0, q1⟩ := hq k hk
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  have hgap : ∀ k ∈ cand Mask.causal n i, k ≠ j → s k ≤ s j - 16 * (ndist j k : ℝ) := by
    intro k hk hne
    rw [Lane4.Seq.mem_cand_causal] at hk
    rw [ndist_cast]
    obtain ⟨hk1, hk2⟩ := abs_le.mp (hsk k hk)
    obtain ⟨hj1, hj2⟩ := abs_le.mp (hsk j hji)
    rcases lt_or_gt_of_ne hne with hkj | hkj
    · have hg := hpg k j (le_of_lt hkj) hji
      have hd1 : (k : ℝ) + 1 ≤ j := by exact_mod_cast hkj
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (j : ℝ) - k)]
      have hD0 : 0 ≤ fl (j : ℝ) - fl (k : ℝ) := by linarith
      have hSD := mul_le_mul_of_nonneg_right hS1 hD0
      have hqq : qt k ≤ qt j := by
        rcases hwin with h | ⟨_, h2⟩
        · rcases hqt k hk with h' | h' <;> linarith
        · linarith [h2 k hk, h2 j hji]
      linarith
    · have hg := hpg j k (le_of_lt hkj) hk
      obtain ⟨hpk1, hpk2⟩ := abs_le.mp (hpn k hk)
      obtain ⟨hpj1, hpj2⟩ := abs_le.mp (hpn j hji)
      have hd1 : (j : ℝ) + 1 ≤ k := by exact_mod_cast hkj
      rw [abs_of_nonpos (by linarith : (j : ℝ) - k ≤ 0)]
      have hD0 : 0 ≤ fl (k : ℝ) - fl (j : ℝ) := by linarith
      have hSD := mul_le_mul_of_nonneg_right hS2 hD0
      have hqj : qt j = Q := by
        rcases hwin with h | ⟨h1, _⟩
        · exact h
        · exfalso; omega
      have hqk : qt k = 0 := hlater k hkj hk
      have hQj := hQ (by omega)
      have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast (show k + 1 ≤ n by omega)
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
  have hj : j ∈ cand Mask.causal n i := by
    rw [Lane4.Seq.mem_cand_causal]; exact hji
  have hlen : (cand Mask.causal n i).length ≤ n := by simpa [cand] using hi
  have hSb : ∀ k ∈ cand Mask.causal n i, |s k| ≤ 500 * (n : ℝ) := by
    intro k hk
    rw [Lane4.Seq.mem_cand_causal] at hk
    exact hsb k hk
  have hfB : ∀ k ∈ cand Mask.causal n i, |f k| ≤ B := by
    intro k hk
    rw [Lane4.Seq.mem_cand_causal] at hk
    exact hfb k hk
  exact soft_near hr E.he E.hu0 E.hu1 E.hη0 E.hη (Lane4.Seq.cand_nodup _ _ _) hlen E.hn E.hnη
    hj hgap hSb (by linarith) hfB hBM

end Lane4.Case

namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

theorem stage1_A {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} (w : List ℕ)
    (E : Env u η M fl ex (w.length + 1)) (hp : p.Within (1 / 200))
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (m : ℕ) (hm : m ≤ w.length) (A : ℝ)
    (hA : A = savg fl ex (cand Mask.strict (w.length + 1) m)
      (hscore hP fl (p.A 0 0) (net.init fl p w) m)
      (fun j => rdot fl rV1 (net.init fl p w j) (p.V 0 0 1) 0 0)) :
    fl A = A ∧ |A - ((tokAt w (m - 1) : ℕ) : ℝ)| ≤ 7 / 100 ∧ |A| ≤ 3 := by
  have hr := E.hr
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have hz : A = 0 := by
      rw [hA]
      exact soft_zeros hr (by intro k hk; simp [cand] at hk)
    rw [hz]
    refine ⟨hr.zero, ?_, ?_⟩
    · norm_num [Lane4.Seq.tokAt_zero]
    · norm_num
  · have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
      have := range_lin E.hM E.hn1 (c := 1) (by norm_num) (by norm_num)
      linarith
    have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast E.hn1
    have h1000 : 1000 * ((w.length + 1 : ℕ) : ℝ) ≤ M :=
      range_lin E.hM E.hn1 (by norm_num) (by norm_num)
    have hS := E.swp 100 100 (by norm_num) (hp.A 0 0 9 10) (by norm_num) (by norm_num)
    have hT := E.swp 1 1 (by norm_num) (hp.V 0 0 1 0) (by norm_num) (by norm_num)
    have hpl : ∀ k, k ≤ w.length + 1 →
        0 ≤ fl (k : ℝ) ∧ fl (k : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) + 1 / 100 :=
      fun k hk => hr.pos_le E.hu0 E.hη hk E.hn hnM
    have hSk : ∀ k, k ≤ w.length + 1 → |sw fl 100 (p.A 0 0 9 10) * fl (k : ℝ)|
        ≤ 1000 * ((w.length + 1 : ℕ) : ℝ) := by
      intro k hk
      obtain ⟨h0, h1⟩ := hpl k hk
      have hS0 : 0 ≤ sw fl 100 (p.A 0 0 9 10) := by linarith [hS.1]
      rw [abs_of_nonneg (mul_nonneg hS0 h0)]
      have := mul_le_mul (show sw fl 100 (p.A 0 0 9 10) ≤ 101 by linarith [hS.2]) h1 h0
        (by norm_num)
      linarith
    have hsk : ∀ k, k ≤ w.length + 1 →
        hscore hP fl (p.A 0 0) (net.init fl p w) m k
          = fl (sw fl 100 (p.A 0 0 9 10) * fl (k : ℝ)) := by
      intro k hk
      simp only [hscore, init_eq hr p w hw]
      exact scoreP_eq hr (p.A 0 0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (hr.idem _ (le_trans (hSk k hk) h1000))
    have hfk : ∀ k, rdot fl rV1 (net.init fl p w k) (p.V 0 0 1) 0 0
        = fl (sw fl 1 (p.V 0 0 1 0) * ev fl p w k) := by
      intro k
      rw [init_eq hr p w hw k]
      exact valP_eq hr (p.V 0 0 1) _ _ _ _ _ _ _ _ _ _ _
        (E.idem_swx 1 (d := p.V 0 0 1 0) (x := ev fl p w k) (hp.V 0 0 1 0) (by norm_num)
          (by norm_num) (by have := (ev_facts E hp w hw k).2.2; linarith))
    have hT' : |sw fl 1 (p.V 0 0 1 0) - 1| ≤ 1 / 150 :=
      abs_le.mpr ⟨by linarith [hT.1], by linarith [hT.2]⟩
    have hTa : |sw fl 1 (p.V 0 0 1 0)| ≤ 151 / 150 :=
      abs_le.mpr ⟨by linarith [hT.1], by linarith [hT.2]⟩
    have hfb : ∀ k, k ≤ m - 1 →
        |(fun j => rdot fl rV1 (net.init fl p w j) (p.V 0 0 1) 0 0) k| ≤ 3 := by
      intro k _
      show |rdot fl rV1 (net.init fl p w k) (p.V 0 0 1) 0 0| ≤ 3
      rw [hfk k]
      obtain ⟨_, hE1, _⟩ := ev_facts E hp w hw k
      have htk : ((tokAt w k : ℕ) : ℝ) ≤ 2 := by exact_mod_cast tok_le w hw k
      have htk0 : (0 : ℝ) ≤ ((tokAt w k : ℕ) : ℝ) := Nat.cast_nonneg _
      obtain ⟨e1, e2⟩ := abs_le.mp hE1
      have hev : |ev fl p w k| ≤ 151 / 75 := abs_le.mpr ⟨by linarith, by linarith⟩
      have h2 := amul hTa hev
      have h3 := E.flabs h2 (by norm_num)
      linarith
    have hcc : cand Mask.strict (w.length + 1) m = cand Mask.causal (w.length + 1) (m - 1) := by
      simp only [cand]
      congr 1
      omega
    have hs : ∀ k, k ≤ m - 1 → hscore hP fl (p.A 0 0) (net.init fl p w) m k
        = fl (fl (sw fl 100 (p.A 0 0 9 10) * fl (k : ℝ)) + (fun _ => (0 : ℝ)) k) := by
      intro k hk
      rw [hsk k (by omega)]
      show fl (sw fl 100 (p.A 0 0 9 10) * fl (k : ℝ))
        = fl (fl (sw fl 100 (p.A 0 0 9 10) * fl (k : ℝ)) + 0)
      rw [add_zero, hr.idem _ (le_trans (hSk k (by omega)) h1000)]
    obtain ⟨hc1, hc2⟩ := head_core E (S := sw fl 100 (p.A 0 0 9 10)) (Q := 0) (B := 3)
      (by linarith [hS.1]) (by linarith [hS.2]) (le_refl _) (by linarith) (by norm_num)
      (by linarith [E.M1e4]) (m - 1) (m - 1) (by omega) (le_refl _)
      (fun h => absurd h (lt_irrefl _)) (fun _ => 0) (fun _ _ => Or.inl rfl) (Or.inl rfl)
      (fun _ _ _ => rfl) (hscore hP fl (p.A 0 0) (net.init fl p w) m)
      (fun j => rdot fl rV1 (net.init fl p w j) (p.V 0 0 1) 0 0) hs hfb
    have hAeq : A = savg fl ex (cand Mask.causal (w.length + 1) (m - 1))
        (hscore hP fl (p.A 0 0) (net.init fl p w) m)
        (fun j => rdot fl rV1 (net.init fl p w j) (p.V 0 0 1) 0 0) := by
      rw [hA, hcc]
    have hE := ev_facts E hp w hw (m - 1)
    have htok : ((tokAt w (m - 1) : ℕ) : ℝ) ≤ 2 := by exact_mod_cast tok_le w hw (m - 1)
    have htok0 : (0 : ℝ) ≤ ((tokAt w (m - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    have m1 := mul_near' hT' hE.2.1 (S := 1) (T := 2) (by norm_num)
      (by rw [abs_of_nonneg htok0]; exact htok)
    rw [one_mul] at m1
    have hb : |sw fl 1 (p.V 0 0 1 0) * ev fl p w (m - 1)| ≤ 3 := by
      obtain ⟨a1, a2⟩ := abs_le.mp m1
      rw [abs_le]
      constructor <;> linarith
    have e1 := E.flnear m1 hb (by norm_num)
    have hc1' : |A - fl (sw fl 1 (p.V 0 0 1 0) * ev fl p w (m - 1))| ≤ 3 / 100 + 1 / 2 ^ 90 := by
      rw [← hfk (m - 1), hAeq]
      exact hc1
    have hc2' : fl A = A := by
      rw [hAeq]
      exact hc2
    have e3 := abs_sub_le A (fl (sw fl 1 (p.V 0 0 1 0) * ev fl p w (m - 1)))
      ((tokAt w (m - 1) : ℕ) : ℝ)
    have e4 : |A - ((tokAt w (m - 1) : ℕ) : ℝ)| ≤ 7 / 100 := by linarith
    refine ⟨hc2', e4, ?_⟩
    have h5 := abs_sub_abs_le_abs_sub A ((tokAt w (m - 1) : ℕ) : ℝ)
    rw [abs_of_nonneg htok0] at h5
    linarith

theorem stage1 {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} (w : List ℕ)
    (E : Env u η M fl ex (w.length + 1)) (hp : p.Within (1 / 200))
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (m : ℕ) (hm : m ≤ w.length) :
    ∃ A S1 S2 : ℝ,
      sblock blk1 fl ex p 0 (w.length + 1) (net.init fl p w) m
        = st (ev fl p w m) A S1 S2 0 0 0 0 0 (fl (m : ℝ)) (fl ((w.length + 1 : ℕ) : ℝ))
      ∧ fl A = A ∧ |A| ≤ 3
      ∧ ((tokAt w (m - 1) = 1 → S1 = 0) ∧ (tokAt w (m - 1) ≠ 1 → 3 ≤ S1)
        ∧ (tokAt w (m - 1) = 2 → S2 = 0) ∧ (tokAt w (m - 1) ≠ 2 → 3 ≤ S2)
        ∧ |S1| ≤ 500 ∧ |S2| ≤ 500 ∧ fl S1 = S1 ∧ fl S2 = S2) := by
  have hr := E.hr
  obtain ⟨A, hAdef⟩ : ∃ A, A = savg fl ex (cand Mask.strict (w.length + 1) m)
      (hscore hP fl (p.A 0 0) (net.init fl p w) m)
      (fun j => rdot fl rV1 (net.init fl p w j) (p.V 0 0 1) 0 0) := ⟨_, rfl⟩
  obtain ⟨hAfix, hAnear, hAb⟩ := stage1_A w E hp hw m hm A hAdef
  have hat := attnP_eq (ex := ex) hr (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) m
  rw [← hAdef] at hat
  have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
    have := range_lin E.hM E.hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have hmM : (m : ℝ) ≤ M := by
    have : (m : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast (show m ≤ w.length + 1 by omega)
    linarith
  have hqi : fl (fl (m : ℝ)) = fl (m : ℝ) :=
    hr.idem _ (by rw [abs_of_nonneg (Nat.cast_nonneg m)]; exact hmM)
  have hqn : fl (fl ((w.length + 1 : ℕ) : ℝ)) = fl ((w.length + 1 : ℕ) : ℝ) :=
    hr.idem _ (by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact hnM)
  have hE := ev_facts E hp w hw m
  have hτ : tokAt w (m - 1) ≤ 2 := tok_le w hw (m - 1)
  refine ⟨A, S1e fl p A, S2e fl p A, ?_, hAfix, hAb, ?_⟩
  · exact blk1_eq E hp (net.init fl p w) m (ev fl p w m) (fl (m : ℝ))
      (fl ((w.length + 1 : ℕ) : ℝ)) A (init_eq hr p w hw m) hat hE.1 hqi hqn hAfix hAb
  · exact mlp1_props E hp A (tokAt w (m - 1)) hτ hAnear (S1e fl p A) (S2e fl p A) rfl rfl

theorem stage12 {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} (w : List ℕ)
    (E : Env u η M fl ex (w.length + 1)) (hp : p.Within (1 / 200))
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) :
    ∀ m : ℕ, ∃ A S1 S2 : ℝ, m ≤ w.length →
      (sblock blk2 fl ex p 1 (w.length + 1)
          (sblock blk1 fl ex p 0 (w.length + 1) (net.init fl p w)) m
        = st (ev fl p w m) A S1 S2 (G1f fl p S1) (G2f fl p S2) 0 0 0 (fl (m : ℝ))
          (fl ((w.length + 1 : ℕ) : ℝ)))
      ∧ fl A = A ∧ |A| ≤ 3 ∧ fl S1 = S1 ∧ fl S2 = S2 ∧ |S1| ≤ 500 ∧ |S2| ≤ 500
      ∧ (tokAt w (m - 1) = 1 → G1f fl p S1 = Gc1 fl p)
      ∧ (tokAt w (m - 1) ≠ 1 → G1f fl p S1 = 0)
      ∧ (tokAt w (m - 1) = 2 → G2f fl p S2 = Gc2 fl p)
      ∧ (tokAt w (m - 1) ≠ 2 → G2f fl p S2 = 0) := by
  intro m
  by_cases hm : m ≤ w.length
  · obtain ⟨A, S1, S2, hb1, hAfix, hAb, hτ1, hτ2, hτ3, hτ4, hS1b, hS2b, hfS1, hfS2⟩ :=
      stage1 w E hp hw m hm
    have hr := E.hr
    have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
      have := range_lin E.hM E.hn1 (c := 1) (by norm_num) (by norm_num)
      linarith
    have hmM : (m : ℝ) ≤ M := by
      have : (m : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show m ≤ w.length + 1 by omega)
      linarith
    have hqi : fl (fl (m : ℝ)) = fl (m : ℝ) :=
      hr.idem _ (by rw [abs_of_nonneg (Nat.cast_nonneg m)]; exact hmM)
    have hqn : fl (fl ((w.length + 1 : ℕ) : ℝ)) = fl ((w.length + 1 : ℕ) : ℝ) :=
      hr.idem _ (by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact hnM)
    have hE := ev_facts E hp w hw m
    have hs1 : tokAt w (m - 1) = 1 ∨ tokAt w (m - 1) ≠ 1 := em _
    have hs2 : tokAt w (m - 1) = 2 ∨ tokAt w (m - 1) ≠ 2 := em _
    have hS1c : S1 = 0 ∨ 3 ≤ S1 := by
      rcases hs1 with h | h
      · exact Or.inl (hτ1 h)
      · exact Or.inr (hτ2 h)
    have hS2c : S2 = 0 ∨ 3 ≤ S2 := by
      rcases hs2 with h | h
      · exact Or.inl (hτ3 h)
      · exact Or.inr (hτ4 h)
    have gp1 := gfun_props E (hp.W1 1 0 2) (hp.b1 1 0) (hp.W2 1 4 0) hS1c hS1b
    have gp2 := gfun_props E (hp.W1 1 1 3) (hp.b1 1 1) (hp.W2 1 5 1) hS2c hS2b
    refine ⟨A, S1, S2, fun _ => ⟨?_, hAfix, hAb, hfS1, hfS2, hS1b, hS2b, ?_, ?_, ?_, ?_⟩⟩
    · exact blk2_eq E hp (sblock blk1 fl ex p 0 (w.length + 1) (net.init fl p w)) m
        (ev fl p w m) A S1 S2 (fl (m : ℝ)) (fl ((w.length + 1 : ℕ) : ℝ)) hb1 hE.1 hAfix hfS1
        hfS2 hqi hqn hS1b hS2b
    · intro h
      exact gp1.1 (hτ1 h)
    · intro h
      exact gp1.2.1 (hτ2 h)
    · intro h
      exact gp2.1 (hτ3 h)
    · intro h
      exact gp2.2.1 (hτ4 h)
  · exact ⟨0, 0, 0, fun h => absurd h hm⟩

end Lane4.Case
