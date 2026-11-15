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
    W1 := [[-3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
           [3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]],
    b1 := [1, -8],
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
            relu (fl (fl (fl (sw fl (-3) (p.W1 2 0 0) * e) + fl (sw fl 1 (p.W1 2 0 6) * H1))
              + sw fl 1 (p.b1 2 0)))) +
          fl (sw fl 1 (p.W2 2 8 1) *
            relu (fl (fl (fl (sw fl 3 (p.W1 2 1 0) * e) + fl (sw fl 1 (p.W1 2 1 7) * H2))
              + sw fl (-8) (p.b1 2 1))))))
        qi qn := by
  have hr := E.hr
  have hR1 := E.pair_bd (-3) 1 (-3) 1 (by norm_num) (by norm_num) (hp.W1 2 0 0) (hp.W1 2 0 6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) heb hH1b (by norm_num) (by norm_num)
  have hR2 := E.pair_bd 3 1 3 1 (by norm_num) (by norm_num) (hp.W1 2 1 0) (hp.W1 2 1 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) heb hH2b (by norm_num) (by norm_num)
  have hb1 := E.swab 1 1 (by norm_num) (hp.b1 2 0) (by norm_num) (by norm_num)
  have hb2 := E.swab (-8) (-8) (by norm_num) (hp.b1 2 1) (by norm_num) (by norm_num)
  have e1 : |(1 : ℝ)| = 1 := abs_one
  have e8 : |(-8 : ℝ)| = 8 := by norm_num
  rw [e1] at hb1
  rw [e8] at hb2
  have hb1' : |sw fl 1 (p.b1 2 0)| ≤ 2 := by linarith
  have hb2' : |sw fl (-8) (p.b1 2 1)| ≤ 9 := by linarith
  have hU1 : |fl (fl (fl (sw fl (-3) (p.W1 2 0 0) * e) + fl (sw fl 1 (p.W1 2 0 6) * H1))
      + sw fl 1 (p.b1 2 0))| ≤ 100 := by
    have h1 : |fl (fl (sw fl (-3) (p.W1 2 0 0) * e) + fl (sw fl 1 (p.W1 2 0 6) * H1))
        + sw fl 1 (p.b1 2 0)| ≤ 90 :=
      le_trans (abs_add_le _ _) (by linarith [hR1.1])
    have := E.flabs h1 (by norm_num)
    linarith
  have hU2 : |fl (fl (fl (sw fl 3 (p.W1 2 1 0) * e) + fl (sw fl 1 (p.W1 2 1 7) * H2))
      + sw fl (-8) (p.b1 2 1))| ≤ 100 := by
    have h1 : |fl (fl (sw fl 3 (p.W1 2 1 0) * e) + fl (sw fl 1 (p.W1 2 1 7) * H2))
        + sw fl (-8) (p.b1 2 1)| ≤ 91 :=
      le_trans (abs_add_le _ _) (by linarith [hR2.1])
    have := E.flabs h1 (by norm_num)
    linarith
  have r1 := relu_abs (fl (fl (fl (sw fl (-3) (p.W1 2 0 0) * e) + fl (sw fl 1 (p.W1 2 0 6) * H1))
      + sw fl 1 (p.b1 2 0)))
  have r2 := relu_abs (fl (fl (fl (sw fl 3 (p.W1 2 1 0) * e) + fl (sw fl 1 (p.W1 2 1 7) * H2))
      + sw fl (-8) (p.b1 2 1)))
  have hI0 := E.idem_swx (-3) (d := p.W1 2 0 0) (x := e) (hp.W1 2 0 0) (by norm_num)
    (by norm_num) (by linarith)
  have hI1 := E.idem_swx 3 (d := p.W1 2 1 0) (x := e) (hp.W1 2 1 0) (by norm_num)
    (by norm_num) (by linarith)
  have hO1 := E.idem_swx 1 (d := p.W2 2 8 0) (hp.W2 2 8 0) (by norm_num) (by norm_num)
    (by linarith : |relu (fl (fl (fl (sw fl (-3) (p.W1 2 0 0) * e)
      + fl (sw fl 1 (p.W1 2 0 6) * H1)) + sw fl 1 (p.b1 2 0)))| ≤ 100000)
  have hO := (E.pair_bd 1 1 1 1 (by norm_num) (by norm_num) (hp.W2 2 8 0) (hp.W2 2 8 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith : |relu (fl (fl (fl (sw fl (-3) (p.W1 2 0 0) * e)
      + fl (sw fl 1 (p.W1 2 0 6) * H1)) + sw fl 1 (p.b1 2 0)))| ≤ 100)
    (by linarith : |relu (fl (fl (fl (sw fl 3 (p.W1 2 1 0) * e)
      + fl (sw fl 1 (p.W1 2 1 7) * H2)) + sw fl (-8) (p.b1 2 1)))| ≤ 100)
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
      ∧ |S1| ≤ 500 ∧ |S2| ≤ 500 := by
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
  have hcases : τ = 0 ∨ τ = 1 ∨ τ = 2 := by omega
  rcases hcases with h | h | h
  · have ht : (τ : ℝ) = 0 := by rw [h]; norm_num
    have r0 : relu P0 = P0 := relu_of_nonneg (by linarith [n0.1])
    have r1 : relu P1 = 0 := relu_of_nonpos (by linarith [n1.2])
    have r2 : relu P2 = P2 := relu_of_nonneg (by linarith [n2.1])
    refine ⟨fun h1 => by exfalso; omega, fun _ => ?_, fun h1 => by exfalso; omega,
      fun _ => ?_, bS1, bS2⟩
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
      fun _ => ?_, bS1, bS2⟩
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
      fun h1 => by exfalso; omega, bS1, bS2⟩
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
