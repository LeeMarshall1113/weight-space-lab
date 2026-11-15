namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.style.longLine false

def z20 : List ℚ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def z17 : List ℚ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def z6 : List ℚ := [0,0,0,0,0,0]
def z3 : List ℚ := [0,0,0]
def rS : List ℚ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,20,0]
def u0 : List ℚ := [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def u1 : List ℚ := [0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def u2 : List ℚ := [0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def rB1 : List ℚ := [0,0,0,0,0,0,0,-60,0,0,0,0,0,0,0,0,0,0,0,0]
def rB2 : List ℚ := [0,0,0,0,0,0,0,0,-60,0,0,0,0,0,0,0,0,0,0,0]
def rB3 : List ℚ := [0,0,0,0,0,0,0,0,0,-60,0,0,0,0,0,0,0,0,0,0]
def v1 : List ℚ := [0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0]
def v2 : List ℚ := [0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0]
def v3 : List ℚ := [0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0]
def wm1 : List ℚ := [0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def wm2 : List ℚ := [0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def wm3 : List ℚ := [0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0]
def wg1 : List ℚ := [0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def wg2 : List ℚ := [0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def wg3 : List ℚ := [0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0]
def wt1 : List ℚ := [1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0]
def wt2 : List ℚ := [0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0]
def wt3 : List ℚ := [0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0]
def owr : List ℚ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,(23/20 : ℚ),0,0,0]

def hd0 : Head :=
  { A := [z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, rS, z20, z20],
    V := [z20, z20, z20, z20, u0, u1, u2, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20],
    mask := Mask.strict }
def hd1 : Head :=
  { A := [z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, rS, z20, rB1],
    V := [z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, v1, z20, z20, z20, z20, z20, z20],
    mask := Mask.causal }
def hd2 : Head :=
  { A := [z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, rS, z20, rB2],
    V := [z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, v2, z20, z20, z20, z20, z20],
    mask := Mask.causal }
def hd3 : Head :=
  { A := [z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, rS, z20, rB3],
    V := [z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, v3, z20, z20, z20, z20],
    mask := Mask.causal }

def blk0 : Block :=
  { heads := [hd0],
    W1 := [wm1, wm2, wm3, wg1, wg2, wg3],
    b1 := [9/10, 9/10, 9/10, -11/10, -11/10, -11/10],
    W2 := [z6, z6, z6, z6, z6, z6, z6, [1,0,0,0,0,0], [0,1,0,0,0,0], [0,0,1,0,0,0],
           [0,0,0,1,0,0], [0,0,0,0,1,0], [0,0,0,0,0,1], z6, z6, z6, z6, z6, z6, z6],
    b2 := z20 }
def blk1 : Block :=
  { heads := [hd1, hd2, hd3],
    W1 := [wt1, wt2, wt3],
    b1 := [-103/100, -103/100, -103/100],
    W2 := [z3, z3, z3, z3, z3, z3, z3, z3, z3, z3, z3, z3, z3, z3, z3, z3, [1,1,1], z3, z3, z3],
    b2 := z20 }

def net : TNet :=
  { embed := [z17, [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], [0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
              [0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0]],
    blocks := [blk0, blk1],
    outW := owr,
    outB := 0 }

theorem net_shape : TNet.shapeOK net 3 = true := by decide

def vec20 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 : ℝ) : Vec :=
  [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19]

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

theorem Env.big {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {c : ℝ}
    (hc : c ≤ 2 ^ 40) : c ≤ M := range_const E.hM E.hn1 hc

theorem Env.lin {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ 2 ^ 40) : c * (n : ℝ) ≤ M := range_lin E.hM E.hn1 hc0 hc

theorem Env.nM {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) : (n : ℝ) ≤ M := by
  have := E.lin (c := 1) (by norm_num) (by norm_num)
  linarith

theorem Env.e5 {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {x : ℝ}
    (hx : |x| ≤ 100) : |fl x - x| ≤ 1 / 10 ^ 5 := by
  have h := E.hr.abs E.hu0 hx (E.big (by norm_num))
  have h1 : u * 100 ≤ 1 / 2 ^ 24 * 100 := mul_le_mul_of_nonneg_right E.hu1 (by norm_num)
  have h2 := eta_tiny E.hη
  have h3 : (1 : ℝ) / 2 ^ 24 * 100 + 1 / 10 ^ 40 ≤ 1 / 10 ^ 5 := by norm_num
  linarith

theorem Env.idem {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {x : ℝ}
    (hx : |x| ≤ 100) : fl (fl x) = fl x :=
  E.hr.idem x (le_trans hx (E.big (by norm_num)))

theorem Env.fl100 {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {x : ℝ}
    (hx : |x| ≤ 100) : |fl x| ≤ 101 := by
  have h := E.e5 hx
  have h1 := abs_sub_abs_le_abs_sub (fl x) x
  have h2 : (1 : ℝ) / 10 ^ 5 ≤ 1 := by norm_num
  linarith

theorem Env.u6 {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) : u ≤ 1 / 10 ^ 6 :=
  le_trans E.hu1 (by norm_num)

theorem Env.swIv {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) (c : ℚ) (x a : ℝ)
    (hx : (c : ℝ) = x) (ha : |x| = a) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 100) {d : ℝ}
    (hd : |d| ≤ 1 / 200) : |sw fl c d - x| ≤ a / 190 := by
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by
    have := E.u6
    have h6 : (1 : ℝ) / 10 ^ 6 ≤ 1 / 10 ^ 6 := le_refl _
    nlinarith [E.hu0]
  have hM2 : 2 * |(c : ℝ)| ≤ M := by
    rw [hx, ha]
    exact le_trans (by linarith) (E.big (c := 200) (by norm_num))
  have h := sw_near E.hr E.hu0 c hd (by norm_num) hM2 hε
  rw [hx, ha] at h
  have h2 := eta_tiny E.hη
  have h3 : (1 : ℝ) / 199 * a + 1 / 10 ^ 40 ≤ a / 190 := by nlinarith
  linarith

theorem Env.sw_one {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {d : ℝ}
    (hd : |d| ≤ 1 / 200) : 994 / 1000 ≤ sw fl 1 d ∧ sw fl 1 d ≤ 1006 / 1000 := by
  have h := E.swIv 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hd
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

theorem Env.sw_m1 {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {d : ℝ}
    (hd : |d| ≤ 1 / 200) : -1006 / 1000 ≤ sw fl (-1) d ∧ sw fl (-1) d ≤ -994 / 1000 := by
  have h := E.swIv (-1) (-1) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hd
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

theorem Env.sw_20 {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {d : ℝ}
    (hd : |d| ≤ 1 / 200) : 198 / 10 ≤ sw fl 20 d ∧ sw fl 20 d ≤ 202 / 10 := by
  have h := E.swIv 20 20 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hd
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

theorem Env.sw_m60 {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {d : ℝ}
    (hd : |d| ≤ 1 / 200) : -604 / 10 ≤ sw fl (-60) d ∧ sw fl (-60) d ≤ -596 / 10 := by
  have h := E.swIv (-60) (-60) 60 (by norm_num) (by rw [abs_of_neg (by norm_num)]; norm_num)
    (by norm_num) (by norm_num) hd
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

theorem Env.sw_9_10 {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {d : ℝ}
    (hd : |d| ≤ 1 / 200) : 894 / 1000 ≤ sw fl (9 / 10) d ∧ sw fl (9 / 10) d ≤ 906 / 1000 := by
  have h := E.swIv (9 / 10) (9 / 10) (9 / 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hd
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

theorem Env.sw_m11_10 {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {d : ℝ}
    (hd : |d| ≤ 1 / 200) :
    -1106 / 1000 ≤ sw fl (-11 / 10) d ∧ sw fl (-11 / 10) d ≤ -1094 / 1000 := by
  have h := E.swIv (-11 / 10) (-11 / 10) (11 / 10) (by norm_num)
    (by rw [abs_of_neg (by norm_num)]; norm_num) (by norm_num) (by norm_num) hd
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

theorem Env.sw_m103 {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {d : ℝ}
    (hd : |d| ≤ 1 / 200) :
    -1036 / 1000 ≤ sw fl (-103 / 100) d ∧ sw fl (-103 / 100) d ≤ -1024 / 1000 := by
  have h := E.swIv (-103 / 100) (-103 / 100) (103 / 100) (by norm_num)
    (by rw [abs_of_neg (by norm_num)]; norm_num) (by norm_num) (by norm_num) hd
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

theorem Env.sw_23_20 {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {d : ℝ}
    (hd : |d| ≤ 1 / 200) :
    1143 / 1000 ≤ sw fl (23 / 20) d ∧ sw fl (23 / 20) d ≤ 1157 / 1000 := by
  have h := E.swIv (23 / 20) (23 / 20) (23 / 20) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hd
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) : tokAt w j ≤ 3 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem tok_pos (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (i : ℕ) (h1 : 1 ≤ i)
    (h2 : i ≤ w.length) : 1 ≤ tokAt w i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < w.length := by omega
  rw [Lane4.Seq.tokAt_succ w k hk]
  exact (hw _ (List.getElem_mem hk)).1

noncomputable def qE (fl : ℝ → ℝ) (p : Pert) (τ s : ℕ) : ℝ :=
  if τ = s then sw fl 1 (p.E s (s - 1)) else 0

noncomputable def hE (fl : ℝ → ℝ) (p : Pert) (τ : ℕ) : ℝ :=
  if τ = 2 then sw fl 1 (p.E 2 3) else if τ = 3 then sw fl 1 (p.E 3 3) else 0

theorem init_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) :
    net.init fl p w j = vec20 (qE fl p (tokAt w j) 1) (qE fl p (tokAt w j) 2)
      (qE fl p (tokAt w j) 3) (hE fl p (tokAt w j)) 0 0 0 0 0 0 0 0 0 0 0 0 0 1 (fl (j : ℝ))
      (fl ((w.length + 1 : ℕ) : ℝ)) := by
  have h3 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 := by
    have := tok_le w hw j
    omega
  rcases h3 with h | h | h | h <;>
    simp [TNet.init, net, swRow, vec20, pos, qE, hE, h, sw_zero hr, z17]

theorem rdot_zeros {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) :
    ∀ (l : List ℚ) (x : Vec) (d : ℕ → ℝ) (j : ℕ) (acc : ℝ), (∀ a ∈ l, a = 0) → fl acc = acc →
      rdot fl l x d j acc = acc := by
  intro l
  induction l with
  | nil => intro x d j acc _ _; cases x <;> simp [rdot]
  | cons a t ih =>
    intro x d j acc h hacc
    cases x with
    | nil => simp [rdot]
    | cons v xs =>
      have ha : a = 0 := h a (by simp)
      subst ha
      simp only [rdot, sw_zero hr, zero_mul, hr.zero, add_zero, hacc]
      exact ih xs d (j + 1) acc (fun b hb => h b (List.mem_cons_of_mem _ hb)) hacc

theorem z20_zero : ∀ a ∈ z20, a = 0 := by
  intro a ha
  simp [z20] at ha
  exact ha

theorem sc0_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 qi qn b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 qj qn' : ℝ)
    (hI : fl (fl (sw fl 20 (dA 17 18) * qj)) = fl (sw fl 20 (dA 17 18) * qj)) :
    hd0.score fl dA (vec20 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 1 qi qn) (vec20 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 1 qj qn')
      = fl (sw fl 20 (dA 17 18) * qj) := by
  simp [Head.score, hd0, z20, rS, vec20, pdot, rmat, rdot, sw_zero hr, hr.zero, hI]

theorem v0_eq0 {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (d : ℕ → ℝ)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 qj qn' : ℝ)
    (hI : fl (fl (sw fl 1 (d 0) * b0)) = fl (sw fl 1 (d 0) * b0)) :
    rdot fl u0 (vec20 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 1 qj qn') d 0 0 = fl (sw fl 1 (d 0) * b0) := by
  simp [u0, vec20, rdot, sw_zero hr, hr.zero, hI]

theorem v0_eq1 {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (d : ℕ → ℝ)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 qj qn' : ℝ)
    (hI : fl (fl (sw fl 1 (d 1) * b1)) = fl (sw fl 1 (d 1) * b1)) :
    rdot fl u1 (vec20 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 1 qj qn') d 0 0 = fl (sw fl 1 (d 1) * b1) := by
  simp [u1, vec20, rdot, sw_zero hr, hr.zero, hI]

theorem v0_eq2 {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (d : ℕ → ℝ)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 qj qn' : ℝ)
    (hI : fl (fl (sw fl 1 (d 2) * b2)) = fl (sw fl 1 (d 2) * b2)) :
    rdot fl u2 (vec20 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 1 qj qn') d 0 0 = fl (sw fl 1 (d 2) * b2) := by
  simp [u2, vec20, rdot, sw_zero hr, hr.zero, hI]

noncomputable def Pf (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (row : List ℚ) (r i : ℕ) : ℝ :=
  savg fl ex (cand Mask.strict (w.length + 1) i) (hscore hd0 fl (p.A 0 0) (net.init fl p w) i)
    (fun j => rdot fl row (net.init fl p w j) (p.V 0 0 r) 0 0)

theorem attn0_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (i : ℕ) :
    sattn hd0 fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = vec20 0 0 0 0 (Pf fl ex p w u0 4 i) (Pf fl ex p w u1 5 i) (Pf fl ex p w u2 6 i)
          0 0 0 0 0 0 0 0 0 0 0 0 0 := by
  have hz : ∀ d : ℕ → ℝ,
      savg fl ex (cand Mask.strict (w.length + 1) i)
        (hscore hd0 fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl z20 (net.init fl p w j) d 0 0) = 0 := by
    intro d
    apply soft_zeros hr
    intro k _
    exact rdot_zeros hr z20 _ d 0 0 z20_zero hr.zero
  have hV : hd0.V = [z20, z20, z20, z20, u0, u1, u2, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20, z20] := rfl
  have hm : hd0.mask = Mask.strict := rfl
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz, Pf, vec20]

theorem Xbd {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {Sw : ℝ}
    (hS : 198 / 10 ≤ Sw ∧ Sw ≤ 202 / 10) {a : ℕ} (ha : a ≤ n) :
    0 ≤ Sw * fl (a : ℝ) ∧ Sw * fl (a : ℝ) ≤ 21 * (n : ℝ) := by
  obtain ⟨h0, h1⟩ := E.hr.pos_le E.hu0 E.hη ha E.hn E.nM
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast E.hn1
  refine ⟨mul_nonneg (by linarith [hS.1]) h0, ?_⟩
  have := mul_le_mul hS.2 h1 h0 (by norm_num)
  linarith

theorem slope_gap {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {Sw : ℝ}
    (hS : 198 / 10 ≤ Sw ∧ Sw ≤ 202 / 10) {a b : ℕ} (hab : a < b) (hbn : b ≤ n) :
    fl (Sw * fl (a : ℝ)) + 16 * ((b : ℝ) - a) ≤ fl (Sw * fl (b : ℝ)) := by
  have han : a ≤ n := le_trans (le_of_lt hab) hbn
  obtain ⟨ha0, ha1⟩ := Xbd E hS han
  obtain ⟨hb0, hb1⟩ := Xbd E hS hbn
  have hpg := E.hr.pos_gap E.hu0 E.hη (le_of_lt hab) hbn E.hn E.nM
  have hd1 : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
  have h21 : 21 * (n : ℝ) ≤ M := E.lin (by norm_num) (by norm_num)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast E.hn1
  have hnn : (0 : ℝ) ≤ n := by linarith
  have hga := E.hr.gap E.hu0 (a := Sw * fl (a : ℝ)) (b := Sw * fl (b : ℝ)) (B := 21 * (n : ℝ))
    (abs_le.mpr ⟨by linarith, ha1⟩) (abs_le.mpr ⟨by linarith, hb1⟩) h21
  have hfd : (b : ℝ) - a - 1 / 100 ≤ fl (b : ℝ) - fl (a : ℝ) := by linarith
  have key : 198 / 10 * ((b : ℝ) - a - 1 / 100) ≤ Sw * (fl (b : ℝ) - fl (a : ℝ)) :=
    mul_le_mul hS.1 hfd (by linarith) (by linarith [hS.1])
  have e : Sw * fl (b : ℝ) - Sw * fl (a : ℝ) = Sw * (fl (b : ℝ) - fl (a : ℝ)) := by ring
  have hun : u * (21 * (n : ℝ)) = 21 * (u * n) := by ring
  have hη := eta_tiny E.hη
  have hn' := E.hn
  nlinarith [hga, key, e, hun, hη, hn', hd1]

theorem l1_gen {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {Sw : ℝ}
    (hS : 198 / 10 ≤ Sw ∧ Sw ≤ 202 / 10) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n)
    (s f : ℕ → ℝ) (hs : ∀ j, j < k → s j = fl (Sw * fl (j : ℝ)))
    (hf : ∀ j, j < k → |f j| ≤ 11 / 10) :
    |savg fl ex (cand Mask.strict n k) s f - f (k - 1)| ≤ 11 / 10 / 100 + 1 / 2 ^ 90 ∧
      fl (savg fl ex (cand Mask.strict n k) s f) = savg fl ex (cand Mask.strict n k) s f := by
  have hj : k - 1 ∈ cand Mask.strict n k := by
    rw [Lane4.Seq.mem_cand_strict]; omega
  have hlen : (cand Mask.strict n k).length ≤ n := by
    simp [cand]; omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast E.hn1
  have h21 : 21 * (n : ℝ) ≤ M := E.lin (by norm_num) (by norm_num)
  have hun : u * (21 * (n : ℝ)) = 21 * (u * n) := by ring
  have hη := eta_tiny E.hη
  have hgap : ∀ j ∈ cand Mask.strict n k, j ≠ k - 1 →
      s j ≤ s (k - 1) - 16 * (ndist (k - 1) j : ℝ) := by
    intro j hj' hne
    rw [Lane4.Seq.mem_cand_strict] at hj'
    have hlt : j < k - 1 := by omega
    rw [hs j hj', hs (k - 1) (by omega), ndist_cast]
    have := slope_gap E hS hlt (show k - 1 ≤ n by omega)
    have hc : (j : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hlt.le
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hSb : ∀ j ∈ cand Mask.strict n k, |s j| ≤ 22 * (n : ℝ) := by
    intro j hj'
    rw [Lane4.Seq.mem_cand_strict] at hj'
    rw [hs j hj']
    obtain ⟨h0, h1⟩ := Xbd E hS (show j ≤ n by omega)
    have := E.hr.bound E.hu0 (abs_le.mpr ⟨by linarith, h1⟩ : |Sw * fl (j : ℝ)| ≤ 21 * (n : ℝ)) h21
    have hn' := E.hn
    linarith
  have hfB : ∀ j ∈ cand Mask.strict n k, |f j| ≤ 11 / 10 := by
    intro j hj'
    rw [Lane4.Seq.mem_cand_strict] at hj'
    exact hf j hj'
  exact soft_near E.hr E.he E.hu0 E.hu1 E.hη0 E.hη (Lane4.Seq.cand_nodup _ _ _) hlen E.hn E.hnη
    hj hgap hSb (by have := E.lin (c := 44) (by norm_num) (by norm_num); linarith) hfB
    (by have := E.big (c := 8.4) (by norm_num); linarith)



theorem pmul_bounds {a b a0 a1 b0 b1 : ℝ} (hb0 : 0 ≤ b0) (hb : 0 ≤ a0) (h1 : a0 ≤ a) (h2 : a ≤ a1)
    (h3 : b0 ≤ b) (h4 : b ≤ b1) : a0 * b0 ≤ a * b ∧ a * b ≤ a1 * b1 :=
  ⟨mul_le_mul h1 h3 hb0 (by linarith), mul_le_mul h2 h4 (by linarith) (by linarith)⟩

theorem relu_abs (a : ℝ) : |relu a| ≤ |a| := by
  unfold relu
  rcases le_total a 0 with h | h
  · rw [max_eq_right h]; simp
  · rw [max_eq_left h]

theorem ab_mul {a b : ℝ} (ha : |a| ≤ 10) (hb : |b| ≤ 10) : |a * b| ≤ 100 := by
  rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg b]

noncomputable def mU (fl : ℝ → ℝ) (w1 b w2 p : ℝ) : ℝ :=
  fl (w2 * relu (fl (fl (w1 * p) + b)))

noncomputable def gU (fl : ℝ → ℝ) (wh wp bg w2 hv p : ℝ) : ℝ :=
  fl (w2 * relu (fl (fl (fl (wh * hv) + fl (wp * p)) + bg)))

theorem mU_spec {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n) {w1 b w2 p : ℝ}
    (hw1 : -1006 / 1000 ≤ w1 ∧ w1 ≤ -994 / 1000) (hb : 894 / 1000 ≤ b ∧ b ≤ 906 / 1000)
    (hw2 : 994 / 1000 ≤ w2 ∧ w2 ≤ 1006 / 1000) (hp : -3 / 250 ≤ p ∧ p ≤ 103 / 100) :
    fl (mU fl w1 b w2 p) = mU fl w1 b w2 p ∧ (97 / 100 ≤ p → mU fl w1 b w2 p = 0) ∧
      (p ≤ 3 / 250 → 87 / 100 ≤ mU fl w1 b w2 p ∧ mU fl w1 b w2 p ≤ 93 / 100) := by
  have hwp : |w1 * p| ≤ 100 := by
    apply ab_mul <;> apply abs_le.mpr <;> constructor <;> linarith
  have he1 := E.e5 hwp
  obtain ⟨hwl, hwu⟩ := abs_le.mp (show |w1 * p| ≤ 3 by
    rw [abs_mul]
    have h1 : |w1| ≤ 11 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |p| ≤ 11 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg w1, abs_nonneg p])
  obtain ⟨he1l, he1u⟩ := abs_le.mp he1
  have hq : |fl (w1 * p) + b| ≤ 100 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hpre := E.e5 hq
  obtain ⟨hpl, hpu⟩ := abs_le.mp hpre
  have hprea : |fl (fl (w1 * p) + b)| ≤ 100 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hrelu := relu_abs (fl (fl (w1 * p) + b))
  have hx : |w2 * relu (fl (fl (w1 * p) + b))| ≤ 100 := by
    apply ab_mul
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
    · have : |fl (fl (w1 * p) + b)| ≤ 5 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
  refine ⟨E.idem hx, ?_, ?_⟩
  · intro hp1
    have hm := mul_le_mul_of_nonneg_right (show 994 / 1000 ≤ -w1 by linarith) (by linarith : (0 : ℝ) ≤ p)
    have hneg : fl (fl (w1 * p) + b) ≤ 0 := by nlinarith
    unfold mU
    rw [relu_of_nonpos hneg]
    simp [E.hr.zero]
  · intro hp1
    have h1 : |w1 * p| ≤ 1007 / 1000 * (3 / 250) := by
      rw [abs_mul]
      have h1 : |w1| ≤ 1006 / 1000 := abs_le.mpr ⟨by linarith, by linarith⟩
      have h2 : |p| ≤ 3 / 250 := abs_le.mpr ⟨by linarith, by linarith⟩
      nlinarith [abs_nonneg w1, abs_nonneg p]
    obtain ⟨h1l, h1u⟩ := abs_le.mp h1
    have hpos : 0 ≤ fl (fl (w1 * p) + b) := by linarith
    have hrl : relu (fl (fl (w1 * p) + b)) = fl (fl (w1 * p) + b) := relu_of_nonneg hpos
    have hxx : |w2 * fl (fl (w1 * p) + b)| ≤ 100 := by rw [← hrl]; exact hx
    have he2 := E.e5 hxx
    obtain ⟨he2l, he2u⟩ := abs_le.mp he2
    unfold mU
    rw [hrl]
    have hlo := mul_le_mul_of_nonneg_right (show 994 / 1000 ≤ w2 by linarith) hpos
    have hhi := mul_le_mul_of_nonneg_right (show w2 ≤ 1006 / 1000 by linarith) hpos
    constructor <;> nlinarith

theorem gU_spec {u η M : ℝ} {fl ex : ℝ → ℝ} {n : ℕ} (E : Env u η M fl ex n)
    {wh wp bg w2 hv p : ℝ}
    (hwh : 994 / 1000 ≤ wh ∧ wh ≤ 1006 / 1000) (hwp : 994 / 1000 ≤ wp ∧ wp ≤ 1006 / 1000)
    (hbg : -1106 / 1000 ≤ bg ∧ bg ≤ -1094 / 1000)
    (hw2 : 994 / 1000 ≤ w2 ∧ w2 ≤ 1006 / 1000) (hhv : hv = 0 ∨ (994 / 1000 ≤ hv ∧ hv ≤ 1006 / 1000))
    (hp : -3 / 250 ≤ p ∧ p ≤ 103 / 100) :
    fl (gU fl wh wp bg w2 hv p) = gU fl wh wp bg w2 hv p ∧ 0 ≤ gU fl wh wp bg w2 hv p ∧
      gU fl wh wp bg w2 hv p ≤ 97 / 100 ∧ (p ≤ 3 / 250 → gU fl wh wp bg w2 hv p = 0) ∧
      (hv = 0 → gU fl wh wp bg w2 hv p = 0) ∧
      (97 / 100 ≤ p → 994 / 1000 ≤ hv → 83 / 100 ≤ gU fl wh wp bg w2 hv p) := by
  have hhv' : 0 ≤ hv ∧ hv ≤ 1006 / 1000 := by
    rcases hhv with h | h
    · rw [h]; constructor <;> norm_num
    · constructor <;> linarith [h.1, h.2]
  have ht1 : |wh * hv| ≤ 100 := by
    apply ab_mul <;> apply abs_le.mpr <;> constructor <;> linarith
  have ht2 : |wp * p| ≤ 100 := by
    apply ab_mul <;> apply abs_le.mpr <;> constructor <;> linarith
  have hb1 := E.e5 ht1
  have hb2 := E.e5 ht2
  obtain ⟨hb1l, hb1u⟩ := abs_le.mp hb1
  obtain ⟨hb2l, hb2u⟩ := abs_le.mp hb2
  have ht1u : wh * hv ≤ 1006 / 1000 * (1006 / 1000) :=
    (pmul_bounds (by norm_num) (by norm_num) hwh.1 hwh.2 (show (0:ℝ) ≤ hv by linarith) hhv'.2).2
  have ht1l : 0 ≤ wh * hv := mul_nonneg (by linarith) hhv'.1
  have ht2u : wp * p ≤ 1006 / 1000 * (103 / 100) := by
    rcases le_total p 0 with h | h
    · nlinarith
    · exact (pmul_bounds (by norm_num) (by norm_num) hwp.1 hwp.2 h hp.2).2
  have ht2l : -(1006 / 1000 * (3 / 250)) ≤ wp * p := by nlinarith
  have hs : |fl (wh * hv) + fl (wp * p)| ≤ 100 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hs1 := E.e5 hs
  obtain ⟨hs1l, hs1u⟩ := abs_le.mp hs1
  have hq : |fl (fl (wh * hv) + fl (wp * p)) + bg| ≤ 100 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hq1 := E.e5 hq
  obtain ⟨hq1l, hq1u⟩ := abs_le.mp hq1
  have hpre_u : fl (fl (fl (wh * hv) + fl (wp * p)) + bg) ≤ 955 / 1000 := by linarith
  have hrelu_u : relu (fl (fl (fl (wh * hv) + fl (wp * p)) + bg)) ≤ 955 / 1000 := by
    unfold relu; exact max_le hpre_u (by norm_num)
  have hrelu_0 : 0 ≤ relu (fl (fl (fl (wh * hv) + fl (wp * p)) + bg)) := le_max_right _ _
  have hxu : w2 * relu (fl (fl (fl (wh * hv) + fl (wp * p)) + bg)) ≤ 1006 / 1000 * (955 / 1000) :=
    (pmul_bounds (by norm_num) (by norm_num) hw2.1 hw2.2 hrelu_0 hrelu_u).2
  have hx0 : 0 ≤ w2 * relu (fl (fl (fl (wh * hv) + fl (wp * p)) + bg)) :=
    mul_nonneg (by linarith) hrelu_0
  have hx : |w2 * relu (fl (fl (fl (wh * hv) + fl (wp * p)) + bg))| ≤ 100 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have he := E.e5 hx
  obtain ⟨hel, heu⟩ := abs_le.mp he
  have hz0 : fl (fl (fl (wh * hv) + fl (wp * p)) + bg) ≤ 0 →
      gU fl wh wp bg w2 hv p = 0 := by
    intro h
    unfold gU
    rw [relu_of_nonpos h]
    simp [E.hr.zero]
  refine ⟨E.idem hx, ?_, ?_, ?_, ?_, ?_⟩
  · unfold gU
    exact E.hr.nonneg hx0 (le_trans (by linarith) (E.big (c := 100) (by norm_num)))
  · unfold gU; linarith
  · intro hp1
    apply hz0
    linarith
  · intro h0
    apply hz0
    subst h0
    have : wh * (0 : ℝ) = 0 := by ring
    rw [this, E.hr.zero] at hs1u hs1l
    rw [this, E.hr.zero]
    linarith
  · intro hp1 hh
    have ht1l' : 994 / 1000 * (994 / 1000) ≤ wh * hv :=
      (pmul_bounds (by norm_num) (by norm_num) hwh.1 hwh.2 hh hhv'.2).1
    have ht2l' : 994 / 1000 * (97 / 100) ≤ wp * p :=
      (pmul_bounds (by norm_num) (by norm_num) hwp.1 hwp.2 hp1 hp.2).1
    have hpre_l : 846 / 1000 ≤ fl (fl (fl (wh * hv) + fl (wp * p)) + bg) := by linarith
    have hrl : relu (fl (fl (fl (wh * hv) + fl (wp * p)) + bg)) =
        fl (fl (fl (wh * hv) + fl (wp * p)) + bg) := relu_of_nonneg (by linarith)
    have hxl : 994 / 1000 * (846 / 1000) ≤ w2 * relu (fl (fl (fl (wh * hv) + fl (wp * p)) + bg)) := by
      rw [hrl]
      exact (pmul_bounds (by norm_num) (by norm_num) hw2.1 hw2.2 hpre_l (by linarith)).1
    unfold gU
    linarith

end Lane4.Case
