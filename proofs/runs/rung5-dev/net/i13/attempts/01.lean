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
  rw [hx] at h
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

end Lane4.Case
