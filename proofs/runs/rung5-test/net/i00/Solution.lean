namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option maxHeartbeats 2000000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

def z14 : List ℚ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def r17 : List ℚ := [0,0,0,0,0,0,0,0,0,0,0,0,17,0]
def r64 : List ℚ := [0,0,0,0,0,0,0,0,0,0,0,0,64,0]
def rBa : List ℚ := [0,0,0,512,0,0,1024,0,0,0,0,0,0,0]
def rBb : List ℚ := [0,0,0,512,0,0,0,1024,0,0,0,0,0,0]
def e0r : List ℚ := [1,0,0,0,0,0,0,0,0,0,0,0,0,0]
def e1r : List ℚ := [0,1,0,0,0,0,0,0,0,0,0,0,0,0]
def hvr : List ℚ := [0,0,1,0,0,0,0,0,0,0,0,0,0,0]
def g1r : List ℚ := [3,0,0,0,0,0,0,0,1,0,0,0,0,0]
def g2r : List ℚ := [0,3,0,0,0,0,0,0,0,1,0,0,0,0]
def m1r : List ℚ := [0,0,0,0,-4,0,0,0,0,0,0,0,0,0]
def m2r : List ℚ := [0,0,0,0,0,-4,0,0,0,0,0,0,0,0]
def w2z : List ℚ := [0,0]

def hd1 : Head :=
  { A := [z14,z14,z14,z14,z14,z14,z14,z14,z14,z14,z14,r17,z14,z14],
    V := [z14,z14,z14,z14,e0r,e1r,z14,z14,z14,z14,z14,z14,z14,z14],
    mask := Mask.strict }

def hd2a : Head :=
  { A := [z14,z14,z14,z14,z14,z14,z14,z14,z14,z14,z14,r64,z14,rBa],
    V := [z14,z14,z14,z14,z14,z14,z14,z14,hvr,z14,z14,z14,z14,z14],
    mask := Mask.causal }

def hd2b : Head :=
  { A := [z14,z14,z14,z14,z14,z14,z14,z14,z14,z14,z14,r64,z14,rBb],
    V := [z14,z14,z14,z14,z14,z14,z14,z14,z14,hvr,z14,z14,z14,z14],
    mask := Mask.causal }

def blk1 : Block :=
  { heads := [hd1], W1 := [m1r, m2r], b1 := [1, 1],
    W2 := [w2z,w2z,w2z,w2z,w2z,w2z,[-1,0],[0,-1],w2z,w2z,w2z,w2z,w2z,w2z],
    b2 := [0,0,0,0,0,0,1,1,0,0,0,0,0,0] }

def blk2 : Block :=
  { heads := [hd2a, hd2b], W1 := [g1r, g2r], b1 := [-3, -3],
    W2 := [w2z,w2z,w2z,w2z,w2z,w2z,w2z,w2z,w2z,w2z,[1,1],w2z,w2z,w2z],
    b2 := z14 }

def net : TNet :=
  { embed := [[0,0,0,1,0,0,0,0,0,0,0],[1,0,2,0,0,0,0,0,0,0,0],[0,1,1,0,0,0,0,0,0,0,0]],
    blocks := [blk1, blk2],
    outW := [0,0,0,0,0,0,0,0,0,0,1,0,0,0],
    outB := 0 }

/-- The facts handed to the theorem, bundled. -/
structure Ctx (u η M : ℝ) (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) : Prop where
  hr : Rnd u η M fl
  he : ExpM u η ex
  hu0 : 0 ≤ u
  hu1 : u ≤ 1 / 2 ^ 24
  hη0 : 0 ≤ η
  hη : η ≤ 1 / 2 ^ 149
  hp : p.Within (1 / 200)
  hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2
  hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256
  hnη : η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100
  hM : 2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M
  hl : 1 ≤ w.length

section
variable {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ}

theorem Ctx.n1 (C : Ctx u η M fl ex p w) : 1 ≤ w.length + 1 := by
  have := C.hl; omega

theorem Ctx.nR (C : Ctx u η M fl ex p w) : (2 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
  have h2 : 2 ≤ w.length + 1 := by have := C.hl; omega
  exact_mod_cast h2

theorem Ctx.lin (C : Ctx u η M fl ex p w) (c : ℝ) (h0 : 0 ≤ c) (h : c ≤ 2 ^ 40) :
    c * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin C.hM C.n1 h0 h

theorem Ctx.cst (C : Ctx u η M fl ex p w) (c : ℝ) (h : c ≤ 2 ^ 40) : c ≤ M :=
  range_const C.hM C.n1 h

theorem Ctx.nM (C : Ctx u η M fl ex p w) : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
  have := C.lin 1 (by norm_num) (by norm_num)
  linarith

theorem Ctx.etaS (C : Ctx u η M fl ex p w) : η ≤ 1 / 100000 := by
  have h1 := eta_tiny C.hη
  have h2 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  linarith

theorem Ctx.u24 (C : Ctx u η M fl ex p w) : u ≤ 1 / 1000000 := by
  have h1 := C.hu1
  have h2 : (1 : ℝ) / 2 ^ 24 ≤ 1 / 1000000 := by norm_num
  linarith

theorem Ctx.pos_b (C : Ctx u η M fl ex p w) {k : ℕ} (hk : k ≤ w.length + 1) :
    0 ≤ fl (k : ℝ) ∧ fl (k : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) + 1 / 100 :=
  C.hr.pos_le C.hu0 C.hη hk C.hn C.nM

theorem Ctx.pos_n (C : Ctx u η M fl ex p w) {k : ℕ} (hk : k ≤ w.length + 1) :
    |fl (k : ℝ) - k| ≤ 1 / 200 :=
  C.hr.pos_near C.hu0 C.hη hk C.hn C.nM

theorem Ctx.pos_g (C : Ctx u η M fl ex p w) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ w.length + 1) :
    fl (a : ℝ) + ((b : ℝ) - a) - 1 / 100 ≤ fl (b : ℝ) :=
  C.hr.pos_gap C.hu0 C.hη hab hb C.hn C.nM

/-- Box for a stored weight. -/
theorem Ctx.swb (C : Ctx u η M fl ex p w) (q : ℚ) (x a : ℝ) (hx : (q : ℝ) = x)
    (ha : |x| ≤ a) (ha2 : a ≤ 2048) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    |sw fl q d - x| ≤ a / 199 + η := by
  have h24 := C.u24
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by linarith
  have hM2 : 2 * |(q : ℝ)| ≤ M := by
    have := C.cst 4096 (by norm_num)
    rw [hx]; linarith
  have h := sw_near C.hr C.hu0 q hd (by norm_num) hM2 hε
  rw [hx] at h
  have : 1 / 199 * |x| ≤ a / 199 := by linarith
  linarith

/-- A stored weight is fixed by rounding. -/
theorem Ctx.flsw (C : Ctx u η M fl ex p w) (q : ℚ) (x : ℝ) (hx : (q : ℝ) = x)
    (ha : |x| ≤ 2048) {d : ℝ} (hd : |d| ≤ 1 / 200) : fl (sw fl q d) = sw fl q d := by
  apply fl_sw C.hr q hd (by norm_num)
  have := C.cst 4096 (by norm_num)
  rw [hx]; linarith

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (j : ℕ) : tokAt w j ≤ 2 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h0 | h0
  · omega
  · exact (hw _ h0).2

theorem tok_pos (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) {k : ℕ} (h1 : 1 ≤ k)
    (h2 : k ≤ w.length) : 1 ≤ tokAt w k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Lane4.Seq.tokAt_succ w k' (by omega)]
  exact (hw _ (List.getElem_mem (by omega))).1

noncomputable def ev1 (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (if tokAt w j = 1 then 1 else 0) (p.E (tokAt w j) 0)
noncomputable def ev2 (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (if tokAt w j = 2 then 1 else 0) (p.E (tokAt w j) 1)
noncomputable def evh (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (if tokAt w j = 1 then 2 else if tokAt w j = 2 then 1 else 0) (p.E (tokAt w j) 2)
noncomputable def evb (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (if tokAt w j = 0 then 1 else 0) (p.E (tokAt w j) 3)

theorem init_eq (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (j : ℕ) :
    net.init fl p w j = [ev1 fl p w j, ev2 fl p w j, evh fl p w j, evb fl p w j,
      0, 0, 0, 0, 0, 0, 0] ++ pos fl j (w.length + 1) := by
  have h3 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 := by
    have := tok_le w hw j
    omega
  rcases h3 with h3 | h3 | h3 <;>
    simp [TNet.init, net, ev1, ev2, evh, evb, swRow, h3, sw_zero hr]

theorem rdot_zeros (hr : Rnd u η M fl) : ∀ (row : List ℚ), (∀ a ∈ row, a = 0) →
    ∀ (v : Vec) (d : ℕ → ℝ) (j : ℕ), rdot fl row v d j 0 = 0 := by
  intro row
  induction row with
  | nil => intro _ v d j; cases v <;> simp [rdot]
  | cons a t ih =>
    intro hz v d j
    have ha : a = 0 := hz a (by simp)
    cases v with
    | nil => simp [rdot]
    | cons x xs =>
      have e : fl (0 + fl (sw fl a (d j) * x)) = 0 := by
        rw [ha, sw_zero hr, zero_mul, hr.zero, add_zero, hr.zero]
      simp only [rdot]
      rw [e]
      exact ih (fun b hb => hz b (List.mem_cons_of_mem _ hb)) xs d (j + 1)

theorem z14_zero : ∀ a ∈ z14, a = 0 := by
  intro a ha
  simp [z14] at ha
  exact ha

/-! ### closed forms of scores and values -/

theorem score1_eq {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 qi qn b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 qk qn' : ℝ}
    (hr : Rnd u η M fl) {dA : ℕ → ℕ → ℝ}
    (hI : fl (fl (sw fl 17 (dA 11 12) * qk)) = fl (sw fl 17 (dA 11 12) * qk)) :
    hd1.score fl dA [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,1,qi,qn]
      [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,1,qk,qn'] = fl (sw fl 17 (dA 11 12) * qk) := by
  simp [Head.score, hd1, z14, r17, pdot, rmat, rdot, sw_zero hr, hr.zero, hI]

theorem score2a_eq {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 qi qn b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 qk qn' : ℝ}
    (hr : Rnd u η M fl) {dA : ℕ → ℕ → ℝ}
    (hT : fl (fl (sw fl 64 (dA 11 12) * qk)) = fl (sw fl 64 (dA 11 12) * qk))
    (hD1 : fl (fl (sw fl 512 (dA 13 3) * b3)) = fl (sw fl 512 (dA 13 3) * b3))
    (hD : fl (fl (fl (sw fl 512 (dA 13 3) * b3) + fl (sw fl 1024 (dA 13 6) * b6)))
      = fl (fl (sw fl 512 (dA 13 3) * b3) + fl (sw fl 1024 (dA 13 6) * b6))) :
    hd2a.score fl dA [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,1,qi,qn]
      [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,1,qk,qn']
    = fl (fl (sw fl 64 (dA 11 12) * qk) + fl (qn * fl (fl (sw fl 512 (dA 13 3) * b3)
        + fl (sw fl 1024 (dA 13 6) * b6)))) := by
  simp [Head.score, hd2a, z14, r64, rBa, pdot, rmat, rdot, sw_zero hr, hr.zero, hT, hD1, hD]

theorem score2b_eq {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 qi qn b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 qk qn' : ℝ}
    (hr : Rnd u η M fl) {dA : ℕ → ℕ → ℝ}
    (hT : fl (fl (sw fl 64 (dA 11 12) * qk)) = fl (sw fl 64 (dA 11 12) * qk))
    (hD1 : fl (fl (sw fl 512 (dA 13 3) * b3)) = fl (sw fl 512 (dA 13 3) * b3))
    (hD : fl (fl (fl (sw fl 512 (dA 13 3) * b3) + fl (sw fl 1024 (dA 13 7) * b7)))
      = fl (fl (sw fl 512 (dA 13 3) * b3) + fl (sw fl 1024 (dA 13 7) * b7))) :
    hd2b.score fl dA [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,1,qi,qn]
      [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,1,qk,qn']
    = fl (fl (sw fl 64 (dA 11 12) * qk) + fl (qn * fl (fl (sw fl 512 (dA 13 3) * b3)
        + fl (sw fl 1024 (dA 13 7) * b7)))) := by
  simp [Head.score, hd2b, z14, r64, rBb, pdot, rmat, rdot, sw_zero hr, hr.zero, hT, hD1, hD]

theorem val0_eq {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 qk qn : ℝ} (hr : Rnd u η M fl) {dv : ℕ → ℝ}
    (hI : fl (fl (sw fl 1 (dv 0) * b0)) = fl (sw fl 1 (dv 0) * b0)) :
    rdot fl e0r [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,1,qk,qn] dv 0 0 = fl (sw fl 1 (dv 0) * b0) := by
  simp [e0r, rdot, sw_zero hr, hr.zero, hI]

theorem val1_eq {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 qk qn : ℝ} (hr : Rnd u η M fl) {dv : ℕ → ℝ}
    (hI : fl (fl (sw fl 1 (dv 1) * b1)) = fl (sw fl 1 (dv 1) * b1)) :
    rdot fl e1r [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,1,qk,qn] dv 0 0 = fl (sw fl 1 (dv 1) * b1) := by
  simp [e1r, rdot, sw_zero hr, hr.zero, hI]

theorem valh_eq {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 qk qn : ℝ} (hr : Rnd u η M fl) {dv : ℕ → ℝ}
    (hI : fl (fl (sw fl 1 (dv 2) * b2)) = fl (sw fl 1 (dv 2) * b2)) :
    rdot fl hvr [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,1,qk,qn] dv 0 0 = fl (sw fl 1 (dv 2) * b2) := by
  simp [hvr, rdot, sw_zero hr, hr.zero, hI]

theorem absmul2 {x y a b : ℝ} (hx : |x| ≤ a) (hy : |y| ≤ b) : |x * y| ≤ a * b := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) (le_trans (abs_nonneg _) hx)

/-! ### embedding entries -/

theorem ev1_one (C : Ctx u η M fl ex p w) (j : ℕ) (hj : tokAt w j = 1) :
    |ev1 fl p w j - 1| ≤ 52 / 10000 := by
  unfold ev1
  rw [if_pos hj, hj]
  have h1 := C.swb 1 1 1 (by norm_num) (by norm_num) (by norm_num) (C.hp.E 1 0)
  have := C.etaS
  linarith

theorem ev1_non (C : Ctx u η M fl ex p w) (j : ℕ) (hj : tokAt w j ≠ 1) : ev1 fl p w j = 0 := by
  unfold ev1
  rw [if_neg hj]
  exact sw_zero C.hr _

theorem ev1_b (C : Ctx u η M fl ex p w) (j : ℕ) : |ev1 fl p w j| ≤ 10052 / 10000 := by
  by_cases hj : tokAt w j = 1
  · have := ev1_one C j hj
    obtain ⟨h2a, h2b⟩ := abs_le.mp this
    rw [abs_le]; constructor <;> linarith
  · rw [ev1_non C j hj]; norm_num

theorem ev2_one (C : Ctx u η M fl ex p w) (j : ℕ) (hj : tokAt w j = 2) :
    |ev2 fl p w j - 1| ≤ 52 / 10000 := by
  unfold ev2
  rw [if_pos hj, hj]
  have h1 := C.swb 1 1 1 (by norm_num) (by norm_num) (by norm_num) (C.hp.E 2 1)
  have := C.etaS
  linarith

theorem ev2_non (C : Ctx u η M fl ex p w) (j : ℕ) (hj : tokAt w j ≠ 2) : ev2 fl p w j = 0 := by
  unfold ev2
  rw [if_neg hj]
  exact sw_zero C.hr _

theorem ev2_b (C : Ctx u η M fl ex p w) (j : ℕ) : |ev2 fl p w j| ≤ 10052 / 10000 := by
  by_cases hj : tokAt w j = 2
  · have := ev2_one C j hj
    obtain ⟨h2a, h2b⟩ := abs_le.mp this
    rw [abs_le]; constructor <;> linarith
  · rw [ev2_non C j hj]; norm_num

theorem evh_one (C : Ctx u η M fl ex p w) (j : ℕ) (hj : tokAt w j = 1) :
    |evh fl p w j - 2| ≤ 105 / 10000 := by
  unfold evh
  rw [if_pos hj, hj]
  have h1 := C.swb 2 2 2 (by norm_num) (by norm_num) (by norm_num) (C.hp.E 1 2)
  have := C.etaS
  linarith

theorem evh_two (C : Ctx u η M fl ex p w) (j : ℕ) (hj : tokAt w j = 2) :
    |evh fl p w j - 1| ≤ 52 / 10000 := by
  have hne : ¬ tokAt w j = 1 := by omega
  unfold evh
  rw [if_neg hne, if_pos hj, hj]
  have h1 := C.swb 1 1 1 (by norm_num) (by norm_num) (by norm_num) (C.hp.E 2 2)
  have := C.etaS
  linarith

theorem evh_b (C : Ctx u η M fl ex p w) (j : ℕ) (hj : tokAt w j ≤ 2) :
    |evh fl p w j| ≤ 2011 / 1000 := by
  by_cases h1 : tokAt w j = 1
  · obtain ⟨h2a, h2b⟩ := abs_le.mp (evh_one C j h1)
    rw [abs_le]; constructor <;> linarith
  · by_cases h2 : tokAt w j = 2
    · obtain ⟨h3a, h3b⟩ := abs_le.mp (evh_two C j h2)
      rw [abs_le]; constructor <;> linarith
    · have : evh fl p w j = 0 := by
        unfold evh
        rw [if_neg h1, if_neg h2]
        exact sw_zero C.hr _
      rw [this]; norm_num

theorem evb_zero (C : Ctx u η M fl ex p w) (j : ℕ) (hj : tokAt w j ≠ 0) : evb fl p w j = 0 := by
  unfold evb
  rw [if_neg hj]
  exact sw_zero C.hr _

theorem evb_one (C : Ctx u η M fl ex p w) (j : ℕ) (hj : tokAt w j = 0) :
    |evb fl p w j - 1| ≤ 52 / 10000 := by
  unfold evb
  rw [if_pos hj, hj]
  have h1 := C.swb 1 1 1 (by norm_num) (by norm_num) (by norm_num) (C.hp.E 0 3)
  have := C.etaS
  linarith

theorem evb_b (C : Ctx u η M fl ex p w) (j : ℕ) : |evb fl p w j| ≤ 10052 / 10000 := by
  by_cases hj : tokAt w j = 0
  · obtain ⟨h2a, h2b⟩ := abs_le.mp (evb_one C j hj)
    rw [abs_le]; constructor <;> linarith
  · rw [evb_zero C j hj]; norm_num

/-- Idempotence of the stored entries. -/
theorem fl_ev1 (C : Ctx u η M fl ex p w) (j : ℕ) : fl (ev1 fl p w j) = ev1 fl p w j := by
  by_cases hj : tokAt w j = 1
  · unfold ev1
    rw [if_pos hj, hj]
    exact C.flsw 1 1 (by norm_num) (by norm_num) (C.hp.E 1 0)
  · rw [ev1_non C j hj, C.hr.zero]

theorem fl_ev2 (C : Ctx u η M fl ex p w) (j : ℕ) : fl (ev2 fl p w j) = ev2 fl p w j := by
  by_cases hj : tokAt w j = 2
  · unfold ev2
    rw [if_pos hj, hj]
    exact C.flsw 1 1 (by norm_num) (by norm_num) (C.hp.E 2 1)
  · rw [ev2_non C j hj, C.hr.zero]

theorem fl_evh (C : Ctx u η M fl ex p w) (j : ℕ) (hj : tokAt w j ≤ 2) :
    fl (evh fl p w j) = evh fl p w j := by
  by_cases h1 : tokAt w j = 1
  · unfold evh
    rw [if_pos h1, h1]
    exact C.flsw 2 2 (by norm_num) (by norm_num) (C.hp.E 1 2)
  · by_cases h2 : tokAt w j = 2
    · unfold evh
      rw [if_neg h1, if_pos h2, h2]
      exact C.flsw 1 1 (by norm_num) (by norm_num) (C.hp.E 2 2)
    · have : evh fl p w j = 0 := by
        unfold evh
        rw [if_neg h1, if_neg h2]
        exact sw_zero C.hr _
      rw [this, C.hr.zero]

theorem fl_evb (C : Ctx u η M fl ex p w) (j : ℕ) : fl (evb fl p w j) = evb fl p w j := by
  by_cases hj : tokAt w j = 0
  · unfold evb
    rw [if_pos hj, hj]
    exact C.flsw 1 1 (by norm_num) (by norm_num) (C.hp.E 0 3)
  · rw [evb_zero C j hj, C.hr.zero]

/-! ### block 1: the previous-token head -/

noncomputable def Pa (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (r : List ℚ) (dv : ℕ → ℝ)
    (i : ℕ) : ℝ :=
  savg fl ex (cand Mask.strict (w.length + 1) i) (hscore hd1 fl (p.A 0 0) (net.init fl p w) i)
    (fun k => rdot fl r (net.init fl p w k) dv 0 0)

theorem attn1_eq (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) (i : ℕ) :
    sattn hd1 fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, 0, 0, Pa fl ex p w e0r (p.V 0 0 4) i, Pa fl ex p w e1r (p.V 0 0 5) i,
         0, 0, 0, 0, 0, 0, 0, 0] := by
  have hz : ∀ d : ℕ → ℝ,
      savg fl ex (cand Mask.strict (w.length + 1) i)
        (hscore hd1 fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl z14 (net.init fl p w j) d 0 0) = 0 := by
    intro d
    apply soft_zeros hr
    intro k _
    exact rdot_zeros hr z14 z14_zero _ d 0
  have hV : hd1.V = [z14,z14,z14,z14,e0r,e1r,z14,z14,z14,z14,z14,z14,z14,z14] := rfl
  have hm : hd1.mask = Mask.strict := rfl
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz, Pa]

theorem Pa_zero (hr : Rnd u η M fl) (p : Pert) (w : List ℕ) (r : List ℚ) (dv : ℕ → ℝ) :
    Pa fl ex p w r dv 0 = 0 := by
  simp [Pa, savg, rsum, cand, hr.zero]

theorem hPb1 (C : Ctx u η M fl ex p w) (k : ℕ) (hk : k ≤ w.length + 1) :
    |sw fl 17 (p.A 0 0 11 12) * fl (k : ℝ)| ≤ 18 * ((w.length + 1 : ℕ) : ℝ) := by
  have hS := C.swb 17 17 17 (by norm_num) (by norm_num) (by norm_num) (C.hp.A 0 0 11 12)
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  obtain ⟨hk0, hk1⟩ := C.pos_b hk
  have hη5 := C.etaS
  have hS0 : 0 ≤ sw fl 17 (p.A 0 0 11 12) := by linarith
  rw [abs_of_nonneg (mul_nonneg hS0 hk0)]
  have := mul_le_mul (show sw fl 17 (p.A 0 0 11 12) ≤ 171 / 10 by linarith) hk1 hk0 (by norm_num)
  have hnR := C.nR
  linarith

theorem hsk1 (C : Ctx u η M fl ex p w) (i k : ℕ) (hk : k ≤ w.length + 1) :
    hscore hd1 fl (p.A 0 0) (net.init fl p w) i k
      = fl (sw fl 17 (p.A 0 0 11 12) * fl (k : ℝ)) := by
  simp only [hscore, init_eq C.hr p w C.hw, pos, List.cons_append, List.nil_append]
  exact score1_eq C.hr
    (C.hr.idem _ (le_trans (hPb1 C k hk) (C.lin 18 (by norm_num) (by norm_num))))

theorem Pa_gen (C : Ctx u η M fl ex p w) (r : List ℚ) (dv : ℕ → ℝ)
    (hfb : ∀ k, k ≤ w.length → |rdot fl r (net.init fl p w k) dv 0 0| ≤ 11 / 10)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    |Pa fl ex p w r dv i - rdot fl r (net.init fl p w (i - 1)) dv 0 0| ≤ 11 / 1000 + 1 / 2 ^ 90 ∧
    fl (Pa fl ex p w r dv i) = Pa fl ex p w r dv i := by
  have hnR := C.nR
  have h18 := C.lin 18 (by norm_num) (by norm_num)
  have h38 := C.lin 38 (by norm_num) (by norm_num)
  have h40 := C.cst 40 (by norm_num)
  have hη5 := C.etaS
  have hS := C.swb 17 17 17 (by norm_num) (by norm_num) (by norm_num) (C.hp.A 0 0 11 12)
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  have hj : i - 1 ∈ cand Mask.strict (w.length + 1) i := by
    rw [Lane4.Seq.mem_cand_strict]; omega
  have hlen : (cand Mask.strict (w.length + 1) i).length ≤ w.length + 1 := by
    simp [cand]; omega
  have hgap : ∀ k ∈ cand Mask.strict (w.length + 1) i, k ≠ i - 1 →
      hscore hd1 fl (p.A 0 0) (net.init fl p w) i k
        ≤ hscore hd1 fl (p.A 0 0) (net.init fl p w) i (i - 1) - 16 * (ndist (i - 1) k : ℝ) := by
    intro k hk hne
    rw [Lane4.Seq.mem_cand_strict] at hk
    have hkj : k < i - 1 := by omega
    rw [hsk1 C i k (by omega), hsk1 C i (i - 1) (by omega), ndist_cast]
    have hg := C.pos_g (le_of_lt hkj) (show i - 1 ≤ w.length + 1 by omega)
    have hgp := C.hr.gap C.hu0 (hPb1 C k (by omega)) (hPb1 C (i - 1) (by omega)) h18
    have hd1' : ((k : ℝ)) + 1 ≤ ((i - 1 : ℕ) : ℝ) := by exact_mod_cast hkj
    rw [abs_of_nonneg (by linarith)]
    have hD0 : 0 ≤ fl ((i - 1 : ℕ) : ℝ) - fl (k : ℝ) := by linarith
    have hSD := mul_le_mul_of_nonneg_right
      (show (169 : ℝ) / 10 ≤ sw fl 17 (p.A 0 0 11 12) by linarith) hD0
    have hun : u * (18 * ((w.length + 1 : ℕ) : ℝ)) = 18 * (u * ((w.length + 1 : ℕ) : ℝ)) := by ring
    linarith [hgp, hSD, hg, hd1', C.hn, hη5, hun]
  have hSb : ∀ k ∈ cand Mask.strict (w.length + 1) i,
      |hscore hd1 fl (p.A 0 0) (net.init fl p w) i k| ≤ 18 * ((w.length + 1 : ℕ) : ℝ) + 1 := by
    intro k hk
    rw [Lane4.Seq.mem_cand_strict] at hk
    rw [hsk1 C i k (by omega)]
    have := C.hr.bound C.hu0 (hPb1 C k (by omega)) h18
    have hun : u * (18 * ((w.length + 1 : ℕ) : ℝ)) = 18 * (u * ((w.length + 1 : ℕ) : ℝ)) := by ring
    linarith [C.hn]
  have hfB : ∀ k ∈ cand Mask.strict (w.length + 1) i,
      |(fun j => rdot fl r (net.init fl p w j) dv 0 0) k| ≤ 11 / 10 := by
    intro k hk
    rw [Lane4.Seq.mem_cand_strict] at hk
    exact hfb k (by omega)
  obtain ⟨hA1, hA2⟩ := soft_near C.hr C.he C.hu0 C.hu1 C.hη0 C.hη (Lane4.Seq.cand_nodup _ _ _)
    hlen C.hn C.hnη hj hgap hSb (by linarith) hfB (by linarith)
  refine ⟨?_, hA2⟩
  have e : (11 / 10 : ℝ) / 100 + 1 / 2 ^ 90 = 11 / 1000 + 1 / 2 ^ 90 := by norm_num
  rw [e] at hA1
  exact hA1

theorem Pa_facts_gen (C : Ctx u η M fl ex p w) (r : List ℚ) (dv : ℕ → ℝ) (sv : ℝ) (e : ℕ → ℝ)
    (t : ℕ) (hsv : |sv - 1| ≤ 52 / 10000) (he : ∀ k, |e k| ≤ 10052 / 10000)
    (hnon : ∀ k, tokAt w k ≠ t → e k = 0) (hone : ∀ k, tokAt w k = t → |e k - 1| ≤ 52 / 10000)
    (hf : ∀ k, rdot fl r (net.init fl p w k) dv 0 0 = fl (sv * e k))
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    (tokAt w (i - 1) ≠ t → |Pa fl ex p w r dv i| ≤ 12 / 1000) ∧
    (tokAt w (i - 1) = t → |Pa fl ex p w r dv i - 1| ≤ 23 / 1000) ∧
    fl (Pa fl ex p w r dv i) = Pa fl ex p w r dv i := by
  have h4 := C.cst 4 (by norm_num)
  have hu6 := C.u24
  have hη5 := C.etaS
  have hsvb : |sv| ≤ 10052 / 10000 := by
    obtain ⟨hh1, hh2⟩ := abs_le.mp hsv
    rw [abs_le]; constructor <;> linarith
  have hx : ∀ k, |sv * e k| ≤ 102 / 100 := by
    intro k
    have := absmul2 hsvb (he k)
    linarith
  have hfb : ∀ k, k ≤ w.length → |rdot fl r (net.init fl p w k) dv 0 0| ≤ 11 / 10 := by
    intro k _
    rw [hf k]
    have := C.hr.bound C.hu0 (hx k) (by linarith)
    linarith
  obtain ⟨hA1, hA2⟩ := Pa_gen C r dv hfb i hi1 hi
  rw [hf (i - 1)] at hA1
  refine ⟨?_, ?_, hA2⟩
  · intro hne
    rw [hnon _ hne, mul_zero, C.hr.zero, sub_zero] at hA1
    have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 1000 := by norm_num
    linarith
  · intro heq
    have e1 : |sv * e (i - 1) - 1| ≤ 105 / 10000 := by
      have := mul_near hsv (hone _ heq)
      simp only [abs_one, mul_one] at this
      linarith
    have e2 := C.hr.near C.hu0 e1 (hx (i - 1)) (by linarith)
    have e3 := abs_sub_le (Pa fl ex p w r dv i) (fl (sv * e (i - 1))) 1
    have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 1000 := by norm_num
    linarith

theorem Pa1_facts (C : Ctx u η M fl ex p w) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    (tokAt w (i - 1) ≠ 1 → |Pa fl ex p w e0r (p.V 0 0 4) i| ≤ 12 / 1000) ∧
    (tokAt w (i - 1) = 1 → |Pa fl ex p w e0r (p.V 0 0 4) i - 1| ≤ 23 / 1000) ∧
    fl (Pa fl ex p w e0r (p.V 0 0 4) i) = Pa fl ex p w e0r (p.V 0 0 4) i := by
  have hV := C.swb 1 1 1 (by norm_num) (by norm_num) (by norm_num) (C.hp.V 0 0 4 0)
  have hη5 := C.etaS
  have hI : ∀ k, rdot fl e0r (net.init fl p w k) (p.V 0 0 4) 0 0
      = fl (sw fl 1 (p.V 0 0 4 0) * ev1 fl p w k) := by
    intro k
    rw [init_eq C.hr p w C.hw k]
    simp only [pos, List.cons_append, List.nil_append]
    have hsvb : |sw fl 1 (p.V 0 0 4 0)| ≤ 10052 / 10000 := by
      obtain ⟨hh1, hh2⟩ := abs_le.mp hV
      rw [abs_le]; constructor <;> linarith
    have := absmul2 hsvb (ev1_b C k)
    exact val0_eq C.hr (C.hr.idem _ (le_trans (by linarith) (C.cst 4 (by norm_num))))
  exact Pa_facts_gen C e0r (p.V 0 0 4) (sw fl 1 (p.V 0 0 4 0)) (fun k => ev1 fl p w k) 1 (by linarith) (ev1_b C)
    (ev1_non C) (ev1_one C) hI i hi1 hi

theorem Pa2_facts (C : Ctx u η M fl ex p w) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    (tokAt w (i - 1) ≠ 2 → |Pa fl ex p w e1r (p.V 0 0 5) i| ≤ 12 / 1000) ∧
    (tokAt w (i - 1) = 2 → |Pa fl ex p w e1r (p.V 0 0 5) i - 1| ≤ 23 / 1000) ∧
    fl (Pa fl ex p w e1r (p.V 0 0 5) i) = Pa fl ex p w e1r (p.V 0 0 5) i := by
  have hV := C.swb 1 1 1 (by norm_num) (by norm_num) (by norm_num) (C.hp.V 0 0 5 1)
  have hη5 := C.etaS
  have hI : ∀ k, rdot fl e1r (net.init fl p w k) (p.V 0 0 5) 0 0
      = fl (sw fl 1 (p.V 0 0 5 1) * ev2 fl p w k) := by
    intro k
    rw [init_eq C.hr p w C.hw k]
    simp only [pos, List.cons_append, List.nil_append]
    have hsvb : |sw fl 1 (p.V 0 0 5 1)| ≤ 10052 / 10000 := by
      obtain ⟨hh1, hh2⟩ := abs_le.mp hV
      rw [abs_le]; constructor <;> linarith
    have := absmul2 hsvb (ev2_b C k)
    exact val1_eq C.hr (C.hr.idem _ (le_trans (by linarith) (C.cst 4 (by norm_num))))
  exact Pa_facts_gen C e1r (p.V 0 0 5) (sw fl 1 (p.V 0 0 5 1)) (fun k => ev2 fl p w k) 2 (by linarith) (ev2_b C)
    (ev2_non C) (ev2_one C) hI i hi1 hi

/-! ### block 1: the clean-up MLP -/

noncomputable def ccf (fl : ℝ → ℝ) (Ks bs W b2 P : ℝ) : ℝ :=
  fl (fl (W * relu (fl (fl (Ks * P) + bs))) + b2)

theorem relu_abs_le (x : ℝ) : |relu x| ≤ |x| := by
  unfold relu
  rcases le_total x 0 with h | h
  · rw [max_eq_right h]; simp
  · rw [max_eq_left h]

theorem pre_bd (C : Ctx u η M fl ex p w) (Ks bs P : ℝ) (hK : |Ks| ≤ 5) (hb : |bs| ≤ 2)
    (hP : |P| ≤ 2) : fl (fl (Ks * P)) = fl (Ks * P) ∧ |fl (fl (Ks * P) + bs)| ≤ 100 := by
  have hM := C.cst 1000 (by norm_num)
  have hu6 := C.u24
  have hη5 := C.etaS
  have hKP : |Ks * P| ≤ 10 := by have := absmul2 hK hP; linarith
  refine ⟨C.hr.idem _ (by linarith), ?_⟩
  have h1 := C.hr.bound C.hu0 hKP (by linarith)
  have h2 : |fl (Ks * P) + bs| ≤ 14 := by
    have := abs_add_le (fl (Ks * P)) bs
    linarith
  have h3 := C.hr.bound C.hu0 h2 (by linarith)
  linarith

theorem wrelu_bd (C : Ctx u η M fl ex p w) (W pre : ℝ) (hW : |W| ≤ 2) (hpre : |pre| ≤ 100) :
    fl (fl (W * relu pre)) = fl (W * relu pre) := by
  have hM := C.cst 1000 (by norm_num)
  have h1 := absmul2 hW (le_trans (relu_abs_le pre) hpre)
  exact C.hr.idem _ (by linarith)

theorem ccf_match (C : Ctx u η M fl ex p w) (Ks bs W b2 P : ℝ) (hK : |Ks + 4| ≤ 21 / 1000)
    (hb : |bs - 1| ≤ 52 / 10000) (hW : |W + 1| ≤ 52 / 10000) (hb2 : |b2 - 1| ≤ 52 / 10000)
    (hP : |P - 1| ≤ 23 / 1000) (hfb : fl b2 = b2) :
    ccf fl Ks bs W b2 P = b2 ∧ fl (ccf fl Ks bs W b2 P) = ccf fl Ks bs W b2 P := by
  have hM := C.cst 1000 (by norm_num)
  have hu6 := C.u24
  have hη5 := C.etaS
  obtain ⟨hK1, hK2⟩ := abs_le.mp hK
  obtain ⟨hb1, hb2'⟩ := abs_le.mp hb
  obtain ⟨hP1, hP2⟩ := abs_le.mp hP
  have hKb : |Ks| ≤ 5 := by rw [abs_le]; constructor <;> linarith
  have hPb : |P| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hKP1 : Ks * P ≤ Ks * (977 / 1000) :=
    mul_le_mul_of_nonpos_left (by linarith) (by linarith)
  have hKP : |Ks * P| ≤ 10 := by have := absmul2 hKb hPb; linarith
  have hup := C.hr.upper C.hu0 hKP (by linarith)
  have hx : fl (Ks * P) + bs ≤ 0 := by linarith
  have hpre : fl (fl (Ks * P) + bs) ≤ 0 := by
    apply C.hr.nonpos hx
    have h3 := C.hr.lower C.hu0 hKP (by linarith)
    obtain ⟨h4a, h4b⟩ := abs_le.mp hKP
    linarith
  have hc : ccf fl Ks bs W b2 P = b2 := by
    unfold ccf
    rw [relu_of_nonpos hpre, mul_zero, C.hr.zero, zero_add, hfb]
  refine ⟨hc, ?_⟩
  rw [hc, hfb]

theorem ccf_non (C : Ctx u η M fl ex p w) (Ks bs W b2 P : ℝ) (hK : |Ks + 4| ≤ 21 / 1000)
    (hb : |bs - 1| ≤ 52 / 10000) (hW : |W + 1| ≤ 52 / 10000) (hb2 : |b2 - 1| ≤ 52 / 10000)
    (hP : |P| ≤ 12 / 1000) :
    |ccf fl Ks bs W b2 P| ≤ 8 / 100 ∧ fl (ccf fl Ks bs W b2 P) = ccf fl Ks bs W b2 P := by
  have hM := C.cst 1000 (by norm_num)
  have hu6 := C.u24
  have hη5 := C.etaS
  obtain ⟨hK1, hK2⟩ := abs_le.mp hK
  obtain ⟨hb1, hb2'⟩ := abs_le.mp hb
  obtain ⟨hW1, hW2⟩ := abs_le.mp hW
  obtain ⟨hc1, hc2⟩ := abs_le.mp hb2
  have hKb : |Ks| ≤ 5 := by rw [abs_le]; constructor <;> linarith
  have hKb' : |Ks| ≤ 4021 / 1000 := by rw [abs_le]; constructor <;> linarith
  have hKP : |Ks * P| ≤ 5 / 100 := by have := absmul2 hKb' hP; linarith
  have hf1 := C.hr.abs C.hu0 hKP (by linarith)
  have hf1' : |fl (Ks * P)| ≤ 51 / 1000 := by
    have := abs_sub_abs_le_abs_sub (fl (Ks * P)) (Ks * P)
    linarith
  obtain ⟨hfa1, hfa2⟩ := abs_le.mp hf1'
  set pre0 := fl (Ks * P) + bs with hpre0
  have hpre0b : |pre0| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hf2 := C.hr.abs C.hu0 hpre0b (by linarith)
  obtain ⟨hf21, hf22⟩ := abs_le.mp hf2
  set pre := fl pre0 with hpre
  have hprepos : 0 ≤ pre := by linarith
  have hprebd : |pre| ≤ 106 / 100 := by rw [abs_le]; constructor <;> linarith
  have hreluv : relu (fl (fl (Ks * P) + bs)) = pre := by
    show relu pre = pre
    exact relu_of_nonneg hprepos
  have hWb : |W| ≤ 10052 / 10000 := by rw [abs_le]; constructor <;> linarith
  have hWp : |(W + 1) * pre| ≤ 6 / 1000 := by
    have := absmul2 hW hprebd
    linarith
  have hWpre : |W * pre| ≤ 107 / 100 := by
    have := absmul2 hWb hprebd
    linarith
  have hf3 := C.hr.abs C.hu0 hWpre (by linarith)
  obtain ⟨hf31, hf32⟩ := abs_le.mp hf3
  obtain ⟨hWp1, hWp2⟩ := abs_le.mp hWp
  have hsum : |fl (W * pre) + b2| ≤ 7 / 100 := by
    have e : (W + 1) * pre = W * pre + pre := by ring
    rw [e] at hWp1 hWp2
    rw [abs_le]; constructor <;> linarith
  have hc : ccf fl Ks bs W b2 P = fl (fl (W * pre) + b2) := by
    unfold ccf
    rw [hreluv]
  rw [hc]
  have hb' := C.hr.bound C.hu0 hsum (by linarith)
  refine ⟨by linarith, ?_⟩
  exact C.hr.idem _ (le_trans hsum (by linarith))

/-- The cleaned indicator, computed from the previous-token average `P`. -/
noncomputable def hp1v (fl : ℝ → ℝ) (p : Pert) (P : ℝ) : ℝ :=
  fl (fl (sw fl (-4) (p.W1 0 0 4) * P) + sw fl 1 (p.b1 0 0))

noncomputable def cc1 (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (i : ℕ) : ℝ :=
  ccf fl (sw fl (-4) (p.W1 0 0 4)) (sw fl 1 (p.b1 0 0)) (sw fl (-1) (p.W2 0 6 0))
    (sw fl 1 (p.b2 0 6)) (Pa fl ex p w e0r (p.V 0 0 4) i)

noncomputable def cc2 (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (i : ℕ) : ℝ :=
  ccf fl (sw fl (-4) (p.W1 0 1 5)) (sw fl 1 (p.b1 0 1)) (sw fl (-1) (p.W2 0 7 1))
    (sw fl 1 (p.b2 0 7)) (Pa fl ex p w e1r (p.V 0 0 5) i)

noncomputable def X1 (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (i : ℕ) : Vec :=
  [ev1 fl p w i, ev2 fl p w i, evh fl p w i, evb fl p w i,
   Pa fl ex p w e0r (p.V 0 0 4) i, Pa fl ex p w e1r (p.V 0 0 5) i,
   cc1 fl ex p w i, cc2 fl ex p w i, 0, 0, 0, 1, fl (i : ℝ), fl ((w.length + 1 : ℕ) : ℝ)]

/-- weights used by block 1's MLP -/
theorem w1_box (C : Ctx u η M fl ex p w) (d : ℝ) (hd : |d| ≤ 1 / 200) (q : ℚ)
    (hq : (q : ℝ) = -4) : |sw fl q d + 4| ≤ 21 / 1000 := by
  have h := C.swb q (-4) 4 hq (by norm_num) (by norm_num) hd
  have e : sw fl q d - -4 = sw fl q d + 4 := by ring
  rw [e] at h
  have := C.etaS
  linarith

theorem w_one_box (C : Ctx u η M fl ex p w) (d : ℝ) (hd : |d| ≤ 1 / 200) (q : ℚ)
    (hq : (q : ℝ) = 1) : |sw fl q d - 1| ≤ 52 / 10000 := by
  have h := C.swb q 1 1 hq (by norm_num) (by norm_num) hd
  have := C.etaS
  linarith

theorem w_mone_box (C : Ctx u η M fl ex p w) (d : ℝ) (hd : |d| ≤ 1 / 200) (q : ℚ)
    (hq : (q : ℝ) = -1) : |sw fl q d + 1| ≤ 52 / 10000 := by
  have h := C.swb q (-1) 1 hq (by norm_num) (by norm_num) hd
  have e : sw fl q d - -1 = sw fl q d + 1 := by ring
  rw [e] at h
  have := C.etaS
  linarith

theorem Ctx.flfl (C : Ctx u η M fl ex p w) {k : ℕ} (hk : k ≤ w.length + 1) :
    fl (fl (k : ℝ)) = fl (k : ℝ) := by
  apply C.hr.idem
  have h1 : (k : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hk
  rw [abs_of_nonneg (Nat.cast_nonneg k)]
  have := C.nM
  linarith

theorem Pa1_all (C : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    (tokAt w (i - 1) ≠ 1 → |Pa fl ex p w e0r (p.V 0 0 4) i| ≤ 12 / 1000) ∧
    (tokAt w (i - 1) = 1 → |Pa fl ex p w e0r (p.V 0 0 4) i - 1| ≤ 23 / 1000) ∧
    fl (Pa fl ex p w e0r (p.V 0 0 4) i) = Pa fl ex p w e0r (p.V 0 0 4) i := by
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    have h00 : tokAt w (0 - 1) = 0 := Lane4.Seq.tokAt_zero w
    refine ⟨fun _ => ?_, fun h1 => by omega, ?_⟩
    · rw [Pa_zero C.hr]; norm_num
    · rw [Pa_zero C.hr, C.hr.zero]
  · exact Pa1_facts C i h0 hi

theorem Pa2_all (C : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    (tokAt w (i - 1) ≠ 2 → |Pa fl ex p w e1r (p.V 0 0 5) i| ≤ 12 / 1000) ∧
    (tokAt w (i - 1) = 2 → |Pa fl ex p w e1r (p.V 0 0 5) i - 1| ≤ 23 / 1000) ∧
    fl (Pa fl ex p w e1r (p.V 0 0 5) i) = Pa fl ex p w e1r (p.V 0 0 5) i := by
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    have h00 : tokAt w (0 - 1) = 0 := Lane4.Seq.tokAt_zero w
    refine ⟨fun _ => ?_, fun h1 => by omega, ?_⟩
    · rw [Pa_zero C.hr]; norm_num
    · rw [Pa_zero C.hr, C.hr.zero]
  · exact Pa2_facts C i h0 hi

theorem cc1_facts (C : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    (tokAt w (i - 1) = 1 → cc1 fl ex p w i = sw fl 1 (p.b2 0 6)) ∧
    (tokAt w (i - 1) ≠ 1 → |cc1 fl ex p w i| ≤ 8 / 100) ∧
    fl (cc1 fl ex p w i) = cc1 fl ex p w i := by
  have hK := w1_box C _ (C.hp.W1 0 0 4) (-4) (by norm_num)
  have hb := w_one_box C _ (C.hp.b1 0 0) 1 (by norm_num)
  have hW := w_mone_box C _ (C.hp.W2 0 6 0) (-1) (by norm_num)
  have hb2 := w_one_box C _ (C.hp.b2 0 6) 1 (by norm_num)
  have hfb2 : fl (sw fl 1 (p.b2 0 6)) = sw fl 1 (p.b2 0 6) :=
    C.flsw 1 1 (by norm_num) (by norm_num) (C.hp.b2 0 6)
  obtain ⟨hA, hB, hC⟩ := Pa1_all C i hi
  refine ⟨fun h1 => ?_, fun h1 => ?_, ?_⟩
  · exact (ccf_match C _ _ _ _ _ hK hb hW hb2 (hB h1) hfb2).1
  · exact (ccf_non C _ _ _ _ _ hK hb hW hb2 (hA h1)).1
  · by_cases h1 : tokAt w (i - 1) = 1
    · exact (ccf_match C _ _ _ _ _ hK hb hW hb2 (hB h1) hfb2).2
    · exact (ccf_non C _ _ _ _ _ hK hb hW hb2 (hA h1)).2

theorem cc2_facts (C : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    (tokAt w (i - 1) = 2 → cc2 fl ex p w i = sw fl 1 (p.b2 0 7)) ∧
    (tokAt w (i - 1) ≠ 2 → |cc2 fl ex p w i| ≤ 8 / 100) ∧
    fl (cc2 fl ex p w i) = cc2 fl ex p w i := by
  have hK := w1_box C _ (C.hp.W1 0 1 5) (-4) (by norm_num)
  have hb := w_one_box C _ (C.hp.b1 0 1) 1 (by norm_num)
  have hW := w_mone_box C _ (C.hp.W2 0 7 1) (-1) (by norm_num)
  have hb2 := w_one_box C _ (C.hp.b2 0 7) 1 (by norm_num)
  have hfb2 : fl (sw fl 1 (p.b2 0 7)) = sw fl 1 (p.b2 0 7) :=
    C.flsw 1 1 (by norm_num) (by norm_num) (C.hp.b2 0 7)
  obtain ⟨hA, hB, hC⟩ := Pa2_all C i hi
  refine ⟨fun h1 => ?_, fun h1 => ?_, ?_⟩
  · exact (ccf_match C _ _ _ _ _ hK hb hW hb2 (hB h1) hfb2).1
  · exact (ccf_non C _ _ _ _ _ hK hb hW hb2 (hA h1)).1
  · by_cases h1 : tokAt w (i - 1) = 2
    · exact (ccf_match C _ _ _ _ _ hK hb hW hb2 (hB h1) hfb2).2
    · exact (ccf_non C _ _ _ _ _ hK hb hW hb2 (hA h1)).2

theorem blk1_eq (C : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    sblock blk1 fl ex p 0 (w.length + 1) (net.init fl p w) i = X1 fl ex p w i := by
  have hat := attn1_eq (ex := ex) C.hr p w C.hw i
  obtain ⟨hA1, hA1', hA1''⟩ := Pa1_all C i hi
  obtain ⟨hA2, hA2', hA2''⟩ := Pa2_all C i hi
  obtain ⟨_, _, hc1⟩ := cc1_facts C i hi
  obtain ⟨_, _, hc2⟩ := cc2_facts C i hi
  have hK1 := w1_box C _ (C.hp.W1 0 0 4) (-4) (by norm_num)
  have hK2 := w1_box C _ (C.hp.W1 0 1 5) (-4) (by norm_num)
  have hb1 := w_one_box C _ (C.hp.b1 0 0) 1 (by norm_num)
  have hb2 := w_one_box C _ (C.hp.b1 0 1) 1 (by norm_num)
  have hW6 := w_mone_box C _ (C.hp.W2 0 6 0) (-1) (by norm_num)
  have hW7 := w_mone_box C _ (C.hp.W2 0 7 1) (-1) (by norm_num)
  have hP1b : |Pa fl ex p w e0r (p.V 0 0 4) i| ≤ 2 := by
    by_cases h1 : tokAt w (i - 1) = 1
    · obtain ⟨hh1, hh2⟩ := abs_le.mp (hA1' h1)
      rw [abs_le]; constructor <;> linarith
    · exact le_trans (hA1 h1) (by norm_num)
  have hP2b : |Pa fl ex p w e1r (p.V 0 0 5) i| ≤ 2 := by
    by_cases h1 : tokAt w (i - 1) = 2
    · obtain ⟨hh1, hh2⟩ := abs_le.mp (hA2' h1)
      rw [abs_le]; constructor <;> linarith
    · exact le_trans (hA2 h1) (by norm_num)
  have hKb1 : |sw fl (-4) (p.W1 0 0 4)| ≤ 5 := by
    obtain ⟨hh1, hh2⟩ := abs_le.mp hK1; rw [abs_le]; constructor <;> linarith
  have hKb2 : |sw fl (-4) (p.W1 0 1 5)| ≤ 5 := by
    obtain ⟨hh1, hh2⟩ := abs_le.mp hK2; rw [abs_le]; constructor <;> linarith
  have hbb1 : |sw fl 1 (p.b1 0 0)| ≤ 2 := by
    obtain ⟨hh1, hh2⟩ := abs_le.mp hb1; rw [abs_le]; constructor <;> linarith
  have hbb2 : |sw fl 1 (p.b1 0 1)| ≤ 2 := by
    obtain ⟨hh1, hh2⟩ := abs_le.mp hb2; rw [abs_le]; constructor <;> linarith
  have hWb6 : |sw fl (-1) (p.W2 0 6 0)| ≤ 2 := by
    obtain ⟨hh1, hh2⟩ := abs_le.mp hW6; rw [abs_le]; constructor <;> linarith
  have hWb7 : |sw fl (-1) (p.W2 0 7 1)| ≤ 2 := by
    obtain ⟨hh1, hh2⟩ := abs_le.mp hW7; rw [abs_le]; constructor <;> linarith
  obtain ⟨hIa1, hpre1⟩ := pre_bd C _ _ _ hKb1 hbb1 hP1b
  obtain ⟨hIa2, hpre2⟩ := pre_bd C _ _ _ hKb2 hbb2 hP2b
  have hIb6 := wrelu_bd C _ _ hWb6 hpre1
  have hIb7 := wrelu_bd C _ _ hWb7 hpre2
  have hc1u := hc1
  have hc2u := hc2
  simp only [cc1, cc2, ccf] at hc1u hc2u
  have hflp := C.flfl (k := i) (by omega)
  have hflN := C.flfl (k := w.length + 1) le_rfl
  push_cast at hflN
  have hle := tok_le w C.hw i
  unfold sblock
  simp only [blk1, sheadsApply, hat]
  simp only [init_eq C.hr p w C.hw i]
  simp [X1, cc1, cc2, ccf, pos, radd, raffine, rdot, m1r, m2r, w2z, sw_zero C.hr, C.hr.zero,
    C.hr.one, fl_ev1 C i, fl_ev2 C i, fl_evh C i hle, fl_evb C i, hA1'', hA2'', hc1u, hc2u,
    hflp, hflN, hIa1, hIa2, hIb6, hIb7]

/-! ### block 2: the selection gap -/

theorem gap_core (C : Ctx u η M fl ex p w) (S qn Dj Dk : ℝ) (j k : ℕ)
    (hS : |S - 64| ≤ 33 / 100) (hqn : |qn - ((w.length + 1 : ℕ) : ℝ)| ≤ 1 / 200)
    (hj : j ≤ w.length) (hk : k ≤ w.length) (hDj : |Dj| ≤ 1100) (hDk : |Dk| ≤ 1100)
    (hD : (Dj = Dk ∧ k < j) ∨ Dk + 300 ≤ Dj) :
    fl (fl (S * fl (k : ℝ)) + fl (qn * Dk))
      ≤ fl (fl (S * fl (j : ℝ)) + fl (qn * Dj)) - 16 * (ndist j k : ℝ) := by
  have hN2 := C.nR
  have hu6 := C.u24
  have hη5 := C.etaS
  have hn := C.hn
  have h65 := C.lin 65 (by norm_num) (by norm_num)
  have h1110 := C.lin 1110 (by norm_num) (by norm_num)
  have h1200 := C.lin 1200 (by norm_num) (by norm_num)
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  obtain ⟨hq1, hq2⟩ := abs_le.mp hqn
  have hS0 : 0 ≤ S := by linarith
  have hqn0 : 0 ≤ qn := by linarith
  have hjN : j ≤ w.length + 1 := by omega
  have hkN : k ≤ w.length + 1 := by omega
  obtain ⟨hj0, hj1⟩ := C.pos_b hjN
  obtain ⟨hk0, hk1⟩ := C.pos_b hkN
  have hjk : ((j : ℝ)) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hjN
  have hkk : ((k : ℝ)) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hkN
  have hTj : |S * fl (j : ℝ)| ≤ 65 * ((w.length + 1 : ℕ) : ℝ) := by
    rw [abs_of_nonneg (mul_nonneg hS0 hj0)]
    have := mul_le_mul (show S ≤ 6433 / 100 by linarith) hj1 hj0 (by norm_num)
    linarith
  have hTk : |S * fl (k : ℝ)| ≤ 65 * ((w.length + 1 : ℕ) : ℝ) := by
    rw [abs_of_nonneg (mul_nonneg hS0 hk0)]
    have := mul_le_mul (show S ≤ 6433 / 100 by linarith) hk1 hk0 (by norm_num)
    linarith
  obtain ⟨ej1, ej2⟩ := abs_le.mp (C.hr.abs C.hu0 hTj h65)
  obtain ⟨ek1, ek2⟩ := abs_le.mp (C.hr.abs C.hu0 hTk h65)
  have hqb : |qn| ≤ ((w.length + 1 : ℕ) : ℝ) + 1 / 200 := by
    rw [abs_le]; constructor <;> linarith
  have hQj : |qn * Dj| ≤ 1110 * ((w.length + 1 : ℕ) : ℝ) := by
    have := absmul2 hqb hDj
    linarith
  have hQk : |qn * Dk| ≤ 1110 * ((w.length + 1 : ℕ) : ℝ) := by
    have := absmul2 hqb hDk
    linarith
  obtain ⟨fj1, fj2⟩ := abs_le.mp (C.hr.abs C.hu0 hQj h1110)
  obtain ⟨fk1, fk2⟩ := abs_le.mp (C.hr.abs C.hu0 hQk h1110)
  have hAj : |fl (S * fl (j : ℝ)) + fl (qn * Dj)| ≤ 1200 * ((w.length + 1 : ℕ) : ℝ) := by
    rw [abs_le]; constructor <;> linarith [(abs_le.mp hTj).1, (abs_le.mp hTj).2, (abs_le.mp hQj).1, (abs_le.mp hQj).2]
  have hAk : |fl (S * fl (k : ℝ)) + fl (qn * Dk)| ≤ 1200 * ((w.length + 1 : ℕ) : ℝ) := by
    rw [abs_le]; constructor <;> linarith [(abs_le.mp hTk).1, (abs_le.mp hTk).2, (abs_le.mp hQk).1, (abs_le.mp hQk).2]
  have hgp := C.hr.gap C.hu0 hAk hAj h1200
  rw [ndist_cast]
  rcases hD with ⟨hDe, hkj⟩ | hDg
  · have hQeq : fl (qn * Dj) = fl (qn * Dk) := by rw [hDe]
    have hkj' : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hkj
    have hg := C.pos_g (le_of_lt hkj) hjN
    rw [abs_of_nonneg (by linarith)]
    have hD0 : 0 ≤ fl (j : ℝ) - fl (k : ℝ) := by linarith
    have hSD := mul_le_mul_of_nonneg_right (show (6367 : ℝ) / 100 ≤ S by linarith) hD0
    linarith [hgp, hSD, hg, hkj', hQeq, hn, hη5]
  · have hQd : 300 * qn ≤ qn * Dj - qn * Dk := by
      have := mul_le_mul_of_nonneg_left hDg hqn0
      linarith [this]
    have hTj0 : 0 ≤ fl (S * fl (j : ℝ)) := C.hr.nonneg (mul_nonneg hS0 hj0) (by linarith [(abs_le.mp hTj).2])
    have hnd : |(j : ℝ) - (k : ℝ)| ≤ ((w.length + 1 : ℕ) : ℝ) := by
      rw [abs_le]; constructor <;> linarith
    linarith [hgp, hQd, hTj0, hnd, hn, hη5, hq1, hq2, ej1, ej2, ek1, ek2, fj1, fj2, fk1, fk2,
      (abs_le.mp hTk).1, (abs_le.mp hTk).2]

theorem score_bd (C : Ctx u η M fl ex p w) (S qn D : ℝ) (m : ℕ)
    (hS : |S - 64| ≤ 33 / 100) (hqn : |qn - ((w.length + 1 : ℕ) : ℝ)| ≤ 1 / 200)
    (hm : m ≤ w.length) (hD : |D| ≤ 1100) :
    |fl (fl (S * fl (m : ℝ)) + fl (qn * D))| ≤ 1210 * ((w.length + 1 : ℕ) : ℝ) := by
  have hN2 := C.nR
  have hu6 := C.u24
  have hη5 := C.etaS
  have hn := C.hn
  have h65 := C.lin 65 (by norm_num) (by norm_num)
  have h1110 := C.lin 1110 (by norm_num) (by norm_num)
  have h1200 := C.lin 1200 (by norm_num) (by norm_num)
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  obtain ⟨hq1, hq2⟩ := abs_le.mp hqn
  have hS0 : 0 ≤ S := by linarith
  have hmN : m ≤ w.length + 1 := by omega
  obtain ⟨hm0, hm1⟩ := C.pos_b hmN
  have hmm : ((m : ℝ)) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hmN
  have hT : |S * fl (m : ℝ)| ≤ 65 * ((w.length + 1 : ℕ) : ℝ) := by
    rw [abs_of_nonneg (mul_nonneg hS0 hm0)]
    have := mul_le_mul (show S ≤ 6433 / 100 by linarith) hm1 hm0 (by norm_num)
    linarith
  obtain ⟨ej1, ej2⟩ := abs_le.mp (C.hr.abs C.hu0 hT h65)
  have hqb : |qn| ≤ ((w.length + 1 : ℕ) : ℝ) + 1 / 200 := by
    rw [abs_le]; constructor <;> linarith
  have hQ : |qn * D| ≤ 1110 * ((w.length + 1 : ℕ) : ℝ) := by
    have := absmul2 hqb hD
    linarith
  obtain ⟨fj1, fj2⟩ := abs_le.mp (C.hr.abs C.hu0 hQ h1110)
  have hA : |fl (S * fl (m : ℝ)) + fl (qn * D)| ≤ 1200 * ((w.length + 1 : ℕ) : ℝ) := by
    rw [abs_le]; constructor <;> linarith [(abs_le.mp hT).1, (abs_le.mp hT).2, (abs_le.mp hQ).1, (abs_le.mp hQ).2]
  obtain ⟨g1, g2⟩ := abs_le.mp (C.hr.abs C.hu0 hA h1200)
  rw [abs_le]; constructor <;> linarith [(abs_le.mp hA).1, (abs_le.mp hA).2]

def win (w : List ℕ) (t : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if tokAt w i = t then i + 1 else win w t i

theorem win_le (w : List ℕ) (t : ℕ) : ∀ i, win w t i ≤ i := by
  intro i
  induction i with
  | zero => simp [win]
  | succ i ih =>
    simp only [win]
    split_ifs <;> omega

theorem win_match (w : List ℕ) (t : ℕ) : ∀ i, 1 ≤ win w t i → tokAt w (win w t i - 1) = t := by
  intro i
  induction i with
  | zero => intro h; simp [win] at h
  | succ i ih =>
    intro h
    by_cases hc : tokAt w i = t
    · simp only [win, if_pos hc]
      simpa using hc
    · simp only [win, if_neg hc] at h ⊢
      exact ih h

theorem win_latest (w : List ℕ) (t : ℕ) :
    ∀ i k, win w t i < k → k ≤ i → tokAt w (k - 1) ≠ t := by
  intro i
  induction i with
  | zero => intro k h1 h2; omega
  | succ i ih =>
    intro k h1 h2
    by_cases hc : tokAt w i = t
    · simp only [win, if_pos hc] at h1; omega
    · simp only [win, if_neg hc] at h1
      by_cases hk : k = i + 1
      · subst hk; simpa using hc
      · exact ih k h1 (by omega)

theorem flerr (C : Ctx u η M fl ex p w) {x B : ℝ} (hx : |x| ≤ B) (hB : B ≤ 2000) :
    |fl x - x| ≤ 1 / 400 := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg x) hx
  have hM := C.cst 2000 (by norm_num)
  have h := C.hr.abs C.hu0 hx (by linarith)
  have h2 : u * B ≤ 1 / 1000000 * B := mul_le_mul_of_nonneg_right C.u24 hB0
  have := C.etaS
  linarith

theorem Dm_bd (C : Ctx u η M fl ex p w) (Bs Ws cm : ℝ) (hWs : |Ws - 1024| ≤ 52 / 10)
    (hcm : |cm - 1| ≤ 52 / 10000) :
    1000 ≤ fl (fl (Bs * 0) + fl (Ws * cm)) ∧ fl (fl (Bs * 0) + fl (Ws * cm)) ≤ 1050 := by
  rw [mul_zero, C.hr.zero, zero_add]
  obtain ⟨a1, a2⟩ := abs_le.mp hWs
  obtain ⟨b1, b2⟩ := abs_le.mp hcm
  have hlo : (10188 / 10 : ℝ) * (9948 / 10000) ≤ Ws * cm :=
    mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
  have hhi : Ws * cm ≤ (10292 / 10 : ℝ) * (10052 / 10000) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have hz : |Ws * cm| ≤ 1100 := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨e1a, e1b⟩ := abs_le.mp (flerr C hz (by norm_num))
  have hz2 : |fl (Ws * cm)| ≤ 1100 := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨e2a, e2b⟩ := abs_le.mp (flerr C hz2 (by norm_num))
  constructor <;> linarith

theorem Do_bd (C : Ctx u η M fl ex p w) (Bs Ws c : ℝ) (hWs : |Ws - 1024| ≤ 52 / 10)
    (hc : |c| ≤ 8 / 100) : |fl (fl (Bs * 0) + fl (Ws * c))| ≤ 90 := by
  rw [mul_zero, C.hr.zero, zero_add]
  have hWb : |Ws| ≤ 10292 / 10 := by
    obtain ⟨hh1, hh2⟩ := abs_le.mp hWs
    rw [abs_le]; constructor <;> linarith
  have hz : |Ws * c| ≤ 83 := by
    have := absmul2 hWb hc
    linarith
  obtain ⟨e1a, e1b⟩ := abs_le.mp (flerr C hz (by norm_num))
  have hz2 : |fl (Ws * c)| ≤ 84 := by
    rw [abs_le]; constructor <;> linarith [(abs_le.mp hz).1, (abs_le.mp hz).2]
  obtain ⟨e2a, e2b⟩ := abs_le.mp (flerr C hz2 (by norm_num))
  rw [abs_le]; constructor <;> linarith [(abs_le.mp hz).1, (abs_le.mp hz).2]

theorem D0_bd (C : Ctx u η M fl ex p w) (Bs Ws b c : ℝ) (hBs : |Bs - 512| ≤ 26 / 10)
    (hWs : |Ws - 1024| ≤ 52 / 10) (hb : |b - 1| ≤ 52 / 10000) (hc : |c| ≤ 8 / 100) :
    420 ≤ fl (fl (Bs * b) + fl (Ws * c)) ∧ fl (fl (Bs * b) + fl (Ws * c)) ≤ 610 := by
  obtain ⟨a1, a2⟩ := abs_le.mp hBs
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  have hWb : |Ws| ≤ 10292 / 10 := by
    obtain ⟨hh1, hh2⟩ := abs_le.mp hWs
    rw [abs_le]; constructor <;> linarith
  have hlo : (5094 / 10 : ℝ) * (9948 / 10000) ≤ Bs * b :=
    mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
  have hhi : Bs * b ≤ (5146 / 10 : ℝ) * (10052 / 10000) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have hz1 : |Bs * b| ≤ 600 := by
    rw [abs_le]; constructor <;> linarith
  have hz2 : |Ws * c| ≤ 83 := by
    have := absmul2 hWb hc
    linarith
  obtain ⟨e1a, e1b⟩ := abs_le.mp (flerr C hz1 (by norm_num))
  obtain ⟨e2a, e2b⟩ := abs_le.mp (flerr C hz2 (by norm_num))
  have hz3 : |fl (Bs * b) + fl (Ws * c)| ≤ 700 := by
    rw [abs_le]; constructor <;> linarith [(abs_le.mp hz2).1, (abs_le.mp hz2).2]
  obtain ⟨e3a, e3b⟩ := abs_le.mp (flerr C hz3 (by norm_num))
  constructor <;> linarith [(abs_le.mp hz2).1, (abs_le.mp hz2).2]

theorem head2_gap (C : Ctx u η M fl ex p w) (t : ℕ) (ht : t = 1 ∨ t = 2) (s cc : ℕ → ℝ)
    (S Bs Ws qn cm : ℝ) (hS : |S - 64| ≤ 33 / 100) (hBs : |Bs - 512| ≤ 26 / 10)
    (hWs : |Ws - 1024| ≤ 52 / 10) (hqn : |qn - ((w.length + 1 : ℕ) : ℝ)| ≤ 1 / 200)
    (hcm : |cm - 1| ≤ 52 / 10000)
    (hccm : ∀ k, k ≤ w.length → tokAt w (k - 1) = t → cc k = cm)
    (hccn : ∀ k, k ≤ w.length → tokAt w (k - 1) ≠ t → |cc k| ≤ 8 / 100)
    (hs : ∀ k, k ≤ w.length → s k = fl (fl (S * fl (k : ℝ)) + fl (qn * fl (fl (Bs * evb fl p w k)
      + fl (Ws * cc k)))))
    (i : ℕ) (hi : i ≤ w.length) :
    (∀ k ∈ cand Mask.causal (w.length + 1) i, k ≠ win w t i →
      s k ≤ s (win w t i) - 16 * (ndist (win w t i) k : ℝ)) ∧
    (∀ m, m ≤ w.length → |s m| ≤ 1210 * ((w.length + 1 : ℕ) : ℝ)) := by
  have hjle := win_le w t i
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ m, D m = fl (fl (Bs * evb fl p w m) + fl (Ws * cc m)) :=
    ⟨_, fun m => rfl⟩
  have hsD : ∀ m, m ≤ w.length → s m = fl (fl (S * fl (m : ℝ)) + fl (qn * D m)) := by
    intro m hm
    rw [hs m hm, hD m]
  have hmatch : ∀ m, m ≤ w.length → tokAt w (m - 1) = t →
      (D m = fl (fl (Bs * 0) + fl (Ws * cm)) ∧ 1000 ≤ D m ∧ D m ≤ 1050) := by
    intro m hm hmt
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        have h00 : tokAt w (0 - 1) = 0 := Lane4.Seq.tokAt_zero w
        omega
      · exact h0
    have hev : evb fl p w m = 0 := evb_zero C m (by have := tok_pos w C.hw hm1 hm; omega)
    have hDm : D m = fl (fl (Bs * 0) + fl (Ws * cm)) := by rw [hD m, hev, hccm m hm hmt]
    have hb := Dm_bd C Bs Ws cm hWs hcm
    exact ⟨hDm, by rw [hDm]; exact hb.1, by rw [hDm]; exact hb.2⟩
  have hother : ∀ m, 1 ≤ m → m ≤ w.length → tokAt w (m - 1) ≠ t → |D m| ≤ 90 := by
    intro m hm1 hm hmt
    have hev : evb fl p w m = 0 := evb_zero C m (by have := tok_pos w C.hw hm1 hm; omega)
    rw [hD m, hev]
    exact Do_bd C Bs Ws (cc m) hWs (hccn m hm hmt)
  have hbos : 420 ≤ D 0 ∧ D 0 ≤ 610 := by
    have hz : tokAt w (0 - 1) ≠ t := by
      have h00 : tokAt w (0 - 1) = 0 := Lane4.Seq.tokAt_zero w
      omega
    have hb := evb_one C 0 (Lane4.Seq.tokAt_zero w)
    rw [hD 0]
    exact D0_bd C Bs Ws (evb fl p w 0) (cc 0) hBs hWs hb (hccn 0 (by omega) hz)
  have hj : win w t i ≤ w.length := by omega
  have hbnd : ∀ m, m ≤ w.length → |D m| ≤ 1100 := by
    intro m hm
    by_cases hmt : tokAt w (m - 1) = t
    · obtain ⟨_, h1, h2⟩ := hmatch m hm hmt
      rw [abs_le]; constructor <;> linarith
    · by_cases hm0 : m = 0
      · subst hm0
        obtain ⟨h1, h2⟩ := hbos
        rw [abs_le]; constructor <;> linarith
      · exact le_trans (hother m (by omega) hm hmt) (by norm_num)
  refine ⟨?_, fun m hm => ?_⟩
  swap
  · rw [hsD m hm]
    exact score_bd C S qn (D m) m hS hqn hm (hbnd m hm)
  intro k hk hne
  rw [Lane4.Seq.mem_cand_causal] at hk
  have hkl : k ≤ w.length := by omega
  rw [hsD k hkl, hsD _ hj]
  refine gap_core C S qn _ _ _ _ hS hqn hj hkl (hbnd _ hj) (hbnd _ hkl) ?_
  by_cases hj0 : win w t i = 0
  · have hk1 : 1 ≤ k := by omega
    have hku : tokAt w (k - 1) ≠ t := win_latest w t i k (by omega) hk
    have h90 := hother k hk1 hkl hku
    obtain ⟨h1, h2⟩ := hbos
    obtain ⟨h90a, h90b⟩ := abs_le.mp h90
    right
    rw [hj0]
    linarith
  · have hjm := win_match w t i (by omega)
    obtain ⟨hDj, hj1, hj2⟩ := hmatch _ hj hjm
    by_cases hkm : tokAt w (k - 1) = t
    · have hkj : k ≤ win w t i := by
        by_contra hh
        exact win_latest w t i k (by omega) hk hkm
      obtain ⟨hDk, hk1', hk2'⟩ := hmatch k hkl hkm
      left
      exact ⟨by rw [hDj, hDk], by omega⟩
    · by_cases hk0 : k = 0
      · subst hk0
        obtain ⟨h1, h2⟩ := hbos
        right
        linarith
      · have h90 := hother k (by omega) hkl hkm
        obtain ⟨h90a, h90b⟩ := abs_le.mp h90
        right
        linarith

/-! ### block 2: heads -/

noncomputable def Hh (fl ex : ℝ → ℝ) (hh : Head) (dA : ℕ → ℕ → ℝ) (dv : ℕ → ℝ) (n i : ℕ)
    (x : ℕ → Vec) : ℝ :=
  savg fl ex (cand Mask.causal n i) (hscore hh fl dA x i) (fun k => rdot fl hvr (x k) dv 0 0)

theorem attn2a_eq (hr : Rnd u η M fl) (dA dV : ℕ → ℕ → ℝ) (n : ℕ) (x : ℕ → Vec) (i : ℕ) :
    sattn hd2a fl ex dA dV n x i
      = [0, 0, 0, 0, 0, 0, 0, 0, Hh fl ex hd2a dA (dV 8) n i x, 0, 0, 0, 0, 0] := by
  have hz : ∀ d : ℕ → ℝ,
      savg fl ex (cand Mask.causal n i) (hscore hd2a fl dA x i)
        (fun j => rdot fl z14 (x j) d 0 0) = 0 := by
    intro d
    apply soft_zeros hr
    intro k _
    exact rdot_zeros hr z14 z14_zero _ d 0
  have hV : hd2a.V = [z14,z14,z14,z14,z14,z14,z14,z14,hvr,z14,z14,z14,z14,z14] := rfl
  have hm : hd2a.mask = Mask.causal := rfl
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz, Hh]

theorem attn2b_eq (hr : Rnd u η M fl) (dA dV : ℕ → ℕ → ℝ) (n : ℕ) (x : ℕ → Vec) (i : ℕ) :
    sattn hd2b fl ex dA dV n x i
      = [0, 0, 0, 0, 0, 0, 0, 0, 0, Hh fl ex hd2b dA (dV 9) n i x, 0, 0, 0, 0] := by
  have hz : ∀ d : ℕ → ℝ,
      savg fl ex (cand Mask.causal n i) (hscore hd2b fl dA x i)
        (fun j => rdot fl z14 (x j) d 0 0) = 0 := by
    intro d
    apply soft_zeros hr
    intro k _
    exact rdot_zeros hr z14 z14_zero _ d 0
  have hV : hd2b.V = [z14,z14,z14,z14,z14,z14,z14,z14,z14,hvr,z14,z14,z14,z14] := rfl
  have hm : hd2b.mask = Mask.causal := rfl
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz, Hh]

theorem cc1_b (C : Ctx u η M fl ex p w) (k : ℕ) (hk : k ≤ w.length) :
    |cc1 fl ex p w k| ≤ 11 / 10 := by
  obtain ⟨h1, h2, h3⟩ := cc1_facts C k hk
  by_cases hm : tokAt w (k - 1) = 1
  · rw [h1 hm]
    have hb := w_one_box C _ (C.hp.b2 0 6) 1 (by norm_num)
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    rw [abs_le]; constructor <;> linarith
  · exact le_trans (h2 hm) (by norm_num)

theorem cc2_b (C : Ctx u η M fl ex p w) (k : ℕ) (hk : k ≤ w.length) :
    |cc2 fl ex p w k| ≤ 11 / 10 := by
  obtain ⟨h1, h2, h3⟩ := cc2_facts C k hk
  by_cases hm : tokAt w (k - 1) = 2
  · rw [h1 hm]
    have hb := w_one_box C _ (C.hp.b2 0 7) 1 (by norm_num)
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    rw [abs_le]; constructor <;> linarith
  · exact le_trans (h2 hm) (by norm_num)

theorem D_idems (C : Ctx u η M fl ex p w) (Bs Ws b c : ℝ) (hBs : |Bs - 512| ≤ 26 / 10)
    (hWs : |Ws - 1024| ≤ 52 / 10) (hb : |b| ≤ 11 / 10) (hc : |c| ≤ 11 / 10) :
    fl (fl (Bs * b)) = fl (Bs * b) ∧
    fl (fl (fl (Bs * b) + fl (Ws * c))) = fl (fl (Bs * b) + fl (Ws * c)) := by
  have hM := C.cst 100000 (by norm_num)
  have hBb : |Bs| ≤ 5146 / 10 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hBs
    rw [abs_le]; constructor <;> linarith
  have hWb : |Ws| ≤ 10292 / 10 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hWs
    rw [abs_le]; constructor <;> linarith
  have h1 : |Bs * b| ≤ 600 := by
    have := absmul2 hBb hb
    linarith
  have h2 : |Ws * c| ≤ 1200 := by
    have := absmul2 hWb hc
    linarith
  refine ⟨C.hr.idem _ (by linarith), C.hr.idem _ ?_⟩
  obtain ⟨e1a, e1b⟩ := abs_le.mp (flerr C h1 (by norm_num))
  obtain ⟨e2a, e2b⟩ := abs_le.mp (flerr C h2 (by norm_num))
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  rw [abs_le]; constructor <;> linarith

theorem hPb2 (C : Ctx u η M fl ex p w) (S : ℝ) (hS : |S - 64| ≤ 33 / 100) (k : ℕ)
    (hk : k ≤ w.length + 1) :
    fl (fl (S * fl (k : ℝ))) = fl (S * fl (k : ℝ)) := by
  have hN2 := C.nR
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  obtain ⟨hk0, hk1⟩ := C.pos_b hk
  have hS0 : 0 ≤ S := by linarith
  have h65 := C.lin 65 (by norm_num) (by norm_num)
  apply C.hr.idem
  rw [abs_of_nonneg (mul_nonneg hS0 hk0)]
  have := mul_le_mul (show S ≤ 6433 / 100 by linarith) hk1 hk0 (by norm_num)
  linarith

theorem hsk2a (C : Ctx u η M fl ex p w) (x : ℕ → Vec)
    (hx : ∀ k, k ≤ w.length → x k = X1 fl ex p w k) (i k : ℕ) (hi : i ≤ w.length)
    (hk : k ≤ w.length) :
    hscore hd2a fl (p.A 1 0) x i k
      = fl (fl (sw fl 64 (p.A 1 0 11 12) * fl (k : ℝ)) + fl (fl ((w.length + 1 : ℕ) : ℝ) *
          fl (fl (sw fl 512 (p.A 1 0 13 3) * evb fl p w k)
            + fl (sw fl 1024 (p.A 1 0 13 6) * cc1 fl ex p w k)))) := by
  have hS := C.swb 64 64 64 (by norm_num) (by norm_num) (by norm_num) (C.hp.A 1 0 11 12)
  have hBs := C.swb 512 512 512 (by norm_num) (by norm_num) (by norm_num) (C.hp.A 1 0 13 3)
  have hWs := C.swb 1024 1024 1024 (by norm_num) (by norm_num) (by norm_num) (C.hp.A 1 0 13 6)
  have hη5 := C.etaS
  have hS' : |sw fl 64 (p.A 1 0 11 12) - 64| ≤ 33 / 100 := by
    refine le_trans hS ?_; linarith
  have hBs' : |sw fl 512 (p.A 1 0 13 3) - 512| ≤ 26 / 10 := by
    refine le_trans hBs ?_; linarith
  have hWs' : |sw fl 1024 (p.A 1 0 13 6) - 1024| ≤ 52 / 10 := by
    refine le_trans hWs ?_; linarith
  obtain ⟨hD1, hD⟩ := D_idems C _ _ (evb fl p w k) (cc1 fl ex p w k) hBs' hWs'
    (by have := evb_b C k; linarith) (cc1_b C k hk)
  have hT := hPb2 C _ hS' k (by omega)
  simp only [hscore, hx i hi, hx k hk, X1]
  exact score2a_eq C.hr hT hD1 hD

theorem hsk2b (C : Ctx u η M fl ex p w) (x : ℕ → Vec)
    (hx : ∀ k, k ≤ w.length → x k = X1 fl ex p w k) (i k : ℕ) (hi : i ≤ w.length)
    (hk : k ≤ w.length) :
    hscore hd2b fl (p.A 1 1) x i k
      = fl (fl (sw fl 64 (p.A 1 1 11 12) * fl (k : ℝ)) + fl (fl ((w.length + 1 : ℕ) : ℝ) *
          fl (fl (sw fl 512 (p.A 1 1 13 3) * evb fl p w k)
            + fl (sw fl 1024 (p.A 1 1 13 7) * cc2 fl ex p w k)))) := by
  have hS := C.swb 64 64 64 (by norm_num) (by norm_num) (by norm_num) (C.hp.A 1 1 11 12)
  have hBs := C.swb 512 512 512 (by norm_num) (by norm_num) (by norm_num) (C.hp.A 1 1 13 3)
  have hWs := C.swb 1024 1024 1024 (by norm_num) (by norm_num) (by norm_num) (C.hp.A 1 1 13 7)
  have hη5 := C.etaS
  have hS' : |sw fl 64 (p.A 1 1 11 12) - 64| ≤ 33 / 100 := by
    refine le_trans hS ?_; linarith
  have hBs' : |sw fl 512 (p.A 1 1 13 3) - 512| ≤ 26 / 10 := by
    refine le_trans hBs ?_; linarith
  have hWs' : |sw fl 1024 (p.A 1 1 13 7) - 1024| ≤ 52 / 10 := by
    refine le_trans hWs ?_; linarith
  obtain ⟨hD1, hD⟩ := D_idems C _ _ (evb fl p w k) (cc2 fl ex p w k) hBs' hWs'
    (by have := evb_b C k; linarith) (cc2_b C k hk)
  have hT := hPb2 C _ hS' k (by omega)
  simp only [hscore, hx i hi, hx k hk, X1]
  exact score2b_eq C.hr hT hD1 hD

theorem valh_all (C : Ctx u η M fl ex p w) (x : ℕ → Vec)
    (hx : ∀ k, k ≤ w.length → x k = X1 fl ex p w k) (dv : ℕ → ℝ) (hdv : |dv 2| ≤ 1 / 200)
    (k : ℕ) (hk : k ≤ w.length) :
    rdot fl hvr (x k) dv 0 0 = fl (sw fl 1 (dv 2) * evh fl p w k) := by
  have hV := C.swb 1 1 1 (by norm_num) (by norm_num) (by norm_num) hdv
  have hη5 := C.etaS
  obtain ⟨hV1, hV2⟩ := abs_le.mp hV
  have hsvb : |sw fl 1 (dv 2)| ≤ 10052 / 10000 := by
    rw [abs_le]; constructor <;> linarith
  have hle := tok_le w C.hw k
  have hprod := absmul2 hsvb (evh_b C k hle)
  rw [hx k hk]
  simp only [X1]
  exact valh_eq C.hr (C.hr.idem _ (le_trans (by linarith) (C.cst 4 (by norm_num))))

theorem head2_main (C : Ctx u η M fl ex p w) (hh : Head) (dA : ℕ → ℕ → ℝ) (dv : ℕ → ℝ)
    (x : ℕ → Vec) (t : ℕ) (ht : t = 1 ∨ t = 2) (cc : ℕ → ℝ) (S Bs Ws cm sv : ℝ)
    (hS : |S - 64| ≤ 33 / 100) (hBs : |Bs - 512| ≤ 26 / 10)
    (hWs : |Ws - 1024| ≤ 52 / 10) (hcm : |cm - 1| ≤ 52 / 10000)
    (hsv : |sv - 1| ≤ 52 / 10000)
    (hccm : ∀ k, k ≤ w.length → tokAt w (k - 1) = t → cc k = cm)
    (hccn : ∀ k, k ≤ w.length → tokAt w (k - 1) ≠ t → |cc k| ≤ 8 / 100)
    (i : ℕ) (hi : i ≤ w.length)
    (hs : ∀ k, k ≤ w.length → hscore hh fl dA x i k
      = fl (fl (S * fl (k : ℝ)) + fl (fl ((w.length + 1 : ℕ) : ℝ) * fl (fl (Bs * evb fl p w k)
          + fl (Ws * cc k)))))
    (hf : ∀ k, k ≤ w.length → rdot fl hvr (x k) dv 0 0 = fl (sv * evh fl p w k)) :
    |Hh fl ex hh dA dv (w.length + 1) i x - fl (sv * evh fl p w (win w t i))|
        ≤ 21 / 1000 + 1 / 2 ^ 90 ∧
      fl (Hh fl ex hh dA dv (w.length + 1) i x) = Hh fl ex hh dA dv (w.length + 1) i x := by
  have hN2 := C.nR
  have hu6 := C.u24
  have hη5 := C.etaS
  have h2420 := C.lin 2420 (by norm_num) (by norm_num)
  have h40 := C.cst 40 (by norm_num)
  obtain ⟨hg, hsb⟩ := head2_gap C t ht (hscore hh fl dA x i) cc S Bs Ws
    (fl ((w.length + 1 : ℕ) : ℝ)) cm hS hBs hWs (C.pos_n le_rfl) hcm hccm hccn hs i hi
  have hjle := win_le w t i
  have hj : win w t i ∈ cand Mask.causal (w.length + 1) i := by
    rw [Lane4.Seq.mem_cand_causal]; omega
  have hlen : (cand Mask.causal (w.length + 1) i).length ≤ w.length + 1 := by
    simp [cand]; omega
  have hSb : ∀ k ∈ cand Mask.causal (w.length + 1) i,
      |hscore hh fl dA x i k| ≤ 1210 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    rw [Lane4.Seq.mem_cand_causal] at hk
    exact hsb k (by omega)
  have hsvb : |sv| ≤ 10052 / 10000 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hsv
    rw [abs_le]; constructor <;> linarith
  have hfB : ∀ k ∈ cand Mask.causal (w.length + 1) i,
      |(fun j => rdot fl hvr (x j) dv 0 0) k| ≤ 21 / 10 := by
    intro k hk
    rw [Lane4.Seq.mem_cand_causal] at hk
    show |rdot fl hvr (x k) dv 0 0| ≤ 21 / 10
    rw [hf k (by omega)]
    have hprod := absmul2 hsvb (evh_b C k (tok_le w C.hw k))
    have hb := C.hr.bound C.hu0 (show |sv * evh fl p w k| ≤ 205 / 100 by linarith) (by linarith)
    linarith
  obtain ⟨hA1, hA2⟩ := soft_near C.hr C.he C.hu0 C.hu1 C.hη0 C.hη (Lane4.Seq.cand_nodup _ _ _)
    hlen C.hn C.hnη hj (fun k hk hne => hg k hk hne) hSb (by linarith) hfB (by linarith)
  refine ⟨?_, hA2⟩
  have e : (21 / 10 : ℝ) / 100 + 1 / 2 ^ 90 = 21 / 1000 + 1 / 2 ^ 90 := by norm_num
  rw [e] at hA1
  have hfj := hf (win w t i) (by omega)
  have hA1' : |Hh fl ex hh dA dv (w.length + 1) i x - rdot fl hvr (x (win w t i)) dv 0 0|
      ≤ 21 / 1000 + 1 / 2 ^ 90 := hA1
  rw [hfj] at hA1'
  exact hA1'

theorem fl_id (C : Ctx u η M fl ex p w) {x : ℝ} (hx : |x| ≤ 5000) : fl (fl x) = fl x :=
  C.hr.idem x (le_trans hx (C.cst 5000 (by norm_num)))

theorem fl_bd (C : Ctx u η M fl ex p w) {x B : ℝ} (hx : |x| ≤ B) (hB : B ≤ 5000) :
    |fl x| ≤ B + 1 := by
  have hB0 := le_trans (abs_nonneg x) hx
  have h := C.hr.bound C.hu0 hx (le_trans hB (C.cst 5000 (by norm_num)))
  have h2 : u * B ≤ 1 / 1000000 * B := mul_le_mul_of_nonneg_right C.u24 hB0
  have := C.etaS
  linarith

noncomputable def gpv (fl : ℝ → ℝ) (s3 s1 nb e H : ℝ) : ℝ :=
  fl (fl (fl (s3 * e) + fl (s1 * H)) + nb)

noncomputable def gRv (fl : ℝ → ℝ) (wa wb g1 g2 : ℝ) : ℝ :=
  fl (fl (wa * relu g1) + fl (wb * relu g2))

theorem gpv_facts (C : Ctx u η M fl ex p w) (s3 s1 nb e H : ℝ) (h3 : |s3| ≤ 6) (h1 : |s1| ≤ 2)
    (hnb : |nb| ≤ 6) (he : |e| ≤ 2) (hH : |H| ≤ 3) :
    fl (fl (s3 * e)) = fl (s3 * e) ∧
    fl (fl (fl (s3 * e) + fl (s1 * H))) = fl (fl (s3 * e) + fl (s1 * H)) ∧
    |gpv fl s3 s1 nb e H| ≤ 100 := by
  have a1 : |s3 * e| ≤ 12 := by have := absmul2 h3 he; linarith
  have a2 : |s1 * H| ≤ 6 := by have := absmul2 h1 hH; linarith
  have b1 := fl_bd C a1 (by norm_num)
  have b2 := fl_bd C a2 (by norm_num)
  have c1 : |fl (s3 * e) + fl (s1 * H)| ≤ 20 := by
    have := abs_add_le (fl (s3 * e)) (fl (s1 * H))
    linarith
  have d1 := fl_bd C c1 (by norm_num)
  have c2 : |fl (fl (s3 * e) + fl (s1 * H)) + nb| ≤ 27 := by
    have := abs_add_le (fl (fl (s3 * e) + fl (s1 * H))) nb
    linarith
  have d2 := fl_bd C c2 (by norm_num)
  refine ⟨fl_id C (by linarith), fl_id C (by linarith), ?_⟩
  unfold gpv
  linarith

theorem gRv_facts (C : Ctx u η M fl ex p w) (wa wb g1 g2 : ℝ) (ha : |wa| ≤ 2) (hb : |wb| ≤ 2)
    (hg1 : |g1| ≤ 100) (hg2 : |g2| ≤ 100) :
    fl (fl (wa * relu g1)) = fl (wa * relu g1) ∧ fl (fl (wb * relu g2)) = fl (wb * relu g2) ∧
    fl (gRv fl wa wb g1 g2) = gRv fl wa wb g1 g2 ∧ |gRv fl wa wb g1 g2| ≤ 1000 := by
  have a1 : |wa * relu g1| ≤ 200 := by
    have := absmul2 ha (le_trans (relu_abs_le g1) hg1); linarith
  have a2 : |wb * relu g2| ≤ 200 := by
    have := absmul2 hb (le_trans (relu_abs_le g2) hg2); linarith
  have b1 := fl_bd C a1 (by norm_num)
  have b2 := fl_bd C a2 (by norm_num)
  have c1 : |fl (wa * relu g1) + fl (wb * relu g2)| ≤ 404 := by
    have := abs_add_le (fl (wa * relu g1)) (fl (wb * relu g2))
    linarith
  have d1 := fl_bd C c1 (by norm_num)
  refine ⟨fl_id C (by linarith), fl_id C (by linarith), ?_, ?_⟩
  · unfold gRv
    exact fl_id C (le_trans c1 (by norm_num))
  · unfold gRv
    linarith

/-! ### the specification side -/

theorem prev_win (w : List ℕ) (t : ℕ) (ht : t ≠ 0) : ∀ i,
    (List.range i).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == t))
      = if win w t i = 0 then none else some (win w t i - 1) := by
  intro i
  induction i with
  | zero => simp [win]
  | succ i ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.find?_cons]
    by_cases hc : tokAt w i = t
    · have hi : 1 ≤ i := by
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · subst h0
          have := Lane4.Seq.tokAt_zero w
          omega
        · exact h0
      simp [win, hc, hi]
    · have hb : (decide (1 ≤ i) && (tokAt w i == t)) = false := by simp [hc]
      rw [hb]
      simp only [win, if_neg hc]
      exact ih

theorem target_eq (w : List ℕ) (i : ℕ) (ht : tokAt w i ≠ 0) :
    target w i = h (tokAt w (win w (tokAt w i) i)) := by
  unfold target prevOcc
  rw [prev_win w _ ht i]
  by_cases h0 : win w (tokAt w i) i = 0
  · rw [if_pos h0, h0]
    simp [h, Lane4.Seq.tokAt_zero]
  · rw [if_neg h0]
    show h (tokAt w (win w (tokAt w i) i - 1 + 1)) = _
    rw [Nat.sub_add_cancel (by omega)]

theorem relu_near {G T d : ℝ} (hT : 0 ≤ T) (hG : |G - T| ≤ d) : |relu G - T| ≤ d := by
  unfold relu
  rcases le_total G 0 with hg | hg
  · rw [max_eq_right hg]
    obtain ⟨h1, h2⟩ := abs_le.mp hG
    rw [abs_le]; constructor <;> linarith
  · rw [max_eq_left hg]; exact hG

theorem fval (C : Ctx u η M fl ex p w) (sv : ℝ) (hsv : |sv - 1| ≤ 52 / 10000) (m : ℕ)
    (hm : tokAt w m ≤ 2) :
    |fl (sv * evh fl p w m) - ((h (tokAt w m) : ℕ) : ℝ)| ≤ 25 / 1000 := by
  obtain ⟨hs1, hs2⟩ := abs_le.mp hsv
  have hsvb : |sv| ≤ 10052 / 10000 := by rw [abs_le]; constructor <;> linarith
  by_cases h1 : tokAt w m = 1
  · have hh : h (tokAt w m) = 2 := by simp [h, h1]
    rw [hh]
    have he := evh_one C m h1
    obtain ⟨e1, e2⟩ := abs_le.mp he
    have heb : |evh fl p w m| ≤ 2011 / 1000 := by rw [abs_le]; constructor <;> linarith
    have hx : |sv * evh fl p w m - 2| ≤ 22 / 1000 := by
      have hh2 : sv * evh fl p w m - 2 = (sv - 1) * evh fl p w m + (evh fl p w m - 2) := by ring
      rw [hh2]
      have t1 := absmul2 hsv heb
      have t3 := abs_add_le ((sv - 1) * evh fl p w m) (evh fl p w m - 2)
      linarith
    have hxb : |sv * evh fl p w m| ≤ 3 := by
      have := absmul2 hsvb heb
      linarith
    obtain ⟨f1, f2⟩ := abs_le.mp (flerr C hxb (by norm_num))
    obtain ⟨x1, x2⟩ := abs_le.mp hx
    push_cast
    rw [abs_le]; constructor <;> linarith
  · by_cases h2 : tokAt w m = 2
    · have hh : h (tokAt w m) = 1 := by simp [h, h1, h2]
      rw [hh]
      have he := evh_two C m h2
      obtain ⟨e1, e2⟩ := abs_le.mp he
      have heb : |evh fl p w m| ≤ 2011 / 1000 := by rw [abs_le]; constructor <;> linarith
      have hx : |sv * evh fl p w m - 1| ≤ 22 / 1000 := by
        have hh2 : sv * evh fl p w m - 1 = (sv - 1) * evh fl p w m + (evh fl p w m - 1) := by ring
        rw [hh2]
        have t1 := absmul2 hsv heb
        have t3 := abs_add_le ((sv - 1) * evh fl p w m) (evh fl p w m - 1)
        linarith
      have hxb : |sv * evh fl p w m| ≤ 3 := by
        have := absmul2 hsvb heb
        linarith
      obtain ⟨f1, f2⟩ := abs_le.mp (flerr C hxb (by norm_num))
      obtain ⟨x1, x2⟩ := abs_le.mp hx
      push_cast
      rw [abs_le]; constructor <;> linarith
    · have hz : evh fl p w m = 0 := by
        unfold evh
        rw [if_neg h1, if_neg h2]
        exact sw_zero C.hr _
      have hh : h (tokAt w m) = 0 := by simp [h, h1, h2]
      rw [hh, hz, mul_zero, C.hr.zero]
      norm_num

theorem chain_ok (C : Ctx u η M fl ex p w) (s3 s1 nb e H w' Os T : ℝ)
    (hs3 : |s3 - 3| ≤ 16 / 1000) (hs1 : |s1 - 1| ≤ 52 / 10000) (hnb : |nb + 3| ≤ 16 / 1000)
    (he : |e - 1| ≤ 52 / 10000) (hH : |H - T| ≤ 50 / 1000) (hT0 : 0 ≤ T) (hT2 : T ≤ 2)
    (hw' : |w' - 1| ≤ 52 / 10000) (hOs : |Os - 1| ≤ 52 / 10000) :
    |fl (Os * fl (w' * relu (gpv fl s3 s1 nb e H))) - T| ≤ 1 / 4 := by
  obtain ⟨hH1, hH2⟩ := abs_le.mp hH
  obtain ⟨he1, he2⟩ := abs_le.mp he
  obtain ⟨hs11, hs12⟩ := abs_le.mp hs1
  obtain ⟨hn1, hn2⟩ := abs_le.mp hnb
  have heb : |e| ≤ 10052 / 10000 := by rw [abs_le]; constructor <;> linarith
  have hHb : |H| ≤ 21 / 10 := by rw [abs_le]; constructor <;> linarith
  have hs1b : |s1| ≤ 10052 / 10000 := by rw [abs_le]; constructor <;> linarith
  have a1 : |s3 * e - 3| ≤ 32 / 1000 := by
    have hh : s3 * e - 3 = (s3 - 3) * e + 3 * (e - 1) := by ring
    rw [hh]
    have t1 := absmul2 hs3 heb
    have t2 := absmul2 (show |(3 : ℝ)| ≤ 3 from le_of_eq (abs_of_pos (by norm_num))) he
    have t3 := abs_add_le ((s3 - 3) * e) (3 * (e - 1))
    linarith
  have a2 : |s1 * H - H| ≤ 11 / 1000 := by
    have hh : s1 * H - H = (s1 - 1) * H := by ring
    rw [hh]
    have := absmul2 hs1 hHb
    linarith
  have hs3e : |s3 * e| ≤ 4 := by
    obtain ⟨q1, q2⟩ := abs_le.mp a1
    rw [abs_le]; constructor <;> linarith
  have hs1H : |s1 * H| ≤ 3 := by
    have := absmul2 hs1b hHb
    linarith
  obtain ⟨f11, f12⟩ := abs_le.mp (flerr C hs3e (by norm_num))
  obtain ⟨f21, f22⟩ := abs_le.mp (flerr C hs1H (by norm_num))
  obtain ⟨a11, a12⟩ := abs_le.mp a1
  obtain ⟨a21, a22⟩ := abs_le.mp a2
  have hsm : |fl (s3 * e) + fl (s1 * H)| ≤ 8 := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨g11, g12⟩ := abs_le.mp (flerr C hsm (by norm_num))
  have hsm2 : |fl (fl (s3 * e) + fl (s1 * H)) + nb| ≤ 12 := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨g21, g22⟩ := abs_le.mp (flerr C hsm2 (by norm_num))
  have hG : |gpv fl s3 s1 nb e H - T| ≤ 12 / 100 := by
    unfold gpv
    rw [abs_le]; constructor <;> linarith
  have hr := relu_near hT0 hG
  obtain ⟨r1, r2⟩ := abs_le.mp hr
  have hrb : |relu (gpv fl s3 s1 nb e H)| ≤ 22 / 10 := by
    rw [abs_le]; constructor <;> linarith
  have hwr : |w' * relu (gpv fl s3 s1 nb e H) - T| ≤ 14 / 100 := by
    have hh : w' * relu (gpv fl s3 s1 nb e H) - T
        = (w' - 1) * relu (gpv fl s3 s1 nb e H) + (relu (gpv fl s3 s1 nb e H) - T) := by ring
    rw [hh]
    have t1 := absmul2 hw' hrb
    have t3 := abs_add_le ((w' - 1) * relu (gpv fl s3 s1 nb e H)) (relu (gpv fl s3 s1 nb e H) - T)
    have hrr : |relu (gpv fl s3 s1 nb e H) - T| ≤ 12 / 100 := hr
    linarith
  have hwrb : |w' * relu (gpv fl s3 s1 nb e H)| ≤ 3 := by
    obtain ⟨q1, q2⟩ := abs_le.mp hwr
    rw [abs_le]; constructor <;> linarith
  obtain ⟨h11, h12⟩ := abs_le.mp (flerr C hwrb (by norm_num))
  obtain ⟨q1, q2⟩ := abs_le.mp hwr
  have hR : |fl (w' * relu (gpv fl s3 s1 nb e H)) - T| ≤ 15 / 100 := by
    rw [abs_le]; constructor <;> linarith
  have hRb : |fl (w' * relu (gpv fl s3 s1 nb e H))| ≤ 23 / 10 := by
    obtain ⟨q3, q4⟩ := abs_le.mp hR
    rw [abs_le]; constructor <;> linarith
  have hos : |Os * fl (w' * relu (gpv fl s3 s1 nb e H)) - T| ≤ 17 / 100 := by
    have hh : Os * fl (w' * relu (gpv fl s3 s1 nb e H)) - T
        = (Os - 1) * fl (w' * relu (gpv fl s3 s1 nb e H))
          + (fl (w' * relu (gpv fl s3 s1 nb e H)) - T) := by ring
    rw [hh]
    have t1 := absmul2 hOs hRb
    have t3 := abs_add_le ((Os - 1) * fl (w' * relu (gpv fl s3 s1 nb e H)))
      (fl (w' * relu (gpv fl s3 s1 nb e H)) - T)
    linarith
  have hosb : |Os * fl (w' * relu (gpv fl s3 s1 nb e H))| ≤ 3 := by
    obtain ⟨q3, q4⟩ := abs_le.mp hos
    rw [abs_le]; constructor <;> linarith
  obtain ⟨k1, k2⟩ := abs_le.mp (flerr C hosb (by norm_num))
  obtain ⟨q3, q4⟩ := abs_le.mp hos
  rw [abs_le]; constructor <;> linarith

theorem inactive (C : Ctx u η M fl ex p w) (s3 s1 nb H : ℝ) (hs1 : |s1 - 1| ≤ 52 / 10000)
    (hnb : |nb + 3| ≤ 16 / 1000) (hH : |H| ≤ 5 / 2) : relu (gpv fl s3 s1 nb 0 H) = 0 := by
  obtain ⟨hs11, hs12⟩ := abs_le.mp hs1
  obtain ⟨hn1, hn2⟩ := abs_le.mp hnb
  obtain ⟨hH1, hH2⟩ := abs_le.mp hH
  have hs1b : |s1| ≤ 10052 / 10000 := by rw [abs_le]; constructor <;> linarith
  have hs1H : |s1 * H| ≤ 3 := by
    have := absmul2 hs1b hH
    linarith
  obtain ⟨f1, f2⟩ := abs_le.mp (flerr C hs1H (by norm_num))
  obtain ⟨p1, p2⟩ := abs_le.mp hs1H
  have hfa : |fl (s1 * H)| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  obtain ⟨g1, g2⟩ := abs_le.mp (flerr C hfa (by norm_num))
  have hM := C.cst 100 (by norm_num)
  obtain ⟨_, hs1Hup⟩ := abs_le.mp (absmul2 hs1b hH)
  unfold gpv
  rw [mul_zero, C.hr.zero, zero_add]
  have hx : fl (fl (s1 * H)) + nb ≤ 0 := by linarith
  apply relu_of_nonpos
  apply C.hr.nonpos hx
  linarith

theorem gRv_act1 (C : Ctx u η M fl ex p w) (wa wb g1 g2 : ℝ) (ha : |wa| ≤ 2) (hg1 : |g1| ≤ 100)
    (hg2 : relu g2 = 0) : gRv fl wa wb g1 g2 = fl (wa * relu g1) := by
  have a1 : |wa * relu g1| ≤ 200 := by
    have := absmul2 ha (le_trans (relu_abs_le g1) hg1); linarith
  have b1 := fl_bd C a1 (by norm_num)
  unfold gRv
  rw [hg2, mul_zero, C.hr.zero, add_zero]
  exact fl_id C (by linarith)

theorem gRv_act2 (C : Ctx u η M fl ex p w) (wa wb g1 g2 : ℝ) (hb : |wb| ≤ 2) (hg2 : |g2| ≤ 100)
    (hg1 : relu g1 = 0) : gRv fl wa wb g1 g2 = fl (wb * relu g2) := by
  have a1 : |wb * relu g2| ≤ 200 := by
    have := absmul2 hb (le_trans (relu_abs_le g2) hg2); linarith
  have b1 := fl_bd C a1 (by norm_num)
  unfold gRv
  rw [hg1, mul_zero, C.hr.zero, zero_add]
  exact fl_id C (by linarith)

/-! ### block 2: MLP and read-out -/

theorem box64 (C : Ctx u η M fl ex p w) (q : ℚ) (hq : (q : ℝ) = 64) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    |sw fl q d - 64| ≤ 33 / 100 := by
  have h := C.swb q 64 64 hq (by norm_num) (by norm_num) hd
  have := C.etaS
  linarith

theorem box512 (C : Ctx u η M fl ex p w) (q : ℚ) (hq : (q : ℝ) = 512) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    |sw fl q d - 512| ≤ 26 / 10 := by
  have h := C.swb q 512 512 hq (by norm_num) (by norm_num) hd
  have := C.etaS
  linarith

theorem box1024 (C : Ctx u η M fl ex p w) (q : ℚ) (hq : (q : ℝ) = 1024) {d : ℝ}
    (hd : |d| ≤ 1 / 200) : |sw fl q d - 1024| ≤ 52 / 10 := by
  have h := C.swb q 1024 1024 hq (by norm_num) (by norm_num) hd
  have := C.etaS
  linarith

theorem box3 (C : Ctx u η M fl ex p w) (q : ℚ) (hq : (q : ℝ) = 3) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    |sw fl q d - 3| ≤ 16 / 1000 := by
  have h := C.swb q 3 3 hq (by norm_num) (by norm_num) hd
  have := C.etaS
  linarith

theorem boxm3 (C : Ctx u η M fl ex p w) (q : ℚ) (hq : (q : ℝ) = -3) {d : ℝ}
    (hd : |d| ≤ 1 / 200) : |sw fl q d + 3| ≤ 16 / 1000 := by
  have h := C.swb q (-3) 3 hq (by norm_num) (by norm_num) hd
  have e : sw fl q d - -3 = sw fl q d + 3 := by ring
  rw [e] at h
  have := C.etaS
  linarith

noncomputable def Rg (fl : ℝ → ℝ) (p : Pert) (e1 e2 Ha Hb : ℝ) : ℝ :=
  gRv fl (sw fl 1 (p.W2 1 10 0)) (sw fl 1 (p.W2 1 10 1))
    (gpv fl (sw fl 3 (p.W1 1 0 0)) (sw fl 1 (p.W1 1 0 8)) (sw fl (-3) (p.b1 1 0)) e1 Ha)
    (gpv fl (sw fl 3 (p.W1 1 1 1)) (sw fl 1 (p.W1 1 1 9)) (sw fl (-3) (p.b1 1 1)) e2 Hb)

theorem abs_of_box {x c e a : ℝ} (h : |x - c| ≤ e) (hc : |c| + e ≤ a) : |x| ≤ a := by
  have := abs_sub_abs_le_abs_sub x c
  linarith

theorem blk2_eq (C : Ctx u η M fl ex p w) (x : ℕ → Vec)
    (hx : ∀ k, k ≤ w.length → x k = X1 fl ex p w k) (i : ℕ) (hi : i ≤ w.length)
    (hHa : fl (Hh fl ex hd2a (p.A 1 0) (p.V 1 0 8) (w.length + 1) i x)
      = Hh fl ex hd2a (p.A 1 0) (p.V 1 0 8) (w.length + 1) i x)
    (hHb : fl (Hh fl ex hd2b (p.A 1 1) (p.V 1 1 9) (w.length + 1) i x)
      = Hh fl ex hd2b (p.A 1 1) (p.V 1 1 9) (w.length + 1) i x)
    (hHa3 : |Hh fl ex hd2a (p.A 1 0) (p.V 1 0 8) (w.length + 1) i x| ≤ 3)
    (hHb3 : |Hh fl ex hd2b (p.A 1 1) (p.V 1 1 9) (w.length + 1) i x| ≤ 3) :
    sblock blk2 fl ex p 1 (w.length + 1) x i
      = [ev1 fl p w i, ev2 fl p w i, evh fl p w i, evb fl p w i,
         Pa fl ex p w e0r (p.V 0 0 4) i, Pa fl ex p w e1r (p.V 0 0 5) i,
         cc1 fl ex p w i, cc2 fl ex p w i,
         Hh fl ex hd2a (p.A 1 0) (p.V 1 0 8) (w.length + 1) i x,
         Hh fl ex hd2b (p.A 1 1) (p.V 1 1 9) (w.length + 1) i x,
         Rg fl p (ev1 fl p w i) (ev2 fl p w i)
           (Hh fl ex hd2a (p.A 1 0) (p.V 1 0 8) (w.length + 1) i x)
           (Hh fl ex hd2b (p.A 1 1) (p.V 1 1 9) (w.length + 1) i x),
         1, fl (i : ℝ), fl ((w.length + 1 : ℕ) : ℝ)] := by
  unfold sblock
  simp only [blk2, sheadsApply, zero_add]
  rw [attn2a_eq (ex := ex) C.hr, attn2b_eq (ex := ex) C.hr, hx i hi]
  generalize Hh fl ex hd2a (p.A 1 0) (p.V 1 0 8) (w.length + 1) i x = Ha at hHa hHa3 ⊢
  generalize Hh fl ex hd2b (p.A 1 1) (p.V 1 1 9) (w.length + 1) i x = Hb at hHb hHb3 ⊢
  obtain ⟨_, _, hP1⟩ := Pa1_all C i hi
  obtain ⟨_, _, hP2⟩ := Pa2_all C i hi
  obtain ⟨_, _, hc1⟩ := cc1_facts C i hi
  obtain ⟨_, _, hc2⟩ := cc2_facts C i hi
  have hs3a := box3 C 3 (by norm_num) (C.hp.W1 1 0 0)
  have hs3b := box3 C 3 (by norm_num) (C.hp.W1 1 1 1)
  have hs1a := w_one_box C _ (C.hp.W1 1 0 8) 1 (by norm_num)
  have hs1b := w_one_box C _ (C.hp.W1 1 1 9) 1 (by norm_num)
  have hnba := boxm3 C (-3) (by norm_num) (C.hp.b1 1 0)
  have hnbb := boxm3 C (-3) (by norm_num) (C.hp.b1 1 1)
  have hwa := w_one_box C _ (C.hp.W2 1 10 0) 1 (by norm_num)
  have hwb := w_one_box C _ (C.hp.W2 1 10 1) 1 (by norm_num)
  have hs3a' : |sw fl 3 (p.W1 1 0 0)| ≤ 6 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hs3a
    rw [abs_le]; constructor <;> linarith
  have hs3b' : |sw fl 3 (p.W1 1 1 1)| ≤ 6 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hs3b
    rw [abs_le]; constructor <;> linarith
  have hs1a' : |sw fl 1 (p.W1 1 0 8)| ≤ 2 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hs1a
    rw [abs_le]; constructor <;> linarith
  have hs1b' : |sw fl 1 (p.W1 1 1 9)| ≤ 2 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hs1b
    rw [abs_le]; constructor <;> linarith
  have hnba' : |sw fl (-3) (p.b1 1 0)| ≤ 6 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hnba
    rw [abs_le]; constructor <;> linarith
  have hnbb' : |sw fl (-3) (p.b1 1 1)| ≤ 6 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hnbb
    rw [abs_le]; constructor <;> linarith
  have hwa' : |sw fl 1 (p.W2 1 10 0)| ≤ 2 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hwa
    rw [abs_le]; constructor <;> linarith
  have hwb' : |sw fl 1 (p.W2 1 10 1)| ≤ 2 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hwb
    rw [abs_le]; constructor <;> linarith
  have hev1 := ev1_b C i
  have hev2 := ev2_b C i
  obtain ⟨hJ1a, hJ1b, hg1⟩ := gpv_facts C _ _ _ (ev1 fl p w i) Ha hs3a' hs1a' hnba'
    (by linarith) hHa3
  obtain ⟨hJ2a, hJ2b, hg2⟩ := gpv_facts C _ _ _ (ev2 fl p w i) Hb hs3b' hs1b' hnbb'
    (by linarith) hHb3
  obtain ⟨hKa, hKb, hKR, hKbd⟩ := gRv_facts C _ _ _ _ hwa' hwb' hg1 hg2
  simp only [gpv, gRv] at hKa hKb hKR
  have hle := tok_le w C.hw i
  have hflp := C.flfl (k := i) (by omega)
  have hflN := C.flfl (k := w.length + 1) le_rfl
  push_cast at hflN
  simp [Rg, gpv, gRv, X1, pos, radd, raffine, rdot, g1r, g2r, w2z, z14, sw_zero C.hr, C.hr.zero,
    C.hr.one, fl_ev1 C i, fl_ev2 C i, fl_evh C i hle, fl_evb C i, hP1, hP2, hc1, hc2, hflp, hflN,
    hHa, hHb, hJ1a, hJ1b, hJ2a, hJ2b, hKa, hKb, hKR]

theorem h_le (t : ℕ) : h t ≤ 2 := by
  unfold h
  split_ifs <;> omega

theorem gate_bounds (C : Ctx u η M fl ex p w) (e1 e2 Ha Hb : ℝ) (he1 : |e1| ≤ 2) (he2 : |e2| ≤ 2)
    (hHa : |Ha| ≤ 3) (hHb : |Hb| ≤ 3) :
    |gpv fl (sw fl 3 (p.W1 1 0 0)) (sw fl 1 (p.W1 1 0 8)) (sw fl (-3) (p.b1 1 0)) e1 Ha| ≤ 100 ∧
    |gpv fl (sw fl 3 (p.W1 1 1 1)) (sw fl 1 (p.W1 1 1 9)) (sw fl (-3) (p.b1 1 1)) e2 Hb| ≤ 100 ∧
    |Rg fl p e1 e2 Ha Hb| ≤ 1000 := by
  have hs3a := box3 C 3 (by norm_num) (C.hp.W1 1 0 0)
  have hs3b := box3 C 3 (by norm_num) (C.hp.W1 1 1 1)
  have hs1a := w_one_box C _ (C.hp.W1 1 0 8) 1 (by norm_num)
  have hs1b := w_one_box C _ (C.hp.W1 1 1 9) 1 (by norm_num)
  have hnba := boxm3 C (-3) (by norm_num) (C.hp.b1 1 0)
  have hnbb := boxm3 C (-3) (by norm_num) (C.hp.b1 1 1)
  have hwa := w_one_box C _ (C.hp.W2 1 10 0) 1 (by norm_num)
  have hwb := w_one_box C _ (C.hp.W2 1 10 1) 1 (by norm_num)
  have hs3a' : |sw fl 3 (p.W1 1 0 0)| ≤ 6 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hs3a
    rw [abs_le]; constructor <;> linarith
  have hs3b' : |sw fl 3 (p.W1 1 1 1)| ≤ 6 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hs3b
    rw [abs_le]; constructor <;> linarith
  have hs1a' : |sw fl 1 (p.W1 1 0 8)| ≤ 2 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hs1a
    rw [abs_le]; constructor <;> linarith
  have hs1b' : |sw fl 1 (p.W1 1 1 9)| ≤ 2 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hs1b
    rw [abs_le]; constructor <;> linarith
  have hnba' : |sw fl (-3) (p.b1 1 0)| ≤ 6 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hnba
    rw [abs_le]; constructor <;> linarith
  have hnbb' : |sw fl (-3) (p.b1 1 1)| ≤ 6 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hnbb
    rw [abs_le]; constructor <;> linarith
  have hwa' : |sw fl 1 (p.W2 1 10 0)| ≤ 2 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hwa
    rw [abs_le]; constructor <;> linarith
  have hwb' : |sw fl 1 (p.W2 1 10 1)| ≤ 2 := by
    obtain ⟨a1, a2⟩ := abs_le.mp hwb
    rw [abs_le]; constructor <;> linarith
  obtain ⟨_, _, hg1⟩ := gpv_facts C _ _ _ e1 Ha hs3a' hs1a' hnba' he1 hHa
  obtain ⟨_, _, hg2⟩ := gpv_facts C _ _ _ e2 Hb hs3b' hs1b' hnbb' he2 hHb
  obtain ⟨_, _, _, hKbd⟩ := gRv_facts C _ _ _ _ hwa' hwb' hg1 hg2
  exact ⟨hg1, hg2, hKbd⟩

set_option maxHeartbeats 4000000 in
theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη p hp w hw hn hnη hM i hi1 hi
  have C : Ctx u η M fl ex p w := ⟨hr, he, hu0, hu1, hη0, hη, hp, hw, hn, hnη, hM, by omega⟩
  obtain ⟨x1, hx1⟩ : ∃ x1 : ℕ → Vec,
      x1 = sblock blk1 fl ex p 0 (w.length + 1) (net.init fl p w) := ⟨_, rfl⟩
  have hx : ∀ k, k ≤ w.length → x1 k = X1 fl ex p w k := fun k hk => by
    rw [hx1]; exact blk1_eq C k hk
  have hηs := C.etaS
  have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 1000 := by norm_num
  -- the stored weights
  have hSa := box64 C 64 (by norm_num) (C.hp.A 1 0 11 12)
  have hBa := box512 C 512 (by norm_num) (C.hp.A 1 0 13 3)
  have hWa := box1024 C 1024 (by norm_num) (C.hp.A 1 0 13 6)
  have hSb := box64 C 64 (by norm_num) (C.hp.A 1 1 11 12)
  have hBb := box512 C 512 (by norm_num) (C.hp.A 1 1 13 3)
  have hWb := box1024 C 1024 (by norm_num) (C.hp.A 1 1 13 7)
  have hcma := w_one_box C _ (C.hp.b2 0 6) 1 (by norm_num)
  have hcmb := w_one_box C _ (C.hp.b2 0 7) 1 (by norm_num)
  have hsva := w_one_box C _ (C.hp.V 1 0 8 2) 1 (by norm_num)
  have hsvb := w_one_box C _ (C.hp.V 1 1 9 2) 1 (by norm_num)
  have hs3a := box3 C 3 (by norm_num) (C.hp.W1 1 0 0)
  have hs3b := box3 C 3 (by norm_num) (C.hp.W1 1 1 1)
  have hs1a := w_one_box C _ (C.hp.W1 1 0 8) 1 (by norm_num)
  have hs1b := w_one_box C _ (C.hp.W1 1 1 9) 1 (by norm_num)
  have hnba := boxm3 C (-3) (by norm_num) (C.hp.b1 1 0)
  have hnbb := boxm3 C (-3) (by norm_num) (C.hp.b1 1 1)
  have hwa := w_one_box C _ (C.hp.W2 1 10 0) 1 (by norm_num)
  have hwb := w_one_box C _ (C.hp.W2 1 10 1) 1 (by norm_num)
  have hOs := w_one_box C _ (C.hp.oW 10) 1 (by norm_num)
  -- the two second-block heads
  have hMa := head2_main C hd2a (p.A 1 0) (p.V 1 0 8) x1 1 (Or.inl rfl) (cc1 fl ex p w)
    _ _ _ _ _ hSa hBa hWa hcma hsva (fun k hk hm => (cc1_facts C k hk).1 hm)
    (fun k hk hm => (cc1_facts C k hk).2.1 hm) i hi (fun k hk => hsk2a C x1 hx i k hi hk)
    (fun k hk => valh_all C x1 hx (p.V 1 0 8) (C.hp.V 1 0 8 2) k hk)
  have hMb := head2_main C hd2b (p.A 1 1) (p.V 1 1 9) x1 2 (Or.inr rfl) (cc2 fl ex p w)
    _ _ _ _ _ hSb hBb hWb hcmb hsvb (fun k hk hm => (cc2_facts C k hk).1 hm)
    (fun k hk hm => (cc2_facts C k hk).2.1 hm) i hi (fun k hk => hsk2b C x1 hx i k hi hk)
    (fun k hk => valh_all C x1 hx (p.V 1 1 9) (C.hp.V 1 1 9 2) k hk)
  obtain ⟨hMa1, hMa2⟩ := hMa
  obtain ⟨hMb1, hMb2⟩ := hMb
  have hfa := fval C _ hsva (win w 1 i) (tok_le w hw _)
  have hfb := fval C _ hsvb (win w 2 i) (tok_le w hw _)
  have hT1 := h_le (tokAt w (win w 1 i))
  have hT2 := h_le (tokAt w (win w 2 i))
  have hT1r : (((h (tokAt w (win w 1 i)) : ℕ)) : ℝ) ≤ 2 := by exact_mod_cast hT1
  have hT2r : (((h (tokAt w (win w 2 i)) : ℕ)) : ℝ) ≤ 2 := by exact_mod_cast hT2
  have hT1n : (0 : ℝ) ≤ (((h (tokAt w (win w 1 i)) : ℕ)) : ℝ) := Nat.cast_nonneg _
  have hT2n : (0 : ℝ) ≤ (((h (tokAt w (win w 2 i)) : ℕ)) : ℝ) := Nat.cast_nonneg _
  obtain ⟨ha1, ha2⟩ := abs_le.mp hMa1
  obtain ⟨hb1, hb2⟩ := abs_le.mp hMb1
  obtain ⟨hfa1, hfa2⟩ := abs_le.mp hfa
  obtain ⟨hfb1, hfb2⟩ := abs_le.mp hfb
  have hHaT : |Hh fl ex hd2a (p.A 1 0) (p.V 1 0 8) (w.length + 1) i x1
      - (((h (tokAt w (win w 1 i)) : ℕ)) : ℝ)| ≤ 50 / 1000 := by
    rw [abs_le]; constructor <;> linarith
  have hHbT : |Hh fl ex hd2b (p.A 1 1) (p.V 1 1 9) (w.length + 1) i x1
      - (((h (tokAt w (win w 2 i)) : ℕ)) : ℝ)| ≤ 50 / 1000 := by
    rw [abs_le]; constructor <;> linarith
  have hHa3 : |Hh fl ex hd2a (p.A 1 0) (p.V 1 0 8) (w.length + 1) i x1| ≤ 5 / 2 := by
    obtain ⟨q1, q2⟩ := abs_le.mp hHaT
    rw [abs_le]; constructor <;> linarith
  have hHb3 : |Hh fl ex hd2b (p.A 1 1) (p.V 1 1 9) (w.length + 1) i x1| ≤ 5 / 2 := by
    obtain ⟨q1, q2⟩ := abs_le.mp hHbT
    rw [abs_le]; constructor <;> linarith
  have hblk2 := blk2_eq C x1 hx i hi hMa2 hMb2 (le_trans hHa3 (by norm_num))
    (le_trans hHb3 (by norm_num))
  have hev1 := ev1_b C i
  have hev2 := ev2_b C i
  obtain ⟨hg1, hg2, hRb⟩ := gate_bounds C (ev1 fl p w i) (ev2 fl p w i) _ _ (by linarith)
    (by linarith) (le_trans hHa3 (by norm_num)) (le_trans hHb3 (by norm_num))
  have hO : fl (fl (sw fl 1 (p.oW 10) * Rg fl p (ev1 fl p w i) (ev2 fl p w i)
      (Hh fl ex hd2a (p.A 1 0) (p.V 1 0 8) (w.length + 1) i x1)
      (Hh fl ex hd2b (p.A 1 1) (p.V 1 1 9) (w.length + 1) i x1)))
      = fl (sw fl 1 (p.oW 10) * Rg fl p (ev1 fl p w i) (ev2 fl p w i)
      (Hh fl ex hd2a (p.A 1 0) (p.V 1 0 8) (w.length + 1) i x1)
      (Hh fl ex hd2b (p.A 1 1) (p.V 1 1 9) (w.length + 1) i x1)) := by
    apply fl_id C
    have hOb : |sw fl 1 (p.oW 10)| ≤ 2 := by
      obtain ⟨a1, a2⟩ := abs_le.mp hOs
      rw [abs_le]; constructor <;> linarith
    have := absmul2 hOb hRb
    linarith
  have hsout : sout net fl ex p w i = fl (sw fl 1 (p.oW 10) * Rg fl p (ev1 fl p w i) (ev2 fl p w i)
      (Hh fl ex hd2a (p.A 1 0) (p.V 1 0 8) (w.length + 1) i x1)
      (Hh fl ex hd2b (p.A 1 1) (p.V 1 1 9) (w.length + 1) i x1)) := by
    unfold sout srun
    have hb : net.blocks = [blk1, blk2] := rfl
    rw [hb]
    simp only [srunFrom, zero_add]
    rw [← hx1, hblk2]
    simp [net, rdot, sw_zero C.hr, C.hr.zero, hO]
  have ht1 := tok_pos w hw hi1 hi
  have ht2 := tok_le w hw i
  have htarget : target w i = h (tokAt w (win w (tokAt w i) i)) := target_eq w i (by omega)
  rw [hsout, htarget]
  rcases (by omega : tokAt w i = 1 ∨ tokAt w i = 2) with ht | ht
  · rw [ht]
    have hev2z : ev2 fl p w i = 0 := ev2_non C i (by omega)
    have hinact := inactive C (sw fl 3 (p.W1 1 1 1)) (sw fl 1 (p.W1 1 1 9))
      (sw fl (-3) (p.b1 1 1))
      (Hh fl ex hd2b (p.A 1 1) (p.V 1 1 9) (w.length + 1) i x1) hs1b hnbb hHb3
    have hwa' : |sw fl 1 (p.W2 1 10 0)| ≤ 2 := by
      obtain ⟨a1, a2⟩ := abs_le.mp hwa
      rw [abs_le]; constructor <;> linarith
    have hRg : Rg fl p (ev1 fl p w i) (ev2 fl p w i)
        (Hh fl ex hd2a (p.A 1 0) (p.V 1 0 8) (w.length + 1) i x1)
        (Hh fl ex hd2b (p.A 1 1) (p.V 1 1 9) (w.length + 1) i x1)
        = fl (sw fl 1 (p.W2 1 10 0) * relu (gpv fl (sw fl 3 (p.W1 1 0 0))
          (sw fl 1 (p.W1 1 0 8)) (sw fl (-3) (p.b1 1 0)) (ev1 fl p w i)
          (Hh fl ex hd2a (p.A 1 0) (p.V 1 0 8) (w.length + 1) i x1))) := by
      unfold Rg
      rw [hev2z]
      exact gRv_act1 C _ _ _ _ hwa' hg1 hinact
    rw [hRg]
    exact chain_ok C _ _ _ _ _ _ _ _ hs3a hs1a hnba (ev1_one C i ht) hHaT hT1n hT1r hwa hOs
  · rw [ht]
    have hev1z : ev1 fl p w i = 0 := ev1_non C i (by omega)
    have hinact := inactive C (sw fl 3 (p.W1 1 0 0)) (sw fl 1 (p.W1 1 0 8))
      (sw fl (-3) (p.b1 1 0))
      (Hh fl ex hd2a (p.A 1 0) (p.V 1 0 8) (w.length + 1) i x1) hs1a hnba hHa3
    have hwb' : |sw fl 1 (p.W2 1 10 1)| ≤ 2 := by
      obtain ⟨a1, a2⟩ := abs_le.mp hwb
      rw [abs_le]; constructor <;> linarith
    have hRg : Rg fl p (ev1 fl p w i) (ev2 fl p w i)
        (Hh fl ex hd2a (p.A 1 0) (p.V 1 0 8) (w.length + 1) i x1)
        (Hh fl ex hd2b (p.A 1 1) (p.V 1 1 9) (w.length + 1) i x1)
        = fl (sw fl 1 (p.W2 1 10 1) * relu (gpv fl (sw fl 3 (p.W1 1 1 1))
          (sw fl 1 (p.W1 1 1 9)) (sw fl (-3) (p.b1 1 1)) (ev2 fl p w i)
          (Hh fl ex hd2b (p.A 1 1) (p.V 1 1 9) (w.length + 1) i x1))) := by
      unfold Rg
      rw [hev1z]
      exact gRv_act2 C _ _ _ _ hwb' hg2 hinact
    rw [hRg]
    exact chain_ok C _ _ _ _ _ _ _ _ hs3b hs1b hnbb (ev2_one C i ht) hHbT hT2n hT2r hwb hOs

end

end Lane4.Case
