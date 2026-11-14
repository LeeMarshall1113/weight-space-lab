set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

/-! ### Weights -/

def z15 : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def e0 : List ℚ := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def e1 : List ℚ := [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def e2 : List ℚ := [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def e3 : List ℚ := [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def ra : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
def rb : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 / 4, 0]
def rc1 : List ℚ := [0, 0, 0, 0, 1 / 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def rc2 : List ℚ := [0, 0, 0, 0, 1 / 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
def rc3 : List ℚ := [0, 0, 0, 0, 1 / 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
def w1a : List ℚ := [3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
def w1b : List ℚ := [0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
def w1c : List ℚ := [0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
def w2z : List ℚ := [0, 0, 0]
def w2o : List ℚ := [1, 1, 1]

def hdP : Head :=
  { A := [z15, z15, z15, z15, z15, z15, z15, z15, z15, z15, z15, z15, ra, z15, z15],
    V := [z15, z15, z15, z15, z15, e0, e1, e2, z15, z15, z15, z15, z15, z15, z15],
    mask := Mask.strict }

def hd1 : Head :=
  { A := [z15, z15, z15, z15, z15, z15, z15, z15, z15, z15, z15, z15, rb, rc1, z15],
    V := [z15, z15, z15, z15, z15, z15, z15, z15, e3, z15, z15, z15, z15, z15, z15],
    mask := Mask.causal }

def hd2 : Head :=
  { A := [z15, z15, z15, z15, z15, z15, z15, z15, z15, z15, z15, z15, rb, rc2, z15],
    V := [z15, z15, z15, z15, z15, z15, z15, z15, z15, e3, z15, z15, z15, z15, z15],
    mask := Mask.causal }

def hd3 : Head :=
  { A := [z15, z15, z15, z15, z15, z15, z15, z15, z15, z15, z15, z15, rb, rc3, z15],
    V := [z15, z15, z15, z15, z15, z15, z15, z15, z15, z15, e3, z15, z15, z15, z15],
    mask := Mask.causal }

theorem hdP_V : hdP.V = [z15, z15, z15, z15, z15, e0, e1, e2, z15, z15, z15, z15, z15, z15, z15] := rfl
theorem hd1_V : hd1.V = [z15, z15, z15, z15, z15, z15, z15, z15, e3, z15, z15, z15, z15, z15, z15] := rfl
theorem hd2_V : hd2.V = [z15, z15, z15, z15, z15, z15, z15, z15, z15, e3, z15, z15, z15, z15, z15] := rfl
theorem hd3_V : hd3.V = [z15, z15, z15, z15, z15, z15, z15, z15, z15, z15, e3, z15, z15, z15, z15] := rfl

def blk1 : Block :=
  { heads := [hdP], W1 := [], b1 := [],
    W2 := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], []],
    b2 := z15 }

def blk2 : Block :=
  { heads := [hd1, hd2, hd3],
    W1 := [w1a, w1b, w1c],
    b1 := [-3, -3, -3],
    W2 := [w2z, w2z, w2z, w2z, w2z, w2z, w2z, w2z, w2z, w2z, w2z, w2o, w2z, w2z, w2z],
    b2 := z15 }

def net : TNet :=
  { embed := [[0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
              [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]],
    blocks := [blk1, blk2],
    outW := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    outB := 0 }

/-! ### States -/

structure St where
  a0 : ℝ
  a1 : ℝ
  a2 : ℝ
  a3 : ℝ
  a4 : ℝ
  a5 : ℝ
  a6 : ℝ
  a7 : ℝ
  r1 : ℝ
  r2 : ℝ
  r3 : ℝ
  o : ℝ
  fq : ℝ
  pn : ℝ

noncomputable def St.v (s : St) : Vec :=
  [s.a0, s.a1, s.a2, s.a3, s.a4, s.a5, s.a6, s.a7, s.r1, s.r2, s.r3, s.o, 1, s.fq, s.pn]

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) : tokAt w j ≤ 3 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h0 | hm
  · omega
  · exact (hw _ hm).2

theorem tok_pos (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : j ≤ w.length) : 1 ≤ tokAt w j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Lane4.Seq.tokAt_succ w k (by omega)]
  exact (hw _ (List.getElem_mem (by omega))).1

/-- Initial state at position `j`. -/
noncomputable def S0 (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : St where
  a0 := if tokAt w j = 1 then sw fl 1 (p.E 1 0) else 0
  a1 := if tokAt w j = 2 then sw fl 1 (p.E 2 1) else 0
  a2 := if tokAt w j = 3 then sw fl 1 (p.E 3 2) else 0
  a3 := sw fl ((h (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 3)
  a4 := if tokAt w j = 0 then sw fl 1 (p.E 0 4) else 0
  a5 := 0
  a6 := 0
  a7 := 0
  r1 := 0
  r2 := 0
  r3 := 0
  o := 0
  fq := fl (j : ℝ)
  pn := fl ((w.length + 1 : ℕ) : ℝ)

theorem S0_fq {fl : ℝ → ℝ} {p : Pert} {w : List ℕ} {j : ℕ} : (S0 fl p w j).fq = fl (j : ℝ) := rfl

theorem S0_z (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) :
    (S0 fl p w j).a5 = 0 ∧ (S0 fl p w j).a6 = 0 ∧ (S0 fl p w j).a7 = 0 ∧
    (S0 fl p w j).r1 = 0 ∧ (S0 fl p w j).r2 = 0 ∧ (S0 fl p w j).r3 = 0 ∧
    (S0 fl p w j).o = 0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem S0_zero0 {fl : ℝ → ℝ} (p : Pert) (w : List ℕ) :
    (S0 fl p w 0).a0 = 0 ∧ (S0 fl p w 0).a1 = 0 ∧ (S0 fl p w 0).a2 = 0 := by
  simp [S0, Lane4.Seq.tokAt_zero]

theorem S0_fix {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ) :
    fl (S0 fl p w j).a0 = (S0 fl p w j).a0 ∧ fl (S0 fl p w j).a1 = (S0 fl p w j).a1 ∧
    fl (S0 fl p w j).a2 = (S0 fl p w j).a2 ∧ fl (S0 fl p w j).a3 = (S0 fl p w j).a3 ∧
    fl (S0 fl p w j).a4 = (S0 fl p w j).a4 ∧ fl (S0 fl p w j).fq = (S0 fl p w j).fq ∧
    fl (S0 fl p w j).pn = (S0 fl p w j).pn := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show fl (if tokAt w j = 1 then sw fl 1 (p.E 1 0) else 0) =
      if tokAt w j = 1 then sw fl 1 (p.E 1 0) else 0
    split_ifs
    · exact fl_sw hr _ _
    · exact hr.zero
  · show fl (if tokAt w j = 2 then sw fl 1 (p.E 2 1) else 0) =
      if tokAt w j = 2 then sw fl 1 (p.E 2 1) else 0
    split_ifs
    · exact fl_sw hr _ _
    · exact hr.zero
  · show fl (if tokAt w j = 3 then sw fl 1 (p.E 3 2) else 0) =
      if tokAt w j = 3 then sw fl 1 (p.E 3 2) else 0
    split_ifs
    · exact fl_sw hr _ _
    · exact hr.zero
  · exact fl_sw hr _ _
  · show fl (if tokAt w j = 0 then sw fl 1 (p.E 0 4) else 0) =
      if tokAt w j = 0 then sw fl 1 (p.E 0 4) else 0
    split_ifs
    · exact fl_sw hr _ _
    · exact hr.zero
  · exact hr.idem _
  · exact hr.idem _

theorem init_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) : net.init fl p w j = (S0 fl p w j).v := by
  have h4 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 := by
    have := tok_le w hw j
    omega
  rcases h4 with hs | hs | hs | hs <;>
    simp [TNet.init, net, S0, St.v, swRow, pos, hs, h, sw_zero hr]

/-! ### Block 1: previous token -/

theorem scoreP {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ) (s s' : St) :
    hdP.score fl dA s.v s'.v = fl (sw fl 1 (dA 12 13) * s'.fq) := by
  simp [Head.score, hdP, z15, ra, St.v, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem, hr.one]

theorem selP {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (q : ℕ) (hq1 : 1 ≤ q) (hq : q ≤ w.length) :
    hdP.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) q = [q - 1] := by
  apply Head.sel_unique
  · rw [show hdP.mask = Mask.strict from rfl, Lane4.Seq.mem_cand_strict]
    omega
  · intro k hk hne
    rw [show hdP.mask = Mask.strict from rfl, Lane4.Seq.mem_cand_strict] at hk
    simp only [init_eq hr p w hw]
    rw [scoreP hr, scoreP hr]
    simp only [S0_fq]
    have hS := sw_rel hr hu0 1 (hp.A 0 0 12 13) (ε := 3 / 250) (by linarith)
    simp only [Rat.cast_one, abs_one, mul_one] at hS
    obtain ⟨hS1, hS2⟩ := abs_le.mp hS
    have hS0 : 0 ≤ sw fl 1 (p.A 0 0 12 13) := by linarith
    have hg := hr.pos_gap hu0 (show k < q - 1 by omega) (show q - 1 ≤ w.length + 1 by omega) hn
    have hk' := hr.pos_le hu0 (show k ≤ w.length + 1 by omega) hn
    have hj' := hr.pos_le hu0 (show q - 1 ≤ w.length + 1 by omega) hn
    apply hr.lt_of_gap hu0 (B := 2 * (((w.length + 1 : ℕ) : ℝ) + 1 / 256))
    · rw [abs_of_nonneg (mul_nonneg hS0 hk'.1)]
      exact mul_le_mul (by linarith) hk'.2 hk'.1 (by norm_num)
    · rw [abs_of_nonneg (mul_nonneg hS0 hj'.1)]
      exact mul_le_mul (by linarith) hj'.2 hj'.1 (by norm_num)
    · have h1 := mul_le_mul_of_nonneg_left hg hS0
      nlinarith [h1, hn, hu0, hu1, hS1]

/-- State after block 1. -/
noncomputable def S1 (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (q : ℕ) : St :=
  { S0 fl p w q with
    a5 := fl (sw fl 1 (p.V 0 0 5 0) * (S0 fl p w (q - 1)).a0)
    a6 := fl (sw fl 1 (p.V 0 0 6 1) * (S0 fl p w (q - 1)).a1)
    a7 := fl (sw fl 1 (p.V 0 0 7 2) * (S0 fl p w (q - 1)).a2) }

theorem S1_fq {fl : ℝ → ℝ} {p : Pert} {w : List ℕ} {q : ℕ} : (S1 fl p w q).fq = fl (q : ℝ) := rfl

noncomputable def X1 (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) : ℕ → Vec :=
  blk1.apply fl p 0 (w.length + 1) (net.init fl p w)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem blk1_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (q : ℕ) (hq1 : 1 ≤ q) (hq : q ≤ w.length) :
    blk1.apply fl p 0 (w.length + 1) (net.init fl p w) q = (S1 fl p w q).v := by
  have hsel := selP hr hu0 hu1 p hp w hw hn q hq1 hq
  obtain ⟨f0, f1, f2, f3, f4, ffq, ffn⟩ := S0_fix hr p w q
  obtain ⟨z5, z6, z7, zr1, zr2, zr3, zo⟩ := S0_z fl p w q
  simp only [Block.apply, blk1, headsApply, Head.attn, hsel, hdP_V, attnRows, ravg_singleton hr]
  simp only [init_eq hr p w hw]
  simp [St.v, S1, z15, e0, e1, e2, radd, raffine, rdot, sw_zero hr, hr.zero, hr.idem, hr.one,
    f0, f1, f2, f3, f4, ffq, ffn, z5, z6, z7, zr1, zr2, zr3, zo]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem blk1_eq0 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) :
    blk1.apply fl p 0 (w.length + 1) (net.init fl p w) 0 = (S1 fl p w 0).v := by
  have hsel : hdP.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) 0 = [] := by
    simp [Head.sel, selOf, hdP, Lane4.Seq.cand]
  obtain ⟨f0, f1, f2, f3, f4, ffq, ffn⟩ := S0_fix hr p w 0
  obtain ⟨z5, z6, z7, zr1, zr2, zr3, zo⟩ := S0_z fl p w 0
  obtain ⟨y0, y1, y2⟩ := S0_zero0 (fl := fl) p w
  simp only [Block.apply, blk1, headsApply, Head.attn, hsel, hdP_V, attnRows]
  simp only [init_eq hr p w hw]
  simp [St.v, S1, z15, ravg, rsum, radd, raffine, rdot, sw_zero hr, hr.zero, hr.idem, hr.one,
    f0, f1, f2, f3, f4, ffq, ffn, z5, z6, z7, zr1, zr2, zr3, zo, y0, y1, y2]

theorem X1_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (q : ℕ) (hq : q ≤ w.length) : X1 fl p w q = (S1 fl p w q).v := by
  unfold X1
  rcases Nat.eq_zero_or_pos q with h0 | hpos
  · subst h0
    exact blk1_eq0 hr p w hw
  · exact blk1_eq hr hu0 hu1 p hp w hw hn q hpos hq

/-! ### Scores of block 2 -/

noncomputable def sc (fl : ℝ → ℝ) (α β γ I fk a4 pk : ℝ) : ℝ :=
  fl (fl (α * fk) + fl (I * fl (fl (β * a4) + fl (γ * pk))))

theorem sc_U {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (α β γ I fk : ℝ) :
    sc fl α β γ I fk 0 0 = fl (α * fk) := by
  simp [sc, hr.zero, hr.idem]

theorem sc_M {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (α β γ I fk π : ℝ) :
    sc fl α β γ I fk 0 π = fl (fl (α * fk) + fl (I * fl (γ * π))) := by
  simp [sc, hr.zero, hr.idem]

theorem sc_B {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (α β γ I b : ℝ) :
    sc fl α β γ I 0 b 0 = fl (I * fl (β * b)) := by
  simp [sc, hr.zero, hr.idem]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem score1 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ) (s s' : St) :
    hd1.score fl dA s.v s'.v = sc fl (sw fl (1 / 4) (dA 12 13)) (sw fl (1 / 2) (dA 13 4))
      (sw fl 1 (dA 13 5)) s.fq s'.fq s'.a4 s'.a5 := by
  simp [Head.score, hd1, z15, rb, rc1, St.v, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem,
    hr.one, sc]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem score2 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ) (s s' : St) :
    hd2.score fl dA s.v s'.v = sc fl (sw fl (1 / 4) (dA 12 13)) (sw fl (1 / 2) (dA 13 4))
      (sw fl 1 (dA 13 6)) s.fq s'.fq s'.a4 s'.a6 := by
  simp [Head.score, hd2, z15, rb, rc2, St.v, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem,
    hr.one, sc]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem score3 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ) (s s' : St) :
    hd3.score fl dA s.v s'.v = sc fl (sw fl (1 / 4) (dA 12 13)) (sw fl (1 / 2) (dA 13 4))
      (sw fl 1 (dA 13 7)) s.fq s'.fq s'.a4 s'.a7 := by
  simp [Head.score, hd3, z15, rb, rc3, St.v, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem,
    hr.one, sc]

/-! ### Real-number lemmas about stored weights -/

theorem sw_eps {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (w : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 200) :
    |sw fl w d - (w : ℝ)| ≤ 1 / 199 * |(w : ℝ)| :=
  sw_rel hr hu0 w hd (by linarith)

theorem sw_ge {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (w : ℚ) (x : ℝ) (hx : (w : ℝ) = x) (hx0 : 0 ≤ x) {d : ℝ}
    (hd : |d| ≤ 1 / 200) : x * (198 / 199) ≤ sw fl w d ∧ sw fl w d ≤ x * (200 / 199) := by
  have h1 := sw_eps hr hu0 hu1 w hd
  rw [hx, abs_of_nonneg hx0] at h1
  obtain ⟨h2, h3⟩ := abs_le.mp h1
  constructor <;> linarith

theorem sw1_near {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {d : ℝ} (hd : |d| ≤ 1 / 200) : |sw fl 1 d - 1| ≤ 1 / 199 := by
  have h1 := sw_eps hr hu0 hu1 1 hd
  simp only [Rat.cast_one, abs_one, mul_one] at h1
  exact h1

theorem sw3_near {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {d : ℝ} (hd : |d| ≤ 1 / 200) : |sw fl 3 d - 3| ≤ 3 / 199 := by
  have h1 := sw_eps hr hu0 hu1 3 hd
  have e : ((3 : ℚ) : ℝ) = 3 := by norm_num
  rw [e, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at h1
  obtain ⟨h2, h3⟩ := abs_le.mp h1
  rw [abs_le]
  constructor <;> linarith

theorem swm3_near {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {d : ℝ} (hd : |d| ≤ 1 / 200) : |sw fl (-3) d + 3| ≤ 3 / 199 := by
  have h1 := sw_eps hr hu0 hu1 (-3) hd
  have e : ((-3 : ℚ) : ℝ) = -3 := by norm_num
  rw [e, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at h1
  obtain ⟨h2, h3⟩ := abs_le.mp h1
  rw [abs_le]
  constructor <;> linarith

/-! ### Score ordering -/

def Bnds (u α β γ b π I : ℝ) : Prop :=
  248 / 1000 ≤ α ∧ α ≤ 252 / 1000 ∧ 497 / 1000 ≤ β ∧ β ≤ 503 / 1000 ∧
  994 / 1000 ≤ γ ∧ γ ≤ 1006 / 1000 ∧ 994 / 1000 ≤ b ∧ b ≤ 1006 / 1000 ∧
  987 / 1000 ≤ π ∧ π ≤ 1013 / 1000 ∧ 1 ≤ I ∧ u * I ≤ 1 / 250

theorem Bnds_I {u α β γ b π I : ℝ} (hB : Bnds u α β γ b π I) : 1 ≤ I ∧ u * I ≤ 1 / 250 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h1, h2⟩ := hB
  exact ⟨h1, h2⟩

theorem errI {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) {I x c : ℝ}
    (hc : 0 ≤ c) (hI : u * I ≤ 1 / 250) (hx : |x| ≤ c * I) : |fl x - x| ≤ c / 250 := by
  have h1 := hr.err hu0 hx
  have h2 : u * (c * I) ≤ c / 250 := by
    have h3 := mul_le_mul_of_nonneg_left hI hc
    nlinarith [h3]
  linarith

theorem E_bnd {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    {α β γ b π I fk : ℝ} (hB : Bnds u α β γ b π I) (hfk0 : 0 ≤ fk) (hfk : fk ≤ I) :
    0 ≤ fl (α * fk) ∧ fl (α * fk) ≤ 252 / 1000 * fk + 11 / 10000 ∧
    α * fk - 11 / 10000 ≤ fl (α * fk) ∧ fl (α * fk) ≤ α * fk + 11 / 10000 := by
  obtain ⟨hα1, hα2, hβ1, hβ2, hγ1, hγ2, hb1, hb2, hπ1, hπ2, hI1, hI⟩ := hB
  have h0 : 0 ≤ α * fk := mul_nonneg (by linarith) hfk0
  have h1 : α * fk ≤ 252 / 1000 * fk := mul_le_mul_of_nonneg_right hα2 hfk0
  have h2 : α * fk ≤ 252 / 1000 * I := by linarith
  have h3 := abs_le.mp (errI hr hu0 (c := 252 / 1000) (x := α * fk) (by norm_num) hI
    (abs_le.mpr ⟨by linarith, h2⟩))
  refine ⟨hr.nonneg h0, by linarith [h3.2], by linarith [h3.1], by linarith [h3.2]⟩

theorem cB_bnd {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {α β γ b π I : ℝ} (hB : Bnds u α β γ b π I) :
    494 / 1000 * I - 21 / 10000 ≤ fl (I * fl (β * b)) ∧
    fl (I * fl (β * b)) ≤ 5061 / 10000 * I + 21 / 10000 := by
  obtain ⟨hα1, hα2, hβ1, hβ2, hγ1, hγ2, hb1, hb2, hπ1, hπ2, hI1, hI⟩ := hB
  have hg1 : 497 / 1000 * (994 / 1000) ≤ β * b := mul_le_mul hβ1 hb1 (by norm_num) (by linarith)
  have hg2 : β * b ≤ 503 / 1000 * (1006 / 1000) := mul_le_mul hβ2 hb2 (by linarith) (by norm_num)
  have hG := abs_le.mp (hr.err hu0 (x := β * b) (B := 1)
    (abs_le.mpr ⟨by linarith, by linarith⟩))
  have hGl : 494 / 1000 ≤ fl (β * b) := by linarith [hG.1]
  have hGu : fl (β * b) ≤ 5061 / 10000 := by linarith [hG.2]
  have hm1 : I * (494 / 1000) ≤ I * fl (β * b) := mul_le_mul_of_nonneg_left hGl (by linarith)
  have hm2 : I * fl (β * b) ≤ I * (5061 / 10000) := mul_le_mul_of_nonneg_left hGu (by linarith)
  have h3 := abs_le.mp (errI hr hu0 (c := 51 / 100) (x := I * fl (β * b)) (by norm_num) hI
    (abs_le.mpr ⟨by linarith, by linarith⟩))
  constructor <;> linarith [h3.1, h3.2]

theorem cM_bnd {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {α β γ b π I : ℝ} (hB : Bnds u α β γ b π I) :
    981 / 1000 * I - 41 / 10000 ≤ fl (I * fl (γ * π)) ∧
    fl (I * fl (γ * π)) ≤ 10191 / 10000 * I + 41 / 10000 := by
  obtain ⟨hα1, hα2, hβ1, hβ2, hγ1, hγ2, hb1, hb2, hπ1, hπ2, hI1, hI⟩ := hB
  have hg1 : 994 / 1000 * (987 / 1000) ≤ γ * π := mul_le_mul hγ1 hπ1 (by norm_num) (by linarith)
  have hg2 : γ * π ≤ 1006 / 1000 * (1013 / 1000) := mul_le_mul hγ2 hπ2 (by linarith) (by norm_num)
  have hG := abs_le.mp (hr.err hu0 (x := γ * π) (B := 2)
    (abs_le.mpr ⟨by linarith, by linarith⟩))
  have hGl : 981 / 1000 ≤ fl (γ * π) := by linarith [hG.1]
  have hGu : fl (γ * π) ≤ 10191 / 10000 := by linarith [hG.2]
  have hm1 : I * (981 / 1000) ≤ I * fl (γ * π) := mul_le_mul_of_nonneg_left hGl (by linarith)
  have hm2 : I * fl (γ * π) ≤ I * (10191 / 10000) := mul_le_mul_of_nonneg_left hGu (by linarith)
  have h3 := abs_le.mp (errI hr hu0 (c := 102 / 100) (x := I * fl (γ * π)) (by norm_num) hI
    (abs_le.mpr ⟨by linarith, by linarith⟩))
  constructor <;> linarith [h3.1, h3.2]

theorem M_lower {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {α β γ b π I fk : ℝ} (hB : Bnds u α β γ b π I) (hfk0 : 0 ≤ fk)
    (hfk : fk ≤ I) : 981 / 1000 * I - 97 / 10000 ≤ fl (fl (α * fk) + fl (I * fl (γ * π))) := by
  have hE := E_bnd hr hu0 hB hfk0 hfk
  have hM := cM_bnd hr hu0 hu1 hB
  obtain ⟨hI1, hI⟩ := Bnds_I hB
  have hx : |fl (α * fk) + fl (I * fl (γ * π))| ≤ 14 / 10 * I := by
    rw [abs_le]
    constructor <;> linarith [hE.1, hE.2.1, hM.1, hM.2]
  have h3 := abs_le.mp (errI hr hu0 (c := 14 / 10) (x := fl (α * fk) + fl (I * fl (γ * π)))
    (by norm_num) hI hx)
  linarith [h3.1, hM.1, hE.1]

theorem M_lt {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {α β γ b π I fk fk' : ℝ} (hB : Bnds u α β γ b π I)
    (hfk' : 0 ≤ fk') (hgap : fk' + 127 / 128 ≤ fk) (hfk : fk ≤ I) :
    fl (fl (α * fk') + fl (I * fl (γ * π))) < fl (fl (α * fk) + fl (I * fl (γ * π))) := by
  have hfk0 : 0 ≤ fk := by linarith
  have hE := E_bnd hr hu0 hB hfk0 hfk
  have hE' := E_bnd hr hu0 hB hfk' (by linarith)
  have hM := cM_bnd hr hu0 hu1 hB
  obtain ⟨hI1, hI⟩ := Bnds_I hB
  obtain ⟨hα1, hα2, _, _, _, _, _, _, _, _, _, _⟩ := hB
  have hd : α * (127 / 128) ≤ α * (fk - fk') :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hxa : |fl (α * fk') + fl (I * fl (γ * π))| ≤ 14 / 10 * I := by
    rw [abs_le]
    constructor <;> linarith [hE'.1, hE'.2.1, hM.1, hM.2]
  have hxb : |fl (α * fk) + fl (I * fl (γ * π))| ≤ 14 / 10 * I := by
    rw [abs_le]
    constructor <;> linarith [hE.1, hE.2.1, hM.1, hM.2]
  apply hr.lt_of_gap hu0 (B := 14 / 10 * I) hxa hxb
  have hu' : u * (14 / 10 * I) ≤ 14 / 10 * (1 / 250) := by nlinarith [hI]
  nlinarith [hE.2.2.1, hE'.2.2.2, hd, hu', hα1]

theorem U_lt_B {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {α β γ b π I fk : ℝ} (hB : Bnds u α β γ b π I) (hfk0 : 0 ≤ fk)
    (hfk : fk ≤ I) : fl (α * fk) < fl (I * fl (β * b)) := by
  have hE := E_bnd hr hu0 hB hfk0 hfk
  have hC := cB_bnd hr hu0 hu1 hB
  obtain ⟨hI1, hI⟩ := Bnds_I hB
  linarith [hE.2.1, hC.1]

theorem B_lt_M {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {α β γ b π I fk : ℝ} (hB : Bnds u α β γ b π I) (hfk0 : 0 ≤ fk)
    (hfk : fk ≤ I) :
    fl (I * fl (β * b)) < fl (fl (α * fk) + fl (I * fl (γ * π))) := by
  have hC := cB_bnd hr hu0 hu1 hB
  have hL := M_lower hr hu0 hu1 hB hfk0 hfk
  obtain ⟨hI1, hI⟩ := Bnds_I hB
  linarith [hC.2, hL]

theorem U_lt_M {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {α β γ b π I fk fk2 : ℝ} (hB : Bnds u α β γ b π I)
    (hfk0 : 0 ≤ fk) (hfk : fk ≤ I) (hfk20 : 0 ≤ fk2) (hfk2 : fk2 ≤ I) :
    fl (α * fk) < fl (fl (α * fk2) + fl (I * fl (γ * π))) := by
  have hE := E_bnd hr hu0 hB hfk0 hfk
  have hL := M_lower hr hu0 hu1 hB hfk20 hfk2
  obtain ⟨hI1, hI⟩ := Bnds_I hB
  linarith [hE.2.1, hL]

/-! ### The selection of a head of block 2 -/

theorem exists_last (P : ℕ → Prop) (i : ℕ) (h : ∃ k, k ≤ i ∧ P k) :
    ∃ q, q ≤ i ∧ P q ∧ ∀ k, q < k → k ≤ i → ¬ P k := by
  classical
  induction i with
  | zero =>
    obtain ⟨k, hk, hPk⟩ := h
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨0, le_refl _, hPk, fun k h1 h2 => by omega⟩
  | succ m ih =>
    by_cases hm : P (m + 1)
    · exact ⟨m + 1, le_refl _, hm, fun k h1 h2 => by omega⟩
    · obtain ⟨k, hk, hPk⟩ := h
      have hk' : k ≤ m := by
        rcases Nat.lt_or_ge k (m + 1) with h1 | h1
        · omega
        · have hkm : k = m + 1 := by omega
          subst hkm
          exact absurd hPk hm
      obtain ⟨q, hq, hPq, hmax⟩ := ih ⟨k, hk', hPk⟩
      refine ⟨q, by omega, hPq, fun k' h1 h2 => ?_⟩
      by_cases hk2 : k' = m + 1
      · subst hk2
        exact hm
      · exact hmax k' h1 (by omega)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem sel2 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (hd : Head) (hmask : hd.mask = Mask.causal) (dA : ℕ → ℕ → ℝ)
    (hdA : ∀ r c, |dA r c| ≤ 1 / 200) (t ci : ℕ) (ht : 1 ≤ t) (pf : St → ℝ) (π : ℝ)
    (hπ1 : 987 / 1000 ≤ π) (hπ2 : π ≤ 1013 / 1000)
    (hscore : ∀ s s' : St, hd.score fl dA s.v s'.v =
      sc fl (sw fl (1 / 4) (dA 12 13)) (sw fl (1 / 2) (dA 13 4)) (sw fl 1 (dA 13 ci))
        s.fq s'.fq s'.a4 (pf s'))
    (hpf : ∀ k, k ≤ w.length → pf (S1 fl p w k) = if tokAt w (k - 1) = t then π else 0)
    (x : ℕ → Vec) (hx : ∀ k, k ≤ w.length → x k = (S1 fl p w k).v)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    ∃ q, q ≤ i ∧ hd.sel fl dA (w.length + 1) x i = [q] ∧
      ((q = 0 ∧ ∀ k, 1 ≤ k → k ≤ i → tokAt w (k - 1) ≠ t) ∨
       (1 ≤ q ∧ tokAt w (q - 1) = t ∧ ∀ k, q < k → k ≤ i → tokAt w (k - 1) ≠ t)) := by
  classical
  have hI1 : 1 ≤ fl (i : ℝ) := by
    have h1 := hr.mono 1 (i : ℝ) (by exact_mod_cast hi1)
    rwa [hr.one] at h1
  have hIle := (hr.pos_le hu0 (show i ≤ w.length + 1 by omega) hn).2
  have hIu : u * fl (i : ℝ) ≤ 1 / 250 := by
    have h1 := mul_le_mul_of_nonneg_left hIle hu0
    nlinarith [h1, hn, hu1, hu0]
  have hα := sw_ge hr hu0 hu1 (1 / 4) (1 / 4) (by norm_num) (by norm_num) (hdA 12 13)
  have hβ := sw_ge hr hu0 hu1 (1 / 2) (1 / 2) (by norm_num) (by norm_num) (hdA 13 4)
  have hγ := sw_ge hr hu0 hu1 1 1 (by norm_num) (by norm_num) (hdA 13 ci)
  have hb := sw_ge hr hu0 hu1 1 1 (by norm_num) (by norm_num) (hp.E 0 4)
  have hB : Bnds u (sw fl (1 / 4) (dA 12 13)) (sw fl (1 / 2) (dA 13 4)) (sw fl 1 (dA 13 ci))
      (sw fl 1 (p.E 0 4)) π (fl (i : ℝ)) :=
    ⟨by linarith [hα.1], by linarith [hα.2], by linarith [hβ.1], by linarith [hβ.2],
     by linarith [hγ.1], by linarith [hγ.2], by linarith [hb.1], by linarith [hb.2],
     hπ1, hπ2, hI1, hIu⟩
  have hk0a : (S1 fl p w 0).a4 = sw fl 1 (p.E 0 4) := by
    simp [S1, S0, Lane4.Seq.tokAt_zero]
  have hkpos : ∀ k, 1 ≤ k → k ≤ w.length → (S1 fl p w k).a4 = 0 := by
    intro k hk1 hk
    have h1 := tok_pos w hw k hk1 hk
    have h2 : tokAt w k ≠ 0 := by omega
    simp [S1, S0, h2]
  have hk0f : (S1 fl p w 0).fq = 0 := by simp [S1, S0, hr.zero]
  have hpf0 : pf (S1 fl p w 0) = 0 := by
    rw [hpf 0 (Nat.zero_le _), if_neg]
    intro hh
    have h0 : tokAt w (0 - 1) = 0 := Lane4.Seq.tokAt_zero w
    omega
  by_cases hex : ∃ k, k ≤ i ∧ (1 ≤ k ∧ tokAt w (k - 1) = t)
  · obtain ⟨q, hqi, ⟨hq1, hqt⟩, hmax⟩ :=
      exists_last (fun k => 1 ≤ k ∧ tokAt w (k - 1) = t) i hex
    refine ⟨q, hqi, ?_, Or.inr ⟨hq1, hqt, fun k h1 h2 hk => hmax k h1 h2 ⟨by omega, hk⟩⟩⟩
    apply Head.sel_unique
    · rw [hmask, Lane4.Seq.mem_cand_causal]
      exact hqi
    · intro k hk hne
      rw [hmask, Lane4.Seq.mem_cand_causal] at hk
      rw [hx i hi, hx k (by omega), hx q (by omega), hscore, hscore]
      have hqf : (S1 fl p w q).fq = fl (q : ℝ) := S1_fq
      have hif : (S1 fl p w i).fq = fl (i : ℝ) := S1_fq
      have hq0 : 0 ≤ fl (q : ℝ) := hr.nonneg (Nat.cast_nonneg q)
      have hqI : fl (q : ℝ) ≤ fl (i : ℝ) := hr.mono _ _ (by exact_mod_cast hqi)
      rw [hqf, hif, hpf q (by omega), if_pos hqt, hkpos q hq1 (by omega), sc_M hr]
      by_cases hk0 : k = 0
      · subst hk0
        rw [hk0a, hpf0, hk0f, sc_B hr]
        exact B_lt_M hr hu0 hu1 hB hq0 hqI
      · have hk1 : 1 ≤ k := by omega
        have hkf : (S1 fl p w k).fq = fl (k : ℝ) := S1_fq
        have hk0' : 0 ≤ fl (k : ℝ) := hr.nonneg (Nat.cast_nonneg k)
        have hkI : fl (k : ℝ) ≤ fl (i : ℝ) := hr.mono _ _ (by exact_mod_cast hk)
        rw [hkf, hkpos k hk1 (by omega)]
        by_cases hkt : tokAt w (k - 1) = t
        · have hkq : k < q := by
            rcases Nat.lt_or_ge k q with h1 | h1
            · exact h1
            · exfalso
              have h2 : q < k := by omega
              exact hmax k h2 hk ⟨hk1, hkt⟩
          rw [hpf k (by omega), if_pos hkt, sc_M hr]
          have hg := hr.pos_gap hu0 hkq (show q ≤ w.length + 1 by omega) hn
          exact M_lt hr hu0 hu1 hB hk0' hg hqI
        · rw [hpf k (by omega), if_neg hkt, sc_U hr]
          exact U_lt_M hr hu0 hu1 hB hk0' hkI hq0 hqI
  · refine ⟨0, Nat.zero_le _, ?_, Or.inl ⟨rfl, fun k hk1 hki hkt => hex ⟨k, hki, hk1, hkt⟩⟩⟩
    apply Head.sel_unique
    · rw [hmask, Lane4.Seq.mem_cand_causal]
      exact Nat.zero_le _
    · intro k hk hne
      rw [hmask, Lane4.Seq.mem_cand_causal] at hk
      have hk1 : 1 ≤ k := by omega
      have hkt : tokAt w (k - 1) ≠ t := fun hh => hex ⟨k, hk, hk1, hh⟩
      rw [hx i hi, hx k (by omega), hx 0 (Nat.zero_le _), hscore, hscore]
      have hif : (S1 fl p w i).fq = fl (i : ℝ) := S1_fq
      have hkf : (S1 fl p w k).fq = fl (k : ℝ) := S1_fq
      have hk0' : 0 ≤ fl (k : ℝ) := hr.nonneg (Nat.cast_nonneg k)
      have hkI : fl (k : ℝ) ≤ fl (i : ℝ) := hr.mono _ _ (by exact_mod_cast hk)
      rw [hif, hk0a, hpf0, hk0f, hkf, hkpos k hk1 (by omega), hpf k (by omega), if_neg hkt,
        sc_B hr, sc_U hr]
      exact U_lt_B hr hu0 hu1 hB hk0' hkI

theorem pf1 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (k : ℕ) :
    (S1 fl p w k).a5 =
      if tokAt w (k - 1) = 1 then fl (sw fl 1 (p.V 0 0 5 0) * sw fl 1 (p.E 1 0)) else 0 := by
  by_cases hh : tokAt w (k - 1) = 1
  · simp [S1, S0, hh]
  · simp [S1, S0, hh, hr.zero]

theorem pf2 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (k : ℕ) :
    (S1 fl p w k).a6 =
      if tokAt w (k - 1) = 2 then fl (sw fl 1 (p.V 0 0 6 1) * sw fl 1 (p.E 2 1)) else 0 := by
  by_cases hh : tokAt w (k - 1) = 2
  · simp [S1, S0, hh]
  · simp [S1, S0, hh, hr.zero]

theorem pf3 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (k : ℕ) :
    (S1 fl p w k).a7 =
      if tokAt w (k - 1) = 3 then fl (sw fl 1 (p.V 0 0 7 2) * sw fl 1 (p.E 3 2)) else 0 := by
  by_cases hh : tokAt w (k - 1) = 3
  · simp [S1, S0, hh]
  · simp [S1, S0, hh, hr.zero]

theorem pi_bnd {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (v T : ℝ) (hv : |v - 1| ≤ 1 / 199) (hT : |T - 1| ≤ 1 / 199) :
    987 / 1000 ≤ fl (v * T) ∧ fl (v * T) ≤ 1013 / 1000 := by
  have h1 := near_mul hv hT
  have h2 := abs_le.mp h1
  have hvT : |v * T| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [h2.1, h2.2]
  have h3 := abs_le.mp (hr.err hu0 hvT)
  constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]

/-! ### Output -/

noncomputable def hidU (fl : ℝ → ℝ) (s3 T s1 r c : ℝ) : ℝ :=
  relu (fl (fl (fl (s3 * T) + fl (s1 * r)) + c))

noncomputable def outE (fl : ℝ → ℝ) (wo w0 w1 w2 H1 H2 H3 : ℝ) : ℝ :=
  fl (wo * fl (fl (fl (w0 * H1) + fl (w1 * H2)) + fl (w2 * H3)))

noncomputable def outOne (fl : ℝ → ℝ) (wo wk Hn : ℝ) : ℝ := fl (wo * fl (wk * Hn))

theorem outE_1 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (wo w0 w1 w2 Hn : ℝ) :
    outE fl wo w0 w1 w2 Hn 0 0 = outOne fl wo w0 Hn := by
  simp [outE, outOne, hr.zero, hr.idem]

theorem outE_2 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (wo w0 w1 w2 Hn : ℝ) :
    outE fl wo w0 w1 w2 0 Hn 0 = outOne fl wo w1 Hn := by
  simp [outE, outOne, hr.zero, hr.idem]

theorem outE_3 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (wo w0 w1 w2 Hn : ℝ) :
    outE fl wo w0 w1 w2 0 0 Hn = outOne fl wo w2 Hn := by
  simp [outE, outOne, hr.zero, hr.idem]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem out_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) (q1 q2 q3 : ℕ)
    (hq1 : q1 ≤ i) (hq2 : q2 ≤ i) (hq3 : q3 ≤ i)
    (hs1 : hd1.sel fl (p.A 1 0) (w.length + 1) (X1 fl p w) i = [q1])
    (hs2 : hd2.sel fl (p.A 1 1) (w.length + 1) (X1 fl p w) i = [q2])
    (hs3 : hd3.sel fl (p.A 1 2) (w.length + 1) (X1 fl p w) i = [q3]) :
    net.out fl p w i =
      outE fl (sw fl 1 (p.oW 11)) (sw fl 1 (p.W2 1 11 0)) (sw fl 1 (p.W2 1 11 1))
        (sw fl 1 (p.W2 1 11 2))
        (hidU fl (sw fl 3 (p.W1 1 0 0)) (S0 fl p w i).a0 (sw fl 1 (p.W1 1 0 8))
          (fl (sw fl 1 (p.V 1 0 8 3) * (S0 fl p w q1).a3)) (sw fl (-3) (p.b1 1 0)))
        (hidU fl (sw fl 3 (p.W1 1 1 1)) (S0 fl p w i).a1 (sw fl 1 (p.W1 1 1 9))
          (fl (sw fl 1 (p.V 1 1 9 3) * (S0 fl p w q2).a3)) (sw fl (-3) (p.b1 1 1)))
        (hidU fl (sw fl 3 (p.W1 1 2 2)) (S0 fl p w i).a2 (sw fl 1 (p.W1 1 2 10))
          (fl (sw fl 1 (p.V 1 2 10 3) * (S0 fl p w q3).a3)) (sw fl (-3) (p.b1 1 2))) := by
  have hxq1 := X1_eq hr hu0 hu1 p hp w hw hn q1 (by omega)
  have hxq2 := X1_eq hr hu0 hu1 p hp w hw hn q2 (by omega)
  have hxq3 := X1_eq hr hu0 hu1 p hp w hw hn q3 (by omega)
  have hxi := X1_eq hr hu0 hu1 p hp w hw hn i hi
  obtain ⟨f0, f1, f2, f3, f4, ffq, ffn⟩ := S0_fix hr p w i
  obtain ⟨z5, z6, z7, zr1, zr2, zr3, zo⟩ := S0_z fl p w i
  have hrun : net.run fl p w = blk2.apply fl p 1 (w.length + 1) (X1 fl p w) := rfl
  unfold TNet.out
  rw [hrun]
  simp [Block.apply, blk2, headsApply, Head.attn, hs1, hs2, hs3, hd1_V, hd2_V, hd3_V, attnRows,
    ravg_singleton hr, hxq1, hxq2, hxq3, hxi, St.v, S1, z15, e3, w1a, w1b, w1c, w2z, w2o, radd,
    raffine, rdot, sw_zero hr, hr.zero, hr.idem, hr.one, f0, f1, f2, z5, z6, z7, zr1, zr2, zr3,
    zo, net, hidU, outE]

/-! ### Final real-number bounds -/

theorem h_le (x : ℕ) : h x ≤ 2 := by
  unfold h
  split_ifs <;> omega

theorem h_le_cast (x : ℕ) : ((h x : ℕ) : ℝ) ≤ 2 := by
  exact_mod_cast h_le x

theorem S0_a3_near {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ) :
    |(S0 fl p w j).a3 - ((h (tokAt w j) : ℕ) : ℝ)| ≤ 1 / 199 * ((h (tokAt w j) : ℕ) : ℝ) := by
  have h1 := sw_eps hr hu0 hu1 ((h (tokAt w j) : ℕ) : ℚ) (hp.E (tokAt w j) 3)
  have h2 : (((h (tokAt w j) : ℕ) : ℚ) : ℝ) = ((h (tokAt w j) : ℕ) : ℝ) := by simp
  have h3 : |((h (tokAt w j) : ℕ) : ℝ)| = ((h (tokAt w j) : ℕ) : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  rw [h2, h3] at h1
  exact h1

theorem r_near {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (v a H : ℝ) (hv : |v - 1| ≤ 1 / 199)
    (ha : |a - H| ≤ 1 / 199 * H) (hH : 0 ≤ H) : |fl (v * a) - H| ≤ 1 / 98 * H := by
  have hv' : |v - 1| ≤ 1 / 199 * |(1 : ℝ)| := by rw [abs_one]; linarith
  have ha' : |a - H| ≤ 1 / 199 * |H| := by rw [abs_of_nonneg hH]; exact ha
  have h1 := rel_mul hv' ha' (c := 1 / 99) (by norm_num)
  have h2 := rel_fl hr hu0 h1 (c := 1 / 98) (by linarith)
  rw [one_mul, abs_of_nonneg hH] at h2
  exact h2

theorem r_bnd {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (q : ℕ) (v : ℝ)
    (hv : |v - 1| ≤ 1 / 199) :
    |fl (v * (S0 fl p w q).a3) - ((h (tokAt w q) : ℕ) : ℝ)| ≤ 1 / 98 * ((h (tokAt w q) : ℕ) : ℝ) :=
  r_near hr hu0 hu1 v _ _ hv (S0_a3_near hr hu0 hu1 p hp w q) (Nat.cast_nonneg _)

theorem r_range {r H : ℝ} (h1 : |r - H| ≤ 1 / 98 * H) (hH0 : 0 ≤ H) (hH2 : H ≤ 2) :
    0 ≤ r ∧ r ≤ 21 / 10 := by
  obtain ⟨a, b⟩ := abs_le.mp h1
  constructor <;> linarith

theorem hidU_off {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (s3 s1 r c : ℝ) (hs1 : |s1 - 1| ≤ 1 / 199)
    (hc : |c + 3| ≤ 3 / 199) (hr0 : 0 ≤ r) (hr2 : r ≤ 21 / 10) :
    hidU fl s3 0 s1 r c = 0 := by
  unfold hidU
  have e0' : fl (s3 * 0) = 0 := by rw [mul_zero, hr.zero]
  rw [e0', zero_add, hr.idem]
  apply relu_of_nonpos
  have hs := abs_le.mp hs1
  have hcc := abs_le.mp hc
  have h1 : s1 * r ≤ 200 / 199 * r := mul_le_mul_of_nonneg_right (by linarith) hr0
  have h2 : 0 ≤ s1 * r := mul_nonneg (by linarith) hr0
  have hF : fl (s1 * r) ≤ s1 * r + u * 5 :=
    hr.upper hu0 (abs_le.mpr ⟨by linarith, by linarith⟩)
  calc fl (fl (s1 * r) + c) ≤ fl 0 := hr.mono _ _ (by linarith)
    _ = 0 := hr.zero

theorem on_bound {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (H s3 T s1 r c wo wk : ℝ) (hH0 : 0 ≤ H) (hH2 : H ≤ 2)
    (hs3 : |s3 - 3| ≤ 3 / 199) (hT : |T - 1| ≤ 1 / 199) (hs1 : |s1 - 1| ≤ 1 / 199)
    (hrr : |r - H| ≤ 1 / 98 * H) (hc : |c + 3| ≤ 3 / 199)
    (hwo : |wo - 1| ≤ 1 / 199) (hwk : |wk - 1| ≤ 1 / 199) :
    |outOne fl wo wk (hidU fl s3 T s1 r c) - H| ≤ 1 / 4 := by
  unfold outOne hidU
  have hs3' : |s3 - 3| ≤ 1 / 199 * |(3 : ℝ)| := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith
  have hT' : |T - 1| ≤ 1 / 199 * |(1 : ℝ)| := by rw [abs_one]; linarith
  have hs1' : |s1 - 1| ≤ 1 / 199 * |(1 : ℝ)| := by rw [abs_one]; linarith
  have hrr' : |r - H| ≤ 1 / 98 * |H| := by rw [abs_of_nonneg hH0]; exact hrr
  have h1 := rel_fl hr hu0 (rel_mul hs3' hT' (c := 1 / 99) (by norm_num)) (c := 1 / 98)
    (by linarith)
  have h2 := rel_fl hr hu0 (rel_mul hs1' hrr' (c := 1 / 65) (by norm_num)) (c := 1 / 64)
    (by linarith)
  have e1 : |(3 : ℝ) * 1| = 3 := by norm_num
  have e2 : |(1 : ℝ) * H| = H := by rw [one_mul, abs_of_nonneg hH0]
  rw [e1] at h1
  rw [e2] at h2
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  obtain ⟨hca, hcb⟩ := abs_le.mp hc
  have hA : |fl (s3 * T) + fl (s1 * r)| ≤ 6 := by
    rw [abs_le]
    constructor <;> linarith
  have hacc := abs_le.mp (hr.err hu0 hA)
  have hB2 : |fl (fl (s3 * T) + fl (s1 * r)) + c| ≤ 6 := by
    rw [abs_le]
    constructor <;> linarith [hacc.1, hacc.2]
  have hpre := abs_le.mp (hr.err hu0 hB2)
  obtain ⟨P, hP⟩ : ∃ P, P = fl (fl (fl (s3 * T) + fl (s1 * r)) + c) := ⟨_, rfl⟩
  rw [← hP] at hpre ⊢
  have hPH : |P - H| ≤ 8 / 100 := by
    rw [abs_le]
    constructor <;> linarith [hacc.1, hacc.2, hpre.1, hpre.2]
  have hrelu : 0 ≤ relu P ∧ |relu P - H| ≤ 8 / 100 := by
    unfold relu
    rcases le_total P 0 with hP0 | hP0
    · rw [max_eq_right hP0]
      have := abs_le.mp hPH
      constructor
      · exact le_refl _
      · rw [abs_le]
        constructor <;> linarith
    · rw [max_eq_left hP0]
      exact ⟨hP0, hPH⟩
  generalize relu P = Hd at hrelu ⊢
  obtain ⟨hd0, hdH⟩ := hrelu
  have hdH' := abs_le.mp hdH
  have hwk0 : 0 ≤ wk := by
    have := abs_le.mp hwk
    linarith
  have hm3 := near_scale (t := Hd) hwk
  rw [abs_of_nonneg hd0] at hm3
  have hm3' := abs_le.mp hm3
  have hA3 : |wk * Hd| ≤ 3 := by
    rw [abs_le]
    constructor <;> linarith [hm3'.1, hm3'.2]
  have ha3 := abs_le.mp (hr.err hu0 hA3)
  have ha30 : 0 ≤ fl (wk * Hd) := hr.nonneg (mul_nonneg hwk0 hd0)
  have hm4 := near_scale (t := fl (wk * Hd)) hwo
  rw [abs_of_nonneg ha30] at hm4
  have hm4' := abs_le.mp hm4
  have hA4 : |wo * fl (wk * Hd)| ≤ 3 := by
    rw [abs_le]
    constructor <;> linarith [hm4'.1, hm4'.2, ha3.1, ha3.2, hm3'.1, hm3'.2]
  have hout := abs_le.mp (hr.err hu0 hA4)
  rw [abs_le]
  constructor <;> linarith [hm4'.1, hm4'.2, ha3.1, ha3.2, hm3'.1, hm3'.2, hout.1, hout.2]

/-! ### Target -/

theorem findRange (P : ℕ → Bool) (m : ℕ) :
    ((List.range m).reverse.find? P = none ∧ ∀ k, k < m → P k = false) ∨
    (∃ j, (List.range m).reverse.find? P = some j ∧ j < m ∧ P j = true ∧
      ∀ k, j < k → k < m → P k = false) := by
  induction m with
  | zero =>
    left
    exact ⟨by simp, fun k hk => by omega⟩
  | succ m ih =>
    have e : (List.range (m + 1)).reverse = m :: (List.range m).reverse := by
      simp [List.range_succ]
    rw [e]
    cases hP : P m with
    | true =>
      right
      exact ⟨m, by simp [List.find?, hP], by omega, hP, fun k h1 h2 => by omega⟩
    | false =>
      rcases ih with ⟨h1, h2⟩ | ⟨j, h1, h2, h3, h4⟩
      · left
        refine ⟨by simp [List.find?, hP, h1], fun k hk => ?_⟩
        by_cases hkm : k = m
        · subst hkm
          exact hP
        · exact h2 k (by omega)
      · right
        refine ⟨j, by simp [List.find?, hP, h1], by omega, h3, fun k hk1 hk2 => ?_⟩
        by_cases hkm : k = m
        · subst hkm
          exact hP
        · exact h4 k hk1 (by omega)

theorem target_eq (w : List ℕ) (i : ℕ) (t : ℕ) (ht : tokAt w i = t) (ht1 : 1 ≤ t)
    (q : ℕ) (hqi : q ≤ i)
    (hsp : (q = 0 ∧ ∀ k, 1 ≤ k → k ≤ i → tokAt w (k - 1) ≠ t) ∨
      (1 ≤ q ∧ tokAt w (q - 1) = t ∧ ∀ k, q < k → k ≤ i → tokAt w (k - 1) ≠ t)) :
    target w i = h (tokAt w q) := by
  have key := findRange (fun j => decide (1 ≤ j) && (tokAt w j == tokAt w i)) i
  unfold target prevOcc
  rcases key with ⟨hnone, hall⟩ | ⟨j, hj, hji, hPj, hbet⟩
  · rw [hnone]
    show (0 : ℕ) = h (tokAt w q)
    rcases hsp with ⟨hq0, _⟩ | ⟨hq1, hqt, _⟩
    · subst hq0
      simp [h, Lane4.Seq.tokAt_zero]
    · exfalso
      have hm : 1 ≤ q - 1 := by
        by_contra hcon
        have h0 : q - 1 = 0 := by omega
        rw [h0, Lane4.Seq.tokAt_zero] at hqt
        omega
      have h1 := hall (q - 1) (by omega)
      simp [hm, hqt, ht] at h1
  · rw [hj]
    show h (tokAt w (j + 1)) = h (tokAt w q)
    have hPj' : 1 ≤ j ∧ tokAt w j = tokAt w i := by simpa using hPj
    rcases hsp with ⟨hq0, hmax⟩ | ⟨hq1, hqt, hmax⟩
    · exfalso
      have h3 := hmax (j + 1) (by omega) (by omega)
      apply h3
      rw [Nat.add_sub_cancel, hPj'.2, ht]
    · have hm : 1 ≤ q - 1 := by
        by_contra hcon
        have h0 : q - 1 = 0 := by omega
        rw [h0, Lane4.Seq.tokAt_zero] at hqt
        omega
      have h1 : q - 1 ≤ j := by
        by_contra hcon
        have h3 := hbet (q - 1) (by omega) (by omega)
        simp [hm, hqt, ht] at h3
      have h2 : j + 1 ≤ q := by
        by_contra hcon
        have h3 := hmax (j + 1) (by omega) (by omega)
        apply h3
        rw [Nat.add_sub_cancel, hPj'.2, ht]
      have hq : q = j + 1 := by omega
      rw [hq]

/-! ### Main theorem -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem net_ok : Statement net := by
  intro u fl hr hu0 hu1 p hp w hw hn i hi1 hi
  have hx : ∀ k, k ≤ w.length → X1 fl p w k = (S1 fl p w k).v :=
    fun k hk => X1_eq hr hu0 hu1 p hp w hw hn k hk
  have hti1 := tok_pos w hw i hi1 hi
  have hti3 := tok_le w hw i
  have hπ1 := pi_bnd hr hu0 hu1 _ _ (sw1_near hr hu0 hu1 (hp.V 0 0 5 0))
    (sw1_near hr hu0 hu1 (hp.E 1 0))
  have hπ2 := pi_bnd hr hu0 hu1 _ _ (sw1_near hr hu0 hu1 (hp.V 0 0 6 1))
    (sw1_near hr hu0 hu1 (hp.E 2 1))
  have hπ3 := pi_bnd hr hu0 hu1 _ _ (sw1_near hr hu0 hu1 (hp.V 0 0 7 2))
    (sw1_near hr hu0 hu1 (hp.E 3 2))
  obtain ⟨q1, hq1i, hs1, hsp1⟩ := sel2 hr hu0 hu1 p hp w hw hn hd1 rfl (p.A 1 0)
    (fun r c => hp.A 1 0 r c) 1 5 (le_refl 1) (fun s => s.a5)
    (fl (sw fl 1 (p.V 0 0 5 0) * sw fl 1 (p.E 1 0))) hπ1.1 hπ1.2 (score1 hr (p.A 1 0))
    (fun k _ => pf1 hr p w k) (X1 fl p w) hx i hi1 hi
  obtain ⟨q2, hq2i, hs2, hsp2⟩ := sel2 hr hu0 hu1 p hp w hw hn hd2 rfl (p.A 1 1)
    (fun r c => hp.A 1 1 r c) 2 6 (by norm_num) (fun s => s.a6)
    (fl (sw fl 1 (p.V 0 0 6 1) * sw fl 1 (p.E 2 1))) hπ2.1 hπ2.2 (score2 hr (p.A 1 1))
    (fun k _ => pf2 hr p w k) (X1 fl p w) hx i hi1 hi
  obtain ⟨q3, hq3i, hs3, hsp3⟩ := sel2 hr hu0 hu1 p hp w hw hn hd3 rfl (p.A 1 2)
    (fun r c => hp.A 1 2 r c) 3 7 (by norm_num) (fun s => s.a7)
    (fl (sw fl 1 (p.V 0 0 7 2) * sw fl 1 (p.E 3 2))) hπ3.1 hπ3.2 (score3 hr (p.A 1 2))
    (fun k _ => pf3 hr p w k) (X1 fl p w) hx i hi1 hi
  have hout := out_eq hr hu0 hu1 p hp w hw hn i hi1 hi q1 q2 q3 hq1i hq2i hq3i hs1 hs2 hs3
  rw [hout]
  have hwo := sw1_near hr hu0 hu1 (hp.oW 11)
  have hw20 := sw1_near hr hu0 hu1 (hp.W2 1 11 0)
  have hw21 := sw1_near hr hu0 hu1 (hp.W2 1 11 1)
  have hw22 := sw1_near hr hu0 hu1 (hp.W2 1 11 2)
  have hb0 := swm3_near hr hu0 hu1 (hp.b1 1 0)
  have hb1 := swm3_near hr hu0 hu1 (hp.b1 1 1)
  have hb2 := swm3_near hr hu0 hu1 (hp.b1 1 2)
  have hW10 := sw3_near hr hu0 hu1 (hp.W1 1 0 0)
  have hW11 := sw3_near hr hu0 hu1 (hp.W1 1 1 1)
  have hW12 := sw3_near hr hu0 hu1 (hp.W1 1 2 2)
  have hV10 := sw1_near hr hu0 hu1 (hp.W1 1 0 8)
  have hV11 := sw1_near hr hu0 hu1 (hp.W1 1 1 9)
  have hV12 := sw1_near hr hu0 hu1 (hp.W1 1 2 10)
  have hvr1 := sw1_near hr hu0 hu1 (hp.V 1 0 8 3)
  have hvr2 := sw1_near hr hu0 hu1 (hp.V 1 1 9 3)
  have hvr3 := sw1_near hr hu0 hu1 (hp.V 1 2 10 3)
  have hR1 := r_bnd hr hu0 hu1 p hp w q1 _ hvr1
  have hR2 := r_bnd hr hu0 hu1 p hp w q2 _ hvr2
  have hR3 := r_bnd hr hu0 hu1 p hp w q3 _ hvr3
  obtain ⟨hR10, hR1u⟩ := r_range hR1 (Nat.cast_nonneg _) (h_le_cast _)
  obtain ⟨hR20, hR2u⟩ := r_range hR2 (Nat.cast_nonneg _) (h_le_cast _)
  obtain ⟨hR30, hR3u⟩ := r_range hR3 (Nat.cast_nonneg _) (h_le_cast _)
  rcases (show tokAt w i = 1 ∨ tokAt w i = 2 ∨ tokAt w i = 3 by omega) with hti | hti | hti
  · have htar := target_eq w i 1 hti (le_refl 1) q1 hq1i hsp1
    rw [htar]
    have ha0 : (S0 fl p w i).a0 = sw fl 1 (p.E 1 0) := by simp [S0, hti]
    have ha1 : (S0 fl p w i).a1 = 0 := by simp [S0, hti]
    have ha2 : (S0 fl p w i).a2 = 0 := by simp [S0, hti]
    rw [ha0, ha1, ha2, hidU_off hr hu0 hu1 _ _ _ _ hV11 hb1 hR20 hR2u,
      hidU_off hr hu0 hu1 _ _ _ _ hV12 hb2 hR30 hR3u, outE_1 hr]
    exact on_bound hr hu0 hu1 _ _ _ _ _ _ _ _ (Nat.cast_nonneg _) (h_le_cast _) hW10
      (sw1_near hr hu0 hu1 (hp.E 1 0)) hV10 hR1 hb0 hwo hw20
  · have htar := target_eq w i 2 hti (by norm_num) q2 hq2i hsp2
    rw [htar]
    have ha0 : (S0 fl p w i).a0 = 0 := by simp [S0, hti]
    have ha1 : (S0 fl p w i).a1 = sw fl 1 (p.E 2 1) := by simp [S0, hti]
    have ha2 : (S0 fl p w i).a2 = 0 := by simp [S0, hti]
    rw [ha0, ha1, ha2, hidU_off hr hu0 hu1 _ _ _ _ hV10 hb0 hR10 hR1u,
      hidU_off hr hu0 hu1 _ _ _ _ hV12 hb2 hR30 hR3u, outE_2 hr]
    exact on_bound hr hu0 hu1 _ _ _ _ _ _ _ _ (Nat.cast_nonneg _) (h_le_cast _) hW11
      (sw1_near hr hu0 hu1 (hp.E 2 1)) hV11 hR2 hb1 hwo hw21
  · have htar := target_eq w i 3 hti (by norm_num) q3 hq3i hsp3
    rw [htar]
    have ha0 : (S0 fl p w i).a0 = 0 := by simp [S0, hti]
    have ha1 : (S0 fl p w i).a1 = 0 := by simp [S0, hti]
    have ha2 : (S0 fl p w i).a2 = sw fl 1 (p.E 3 2) := by simp [S0, hti]
    rw [ha0, ha1, ha2, hidU_off hr hu0 hu1 _ _ _ _ hV10 hb0 hR10 hR1u,
      hidU_off hr hu0 hu1 _ _ _ _ hV11 hb1 hR20 hR2u, outE_3 hr]
    exact on_bound hr hu0 hu1 _ _ _ _ _ _ _ _ (Nat.cast_nonneg _) (h_le_cast _) hW12
      (sw1_near hr hu0 hu1 (hp.E 3 2)) hV12 hR3 hb2 hwo hw22

end Lane4.Case
