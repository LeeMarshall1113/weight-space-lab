namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)
set_option linter.unusedVariables false

def zr : List ℚ := List.replicate 16 0
def zr3 : List ℚ := List.replicate 3 0
def sp (c m : ℕ) (a : ℚ) : List ℚ := List.replicate c 0 ++ a :: List.replicate m 0

def A1 : List (List ℚ) := [zr, zr, zr, zr, zr, zr, zr, zr, zr, zr, zr, zr, zr, sp 14 1 40, zr, zr]

/-- block 1: strict head c writes the one-hot of the previous token into slot 3+c. -/
def hd1 (c : ℕ) : Head :=
  { A := A1, V := List.replicate (3 + c) zr ++ sp c (15 - c) 1 :: List.replicate (12 - c) zr,
    mask := Mask.strict }

def A2 (c : ℕ) : List (List ℚ) :=
  [zr, zr, zr, zr, zr, zr, zr, zr, zr, zr, zr, zr, zr, sp 14 1 40, zr, sp (6 + c) (9 - c) (-1)]

/-- block 2: causal head c, flag = slot 6+c (small = flagged). -/
def hd2 (c : ℕ) : Head :=
  { A := A2 c, V := List.replicate (9 + c) zr ++ sp 1 14 2 :: List.replicate (6 - c) zr,
    mask := Mask.causal }

def blk1 : Block :=
  { heads := [hd1 0, hd1 1, hd1 2],
    W1 := [sp 3 12 (-250), sp 4 11 (-250), sp 5 10 (-250)],
    b1 := [200, 200, 200],
    W2 := [zr3, zr3, zr3, zr3, zr3, zr3, sp 0 2 1, sp 1 1 1, sp 2 0 1,
           zr3, zr3, zr3, zr3, zr3, zr3, zr3],
    b2 := zr }

def gt0 : List ℚ := [3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
def gt1 : List ℚ := [0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
def gt2 : List ℚ := [0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]

def blk2 : Block :=
  { heads := [hd2 0, hd2 1, hd2 2],
    W1 := [gt0, gt1, gt2],
    b1 := [-3, -3, -3],
    W2 := [zr3, zr3, zr3, zr3, zr3, zr3, zr3, zr3, zr3, zr3, zr3, zr3, [1, 1, 1],
           zr3, zr3, zr3],
    b2 := zr }

def net : TNet :=
  { embed := [[0, 0, 0, 0, 0, 0, -100, -100, -100, 0, 0, 0, 0],
              [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
              [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
              [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    blocks := [blk1, blk2],
    outW := sp 12 3 1,
    outB := 0 }

theorem rdot_zeros {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) :
    ∀ (m : ℕ) (xs : Vec) (d : ℕ → ℝ) (j : ℕ) (acc : ℝ), fl acc = acc →
      rdot fl (List.replicate m 0) xs d j acc = acc := by
  intro m
  induction m with
  | zero => intro xs d j acc _; simp [rdot]
  | succ m ih =>
    intro xs d j acc hacc
    cases xs with
    | nil => simp [rdot]
    | cons x xs' =>
      have h1 : rdot fl (List.replicate (m + 1) (0 : ℚ)) (x :: xs') d j acc
          = rdot fl (List.replicate m (0 : ℚ)) xs' d (j + 1)
              (fl (acc + fl (sw fl 0 (d j) * x))) := by
        simp [List.replicate_succ, rdot]
      rw [h1]
      simp only [sw_zero hr, zero_mul, hr.zero, add_zero, hacc]
      exact ih _ _ _ _ hacc

theorem rdot_zr {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (xs : Vec) (d : ℕ → ℝ) (j : ℕ) :
    rdot fl zr xs d j 0 = 0 := by
  unfold zr
  exact rdot_zeros hr 16 xs d j 0 hr.zero

theorem rdot_zr3 {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (xs : Vec) (d : ℕ → ℝ) (j : ℕ) :
    rdot fl zr3 xs d j 0 = 0 := by
  unfold zr3
  exact rdot_zeros hr 3 xs d j 0 hr.zero

theorem rdot_sp {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) :
    ∀ (c m : ℕ) (a : ℚ) (xs : Vec) (d : ℕ → ℝ) (j : ℕ), c < xs.length →
      |sw fl a (d (j + c)) * xs.getD c 0| ≤ M →
      rdot fl (sp c m a) xs d j 0 = fl (sw fl a (d (j + c)) * xs.getD c 0) := by
  intro c
  induction c with
  | zero =>
    intro m a xs d j hlen hM
    cases xs with
    | nil => simp at hlen
    | cons x xs' =>
      have h1 : rdot fl (sp 0 m a) (x :: xs') d j 0
          = rdot fl (List.replicate m 0) xs' d (j + 1) (fl (0 + fl (sw fl a (d j) * x))) := by
        simp [sp, rdot]
      rw [h1]
      have hM' : |sw fl a (d j) * x| ≤ M := by simpa using hM
      have e1 : fl (0 + fl (sw fl a (d j) * x)) = fl (sw fl a (d j) * x) := by
        rw [zero_add]; exact hr.idem _ hM'
      rw [e1, rdot_zeros hr m xs' d (j + 1) _ (hr.idem _ hM')]
      simp
  | succ c ih =>
    intro m a xs d j hlen hM
    cases xs with
    | nil => simp at hlen
    | cons x xs' =>
      have h1 : rdot fl (sp (c + 1) m a) (x :: xs') d j 0
          = rdot fl (sp c m a) xs' d (j + 1) 0 := by
        simp [sp, List.replicate_succ, rdot, sw_zero hr, hr.zero]
      rw [h1]
      have hlen' : c < xs'.length := by simpa using hlen
      have hidx : j + 1 + c = j + (c + 1) := by omega
      have hM' : |sw fl a (d (j + 1 + c)) * xs'.getD c 0| ≤ M := by
        rw [hidx]; simpa using hM
      rw [ih m a xs' d (j + 1) hlen' hM', hidx]
      simp

noncomputable def ee (fl : ℝ → ℝ) (p : Pert) (τ c : ℕ) : ℝ :=
  if τ = c + 1 then sw fl 1 (p.E τ c) else 0
noncomputable def eg (fl : ℝ → ℝ) (p : Pert) (τ c : ℕ) : ℝ :=
  if τ = 0 then sw fl (-100) (p.E 0 (6 + c)) else 0

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) : tokAt w j ≤ 3 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) :
    net.init fl p w j =
      [ee fl p (tokAt w j) 0, ee fl p (tokAt w j) 1, ee fl p (tokAt w j) 2, 0, 0, 0,
       eg fl p (tokAt w j) 0, eg fl p (tokAt w j) 1, eg fl p (tokAt w j) 2, 0, 0, 0, 0,
       1, fl (j : ℝ), fl ((w.length + 1 : ℕ) : ℝ)] := by
  have h3 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 := by
    have := tok_le w hw j
    omega
  rcases h3 with h | h | h | h <;>
    simp [TNet.init, net, swRow, ee, eg, pos, h, sw_zero hr]

theorem sattnRows_zr {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) :
    ∀ (m : ℕ) (dV : ℕ → ℕ → ℝ) (cc : List ℕ) (s : ℕ → ℝ) (x : ℕ → Vec) (i : ℕ),
      sattnRows fl ex (List.replicate m zr) dV cc s x i = List.replicate m 0 := by
  intro m
  induction m with
  | zero => intro dV cc s x i; simp [sattnRows]
  | succ m ih =>
    intro dV cc s x i
    have hz : savg fl ex cc s (fun j => rdot fl zr (x j) (dV i) 0 0) = 0 :=
      soft_zeros hr (fun k _ => rdot_zr hr _ _ _)
    rw [List.replicate_succ, sattnRows, ih, hz]
    simp [List.replicate_succ]

theorem sattnRows_one {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) :
    ∀ (q m : ℕ) (r : List ℚ) (dV : ℕ → ℕ → ℝ) (cc : List ℕ) (s : ℕ → ℝ) (x : ℕ → Vec) (i : ℕ),
      sattnRows fl ex (List.replicate q zr ++ r :: List.replicate m zr) dV cc s x i
        = List.replicate q 0 ++
          savg fl ex cc s (fun j => rdot fl r (x j) (dV (i + q)) 0 0) :: List.replicate m 0 := by
  intro q
  induction q with
  | zero =>
    intro m r dV cc s x i
    simp only [List.replicate_zero, List.nil_append, Nat.add_zero]
    rw [sattnRows, sattnRows_zr hr]
  | succ q ih =>
    intro m r dV cc s x i
    have hz : savg fl ex cc s (fun j => rdot fl zr (x j) (dV i) 0 0) = 0 :=
      soft_zeros hr (fun k _ => rdot_zr hr _ _ _)
    rw [List.replicate_succ, List.cons_append, sattnRows, ih, hz]
    have : i + 1 + q = i + (q + 1) := by omega
    rw [this]
    simp [List.replicate_succ]

theorem score1_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ) (c : ℕ)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a14 a15 : ℝ) (xj : Vec)
    (hlen : xj.length = 16) (qk : ℝ) (h14 : xj.getD 14 0 = qk)
    (hM : |sw fl 40 (dA 13 14) * qk| ≤ M)
    (hI : fl (fl (sw fl 40 (dA 13 14) * qk)) = fl (sw fl 40 (dA 13 14) * qk)) :
    (hd1 c).score fl dA [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, 1, a14, a15] xj
      = fl (sw fl 40 (dA 13 14) * qk) := by
  have hrow : rdot fl (sp 14 1 40) xj (dA 13) 0 0 = fl (sw fl 40 (dA 13 14) * qk) := by
    have := rdot_sp hr 14 1 40 xj (dA 13) 0 (by omega) (by simpa [h14] using hM)
    simpa [h14] using this
  simp [Head.score, hd1, A1, rmat, rdot_zr hr, hrow, pdot, hr.zero, hI]

theorem score2_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ) (c : ℕ)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a14 qn : ℝ) (xj : Vec)
    (hlen : xj.length = 16) (qk g : ℝ) (hc : c < 3) (h14 : xj.getD 14 0 = qk)
    (hg : xj.getD (6 + c) 0 = g)
    (hM1 : |sw fl 40 (dA 13 14) * qk| ≤ M) (hM2 : |sw fl (-1) (dA 15 (6 + c)) * g| ≤ M)
    (hI : fl (fl (sw fl 40 (dA 13 14) * qk)) = fl (sw fl 40 (dA 13 14) * qk)) :
    (hd2 c).score fl dA [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, 1, a14, qn] xj
      = fl (fl (sw fl 40 (dA 13 14) * qk) + fl (qn * fl (sw fl (-1) (dA 15 (6 + c)) * g))) := by
  have hr13 : rdot fl (sp 14 1 40) xj (dA 13) 0 0 = fl (sw fl 40 (dA 13 14) * qk) := by
    have := rdot_sp hr 14 1 40 xj (dA 13) 0 (by omega) (by simpa [h14] using hM1)
    simpa [h14] using this
  have hr15 : rdot fl (sp (6 + c) (9 - c) (-1)) xj (dA 15) 0 0
      = fl (sw fl (-1) (dA 15 (6 + c)) * g) := by
    have := rdot_sp hr (6 + c) (9 - c) (-1) xj (dA 15) 0 (by omega) (by simpa [hg] using hM2)
    simpa [hg] using this
  simp [Head.score, hd2, A2, rmat, rdot_zr hr, hr13, hr15, pdot, hr.zero, hI]

noncomputable def Pc (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (c k : ℕ) : ℝ :=
  savg fl ex (cand Mask.strict (w.length + 1) k)
    (hscore (hd1 c) fl (p.A 0 c) (net.init fl p w) k)
    (fun j => rdot fl (sp c (15 - c) 1) (net.init fl p w j) (p.V 0 c (3 + c)) 0 0)

theorem attn1_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (c k : ℕ) :
    sattn (hd1 c) fl ex (p.A 0 c) (p.V 0 c) (w.length + 1) (net.init fl p w) k
      = List.replicate (3 + c) 0 ++ Pc fl ex p w c k :: List.replicate (12 - c) 0 := by
  unfold sattn
  show sattnRows fl ex (List.replicate (3 + c) zr ++ sp c (15 - c) 1 :: List.replicate (12 - c) zr)
    (p.V 0 c) (cand Mask.strict (w.length + 1) k)
    (hscore (hd1 c) fl (p.A 0 c) (net.init fl p w) k) (net.init fl p w) 0 = _
  rw [sattnRows_one hr]
  simp only [zero_add]
  rfl

theorem attn1_0 {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ) (k : ℕ) :
    sattn (hd1 0) fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) k
      = [0, 0, 0, Pc fl ex p w 0 k, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [attn1_eq hr]; rfl

theorem attn1_1 {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ) (k : ℕ) :
    sattn (hd1 1) fl ex (p.A 0 1) (p.V 0 1) (w.length + 1) (net.init fl p w) k
      = [0, 0, 0, 0, Pc fl ex p w 1 k, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [attn1_eq hr]; rfl

theorem attn1_2 {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ) (k : ℕ) :
    sattn (hd1 2) fl ex (p.A 0 2) (p.V 0 2) (w.length + 1) (net.init fl p w) k
      = [0, 0, 0, 0, 0, Pc fl ex p w 2 k, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [attn1_eq hr]; rfl

theorem net_ok : Statement net := by
  trivial

end Lane4.Case
