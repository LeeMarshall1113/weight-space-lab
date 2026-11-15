namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)
set_option linter.unusedVariables false

def zr : List ℚ := List.replicate 16 0
def zr3 : List ℚ := List.replicate 3 0
def zb : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
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
    b2 := zb }

def gt0 : List ℚ := [3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
def gt1 : List ℚ := [0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
def gt2 : List ℚ := [0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]

def blk2 : Block :=
  { heads := [hd2 0, hd2 1, hd2 2],
    W1 := [gt0, gt1, gt2],
    b1 := [-3, -3, -3],
    W2 := [zr3, zr3, zr3, zr3, zr3, zr3, zr3, zr3, zr3, zr3, zr3, zr3, [1, 1, 1],
           zr3, zr3, zr3],
    b2 := zb }

def net : TNet :=
  { embed := [[0, 0, 0, 0, 0, 0, -150, -150, -150, 0, 0, 0, 0],
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
  if τ = 0 then sw fl (-150) (p.E 0 (6 + c)) else 0

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
    have := rdot_sp hr 14 1 40 xj (dA 13) 0 (by omega) (by rw [h14, zero_add]; exact hM)
    rw [h14, zero_add] at this; exact this
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
    have := rdot_sp hr 14 1 40 xj (dA 13) 0 (by omega) (by rw [h14, zero_add]; exact hM1)
    rw [h14, zero_add] at this; exact this
  have hr15 : rdot fl (sp (6 + c) (9 - c) (-1)) xj (dA 15) 0 0
      = fl (sw fl (-1) (dA 15 (6 + c)) * g) := by
    have := rdot_sp hr (6 + c) (9 - c) (-1) xj (dA 15) 0 (by omega) (by rw [hg, zero_add]; exact hM2)
    rw [hg, zero_add] at this; exact this
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

theorem val1_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (c : ℕ) (hc : c < 3)
    (d : ℕ → ℝ) (xj : Vec) (hlen : xj.length = 16) (v : ℝ) (hv : xj.getD c 0 = v)
    (hM : |sw fl 1 (d c) * v| ≤ M) :
    rdot fl (sp c (15 - c) 1) xj d 0 0 = fl (sw fl 1 (d c) * v) := by
  have := rdot_sp hr c (15 - c) 1 xj d 0 (by omega) (by rw [hv, zero_add]; exact hM)
  rw [hv, zero_add] at this; exact this

theorem ee_facts {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) (hM40 : (40 : ℝ) ≤ M) (p : Pert)
    (hp : p.Within (1 / 200)) (τ c : ℕ) :
    (τ = c + 1 → |ee fl p τ c - 1| ≤ 1 / 190) ∧ (τ ≠ c + 1 → ee fl p τ c = 0) := by
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by linarith
  by_cases h : τ = c + 1
  · refine ⟨fun _ => ?_, fun h' => absurd h h'⟩
    have hs := sw_near hr hu0 1 (hp.E τ c) (by norm_num) (by norm_num; linarith) hε
    have ht := eta_tiny hη
    have c1 : ((1 : ℚ) : ℝ) = 1 := by norm_num
    rw [c1, abs_one] at hs
    have : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
    simp only [ee, if_pos h]
    linarith
  · refine ⟨fun h' => absurd h' h, fun _ => ?_⟩
    simp [ee, h]

theorem Pfact {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (he : ExpM u η ex)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2 ^ 149)
    (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3)
    (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (hnη : η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100)
    (hM : 2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M) (c : ℕ) (hc : c < 3) (k : ℕ)
    (hk : k ≤ w.length) :
    fl (Pc fl ex p w c k) = Pc fl ex p w c k ∧ |Pc fl ex p w c k| ≤ 2 ∧
    (1 ≤ k → tokAt w (k - 1) = c + 1 → 19 / 20 ≤ Pc fl ex p w c k) ∧
    ((k = 0 ∨ tokAt w (k - 1) ≠ c + 1) → |Pc fl ex p w c k| ≤ 3 / 100) := by
  by_cases hk0 : k = 0
  · subst hk0
    have h0 : Pc fl ex p w c 0 = 0 := by simp [Pc, savg, cand, rsum, hr.zero]
    rw [h0]
    refine ⟨hr.zero, by norm_num, fun h => absurd h (by norm_num), fun _ => by norm_num⟩
  have hk1 : 1 ≤ k := by omega
  have hn1 : 1 ≤ w.length + 1 := by omega
  have hnR : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hn1
  have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
    have := range_lin hM hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have h45 : 45 * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  have h300 : 300 * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin hM hn1 (by norm_num) (by norm_num)
  have h40 : (40 : ℝ) ≤ M := range_const hM hn1 (by norm_num)
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by linarith
  have c40 : ((40 : ℚ) : ℝ) = 40 := by norm_num
  have c1 : ((1 : ℚ) : ℝ) = 1 := by norm_num
  have hS := sw_near hr hu0 40 (hp.A 0 c 13 14) (by norm_num) (by rw [c40]; norm_num; linarith) hε
  rw [c40, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 40)] at hS
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  have hV := sw_near hr hu0 1 (hp.V 0 c (3 + c) c) (by norm_num) (by norm_num; linarith) hε
  rw [c1, abs_one] at hV
  obtain ⟨hV1, hV2⟩ := abs_le.mp hV
  have hee := ee_facts hr hu0 hu1 hη h40 p hp
  have hPb : ∀ k' : ℕ, k' ≤ w.length + 1 →
      |sw fl 40 (p.A 0 c 13 14) * fl (k' : ℝ)| ≤ 41 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k' hk'
    obtain ⟨hk0', hk1'⟩ := hr.pos_le hu0 hη hk' hn hnM
    have hS0 : 0 ≤ sw fl 40 (p.A 0 c 13 14) := by linarith
    rw [abs_of_nonneg (mul_nonneg hS0 hk0')]
    have := mul_le_mul (show sw fl 40 (p.A 0 c 13 14) ≤ 403 / 10 by linarith) hk1' hk0'
      (by norm_num)
    linarith
  have hsk : ∀ k' : ℕ, k' ≤ w.length + 1 →
      hscore (hd1 c) fl (p.A 0 c) (net.init fl p w) k k' = fl (sw fl 40 (p.A 0 c 13 14) * fl (k' : ℝ)) := by
    intro k' hk'
    have hM1 : |sw fl 40 (p.A 0 c 13 14) * fl (k' : ℝ)| ≤ M := le_trans (hPb k' hk') (by linarith)
    simp only [hscore]
    rw [init_eq hr p w hw k, init_eq hr p w hw k']
    exact score1_eq hr (p.A 0 c) c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp) (fl (k' : ℝ)) (by simp)
      hM1 (hr.idem _ hM1)
  have hEb : ∀ τ : ℕ, |ee fl p τ c| ≤ 11 / 10 := by
    intro τ
    by_cases h : τ = c + 1
    · have := abs_le.mp (((hee τ c).1 h))
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    · rw [(hee τ c).2 h]; norm_num
  have hVb : |sw fl 1 (p.V 0 c (3 + c) c)| ≤ 11 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hVEb : ∀ τ : ℕ, |sw fl 1 (p.V 0 c (3 + c) c) * ee fl p τ c| ≤ 5 / 4 := by
    intro τ
    rw [abs_mul]
    have := mul_le_mul hVb (hEb τ) (abs_nonneg _) (by norm_num)
    linarith
  have hfk : ∀ j : ℕ, rdot fl (sp c (15 - c) 1) (net.init fl p w j) (p.V 0 c (3 + c)) 0 0
      = fl (sw fl 1 (p.V 0 c (3 + c) c) * ee fl p (tokAt w j) c) := by
    intro j
    rw [init_eq hr p w hw j]
    exact val1_eq hr c hc _ _ (by simp) _ (by interval_cases c <;> simp)
      (le_trans (hVEb _) (by linarith))
  have hj : k - 1 ∈ cand Mask.strict (w.length + 1) k := by
    rw [Lane4.Seq.mem_cand_strict]; omega
  have hlen : (cand Mask.strict (w.length + 1) k).length ≤ w.length + 1 := by
    simp [cand]; omega
  have hgap : ∀ k' ∈ cand Mask.strict (w.length + 1) k, k' ≠ k - 1 →
      hscore (hd1 c) fl (p.A 0 c) (net.init fl p w) k k'
        ≤ hscore (hd1 c) fl (p.A 0 c) (net.init fl p w) k (k - 1)
          - 16 * (ndist (k - 1) k' : ℝ) := by
    intro k' hk' hne
    rw [Lane4.Seq.mem_cand_strict] at hk'
    have hkj : k' < k - 1 := by omega
    rw [hsk k' (by omega), hsk (k - 1) (by omega), ndist_cast]
    have hg := hr.pos_gap hu0 hη (le_of_lt hkj) (show k - 1 ≤ w.length + 1 by omega) hn hnM
    have hgp := hr.gap hu0 (hPb k' (by omega)) (hPb (k - 1) (by omega)) (by linarith)
    have hd1' : ((k' : ℝ)) + 1 ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hkj
    rw [abs_of_nonneg (by linarith)]
    have hD0 : 0 ≤ fl ((k - 1 : ℕ) : ℝ) - fl (k' : ℝ) := by linarith
    have hSD := mul_le_mul_of_nonneg_right
      (show (39 : ℝ) ≤ sw fl 40 (p.A 0 c 13 14) by linarith) hD0
    have hun : u * (41 * ((w.length + 1 : ℕ) : ℝ)) = 41 * (u * ((w.length + 1 : ℕ) : ℝ)) := by ring
    linarith [hgp, hSD, hg, hd1', hn, hηs, hηs', hun]
  have hSb : ∀ k' ∈ cand Mask.strict (w.length + 1) k,
      |hscore (hd1 c) fl (p.A 0 c) (net.init fl p w) k k'| ≤ 41 * ((w.length + 1 : ℕ) : ℝ) + 1 := by
    intro k' hk'
    rw [Lane4.Seq.mem_cand_strict] at hk'
    rw [hsk k' (by omega)]
    have := hr.bound hu0 (hPb k' (by omega)) (by linarith)
    have hun : u * (41 * ((w.length + 1 : ℕ) : ℝ)) = 41 * (u * ((w.length + 1 : ℕ) : ℝ)) := by ring
    linarith
  have hfB : ∀ k' ∈ cand Mask.strict (w.length + 1) k,
      |(fun j => rdot fl (sp c (15 - c) 1) (net.init fl p w j) (p.V 0 c (3 + c)) 0 0) k'| ≤ 2 := by
    intro k' _
    show |rdot fl (sp c (15 - c) 1) (net.init fl p w k') (p.V 0 c (3 + c)) 0 0| ≤ 2
    rw [hfk k']
    have := hr.bound hu0 (hVEb (tokAt w k')) (by linarith)
    linarith
  have hA : |Pc fl ex p w c k - rdot fl (sp c (15 - c) 1) (net.init fl p w (k - 1))
        (p.V 0 c (3 + c)) 0 0| ≤ 2 / 100 + 1 / 2 ^ 90 ∧ fl (Pc fl ex p w c k) = Pc fl ex p w c k :=
    soft_near hr he hu0 hu1 hη0 hη (Lane4.Seq.cand_nodup _ _ _) hlen hn hnη hj hgap hSb
      (by linarith) hfB (by linarith [range_const hM hn1 (c := 12) (by norm_num)])
  obtain ⟨hA1, hA2⟩ := hA
  rw [hfk (k - 1)] at hA1
  have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 100000 := by norm_num
  have hfb := hr.bound hu0 (hVEb (tokAt w (k - 1))) (by linarith)
  have hAb := abs_le.mp hA1
  have hfb' := abs_le.mp hfb
  refine ⟨hA2, ?_, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · intro _ htk
    have e1 := mul_near (abs_le.mpr ⟨by linarith, by linarith⟩ : |sw fl 1 (p.V 0 c (3 + c) c) - 1| ≤ 1 / 190)
      ((hee (tokAt w (k - 1)) c).1 htk)
    rw [one_mul, abs_one] at e1
    have e1' : |sw fl 1 (p.V 0 c (3 + c) c) * ee fl p (tokAt w (k - 1)) c - 1| ≤ 1 / 90 := by
      linarith [e1]
    have e2 := hr.near hu0 e1' (hVEb _) (by linarith)
    have e3 := abs_le.mp e2
    linarith [e3.1, e3.2]
  · intro hnf
    have hne : tokAt w (k - 1) ≠ c + 1 := by
      rcases hnf with h | h
      · exact absurd h hk0
      · exact h
    rw [(hee _ c).2 hne, mul_zero, hr.zero, sub_zero] at hA1
    rw [abs_le] at hA1 ⊢
    constructor <;> linarith [hA1.1, hA1.2]

structure Ctx (u η M : ℝ) (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) : Prop where
  hr : Rnd u η M fl
  he : ExpM u η ex
  hu0 : 0 ≤ u
  hu1 : u ≤ 1 / 2 ^ 24
  hη0 : 0 ≤ η
  hη : η ≤ 1 / 2 ^ 149
  hp : p.Within (1 / 200)
  hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3
  hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256
  hnη : η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100
  hM : 2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M

theorem tok_pos (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (k : ℕ) (h1 : 1 ≤ k)
    (h2 : k ≤ w.length) : 1 ≤ tokAt w k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Lane4.Seq.tokAt_succ w k' (by omega)]
  exact (hw _ (List.getElem_mem (by omega))).1

theorem core_step {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) (h1000 : (1000 : ℝ) ≤ M)
    (sP P sb w2 : ℝ) (hsP : -252 ≤ sP ∧ sP ≤ -248) (hP : |P| ≤ 3 / 100)
    (hsb : 198 ≤ sb ∧ sb ≤ 202) (hw2 : 99 / 100 ≤ w2 ∧ w2 ≤ 101 / 100) :
    187 ≤ fl (w2 * relu (fl (fl (sP * P) + sb))) ∧
    fl (w2 * relu (fl (fl (sP * P) + sb))) ≤ 213 ∧
    fl (fl (w2 * relu (fl (fl (sP * P) + sb)))) = fl (w2 * relu (fl (fl (sP * P) + sb))) := by
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hz : |sP * P| ≤ 76 / 10 := by
    rw [abs_mul]
    have := mul_le_mul (abs_le.mpr ⟨by linarith [hsP.1], by linarith [hsP.2]⟩ : |sP| ≤ 252) hP
      (abs_nonneg _) (by norm_num)
    linarith
  have hfz := abs_le.mp (hr.abs hu0 hz (by linarith))
  have hz2 := abs_le.mp hz
  have hy_abs : |fl (sP * P) + sb| ≤ 210 := by
    rw [abs_le]; constructor <;> linarith [hfz.1, hfz.2, hz2.1, hz2.2, hsb.1, hsb.2]
  have hfy := abs_le.mp (hr.abs hu0 hy_abs (by linarith))
  have hy1 : 190 ≤ fl (fl (sP * P) + sb) := by
    linarith [hfz.1, hfz.2, hz2.1, hz2.2, hsb.1, hsb.2, hfy.1, hfy.2]
  have hy2 : fl (fl (sP * P) + sb) ≤ 210 := by
    linarith [hfz.1, hfz.2, hz2.1, hz2.2, hsb.1, hsb.2, hfy.1, hfy.2]
  have hr0 : relu (fl (fl (sP * P) + sb)) = fl (fl (sP * P) + sb) := relu_of_nonneg (by linarith)
  rw [hr0]
  have hxl : 99 / 100 * 190 ≤ w2 * fl (fl (sP * P) + sb) :=
    mul_le_mul hw2.1 hy1 (by norm_num) (by linarith)
  have hxu : w2 * fl (fl (sP * P) + sb) ≤ 101 / 100 * 210 :=
    mul_le_mul hw2.2 hy2 (by linarith) (by norm_num)
  have hxa : |w2 * fl (fl (sP * P) + sb)| ≤ 213 := by
    rw [abs_le]; constructor <;> linarith
  have hfx := abs_le.mp (hr.abs hu0 hxa (by linarith))
  refine ⟨by linarith [hfx.1, hfx.2], by linarith [hfx.1, hfx.2], hr.idem _ (by linarith)⟩

theorem fl_ee {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hM40 : (40 : ℝ) ≤ M) (p : Pert)
    (hp : p.Within (1 / 200)) (τ c : ℕ) : fl (ee fl p τ c) = ee fl p τ c := by
  unfold ee
  split_ifs with h
  · exact fl_sw hr 1 (hp.E τ c) (by norm_num) (by norm_num; linarith)
  · exact hr.zero

theorem fl_eg {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hM : (300 : ℝ) ≤ M) (p : Pert)
    (hp : p.Within (1 / 200)) (τ c : ℕ) : fl (eg fl p τ c) = eg fl p τ c := by
  unfold eg
  split_ifs with h
  · exact fl_sw hr (-150) (hp.E 0 (6 + c)) (by norm_num) (by norm_num; linarith)
  · exact hr.zero

noncomputable def Ha (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (c k : ℕ) : ℝ :=
  fl (fl (sw fl (-250) (p.W1 0 c (3 + c)) * Pc fl ex p w c k) + sw fl 200 (p.b1 0 c))

noncomputable def Gc (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (c k : ℕ) : ℝ :=
  fl (eg fl p (tokAt w k) c + fl (sw fl 1 (p.W2 0 (6 + c) c) * relu (Ha fl ex p w c k)))

theorem Gfact {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (c : ℕ) (hc : c < 3) (k : ℕ) (hk : k ≤ w.length) :
    (1 ≤ k → tokAt w (k - 1) = c + 1 → Gc fl ex p w c k = 0) ∧
    (1 ≤ k → tokAt w (k - 1) ≠ c + 1 → 185 ≤ Gc fl ex p w c k ∧ Gc fl ex p w c k ≤ 215) ∧
    (k = 0 → 35 ≤ Gc fl ex p w c k ∧ Gc fl ex p w c k ≤ 65) := by
  obtain ⟨hr, he, hu0, hu1, hη0, hη, hp, hw, hn, hnη, hM⟩ := H
  have hn1 : 1 ≤ w.length + 1 := by omega
  have h1000 : (1000 : ℝ) ≤ M := range_const hM hn1 (by norm_num)
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by linarith
  obtain ⟨hPfl, hPb2, hPf, hPn⟩ := Pfact hr he hu0 hu1 hη0 hη p hp w hw hn hnη hM c hc k hk
  have c250 : (((-250 : ℚ)) : ℝ) = -250 := by norm_num
  have hsP := sw_near hr hu0 (-250) (hp.W1 0 c (3 + c)) (by norm_num)
    (by rw [c250]; norm_num; linarith) hε
  have a250 : |(-250 : ℝ)| = 250 := by norm_num
  rw [c250, a250] at hsP
  obtain ⟨hsP1, hsP2⟩ := abs_le.mp hsP
  have c200 : ((200 : ℚ) : ℝ) = 200 := by norm_num
  have hsb := sw_near hr hu0 200 (hp.b1 0 c) (by norm_num) (by rw [c200]; norm_num; linarith) hε
  rw [c200, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 200)] at hsb
  obtain ⟨hsb1, hsb2⟩ := abs_le.mp hsb
  have c1 : ((1 : ℚ) : ℝ) = 1 := by norm_num
  have hw2 := sw_near hr hu0 1 (hp.W2 0 (6 + c) c) (by norm_num) (by rw [c1]; norm_num; linarith) hε
  rw [c1, abs_one] at hw2
  obtain ⟨hw21, hw22⟩ := abs_le.mp hw2
  have hcore : |Pc fl ex p w c k| ≤ 3 / 100 →
      187 ≤ fl (sw fl 1 (p.W2 0 (6 + c) c) * relu (Ha fl ex p w c k)) ∧
      fl (sw fl 1 (p.W2 0 (6 + c) c) * relu (Ha fl ex p w c k)) ≤ 213 ∧
      fl (fl (sw fl 1 (p.W2 0 (6 + c) c) * relu (Ha fl ex p w c k)))
        = fl (sw fl 1 (p.W2 0 (6 + c) c) * relu (Ha fl ex p w c k)) := by
    intro hP
    unfold Ha
    exact core_step hr hu0 hu1 hη h1000 _ _ _ _ ⟨by linarith, by linarith⟩ hP
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h1 htk
    have hP := hPf h1 htk
    have hsPn : sw fl (-250) (p.W1 0 c (3 + c)) ≤ 0 := by linarith
    have hz : sw fl (-250) (p.W1 0 c (3 + c)) * Pc fl ex p w c k ≤ -236 := by
      have h := mul_le_mul_of_nonpos_left hP hsPn
      linarith
    have hzb : |sw fl (-250) (p.W1 0 c (3 + c)) * Pc fl ex p w c k| ≤ 504 := by
      rw [abs_mul]
      have := mul_le_mul (abs_le.mpr ⟨by linarith, by linarith⟩ :
        |sw fl (-250) (p.W1 0 c (3 + c))| ≤ 252) hPb2 (abs_nonneg _) (by norm_num)
      linarith
    have hup := hr.upper hu0 hzb (by linarith)
    have hbd := abs_le.mp (hr.bound hu0 hzb (by linarith))
    have hy : fl (sw fl (-250) (p.W1 0 c (3 + c)) * Pc fl ex p w c k) + sw fl 200 (p.b1 0 c) ≤ 0 := by
      linarith
    have h0 := hr.nonpos hy (by linarith [hbd.1])
    have hH : relu (Ha fl ex p w c k) = 0 := relu_of_nonpos h0
    have heg0 : eg fl p (tokAt w k) c = 0 := by
      have := tok_pos w hw k h1 hk
      have hne0 : tokAt w k ≠ 0 := by omega
      unfold eg
      rw [if_neg hne0]
    unfold Gc
    rw [hH, mul_zero, hr.zero, add_zero, heg0, hr.zero]
  · intro h1 hne
    obtain ⟨hl, hu, hid⟩ := hcore (hPn (Or.inr hne))
    have heg0 : eg fl p (tokAt w k) c = 0 := by
      have := tok_pos w hw k h1 hk
      have hne0 : tokAt w k ≠ 0 := by omega
      unfold eg
      rw [if_neg hne0]
    unfold Gc
    rw [heg0, zero_add, hid]
    exact ⟨by linarith, by linarith⟩
  · intro h0
    subst h0
    obtain ⟨hl, hu, hid⟩ := hcore (hPn (Or.inl rfl))
    have heg : eg fl p (tokAt w 0) c = sw fl (-150) (p.E 0 (6 + c)) := by
      simp [eg, Lane4.Seq.tokAt_zero]
    have c150 : (((-150 : ℚ)) : ℝ) = -150 := by norm_num
    have a150 : |(-150 : ℝ)| = 150 := by norm_num
    have hE := sw_near hr hu0 (-150) (hp.E 0 (6 + c)) (by norm_num)
      (by rw [c150]; norm_num; linarith) hε
    rw [c150, a150] at hE
    obtain ⟨hE1, hE2⟩ := abs_le.mp hE
    unfold Gc
    rw [heg]
    have hya : |sw fl (-150) (p.E 0 (6 + c)) + fl (sw fl 1 (p.W2 0 (6 + c) c) * relu (Ha fl ex p w c 0))| ≤ 100 := by
      rw [abs_le]; constructor <;> linarith
    have hf := abs_le.mp (hr.abs hu0 hya (by linarith))
    constructor <;> linarith [hf.1, hf.2]

noncomputable def Ylist (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (k : ℕ) : List ℝ :=
  [ee fl p (tokAt w k) 0, ee fl p (tokAt w k) 1, ee fl p (tokAt w k) 2,
   Pc fl ex p w 0 k, Pc fl ex p w 1 k, Pc fl ex p w 2 k,
   eg fl p (tokAt w k) 0, eg fl p (tokAt w k) 1, eg fl p (tokAt w k) 2, 0, 0, 0, 0,
   1, fl (k : ℝ), fl ((w.length + 1 : ℕ) : ℝ)]

noncomputable def Hl (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (k : ℕ) : List ℝ :=
  [relu (Ha fl ex p w 0 k), relu (Ha fl ex p w 1 k), relu (Ha fl ex p w 2 k)]

theorem Pfl {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (c : ℕ) (hc : c < 3) (k : ℕ) (hk : k ≤ w.length) :
    fl (Pc fl ex p w c k) = Pc fl ex p w c k :=
  (Pfact H.hr H.he H.hu0 H.hu1 H.hη0 H.hη p H.hp w H.hw H.hn H.hnη H.hM c hc k hk).1

theorem Y_eq {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (k : ℕ) (hk : k ≤ w.length) :
    sheadsApply fl ex blk1.heads (p.A 0) (p.V 0) (w.length + 1) (net.init fl p w) k
        (net.init fl p w k) 0 = Ylist fl ex p w k := by
  have hP0 := Pfl H 0 (by norm_num) k hk
  have hP1 := Pfl H 1 (by norm_num) k hk
  have hP2 := Pfl H 2 (by norm_num) k hk
  obtain ⟨hr, he, hu0, hu1, hη0, hη, hp, hw, hn, hnη, hM⟩ := H
  have hn1 : 1 ≤ w.length + 1 := by omega
  have h300 : (300 : ℝ) ≤ M := range_const hM hn1 (by norm_num)
  have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
    have := range_lin hM hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have hk1 : fl (fl (k : ℝ)) = fl (k : ℝ) := by
    apply hr.idem
    rw [abs_of_nonneg (Nat.cast_nonneg k)]
    have : (k : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : k ≤ w.length + 1)
    linarith
  have hn1' : fl (fl (((w.length + 1 : ℕ) : ℝ))) = fl (((w.length + 1 : ℕ) : ℝ)) := by
    apply hr.idem
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact hnM
  simp only [Ylist, blk1, sheadsApply, Nat.reduceAdd, zero_add]
  rw [attn1_0 hr p w k, attn1_1 hr p w k, attn1_2 hr p w k, init_eq hr p w hw k]
  simp only [radd, add_zero, zero_add, fl_ee hr (by linarith : (40 : ℝ) ≤ M) p hp,
    fl_eg hr h300 p hp, hP0, hP1, hP2, hr.zero, hr.one, hk1, hn1']

theorem Ha_bd {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (c : ℕ) (hc : c < 3) (k : ℕ) (hk : k ≤ w.length) :
    |sw fl (-250) (p.W1 0 c (3 + c)) * Pc fl ex p w c k| ≤ 504 ∧ |Ha fl ex p w c k| ≤ 708 := by
  obtain ⟨hPfl, hPb2, hPf, hPn⟩ := Pfact H.hr H.he H.hu0 H.hu1 H.hη0 H.hη p H.hp w H.hw H.hn
    H.hnη H.hM c hc k hk
  obtain ⟨hr, he, hu0, hu1, hη0, hη, hp, hw, hn, hnη, hM⟩ := H
  have hn1 : 1 ≤ w.length + 1 := by omega
  have h1000 : (1000 : ℝ) ≤ M := range_const hM hn1 (by norm_num)
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by linarith
  have c250 : (((-250 : ℚ)) : ℝ) = -250 := by norm_num
  have hsP := sw_near hr hu0 (-250) (hp.W1 0 c (3 + c)) (by norm_num)
    (by rw [c250]; norm_num; linarith) hε
  have a250 : |(-250 : ℝ)| = 250 := by norm_num
  rw [c250, a250] at hsP
  obtain ⟨hsP1, hsP2⟩ := abs_le.mp hsP
  have c200 : ((200 : ℚ) : ℝ) = 200 := by norm_num
  have hsb := sw_near hr hu0 200 (hp.b1 0 c) (by norm_num) (by rw [c200]; norm_num; linarith) hε
  rw [c200, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 200)] at hsb
  obtain ⟨hsb1, hsb2⟩ := abs_le.mp hsb
  have hzb : |sw fl (-250) (p.W1 0 c (3 + c)) * Pc fl ex p w c k| ≤ 504 := by
    rw [abs_mul]
    have := mul_le_mul (abs_le.mpr ⟨by linarith, by linarith⟩ :
      |sw fl (-250) (p.W1 0 c (3 + c))| ≤ 252) hPb2 (abs_nonneg _) (by norm_num)
    linarith
  refine ⟨hzb, ?_⟩
  have hbd := abs_le.mp (hr.bound hu0 hzb (by linarith))
  have hy : |fl (sw fl (-250) (p.W1 0 c (3 + c)) * Pc fl ex p w c k) + sw fl 200 (p.b1 0 c)| ≤ 707 := by
    rw [abs_le]; constructor <;> linarith [hbd.1, hbd.2]
  have := abs_le.mp (hr.bound hu0 hy (by linarith))
  unfold Ha
  rw [abs_le]; constructor <;> linarith [this.1, this.2]

theorem hid_eq {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (c : ℕ) (hc : c < 3) (k : ℕ) (hk : k ≤ w.length) :
    fl (rdot fl (sp (3 + c) (12 - c) (-250)) (Ylist fl ex p w k) (p.W1 0 c) 0 0
        + sw fl 200 (p.b1 0 c)) = Ha fl ex p w c k := by
  have hb := (Ha_bd H c hc k hk).1
  have hM1000 : (1000 : ℝ) ≤ M := range_const H.hM (by omega : 1 ≤ w.length + 1) (by norm_num)
  have hg : (Ylist fl ex p w k).getD (3 + c) 0 = Pc fl ex p w c k := by
    interval_cases c <;> simp [Ylist]
  have := rdot_sp H.hr (3 + c) (12 - c) (-250) (Ylist fl ex p w k) (p.W1 0 c) 0
    (by simp only [Ylist, List.length_cons, List.length_nil]; omega)
    (by rw [hg, zero_add]; linarith)
  rw [hg, zero_add] at this
  unfold Ha
  rw [this]

theorem out_eq {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (c : ℕ) (hc : c < 3) (k : ℕ) (hk : k ≤ w.length) :
    fl (rdot fl (sp c (2 - c) 1) (Hl fl ex p w k) (p.W2 0 (6 + c)) 0 0
        + sw fl 0 (p.b2 0 (6 + c)))
      = fl (sw fl 1 (p.W2 0 (6 + c) c) * relu (Ha fl ex p w c k)) := by
  have hb := (Ha_bd H c hc k hk).2
  have hM1000 : (1000 : ℝ) ≤ M := range_const H.hM (by omega : 1 ≤ w.length + 1) (by norm_num)
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by linarith [H.hu0, H.hu1]
  have c1 : ((1 : ℚ) : ℝ) = 1 := by norm_num
  have hw2 := sw_near H.hr H.hu0 1 (H.hp.W2 0 (6 + c) c) (by norm_num)
    (by rw [c1]; norm_num; linarith) hε
  rw [c1, abs_one] at hw2
  have hηs := eta_tiny H.hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hw3 := abs_le.mp hw2
  have h0 : 0 ≤ relu (Ha fl ex p w c k) := le_max_right _ _
  have h1 : relu (Ha fl ex p w c k) ≤ 708 :=
    max_le (le_trans (le_abs_self _) hb) (by norm_num)
  have hsw : |sw fl 1 (p.W2 0 (6 + c) c)| ≤ 11 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hm : |sw fl 1 (p.W2 0 (6 + c) c) * relu (Ha fl ex p w c k)| ≤ M := by
    rw [abs_mul, abs_of_nonneg h0]
    have := mul_le_mul hsw h1 h0 (by norm_num)
    linarith
  have hg : (Hl fl ex p w k).getD c 0 = relu (Ha fl ex p w c k) := by
    interval_cases c <;> simp [Hl]
  have := rdot_sp H.hr c (2 - c) 1 (Hl fl ex p w k) (p.W2 0 (6 + c)) 0
    (by simp only [Hl, List.length_cons, List.length_nil]; omega)
    (by rw [hg, zero_add]; exact hm)
  rw [hg, zero_add] at this
  rw [this, sw_zero H.hr, add_zero]
  exact H.hr.idem _ hm

theorem x1_eq {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (k : ℕ) (hk : k ≤ w.length) :
    sblock blk1 fl ex p 0 (w.length + 1) (net.init fl p w) k =
      [ee fl p (tokAt w k) 0, ee fl p (tokAt w k) 1, ee fl p (tokAt w k) 2,
       Pc fl ex p w 0 k, Pc fl ex p w 1 k, Pc fl ex p w 2 k,
       Gc fl ex p w 0 k, Gc fl ex p w 1 k, Gc fl ex p w 2 k, 0, 0, 0, 0, 1,
       fl (k : ℝ), fl ((w.length + 1 : ℕ) : ℝ)] := by
  have hY := Y_eq H k hk
  have hh0 : fl (rdot fl (sp 3 12 (-250)) (Ylist fl ex p w k) (p.W1 0 0) 0 0
      + sw fl 200 (p.b1 0 0)) = Ha fl ex p w 0 k := hid_eq H 0 (by norm_num) k hk
  have hh1 : fl (rdot fl (sp 4 11 (-250)) (Ylist fl ex p w k) (p.W1 0 1) 0 0
      + sw fl 200 (p.b1 0 1)) = Ha fl ex p w 1 k := hid_eq H 1 (by norm_num) k hk
  have hh2 : fl (rdot fl (sp 5 10 (-250)) (Ylist fl ex p w k) (p.W1 0 2) 0 0
      + sw fl 200 (p.b1 0 2)) = Ha fl ex p w 2 k := hid_eq H 2 (by norm_num) k hk
  have ho0 : fl (rdot fl (sp 0 2 1) (Hl fl ex p w k) (p.W2 0 6) 0 0 + sw fl 0 (p.b2 0 6))
      = fl (sw fl 1 (p.W2 0 6 0) * relu (Ha fl ex p w 0 k)) := out_eq H 0 (by norm_num) k hk
  have ho1 : fl (rdot fl (sp 1 1 1) (Hl fl ex p w k) (p.W2 0 7) 0 0 + sw fl 0 (p.b2 0 7))
      = fl (sw fl 1 (p.W2 0 7 1) * relu (Ha fl ex p w 1 k)) := out_eq H 1 (by norm_num) k hk
  have ho2 : fl (rdot fl (sp 2 0 1) (Hl fl ex p w k) (p.W2 0 8) 0 0 + sw fl 0 (p.b2 0 8))
      = fl (sw fl 1 (p.W2 0 8 2) * relu (Ha fl ex p w 2 k)) := out_eq H 2 (by norm_num) k hk
  have hP0 := Pfl H 0 (by norm_num) k hk
  have hP1 := Pfl H 1 (by norm_num) k hk
  have hP2 := Pfl H 2 (by norm_num) k hk
  obtain ⟨hr, he, hu0, hu1, hη0, hη, hp, hw, hn, hnη, hM⟩ := H
  have hn1 : 1 ≤ w.length + 1 := by omega
  have h300 : (300 : ℝ) ≤ M := range_const hM hn1 (by norm_num)
  have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
    have := range_lin hM hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have hk1 : fl (fl (k : ℝ)) = fl (k : ℝ) := by
    apply hr.idem
    rw [abs_of_nonneg (Nat.cast_nonneg k)]
    have : (k : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : k ≤ w.length + 1)
    linarith
  have hn1' : fl (fl (((w.length + 1 : ℕ) : ℝ))) = fl (((w.length + 1 : ℕ) : ℝ)) := by
    apply hr.idem
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact hnM
  simp only [sblock]
  rw [hY]
  simp only [blk1, raffine, zb, Nat.reduceAdd, zero_add, List.map]
  rw [hh0, hh1, hh2]
  simp only [Hl] at ho0 ho1 ho2
  rw [ho0, ho1, ho2]
  simp only [rdot_zr3 hr, sw_zero hr, add_zero, zero_add, hr.zero, Ylist, radd, Gc,
    fl_ee hr (by linarith : (40 : ℝ) ≤ M) p hp, fl_eg hr h300 p hp, hP0, hP1, hP2, hr.one,
    hk1, hn1', Nat.reduceAdd]

noncomputable def X1 (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) : ℕ → Vec :=
  sblock blk1 fl ex p 0 (w.length + 1) (net.init fl p w)

noncomputable def x1l (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (k : ℕ) : List ℝ :=
  [ee fl p (tokAt w k) 0, ee fl p (tokAt w k) 1, ee fl p (tokAt w k) 2,
   Pc fl ex p w 0 k, Pc fl ex p w 1 k, Pc fl ex p w 2 k,
   Gc fl ex p w 0 k, Gc fl ex p w 1 k, Gc fl ex p w 2 k, 0, 0, 0, 0, 1,
   fl (k : ℝ), fl ((w.length + 1 : ℕ) : ℝ)]

theorem X1_eq {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (k : ℕ) (hk : k ≤ w.length) : X1 fl ex p w k = x1l fl ex p w k := by
  unfold X1 x1l
  exact x1_eq H k hk

theorem Gc_rng {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (c : ℕ) (hc : c < 3) (k : ℕ) (hk : k ≤ w.length) :
    0 ≤ Gc fl ex p w c k ∧ Gc fl ex p w c k ≤ 215 := by
  obtain ⟨h1, h2, h3⟩ := Gfact H c hc k hk
  by_cases hk0 : k = 0
  · have := h3 hk0
    constructor <;> linarith [this.1, this.2]
  · have hk1 : 1 ≤ k := by omega
    by_cases ht : tokAt w (k - 1) = c + 1
    · rw [h1 hk1 ht]; constructor <;> norm_num
    · have := h2 hk1 ht
      constructor <;> linarith [this.1, this.2]

theorem w2_facts {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (c : ℕ) (hc : c < 3) :
    (39 + 79 / 100 ≤ sw fl 40 (p.A 1 c 13 14) ∧ sw fl 40 (p.A 1 c 13 14) ≤ 40 + 21 / 100) ∧
    (-101 / 100 ≤ sw fl (-1) (p.A 1 c 15 (6 + c)) ∧ sw fl (-1) (p.A 1 c 15 (6 + c)) ≤ -99 / 100) ∧
    |sw fl 2 (p.V 1 c (9 + c) 1) - 2| ≤ 101 / 10000 := by
  have hr := H.hr
  have hu0 := H.hu0
  have h1000 : (1000 : ℝ) ≤ M := range_const H.hM (by omega : 1 ≤ w.length + 1) (by norm_num)
  have hηs := eta_tiny H.hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hu1 := H.hu1
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by linarith
  have c40 : ((40 : ℚ) : ℝ) = 40 := by norm_num
  have hS := sw_near hr hu0 40 (H.hp.A 1 c 13 14) (by norm_num) (by rw [c40]; norm_num; linarith) hε
  rw [c40, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 40)] at hS
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  have cm1 : (((-1 : ℚ)) : ℝ) = -1 := by norm_num
  have hB := sw_near hr hu0 (-1) (H.hp.A 1 c 15 (6 + c)) (by norm_num)
    (by rw [cm1]; norm_num; linarith) hε
  rw [cm1, abs_neg, abs_one] at hB
  obtain ⟨hB1, hB2⟩ := abs_le.mp hB
  have c2 : ((2 : ℚ) : ℝ) = 2 := by norm_num
  have hV := sw_near hr hu0 2 (H.hp.V 1 c (9 + c) 1) (by norm_num)
    (by rw [c2]; norm_num; linarith) hε
  rw [c2, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hV
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ?_⟩
  rw [abs_le] at hV ⊢
  constructor <;> linarith [hV.1, hV.2]

theorem s2_est {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) {N : ℝ} (hN : 2 ≤ N) (hn : u * N ≤ 1 / 256)
    (hnη : η * N ≤ 1 / 2 ^ 100) (hNM : 300 * N ≤ M) (a qk b g nq : ℝ)
    (ha : 39 ≤ a ∧ a ≤ 41) (hqk : 0 ≤ qk ∧ qk ≤ N + 1 / 100)
    (hb : -101 / 100 ≤ b ∧ b ≤ -99 / 100) (hg : 0 ≤ g ∧ g ≤ 215) (hnq : |nq - N| ≤ 1 / 200) :
    |fl (fl (a * qk) + fl (nq * fl (b * g))) - (a * qk + nq * (b * g))| ≤ 4 ∧
    |fl (fl (a * qk) + fl (nq * fl (b * g)))| ≤ 302 * N := by
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hnq' := abs_le.mp hnq
  have hnq0 : 0 ≤ nq := by linarith
  have hAq : 0 ≤ a * qk := mul_nonneg (by linarith) hqk.1
  have hAq2 : a * qk ≤ 41 * (N + 1 / 100) := mul_le_mul ha.2 hqk.2 hqk.1 (by norm_num)
  have hA : |a * qk| ≤ 42 * N := by
    rw [abs_of_nonneg hAq]; linarith
  have e1 := abs_le.mp (hr.abs hu0 hA (by linarith))
  have hbg1 : b * g ≤ -99 / 100 * g := mul_le_mul_of_nonneg_right hb.2 hg.1
  have hbg2 : -101 / 100 * g ≤ b * g := mul_le_mul_of_nonneg_right hb.1 hg.1
  have hbg : |b * g| ≤ 218 := by
    rw [abs_le]; constructor <;> linarith
  have e2 := abs_le.mp (hr.abs hu0 hbg (by linarith))
  have e2' : |fl (b * g)| ≤ 219 := by
    rw [abs_le]; constructor <;> linarith [e2.1, e2.2]
  have ht : |nq * fl (b * g)| ≤ 220 * N := by
    rw [abs_mul]
    have := mul_le_mul (show |nq| ≤ N + 1 / 200 by rw [abs_of_nonneg hnq0]; linarith) e2'
      (abs_nonneg _) (by linarith)
    linarith
  have e3 := abs_le.mp (hr.abs hu0 ht (by linarith))
  have d2 : |nq * fl (b * g) - nq * (b * g)| ≤ (N + 1 / 200) * (u * 218 + η) := by
    have : nq * fl (b * g) - nq * (b * g) = nq * (fl (b * g) - b * g) := by ring
    rw [this, abs_mul]
    have h1 : |fl (b * g) - b * g| ≤ u * 218 + η := hr.abs hu0 hbg (by linarith)
    exact mul_le_mul (show |nq| ≤ N + 1 / 200 by rw [abs_of_nonneg hnq0]; linarith) h1
      (abs_nonneg _) (by linarith)
  have d2' := abs_le.mp d2
  have hsum : |fl (a * qk) + fl (nq * fl (b * g))| ≤ 300 * N := by
    have hA' := abs_le.mp hA
    have ht' := abs_le.mp ht
    rw [abs_le]
    constructor <;> linarith [e1.1, e1.2, e3.1, e3.2, hA'.1, hA'.2, ht'.1, ht'.2, hn, hηs, hηs']
  have e4 := abs_le.mp (hr.abs hu0 hsum (by linarith))
  have hexp : (N + 1 / 200) * (u * 218 + η) = 218 * (u * N) + 218 / 200 * u + η * N + η / 200 := by
    ring
  refine ⟨?_, ?_⟩
  · rw [abs_le]
    constructor <;> nlinarith [e1.1, e1.2, e3.1, e3.2, e4.1, e4.2, d2'.1, d2'.2, hexp, hn, hnη, hu1]
  · have := hr.bound hu0 hsum (by linarith)
    have hun : u * (300 * N) = 300 * (u * N) := by ring
    linarith [hn, hηs, hηs', hun]

theorem s_eq {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (c : ℕ) (hc : c < 3) (i k : ℕ) (hi : i ≤ w.length) (hk : k ≤ w.length) :
    hscore (hd2 c) fl (p.A 1 c) (X1 fl ex p w) i k
      = fl (fl (sw fl 40 (p.A 1 c 13 14) * fl (k : ℝ)) +
          fl (fl (((w.length + 1 : ℕ) : ℝ)) *
            fl (sw fl (-1) (p.A 1 c 15 (6 + c)) * Gc fl ex p w c k))) := by
  obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hv⟩ := w2_facts H c hc
  obtain ⟨hG0, hG1⟩ := Gc_rng H c hc k hk
  have hr := H.hr
  have hn1 : 1 ≤ w.length + 1 := by omega
  have hnR : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hn1
  have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
    have := range_lin H.hM hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have h45 : 45 * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin H.hM hn1 (by norm_num) (by norm_num)
  have h1000 : (1000 : ℝ) ≤ M := range_const H.hM hn1 (by norm_num)
  obtain ⟨hk0, hk1⟩ := hr.pos_le H.hu0 H.hη (show k ≤ w.length + 1 by omega) H.hn hnM
  have hM1 : |sw fl 40 (p.A 1 c 13 14) * fl (k : ℝ)| ≤ M := by
    rw [abs_of_nonneg (mul_nonneg (by linarith) hk0)]
    have := mul_le_mul (show sw fl 40 (p.A 1 c 13 14) ≤ 41 by linarith) hk1 hk0 (by norm_num)
    linarith
  have hM2 : |sw fl (-1) (p.A 1 c 15 (6 + c)) * Gc fl ex p w c k| ≤ M := by
    rw [abs_mul]
    have := mul_le_mul (show |sw fl (-1) (p.A 1 c 15 (6 + c))| ≤ 11 / 10 from
      abs_le.mpr ⟨by linarith, by linarith⟩) (show |Gc fl ex p w c k| ≤ 215 by
        rw [abs_of_nonneg hG0]; exact hG1) (abs_nonneg _) (by norm_num)
    linarith
  simp only [hscore]
  rw [X1_eq H i hi, X1_eq H k hk]
  unfold x1l
  exact score2_eq hr (p.A 1 c) c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp) (fl (k : ℝ))
    (Gc fl ex p w c k) hc (by simp) (by interval_cases c <;> simp) hM1 hM2 (hr.idem _ hM1)

theorem val2_eq {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (c : ℕ) (hc : c < 3) (j : ℕ) (hj : j ≤ w.length) :
    rdot fl (sp 1 14 2) (X1 fl ex p w j) (p.V 1 c (9 + c)) 0 0
      = fl (sw fl 2 (p.V 1 c (9 + c) 1) * ee fl p (tokAt w j) 1) := by
  have hee := ee_facts H.hr H.hu0 H.hu1 H.hη
    (range_const H.hM (by omega : 1 ≤ w.length + 1) (by norm_num)) p H.hp (tokAt w j) 1
  have hEb : |ee fl p (tokAt w j) 1| ≤ 11 / 10 := by
    by_cases h : tokAt w j = 1 + 1
    · have := abs_le.mp ((hee.1 h))
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    · rw [hee.2 h]; norm_num
  obtain ⟨_, _, hv⟩ := w2_facts H c hc
  have h1000 : (1000 : ℝ) ≤ M := range_const H.hM (by omega : 1 ≤ w.length + 1) (by norm_num)
  have hm : |sw fl 2 (p.V 1 c (9 + c) 1) * ee fl p (tokAt w j) 1| ≤ M := by
    rw [abs_mul]
    have hs : |sw fl 2 (p.V 1 c (9 + c) 1)| ≤ 21 / 10 := abs_le.mpr ⟨by
      linarith [(abs_le.mp hv).1], by linarith [(abs_le.mp hv).2]⟩
    have := mul_le_mul hs hEb (abs_nonneg _) (by norm_num)
    linarith
  have hg : (X1 fl ex p w j).getD 1 0 = ee fl p (tokAt w j) 1 := by
    rw [X1_eq H j hj]; simp [x1l]
  have := rdot_sp H.hr 1 14 2 (X1 fl ex p w j) (p.V 1 c (9 + c)) 0
    (by rw [X1_eq H j hj]; simp [x1l]) (by rw [hg, zero_add]; exact hm)
  rw [hg, zero_add] at this
  exact this

noncomputable def Ao (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (c i : ℕ) : ℝ :=
  savg fl ex (cand Mask.causal (w.length + 1) i)
    (hscore (hd2 c) fl (p.A 1 c) (X1 fl ex p w) i)
    (fun j => rdot fl (sp 1 14 2) (X1 fl ex p w j) (p.V 1 c (9 + c)) 0 0)

def Wp (w : List ℕ) (τ i W : ℕ) : Prop :=
  (1 ≤ W ∧ W ≤ i ∧ tokAt w (W - 1) = τ ∧ ∀ m, W < m → m ≤ i → tokAt w (m - 1) ≠ τ) ∨
  (W = 0 ∧ ∀ m, 1 ≤ m → m ≤ i → tokAt w (m - 1) ≠ τ)

theorem head2 {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (c : ℕ) (hc : c < 3) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) (W : ℕ)
    (hW : Wp w (c + 1) i W) :
    fl (Ao fl ex p w c i) = Ao fl ex p w c i ∧
    |Ao fl ex p w c i - fl (sw fl 2 (p.V 1 c (9 + c) 1) * ee fl p (tokAt w W) 1)|
      ≤ 3 / 100 + 1 / 2 ^ 90 := by
  obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hv⟩ := w2_facts H c hc
  have hr := H.hr
  have hu0 := H.hu0
  have hu1 := H.hu1
  have hη := H.hη
  have hn := H.hn
  have hnη := H.hnη
  have hn1 : 1 ≤ w.length + 1 := by omega
  have hN2 : (2 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    have : 2 ≤ w.length + 1 := by omega
    exact_mod_cast this
  have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
    have := range_lin H.hM hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have h604 : 604 * ((w.length + 1 : ℕ) : ℝ) ≤ M := range_lin H.hM hn1 (by norm_num) (by norm_num)
  have h1000 : (1000 : ℝ) ≤ M := range_const H.hM hn1 (by norm_num)
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hlenR : ((w.length : ℕ) : ℝ) = ((w.length + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
  have hnq : |fl (((w.length + 1 : ℕ) : ℝ)) - ((w.length + 1 : ℕ) : ℝ)| ≤ 1 / 200 :=
    hr.pos_near hu0 hη (le_refl (w.length + 1)) hn hnM
  have hposle : ∀ k : ℕ, k ≤ w.length →
      0 ≤ fl (k : ℝ) ∧ fl (k : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) + 1 / 100 := fun k hk =>
    hr.pos_le hu0 hη (show k ≤ w.length + 1 by omega) hn hnM
  have hposn : ∀ k : ℕ, k ≤ w.length → |fl (k : ℝ) - (k : ℝ)| ≤ 1 / 200 := fun k hk =>
    hr.pos_near hu0 hη (show k ≤ w.length + 1 by omega) hn hnM
  have hkR : ∀ k : ℕ, k ≤ w.length → (k : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) - 1 := by
    intro k hk
    have : (k : ℝ) ≤ (w.length : ℝ) := by exact_mod_cast hk
    linarith
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = sw fl 40 (p.A 1 c 13 14) := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : ℝ, b = sw fl (-1) (p.A 1 c 15 (6 + c)) := ⟨_, rfl⟩
  rw [← ha_def] at ha1 ha2
  rw [← hb_def] at hb1 hb2
  have hsk : ∀ k : ℕ, k ≤ w.length →
      hscore (hd2 c) fl (p.A 1 c) (X1 fl ex p w) i k
        = fl (fl (a * fl (k : ℝ)) + fl (fl (((w.length + 1 : ℕ) : ℝ)) *
            fl (b * Gc fl ex p w c k))) := by
    intro k hk
    rw [ha_def, hb_def]
    exact s_eq H c hc i k hi hk
  have hs2 : ∀ k : ℕ, k ≤ w.length →
      |hscore (hd2 c) fl (p.A 1 c) (X1 fl ex p w) i k
        - (a * fl (k : ℝ) + fl (((w.length + 1 : ℕ) : ℝ)) * (b * Gc fl ex p w c k))| ≤ 4 ∧
      |hscore (hd2 c) fl (p.A 1 c) (X1 fl ex p w) i k| ≤ 302 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    rw [hsk k hk]
    exact s2_est hr hu0 hu1 hη hN2 hn hnη (by linarith) a (fl (k : ℝ)) b (Gc fl ex p w c k)
      (fl (((w.length + 1 : ℕ) : ℝ))) ⟨by linarith, by linarith⟩ (hposle k hk) ⟨hb1, hb2⟩
      (Gc_rng H c hc k hk) hnq
  have hAb : ∀ k : ℕ, k ≤ w.length → |a * fl (k : ℝ)| ≤ 42 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    obtain ⟨h0, h1⟩ := hposle k hk
    rw [abs_of_nonneg (mul_nonneg (by linarith) h0)]
    have := mul_le_mul (show a ≤ 41 by linarith) h1 h0 (by norm_num)
    linarith
  have hsF : ∀ k : ℕ, k ≤ w.length → (1 ≤ k ∧ tokAt w (k - 1) = c + 1) →
      hscore (hd2 c) fl (p.A 1 c) (X1 fl ex p w) i k = fl (a * fl (k : ℝ)) := by
    intro k hk hf
    rw [hsk k hk, (Gfact H c hc k hk).1 hf.1 hf.2]
    simp only [mul_zero, hr.zero, add_zero]
    exact hr.idem _ (le_trans (hAb k hk) (by linarith))
  have hsU : ∀ k : ℕ, 1 ≤ k → k ≤ w.length → tokAt w (k - 1) ≠ c + 1 →
      hscore (hd2 c) fl (p.A 1 c) (X1 fl ex p w) i k
        ≤ 4021 / 100 * (k : ℝ) - 18315 / 100 * ((w.length + 1 : ℕ) : ℝ) + 6 := by
    intro k h1 hk hne
    obtain ⟨hG1, hG2⟩ := (Gfact H c hc k hk).2.1 h1 hne
    have e := abs_le.mp (hs2 k hk).1
    have hnear := abs_le.mp (hposn k hk)
    have hnq2 := abs_le.mp hnq
    have hA1 : a * fl (k : ℝ) ≤ 4021 / 100 * fl (k : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (hposle k hk).1
    have hbg : b * Gc fl ex p w c k ≤ -99 / 100 * Gc fl ex p w c k :=
      mul_le_mul_of_nonneg_right hb2 (by linarith)
    have hbg' : b * Gc fl ex p w c k ≤ -18315 / 100 := by linarith
    have hnqG : fl (((w.length + 1 : ℕ) : ℝ)) * (b * Gc fl ex p w c k)
        ≤ fl (((w.length + 1 : ℕ) : ℝ)) * (-18315 / 100) :=
      mul_le_mul_of_nonneg_left hbg' (by linarith)
    linarith [e.1, e.2, hnear.1, hnear.2, hnq2.1, hnq2.2]
  have hs0 : hscore (hd2 c) fl (p.A 1 c) (X1 fl ex p w) i 0
        ≤ -3465 / 100 * ((w.length + 1 : ℕ) : ℝ) + 5 ∧
      -6565 / 100 * ((w.length + 1 : ℕ) : ℝ) - 5
        ≤ hscore (hd2 c) fl (p.A 1 c) (X1 fl ex p w) i 0 := by
    obtain ⟨hG1, hG2⟩ := (Gfact H c hc 0 (Nat.zero_le _)).2.2 rfl
    have e := abs_le.mp (hs2 0 (Nat.zero_le _)).1
    have hf0 : fl ((0 : ℕ) : ℝ) = 0 := by simp [hr.zero]
    rw [hf0, mul_zero, zero_add] at e
    have hnq2 := abs_le.mp hnq
    have hbgu : b * Gc fl ex p w c 0 ≤ -99 / 100 * Gc fl ex p w c 0 :=
      mul_le_mul_of_nonneg_right hb2 (by linarith)
    have hbgl : -101 / 100 * Gc fl ex p w c 0 ≤ b * Gc fl ex p w c 0 :=
      mul_le_mul_of_nonneg_right hb1 (by linarith)
    have hu' : b * Gc fl ex p w c 0 ≤ -3465 / 100 := by linarith
    have hl' : -6565 / 100 ≤ b * Gc fl ex p w c 0 := by linarith
    have h1 : fl (((w.length + 1 : ℕ) : ℝ)) * (b * Gc fl ex p w c 0)
        ≤ fl (((w.length + 1 : ℕ) : ℝ)) * (-3465 / 100) :=
      mul_le_mul_of_nonneg_left hu' (by linarith)
    have h2 : fl (((w.length + 1 : ℕ) : ℝ)) * (-6565 / 100)
        ≤ fl (((w.length + 1 : ℕ) : ℝ)) * (b * Gc fl ex p w c 0) :=
      mul_le_mul_of_nonneg_left hl' (by linarith)
    constructor <;> linarith [e.1, e.2, hnq2.1, hnq2.2]
  have hWle : W ≤ i := by
    rcases hW with ⟨_, h, _, _⟩ | ⟨h, _⟩ <;> omega
  have hgap : ∀ k ∈ cand Mask.causal (w.length + 1) i, k ≠ W →
      hscore (hd2 c) fl (p.A 1 c) (X1 fl ex p w) i k
        ≤ hscore (hd2 c) fl (p.A 1 c) (X1 fl ex p w) i W - 16 * (ndist W k : ℝ) := by
    intro k hk hne
    rw [Lane4.Seq.mem_cand_causal] at hk
    have hkl : k ≤ w.length := by omega
    have hdk : |(W : ℝ) - (k : ℝ)| ≤ ((w.length + 1 : ℕ) : ℝ) - 1 := by
      rw [abs_le]
      constructor <;> linarith [hkR k hkl, hkR W (by omega), (Nat.cast_nonneg k : (0 : ℝ) ≤ k),
        (Nat.cast_nonneg W : (0 : ℝ) ≤ W)]
    rw [ndist_cast]
    rcases hW with ⟨hW1, hWi, hWt, hWl⟩ | ⟨hW0, hWn⟩
    · have hWf : 1 ≤ W ∧ tokAt w (W - 1) = c + 1 := ⟨hW1, hWt⟩
      have hSW := hsF W (by omega) hWf
      have hSWlow : -(17 / 100) ≤ hscore (hd2 c) fl (p.A 1 c) (X1 fl ex p w) i W := by
        rw [hSW]
        have := abs_le.mp (hr.abs hu0 (hAb W (by omega)) (by linarith))
        have h0 : 0 ≤ a * fl (W : ℝ) := mul_nonneg (by linarith) (hposle W (by omega)).1
        have hun : u * (42 * ((w.length + 1 : ℕ) : ℝ)) = 42 * (u * ((w.length + 1 : ℕ) : ℝ)) := by
          ring
        linarith [this.1, hn, hηs, hηs', hun]
      by_cases hkf : 1 ≤ k ∧ tokAt w (k - 1) = c + 1
      · have hkW : k < W := by
          by_contra hcon
          have : W < k := by omega
          exact hWl k this hk hkf.2
        rw [hsF k hkl hkf, hSW]
        have hg := hr.pos_gap hu0 hη (le_of_lt hkW) (show W ≤ w.length + 1 by omega) hn hnM
        have hgp := hr.gap hu0 (hAb k hkl) (hAb W (by omega)) (by linarith)
        have hd1' : (k : ℝ) + 1 ≤ (W : ℝ) := by exact_mod_cast hkW
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (W : ℝ) - (k : ℝ))]
        have hD0 : 0 ≤ fl (W : ℝ) - fl (k : ℝ) := by linarith
        have hSD := mul_le_mul_of_nonneg_right (show (39 : ℝ) ≤ a by linarith) hD0
        have hun : u * (42 * ((w.length + 1 : ℕ) : ℝ)) = 42 * (u * ((w.length + 1 : ℕ) : ℝ)) := by
          ring
        linarith [hgp, hSD, hg, hd1', hn, hηs, hηs', hun]
      · by_cases hk0 : k = 0
        · subst hk0
          linarith [hs0.1, hSWlow, hdk, hN2]
        · have hk1 : 1 ≤ k := by omega
          have hne' : tokAt w (k - 1) ≠ c + 1 := fun h => hkf ⟨hk1, h⟩
          linarith [hsU k hk1 hkl hne', hSWlow, hdk, hkR k hkl, hN2]
    · subst hW0
      have hk1 : 1 ≤ k := by omega
      have hne' := hWn k hk1 hk
      linarith [hsU k hk1 hkl hne', hs0.2, hdk, hkR k hkl, hN2]
  have hlen : (cand Mask.causal (w.length + 1) i).length ≤ w.length + 1 := by
    simp [cand]; omega
  have hjW : W ∈ cand Mask.causal (w.length + 1) i := Lane4.Seq.mem_cand_causal.mpr hWle
  have hSb : ∀ k ∈ cand Mask.causal (w.length + 1) i,
      |hscore (hd2 c) fl (p.A 1 c) (X1 fl ex p w) i k| ≤ 302 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    rw [Lane4.Seq.mem_cand_causal] at hk
    exact (hs2 k (by omega)).2
  have hfB : ∀ k ∈ cand Mask.causal (w.length + 1) i,
      |(fun j => rdot fl (sp 1 14 2) (X1 fl ex p w j) (p.V 1 c (9 + c)) 0 0) k| ≤ 3 := by
    intro k hk
    rw [Lane4.Seq.mem_cand_causal] at hk
    show |rdot fl (sp 1 14 2) (X1 fl ex p w k) (p.V 1 c (9 + c)) 0 0| ≤ 3
    rw [val2_eq H c hc k (by omega)]
    have hee := ee_facts hr hu0 hu1 hη (by linarith : (40 : ℝ) ≤ M) p H.hp (tokAt w k) 1
    have hEb : |ee fl p (tokAt w k) 1| ≤ 11 / 10 := by
      by_cases h : tokAt w k = 1 + 1
      · have := abs_le.mp ((hee.1 h))
        rw [abs_le]; constructor <;> linarith [this.1, this.2]
      · rw [hee.2 h]; norm_num
    have hvb := abs_le.mp hv
    have hs : |sw fl 2 (p.V 1 c (9 + c) 1)| ≤ 21 / 10 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have hm : |sw fl 2 (p.V 1 c (9 + c) 1) * ee fl p (tokAt w k) 1| ≤ 231 / 100 := by
      rw [abs_mul]
      have := mul_le_mul hs hEb (abs_nonneg _) (by norm_num)
      linarith
    have := hr.bound hu0 hm (by linarith)
    linarith [hu1]
  unfold Ao
  have hsn := soft_near hr H.he hu0 hu1 H.hη0 hη (Lane4.Seq.cand_nodup _ _ _) hlen hn hnη hjW
    hgap hSb (by linarith) hfB (by linarith)
  refine ⟨hsn.2, ?_⟩
  have h1 := hsn.1
  rw [val2_eq H c hc W (by omega)] at h1
  have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 100000 := by norm_num
  have h3 : (3 : ℝ) / 100 = 3 / 100 := rfl
  exact h1

theorem find_rev (q : ℕ → Bool) : ∀ m : ℕ,
    (∀ j, (List.range m).reverse.find? q = some j →
      j < m ∧ q j = true ∧ ∀ x, j < x → x < m → q x = false) ∧
    ((List.range m).reverse.find? q = none → ∀ x, x < m → q x = false) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hr : (List.range (m + 1)).reverse = m :: (List.range m).reverse := by
      simp [List.range_succ]
    rw [hr]
    by_cases hqm : q m = true
    · refine ⟨?_, ?_⟩
      · intro j hj
        simp [List.find?, hqm] at hj
        subst hj
        exact ⟨by omega, hqm, fun x h1 h2 => by omega⟩
      · intro hn
        simp [List.find?, hqm] at hn
    · have hqf : q m = false := by simpa using hqm
      refine ⟨?_, ?_⟩
      · intro j hj
        simp [List.find?, hqf] at hj
        obtain ⟨h1, h2, h3⟩ := ih.1 j hj
        refine ⟨by omega, h2, fun x hx1 hx2 => ?_⟩
        by_cases hxm : x = m
        · subst hxm; exact hqf
        · exact h3 x hx1 (by omega)
      · intro hn x hx
        simp [List.find?, hqf] at hn
        by_cases hxm : x = m
        · subst hxm; exact hqf
        · exact hn x (by omega)

theorem exW (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (i : ℕ) (hi1 : 1 ≤ i)
    (hi : i ≤ w.length) :
    ∃ W, Wp w (tokAt w i) i W ∧ target w i = h (tokAt w W) := by
  have hτ : 1 ≤ tokAt w i := tok_pos w hw i hi1 hi
  have hfind := find_rev (fun j => decide (1 ≤ j) && (tokAt w j == tokAt w i)) i
  unfold target prevOcc
  cases hq : (List.range i).reverse.find?
      (fun j => decide (1 ≤ j) && (tokAt w j == tokAt w i)) with
  | some j =>
    obtain ⟨hj1, hj2, hj3⟩ := hfind.1 j hq
    simp at hj2
    refine ⟨j + 1, Or.inl ⟨by omega, by omega, ?_, ?_⟩, ?_⟩
    · simpa using hj2.2
    · intro m hm1 hm2 heq
      have h1' : 1 ≤ m - 1 := by omega
      have := hj3 (m - 1) (by omega) (by omega)
      simp [h1', heq] at this
    · rfl
  | none =>
    have hall := hfind.2 hq
    refine ⟨0, Or.inr ⟨rfl, ?_⟩, ?_⟩
    · intro m hm1 hm2 heq
      by_cases hm : m = 1
      · subst hm
        simp [Lane4.Seq.tokAt_zero] at heq
        omega
      · have h1' : 1 ≤ m - 1 := by omega
        have := hall (m - 1) (by omega)
        simp [h1', heq] at this
    · simp [h, Lane4.Seq.tokAt_zero]

theorem exWp (w : List ℕ) (τ : ℕ) (hτ : 1 ≤ τ) : ∀ i : ℕ, ∃ W, Wp w τ i W := by
  intro i
  induction i with
  | zero => exact ⟨0, Or.inr ⟨rfl, fun m h1 h2 => by omega⟩⟩
  | succ i ih =>
    by_cases hq : tokAt w i = τ
    · exact ⟨i + 1, Or.inl ⟨by omega, le_refl _, by simpa using hq, fun m h1 h2 => by omega⟩⟩
    · obtain ⟨W, hW⟩ := ih
      refine ⟨W, ?_⟩
      rcases hW with ⟨h1, h2, h3, h4⟩ | ⟨h0, hn⟩
      · refine Or.inl ⟨h1, by omega, h3, fun m hm hm2 => ?_⟩
        by_cases hmi : m = i + 1
        · subst hmi; simpa using hq
        · exact h4 m hm (by omega)
      · refine Or.inr ⟨h0, fun m hm hm2 => ?_⟩
        by_cases hmi : m = i + 1
        · subst hmi; simpa using hq
        · exact hn m hm (by omega)

theorem eg_bd {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (τ c : ℕ) : |eg fl p τ c| ≤ 151 := by
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by linarith [H.hu0, H.hu1]
  unfold eg
  split_ifs with h
  · have c150 : (((-150 : ℚ)) : ℝ) = -150 := by norm_num
    have a150 : |(-150 : ℝ)| = 150 := by norm_num
    have hM300 : (300 : ℝ) ≤ M := range_const H.hM (by omega : 1 ≤ w.length + 1) (by norm_num)
    have hE := sw_near H.hr H.hu0 (-150) (H.hp.E 0 (6 + c)) (by norm_num)
      (by rw [c150]; norm_num; linarith) hε
    rw [c150, a150] at hE
    have hηs := eta_tiny H.hη
    have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
    obtain ⟨h1, h2⟩ := abs_le.mp hE
    rw [abs_le]; constructor <;> linarith
  · simp

theorem X_bd {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (c : ℕ) (hc : c < 3) (k : ℕ) (hk : k ≤ w.length) :
    |sw fl 1 (p.W2 0 (6 + c) c) * relu (Ha fl ex p w c k)| ≤ 800 := by
  have hb := (Ha_bd H c hc k hk).2
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by linarith [H.hu0, H.hu1]
  have hM1000 : (1000 : ℝ) ≤ M := range_const H.hM (by omega : 1 ≤ w.length + 1) (by norm_num)
  have c1 : ((1 : ℚ) : ℝ) = 1 := by norm_num
  have hw2 := sw_near H.hr H.hu0 1 (H.hp.W2 0 (6 + c) c) (by norm_num)
    (by rw [c1]; norm_num; linarith) hε
  rw [c1, abs_one] at hw2
  have hηs := eta_tiny H.hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hw3 := abs_le.mp hw2
  have h0 : 0 ≤ relu (Ha fl ex p w c k) := le_max_right _ _
  have h1 : relu (Ha fl ex p w c k) ≤ 708 := max_le (le_trans (le_abs_self _) hb) (by norm_num)
  have hsw : |sw fl 1 (p.W2 0 (6 + c) c)| ≤ 11 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [abs_mul, abs_of_nonneg h0]
  have := mul_le_mul hsw h1 h0 (by norm_num)
  linarith

theorem Gc_idem {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (c : ℕ) (hc : c < 3) (k : ℕ) (hk : k ≤ w.length) :
    fl (Gc fl ex p w c k) = Gc fl ex p w c k := by
  have hX := X_bd H c hc k hk
  have hEg := abs_le.mp (eg_bd H (tokAt w k) c)
  have hM1000 : (1000 : ℝ) ≤ M := range_const H.hM (by omega : 1 ≤ w.length + 1) (by norm_num)
  have hηs := eta_tiny H.hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hfX := abs_le.mp (H.hr.bound H.hu0 hX (by linarith))
  have hu1 := H.hu1
  unfold Gc
  apply H.hr.idem
  rw [abs_le]
  constructor <;> linarith [hfX.1, hfX.2, hEg.1, hEg.2]

theorem f_bd {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (c : ℕ) (hc : c < 3) (τ : ℕ) :
    |fl (sw fl 2 (p.V 1 c (9 + c) 1) * ee fl p τ 1)| ≤ 233 / 100 := by
  have hee := ee_facts H.hr H.hu0 H.hu1 H.hη
    (range_const H.hM (by omega : 1 ≤ w.length + 1) (by norm_num)) p H.hp τ 1
  have hM1000 : (1000 : ℝ) ≤ M := range_const H.hM (by omega : 1 ≤ w.length + 1) (by norm_num)
  have hEb : |ee fl p τ 1| ≤ 11 / 10 := by
    by_cases h : τ = 1 + 1
    · have := abs_le.mp ((hee.1 h))
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    · rw [hee.2 h]; norm_num
  obtain ⟨_, _, hv⟩ := w2_facts H c hc
  have hvb := abs_le.mp hv
  have hs : |sw fl 2 (p.V 1 c (9 + c) 1)| ≤ 21 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hm : |sw fl 2 (p.V 1 c (9 + c) 1) * ee fl p τ 1| ≤ 231 / 100 := by
    rw [abs_mul]
    have := mul_le_mul hs hEb (abs_nonneg _) (by norm_num)
    linarith
  have := H.hr.bound H.hu0 hm (by linarith)
  have hηs := eta_tiny H.hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  linarith [H.hu1]

theorem f_val {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (c : ℕ) (hc : c < 3) (τ : ℕ) :
    (τ = 2 → |fl (sw fl 2 (p.V 1 c (9 + c) 1) * ee fl p τ 1) - 2| ≤ 22 / 1000) ∧
    (τ ≠ 2 → fl (sw fl 2 (p.V 1 c (9 + c) 1) * ee fl p τ 1) = 0) := by
  have hee := ee_facts H.hr H.hu0 H.hu1 H.hη
    (range_const H.hM (by omega : 1 ≤ w.length + 1) (by norm_num)) p H.hp τ 1
  have hM1000 : (1000 : ℝ) ≤ M := range_const H.hM (by omega : 1 ≤ w.length + 1) (by norm_num)
  obtain ⟨_, _, hv⟩ := w2_facts H c hc
  have hηs := eta_tiny H.hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  constructor
  · intro h2
    have h2' : τ = 1 + 1 := h2
    have hE := hee.1 h2'
    have hEb := abs_le.mp hE
    have e1' : |sw fl 2 (p.V 1 c (9 + c) 1) * ee fl p τ 1 - 2| ≤ 217 / 10000 := by
      have hq : sw fl 2 (p.V 1 c (9 + c) 1) * ee fl p τ 1 - 2
          = (sw fl 2 (p.V 1 c (9 + c) 1) - 2) * ee fl p τ 1 + 2 * (ee fl p τ 1 - 1) := by ring
      rw [hq]
      have h3 := abs_add_le ((sw fl 2 (p.V 1 c (9 + c) 1) - 2) * ee fl p τ 1)
        (2 * (ee fl p τ 1 - 1))
      have h4 : |(sw fl 2 (p.V 1 c (9 + c) 1) - 2) * ee fl p τ 1| ≤ 101 / 10000 * (11 / 10) := by
        rw [abs_mul]
        exact mul_le_mul hv (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_nonneg _) (by norm_num)
      have h5 : |2 * (ee fl p τ 1 - 1)| ≤ 2 * (1 / 190) := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith
      linarith
    have hm : |sw fl 2 (p.V 1 c (9 + c) 1) * ee fl p τ 1| ≤ 3 := by
      have := abs_le.mp e1'
      rw [abs_le]
      constructor <;> linarith [this.1, this.2]
    have := H.hr.near H.hu0 e1' hm (by linarith)
    linarith [H.hu1]
  · intro h2
    have h2' : τ ≠ 1 + 1 := h2
    rw [hee.2 h2', mul_zero, H.hr.zero]

theorem attn2_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (c i : ℕ) :
    sattn (hd2 c) fl ex (p.A 1 c) (p.V 1 c) (w.length + 1) (X1 fl ex p w) i
      = List.replicate (9 + c) 0 ++ Ao fl ex p w c i :: List.replicate (6 - c) 0 := by
  unfold sattn
  show sattnRows fl ex (List.replicate (9 + c) zr ++ sp 1 14 2 :: List.replicate (6 - c) zr)
    (p.V 1 c) (cand Mask.causal (w.length + 1) i)
    (hscore (hd2 c) fl (p.A 1 c) (X1 fl ex p w) i) (X1 fl ex p w) 0 = _
  rw [sattnRows_one hr]
  simp only [zero_add]
  rfl

theorem attn2_0 {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ) (i : ℕ) :
    sattn (hd2 0) fl ex (p.A 1 0) (p.V 1 0) (w.length + 1) (X1 fl ex p w) i
      = [0, 0, 0, 0, 0, 0, 0, 0, 0, Ao fl ex p w 0 i, 0, 0, 0, 0, 0, 0] := by
  rw [attn2_eq hr]; rfl

theorem attn2_1 {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ) (i : ℕ) :
    sattn (hd2 1) fl ex (p.A 1 1) (p.V 1 1) (w.length + 1) (X1 fl ex p w) i
      = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, Ao fl ex p w 1 i, 0, 0, 0, 0, 0] := by
  rw [attn2_eq hr]; rfl

theorem attn2_2 {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ) (i : ℕ) :
    sattn (hd2 2) fl ex (p.A 1 2) (p.V 1 2) (w.length + 1) (X1 fl ex p w) i
      = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, Ao fl ex p w 2 i, 0, 0, 0, 0] := by
  rw [attn2_eq hr]; rfl

noncomputable def Zl (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (i : ℕ) : List ℝ :=
  [ee fl p (tokAt w i) 0, ee fl p (tokAt w i) 1, ee fl p (tokAt w i) 2,
   Pc fl ex p w 0 i, Pc fl ex p w 1 i, Pc fl ex p w 2 i,
   Gc fl ex p w 0 i, Gc fl ex p w 1 i, Gc fl ex p w 2 i,
   Ao fl ex p w 0 i, Ao fl ex p w 1 i, Ao fl ex p w 2 i, 0, 1,
   fl (i : ℝ), fl ((w.length + 1 : ℕ) : ℝ)]

theorem Z_eq {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (i : ℕ) (hi : i ≤ w.length)
    (hA : ∀ c, c < 3 → fl (Ao fl ex p w c i) = Ao fl ex p w c i) :
    sheadsApply fl ex blk2.heads (p.A 1) (p.V 1) (w.length + 1) (X1 fl ex p w) i
        (X1 fl ex p w i) 0 = Zl fl ex p w i := by
  have hP0 := Pfl H 0 (by norm_num) i hi
  have hP1 := Pfl H 1 (by norm_num) i hi
  have hP2 := Pfl H 2 (by norm_num) i hi
  have hG0 := Gc_idem H 0 (by norm_num) i hi
  have hG1 := Gc_idem H 1 (by norm_num) i hi
  have hG2 := Gc_idem H 2 (by norm_num) i hi
  have hA0 := hA 0 (by norm_num)
  have hA1 := hA 1 (by norm_num)
  have hA2 := hA 2 (by norm_num)
  have hr := H.hr
  have hn1 : 1 ≤ w.length + 1 := by omega
  have h300 : (300 : ℝ) ≤ M := range_const H.hM hn1 (by norm_num)
  have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
    have := range_lin H.hM hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have hk1 : fl (fl (i : ℝ)) = fl (i : ℝ) := by
    apply hr.idem
    rw [abs_of_nonneg (Nat.cast_nonneg i)]
    have : (i : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : i ≤ w.length + 1)
    linarith
  have hn1' : fl (fl (((w.length + 1 : ℕ) : ℝ))) = fl (((w.length + 1 : ℕ) : ℝ)) := by
    apply hr.idem
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact hnM
  simp only [Zl, blk2, sheadsApply, Nat.reduceAdd, zero_add]
  rw [attn2_0 hr p w i, attn2_1 hr p w i, attn2_2 hr p w i, X1_eq H i hi]
  simp only [x1l, radd, add_zero, zero_add, fl_ee hr (by linarith : (40 : ℝ) ≤ M) p H.hp,
    fl_eg hr h300 p H.hp, hP0, hP1, hP2, hG0, hG1, hG2, hA0, hA1, hA2, hr.zero, hr.one, hk1, hn1']

noncomputable def Pre (fl : ℝ → ℝ) (s3 s1 sb e a : ℝ) : ℝ :=
  fl (fl (fl (s3 * e) + fl (s1 * a)) + sb)

noncomputable def Pc2 (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (c i : ℕ) : ℝ :=
  Pre fl (sw fl 3 (p.W1 1 c c)) (sw fl 1 (p.W1 1 c (9 + c))) (sw fl (-3) (p.b1 1 c))
    (ee fl p (tokAt w i) c) (Ao fl ex p w c i)

theorem gate_wts {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (c : ℕ) :
    |sw fl 3 (p.W1 1 c c) - 3| ≤ 16 / 1000 ∧ |sw fl 1 (p.W1 1 c (9 + c)) - 1| ≤ 6 / 1000 ∧
    |sw fl (-3) (p.b1 1 c) + 3| ≤ 16 / 1000 ∧ |sw fl 1 (p.W2 1 12 c) - 1| ≤ 6 / 1000 ∧
    |sw fl 1 (p.oW 12) - 1| ≤ 6 / 1000 := by
  have hr := H.hr
  have hu0 := H.hu0
  have hu1 := H.hu1
  have h1000 : (1000 : ℝ) ≤ M := range_const H.hM (by omega : 1 ≤ w.length + 1) (by norm_num)
  have hηs := eta_tiny H.hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by linarith
  have c3 : ((3 : ℚ) : ℝ) = 3 := by norm_num
  have c1 : ((1 : ℚ) : ℝ) = 1 := by norm_num
  have cm3 : (((-3 : ℚ)) : ℝ) = -3 := by norm_num
  have h3 := sw_near hr hu0 3 (H.hp.W1 1 c c) (by norm_num) (by rw [c3]; norm_num; linarith) hε
  rw [c3, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at h3
  have h1 := sw_near hr hu0 1 (H.hp.W1 1 c (9 + c)) (by norm_num)
    (by rw [c1]; norm_num; linarith) hε
  rw [c1, abs_one] at h1
  have hb := sw_near hr hu0 (-3) (H.hp.b1 1 c) (by norm_num) (by rw [cm3]; norm_num; linarith) hε
  rw [cm3, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at hb
  have h2 := sw_near hr hu0 1 (H.hp.W2 1 12 c) (by norm_num) (by rw [c1]; norm_num; linarith) hε
  rw [c1, abs_one] at h2
  have ho := sw_near hr hu0 1 (H.hp.oW 12) (by norm_num) (by rw [c1]; norm_num; linarith) hε
  rw [c1, abs_one] at ho
  have a1 := abs_le.mp h3
  have a2 := abs_le.mp h1
  have a3 := abs_le.mp hb
  have a4 := abs_le.mp h2
  have a5 := abs_le.mp ho
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2, a5.1, a5.2]

theorem gate_idem {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (c : ℕ) (hc : c < 3) (i : ℕ) (hAo : |Ao fl ex p w c i| ≤ 5 / 2) :
    fl (fl (sw fl 3 (p.W1 1 c c) * ee fl p (tokAt w i) c))
      = fl (sw fl 3 (p.W1 1 c c) * ee fl p (tokAt w i) c) ∧
    fl (fl (fl (sw fl 3 (p.W1 1 c c) * ee fl p (tokAt w i) c)
        + fl (sw fl 1 (p.W1 1 c (9 + c)) * Ao fl ex p w c i)))
      = fl (fl (sw fl 3 (p.W1 1 c c) * ee fl p (tokAt w i) c)
        + fl (sw fl 1 (p.W1 1 c (9 + c)) * Ao fl ex p w c i)) := by
  obtain ⟨h3, h1, hb, h2, ho⟩ := gate_wts H c
  have hr := H.hr
  have hu0 := H.hu0
  have h1000 : (1000 : ℝ) ≤ M := range_const H.hM (by omega : 1 ≤ w.length + 1) (by norm_num)
  have hηs := eta_tiny H.hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hee := ee_facts hr hu0 H.hu1 H.hη (by linarith : (40 : ℝ) ≤ M) p H.hp (tokAt w i) c
  have hEb : |ee fl p (tokAt w i) c| ≤ 11 / 10 := by
    by_cases h : tokAt w i = c + 1
    · have := abs_le.mp ((hee.1 h))
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    · rw [hee.2 h]; norm_num
  have hs3 : |sw fl 3 (p.W1 1 c c)| ≤ 31 / 10 :=
    abs_le.mpr ⟨by linarith [(abs_le.mp h3).1], by linarith [(abs_le.mp h3).2]⟩
  have hs1 : |sw fl 1 (p.W1 1 c (9 + c))| ≤ 11 / 10 :=
    abs_le.mpr ⟨by linarith [(abs_le.mp h1).1], by linarith [(abs_le.mp h1).2]⟩
  have hX : |sw fl 3 (p.W1 1 c c) * ee fl p (tokAt w i) c| ≤ 4 := by
    rw [abs_mul]
    have := mul_le_mul hs3 hEb (abs_nonneg _) (by norm_num)
    linarith
  have hY : |sw fl 1 (p.W1 1 c (9 + c)) * Ao fl ex p w c i| ≤ 3 := by
    rw [abs_mul]
    have := mul_le_mul hs1 hAo (abs_nonneg _) (by norm_num)
    linarith
  have fX := abs_le.mp (hr.bound hu0 hX (by linarith))
  have fY := abs_le.mp (hr.bound hu0 hY (by linarith))
  have hsum : |fl (sw fl 3 (p.W1 1 c c) * ee fl p (tokAt w i) c)
      + fl (sw fl 1 (p.W1 1 c (9 + c)) * Ao fl ex p w c i)| ≤ 8 := by
    rw [abs_le]; constructor <;> linarith [fX.1, fX.2, fY.1, fY.2, H.hu1]
  exact ⟨hr.idem _ (by linarith), hr.idem _ (by linarith)⟩

theorem gate0 {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (i : ℕ) (hAo : |Ao fl ex p w 0 i| ≤ 5 / 2) :
    fl (rdot fl gt0 (Zl fl ex p w i) (p.W1 1 0) 0 0 + sw fl (-3) (p.b1 1 0))
      = Pc2 fl ex p w 0 i := by
  obtain ⟨hI1, hI2⟩ := gate_idem H 0 (by norm_num) i hAo
  simp only [Nat.reduceAdd] at hI2
  have hr := H.hr
  simp only [Pc2, Pre, Zl, gt0, rdot, Nat.reduceAdd, zero_add, sw_zero hr, zero_mul, hr.zero,
    add_zero, hI1, hI2]

theorem gate1 {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (i : ℕ) (hAo : |Ao fl ex p w 1 i| ≤ 5 / 2) :
    fl (rdot fl gt1 (Zl fl ex p w i) (p.W1 1 1) 0 0 + sw fl (-3) (p.b1 1 1))
      = Pc2 fl ex p w 1 i := by
  obtain ⟨hI1, hI2⟩ := gate_idem H 1 (by norm_num) i hAo
  simp only [Nat.reduceAdd] at hI2
  have hr := H.hr
  simp only [Pc2, Pre, Zl, gt1, rdot, Nat.reduceAdd, zero_add, sw_zero hr, zero_mul, hr.zero,
    add_zero, hI1, hI2]

theorem gate2 {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (i : ℕ) (hAo : |Ao fl ex p w 2 i| ≤ 5 / 2) :
    fl (rdot fl gt2 (Zl fl ex p w i) (p.W1 1 2) 0 0 + sw fl (-3) (p.b1 1 2))
      = Pc2 fl ex p w 2 i := by
  obtain ⟨hI1, hI2⟩ := gate_idem H 2 (by norm_num) i hAo
  simp only [Nat.reduceAdd] at hI2
  have hr := H.hr
  simp only [Pc2, Pre, Zl, gt2, rdot, Nat.reduceAdd, zero_add, sw_zero hr, zero_mul, hr.zero,
    add_zero, hI1, hI2]

theorem relu_near (x T : ℝ) (hT : T = 0 ∨ T = 2) (h : |x - T| ≤ 13 / 100) :
    |relu x - T| ≤ 13 / 100 := by
  have h' := abs_le.mp h
  rcases hT with rfl | rfl
  · rcases le_total 0 x with hx | hx
    · rw [relu_of_nonneg hx]; exact h
    · rw [relu_of_nonpos hx]; norm_num
  · rw [relu_of_nonneg (by linarith [h'.1])]; exact h

theorem gate_off {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) (h1000 : (1000 : ℝ) ≤ M)
    (s3 s1 sb e a : ℝ) (hs1 : |s1 - 1| ≤ 6 / 1000) (hsb : |sb + 3| ≤ 16 / 1000) (he : e = 0)
    (ha : |a| ≤ 5 / 2) : Pre fl s3 s1 sb e a ≤ 0 := by
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  unfold Pre
  subst he
  rw [mul_zero, hr.zero]
  have hs1' := abs_le.mp hs1
  have hsb' := abs_le.mp hsb
  have hY : |s1 * a| ≤ 3 := by
    rw [abs_mul]
    have := mul_le_mul (abs_le.mpr ⟨by linarith, by linarith⟩ : |s1| ≤ 11 / 10) ha
      (abs_nonneg _) (by norm_num)
    linarith
  have hy := abs_le.mp (hr.bound hu0 hY (by linarith))
  have hs1a : s1 * a ≤ 2519 / 1000 := by
    have h0 : |s1 * a| ≤ 1006 / 1000 * (5 / 2) := by
      rw [abs_mul]
      exact mul_le_mul (abs_le.mpr ⟨by linarith, by linarith⟩) ha (abs_nonneg _) (by norm_num)
    have := (abs_le.mp h0).2
    linarith
  have hup := hr.upper hu0 hY (by linarith)
  have hz : |0 + fl (s1 * a)| ≤ 4 := by
    rw [zero_add, abs_le]; constructor <;> linarith [hy.1, hy.2, hu1]
  have hz2 := hr.upper hu0 hz (by linarith)
  have hb := abs_le.mp (hr.bound hu0 hz (by linarith))
  have hneg : fl (0 + fl (s1 * a)) + sb ≤ 0 := by
    linarith [hz2, hup, hs1a, hsb'.1, hsb'.2, hu1, hηs, hηs']
  exact hr.nonpos hneg (by linarith [hb.1, hu1, hηs, hηs', hsb'.1])

theorem gate_on {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) (h1000 : (1000 : ℝ) ≤ M)
    (s3 s1 sb e a T : ℝ) (hs3 : |s3 - 3| ≤ 16 / 1000) (hs1 : |s1 - 1| ≤ 6 / 1000)
    (hsb : |sb + 3| ≤ 16 / 1000) (he : |e - 1| ≤ 1 / 190) (ha : |a - T| ≤ 6 / 100)
    (hT : T = 0 ∨ T = 2) : |relu (Pre fl s3 s1 sb e a) - T| ≤ 13 / 100 := by
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hT2 : |T| ≤ 2 := by rcases hT with rfl | rfl <;> norm_num
  have hs3' := abs_le.mp hs3
  have hs1' := abs_le.mp hs1
  have hsb' := abs_le.mp hsb
  have he' := abs_le.mp he
  have ha' := abs_le.mp ha
  have hT2' := abs_le.mp hT2
  refine relu_near _ T hT ?_
  unfold Pre
  have hEb : |e| ≤ 11 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hX1 : |s3 * e - 3| ≤ 34 / 1000 := by
    have hq : s3 * e - 3 = (s3 - 3) * e + 3 * (e - 1) := by ring
    rw [hq]
    have h3 := abs_add_le ((s3 - 3) * e) (3 * (e - 1))
    have h4 : |(s3 - 3) * e| ≤ 16 / 1000 * (11 / 10) := by
      rw [abs_mul]
      exact mul_le_mul hs3 hEb (abs_nonneg _) (by norm_num)
    have h5 : |3 * (e - 1)| ≤ 3 * (1 / 190) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      linarith
    linarith
  have hXb : |s3 * e| ≤ 4 := by
    rw [abs_mul]
    have := mul_le_mul (abs_le.mpr ⟨by linarith, by linarith⟩ : |s3| ≤ 31 / 10) hEb
      (abs_nonneg _) (by norm_num)
    linarith
  have hFX := abs_le.mp (hr.near hu0 hX1 hXb (by linarith))
  have haB : |a| ≤ 21 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hY1 : |s1 * a - T| ≤ 73 / 1000 := by
    have hq : s1 * a - T = (s1 - 1) * a + (a - T) := by ring
    rw [hq]
    have h3 := abs_add_le ((s1 - 1) * a) (a - T)
    have h4 : |(s1 - 1) * a| ≤ 6 / 1000 * (21 / 10) := by
      rw [abs_mul]
      exact mul_le_mul hs1 haB (abs_nonneg _) (by norm_num)
    linarith
  have hYb : |s1 * a| ≤ 3 := by
    rw [abs_mul]
    have := mul_le_mul (abs_le.mpr ⟨by linarith, by linarith⟩ : |s1| ≤ 11 / 10) haB
      (abs_nonneg _) (by norm_num)
    linarith
  have hFY := abs_le.mp (hr.near hu0 hY1 hYb (by linarith))
  have hz1 : |fl (s3 * e) + fl (s1 * a) - (3 + T)| ≤ 108 / 1000 := by
    rw [abs_le]; constructor <;> linarith [hFX.1, hFX.2, hFY.1, hFY.2, hu1]
  have hzb : |fl (s3 * e) + fl (s1 * a)| ≤ 6 := by
    rw [abs_le]; constructor <;> linarith [hFX.1, hFX.2, hFY.1, hFY.2, hu1]
  have hFz := abs_le.mp (hr.near hu0 hz1 hzb (by linarith))
  have hw1 : |fl (fl (s3 * e) + fl (s1 * a)) + sb - T| ≤ 125 / 1000 := by
    rw [abs_le]; constructor <;> linarith [hFz.1, hFz.2, hsb'.1, hsb'.2, hu1]
  have hwb : |fl (fl (s3 * e) + fl (s1 * a)) + sb| ≤ 3 := by
    rw [abs_le]; constructor <;> linarith [hFz.1, hFz.2, hsb'.1, hsb'.2, hu1]
  have hFp := abs_le.mp (hr.near hu0 hw1 hwb (by linarith))
  rw [abs_le]; constructor <;> linarith [hFp.1, hFp.2, hu1]

theorem Ao_bd {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (c : ℕ) (hc : c < 3) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    |Ao fl ex p w c i| ≤ 5 / 2 ∧ fl (Ao fl ex p w c i) = Ao fl ex p w c i := by
  obtain ⟨W', hW'⟩ := exWp w (c + 1) (by omega) i
  obtain ⟨hfl, hcl⟩ := head2 H c hc i hi1 hi W' hW'
  have hf := abs_le.mp (f_bd H c hc (tokAt w W'))
  have hc' := abs_le.mp hcl
  have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 100000 := by norm_num
  refine ⟨?_, hfl⟩
  rw [abs_le]; constructor <;> linarith [hf.1, hf.2, hc'.1, hc'.2]

theorem fin_gen {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (d : ℕ → ℝ) (b : ℝ)
    (u0 u1 u2 : ℝ) (c0 : ℕ) (hc0 : c0 < 3)
    (hz : ∀ c, c < 3 → c ≠ c0 → [u0, u1, u2].getD c 0 = 0)
    (hM : |sw fl 1 (d c0) * [u0, u1, u2].getD c0 0| ≤ M) :
    fl (rdot fl [1, 1, 1] [u0, u1, u2] d 0 0 + sw fl 0 b)
      = fl (sw fl 1 (d c0) * [u0, u1, u2].getD c0 0) := by
  interval_cases c0
  · have h1 : u1 = 0 := by simpa using hz 1 (by norm_num) (by norm_num)
    have h2 : u2 = 0 := by simpa using hz 2 (by norm_num) (by norm_num)
    subst h1 h2
    have hM' : |sw fl 1 (d 0) * u0| ≤ M := by simpa using hM
    have hI : fl (fl (sw fl 1 (d 0) * u0)) = fl (sw fl 1 (d 0) * u0) := hr.idem _ hM'
    simp [rdot, sw_zero hr, hr.zero, hI]
  · have h1 : u0 = 0 := by simpa using hz 0 (by norm_num) (by norm_num)
    have h2 : u2 = 0 := by simpa using hz 2 (by norm_num) (by norm_num)
    subst h1 h2
    have hM' : |sw fl 1 (d 1) * u1| ≤ M := by simpa using hM
    have hI : fl (fl (sw fl 1 (d 1) * u1)) = fl (sw fl 1 (d 1) * u1) := hr.idem _ hM'
    simp [rdot, sw_zero hr, hr.zero, hI]
  · have h1 : u0 = 0 := by simpa using hz 0 (by norm_num) (by norm_num)
    have h2 : u1 = 0 := by simpa using hz 1 (by norm_num) (by norm_num)
    subst h1 h2
    have hM' : |sw fl 1 (d 2) * u2| ≤ M := by simpa using hM
    have hI : fl (fl (sw fl 1 (d 2) * u2)) = fl (sw fl 1 (d 2) * u2) := hr.idem _ hM'
    simp [rdot, sw_zero hr, hr.zero, hI]

noncomputable def Hid3 (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (i : ℕ) : List ℝ :=
  [relu (Pc2 fl ex p w 0 i), relu (Pc2 fl ex p w 1 i), relu (Pc2 fl ex p w 2 i)]

noncomputable def Fe (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (i : ℕ) : ℝ :=
  fl (rdot fl [1, 1, 1] (Hid3 fl ex p w i) (p.W2 1 12) 0 0 + sw fl 0 (p.b2 1 12))

noncomputable def x2l (fl ex : ℝ → ℝ) (p : Pert) (w : List ℕ) (i : ℕ) : List ℝ :=
  [ee fl p (tokAt w i) 0, ee fl p (tokAt w i) 1, ee fl p (tokAt w i) 2,
   Pc fl ex p w 0 i, Pc fl ex p w 1 i, Pc fl ex p w 2 i,
   Gc fl ex p w 0 i, Gc fl ex p w 1 i, Gc fl ex p w 2 i,
   Ao fl ex p w 0 i, Ao fl ex p w 1 i, Ao fl ex p w 2 i, fl (Fe fl ex p w i), 1,
   fl (i : ℝ), fl ((w.length + 1 : ℕ) : ℝ)]

theorem x2_eq {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (i : ℕ) (hi : i ≤ w.length)
    (hA : ∀ c, c < 3 → |Ao fl ex p w c i| ≤ 5 / 2 ∧ fl (Ao fl ex p w c i) = Ao fl ex p w c i) :
    sblock blk2 fl ex p 1 (w.length + 1) (X1 fl ex p w) i = x2l fl ex p w i := by
  have hZ := Z_eq H i hi (fun c hc => (hA c hc).2)
  have hg0 := gate0 H i (hA 0 (by norm_num)).1
  have hg1 := gate1 H i (hA 1 (by norm_num)).1
  have hg2 := gate2 H i (hA 2 (by norm_num)).1
  have hP0 := Pfl H 0 (by norm_num) i hi
  have hP1 := Pfl H 1 (by norm_num) i hi
  have hP2 := Pfl H 2 (by norm_num) i hi
  have hG0 := Gc_idem H 0 (by norm_num) i hi
  have hG1 := Gc_idem H 1 (by norm_num) i hi
  have hG2 := Gc_idem H 2 (by norm_num) i hi
  have hA0 := (hA 0 (by norm_num)).2
  have hA1 := (hA 1 (by norm_num)).2
  have hA2 := (hA 2 (by norm_num)).2
  have hr := H.hr
  have hn1 : 1 ≤ w.length + 1 := by omega
  have h300 : (300 : ℝ) ≤ M := range_const H.hM hn1 (by norm_num)
  have hnM : ((w.length + 1 : ℕ) : ℝ) ≤ M := by
    have := range_lin H.hM hn1 (c := 1) (by norm_num) (by norm_num)
    linarith
  have hk1 : fl (fl (i : ℝ)) = fl (i : ℝ) := by
    apply hr.idem
    rw [abs_of_nonneg (Nat.cast_nonneg i)]
    have : (i : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : i ≤ w.length + 1)
    linarith
  have hn1' : fl (fl (((w.length + 1 : ℕ) : ℝ))) = fl (((w.length + 1 : ℕ) : ℝ)) := by
    apply hr.idem
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact hnM
  simp only [sblock]
  rw [hZ]
  simp only [blk2, raffine, zb, Nat.reduceAdd, zero_add, List.map]
  rw [hg0, hg1, hg2]
  simp only [rdot_zr3 hr, sw_zero hr, add_zero, zero_add, hr.zero, Zl, radd, x2l, Fe, Hid3,
    fl_ee hr (by linarith : (40 : ℝ) ≤ M) p H.hp, fl_eg hr h300 p H.hp, hP0, hP1, hP2, hG0, hG1,
    hG2, hA0, hA1, hA2, hr.one, hk1, hn1', Nat.reduceAdd]

theorem out_bound {u η M : ℝ} {fl ex : ℝ → ℝ} {p : Pert} {w : List ℕ} (H : Ctx u η M fl ex p w)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) (c0 : ℕ) (hc0 : c0 < 3)
    (hτ : tokAt w i = c0 + 1) (W : ℕ) (hWp : Wp w (c0 + 1) i W) (T : ℝ) (hT : T = 0 ∨ T = 2)
    (hTW : (tokAt w W = 2 → T = 2) ∧ (tokAt w W ≠ 2 → T = 0)) :
    |sout net fl ex p w i - T| ≤ 1 / 4 := by
  have hr := H.hr
  have hu0 := H.hu0
  have hu1 := H.hu1
  have hη := H.hη
  have hn1 : 1 ≤ w.length + 1 := by omega
  have h1000 : (1000 : ℝ) ≤ M := range_const H.hM hn1 (by norm_num)
  have hηs := eta_tiny hη
  have hηs' : (1 : ℝ) / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have hAb : ∀ c, c < 3 → |Ao fl ex p w c i| ≤ 5 / 2 ∧ fl (Ao fl ex p w c i) = Ao fl ex p w c i :=
    fun c hc => Ao_bd H c hc i hi1 hi
  have hT2 : |T| ≤ 2 := by rcases hT with rfl | rfl <;> norm_num
  have hT2' := abs_le.mp hT2
  have hclose : |Ao fl ex p w c0 i - T| ≤ 6 / 100 := by
    obtain ⟨hfl, hcl⟩ := head2 H c0 hc0 i hi1 hi W hWp
    have hc' := abs_le.mp hcl
    have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 100000 := by norm_num
    by_cases h2 : tokAt w W = 2
    · have hv := abs_le.mp ((f_val H c0 hc0 (tokAt w W)).1 h2)
      have hT' := hTW.1 h2
      rw [hT', abs_le]
      constructor <;> linarith [hc'.1, hc'.2, hv.1, hv.2]
    · have hv := (f_val H c0 hc0 (tokAt w W)).2 h2
      have hT' := hTW.2 h2
      rw [hv] at hc'
      rw [hT', abs_le]
      constructor <;> linarith [hc'.1, hc'.2]
  have hee : ∀ c, c ≠ c0 → ee fl p (tokAt w i) c = 0 := by
    intro c hne
    exact (ee_facts hr hu0 hu1 hη (by linarith : (40 : ℝ) ≤ M) p H.hp (tokAt w i) c).2
      (by omega)
  have hee0 : |ee fl p (tokAt w i) c0 - 1| ≤ 1 / 190 :=
    (ee_facts hr hu0 hu1 hη (by linarith : (40 : ℝ) ≤ M) p H.hp (tokAt w i) c0).1 hτ
  have hu_off : ∀ c, c < 3 → c ≠ c0 → relu (Pc2 fl ex p w c i) = 0 := by
    intro c hc hne
    obtain ⟨h3, h1, hb, _, _⟩ := gate_wts H c
    exact relu_of_nonpos (gate_off hr hu0 hu1 hη h1000 (sw fl 3 (p.W1 1 c c))
      (sw fl 1 (p.W1 1 c (9 + c))) (sw fl (-3) (p.b1 1 c)) (ee fl p (tokAt w i) c)
      (Ao fl ex p w c i) h1 hb (hee c hne) (hAb c hc).1)
  have hu_on : |relu (Pc2 fl ex p w c0 i) - T| ≤ 13 / 100 := by
    obtain ⟨h3, h1, hb, _, _⟩ := gate_wts H c0
    exact gate_on hr hu0 hu1 hη h1000 (sw fl 3 (p.W1 1 c0 c0))
      (sw fl 1 (p.W1 1 c0 (9 + c0))) (sw fl (-3) (p.b1 1 c0)) (ee fl p (tokAt w i) c0)
      (Ao fl ex p w c0 i) T h3 h1 hb hee0 hclose hT
  have hget : ∀ c, c < 3 → (Hid3 fl ex p w i).getD c 0 = relu (Pc2 fl ex p w c i) := by
    intro c hc
    interval_cases c <;> simp [Hid3]
  have hz' : ∀ c, c < 3 → c ≠ c0 →
      [relu (Pc2 fl ex p w 0 i), relu (Pc2 fl ex p w 1 i), relu (Pc2 fl ex p w 2 i)].getD c 0
        = 0 := by
    intro c hc hne
    have := hget c hc
    unfold Hid3 at this
    rw [this]
    exact hu_off c hc hne
  have hgl : [relu (Pc2 fl ex p w 0 i), relu (Pc2 fl ex p w 1 i),
      relu (Pc2 fl ex p w 2 i)].getD c0 0 = relu (Pc2 fl ex p w c0 i) := by
    have := hget c0 hc0
    unfold Hid3 at this
    exact this
  obtain ⟨_, _, _, h2w, h2o⟩ := gate_wts H c0
  have hu_on' := abs_le.mp hu_on
  have hub : |relu (Pc2 fl ex p w c0 i)| ≤ 22 / 10 := by
    rw [abs_le]; constructor <;> linarith [hu_on'.1, hu_on'.2, hT2'.1, hT2'.2]
  have hsu : |sw fl 1 (p.W2 1 12 c0) * relu (Pc2 fl ex p w c0 i) - T| ≤ 1433 / 10000 := by
    have hq : sw fl 1 (p.W2 1 12 c0) * relu (Pc2 fl ex p w c0 i) - T
        = (sw fl 1 (p.W2 1 12 c0) - 1) * relu (Pc2 fl ex p w c0 i)
          + (relu (Pc2 fl ex p w c0 i) - T) := by ring
    rw [hq]
    have h3 := abs_add_le ((sw fl 1 (p.W2 1 12 c0) - 1) * relu (Pc2 fl ex p w c0 i))
      (relu (Pc2 fl ex p w c0 i) - T)
    have h4 : |(sw fl 1 (p.W2 1 12 c0) - 1) * relu (Pc2 fl ex p w c0 i)|
        ≤ 6 / 1000 * (22 / 10) := by
      rw [abs_mul]
      exact mul_le_mul h2w hub (abs_nonneg _) (by norm_num)
    linarith
  have hsub : |sw fl 1 (p.W2 1 12 c0) * relu (Pc2 fl ex p w c0 i)| ≤ 3 := by
    have := abs_le.mp hsu
    rw [abs_le]; constructor <;> linarith [this.1, this.2, hT2'.1, hT2'.2]
  have hMo : |sw fl 1 (p.W2 1 12 c0) * [relu (Pc2 fl ex p w 0 i), relu (Pc2 fl ex p w 1 i),
      relu (Pc2 fl ex p w 2 i)].getD c0 0| ≤ M := by
    rw [hgl]; linarith
  have hFe : Fe fl ex p w i = fl (sw fl 1 (p.W2 1 12 c0) * relu (Pc2 fl ex p w c0 i)) := by
    have h := fin_gen hr (p.W2 1 12) (p.b2 1 12) _ _ _ c0 hc0 hz' hMo
    unfold Fe Hid3
    rw [h, hgl]
  have hFeb := abs_le.mp (hr.near hu0 hsu hsub (by linarith))
  have hFeclose : |Fe fl ex p w i - T| ≤ 145 / 1000 := by
    rw [hFe, abs_le]; constructor <;> linarith [hFeb.1, hFeb.2, hu1, hηs, hηs']
  have hFeb2 := abs_le.mp hFeclose
  have hfFe : fl (Fe fl ex p w i) = Fe fl ex p w i := by
    rw [hFe]; exact hr.idem _ (by linarith)
  have hs : sout net fl ex p w i
      = fl (rdot fl (sp 12 3 1) (srun net fl ex p w i) p.oW 0 0 + sw fl 0 p.oB) := rfl
  have hsrun : srun net fl ex p w i = x2l fl ex p w i := by
    show srunFrom fl ex p (w.length + 1) [blk1, blk2] 0 (net.init fl p w) i = _
    simp only [srunFrom, Nat.reduceAdd, zero_add]
    exact x2_eq H i hi hAb
  rw [hs, hsrun]
  have hg12 : (x2l fl ex p w i).getD 12 0 = fl (Fe fl ex p w i) := by simp [x2l]
  have hlen12 : 12 < (x2l fl ex p w i).length := by simp [x2l]
  have hFb : |Fe fl ex p w i| ≤ 22 / 10 := by
    rw [abs_le]; constructor <;> linarith [hFeb2.1, hFeb2.2, hT2'.1, hT2'.2]
  have hbd : |sw fl 1 (p.oW 12) * Fe fl ex p w i| ≤ 3 := by
    rw [abs_mul]
    have := mul_le_mul (abs_le.mpr ⟨by linarith [(abs_le.mp h2o).1], by linarith [(abs_le.mp h2o).2]⟩ :
      |sw fl 1 (p.oW 12)| ≤ 11 / 10) hFb (abs_nonneg _) (by norm_num)
    linarith
  have hso := rdot_sp hr 12 3 1 (x2l fl ex p w i) p.oW 0 hlen12
    (by rw [hg12, zero_add, hfFe]; linarith)
  rw [hg12, zero_add, hfFe] at hso
  rw [hso, sw_zero hr, add_zero, hr.idem _ (by linarith)]
  have hq : sw fl 1 (p.oW 12) * Fe fl ex p w i - T
      = (sw fl 1 (p.oW 12) - 1) * Fe fl ex p w i + (Fe fl ex p w i - T) := by ring
  have hq2 : |sw fl 1 (p.oW 12) * Fe fl ex p w i - T| ≤ 16 / 100 := by
    rw [hq]
    have h3 := abs_add_le ((sw fl 1 (p.oW 12) - 1) * Fe fl ex p w i) (Fe fl ex p w i - T)
    have h4 : |(sw fl 1 (p.oW 12) - 1) * Fe fl ex p w i| ≤ 6 / 1000 * (22 / 10) := by
      rw [abs_mul]
      exact mul_le_mul h2o hFb (abs_nonneg _) (by norm_num)
    linarith
  have hfin := abs_le.mp (hr.near hu0 hq2 hbd (by linarith))
  rw [abs_le]; constructor <;> linarith [hfin.1, hfin.2, hu1, hηs, hηs']

theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη p hp w hw hn hnη hM i hi1 hi
  have H : Ctx u η M fl ex p w := ⟨hr, he, hu0, hu1, hη0, hη, hp, hw, hn, hnη, hM⟩
  obtain ⟨W, hWp, htarget⟩ := exW w hw i hi1 hi
  have hτ1 := tok_pos w hw i hi1 hi
  have hτ3 := tok_le w hw i
  obtain ⟨c0, hc0, hτ⟩ : ∃ c0, c0 < 3 ∧ tokAt w i = c0 + 1 :=
    ⟨tokAt w i - 1, by omega, by omega⟩
  rw [hτ] at hWp
  by_cases hW2 : tokAt w W = 2
  · have hh : h (tokAt w W) = 2 := by simp [h, hW2]
    have hcast : ((target w i : ℕ) : ℝ) = 2 := by rw [htarget, hh]; norm_num
    rw [hcast]
    exact out_bound H i hi1 hi c0 hc0 hτ W hWp 2 (Or.inr rfl)
      ⟨fun _ => rfl, fun h' => absurd hW2 h'⟩
  · have hh : h (tokAt w W) = 0 := by simp [h, hW2]
    have hcast : ((target w i : ℕ) : ℝ) = 0 := by rw [htarget, hh]; norm_num
    rw [hcast]
    exact out_bound H i hi1 hi c0 hc0 hτ W hWp 0 (Or.inl rfl)
      ⟨fun h' => absurd h' hW2, fun _ => rfl⟩

end Lane4.Case
