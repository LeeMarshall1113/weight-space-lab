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
    |fl (fl (a * qk) + fl (nq * fl (b * g))) - (a * qk + nq * (b * g))| ≤ 4 := by
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
    rw [abs_le]; constructor <;> linarith [e1.1, e1.2, e3.1, e3.2]
  have e4 := abs_le.mp (hr.abs hu0 hsum (by linarith))
  have hexp : (N + 1 / 200) * (u * 218 + η) = 218 * (u * N) + 218 / 200 * u + η * N + η / 200 := by
    ring
  rw [abs_le]
  constructor <;> nlinarith [e1.1, e1.2, e3.1, e3.2, e4.1, e4.2, d2'.1, d2'.2, hexp, hn, hnη, hu1]

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

theorem net_ok : Statement net := by
  trivial

end Lane4.Case
