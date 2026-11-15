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
    exact score1_eq hr (p.A 0 c) c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp) (fl (k' : ℝ)) (by simp)
      hM1 (hr.idem _ hM1)
  have hEb : ∀ τ : ℕ, |ee fl p τ c| ≤ 11 / 10 := by
    intro τ
    by_cases h : τ = c + 1
    · have := abs_le.mp (((hee τ c).1 h))
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    · rw [(hee τ c).2 h]; norm_num
  have hVb : |sw fl 1 (p.V 0 c (3 + c) c)| ≤ 11 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hVEb : ∀ τ : ℕ, |sw fl 1 (p.V 0 c (3 + c) c) * ee fl p τ c| ≤ 6 / 5 := by
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
    have e2 := hr.near hu0 (e1 : |sw fl 1 (p.V 0 c (3 + c) c) * ee fl p (tokAt w (k - 1)) c - 1| ≤ 1 / 190 + 1 / 190 + 1 / 190 * (1 / 190)) (hVEb _) (by linarith)
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

theorem net_ok : Statement net := by
  trivial

end Lane4.Case
