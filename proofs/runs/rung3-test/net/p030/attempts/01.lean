namespace Lane4.Case
open Lane4

/-! ### Network -/

def L1W : List (List ℚ) := [[-6, -3], [6, 3], [11/4, 33/4], [-11/4, -33/4], [11/5, 44/5], [-11/5, -44/5], [0, 27/5], [0, -57/10], [0, -27/10]]
def L1b : List ℚ := [-24, 24, 11, -11, -22/5, 22/5, 9/5, 247/20, 54/5]
def L2W : List (List ℚ) := [[0, -17/3, 68/11, 0, 0, 0, 0, 0, 0], [-19/2, 0, 0, 114/11, 0, 0, 0, 0, 0], [0, 0, 0, 0, -80/11, 0, 80/9, 0, 0], [0, 0, 0, 0, 0, -135/11, 0, 270/19, 0], [0, 0, 0, 0, 0, 0, 0, 0, 20/3]]
def L2b : List ℚ := [0, 0, 0, 0, 0]
def L3W : List (List ℚ) := [[-4/17, 8/57, 1/2, 0, 0], [18/17, -12/19, 0, 4/3, 0], [6/17, -4/19, 0, 0, 2/3]]
def L3b : List ℚ := [-20, -180, -18]
def OW : List (List ℚ) := [[1/8, -1/36, 1/12]]
def Ob : List ℚ := [-7/2]

def net : Net :=
  { hidden := [⟨L1W, L1b⟩, ⟨L2W, L2b⟩, ⟨L3W, L3b⟩], out := ⟨OW, Ob⟩ }

/-! ### Generic error bookkeeping -/

noncomputable def Err : List ℝ → List ℝ → List ℚ → Prop
  | y :: ys, z :: zs, e :: es => |y - z| ≤ (e : ℝ) ∧ Err ys zs es
  | [], [], [] => True
  | _, _, _ => False

noncomputable def absSum : List ℝ → ℝ
  | [] => 0
  | y :: ys => |y| + absSum ys

def wE : List ℚ → List ℚ → ℚ
  | a :: w, e :: es => |a| * e + wE w es
  | _, _ => 0

def sumL : List ℚ → ℚ
  | [] => 0
  | e :: es => e + sumL es

def errRows : List (List ℚ) → List ℚ → List ℚ → ℚ → List ℚ
  | r :: W, _ :: b, ε, T => (wE r ε + (1/1000) * (T + sumL ε) + 1/1000) :: errRows W b ε T
  | _, _, _, _ => []

theorem Err_cons {y z : ℝ} {ys zs : List ℝ} {e : ℚ} {es : List ℚ} :
    Err (y :: ys) (z :: zs) (e :: es) ↔ (|y - z| ≤ (e : ℝ) ∧ Err ys zs es) := Iff.rfl

theorem absSum_nonneg : ∀ l : List ℝ, 0 ≤ absSum l
  | [] => by simp [absSum]
  | y :: ys => by
    simp only [absSum]
    exact add_nonneg (abs_nonneg y) (absSum_nonneg ys)

theorem absSum_map_relu : ∀ l : List ℝ, absSum (l.map relu) = (l.map relu).sum
  | [] => by simp [absSum]
  | y :: ys => by
    simp only [List.map_cons, absSum, List.sum_cons]
    rw [abs_of_nonneg (relu_nonneg' y), absSum_map_relu ys]

theorem dotP_cons (a : ℚ) (w : List ℚ) (v : ℝ) (x : List ℝ) (d : ℕ → ℝ) (j : ℕ) :
    dotP (a :: w) (v :: x) d j = ((a : ℝ) + d j) * v + dotP w x d (j + 1) := by
  first | rfl | simp [dotP]

theorem dotP_nil_l (x : List ℝ) (d : ℕ → ℝ) (j : ℕ) : dotP [] x d j = 0 := by
  cases x <;> first | rfl | simp [dotP]

theorem dotP_nil_r (a : ℚ) (w : List ℚ) (d : ℕ → ℝ) (j : ℕ) : dotP (a :: w) [] d j = 0 := by
  first | rfl | simp [dotP]

theorem rowsP_cons (r : List ℚ) (W : List (List ℚ)) (c : ℚ) (b : List ℚ) (dW : ℕ → ℕ → ℝ)
    (db : ℕ → ℝ) (x : List ℝ) (i : ℕ) :
    rowsP (r :: W) (c :: b) dW db x i
      = (dotP r x (dW i) 0 + ((c : ℝ) + db i)) :: rowsP W b dW db x (i + 1) := by
  first | rfl | simp [rowsP]

theorem rowsP_nil_l (b : List ℚ) (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ) (x : List ℝ) (i : ℕ) :
    rowsP [] b dW db x i = [] := by
  cases b <;> first | rfl | simp [rowsP]

theorem rowsP_nil_r (r : List ℚ) (W : List (List ℚ)) (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ)
    (x : List ℝ) (i : ℕ) : rowsP (r :: W) [] dW db x i = [] := by
  first | rfl | simp [rowsP]

theorem errRows_cons (r : List ℚ) (W : List (List ℚ)) (c : ℚ) (b : List ℚ) (ε : List ℚ) (T : ℚ) :
    errRows (r :: W) (c :: b) ε T = (wE r ε + (1/1000) * (T + sumL ε) + 1/1000) :: errRows W b ε T := rfl

theorem errRows_nil_l (b ε : List ℚ) (T : ℚ) : errRows [] b ε T = [] := by
  cases b <;> rfl

theorem errRows_nil_r (r : List ℚ) (W : List (List ℚ)) (ε : List ℚ) (T : ℚ) :
    errRows (r :: W) [] ε T = [] := rfl

theorem absSum_le_of_Err : ∀ (y z : List ℝ) (e : List ℚ), Err y z e →
    absSum y ≤ absSum z + ((sumL e : ℚ) : ℝ) := by
  intro y
  induction y with
  | nil =>
    intro z e h
    cases z with
    | nil =>
      cases e with
      | nil => simp [absSum, sumL]
      | cons e es => simp [Err] at h
    | cons z zs => cases e <;> simp [Err] at h
  | cons y ys ih =>
    intro z e h
    cases z with
    | nil => cases e <;> simp [Err] at h
    | cons z zs =>
      cases e with
      | nil => simp [Err] at h
      | cons e es =>
        obtain ⟨h1, h2⟩ := Err_cons.mp h
        have h3 := ih zs es h2
        have h4 : |y| ≤ |z| + (e : ℝ) := by
          have := abs_sub_abs_le_abs_sub y z
          linarith
        simp only [absSum, sumL, Rat.cast_add]
        linarith

theorem abs_combo {A B P Q c1 c2 : ℝ} (h1 : |A - B| ≤ c1) (h2 : |P - Q| ≤ c2) :
    |A + P - (B + Q)| ≤ c1 + c2 := by
  have e : A + P - (B + Q) = (A - B) + (P - Q) := by ring
  rw [e]
  exact le_trans (abs_add_le _ _) (add_le_add h1 h2)

theorem dotP_err (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1/1000) :
    ∀ (w : List ℚ) (x' x : List ℝ) (ε : List ℚ) (j : ℕ), Err x' x ε →
      |dotP w x' d j - dotP w x (fun _ => 0) j| ≤ ((wE w ε : ℚ) : ℝ) + 1/1000 * absSum x' := by
  intro w
  induction w with
  | nil =>
    intro x' x ε j _
    have h0 : ((wE [] ε : ℚ) : ℝ) = 0 := by
      rw [show wE [] ε = 0 by cases ε <;> rfl]
      simp
    have h1 := absSum_nonneg x'
    rw [dotP_nil_l, dotP_nil_l, h0]
    have e1 : |(0:ℝ) - 0| = 0 := by simp
    rw [e1]
    linarith
  | cons a w ih =>
    intro x' x ε j h
    cases x' with
    | nil =>
      cases x with
      | nil =>
        cases ε with
        | nil =>
          rw [dotP_nil_r, dotP_nil_r]
          have h0 : ((wE (a :: w) [] : ℚ) : ℝ) = 0 := by
            rw [show wE (a :: w) [] = 0 from rfl]
            simp
          rw [h0]
          simp [absSum]
        | cons e es => simp [Err] at h
      | cons v xs => cases ε <;> simp [Err] at h
    | cons v' xs' =>
      cases x with
      | nil => cases ε <;> simp [Err] at h
      | cons v xs =>
        cases ε with
        | nil => simp [Err] at h
        | cons e es =>
          obtain ⟨h1, h2⟩ := Err_cons.mp h
          have ihh := ih xs' xs es (j + 1) h2
          have k1 : |((a:ℝ) + d j) * v' - ((a:ℝ) + 0) * v|
              ≤ |(a:ℝ)| * (e:ℝ) + 1/1000 * |v'| := by
            have e1 : ((a:ℝ) + d j) * v' - ((a:ℝ) + 0) * v
                = (a:ℝ) * (v' - v) + d j * v' := by ring
            rw [e1]
            have m1 : |(a:ℝ) * (v' - v)| ≤ |(a:ℝ)| * (e:ℝ) := by
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
            have m2 : |d j * v'| ≤ 1/1000 * |v'| := by
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_right (hd j) (abs_nonneg _)
            exact le_trans (abs_add_le _ _) (add_le_add m1 m2)
          rw [dotP_cons, dotP_cons]
          refine le_trans (abs_combo k1 ihh) (le_of_eq ?_)
          simp only [wE, absSum]
          push_cast
          ring

theorem Err_map_relu : ∀ (y z : List ℝ) (e : List ℚ), Err y z e →
    Err (y.map relu) (z.map relu) e := by
  intro y
  induction y with
  | nil =>
    intro z e h
    cases z with
    | nil =>
      cases e with
      | nil => exact trivial
      | cons e es => simp [Err] at h
    | cons z zs => cases e <;> simp [Err] at h
  | cons y ys ih =>
    intro z e h
    cases z with
    | nil => cases e <;> simp [Err] at h
    | cons z zs =>
      cases e with
      | nil => simp [Err] at h
      | cons e es =>
        obtain ⟨h1, h2⟩ := Err_cons.mp h
        simp only [List.map_cons]
        exact Err_cons.mpr ⟨le_trans (relu_sub_le y z) h1, ih zs es h2⟩

theorem rowsP_err (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ) (hw : ∀ i j, |dW i j| ≤ 1/1000)
    (hb : ∀ i, |db i| ≤ 1/1000) :
    ∀ (W : List (List ℚ)) (b : List ℚ) (x' x : List ℝ) (ε : List ℚ) (T : ℚ) (i : ℕ),
      Err x' x ε → absSum x ≤ (T : ℝ) →
      Err (rowsP W b dW db x' i) (rowsP W b (fun _ _ => 0) (fun _ => 0) x i) (errRows W b ε T) := by
  intro W
  induction W with
  | nil =>
    intro b x' x ε T i _ _
    rw [rowsP_nil_l, rowsP_nil_l, errRows_nil_l]
    exact trivial
  | cons r W ih =>
    intro b x' x ε T i hE hA
    cases b with
    | nil =>
      rw [rowsP_nil_r, rowsP_nil_r, errRows_nil_r]
      exact trivial
    | cons c b =>
      rw [rowsP_cons, rowsP_cons, errRows_cons]
      refine Err_cons.mpr ⟨?_, ih b x' x ε T (i + 1) hE hA⟩
      have h1 := dotP_err (dW i) (hw i) r x' x ε 0 hE
      have h2 := absSum_le_of_Err x' x ε hE
      have h3 := abs_le.mp (hb i)
      have h4 := abs_le.mp h1
      have h5 : ((wE r ε + (1/1000) * (T + sumL ε) + 1/1000 : ℚ) : ℝ)
          = (wE r ε : ℝ) + 1/1000 * ((T : ℝ) + (sumL ε : ℝ)) + 1/1000 := by
        push_cast
        ring
      rw [h5]
      show |(dotP r x' (dW i) 0 + ((c : ℝ) + db i))
          - (dotP r x (fun _ => 0) 0 + ((c : ℝ) + 0))| ≤ _
      rw [abs_le]
      constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]

theorem fin_aux {l z : List ℝ} {es : List ℚ} {s : ℝ} (hz : z = [s]) (hE : Err l z es)
    (hl : ∀ q ∈ es, q ≤ 3/10) : ∃ y, l = [y] ∧ |y - s| ≤ 3/10 := by
  subst hz
  cases l with
  | nil => cases es <;> simp [Err] at hE
  | cons y ys =>
    cases es with
    | nil => simp [Err] at hE
    | cons e es' =>
      obtain ⟨h1, h2⟩ := Err_cons.mp hE
      cases ys with
      | nil =>
        refine ⟨y, rfl, ?_⟩
        have h3 : e ≤ 3/10 := hl e (by simp)
        have h4 : (e : ℝ) ≤ 3/10 := by exact_mod_cast h3
        linarith
      | cons y2 ys2 => cases es' <;> simp [Err] at h2

theorem relu_eq' {p s y v : ℝ} (hs : 0 ≤ s) (h : p = s * y) (hv : v = relu y) :
    relu p = s * v := by
  subst hv
  subst h
  unfold relu
  rw [mul_max_of_nonneg _ _ hs, mul_zero]

/-! ### Clean (unperturbed) semantics -/

noncomputable def cl (W : List (List ℚ)) (b : List ℚ) (x : List ℝ) : List ℝ :=
  (rowsP W b (fun _ _ => 0) (fun _ => 0) x 0).map relu

theorem absSum_cl (W : List (List ℚ)) (b : List ℚ) (x : List ℝ) :
    absSum (cl W b x) = (cl W b x).sum := absSum_map_relu _

noncomputable def qa (x0 x1 : ℝ) : ℝ := 2 * x1 + (-5/2)
noncomputable def qb (x0 x1 : ℝ) : ℝ := (-1) * x0 + (-2) * x1 + (-1/2)
noncomputable def qc (x0 x1 : ℝ) : ℝ := (-1) * x1 + (-1)
noncomputable def qd (x0 x1 : ℝ) : ℝ := (1/2) * x0 + (1/2) * x1 + 1
noncomputable def qe (x0 x1 : ℝ) : ℝ := (-1/2) * x0 + (-3)

noncomputable def uR1 (x0 x1 : ℝ) : ℝ := relu (qe x0 x1 - qd x0 x1)
noncomputable def uR2 (x0 x1 : ℝ) : ℝ := relu (qd x0 x1 - qe x0 x1)
noncomputable def uD1 (x0 x1 : ℝ) : ℝ := relu (qd x0 x1 - qc x0 x1)
noncomputable def uD2 (x0 x1 : ℝ) : ℝ := relu (qc x0 x1 - qd x0 x1)
noncomputable def uV1 (x0 x1 : ℝ) : ℝ := relu ((qa x0 x1 - qc x0 x1) - (qb x0 x1 - qc x0 x1))
noncomputable def uV2 (x0 x1 : ℝ) : ℝ := relu ((qb x0 x1 - qc x0 x1) - (qa x0 x1 - qc x0 x1))
noncomputable def uEf (x0 x1 : ℝ) : ℝ := relu ((qa x0 x1 - qc x0 x1) + 5/2)
noncomputable def uFf (x0 x1 : ℝ) : ℝ := relu (5 - (qa x0 x1 - qc x0 x1))
noncomputable def uCc (x0 x1 : ℝ) : ℝ := relu (qc x0 x1 + 5)

noncomputable def uU1 (x0 x1 : ℝ) : ℝ := relu (uD1 x0 x1 - uR2 x0 x1)
noncomputable def uU2 (x0 x1 : ℝ) : ℝ := relu (uD2 x0 x1 - uR1 x0 x1)
noncomputable def uSa (x0 x1 : ℝ) : ℝ := relu (uEf x0 x1 - uV1 x0 x1)
noncomputable def uSb (x0 x1 : ℝ) : ℝ := relu (uFf x0 x1 - uV2 x0 x1)
noncomputable def uC2 (x0 x1 : ℝ) : ℝ := relu (uCc x0 x1)

noncomputable def uN (x0 x1 : ℝ) : ℝ := relu (uSa x0 x1 - 5/2 - uU1 x0 x1 + uU2 x0 x1)
noncomputable def uP (x0 x1 : ℝ) : ℝ := relu (uSb x0 x1 - 5 + uU1 x0 x1 - uU2 x0 x1)
noncomputable def uQ (x0 x1 : ℝ) : ℝ := relu (uC2 x0 x1 + uU1 x0 x1 - uU2 x0 x1 - 5 + 7/2)

noncomputable def Qf (x0 x1 : ℝ) : ℝ :=
  max (min (qc x0 x1) (qd x0 x1)) (min (max (qc x0 x1) (qd x0 x1)) (qe x0 x1))

theorem cl1_eq (x0 x1 : ℝ) : cl L1W L1b [x0, x1] = [6 * uR1 x0 x1, 6 * uR2 x0 x1, 11/2 * uD1 x0 x1, 11/2 * uD2 x0 x1, 11/5 * uV1 x0 x1, 11/5 * uV2 x0 x1, 9/5 * uEf x0 x1, 19/10 * uFf x0 x1, 27/10 * uCc x0 x1] := by
  simp only [cl, L1W, L1b, rowsP_cons, rowsP_nil_l, dotP_cons, dotP_nil_l, List.map_cons, List.map_nil]
  exact List.cons_eq_cons.mpr ⟨relu_eq' (by norm_num) (by simp only [qa, qb, qc, qd, qe]; push_cast; ring) rfl, List.cons_eq_cons.mpr ⟨relu_eq' (by norm_num) (by simp only [qa, qb, qc, qd, qe]; push_cast; ring) rfl, List.cons_eq_cons.mpr ⟨relu_eq' (by norm_num) (by simp only [qa, qb, qc, qd, qe]; push_cast; ring) rfl, List.cons_eq_cons.mpr ⟨relu_eq' (by norm_num) (by simp only [qa, qb, qc, qd, qe]; push_cast; ring) rfl, List.cons_eq_cons.mpr ⟨relu_eq' (by norm_num) (by simp only [qa, qb, qc, qd, qe]; push_cast; ring) rfl, List.cons_eq_cons.mpr ⟨relu_eq' (by norm_num) (by simp only [qa, qb, qc, qd, qe]; push_cast; ring) rfl, List.cons_eq_cons.mpr ⟨relu_eq' (by norm_num) (by simp only [qa, qb, qc, qd, qe]; push_cast; ring) rfl, List.cons_eq_cons.mpr ⟨relu_eq' (by norm_num) (by simp only [qa, qb, qc, qd, qe]; push_cast; ring) rfl, List.cons_eq_cons.mpr ⟨relu_eq' (by norm_num) (by simp only [qa, qb, qc, qd, qe]; push_cast; ring) rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem cl2_eq (x0 x1 : ℝ) : cl L2W L2b (cl L1W L1b [x0, x1]) = [34 * uU1 x0 x1, 57 * uU2 x0 x1, 16 * uSa x0 x1, 27 * uSb x0 x1, 18 * uC2 x0 x1] := by
  rw [cl1_eq x0 x1]
  simp only [cl, L2W, L2b, rowsP_cons, rowsP_nil_l, dotP_cons, dotP_nil_l, List.map_cons, List.map_nil]
  exact List.cons_eq_cons.mpr ⟨relu_eq' (by norm_num) (by push_cast; ring) rfl, List.cons_eq_cons.mpr ⟨relu_eq' (by norm_num) (by push_cast; ring) rfl, List.cons_eq_cons.mpr ⟨relu_eq' (by norm_num) (by push_cast; ring) rfl, List.cons_eq_cons.mpr ⟨relu_eq' (by norm_num) (by push_cast; ring) rfl, List.cons_eq_cons.mpr ⟨relu_eq' (by norm_num) (by push_cast; ring) rfl, rfl⟩⟩⟩⟩⟩

theorem cl3_eq (x0 x1 : ℝ) : cl L3W L3b (cl L2W L2b (cl L1W L1b [x0, x1])) = [8 * uN x0 x1, 36 * uP x0 x1, 12 * uQ x0 x1] := by
  rw [cl2_eq x0 x1]
  simp only [cl, L3W, L3b, rowsP_cons, rowsP_nil_l, dotP_cons, dotP_nil_l, List.map_cons, List.map_nil]
  exact List.cons_eq_cons.mpr ⟨relu_eq' (by norm_num) (by push_cast; ring) rfl, List.cons_eq_cons.mpr ⟨relu_eq' (by norm_num) (by push_cast; ring) rfl, List.cons_eq_cons.mpr ⟨relu_eq' (by norm_num) (by push_cast; ring) rfl, rfl⟩⟩⟩

/-! ### Semantic identities (plain real numbers) -/

theorem sem_U1 (c d e : ℝ) :
    relu (relu (d - c) - relu (d - e)) = relu (min (d - c) (e - c)) := by
  simp only [relu, max_def, min_def]
  split_ifs <;> linarith

theorem sem_U2 (c d e : ℝ) :
    relu (relu (c - d) - relu (e - d)) = relu (-(max (d - c) (e - c))) := by
  simp only [relu, max_def, min_def]
  split_ifs <;> linarith

theorem sem_Sa (a b c : ℝ) :
    relu (relu ((a - c) + 5/2) - relu ((a - c) - (b - c))) = relu (min (a - c) (b - c) + 5/2) := by
  simp only [relu, max_def, min_def]
  split_ifs <;> linarith

theorem sem_Sb (a b c : ℝ) :
    relu (relu (5 - (a - c)) - relu ((b - c) - (a - c))) = relu (5 - max (a - c) (b - c)) := by
  simp only [relu, max_def, min_def]
  split_ifs <;> linarith

theorem sem_Q (c d e : ℝ) :
    c + (relu (min (d - c) (e - c)) - relu (-(max (d - c) (e - c))))
      = max (min c d) (min (max c d) e) := by
  simp only [relu, max_def, min_def]
  split_ifs <;> linarith

theorem sem_N (m U1 U2 : ℝ) (h : -5/2 ≤ U1 - U2) :
    relu (relu (m + 5/2) - 5/2 - U1 + U2) = relu (m - (U1 - U2)) := by
  simp only [relu, max_def]
  split_ifs <;> linarith

theorem sem_P (M U1 U2 : ℝ) (h : U1 - U2 ≤ 5) :
    relu (relu (5 - M) - 5 + U1 - U2) = relu ((U1 - U2) - M) := by
  simp only [relu, max_def]
  split_ifs <;> linarith

theorem clamp_eq (a b q : ℝ) :
    max (min a b) (min (max a b) q) = q + relu (min a b - q) - relu (q - max a b) := by
  simp only [relu, max_def, min_def]
  split_ifs <;> linarith

theorem eU1 (x0 x1 : ℝ) :
    uU1 x0 x1 = relu (min (qd x0 x1 - qc x0 x1) (qe x0 x1 - qc x0 x1)) :=
  sem_U1 (qc x0 x1) (qd x0 x1) (qe x0 x1)

theorem eU2 (x0 x1 : ℝ) :
    uU2 x0 x1 = relu (-(max (qd x0 x1 - qc x0 x1) (qe x0 x1 - qc x0 x1))) :=
  sem_U2 (qc x0 x1) (qd x0 x1) (qe x0 x1)

theorem eSa (x0 x1 : ℝ) :
    uSa x0 x1 = relu (min (qa x0 x1 - qc x0 x1) (qb x0 x1 - qc x0 x1) + 5/2) :=
  sem_Sa (qa x0 x1) (qb x0 x1) (qc x0 x1)

theorem eSb (x0 x1 : ℝ) :
    uSb x0 x1 = relu (5 - max (qa x0 x1 - qc x0 x1) (qb x0 x1 - qc x0 x1)) :=
  sem_Sb (qa x0 x1) (qb x0 x1) (qc x0 x1)

theorem eC2 (x0 x1 : ℝ) (l1 : -2 ≤ x1) (u1 : x1 ≤ 4) : uC2 x0 x1 = qc x0 x1 + 5 := by
  have h5 : 0 ≤ qc x0 x1 + 5 := by
    simp only [qc]
    linarith
  show relu (relu (qc x0 x1 + 5)) = qc x0 x1 + 5
  rw [relu_of_nonneg h5, relu_of_nonneg h5]

theorem spec_eq (x0 x1 : ℝ) :
    spec x0 x1 = max (min (qa x0 x1) (qb x0 x1)) (min (max (qa x0 x1) (qb x0 x1)) (Qf x0 x1)) := rfl

theorem sem_facts (x0 x1 : ℝ) (l0 : -8 ≤ x0) (u0 : x0 ≤ 1) (l1 : -2 ≤ x1) (u1 : x1 ≤ 4) :
    uN x0 x1 = relu (min (qa x0 x1) (qb x0 x1) - Qf x0 x1) ∧
    uP x0 x1 = relu (Qf x0 x1 - max (qa x0 x1) (qb x0 x1)) ∧
    uQ x0 x1 = Qf x0 x1 + 7/2 := by
  have hU1 := eU1 x0 x1
  have hU2 := eU2 x0 x1
  have hSa := eSa x0 x1
  have hSb := eSb x0 x1
  have hC := eC2 x0 x1 l1 u1
  have hQeq : qc x0 x1 + (uU1 x0 x1 - uU2 x0 x1) = Qf x0 x1 := by
    rw [hU1, hU2]
    exact sem_Q (qc x0 x1) (qd x0 x1) (qe x0 x1)
  have hub1 : uU1 x0 x1 - uU2 x0 x1 ≤ 5 := by
    rw [hU1, hU2]
    simp only [qc, qd, qe, relu, max_def, min_def]
    split_ifs <;> linarith
  have hub2 : -5/2 ≤ uU1 x0 x1 - uU2 x0 x1 := by
    rw [hU1, hU2]
    simp only [qc, qd, qe, relu, max_def, min_def]
    split_ifs <;> linarith
  have hQlo : -7/2 ≤ Qf x0 x1 := by
    simp only [Qf, qc, qd, qe, max_def, min_def]
    split_ifs <;> linarith
  have hu : uU1 x0 x1 - uU2 x0 x1 = Qf x0 x1 - qc x0 x1 := by linarith
  have hm : min (qa x0 x1 - qc x0 x1) (qb x0 x1 - qc x0 x1)
      = min (qa x0 x1) (qb x0 x1) - qc x0 x1 := by
    simp only [min_def]
    split_ifs <;> linarith
  have hM : max (qa x0 x1 - qc x0 x1) (qb x0 x1 - qc x0 x1)
      = max (qa x0 x1) (qb x0 x1) - qc x0 x1 := by
    simp only [max_def]
    split_ifs <;> linarith
  refine ⟨?_, ?_, ?_⟩
  · have h1 : uN x0 x1 = relu (relu (min (qa x0 x1 - qc x0 x1) (qb x0 x1 - qc x0 x1) + 5/2)
        - 5/2 - uU1 x0 x1 + uU2 x0 x1) := by
      show relu (uSa x0 x1 - 5/2 - uU1 x0 x1 + uU2 x0 x1) = _
      rw [hSa]
    rw [h1, sem_N _ _ _ hub2, hm, hu]
    congr 1
    ring
  · have h1 : uP x0 x1 = relu (relu (5 - max (qa x0 x1 - qc x0 x1) (qb x0 x1 - qc x0 x1))
        - 5 + uU1 x0 x1 - uU2 x0 x1) := by
      show relu (uSb x0 x1 - 5 + uU1 x0 x1 - uU2 x0 x1) = _
      rw [hSb]
    rw [h1, sem_P _ _ _ hub1, hM, hu]
    congr 1
    ring
  · have h1 : uQ x0 x1 = relu (qc x0 x1 + 5 + uU1 x0 x1 - uU2 x0 x1 - 5 + 7/2) := by
      show relu (uC2 x0 x1 + uU1 x0 x1 - uU2 x0 x1 - 5 + 7/2) = _
      rw [hC]
    rw [h1]
    have h2 : qc x0 x1 + 5 + uU1 x0 x1 - uU2 x0 x1 - 5 + 7/2 = Qf x0 x1 + 7/2 := by linarith
    rw [h2]
    exact relu_of_nonneg (by linarith)

theorem sem_all (x0 x1 : ℝ) (l0 : -8 ≤ x0) (u0 : x0 ≤ 1) (l1 : -2 ≤ x1) (u1 : x1 ≤ 4) :
    uQ x0 x1 + uN x0 x1 - uP x0 x1 - 7/2 = spec x0 x1 := by
  obtain ⟨hN, hP, hQ⟩ := sem_facts x0 x1 l0 u0 l1 u1
  rw [spec_eq, clamp_eq, hN, hP, hQ]
  ring

theorem clout (x0 x1 : ℝ) (l0 : -8 ≤ x0) (u0 : x0 ≤ 1) (l1 : -2 ≤ x1) (u1 : x1 ≤ 4) :
    rowsP OW Ob (fun _ _ => 0) (fun _ => 0) (cl L3W L3b (cl L2W L2b (cl L1W L1b [x0, x1]))) 0
      = [spec x0 x1] := by
  rw [cl3_eq x0 x1]
  simp only [OW, Ob, rowsP_cons, rowsP_nil_l, dotP_cons, dotP_nil_l]
  refine List.cons_eq_cons.mpr ⟨?_, rfl⟩
  rw [← sem_all x0 x1 l0 u0 l1 u1]
  push_cast
  ring

/-! ### Bounds on the sums of clean hidden values -/

theorem A0 (x0 x1 : ℝ) (l0 : -8 ≤ x0) (u0 : x0 ≤ 1) (l1 : -2 ≤ x1) (u1 : x1 ≤ 4) :
    absSum [x0, x1] ≤ ((12 : ℚ) : ℝ) := by
  have h0 : |x0| ≤ 8 := abs_le.mpr ⟨by linarith, by linarith⟩
  have h1 : |x1| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  simp only [absSum]
  push_cast
  linarith

theorem bR (x0 x1 : ℝ) (l0 : -8 ≤ x0) (u0 : x0 ≤ 1) (l1 : -2 ≤ x1) (u1 : x1 ≤ 4) :
    uR1 x0 x1 + uR2 x0 x1 ≤ 7 := by
  simp only [uR1, uR2, qd, qe, relu, max_def]
  split_ifs <;> linarith

theorem bD (x0 x1 : ℝ) (l0 : -8 ≤ x0) (u0 : x0 ≤ 1) (l1 : -2 ≤ x1) (u1 : x1 ≤ 4) :
    uD1 x0 x1 + uD2 x0 x1 ≤ 17/2 := by
  simp only [uD1, uD2, qc, qd, relu, max_def]
  split_ifs <;> linarith

theorem bV (x0 x1 : ℝ) (l0 : -8 ≤ x0) (u0 : x0 ≤ 1) (l1 : -2 ≤ x1) (u1 : x1 ≤ 4) :
    uV1 x0 x1 + uV2 x0 x1 ≤ 18 := by
  simp only [uV1, uV2, qa, qb, qc, relu, max_def]
  split_ifs <;> linarith

theorem bEf (x0 x1 : ℝ) (l0 : -8 ≤ x0) (u0 : x0 ≤ 1) (l1 : -2 ≤ x1) (u1 : x1 ≤ 4) :
    uEf x0 x1 ≤ 13 := by
  simp only [uEf, qa, qc, relu, max_def]
  split_ifs <;> linarith

theorem bFf (x0 x1 : ℝ) (l0 : -8 ≤ x0) (u0 : x0 ≤ 1) (l1 : -2 ≤ x1) (u1 : x1 ≤ 4) :
    uFf x0 x1 ≤ 25/2 := by
  simp only [uFf, qa, qc, relu, max_def]
  split_ifs <;> linarith

theorem bCc (x0 x1 : ℝ) (l0 : -8 ≤ x0) (u0 : x0 ≤ 1) (l1 : -2 ≤ x1) (u1 : x1 ≤ 4) :
    uCc x0 x1 ≤ 6 := by
  simp only [uCc, qc, relu, max_def]
  split_ifs <;> linarith

theorem A1 (x0 x1 : ℝ) (l0 : -8 ≤ x0) (u0 : x0 ≤ 1) (l1 : -2 ≤ x1) (u1 : x1 ≤ 4) :
    absSum (cl L1W L1b [x0, x1]) ≤ ((1917/10 : ℚ) : ℝ) := by
  rw [absSum_cl, cl1_eq]
  simp only [List.sum_cons, List.sum_nil]
  push_cast
  linarith [bR x0 x1 l0 u0 l1 u1, bD x0 x1 l0 u0 l1 u1, bV x0 x1 l0 u0 l1 u1,
    bEf x0 x1 l0 u0 l1 u1, bFf x0 x1 l0 u0 l1 u1, bCc x0 x1 l0 u0 l1 u1]

theorem A2 (x0 x1 : ℝ) (l0 : -8 ≤ x0) (u0 : x0 ≤ 1) (l1 : -2 ≤ x1) (u1 : x1 ≤ 4) :
    absSum (cl L2W L2b (cl L1W L1b [x0, x1])) ≤ ((252 : ℚ) : ℝ) := by
  rw [absSum_cl, cl2_eq]
  simp only [List.sum_cons, List.sum_nil]
  push_cast
  rw [eU1 x0 x1, eU2 x0 x1, eSa x0 x1, eSb x0 x1, eC2 x0 x1 l1 u1]
  simp only [qa, qb, qc, qd, qe, relu, max_def, min_def]
  split_ifs <;> linarith

theorem A3 (x0 x1 : ℝ) (l0 : -8 ≤ x0) (u0 : x0 ≤ 1) (l1 : -2 ≤ x1) (u1 : x1 ≤ 4) :
    absSum (cl L3W L3b (cl L2W L2b (cl L1W L1b [x0, x1]))) ≤ ((56 : ℚ) : ℝ) := by
  rw [absSum_cl, cl3_eq]
  simp only [List.sum_cons, List.sum_nil]
  push_cast
  obtain ⟨hN, hP, hQ⟩ := sem_facts x0 x1 l0 u0 l1 u1
  rw [hN, hP, hQ]
  simp only [Qf, qa, qb, qc, qd, qe, relu, max_def, min_def]
  split_ifs <;> linarith

/-! ### The numeric check -/

def eOut : List ℚ :=
  errRows OW Ob (errRows L3W L3b (errRows L2W L2b (errRows L1W L1b [0, 0] 12) (1917/10)) 252) 56

set_option maxRecDepth 100000 in
theorem eOut_ok : ∀ q ∈ eOut, q ≤ 3/10 := by
  first
    | decide
    | (simp only [eOut, errRows, wE, sumL, L1W, L1b, L2W, L2b, L3W, L3b, OW, Ob]; norm_num)

/-! ### The theorem -/

theorem net_robust : StatementRobust net := by
  intro dW db hW x0 x1 l0 u0 l1 u1
  obtain ⟨hw, hb⟩ := hW
  have E0 : Err [x0, x1] [x0, x1] [0, 0] := by simp [Err]
  have E1 := Err_map_relu _ _ _
    (rowsP_err (dW 0) (db 0) (hw 0) (hb 0) L1W L1b [x0, x1] [x0, x1] [0, 0] 12 0 E0
      (A0 x0 x1 l0 u0 l1 u1))
  have E2 := Err_map_relu _ _ _
    (rowsP_err (dW 1) (db 1) (hw 1) (hb 1) L2W L2b _ _ _ (1917/10) 0 E1 (A1 x0 x1 l0 u0 l1 u1))
  have E3 := Err_map_relu _ _ _
    (rowsP_err (dW 2) (db 2) (hw 2) (hb 2) L3W L3b _ _ _ 252 0 E2 (A2 x0 x1 l0 u0 l1 u1))
  have E4 := rowsP_err (dW 3) (db 3) (hw 3) (hb 3) OW Ob _ _ _ 56 0 E3 (A3 x0 x1 l0 u0 l1 u1)
  obtain ⟨y, hy, hy2⟩ := fin_aux (clout x0 x1 l0 u0 l1 u1) E4 eOut_ok
  exact ⟨y, hy, hy2⟩

end Lane4.Case
