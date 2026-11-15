/-
Bridge (PREREG_BRIDGE): weight-space interval bound propagation, proved sound once
against lane 4's perturbed forward pass `Lane4.Net.evalP` (Lane4/Robust.lean, read-only).

`ibpNet N τ x` is a computable rational interval for every output of every network whose
weights and biases are each within τ of `N`'s, on the fixed input `x`. `cert` turns a
passing Boolean check (closed by kernel evaluation, no `native_decide`) into the statement
`Spec6`: for every weight setting in the closed τ-ball and every x ∈ {0,1}^6, the output
has the sign of the label "popcount(x) mod 3 = 0".
-/
import Lane4.Robust

namespace Bridge
open Lane4

/-! ### Intervals of one perturbed product -/

def min4 (a b c d : ℚ) : ℚ := min (min a b) (min c d)
def max4 (a b c d : ℚ) : ℚ := max (max a b) (max c d)

/-- Bounds of `(a + d) * v` for `|d| ≤ τ`, `v ∈ [l, u]`. -/
def pLo (a τ l u : ℚ) : ℚ := min4 ((a - τ) * l) ((a - τ) * u) ((a + τ) * l) ((a + τ) * u)
def pHi (a τ l u : ℚ) : ℚ := max4 ((a - τ) * l) ((a - τ) * u) ((a + τ) * l) ((a + τ) * u)

theorem lin_ge_min {c p q t : ℝ} (hp : p ≤ t) (hq : t ≤ q) : min (c * p) (c * q) ≤ c * t := by
  rcases le_total 0 c with h | h
  · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hp h)
  · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hq h)

theorem lin_le_max {c p q t : ℝ} (hp : p ≤ t) (hq : t ≤ q) : c * t ≤ max (c * p) (c * q) := by
  rcases le_total 0 c with h | h
  · exact le_trans (mul_le_mul_of_nonneg_left hq h) (le_max_right _ _)
  · exact le_trans (mul_le_mul_of_nonpos_left hp h) (le_max_left _ _)

theorem prod_lo {α β l u x v : ℝ} (hx1 : α ≤ x) (hx2 : x ≤ β) (hv1 : l ≤ v) (hv2 : v ≤ u) :
    min (min (α * l) (α * u)) (min (β * l) (β * u)) ≤ x * v := by
  have h1 : min (x * l) (x * u) ≤ x * v := lin_ge_min hv1 hv2
  have h2 : min (l * α) (l * β) ≤ l * x := lin_ge_min hx1 hx2
  have h3 : min (u * α) (u * β) ≤ u * x := lin_ge_min hx1 hx2
  refine le_trans (le_min ?_ ?_) h1
  · have : min (min (α * l) (α * u)) (min (β * l) (β * u)) ≤ min (l * α) (l * β) := by
      rw [mul_comm l α, mul_comm l β]
      exact le_min (le_trans (min_le_left _ _) (min_le_left _ _))
        (le_trans (min_le_right _ _) (min_le_left _ _))
    linarith [mul_comm l x]
  · have : min (min (α * l) (α * u)) (min (β * l) (β * u)) ≤ min (u * α) (u * β) := by
      rw [mul_comm u α, mul_comm u β]
      exact le_min (le_trans (min_le_left _ _) (min_le_right _ _))
        (le_trans (min_le_right _ _) (min_le_right _ _))
    linarith [mul_comm u x]

theorem prod_hi {α β l u x v : ℝ} (hx1 : α ≤ x) (hx2 : x ≤ β) (hv1 : l ≤ v) (hv2 : v ≤ u) :
    x * v ≤ max (max (α * l) (α * u)) (max (β * l) (β * u)) := by
  have h1 : x * v ≤ max (x * l) (x * u) := lin_le_max hv1 hv2
  have h2 : l * x ≤ max (l * α) (l * β) := lin_le_max hx1 hx2
  have h3 : u * x ≤ max (u * α) (u * β) := lin_le_max hx1 hx2
  refine le_trans h1 (max_le ?_ ?_)
  · have : max (l * α) (l * β) ≤ max (max (α * l) (α * u)) (max (β * l) (β * u)) := by
      rw [mul_comm l α, mul_comm l β]
      exact max_le (le_trans (le_max_left _ _) (le_max_left _ _))
        (le_trans (le_max_left _ _) (le_max_right _ _))
    linarith [mul_comm l x]
  · have : max (u * α) (u * β) ≤ max (max (α * l) (α * u)) (max (β * l) (β * u)) := by
      rw [mul_comm u α, mul_comm u β]
      exact max_le (le_trans (le_max_right _ _) (le_max_left _ _))
        (le_trans (le_max_right _ _) (le_max_right _ _))
    linarith [mul_comm u x]

theorem pert_bounds {a τ l u : ℚ} {d v : ℝ} (hd : |d| ≤ (τ : ℝ)) (hl : (l : ℝ) ≤ v) (hu : v ≤ (u : ℝ)) :
    ((pLo a τ l u : ℚ) : ℝ) ≤ ((a : ℝ) + d) * v ∧ ((a : ℝ) + d) * v ≤ ((pHi a τ l u : ℚ) : ℝ) := by
  obtain ⟨h1, h2⟩ := abs_le.mp hd
  have hx1 : (a : ℝ) - τ ≤ (a : ℝ) + d := by linarith
  have hx2 : (a : ℝ) + d ≤ (a : ℝ) + τ := by linarith
  unfold pLo pHi min4 max4
  push_cast
  exact ⟨prod_lo hx1 hx2 hl hu, prod_hi hx1 hx2 hl hu⟩

/-! ### Bounds on lists -/

/-- `vs` lies componentwise in `[ls, us]`, and the three lists have equal length. -/
def Bnd : List ℚ → List ℚ → List ℝ → Prop
  | l :: ls, u :: us, v :: vs => (l : ℝ) ≤ v ∧ v ≤ (u : ℝ) ∧ Bnd ls us vs
  | [], [], [] => True
  | _, _, _ => False

def ibpDot : List ℚ → List ℚ → List ℚ → ℚ → ℚ × ℚ
  | a :: w, l :: ls, u :: us, τ =>
    (pLo a τ l u + (ibpDot w ls us τ).1, pHi a τ l u + (ibpDot w ls us τ).2)
  | _, _, _, _ => (0, 0)

theorem dot_sound (τ : ℚ) (d : ℕ → ℝ) (hd : ∀ j, |d j| ≤ (τ : ℝ)) :
    ∀ (w ls us : List ℚ) (vs : List ℝ) (j : ℕ), Bnd ls us vs →
      (((ibpDot w ls us τ).1 : ℚ) : ℝ) ≤ dotP w vs d j ∧ dotP w vs d j ≤ (((ibpDot w ls us τ).2 : ℚ) : ℝ) := by
  intro w
  induction w with
  | nil =>
    intro ls us vs j _
    simp [ibpDot, dotP]
  | cons a w ih =>
    intro ls us vs j h
    rcases ls with _ | ⟨l, ls⟩ <;> rcases us with _ | ⟨u, us⟩ <;> rcases vs with _ | ⟨v, vs⟩ <;>
      simp only [Bnd] at h
    · simp [ibpDot, dotP]
    · obtain ⟨hl, hu, hr⟩ := h
      obtain ⟨p1, p2⟩ := pert_bounds (a := a) (hd j) hl hu
      obtain ⟨r1, r2⟩ := ih ls us vs (j + 1) hr
      simp only [ibpDot, dotP]
      push_cast
      constructor <;> linarith

def ibpRows : List (List ℚ) → List ℚ → ℚ → List ℚ → List ℚ → List ℚ × List ℚ
  | r :: W, c :: b, τ, ls, us =>
    (((ibpDot r ls us τ).1 + c - τ) :: (ibpRows W b τ ls us).1,
     ((ibpDot r ls us τ).2 + c + τ) :: (ibpRows W b τ ls us).2)
  | _, _, _, _, _ => ([], [])

theorem rows_sound (τ : ℚ) (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ)
    (hW : ∀ i j, |dW i j| ≤ (τ : ℝ)) (hb : ∀ i, |db i| ≤ (τ : ℝ))
    (ls us : List ℚ) (vs : List ℝ) (hv : Bnd ls us vs) :
    ∀ (W : List (List ℚ)) (b : List ℚ) (i : ℕ),
      Bnd (ibpRows W b τ ls us).1 (ibpRows W b τ ls us).2 (rowsP W b dW db vs i) := by
  intro W
  induction W with
  | nil => intro b i; simp [ibpRows, rowsP, Bnd]
  | cons r W ih =>
    intro b i
    rcases b with _ | ⟨c, b⟩
    · simp [ibpRows, rowsP, Bnd]
    · obtain ⟨p1, p2⟩ := dot_sound τ (dW i) (hW i) r ls us vs 0 hv
      obtain ⟨q1, q2⟩ := abs_le.mp (hb i)
      simp only [ibpRows, rowsP, Bnd]
      push_cast
      exact ⟨by linarith, by linarith, ih b (i + 1)⟩

theorem relu_cast (q : ℚ) : ((relu q : ℚ) : ℝ) = relu (q : ℝ) := by
  unfold relu; push_cast; rfl

theorem bnd_relu : ∀ (ls us : List ℚ) (vs : List ℝ), Bnd ls us vs →
    Bnd (ls.map relu) (us.map relu) (vs.map relu) := by
  intro ls
  induction ls with
  | nil =>
    intro us vs h
    rcases us with _ | ⟨u, us⟩ <;> rcases vs with _ | ⟨v, vs⟩ <;> simp_all [Bnd]
  | cons l ls ih =>
    intro us vs h
    rcases us with _ | ⟨u, us⟩ <;> rcases vs with _ | ⟨v, vs⟩ <;> simp only [Bnd] at h
    obtain ⟨hl, hu, hr⟩ := h
    simp only [List.map, Bnd, relu_cast]
    refine ⟨?_, ?_, ih us vs hr⟩
    · unfold relu; exact max_le_max hl le_rfl
    · unfold relu; exact max_le_max hu le_rfl

def ibpHidden : List Layer → ℚ → List ℚ → List ℚ → List ℚ × List ℚ
  | L :: Ls, τ, ls, us =>
    ibpHidden Ls τ ((ibpRows L.W L.b τ ls us).1.map relu) ((ibpRows L.W L.b τ ls us).2.map relu)
  | [], _, ls, us => (ls, us)

theorem hidden_sound (τ : ℚ) (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (h : Within (τ : ℝ) dW db) :
    ∀ (Ls : List Layer) (ls us : List ℚ) (vs : List ℝ) (l : ℕ), Bnd ls us vs →
      Bnd (ibpHidden Ls τ ls us).1 (ibpHidden Ls τ ls us).2 (hiddenP Ls dW db vs l) := by
  intro Ls
  induction Ls with
  | nil => intro ls us vs l hv; simpa [ibpHidden, hiddenP] using hv
  | cons L Ls ih =>
    intro ls us vs l hv
    simp only [ibpHidden, hiddenP]
    apply ih
    exact bnd_relu _ _ _ (rows_sound τ (dW l) (db l) (h.1 l) (h.2 l) ls us vs hv L.W L.b 0)

def ibpNet (N : Net) (τ : ℚ) (x : List ℚ) : List ℚ × List ℚ :=
  ibpRows N.out.W N.out.b τ (ibpHidden N.hidden τ x x).1 (ibpHidden N.hidden τ x x).2

theorem bnd_self : ∀ x : List ℚ, Bnd x x (x.map (fun q : ℚ => (q : ℝ))) := by
  intro x
  induction x with
  | nil => simp [Bnd]
  | cons q x ih => exact ⟨le_rfl, le_rfl, ih⟩

theorem net_sound (N : Net) (τ : ℚ) (x : List ℚ) (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ)
    (h : Within (τ : ℝ) dW db) :
    Bnd (ibpNet N τ x).1 (ibpNet N τ x).2 (N.evalP dW db (x.map (fun q : ℚ => (q : ℝ)))) := by
  unfold ibpNet Net.evalP
  exact rows_sound τ (dW N.hidden.length) (db N.hidden.length) (h.1 _) (h.2 _) _ _ _
    (hidden_sound τ dW db h N.hidden x x _ 0 (bnd_self x)) _ _ 0

/-! ### The task and the certificate -/

/-- All 0/1 vectors of length n. -/
def boolVecs : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (boolVecs n).map (List.cons 0) ++ (boolVecs n).map (List.cons 1)

def label (xs : List ℕ) : Bool := xs.sum % 3 == 0

def toQ (xs : List ℕ) : List ℚ := xs.map (fun n : ℕ => (n : ℚ))

def out1 : List ℝ → ℝ
  | v :: _ => v
  | [] => 0

/-- The certified statement: every weight setting within τ, every input, correct sign. -/
def SpecN (n : ℕ) (N : Net) (τ : ℚ) : Prop :=
  ∀ dW db, Within (τ : ℝ) dW db → ∀ xs ∈ boolVecs n,
    if label xs then 0 < out1 (N.evalP dW db ((toQ xs).map (fun q : ℚ => (q : ℝ))))
    else out1 (N.evalP dW db ((toQ xs).map (fun q : ℚ => (q : ℝ)))) < 0

def checkOne (N : Net) (τ : ℚ) (xs : List ℕ) : Bool :=
  match (ibpNet N τ (toQ xs)).1, (ibpNet N τ (toQ xs)).2 with
  | l :: _, u :: _ => if label xs then decide (0 < l) else decide (u < 0)
  | _, _ => false

def checkN (n : ℕ) (N : Net) (τ : ℚ) : Bool := (boolVecs n).all (checkOne N τ)

theorem cert (n : ℕ) (N : Net) (τ : ℚ) (hc : checkN n N τ = true) : SpecN n N τ := by
  intro dW db h xs hx
  have h1 : checkOne N τ xs = true := List.all_eq_true.mp hc xs hx
  have hb := net_sound N τ (toQ xs) dW db h
  unfold checkOne at h1
  revert hb h1
  generalize (ibpNet N τ (toQ xs)).1 = L
  generalize (ibpNet N τ (toQ xs)).2 = U
  generalize N.evalP dW db ((toQ xs).map (fun q : ℚ => (q : ℝ))) = V
  intro h1 hb
  rcases L with _ | ⟨l, L⟩
  · simp at h1
  rcases U with _ | ⟨u, U⟩
  · simp at h1
  rcases V with _ | ⟨v, V⟩
  · simp [Bnd] at hb
  obtain ⟨hl, hu, _⟩ := hb
  simp only at h1
  show (if label xs = true then 0 < v else v < 0)
  split_ifs at h1 ⊢ with hc
  · have h2 : 0 < l := by simpa using h1
    have : (0 : ℝ) < ((l : ℚ) : ℝ) := by exact_mod_cast h2
    linarith
  · have h2 : u < 0 := by simpa using h1
    have : ((u : ℚ) : ℝ) < 0 := by exact_mod_cast h2
    linarith

/-! ### Shared-evaluation versions (each recursive pair computed once), proved equal -/

def ibpDotF : List ℚ → List ℚ → List ℚ → ℚ → ℚ × ℚ
  | a :: w, l :: ls, u :: us, τ =>
    match ibpDotF w ls us τ with
    | (L, U) => (pLo a τ l u + L, pHi a τ l u + U)
  | _, _, _, _ => (0, 0)

theorem ibpDotF_eq : ∀ (w ls us : List ℚ) (τ : ℚ), ibpDotF w ls us τ = ibpDot w ls us τ := by
  intro w
  induction w with
  | nil => intro ls us τ; simp [ibpDotF, ibpDot]
  | cons a w ih =>
    intro ls us τ
    rcases ls with _ | ⟨l, ls⟩ <;> rcases us with _ | ⟨u, us⟩
    · simp [ibpDotF, ibpDot]
    · simp [ibpDotF, ibpDot]
    · simp [ibpDotF, ibpDot]
    · simp only [ibpDotF, ibpDot, ih]

def ibpRowsF : List (List ℚ) → List ℚ → ℚ → List ℚ → List ℚ → List ℚ × List ℚ
  | r :: W, c :: b, τ, ls, us =>
    match ibpDotF r ls us τ, ibpRowsF W b τ ls us with
    | (L, U), (Ls, Us) => ((L + c - τ) :: Ls, (U + c + τ) :: Us)
  | _, _, _, _, _ => ([], [])

theorem ibpRowsF_eq (τ : ℚ) (ls us : List ℚ) :
    ∀ (W : List (List ℚ)) (b : List ℚ), ibpRowsF W b τ ls us = ibpRows W b τ ls us := by
  intro W
  induction W with
  | nil => intro b; simp [ibpRowsF, ibpRows]
  | cons r W ih =>
    intro b
    rcases b with _ | ⟨c, b⟩
    · simp [ibpRowsF, ibpRows]
    · simp only [ibpRowsF, ibpRows, ibpDotF_eq, ih]

def ibpHiddenF : List Layer → ℚ → List ℚ → List ℚ → List ℚ × List ℚ
  | L :: Ls, τ, ls, us =>
    match ibpRowsF L.W L.b τ ls us with
    | (a, b) => ibpHiddenF Ls τ (a.map relu) (b.map relu)
  | [], _, ls, us => (ls, us)

theorem ibpHiddenF_eq (τ : ℚ) :
    ∀ (Ls : List Layer) (ls us : List ℚ), ibpHiddenF Ls τ ls us = ibpHidden Ls τ ls us := by
  intro Ls
  induction Ls with
  | nil => intro ls us; rfl
  | cons L Ls ih =>
    intro ls us
    simp only [ibpHiddenF, ibpHidden, ibpRowsF_eq]
    generalize ibpRows L.W L.b τ ls us = p
    rcases p with ⟨a, b⟩
    exact ih _ _

def ibpNetF (N : Net) (τ : ℚ) (x : List ℚ) : List ℚ × List ℚ :=
  match ibpHiddenF N.hidden τ x x with
  | (a, b) => ibpRowsF N.out.W N.out.b τ a b

theorem ibpNetF_eq (N : Net) (τ : ℚ) (x : List ℚ) : ibpNetF N τ x = ibpNet N τ x := by
  unfold ibpNetF ibpNet
  rw [ibpHiddenF_eq]
  generalize ibpHidden N.hidden τ x x = p
  rcases p with ⟨a, b⟩
  exact ibpRowsF_eq τ a b _ _

def checkOneF (N : Net) (τ : ℚ) (xs : List ℕ) : Bool :=
  match ibpNetF N τ (toQ xs) with
  | (l :: _, u :: _) => if label xs then decide (0 < l) else decide (u < 0)
  | _ => false

theorem checkOneF_eq (N : Net) (τ : ℚ) (xs : List ℕ) : checkOneF N τ xs = checkOne N τ xs := by
  unfold checkOneF checkOne
  rw [ibpNetF_eq]
  generalize ibpNet N τ (toQ xs) = p
  rcases p with ⟨L, U⟩
  rcases L with _ | ⟨l, L⟩ <;> rcases U with _ | ⟨u, U⟩ <;> rfl

def checkNF (n : ℕ) (N : Net) (τ : ℚ) : Bool := (boolVecs n).all (checkOneF N τ)

theorem certF (n : ℕ) (N : Net) (τ : ℚ) (hc : checkNF n N τ = true) : SpecN n N τ := by
  apply cert n N τ
  have : checkNF n N τ = checkN n N τ := by
    unfold checkNF checkN
    congr 1
    funext xs
    exact checkOneF_eq N τ xs
  rw [← this]; exact hc

end Bridge
