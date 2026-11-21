/-
Lane 4, rung 7 kit module, assembled by tools/r7_assemble.py from kit case k2
(runs/r7-kit/k2): statements by the lane, proofs by a Sonnet doctor, checked by tools/check.py.
-/
import Lane4.R7Cert

namespace Lane4.R7K2
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert

/-- The standing hypotheses on the rounding model. -/
structure Ctx (u η M : ℝ) (fl : ℝ → ℝ) : Prop where
  rnd : Rnd u η M fl
  u0 : 0 ≤ u
  u1 : u ≤ 1 / 2 ^ 24
  h0 : 0 ≤ η
  h1 : η ≤ 1 / 2 ^ 149
  M1 : 2 ^ 40 ≤ M

/-- The real `x` lies in the interval `v` = (centre, radius). -/
def InIV (x : ℝ) (v : IV) : Prop := |x - ((v.1 : ℚ) : ℝ)| ≤ ((v.2 : ℚ) : ℝ)

/-- Entry by entry, with equal lengths. -/
def InIVs (x : List ℝ) (v : List IV) : Prop :=
  x.length = v.length ∧ ∀ k, k < x.length → InIV (x.getD k 0) (v.getD k (0, 0))

/-- Every interval has a non-negative radius and reaches at most `B` from 0. -/
def Bdd (B : ℚ) (v : List IV) : Prop := ∀ a ∈ v, 0 ≤ a.2 ∧ qabs a.1 + a.2 ≤ B

/-- A stored embedding row lies in `embIV`. -/
def EmbSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (row : List ℚ) (d : ℕ → ℝ), (∀ k, |d k| ≤ (δ : ℝ)) → smallQ row = true →
    InIVs (aswRow fl row d 0) (embIV δ row) ∧ Bdd 16 (embIV δ row)

/-- A stored-weight dot product lies in `dotIV`. -/
def DotSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (r : List ℚ) (x : List ℝ) (xv : List IV) (d : ℕ → ℝ), (∀ k, |d k| ≤ (δ : ℝ)) →
  r.length = x.length → r.length ≤ 32 → smallQ r = true → InIVs x xv → Bdd 16 xv →
    InIV (ardot fl r x d 0 0) (dotIV δ r xv) ∧ 0 ≤ (dotIV δ r xv).2

/-- A stored matrix applied to a vector lies in `matIV`. -/
def MatSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (A : List (List ℚ)) (x : List ℝ) (xv : List IV) (d : ℕ → ℕ → ℝ),
  (∀ i k, |d i k| ≤ (δ : ℝ)) → (∀ r ∈ A, r.length = x.length) → x.length ≤ 32 →
  smallM A = true → InIVs x xv → Bdd 16 xv →
    InIVs (armat fl A x d 0) (matIV δ A xv) ∧ ∀ a ∈ matIV δ A xv, 0 ≤ a.2

/-- A stored affine map lies in `affIV`, when every output passes the magnitude guard. -/
def AffSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (A : List (List ℚ)) (b : List ℚ) (x : List ℝ) (xv : List IV) (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ),
  (∀ i k, |dW i k| ≤ (δ : ℝ)) → (∀ i, |db i| ≤ (δ : ℝ)) →
  (∀ r ∈ A, r.length = x.length) → x.length ≤ 32 →
  smallM A = true → smallQ b = true → InIVs x xv → Bdd 16 xv →
  (affIV δ A b xv).all small = true →
    InIVs (araffine fl A b x dW db 0) (affIV δ A b xv) ∧ Bdd 15 (affIV δ A b xv)

/-- A rounded entrywise sum lies in `addIV`, when every output passes the magnitude guard. -/
def AddSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl →
  ∀ (a b : List ℝ) (av bv : List IV), InIVs a av → InIVs b bv →
  (∀ v ∈ av, 0 ≤ v.2) → (∀ v ∈ bv, 0 ≤ v.2) → (addIV av bv).all small = true →
    InIVs (radd fl a b) (addIV av bv) ∧ Bdd 15 (addIV av bv)

/-- ReLU maps an interval into its clamp. -/
def ReluSound : Prop :=
  ∀ (x : List ℝ) (xv : List IV), InIVs x xv → Bdd 15 xv →
    InIVs (x.map Lane4.relu) (xv.map reluIV) ∧ Bdd 15 (xv.map reluIV)

/-- A decided gate: the gate neuron is exactly 0 if and only if the checker says "candidate". -/
def GateSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (h : AHead) (x : List ℝ) (xv : List IV) (dg : ℕ → ℝ) (dgb : ℝ),
  (∀ k, |dg k| ≤ (δ : ℝ)) → |dgb| ≤ (δ : ℝ) →
  h.g.length = x.length → h.g.length ≤ 32 → smallQ h.g = true → smallQ [h.gb] = true →
  InIVs x xv → Bdd 16 xv →
  ∀ b : Bool, gateDec δ h xv = some b → (h.gate fl dg dgb x = 0 ↔ b = true)

/-- The content score of a query state against a key state lies in `scoreIV`, and is at most
1024 in size, when `scoreOK` holds. -/
def ScoreSound : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (h : AHead) (xq xt : List ℝ) (xqv xtv : List IV) (dA : ℕ → ℕ → ℝ),
  (∀ i k, |dA i k| ≤ (δ : ℝ)) →
  (∀ r ∈ h.A, r.length = xt.length) → xt.length ≤ 32 → h.A.length = xq.length → xq.length ≤ 32 →
  smallM h.A = true → InIVs xq xqv → Bdd 16 xqv → InIVs xt xtv → Bdd 16 xtv →
  scoreOK δ h xqv xtv = true →
    InIV (pdot fl xq (armat fl h.A xt dA 0) 0) (scoreIV δ h xqv xtv)
    ∧ 0 ≤ (scoreIV δ h xqv xtv).2
    ∧ |pdot fl xq (armat fl h.A xt dA 0) 0| ≤ 1024

end Lane4.R7K2


set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Lane4.R7K2
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert

/-! ### qabs and maxAbs -/

theorem zqabs_cast (a : ℚ) : ((qabs a : ℚ) : ℝ) = |(a : ℝ)| := by
  unfold qabs
  split_ifs with h
  · have h' : (a : ℝ) < 0 := by exact_mod_cast h
    simp [abs_of_neg h']
  · have h' : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast not_lt.mp h
    simp [abs_of_nonneg h']

theorem zqabs_nonneg (a : ℚ) : 0 ≤ qabs a := by
  unfold qabs
  split_ifs with h
  · linarith
  · exact not_lt.mp h

theorem zqabs_of_nonneg {a : ℚ} (h : 0 ≤ a) : qabs a = a := by
  unfold qabs
  rw [if_neg (not_lt.mpr h)]

theorem zle_qabs (a : ℚ) : a ≤ qabs a := by
  unfold qabs
  split_ifs with h
  · linarith
  · exact le_refl a

theorem zmaxAbs_aux (l : List ℚ) : ∀ m : ℚ, m ≤ l.foldl (fun m a => max m (qabs a)) m ∧
    ∀ a ∈ l, qabs a ≤ l.foldl (fun m a => max m (qabs a)) m := by
  induction l with
  | nil => intro m; simp
  | cons b l ih =>
    intro m
    obtain ⟨h1, h2⟩ := ih (max m (qabs b))
    simp only [List.foldl_cons]
    refine ⟨le_trans (le_max_left _ _) h1, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with h3 | ha'
    · rw [h3]
      exact le_trans (le_max_right _ _) h1
    · exact h2 a ha'

theorem zmaxAbs_nonneg (l : List ℚ) : 0 ≤ maxAbs l := (zmaxAbs_aux l 0).1

theorem zle_maxAbs {l : List ℚ} {a : ℚ} (h : a ∈ l) : qabs a ≤ maxAbs l := (zmaxAbs_aux l 0).2 a h

theorem zfoldl_le_aux (B : ℚ) (l : List ℚ) : ∀ m : ℚ, m ≤ B → (∀ a ∈ l, qabs a ≤ B) →
    l.foldl (fun m a => max m (qabs a)) m ≤ B := by
  induction l with
  | nil => intro m hm _; simpa using hm
  | cons b l ih =>
    intro m hm hl
    simp only [List.foldl_cons]
    exact ih _ (max_le hm (hl b (by simp))) (fun a ha => hl a (by simp [ha]))

theorem zmaxAbs_le {l : List ℚ} {B : ℚ} (hB : 0 ≤ B) (h : ∀ a ∈ l, qabs a ≤ B) : maxAbs l ≤ B :=
  zfoldl_le_aux B l 0 hB h

theorem zsmallQ_le {l : List ℚ} (h : smallQ l = true) : maxAbs l ≤ 15 := by
  unfold smallQ at h
  exact of_decide_eq_true h

theorem zsmallQ_mem {l : List ℚ} (h : smallQ l = true) : ∀ a ∈ l, qabs a ≤ 15 :=
  fun a ha => le_trans (zle_maxAbs ha) (zsmallQ_le h)

theorem zsmallM_mem {A : List (List ℚ)} (h : smallM A = true) : ∀ r ∈ A, smallQ r = true := by
  have h' : A.all smallQ = true := h
  exact List.all_eq_true.mp h'

theorem zsmall_le {v : IV} (h : small v = true) : qabs v.1 + v.2 ≤ 15 := by
  unfold small at h
  exact of_decide_eq_true h

theorem zbdd_bounds {B : ℚ} (hB0 : 0 ≤ B) {v : List IV} (h : Bdd B v) :
    maxAbs (v.map Prod.fst) ≤ B ∧ maxAbs (v.map Prod.snd) ≤ B := by
  constructor
  · apply zmaxAbs_le hB0
    intro a ha
    obtain ⟨b, hb, hba⟩ := List.mem_map.mp ha
    rw [← hba]
    have h1 := h b hb
    have h2 := zqabs_nonneg b.2
    linarith [h1.1, h1.2]
  · apply zmaxAbs_le hB0
    intro a ha
    obtain ⟨b, hb, hba⟩ := List.mem_map.mp ha
    rw [← hba]
    have h1 := h b hb
    have h2 := zqabs_nonneg b.1
    rw [zqabs_of_nonneg h1.1]
    linarith [h1.1, h1.2]

/-! ### rnd, e0 -/

theorem zrnd_real : ((rnd : ℚ) : ℝ) = 1 / 1048576 := by
  unfold rnd
  norm_num

theorem zrnd_pos : (0 : ℚ) < rnd := by
  unfold rnd
  norm_num

theorem zrnd_small : rnd ≤ 1 / 1000 := by
  unfold rnd
  norm_num

theorem ze0_real (δ : ℚ) : ((e0 δ : ℚ) : ℝ) = (δ : ℝ) + 1 / 1048576 := by
  unfold e0
  push_cast
  rw [zrnd_real]

theorem ze0_nonneg {δ : ℚ} (hδ : 0 ≤ δ) : 0 ≤ e0 δ := by
  unfold e0
  have := zrnd_pos
  linarith

theorem zhalf (δ : ℚ) (h : δ ≤ 1 / 2) : (δ : ℝ) ≤ 1 / 2 := by
  have h2 : ((δ : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr h
  have h3 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
  linarith

/-! ### getD -/

theorem zgetD_map' {α β : Type} (f : α → β) (d : α) :
    ∀ (l : List α) (k : ℕ), k < l.length → (l.map f).getD k (f d) = f (l.getD k d)
  | [], k, h => by simp at h
  | a :: l, 0, _ => by simp
  | a :: l, k + 1, h => by
      simp only [List.map_cons, List.getD_cons_succ]
      exact zgetD_map' f d l k (by simpa using h)

theorem zgetD_map'' {α β : Type} (f : α → β) (d : α) (d' : β) (hd : d' = f d) (l : List α) (k : ℕ)
    (hk : k < l.length) : (l.map f).getD k d' = f (l.getD k d) := by
  subst hd
  exact zgetD_map' f d l k hk

theorem zgetD_mem' {α : Type} (d : α) :
    ∀ (l : List α) (k : ℕ), k < l.length → l.getD k d ∈ l
  | [], k, h => by simp at h
  | a :: l, 0, _ => by simp
  | a :: l, k + 1, h => by
      simp only [List.getD_cons_succ]
      exact List.mem_cons_of_mem _ (zgetD_mem' d l k (by simpa using h))

/-! ### InIV / InIVs -/

theorem zinIV_iff {x : ℝ} {v : IV} : InIV x v ↔ |x - ((v.1 : ℚ) : ℝ)| ≤ ((v.2 : ℚ) : ℝ) := Iff.rfl

theorem zinIVs_len {x : List ℝ} {xv : List IV} (h : InIVs x xv) : x.length = xv.length := by
  obtain ⟨hl, _⟩ := h
  exact hl

theorem zinIVs_nil : InIVs ([] : List ℝ) ([] : List IV) := by
  unfold InIVs
  exact ⟨rfl, fun k hk => absurd hk (by simp)⟩

theorem zinIVs_nil_left {vs : List IV} (h : InIVs ([] : List ℝ) vs) : vs = [] := by
  obtain ⟨hl, _⟩ := h
  cases vs with
  | nil => rfl
  | cons v vs => simp at hl

theorem zinIVs_cons {a : ℝ} {as : List ℝ} {v : IV} {vs : List IV} (h1 : InIV a v)
    (h2 : InIVs as vs) : InIVs (a :: as) (v :: vs) := by
  obtain ⟨hl, hk⟩ := h2
  unfold InIVs
  refine ⟨by simp [hl], ?_⟩
  intro k hk'
  cases k with
  | zero => simpa using h1
  | succ k =>
    have := hk k (by simpa using hk')
    simpa using this

theorem zinIVs_cons_inv {a : ℝ} {as : List ℝ} {v : IV} {vs : List IV}
    (h : InIVs (a :: as) (v :: vs)) : InIV a v ∧ InIVs as vs := by
  obtain ⟨hl, hk⟩ := h
  refine ⟨?_, ?_⟩
  · have := hk 0 (by simp)
    simpa using this
  · unfold InIVs
    refine ⟨by simpa using hl, ?_⟩
    intro k hk'
    have := hk (k + 1) (by simpa using hk')
    simpa using this

theorem zabs_add_pair {a b p q e f : ℝ} (h1 : |a - p| ≤ e) (h2 : |b - q| ≤ f) :
    |(a + b) - (p + q)| ≤ e + f := by
  obtain ⟨a1, a2⟩ := abs_le.mp h1
  obtain ⟨b1, b2⟩ := abs_le.mp h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ### casts of the rational evaluator -/

theorem zdotC_nl (xv : List IV) : dotC [] xv = 0 := by cases xv <;> rfl
theorem zdotC_nr (r : List ℚ) : dotC r [] = 0 := by cases r <;> rfl
theorem zwErrQ_nl (δ : ℚ) (xv : List IV) : wErrQ δ [] xv = 0 := by cases xv <;> rfl
theorem zwErrQ_nr (δ : ℚ) (r : List ℚ) : wErrQ δ r [] = 0 := by cases r <;> rfl
theorem zwErr_nl (δ : ℝ) (es Xs : List ℝ) : wErr δ [] es Xs = 0 := by
  cases es <;> cases Xs <;> rfl
theorem zwErr_nr (δ : ℝ) (r : List ℚ) : wErr δ r [] [] = 0 := by cases r <;> rfl
theorem zwErr_cons (δ : ℝ) (a : ℚ) (r : List ℚ) (e X : ℝ) (es Xs : List ℝ) :
    wErr δ (a :: r) (e :: es) (X :: Xs) = |(a : ℝ)| * e + δ * (X + e) + wErr δ r es Xs := rfl

theorem zdotC_cast (r : List ℚ) : ∀ (xv : List IV),
    ((dotC r xv : ℚ) : ℝ) = dotQ r (xv.map (fun a => ((a.1 : ℚ) : ℝ))) := by
  induction r with
  | nil => intro xv; simp [zdotC_nl, dotQ]
  | cons a r ih =>
    intro xv
    cases xv with
    | nil => simp [zdotC_nr, dotQ]
    | cons x xs =>
      have e1 : dotC (a :: r) (x :: xs) = a * x.1 + dotC r xs := rfl
      have e2 : dotQ (a :: r) (((x.1 : ℚ) : ℝ) :: xs.map (fun a => ((a.1 : ℚ) : ℝ)))
          = (a : ℝ) * ((x.1 : ℚ) : ℝ) + dotQ r (xs.map (fun a => ((a.1 : ℚ) : ℝ))) := by
        simp [dotQ]
      simp only [List.map_cons]
      rw [e1, e2]
      push_cast
      rw [ih xs]

theorem zdotC_cast_R : ∀ (xq y : List IV),
    ((dotC (xq.map Prod.fst) y : ℚ) : ℝ) =
      dotR (xq.map (fun a => ((a.1 : ℚ) : ℝ))) (y.map (fun a => ((a.1 : ℚ) : ℝ))) := by
  intro xq
  induction xq with
  | nil => intro y; simp [zdotC_nl, dotR]
  | cons a xs ih =>
    intro y
    cases y with
    | nil => simp [zdotC_nr, dotR]
    | cons w ys =>
      have e1 : dotC (a.1 :: xs.map Prod.fst) (w :: ys) = a.1 * w.1 + dotC (xs.map Prod.fst) ys := rfl
      have e2 : dotR (((a.1 : ℚ) : ℝ) :: xs.map (fun a => ((a.1 : ℚ) : ℝ)))
            (((w.1 : ℚ) : ℝ) :: ys.map (fun a => ((a.1 : ℚ) : ℝ)))
          = ((a.1 : ℚ) : ℝ) * ((w.1 : ℚ) : ℝ)
            + dotR (xs.map (fun a => ((a.1 : ℚ) : ℝ))) (ys.map (fun a => ((a.1 : ℚ) : ℝ))) := by
        simp [dotR]
      simp only [List.map_cons]
      rw [e1, e2]
      push_cast
      rw [ih ys]

theorem zwErrQ_cast (δ : ℚ) (r : List ℚ) : ∀ (xv : List IV),
    ((wErrQ δ r xv : ℚ) : ℝ) = wErr (δ : ℝ) r (xv.map (fun a => ((a.2 : ℚ) : ℝ)))
      (xv.map (fun a => |((a.1 : ℚ) : ℝ)|)) := by
  induction r with
  | nil => intro xv; simp [zwErrQ_nl, zwErr_nl]
  | cons a r ih =>
    intro xv
    cases xv with
    | nil => simp [zwErrQ_nr, zwErr_nr]
    | cons x xs =>
      have e1 : wErrQ δ (a :: r) (x :: xs)
          = qabs a * x.2 + δ * (qabs x.1 + x.2) + wErrQ δ r xs := rfl
      simp only [List.map_cons]
      rw [e1, zwErr_cons]
      push_cast
      simp only [zqabs_cast]
      linarith [ih xs]

theorem zwErrQ_nonneg {δ : ℚ} (hδ : 0 ≤ δ) (r : List ℚ) :
    ∀ xv : List IV, (∀ a ∈ xv, 0 ≤ a.2) → 0 ≤ wErrQ δ r xv := by
  induction r with
  | nil => intro xv _; rw [zwErrQ_nl]
  | cons a r ih =>
    intro xv hx
    cases xv with
    | nil => rw [zwErrQ_nr]
    | cons x xs =>
      have h1 := hx x (by simp)
      have h2 := ih xs (fun b hb => hx b (List.mem_cons_of_mem _ hb))
      have e1 : wErrQ δ (a :: r) (x :: xs)
          = qabs a * x.2 + δ * (qabs x.1 + x.2) + wErrQ δ r xs := rfl
      rw [e1]
      have q1 := zqabs_nonneg a
      have q2 := zqabs_nonneg x.1
      have t1 : 0 ≤ qabs a * x.2 := mul_nonneg q1 h1
      have t2 : 0 ≤ δ * (qabs x.1 + x.2) := mul_nonneg hδ (by linarith)
      linarith

theorem zdot_nonneg {δ : ℚ} (hδ : 0 ≤ δ) (r : List ℚ) (xv : List IV) (h : ∀ a ∈ xv, 0 ≤ a.2) :
    0 ≤ (dotIV δ r xv).2 := by
  have h1 := zwErrQ_nonneg hδ r xv h
  have h2 := zmaxAbs_nonneg r
  have h3 := zmaxAbs_nonneg (xv.map Prod.fst)
  have h4 := zmaxAbs_nonneg (xv.map Prod.snd)
  have h5 : (0 : ℚ) ≤ (r.length : ℚ) * (maxAbs r + 1) *
      (maxAbs (xv.map Prod.fst) + maxAbs (xv.map Prod.snd) + 1) / 2 ^ 16 :=
    div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by linarith))
      (by norm_num)
  have h6 : (0 : ℚ) ≤ 1 / 2 ^ 100 := by norm_num
  show 0 ≤ wErrQ δ r xv + (r.length : ℚ) * (maxAbs r + 1) *
      (maxAbs (xv.map Prod.fst) + maxAbs (xv.map Prod.snd) + 1) / 2 ^ 16 + 1 / 2 ^ 100
  linarith

/-! ### Close and CloseL from InIVs -/

theorem zclosel_of_iv {x : List ℝ} {xv : List IV} (h : InIVs x xv) :
    CloseL x (xv.map (fun a => ((a.1 : ℚ) : ℝ))) (xv.map (fun a => ((a.2 : ℚ) : ℝ)))
      (xv.map (fun a => |((a.1 : ℚ) : ℝ)|)) := by
  obtain ⟨hl, hk⟩ := h
  unfold CloseL
  refine ⟨by simp [hl], by simp [hl], by simp [hl], ?_⟩
  intro k hk'
  have hk2 : k < xv.length := by rw [← hl]; exact hk'
  have h1 := zinIV_iff.mp (hk k hk')
  have e1 := zgetD_map'' (fun a : IV => ((a.1 : ℚ) : ℝ)) (0, 0) 0 (by simp) xv k hk2
  have e2 := zgetD_map'' (fun a : IV => ((a.2 : ℚ) : ℝ)) (0, 0) 0 (by simp) xv k hk2
  have e3 := zgetD_map'' (fun a : IV => |((a.1 : ℚ) : ℝ)|) (0, 0) 0 (by simp) xv k hk2
  rw [e1, e2, e3]
  exact ⟨h1, le_refl _⟩

theorem zclose_of_iv {x : List ℝ} {xv : List IV} (hx : InIVs x xv) (hnn : ∀ a ∈ xv, 0 ≤ a.2) :
    Close x (xv.map (fun a => ((a.1 : ℚ) : ℝ))) ((maxAbs (xv.map Prod.snd) : ℚ) : ℝ)
      ((maxAbs (xv.map Prod.fst) : ℚ) : ℝ) := by
  obtain ⟨hl, hk⟩ := hx
  unfold Close
  refine ⟨by simp [hl], ?_⟩
  intro k hk'
  have hk2 : k < xv.length := by rw [← hl]; exact hk'
  have h1 := zinIV_iff.mp (hk k hk')
  have e1 := zgetD_map'' (fun a : IV => ((a.1 : ℚ) : ℝ)) (0, 0) 0 (by simp) xv k hk2
  rw [e1]
  have hm := zgetD_mem' ((0, 0) : IV) xv k hk2
  constructor
  · have h2 := zle_maxAbs (List.mem_map.mpr ⟨_, hm, rfl⟩ :
      (xv.getD k (0, 0)).2 ∈ xv.map Prod.snd)
    rw [zqabs_of_nonneg (hnn _ hm)] at h2
    have h3 : (((xv.getD k (0, 0)).2 : ℚ) : ℝ) ≤ ((maxAbs (xv.map Prod.snd) : ℚ) : ℝ) := by
      exact_mod_cast h2
    exact le_trans h1 h3
  · have h2 := zle_maxAbs (List.mem_map.mpr ⟨_, hm, rfl⟩ :
      (xv.getD k (0, 0)).1 ∈ xv.map Prod.fst)
    have h3 : ((qabs (xv.getD k (0, 0)).1 : ℚ) : ℝ) ≤ ((maxAbs (xv.map Prod.fst) : ℚ) : ℝ) := by
      exact_mod_cast h2
    rwa [zqabs_cast] at h3

/-! ### rounding -/

theorem zrnd_step {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) {y t e : ℝ}
    (hy : |y - t| ≤ e) (hb : |y| ≤ 15) : |fl y - t| ≤ e + 1 / 1048576 := by
  have hM : (15 : ℝ) ≤ M := by
    have h1 := hC.M1
    have h40 : (15 : ℝ) ≤ 2 ^ 40 := by norm_num
    linarith
  have h1 := hC.rnd.near hC.u0 hy hb hM
  have hu : u ≤ 1 / 16777216 := le_trans hC.u1 (by norm_num)
  have hη : η ≤ 1 / 1000000000000 := le_trans hC.h1 (by norm_num)
  have h2 : u * 15 ≤ 1 / 16777216 * 15 := mul_le_mul_of_nonneg_right hu (by norm_num)
  linarith

theorem zround_step {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) {y : ℝ} {c e : ℚ}
    (hy : |y - (c : ℝ)| ≤ (e : ℝ)) (hs : qabs c + (e + rnd) ≤ 15) :
    |fl y - (c : ℝ)| ≤ ((e + rnd : ℚ) : ℝ) := by
  have h1 : ((qabs c : ℚ) : ℝ) + (((e : ℚ) : ℝ) + ((rnd : ℚ) : ℝ)) ≤ 15 := by
    exact_mod_cast hs
  rw [zqabs_cast, zrnd_real] at h1
  have h2 : |y| ≤ |(c : ℝ)| + (e : ℝ) := by
    have := abs_sub_abs_le_abs_sub y (c : ℝ)
    linarith
  have h3 := zrnd_step hC hy (by linarith)
  have h4 : ((e + rnd : ℚ) : ℝ) = (e : ℝ) + 1 / 1048576 := by
    push_cast
    rw [zrnd_real]
  rw [h4]
  exact h3

theorem zasw_e0 {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) {δ : ℚ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2) {c : ℚ} (hc : qabs c ≤ 15) {d : ℝ} (hd : |d| ≤ (δ : ℝ)) :
    |asw fl c d - (c : ℝ)| ≤ ((e0 δ : ℚ) : ℝ) := by
  have hcR : |(c : ℝ)| ≤ 15 := by
    have h : ((qabs c : ℚ) : ℝ) ≤ 15 := by exact_mod_cast hc
    rwa [zqabs_cast] at h
  have hδR : (δ : ℝ) ≤ 1 / 2 := zhalf δ hδ1
  have hδ0R : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ0
  have hM : |(c : ℝ)| + (δ : ℝ) ≤ M := by
    have h1 := hC.M1
    have h40 : (16 : ℝ) ≤ 2 ^ 40 := by norm_num
    linarith
  have h := asw_near hC.rnd hC.u0 c hd hM
  have hu : u ≤ 1 / 16777216 := le_trans hC.u1 (by norm_num)
  have hη : η ≤ 1 / 1000000000000 := le_trans hC.h1 (by norm_num)
  have h2 : u * (|(c : ℝ)| + (δ : ℝ)) ≤ 1 / 16777216 * (31 / 2) :=
    mul_le_mul hu (by linarith) (add_nonneg (abs_nonneg _) hδ0R) (by norm_num)
  rw [ze0_real]
  linarith

theorem zlin_step {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) {δ : ℚ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2) {s : ℝ} {D : IV} {c : ℚ} {d : ℝ} (hin : InIV s D) (hc : qabs c ≤ 15)
    (hd : |d| ≤ (δ : ℝ)) :
    |(s + asw fl c d) - (((D.1 + c : ℚ)) : ℝ)| ≤ (((D.2 + e0 δ : ℚ)) : ℝ) := by
  have hasw := zasw_e0 hC hδ0 hδ1 hc hd
  have hin' := zinIV_iff.mp hin
  push_cast
  exact zabs_add_pair hin' hasw

/-! ### emb -/

theorem zemb_aux {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) {δ : ℚ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ (δ : ℝ)) :
    ∀ (row : List ℚ) (j : ℕ), (∀ a ∈ row, qabs a ≤ 15) →
      InIVs (aswRow fl row d j) (embIV δ row) := by
  intro row
  induction row with
  | nil => intro j _; exact zinIVs_nil
  | cons a row ih =>
    intro j hs
    have e1 : aswRow fl (a :: row) d j = asw fl a (d j) :: aswRow fl row d (j + 1) := rfl
    have e2 : embIV δ (a :: row) = (a, e0 δ) :: embIV δ row := rfl
    rw [e1, e2]
    exact zinIVs_cons (zasw_e0 hC hδ0 hδ1 (hs a (by simp)) (hd j))
      (ih (j + 1) (fun b hb => hs b (List.mem_cons_of_mem _ hb)))

theorem zemb_bdd {δ : ℚ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (row : List ℚ)
    (hs : ∀ a ∈ row, qabs a ≤ 15) : Bdd 16 (embIV δ row) := by
  intro v hv
  have hv' : v ∈ row.map (fun a => (a, e0 δ)) := hv
  obtain ⟨a, ha, hva⟩ := List.mem_map.mp hv'
  rw [← hva]
  have h1 : 0 ≤ e0 δ := ze0_nonneg hδ0
  have h2 : e0 δ ≤ 1 := by
    unfold e0
    have := zrnd_small
    linarith
  have h3 := hs a ha
  exact ⟨h1, by show qabs a + e0 δ ≤ 16; linarith⟩

theorem emb_sound : EmbSound := by
  intro u η M fl hC δ hδ0 hδ1 row d hd hsm
  have hs := zsmallQ_mem hsm
  exact ⟨zemb_aux hC hδ0 hδ1 d hd row 0 hs, zemb_bdd hδ0 hδ1 row hs⟩

/-! ### dot -/

theorem dot_sound : DotSound := by
  intro u η M fl hC δ hδ0 hδ1 r x xv d hd hrx hr32 hsm hx hB
  have hW : maxAbs r ≤ 15 := zsmallQ_le hsm
  have hlen : x.length = xv.length := zinIVs_len hx
  have hbd := zbdd_bounds (B := 16) (by norm_num) hB
  have hnn : ∀ a ∈ xv, 0 ≤ a.2 := fun a ha => (hB a ha).1
  have hCL := zclosel_of_iv hx
  have hδR0 : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ0
  have hδR1 : (δ : ℝ) ≤ 1 / 2 := zhalf δ hδ1
  have hM : (2 : ℝ) ^ 30 ≤ M := by
    have h1 := hC.M1
    have h2 : (2 : ℝ) ^ 30 ≤ 2 ^ 40 := by norm_num
    linarith
  have hWR : ((maxAbs r : ℚ) : ℝ) ≤ 15 := by exact_mod_cast hW
  have hXR : ((maxAbs (xv.map Prod.fst) : ℚ) : ℝ) ≤ 16 := by exact_mod_cast hbd.1
  have heR : ((maxAbs (xv.map Prod.snd) : ℚ) : ℝ) ≤ 16 := by exact_mod_cast hbd.2
  have hW0 : (0 : ℝ) ≤ ((maxAbs r : ℚ) : ℝ) := by exact_mod_cast zmaxAbs_nonneg r
  have hX0 : (0 : ℝ) ≤ ((maxAbs (xv.map Prod.fst) : ℚ) : ℝ) := by
    exact_mod_cast zmaxAbs_nonneg (xv.map Prod.fst)
  have he0 : (0 : ℝ) ≤ ((maxAbs (xv.map Prod.snd) : ℚ) : ℝ) := by
    exact_mod_cast zmaxAbs_nonneg (xv.map Prod.snd)
  have hT : (((maxAbs r : ℚ) : ℝ) + 1) * (((maxAbs (xv.map Prod.fst) : ℚ) : ℝ)
      + ((maxAbs (xv.map Prod.snd) : ℚ) : ℝ) + 1) ≤ 2 ^ 20 := by
    have h1 : (((maxAbs r : ℚ) : ℝ) + 1) * (((maxAbs (xv.map Prod.fst) : ℚ) : ℝ)
        + ((maxAbs (xv.map Prod.snd) : ℚ) : ℝ) + 1) ≤ 16 * 33 :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    have h2 : (16 : ℝ) * 33 ≤ 2 ^ 20 := by norm_num
    linarith
  have hk : ∀ k, k < x.length →
      (xv.map (fun a => ((a.2 : ℚ) : ℝ))).getD k 0 ≤ ((maxAbs (xv.map Prod.snd) : ℚ) : ℝ) ∧
      (xv.map (fun a => |((a.1 : ℚ) : ℝ)|)).getD k 0 ≤ ((maxAbs (xv.map Prod.fst) : ℚ) : ℝ) := by
    intro k hk'
    have hk2 : k < xv.length := by rw [← hlen]; exact hk'
    have e2 := zgetD_map'' (fun a : IV => ((a.2 : ℚ) : ℝ)) (0, 0) 0 (by simp) xv k hk2
    have e3 := zgetD_map'' (fun a : IV => |((a.1 : ℚ) : ℝ)|) (0, 0) 0 (by simp) xv k hk2
    rw [e2, e3]
    have hm := zgetD_mem' ((0, 0) : IV) xv k hk2
    obtain ⟨h1, h2⟩ := hB _ hm
    constructor
    · have h3 := zle_maxAbs (List.mem_map.mpr ⟨_, hm, rfl⟩ :
        (xv.getD k (0, 0)).2 ∈ xv.map Prod.snd)
      rw [zqabs_of_nonneg h1] at h3
      exact_mod_cast h3
    · have h3 := zle_maxAbs (List.mem_map.mpr ⟨_, hm, rfl⟩ :
        (xv.getD k (0, 0)).1 ∈ xv.map Prod.fst)
      have h4 : ((qabs (xv.getD k (0, 0)).1 : ℚ) : ℝ)
          ≤ ((maxAbs (xv.map Prod.fst) : ℚ) : ℝ) := by exact_mod_cast h3
      rwa [zqabs_cast] at h4
  have hrW : ∀ a ∈ r, |(a : ℝ)| ≤ ((maxAbs r : ℚ) : ℝ) := by
    intro a ha
    have h3 := zle_maxAbs ha
    have h4 : ((qabs a : ℚ) : ℝ) ≤ ((maxAbs r : ℚ) : ℝ) := by exact_mod_cast h3
    rwa [zqabs_cast] at h4
  have key := ardot_near_w u η M (δ : ℝ) fl hC.rnd hC.u0 hC.u1 hC.h0 hC.h1 hδR0
    (by linarith) r x
    (xv.map (fun a => ((a.1 : ℚ) : ℝ))) (xv.map (fun a => ((a.2 : ℚ) : ℝ)))
    (xv.map (fun a => |((a.1 : ℚ) : ℝ)|)) d
    ((maxAbs r : ℚ) : ℝ) ((maxAbs (xv.map Prod.fst) : ℚ) : ℝ)
    ((maxAbs (xv.map Prod.snd) : ℚ) : ℝ)
    hrx hr32 hCL hk hd hrW hW0 hX0 he0 hT hM
  obtain ⟨k1, _⟩ := key
  have hc1 : (((dotIV δ r xv).1 : ℚ) : ℝ) = dotQ r (xv.map (fun a => ((a.1 : ℚ) : ℝ))) :=
    zdotC_cast r xv
  have e := zwErrQ_cast δ r xv
  have hc2 : (((dotIV δ r xv).2 : ℚ) : ℝ) =
      wErr (δ : ℝ) r (xv.map (fun a => ((a.2 : ℚ) : ℝ))) (xv.map (fun a => |((a.1 : ℚ) : ℝ)|))
      + (r.length : ℝ) * (((maxAbs r : ℚ) : ℝ) + 1) * (((maxAbs (xv.map Prod.fst) : ℚ) : ℝ)
        + ((maxAbs (xv.map Prod.snd) : ℚ) : ℝ) + 1) / 2 ^ 16 + 1 / 2 ^ 100 := by
    simp only [dotIV]
    push_cast
    linarith [e]
  refine ⟨?_, zdot_nonneg hδ0 r xv hnn⟩
  rw [zinIV_iff, hc1, hc2]
  first | exact k1 | linarith [k1]

/-! ### mat -/

theorem zmat_aux {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) {δ : ℚ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2) {x : List ℝ} {xv : List IV} (hx32 : x.length ≤ 32) (hx : InIVs x xv)
    (hB : Bdd 16 xv) (d : ℕ → ℕ → ℝ) (hd : ∀ i k, |d i k| ≤ (δ : ℝ)) :
    ∀ (A : List (List ℚ)) (i : ℕ), (∀ r ∈ A, r.length = x.length) →
      (∀ r ∈ A, smallQ r = true) →
      InIVs (armat fl A x d i) (matIV δ A xv) ∧ ∀ a ∈ matIV δ A xv, 0 ≤ a.2 := by
  intro A
  induction A with
  | nil =>
    intro i _ _
    exact ⟨zinIVs_nil, fun a ha => absurd ha (by simp [matIV])⟩
  | cons r A ih =>
    intro i hr hs
    obtain ⟨ih1, ih2⟩ := ih (i + 1) (fun r' h' => hr r' (List.mem_cons_of_mem _ h'))
      (fun r' h' => hs r' (List.mem_cons_of_mem _ h'))
    have hrx : r.length = x.length := hr r (by simp)
    obtain ⟨hin, hnn⟩ := dot_sound u η M fl hC δ hδ0 hδ1 r x xv (d i) (hd i) hrx (by omega)
      (hs r (by simp)) hx hB
    have e1 : armat fl (r :: A) x d i = ardot fl r x (d i) 0 0 :: armat fl A x d (i + 1) := rfl
    have e2 : matIV δ (r :: A) xv = dotIV δ r xv :: matIV δ A xv := rfl
    rw [e1, e2]
    refine ⟨zinIVs_cons hin ih1, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with h3 | ha'
    · rw [h3]
      exact hnn
    · exact ih2 a ha'

theorem mat_sound : MatSound := by
  intro u η M fl hC δ hδ0 hδ1 A x xv d hd hr hx32 hsm hx hB
  exact zmat_aux hC hδ0 hδ1 hx32 hx hB d hd A 0 hr (zsmallM_mem hsm)

/-! ### aff -/

theorem zaff_aux {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) {δ : ℚ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2) {x : List ℝ} {xv : List IV} (hx32 : x.length ≤ 32) (hx : InIVs x xv)
    (hB : Bdd 16 xv) (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ) (hdW : ∀ i k, |dW i k| ≤ (δ : ℝ))
    (hdb : ∀ i, |db i| ≤ (δ : ℝ)) :
    ∀ (A : List (List ℚ)) (b : List ℚ) (i : ℕ), (∀ r ∈ A, r.length = x.length) →
      (∀ r ∈ A, smallQ r = true) → (∀ c ∈ b, qabs c ≤ 15) →
      (∀ v ∈ affIV δ A b xv, small v = true) →
      InIVs (araffine fl A b x dW db i) (affIV δ A b xv) ∧ Bdd 15 (affIV δ A b xv) := by
  intro A
  induction A with
  | nil =>
    intro b i _ _ _ _
    have e1 : affIV δ [] b xv = [] := by cases b <;> rfl
    have e2 : araffine fl [] b x dW db i = [] := by cases b <;> rfl
    rw [e1, e2]
    exact ⟨zinIVs_nil, fun a ha => absurd ha (by simp)⟩
  | cons r A ih =>
    intro b i hr hs hb hsm
    cases b with
    | nil =>
      have e1 : affIV δ (r :: A) [] xv = [] := rfl
      have e2 : araffine fl (r :: A) [] x dW db i = [] := rfl
      rw [e1, e2]
      exact ⟨zinIVs_nil, fun a ha => absurd ha (by simp)⟩
    | cons c b =>
      have e1 : affIV δ (r :: A) (c :: b) xv
          = ((dotIV δ r xv).1 + c, (dotIV δ r xv).2 + e0 δ + rnd) :: affIV δ A b xv := rfl
      have e2 : araffine fl (r :: A) (c :: b) x dW db i
          = fl (ardot fl r x (dW i) 0 0 + asw fl c (db i)) :: araffine fl A b x dW db (i + 1) :=
        rfl
      have hsm' : ∀ v ∈ (((dotIV δ r xv).1 + c, (dotIV δ r xv).2 + e0 δ + rnd)
          :: affIV δ A b xv), small v = true := hsm
      have hsm0 : qabs ((dotIV δ r xv).1 + c) + ((dotIV δ r xv).2 + e0 δ + rnd) ≤ 15 :=
        zsmall_le (v := ((dotIV δ r xv).1 + c, (dotIV δ r xv).2 + e0 δ + rnd))
          (hsm' ((dotIV δ r xv).1 + c, (dotIV δ r xv).2 + e0 δ + rnd) (by simp))
      have hsm1 : ∀ v ∈ affIV δ A b xv, small v = true :=
        fun v hv => hsm' v (List.mem_cons_of_mem _ hv)
      obtain ⟨ih1, ih2⟩ := ih b (i + 1) (fun r' h' => hr r' (List.mem_cons_of_mem _ h'))
        (fun r' h' => hs r' (List.mem_cons_of_mem _ h'))
        (fun c' h' => hb c' (List.mem_cons_of_mem _ h')) hsm1
      have hrx : r.length = x.length := hr r (by simp)
      obtain ⟨hin, hnn⟩ := dot_sound u η M fl hC δ hδ0 hδ1 r x xv (dW i) (hdW i) hrx (by omega)
        (hs r (by simp)) hx hB
      have hy := zlin_step hC hδ0 hδ1 hin (hb c (by simp)) (hdb i)
      have hr1 := zround_step hC hy hsm0
      rw [e1, e2]
      refine ⟨zinIVs_cons hr1 ih1, ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with h3 | ha'
      · rw [h3]
        refine ⟨?_, hsm0⟩
        have t1 := ze0_nonneg hδ0
        have t2 := zrnd_pos
        show 0 ≤ (dotIV δ r xv).2 + e0 δ + rnd
        linarith
      · exact ih2 a ha'

theorem aff_sound : AffSound := by
  intro u η M fl hC δ hδ0 hδ1 A b x xv dW db hdW hdb hr hx32 hsA hsb hx hB hall
  exact zaff_aux hC hδ0 hδ1 hx32 hx hB dW db hdW hdb A b 0 hr (zsmallM_mem hsA)
    (zsmallQ_mem hsb) (List.all_eq_true.mp hall)

/-! ### add -/

theorem zadd_aux {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) :
    ∀ (a b : List ℝ) (av bv : List IV), InIVs a av → InIVs b bv → (∀ v ∈ av, 0 ≤ v.2) →
      (∀ v ∈ bv, 0 ≤ v.2) → (∀ v ∈ addIV av bv, small v = true) →
      InIVs (radd fl a b) (addIV av bv) ∧ Bdd 15 (addIV av bv) := by
  intro a
  induction a with
  | nil =>
    intro b av bv ha hb _ _ _
    have h0 := zinIVs_nil_left ha
    subst h0
    have e1 : radd fl [] b = [] := by cases b <;> rfl
    have e2 : addIV [] bv = [] := by cases bv <;> rfl
    rw [e1, e2]
    exact ⟨zinIVs_nil, fun a ha => absurd ha (by simp)⟩
  | cons a0 a ih =>
    intro b av bv ha hb hna hnb hsm
    cases av with
    | nil => exact absurd (zinIVs_len ha) (by simp)
    | cons v av =>
      cases b with
      | nil =>
        have h0 := zinIVs_nil_left hb
        subst h0
        have e1 : radd fl (a0 :: a) [] = [] := rfl
        have e2 : addIV (v :: av) [] = [] := rfl
        rw [e1, e2]
        exact ⟨zinIVs_nil, fun a ha => absurd ha (by simp)⟩
      | cons b0 b =>
        cases bv with
        | nil => exact absurd (zinIVs_len hb) (by simp)
        | cons w bv =>
          obtain ⟨ha1, ha2⟩ := zinIVs_cons_inv ha
          obtain ⟨hb1, hb2⟩ := zinIVs_cons_inv hb
          have e1 : radd fl (a0 :: a) (b0 :: b) = fl (a0 + b0) :: radd fl a b := rfl
          have e2 : addIV (v :: av) (w :: bv)
              = (v.1 + w.1, v.2 + w.2 + rnd) :: addIV av bv := rfl
          have hsm' : ∀ y ∈ ((v.1 + w.1, v.2 + w.2 + rnd) :: addIV av bv), small y = true := hsm
          have hsm0 : qabs (v.1 + w.1) + (v.2 + w.2 + rnd) ≤ 15 :=
            zsmall_le (v := (v.1 + w.1, v.2 + w.2 + rnd))
              (hsm' (v.1 + w.1, v.2 + w.2 + rnd) (by simp))
          have hsm1 : ∀ y ∈ addIV av bv, small y = true :=
            fun y hy => hsm' y (List.mem_cons_of_mem _ hy)
          have hv0 : 0 ≤ v.2 := hna v (by simp)
          have hw0 : 0 ≤ w.2 := hnb w (by simp)
          obtain ⟨ih1, ih2⟩ := ih b av bv ha2 hb2
            (fun y hy => hna y (List.mem_cons_of_mem _ hy))
            (fun y hy => hnb y (List.mem_cons_of_mem _ hy)) hsm1
          have hy : |(a0 + b0) - (((v.1 : ℚ) : ℝ) + ((w.1 : ℚ) : ℝ))|
              ≤ ((v.2 : ℚ) : ℝ) + ((w.2 : ℚ) : ℝ) :=
            zabs_add_pair (zinIV_iff.mp ha1) (zinIV_iff.mp hb1)
          have hy' : |(a0 + b0) - (((v.1 + w.1 : ℚ)) : ℝ)| ≤ (((v.2 + w.2 : ℚ)) : ℝ) := by
            push_cast
            exact hy
          have hr1 := zround_step hC hy' hsm0
          rw [e1, e2]
          refine ⟨zinIVs_cons hr1 ih1, ?_⟩
          intro y hyy
          rcases List.mem_cons.mp hyy with h3 | hy3
          · rw [h3]
            refine ⟨?_, hsm0⟩
            have t2 := zrnd_pos
            show 0 ≤ v.2 + w.2 + rnd
            linarith
          · exact ih2 y hy3

theorem add_sound : AddSound := by
  intro u η M fl hC a b av bv ha hb hna hnb hall
  exact zadd_aux hC a b av bv ha hb hna hnb (List.all_eq_true.mp hall)

/-! ### relu -/

theorem zrelu_in {x : ℝ} {c r : ℚ} (h : |x - (c : ℝ)| ≤ (r : ℝ)) :
    InIV (Lane4.relu x) (reluIV (c, r)) := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  have hlo : max ((c : ℝ) - (r : ℝ)) 0 ≤ max x 0 := max_le_max (by linarith) le_rfl
  have hhi : max x 0 ≤ max ((c : ℝ) + (r : ℝ)) 0 := max_le_max (by linarith) le_rfl
  rw [zinIV_iff]
  have e1 : (reluIV (c, r)).1 = (max (c - r) 0 + max (c + r) 0) / 2 := rfl
  have e2 : (reluIV (c, r)).2 = (max (c + r) 0 - max (c - r) 0) / 2 := rfl
  rw [e1, e2]
  push_cast
  show |max x 0 - (max ((c : ℝ) - (r : ℝ)) 0 + max ((c : ℝ) + (r : ℝ)) 0) / 2|
    ≤ (max ((c : ℝ) + (r : ℝ)) 0 - max ((c : ℝ) - (r : ℝ)) 0) / 2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem zrelu_bdd (c r : ℚ) (h0 : 0 ≤ r) (h1 : qabs c + r ≤ 15) :
    0 ≤ (reluIV (c, r)).2 ∧ qabs (reluIV (c, r)).1 + (reluIV (c, r)).2 ≤ 15 := by
  have hlo : max (c - r) 0 ≤ max (c + r) 0 := max_le_max (by linarith) le_rfl
  have hnn : 0 ≤ max (c - r) 0 := le_max_right _ _
  have hnn2 : 0 ≤ max (c + r) 0 := le_max_right _ _
  have hc : c ≤ qabs c := zle_qabs c
  have hhi : max (c + r) 0 ≤ 15 := max_le (by linarith) (by norm_num)
  have e1 : (reluIV (c, r)).1 = (max (c - r) 0 + max (c + r) 0) / 2 := rfl
  have e2 : (reluIV (c, r)).2 = (max (c + r) 0 - max (c - r) 0) / 2 := rfl
  have hpos : 0 ≤ (max (c - r) 0 + max (c + r) 0) / 2 := by linarith
  rw [e1, e2, zqabs_of_nonneg hpos]
  constructor <;> linarith

theorem relu_sound : ReluSound := by
  intro x
  induction x with
  | nil =>
    intro xv hx hB
    have h0 := zinIVs_nil_left hx
    subst h0
    exact ⟨zinIVs_nil, fun a ha => absurd ha (by simp)⟩
  | cons a0 x ih =>
    intro xv hx hB
    cases xv with
    | nil => exact absurd (zinIVs_len hx) (by simp)
    | cons v vs =>
      obtain ⟨h1, h2⟩ := zinIVs_cons_inv hx
      obtain ⟨ih1, ih2⟩ := ih vs h2 (fun a ha => hB a (List.mem_cons_of_mem _ ha))
      have hv := hB v (by simp)
      have e1 : (a0 :: x).map Lane4.relu = Lane4.relu a0 :: x.map Lane4.relu := rfl
      have e2 : (v :: vs).map reluIV = reluIV v :: vs.map reluIV := rfl
      rw [e1, e2]
      refine ⟨zinIVs_cons (zrelu_in (zinIV_iff.mp h1)) ih1, ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with h3 | ha'
      · rw [h3]
        exact zrelu_bdd v.1 v.2 hv.1 hv.2
      · exact ih2 a ha'

/-! ### gate -/

theorem zgate_logic (c e : ℚ) (b : Bool)
    (hg : (if qabs c + e ≤ 15 then
      (if c + e < 0 then some true else if 0 < c - e then some false else none)
      else none) = some b) :
    qabs c + e ≤ 15 ∧ ((b = true ∧ c + e < 0) ∨ (b = false ∧ 0 < c - e)) := by
  by_cases h1 : qabs c + e ≤ 15
  · rw [if_pos h1] at hg
    refine ⟨h1, ?_⟩
    by_cases h2 : c + e < 0
    · rw [if_pos h2] at hg
      exact Or.inl ⟨(Option.some.inj hg).symm, h2⟩
    · rw [if_neg h2] at hg
      by_cases h3 : 0 < c - e
      · rw [if_pos h3] at hg
        exact Or.inr ⟨(Option.some.inj hg).symm, h3⟩
      · rw [if_neg h3] at hg
        exact absurd hg (by simp)
  · rw [if_neg h1] at hg
    exact absurd hg (by simp)

theorem zgate_core {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) {y : ℝ} {c e : ℚ}
    (hy : |y - (c : ℝ)| ≤ (e : ℝ)) (hs : qabs c + (e + rnd) ≤ 15) {b : Bool}
    (hcase : (b = true ∧ c + (e + rnd) < 0) ∨ (b = false ∧ 0 < c - (e + rnd))) :
    (Lane4.relu (fl y) = 0 ↔ b = true) := by
  have h1 := zround_step hC hy hs
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  rcases hcase with ⟨hb, hneg⟩ | ⟨hb, hpos⟩
  · subst hb
    have h4 : ((c + (e + rnd) : ℚ) : ℝ) < 0 := by exact_mod_cast hneg
    have h5 : ((c + (e + rnd) : ℚ) : ℝ) = (c : ℝ) + ((e + rnd : ℚ) : ℝ) := Rat.cast_add _ _
    have hz : Lane4.relu (fl y) = 0 := by
      unfold Lane4.relu
      exact max_eq_right (by linarith)
    exact ⟨fun _ => rfl, fun _ => hz⟩
  · subst hb
    have h4 : (0 : ℝ) < ((c - (e + rnd) : ℚ) : ℝ) := by exact_mod_cast hpos
    have h5 : ((c - (e + rnd) : ℚ) : ℝ) = (c : ℝ) - ((e + rnd : ℚ) : ℝ) := Rat.cast_sub _ _
    have hpos' : 0 < fl y := by linarith
    have hr : Lane4.relu (fl y) = fl y := max_eq_left hpos'.le
    constructor
    · intro h
      rw [hr] at h
      exact absurd h hpos'.ne'
    · intro h
      exact absurd h (by simp)

theorem gate_sound : GateSound := by
  intro u η M fl hC δ hδ0 hδ1 h x xv dg dgb hdg hdgb hgx hg32 hsg hsgb hx hB b hgd
  have hgd' := zgate_logic ((dotIV δ h.g xv).1 + h.gb) ((dotIV δ h.g xv).2 + e0 δ + rnd) b hgd
  obtain ⟨hs, hcase⟩ := hgd'
  obtain ⟨hin, hnn⟩ := dot_sound u η M fl hC δ hδ0 hδ1 h.g x xv dg hdg hgx hg32 hsg hx hB
  have hgb : qabs h.gb ≤ 15 := zsmallQ_mem hsgb h.gb (by simp)
  have hy := zlin_step hC hδ0 hδ1 hin hgb hdgb
  have hgate : h.gate fl dg dgb x
      = Lane4.relu (fl (ardot fl h.g x dg 0 0 + asw fl h.gb dgb)) := rfl
  rw [hgate]
  exact zgate_core hC hy hs hcase

/-! ### score -/

def srad (n X e1 Y e2 : ℚ) : ℚ :=
  n * (e1 * (Y + e2) + X * e2) + n * (X + e1 + 1) * (Y + e2 + 1) / 2 ^ 16 + 1 / 2 ^ 100

def sIV (xq y : List IV) : IV :=
  (dotC (xq.map Prod.fst) y,
   srad (xq.length : ℚ) (maxAbs (xq.map Prod.fst)) (maxAbs (xq.map Prod.snd))
     (maxAbs (y.map Prod.fst)) (maxAbs (y.map Prod.snd)))

theorem zscoreIV_eq (δ : ℚ) (h : AHead) (xq xt : List IV) :
    scoreIV δ h xq xt = sIV xq (matIV δ h.A xt) := rfl

theorem zsrad_nonneg {n X e1 Y e2 : ℚ} (hn : 0 ≤ n) (hX : 0 ≤ X) (he1 : 0 ≤ e1) (hY : 0 ≤ Y)
    (he2 : 0 ≤ e2) : 0 ≤ srad n X e1 Y e2 := by
  unfold srad
  have t1 : 0 ≤ e1 * (Y + e2) + X * e2 :=
    add_nonneg (mul_nonneg he1 (add_nonneg hY he2)) (mul_nonneg hX he2)
  have t2 : 0 ≤ n * (X + e1 + 1) * (Y + e2 + 1) / 2 ^ 16 :=
    div_nonneg (mul_nonneg (mul_nonneg hn (by linarith)) (by linarith)) (by norm_num)
  have t3 : (0 : ℚ) ≤ 1 / 2 ^ 100 := by norm_num
  have t4 := mul_nonneg hn t1
  linarith

theorem zsrad_cast (n X e1 Y e2 : ℚ) :
    ((srad n X e1 Y e2 : ℚ) : ℝ) = (n : ℝ) * ((e1 : ℝ) * ((Y : ℝ) + (e2 : ℝ)) + (X : ℝ) * (e2 : ℝ))
      + (n : ℝ) * ((X : ℝ) + (e1 : ℝ) + 1) * ((Y : ℝ) + (e2 : ℝ) + 1) / 2 ^ 16 + 1 / 2 ^ 100 := by
  unfold srad
  first | (push_cast; ring) | push_cast | simp

theorem zsIV_nonneg (xq y : List IV) : 0 ≤ (sIV xq y).2 :=
  zsrad_nonneg (Nat.cast_nonneg _) (zmaxAbs_nonneg _) (zmaxAbs_nonneg _) (zmaxAbs_nonneg _)
    (zmaxAbs_nonneg _)

theorem zarmat_length (fl : ℝ → ℝ) (x : List ℝ) (d : ℕ → ℕ → ℝ) :
    ∀ (A : List (List ℚ)) (i : ℕ), (armat fl A x d i).length = A.length := by
  intro A
  induction A with
  | nil => intro i; rfl
  | cons r A ih =>
    intro i
    have e1 : armat fl (r :: A) x d i = ardot fl r x (d i) 0 0 :: armat fl A x d (i + 1) := rfl
    rw [e1]
    simp [ih]

theorem zsIV_sound {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) {xq y : List ℝ}
    {xqv yv : List IV} (hxq : InIVs xq xqv) (hy : InIVs y yv) (hn1 : ∀ a ∈ xqv, 0 ≤ a.2)
    (hn2 : ∀ a ∈ yv, 0 ≤ a.2) (hlen : xq.length = y.length) (h32 : xq.length ≤ 32)
    (hT : (maxAbs (xqv.map Prod.fst) + maxAbs (xqv.map Prod.snd) + 1) *
          (maxAbs (yv.map Prod.fst) + maxAbs (yv.map Prod.snd) + 1) ≤ 2 ^ 20) :
    |pdot fl xq y 0 - (((sIV xqv yv).1 : ℚ) : ℝ)| ≤ (((sIV xqv yv).2 : ℚ) : ℝ) := by
  have hC1 := zclose_of_iv hxq hn1
  have hC2 := zclose_of_iv hy hn2
  have hM : (2 : ℝ) ^ 30 ≤ M := by
    have h1 := hC.M1
    have h2 : (2 : ℝ) ^ 30 ≤ 2 ^ 40 := by norm_num
    linarith
  have hT' : (((maxAbs (xqv.map Prod.fst) : ℚ) : ℝ) + ((maxAbs (xqv.map Prod.snd) : ℚ) : ℝ) + 1) *
      (((maxAbs (yv.map Prod.fst) : ℚ) : ℝ) + ((maxAbs (yv.map Prod.snd) : ℚ) : ℝ) + 1)
      ≤ 2 ^ 20 := by exact_mod_cast hT
  have hX0 : (0 : ℝ) ≤ ((maxAbs (xqv.map Prod.fst) : ℚ) : ℝ) := by
    exact_mod_cast zmaxAbs_nonneg (xqv.map Prod.fst)
  have hY0 : (0 : ℝ) ≤ ((maxAbs (yv.map Prod.fst) : ℚ) : ℝ) := by
    exact_mod_cast zmaxAbs_nonneg (yv.map Prod.fst)
  have he10 : (0 : ℝ) ≤ ((maxAbs (xqv.map Prod.snd) : ℚ) : ℝ) := by
    exact_mod_cast zmaxAbs_nonneg (xqv.map Prod.snd)
  have he20 : (0 : ℝ) ≤ ((maxAbs (yv.map Prod.snd) : ℚ) : ℝ) := by
    exact_mod_cast zmaxAbs_nonneg (yv.map Prod.snd)
  have key := pdot_near u η M fl hC.rnd hC.u0 hC.u1 hC.h0 hC.h1 xq
    (xqv.map (fun a => ((a.1 : ℚ) : ℝ))) y (yv.map (fun a => ((a.1 : ℚ) : ℝ)))
    ((maxAbs (xqv.map Prod.fst) : ℚ) : ℝ) ((maxAbs (yv.map Prod.fst) : ℚ) : ℝ)
    ((maxAbs (xqv.map Prod.snd) : ℚ) : ℝ) ((maxAbs (yv.map Prod.snd) : ℚ) : ℝ)
    hlen h32 hC1 hC2 hX0 hY0 he10 he20 hT' hM
  obtain ⟨k1, _⟩ := key
  have hxl : xq.length = xqv.length := zinIVs_len hxq
  rw [hxl] at k1
  have e1 : (((sIV xqv yv).1 : ℚ) : ℝ)
      = dotR (xqv.map (fun a => ((a.1 : ℚ) : ℝ))) (yv.map (fun a => ((a.1 : ℚ) : ℝ))) :=
    zdotC_cast_R xqv yv
  have e2 := zsrad_cast (xqv.length : ℚ) (maxAbs (xqv.map Prod.fst)) (maxAbs (xqv.map Prod.snd))
    (maxAbs (yv.map Prod.fst)) (maxAbs (yv.map Prod.snd))
  rw [Rat.cast_natCast] at e2
  have e3 : (((sIV xqv yv).2 : ℚ) : ℝ)
      = ((srad (xqv.length : ℚ) (maxAbs (xqv.map Prod.fst)) (maxAbs (xqv.map Prod.snd))
          (maxAbs (yv.map Prod.fst)) (maxAbs (yv.map Prod.snd)) : ℚ) : ℝ) := rfl
  rw [e1, e3, e2]
  first | exact k1 | linarith [k1]

theorem score_sound : ScoreSound := by
  intro u η M fl hC δ hδ0 hδ1 h xq xt xqv xtv dA hdA hr hxt32 hAq hxq32 hsA hxq hBq hxt hBt hsc
  obtain ⟨hmat, hmnn⟩ := mat_sound u η M fl hC δ hδ0 hδ1 h.A xt xtv dA hdA hr hxt32 hsA hxt hBt
  have hlenA : (armat fl h.A xt dA 0).length = h.A.length := zarmat_length fl xt dA h.A 0
  have hlen : xq.length = (armat fl h.A xt dA 0).length := by rw [hlenA, hAq]
  have hxqv : ∀ a ∈ xqv, 0 ≤ a.2 := fun a ha => (hBq a ha).1
  have hsc' := hsc
  simp only [scoreOK, Bool.and_eq_true, decide_eq_true_eq] at hsc'
  obtain ⟨hsc1, hsc2⟩ := hsc'
  rw [zscoreIV_eq] at hsc2 ⊢
  have hmain := zsIV_sound hC hxq hmat hxqv hmnn hlen hxq32 hsc1
  refine ⟨zinIV_iff.mpr hmain, zsIV_nonneg _ _, ?_⟩
  have hs2 : ((qabs (sIV xqv (matIV δ h.A xtv)).1 : ℚ) : ℝ)
      + (((sIV xqv (matIV δ h.A xtv)).2 : ℚ) : ℝ) ≤ 1024 := by
    exact_mod_cast hsc2
  rw [zqabs_cast] at hs2
  have h3 := abs_sub_abs_le_abs_sub (pdot fl xq (armat fl h.A xt dA 0) 0)
    (((sIV xqv (matIV δ h.A xtv)).1 : ℚ) : ℝ)
  linarith [hmain]

end Lane4.R7K2

