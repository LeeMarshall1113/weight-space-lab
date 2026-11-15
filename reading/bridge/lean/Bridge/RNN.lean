/-
PREREG_RNN: all-lengths weight-ball certificates for (trained) clipped-ReLU Elman RNNs.

Cell: h' = clip(W [h ; onehot a] + b), clip x = min (max x 0) 1, one perturbed affine layer
(`rowsP` of the proofs/ study). Read-out: y = v·h + c (one perturbed row). Start h₀ = 0.
Spec: a DFA (δ, q₀, acc) over symbols 0..k-1.

`RSpec` says: for every perturbation of every cell and read-out weight/bias by at most τ,
and every string of every length, sign y = DFA acceptance. `certR` derives it from a finite
Boolean check (box invariant), closed by kernel evaluation. Imports Bridge.Region (for
`bnd_append`) and the frozen Bridge.IBP (for `rows_sound`, `ibpRowsF_eq`), both unchanged.
-/
import Bridge.Region

namespace Bridge
open Lane4

/-! ### clip -/

def clipQ (x : ℚ) : ℚ := min (max x 0) 1
noncomputable def clipR (x : ℝ) : ℝ := min (max x 0) 1

theorem clip_cast (q : ℚ) : ((clipQ q : ℚ) : ℝ) = clipR (q : ℝ) := by
  unfold clipQ clipR; push_cast; rfl

theorem clip_mono {a b : ℝ} (h : a ≤ b) : clipR a ≤ clipR b := by
  unfold clipR; exact min_le_min_right _ (max_le_max h le_rfl)

theorem bnd_clip : ∀ (ls us : List ℚ) (vs : List ℝ), Bnd ls us vs →
    Bnd (ls.map clipQ) (us.map clipQ) (vs.map clipR) := by
  intro ls
  induction ls with
  | nil =>
    intro us vs h
    rcases us with _ | ⟨u, us⟩ <;> rcases vs with _ | ⟨v, vs⟩ <;> simp_all [Bnd]
  | cons l ls ih =>
    intro us vs h
    rcases us with _ | ⟨u, us⟩ <;> rcases vs with _ | ⟨v, vs⟩ <;> simp only [Bnd] at h
    obtain ⟨hl, hu, hr⟩ := h
    simp only [List.map, Bnd, clip_cast]
    exact ⟨clip_mono hl, clip_mono hu, ih us vs hr⟩

/-! ### boxes -/

/-- `[lo, hi] ⊆ [lo', hi']` componentwise, same lengths. -/
def subBox : List ℚ → List ℚ → List ℚ → List ℚ → Bool
  | l :: ls, u :: us, l' :: ls', u' :: us' => decide (l' ≤ l) && decide (u ≤ u') && subBox ls us ls' us'
  | [], [], [], [] => true
  | _, _, _, _ => false

theorem bnd_sub : ∀ (ls us ls' us' : List ℚ) (vs : List ℝ), subBox ls us ls' us' = true →
    Bnd ls us vs → Bnd ls' us' vs := by
  intro ls
  induction ls with
  | nil =>
    intro us ls' us' vs hs hb
    rcases us with _ | ⟨u, us⟩ <;> rcases ls' with _ | ⟨l', ls'⟩ <;> rcases us' with _ | ⟨u', us'⟩ <;>
      simp [subBox] at hs
    exact hb
  | cons l ls ih =>
    intro us ls' us' vs hs hb
    rcases us with _ | ⟨u, us⟩ <;> rcases ls' with _ | ⟨l', ls'⟩ <;> rcases us' with _ | ⟨u', us'⟩ <;>
      simp [subBox] at hs
    rcases vs with _ | ⟨v, vs⟩ <;> simp only [Bnd] at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hs
    obtain ⟨b1, b2, b3⟩ := hb
    refine ⟨?_, ?_, ih us ls' us' vs h3 b3⟩
    · have : ((l' : ℚ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast h1
      linarith
    · have : ((u : ℚ) : ℝ) ≤ (u' : ℝ) := by exact_mod_cast h2
      linarith

/-! ### the net, its run, the DFA -/

def onehot (k a : ℕ) : List ℚ := (List.range k).map (fun i => if i = a then (1 : ℚ) else 0)

def zerosL (d : ℕ) : List ℚ := List.replicate d 0

noncomputable def cellR (C : Layer) (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ) (k : ℕ) (h : List ℝ) (a : ℕ) : List ℝ :=
  (rowsP C.W C.b dW db (h ++ (onehot k a).map (fun q : ℚ => (q : ℝ))) 0).map clipR

noncomputable def runR (C : Layer) (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ) (k : ℕ) : List ℝ → List ℕ → List ℝ
  | h, [] => h
  | h, a :: w => runR C dW db k (cellR C dW db k h a) w

noncomputable def outR (R : Layer) (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ) (h : List ℝ) : ℝ :=
  out1 (rowsP R.W R.b dW db h 0)

def runD (δ : ℕ → ℕ → ℕ) : ℕ → List ℕ → ℕ
  | q, [] => q
  | q, a :: w => runD δ (δ q a) w

/-- The certified statement. -/
def RSpec (C R : Layer) (k d : ℕ) (δ : ℕ → ℕ → ℕ) (q0 : ℕ) (acc : ℕ → Bool) (τ : ℚ) : Prop :=
  ∀ (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ) (dWo : ℕ → ℕ → ℝ) (dbo : ℕ → ℝ),
    (∀ i j, |dW i j| ≤ (τ : ℝ)) → (∀ i, |db i| ≤ (τ : ℝ)) →
    (∀ i j, |dWo i j| ≤ (τ : ℝ)) → (∀ i, |dbo i| ≤ (τ : ℝ)) →
    ∀ w : List ℕ, (∀ a ∈ w, a < k) →
      let y := outR R dWo dbo (runR C dW db k ((zerosL d).map (fun q : ℚ => (q : ℝ))) w)
      if acc (runD δ q0 w) then 0 < y else y < 0

/-! ### the finite check -/

def cellI (C : Layer) (τ : ℚ) (k : ℕ) (lo hi : List ℚ) (a : ℕ) : List ℚ × List ℚ :=
  match ibpRowsF C.W C.b τ (lo ++ onehot k a) (hi ++ onehot k a) with
  | (x, y) => (x.map clipQ, y.map clipQ)

def boxOf (B : List (List ℚ × List ℚ)) (q : ℕ) : List ℚ × List ℚ := B.getD q ([], [])

def stepOK (C : Layer) (τ : ℚ) (k : ℕ) (δ : ℕ → ℕ → ℕ) (B : List (List ℚ × List ℚ)) (q a : ℕ) : Bool :=
  match cellI C τ k (boxOf B q).1 (boxOf B q).2 a with
  | (x, y) => subBox x y (boxOf B (δ q a)).1 (boxOf B (δ q a)).2

def readOK (R : Layer) (τ : ℚ) (acc : ℕ → Bool) (B : List (List ℚ × List ℚ)) (q : ℕ) : Bool :=
  match ibpRowsF R.W R.b τ (boxOf B q).1 (boxOf B q).2 with
  | (l :: _, u :: _) => if acc q then decide (0 < l) else decide (u < 0)
  | _ => false

/-- Every state reachable from q0 lies below nQ; every check holds for q < nQ, a < k. -/
def checkR (C R : Layer) (k d nQ : ℕ) (δ : ℕ → ℕ → ℕ) (q0 : ℕ) (acc : ℕ → Bool) (τ : ℚ)
    (B : List (List ℚ × List ℚ)) : Bool :=
  decide (q0 < nQ) && decide (0 < k) &&
  subBox (zerosL d) (zerosL d) (boxOf B q0).1 (boxOf B q0).2 &&
  (List.range nQ).all (fun q => readOK R τ acc B q &&
    (List.range k).all (fun a => decide (δ q a < nQ) && stepOK C τ k δ B q a))

/-! ### soundness -/

theorem cell_sound (C : Layer) (τ : ℚ) (k : ℕ) (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ)
    (hW : ∀ i j, |dW i j| ≤ (τ : ℝ)) (hb : ∀ i, |db i| ≤ (τ : ℝ))
    (lo hi : List ℚ) (h : List ℝ) (hv : Bnd lo hi h) (a : ℕ) :
    Bnd (cellI C τ k lo hi a).1 (cellI C τ k lo hi a).2 (cellR C dW db k h a) := by
  have hin : Bnd (lo ++ onehot k a) (hi ++ onehot k a) (h ++ (onehot k a).map (fun q : ℚ => (q : ℝ))) :=
    bnd_append _ _ _ _ _ _ hv (bnd_self _)
  have hr := rows_sound τ dW db hW hb _ _ _ hin C.W C.b 0
  have e : cellI C τ k lo hi a =
      ((ibpRows C.W C.b τ (lo ++ onehot k a) (hi ++ onehot k a)).1.map clipQ,
       (ibpRows C.W C.b τ (lo ++ onehot k a) (hi ++ onehot k a)).2.map clipQ) := by
    unfold cellI
    rw [ibpRowsF_eq]
  rw [e]
  exact bnd_clip _ _ _ hr

theorem inv_sound (C : Layer) (τ : ℚ) (k nQ : ℕ) (δ : ℕ → ℕ → ℕ) (B : List (List ℚ × List ℚ))
    (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ) (hW : ∀ i j, |dW i j| ≤ (τ : ℝ)) (hb : ∀ i, |db i| ≤ (τ : ℝ))
    (hstep : ∀ q, q < nQ → ∀ a, a < k → δ q a < nQ ∧ stepOK C τ k δ B q a = true) :
    ∀ (w : List ℕ), (∀ a ∈ w, a < k) → ∀ (q : ℕ) (h : List ℝ), q < nQ → Bnd (boxOf B q).1 (boxOf B q).2 h →
      runD δ q w < nQ ∧ Bnd (boxOf B (runD δ q w)).1 (boxOf B (runD δ q w)).2 (runR C dW db k h w) := by
  intro w
  induction w with
  | nil => intro _ q h hq hv; exact ⟨hq, hv⟩
  | cons a w ih =>
    intro hw q h hq hv
    have ha : a < k := hw a (by simp)
    have hw' : ∀ b ∈ w, b < k := fun b hb' => hw b (by simp [hb'])
    obtain ⟨hδ, hs⟩ := hstep q hq a ha
    have hc := cell_sound C τ k dW db hW hb _ _ h hv a
    unfold stepOK at hs
    have hn : Bnd (boxOf B (δ q a)).1 (boxOf B (δ q a)).2 (cellR C dW db k h a) := by
      revert hs hc
      generalize cellI C τ k (boxOf B q).1 (boxOf B q).2 a = P
      rcases P with ⟨x, y⟩
      intro hs hc
      exact bnd_sub x y _ _ _ hs hc
    exact ih hw' (δ q a) _ hδ hn

theorem read_sound (R : Layer) (τ : ℚ) (acc : ℕ → Bool) (B : List (List ℚ × List ℚ)) (q : ℕ)
    (dWo : ℕ → ℕ → ℝ) (dbo : ℕ → ℝ) (hW : ∀ i j, |dWo i j| ≤ (τ : ℝ)) (hb : ∀ i, |dbo i| ≤ (τ : ℝ))
    (h : List ℝ) (hv : Bnd (boxOf B q).1 (boxOf B q).2 h) (hr : readOK R τ acc B q = true) :
    if acc q then 0 < outR R dWo dbo h else outR R dWo dbo h < 0 := by
  have hn := rows_sound τ dWo dbo hW hb _ _ _ hv R.W R.b 0
  unfold readOK at hr
  rw [ibpRowsF_eq] at hr
  unfold outR
  revert hn hr
  generalize ibpRows R.W R.b τ (boxOf B q).1 (boxOf B q).2 = P
  generalize rowsP R.W R.b dWo dbo h 0 = V
  rcases P with ⟨L, U⟩
  intro hr hn
  simp only at hn hr
  rcases L with _ | ⟨l, L⟩
  · simp at hr
  rcases U with _ | ⟨u, U⟩
  · simp at hr
  rcases V with _ | ⟨v, V⟩
  · simp [Bnd] at hn
  obtain ⟨hl, hu, _⟩ := hn
  show (if acc q = true then 0 < v else v < 0)
  split_ifs at hr ⊢
  · have h2 : 0 < l := by simpa using hr
    have : (0 : ℝ) < ((l : ℚ) : ℝ) := by exact_mod_cast h2
    linarith
  · have h2 : u < 0 := by simpa using hr
    have : ((u : ℚ) : ℝ) < 0 := by exact_mod_cast h2
    linarith

theorem certR (C R : Layer) (k d nQ : ℕ) (δ : ℕ → ℕ → ℕ) (q0 : ℕ) (acc : ℕ → Bool) (τ : ℚ)
    (B : List (List ℚ × List ℚ)) (hc : checkR C R k d nQ δ q0 acc τ B = true) :
    RSpec C R k d δ q0 acc τ := by
  intro dW db dWo dbo hW hb hWo hbo w hw
  unfold checkR at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hq0, _⟩, hstart⟩, hall⟩ := hc
  have hq0' : q0 < nQ := of_decide_eq_true hq0
  have hq : ∀ q, q < nQ → readOK R τ acc B q = true ∧
      ∀ a, a < k → δ q a < nQ ∧ stepOK C τ k δ B q a = true := by
    intro q hqn
    have h1 := List.all_eq_true.mp hall q (List.mem_range.mpr hqn)
    rw [Bool.and_eq_true] at h1
    refine ⟨h1.1, fun a ha => ?_⟩
    have h2 := List.all_eq_true.mp h1.2 a (List.mem_range.mpr ha)
    rw [Bool.and_eq_true] at h2
    exact ⟨of_decide_eq_true h2.1, h2.2⟩
  have h0 : Bnd (boxOf B q0).1 (boxOf B q0).2 ((zerosL d).map (fun q : ℚ => (q : ℝ))) :=
    bnd_sub _ _ _ _ _ hstart (bnd_self _)
  obtain ⟨hqe, hv⟩ := inv_sound C τ k nQ δ B dW db hW hb (fun q hq' a ha => (hq q hq').2 a ha) w hw q0 _ hq0' h0
  exact read_sound R τ acc B _ dWo dbo hWo hbo _ hv (hq _ hqe).1

end Bridge
