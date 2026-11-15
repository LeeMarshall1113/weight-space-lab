/-
Bridge, A6(c): region certificates. Extends the frozen Bridge/IBP.lean (unchanged).

A region is a subcube: a fixed prefix `pre` of bits followed by `k` free bits, relaxed to
inputs in [0, 1]. A branch-and-bound tree splits on the next free bit. `checkT` closes a
leaf when the label is constant on the region (labels here depend only on popcount) and
interval bound propagation, with interval inputs AND interval weights, gives the right
sign. The cover of {0,1}^n is by construction of the tree, so no input is enumerated.
-/
import Bridge.IBP

namespace Bridge
open Lane4

/-! ### Interval inputs -/

def zerosQ : ℕ → List ℚ
  | 0 => []
  | k + 1 => 0 :: zerosQ k

def onesQ : ℕ → List ℚ
  | 0 => []
  | k + 1 => 1 :: onesQ k

theorem bnd_append : ∀ (a b : List ℚ) (c : List ℝ) (a' b' : List ℚ) (c' : List ℝ),
    Bnd a b c → Bnd a' b' c' → Bnd (a ++ a') (b ++ b') (c ++ c') := by
  intro a
  induction a with
  | nil =>
    intro b c a' b' c' h h'
    rcases b with _ | ⟨u, b⟩ <;> rcases c with _ | ⟨v, c⟩ <;> simp only [Bnd] at h
    simpa using h'
  | cons l a ih =>
    intro b c a' b' c' h h'
    rcases b with _ | ⟨u, b⟩ <;> rcases c with _ | ⟨v, c⟩ <;> simp only [Bnd] at h
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h1, h2, ih b c a' b' c' h3 h'⟩

theorem boolVecs_bnd : ∀ (k : ℕ) (ys : List ℕ), ys ∈ boolVecs k →
    Bnd (zerosQ k) (onesQ k) ((toQ ys).map (fun q : ℚ => (q : ℝ))) ∧ ys.sum ≤ k := by
  intro k
  induction k with
  | zero => intro ys h; simp [boolVecs] at h; subst h; simp [Bnd, toQ, zerosQ, onesQ]
  | succ k ih =>
    intro ys h
    simp only [boolVecs, List.mem_append, List.mem_map] at h
    rcases h with ⟨zs, hz, rfl⟩ | ⟨zs, hz, rfl⟩
    · obtain ⟨hb, hs⟩ := ih zs hz
      refine ⟨⟨by simp, by simp, ?_⟩, by simp; omega⟩
      simpa [toQ] using hb
    · obtain ⟨hb, hs⟩ := ih zs hz
      refine ⟨⟨by simp, by simp, ?_⟩, by simp; omega⟩
      simpa [toQ] using hb

/-- Interval forward pass with interval inputs `[lo, hi]` (shared evaluation). -/
def ibpNet2F (N : Net) (τ : ℚ) (lo hi : List ℚ) : List ℚ × List ℚ :=
  match ibpHiddenF N.hidden τ lo hi with
  | (a, b) => ibpRowsF N.out.W N.out.b τ a b

theorem net_sound2 (N : Net) (τ : ℚ) (lo hi : List ℚ) (vs : List ℝ) (hv : Bnd lo hi vs)
    (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (h : Within (τ : ℝ) dW db) :
    Bnd (ibpNet2F N τ lo hi).1 (ibpNet2F N τ lo hi).2 (N.evalP dW db vs) := by
  have e : ibpNet2F N τ lo hi =
      ibpRows N.out.W N.out.b τ (ibpHidden N.hidden τ lo hi).1 (ibpHidden N.hidden τ lo hi).2 := by
    unfold ibpNet2F
    rw [ibpHiddenF_eq]
    generalize ibpHidden N.hidden τ lo hi = p
    rcases p with ⟨a, b⟩
    exact ibpRowsF_eq τ a b _ _
  rw [e]
  unfold Net.evalP
  exact rows_sound τ (dW N.hidden.length) (db N.hidden.length) (h.1 _) (h.2 _) _ _ _
    (hidden_sound τ dW db h N.hidden lo hi vs 0 hv) _ _ 0

/-! ### Region check and the branch-and-bound tree -/

/-- The label `f` (a function of popcount) is constant on popcounts `p, p+1, ..., p+k`. -/
def constOn (f : ℕ → Bool) (p k : ℕ) : Bool := (List.range (k + 1)).all (fun c => f (p + c) == f p)

theorem constOn_spec {f : ℕ → Bool} {p k : ℕ} (h : constOn f p k = true) (c : ℕ) (hc : c ≤ k) :
    f (p + c) = f p := by
  have := List.all_eq_true.mp h c (List.mem_range.mpr (by omega))
  simpa using this

def regionOK (N : Net) (τ : ℚ) (f : ℕ → Bool) (pre : List ℕ) (k : ℕ) : Bool :=
  constOn f pre.sum k &&
  match ibpNet2F N τ (toQ pre ++ zerosQ k) (toQ pre ++ onesQ k) with
  | (l :: _, u :: _) => if f pre.sum then decide (0 < l) else decide (u < 0)
  | _ => false

inductive RTree where
  | leaf : RTree
  | split : RTree → RTree → RTree

def checkT (N : Net) (τ : ℚ) (f : ℕ → Bool) : List ℕ → ℕ → RTree → Bool
  | pre, k, .leaf => regionOK N τ f pre k
  | pre, k + 1, .split t0 t1 => checkT N τ f (pre ++ [0]) k t0 && checkT N τ f (pre ++ [1]) k t1
  | _, 0, .split _ _ => false

theorem checkT_split (N : Net) (τ : ℚ) (f : ℕ → Bool) (pre : List ℕ) (k : ℕ) (t0 t1 : RTree)
    (h0 : checkT N τ f (pre ++ [0]) k t0 = true) (h1 : checkT N τ f (pre ++ [1]) k t1 = true) :
    checkT N τ f pre (k + 1) (.split t0 t1) = true := by
  simp [checkT, h0, h1]

/-- Correct sign for one input vector. -/
def Good (N : Net) (f : ℕ → Bool) (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (xs : List ℕ) : Prop :=
  if f xs.sum then 0 < out1 (N.evalP dW db ((toQ xs).map (fun q : ℚ => (q : ℝ))))
  else out1 (N.evalP dW db ((toQ xs).map (fun q : ℚ => (q : ℝ)))) < 0

theorem regionOK_sound (N : Net) (τ : ℚ) (f : ℕ → Bool) (pre : List ℕ) (k : ℕ)
    (hc : regionOK N τ f pre k = true) (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ)
    (h : Within (τ : ℝ) dW db) (ys : List ℕ) (hy : ys ∈ boolVecs k) : Good N f dW db (pre ++ ys) := by
  obtain ⟨hb, hs⟩ := boolVecs_bnd k ys hy
  unfold regionOK at hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hconst, hc⟩ := hc
  have hlab : f (pre ++ ys).sum = f pre.sum := by
    rw [List.sum_append]; exact constOn_spec hconst ys.sum hs
  have hv : Bnd (toQ pre ++ zerosQ k) (toQ pre ++ onesQ k)
      ((toQ (pre ++ ys)).map (fun q : ℚ => (q : ℝ))) := by
    have : (toQ (pre ++ ys)).map (fun q : ℚ => (q : ℝ)) =
        (toQ pre).map (fun q : ℚ => (q : ℝ)) ++ (toQ ys).map (fun q : ℚ => (q : ℝ)) := by
      simp [toQ, List.map_append]
    rw [this]
    exact bnd_append _ _ _ _ _ _ (bnd_self (toQ pre)) hb
  have hn := net_sound2 N τ _ _ _ hv dW db h
  unfold Good
  rw [hlab]
  generalize ibpNet2F N τ (toQ pre ++ zerosQ k) (toQ pre ++ onesQ k) = P at hn hc
  rcases P with ⟨L, U⟩
  simp only at hn
  generalize N.evalP dW db ((toQ (pre ++ ys)).map (fun q : ℚ => (q : ℝ))) = V at hn ⊢
  rcases L with _ | ⟨l, L⟩
  · simp at hc
  rcases U with _ | ⟨u, U⟩
  · simp at hc
  rcases V with _ | ⟨v, V⟩
  · simp [Bnd] at hn
  obtain ⟨hl, hu, _⟩ := hn
  simp only at hc
  show (if f pre.sum = true then 0 < v else v < 0)
  split_ifs at hc ⊢
  · have h2 : 0 < l := by simpa using hc
    have : (0 : ℝ) < ((l : ℚ) : ℝ) := by exact_mod_cast h2
    linarith
  · have h2 : u < 0 := by simpa using hc
    have : ((u : ℚ) : ℝ) < 0 := by exact_mod_cast h2
    linarith

theorem checkT_sound (N : Net) (τ : ℚ) (f : ℕ → Bool) (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ)
    (h : Within (τ : ℝ) dW db) :
    ∀ (t : RTree) (pre : List ℕ) (k : ℕ), checkT N τ f pre k t = true →
      ∀ ys ∈ boolVecs k, Good N f dW db (pre ++ ys) := by
  intro t
  induction t with
  | leaf =>
    intro pre k hc ys hy
    simp only [checkT] at hc
    exact regionOK_sound N τ f pre k hc dW db h ys hy
  | split t0 t1 ih0 ih1 =>
    intro pre k hc ys hy
    rcases k with _ | k
    · simp [checkT] at hc
    simp only [checkT, Bool.and_eq_true] at hc
    simp only [boolVecs, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨zs, hz, rfl⟩ | ⟨zs, hz, rfl⟩
    · have := ih0 (pre ++ [0]) k hc.1 zs hz
      simpa using this
    · have := ih1 (pre ++ [1]) k hc.2 zs hz
      simpa using this

/-- The certified statement for a popcount label `f`: every weight setting within τ and
every x ∈ {0,1}^n gets the sign of `f (popcount x)`. -/
def SpecG (n : ℕ) (N : Net) (τ : ℚ) (f : ℕ → Bool) : Prop :=
  ∀ dW db, Within (τ : ℝ) dW db → ∀ xs ∈ boolVecs n, Good N f dW db xs

theorem certT (n : ℕ) (N : Net) (τ : ℚ) (f : ℕ → Bool) (t : RTree)
    (hc : checkT N τ f [] n t = true) : SpecG n N τ f := by
  intro dW db h xs hx
  simpa using checkT_sound N τ f dW db h t [] n hc xs hx

end Bridge
