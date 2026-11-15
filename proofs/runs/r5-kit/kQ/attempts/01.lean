set_option linter.unusedVariables false
namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

theorem sw0 (a : ℚ) (d : ℝ) (h : d = 0) : sw (fun x => x) a d = (a : ℝ) := by
  simp [sw, h]

theorem rdot_cast (r : List ℚ) : ∀ (x : List ℚ) (d : ℕ → ℝ) (hd : ∀ j, d j = 0) (j : ℕ) (acc : ℚ),
    rdot (fun x => x) r (x.map (fun q : ℚ => (q : ℝ))) d j (acc : ℝ) = ((qrdot r x acc : ℚ) : ℝ) := by
  induction r with
  | nil => intro x d hd j acc; cases x <;> simp [rdot, qrdot]
  | cons a w ih =>
    intro x d hd j acc
    cases x with
    | nil => simp [rdot, qrdot]
    | cons v x =>
      have e : sw (fun x => x) a (d j) = (a : ℝ) := sw0 _ _ (hd j)
      simp only [List.map_cons, rdot, qrdot, e]
      rw [← ih x d hd (j + 1) (acc + a * v)]
      push_cast
      rfl

theorem pdot_cast : ∀ (x y : List ℚ) (acc : ℚ),
    pdot (fun x => x) (x.map (fun q : ℚ => (q : ℝ))) (y.map (fun q : ℚ => (q : ℝ))) (acc : ℝ)
      = ((qrdot x y acc : ℚ) : ℝ) := by
  intro x
  induction x with
  | nil => intro y acc; cases y <;> simp [pdot, qrdot]
  | cons a w ih =>
    intro y acc
    cases y with
    | nil => simp [pdot, qrdot]
    | cons v y =>
      simp only [List.map_cons, pdot, qrdot]
      rw [← ih y (acc + a * v)]
      push_cast
      rfl

theorem rmat_cast (M : List (List ℚ)) (x : List ℚ) (d : ℕ → ℕ → ℝ) (hd : ∀ i j, d i j = 0) :
    ∀ i, rmat (fun x => x) M (x.map (fun q : ℚ => (q : ℝ))) d i
      = (qrmat M x).map (fun q : ℚ => (q : ℝ)) := by
  induction M with
  | nil => intro i; simp [rmat, qrmat]
  | cons r M ih =>
    intro i
    have h1 := rdot_cast r x (d i) (hd i) 0 0
    simp only [Rat.cast_zero] at h1
    simp only [rmat, qrmat, List.map_cons, h1]
    have := ih (i + 1)
    simp only [qrmat] at this
    rw [this]

theorem raffine_cast (M : List (List ℚ)) (x : List ℚ) (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ)
    (hW : ∀ i j, dW i j = 0) (hb : ∀ i, db i = 0) :
    ∀ (b : List ℚ) (i : ℕ), raffine (fun x => x) M b (x.map (fun q : ℚ => (q : ℝ))) dW db i
      = (qraffine M b x).map (fun q : ℚ => (q : ℝ)) := by
  induction M with
  | nil => intro b i; cases b <;> simp [raffine, qraffine]
  | cons r M ih =>
    intro b i
    cases b with
    | nil => simp [raffine, qraffine]
    | cons c b =>
      have h1 := rdot_cast r x (dW i) (hW i) 0 0
      simp only [Rat.cast_zero] at h1
      have e : sw (fun x => x) c (db i) = (c : ℝ) := sw0 _ _ (hb i)
      simp only [raffine, qraffine, List.map_cons, h1, e]
      rw [ih b (i + 1)]
      push_cast
      rfl

theorem radd_cast : ∀ (a b : List ℚ),
    radd (fun x => x) (a.map (fun q : ℚ => (q : ℝ))) (b.map (fun q : ℚ => (q : ℝ)))
      = (qradd a b).map (fun q : ℚ => (q : ℝ)) := by
  intro a
  induction a with
  | nil => intro b; simp [radd, qradd]
  | cons a x ih =>
    intro b
    cases b with
    | nil => simp [radd, qradd]
    | cons b y =>
      simp only [List.map_cons, radd, qradd]
      rw [ih y]
      push_cast
      rfl

theorem rsum_cast : ∀ (L : List ℚ) (acc : ℚ),
    rsum (fun x => x) (L.map (fun q : ℚ => (q : ℝ))) (acc : ℝ) = ((qrsum L acc : ℚ) : ℝ) := by
  intro L
  induction L with
  | nil => intro acc; simp [rsum, qrsum]
  | cons a l ih =>
    intro acc
    simp only [List.map_cons, rsum, qrsum]
    rw [← ih (acc + a)]
    push_cast
    rfl

theorem selOf_cast (c : List ℕ) (s : ℕ → ℝ) (s' : ℕ → ℚ) (h : ∀ k, s k = (s' k : ℝ)) :
    selOf c s = qsel c s' := by
  unfold selOf qsel
  apply List.filter_congr
  intro j _
  apply decide_eq_decide.mpr
  constructor
  · intro H k hk
    have := H k hk
    rw [h, h] at this
    exact_mod_cast this
  · intro H k hk
    rw [h, h]
    exact_mod_cast H k hk

theorem sel_cast (hd : Head) (dA : ℕ → ℕ → ℝ) (hA : ∀ i j, dA i j = 0) (n : ℕ) (x : ℕ → List ℚ)
    (i : ℕ) :
    hd.sel (fun x => x) dA n (fun j => (x j).map (fun q : ℚ => (q : ℝ))) i
      = qsel (cand hd.mask n i) (fun j => qscore hd (x i) (x j)) := by
  unfold Head.sel
  apply selOf_cast
  intro k
  unfold Head.score qscore
  rw [rmat_cast _ _ _ hA]
  have := pdot_cast (x i) (qrmat hd.A (x k)) 0
  simpa using this

theorem attnRows_cast (S : List ℕ) (x : ℕ → List ℚ) (dV : ℕ → ℕ → ℝ) (hV : ∀ i j, dV i j = 0) :
    ∀ (M : List (List ℚ)) (i : ℕ),
    attnRows (fun x => x) M dV S (fun j => (x j).map (fun q : ℚ => (q : ℝ))) i
      = (M.map (fun r => qavg S (fun j => qrdot r (x j) 0))).map (fun q : ℚ => (q : ℝ)) := by
  intro M
  induction M with
  | nil => intro i; simp [attnRows]
  | cons r M ih =>
    intro i
    simp only [attnRows, List.map_cons]
    rw [ih (i + 1)]
    congr 1
    unfold ravg qavg
    have h1 : S.map (fun j => rdot (fun x => x) r ((x j).map (fun q : ℚ => (q : ℝ))) (dV i) 0 0)
        = (S.map (fun j => qrdot r (x j) 0)).map (fun q : ℚ => (q : ℝ)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro j _
      have h2 := rdot_cast r (x j) (dV i) (hV i) 0 0
      simp only [Rat.cast_zero] at h2
      simpa using h2
    rw [h1]
    have h3 := rsum_cast (S.map (fun j => qrdot r (x j) 0)) 0
    simp only [Rat.cast_zero] at h3
    simp only [h3]
    push_cast
    rfl

theorem attn_cast (hd : Head) (dA dV : ℕ → ℕ → ℝ) (hA : ∀ i j, dA i j = 0)
    (hV : ∀ i j, dV i j = 0) (n : ℕ) (x : ℕ → List ℚ) (i : ℕ) :
    hd.attn (fun x => x) dA dV n (fun j => (x j).map (fun q : ℚ => (q : ℝ))) i
      = (qattn hd n x i).map (fun q : ℚ => (q : ℝ)) := by
  unfold Head.attn qattn
  rw [sel_cast hd dA hA n x i]
  exact attnRows_cast _ x dV hV _ 0

theorem heads_cast (hs : List Head) (dA dV : ℕ → ℕ → ℕ → ℝ) (hA : ∀ k i j, dA k i j = 0)
    (hV : ∀ k i j, dV k i j = 0) (n : ℕ) (x : ℕ → List ℚ) (i : ℕ) :
    ∀ (acc : List ℚ) (k : ℕ),
    headsApply (fun x => x) hs dA dV n (fun j => (x j).map (fun q : ℚ => (q : ℝ))) i
      (acc.map (fun q : ℚ => (q : ℝ))) k
      = (qheads hs n x i acc).map (fun q : ℚ => (q : ℝ)) := by
  induction hs with
  | nil => intro acc k; simp [headsApply, qheads]
  | cons h hs ih =>
    intro acc k
    simp only [headsApply, qheads]
    rw [attn_cast h (dA k) (dV k) (hA k) (hV k) n x i, radd_cast]
    exact ih _ _

theorem block_cast (B : Block) (b n : ℕ) (x : ℕ → List ℚ) :
    B.apply (fun x => x) pert0 b n (fun j => (x j).map (fun q : ℚ => (q : ℝ)))
      = fun i => (qblock B n x i).map (fun q : ℚ => (q : ℝ)) := by
  funext i
  have hA : ∀ k i j, (pert0.A b) k i j = 0 := fun _ _ _ => rfl
  have hV : ∀ k i j, (pert0.V b) k i j = 0 := fun _ _ _ => rfl
  have hh := heads_cast B.heads (pert0.A b) (pert0.V b) hA hV n x i (x i) 0
  unfold Block.apply qblock
  rw [hh]
  have h1 := raffine_cast B.W1 (qheads B.heads n x i (x i)) (pert0.W1 b) (pert0.b1 b)
    (fun _ _ => rfl) (fun _ => rfl) B.b1 0
  rw [h1, List.map_map]
  have h2 : ((qraffine B.W1 B.b1 (qheads B.heads n x i (x i))).map
      (fun v => max v 0)).map (fun q : ℚ => (q : ℝ))
      = ((qraffine B.W1 B.b1 (qheads B.heads n x i (x i))).map (fun q : ℚ => (q : ℝ))).map relu := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro v _
    simp [Lane4.relu, Rat.cast_max]
  rw [← h2]
  rw [raffine_cast B.W2 _ (pert0.W2 b) (pert0.b2 b) (fun _ _ => rfl) (fun _ => rfl) B.b2 0]
  rw [radd_cast]

theorem run_cast (p : Pert) (n : ℕ) (Bs : List Block) :
    ∀ (b : ℕ) (x : ℕ → List ℚ),
    runFrom (fun x => x) pert0 n Bs b (fun j => (x j).map (fun q : ℚ => (q : ℝ)))
      = fun j => (qrunFrom n Bs x j).map (fun q : ℚ => (q : ℝ)) := by
  induction Bs with
  | nil => intro b x; rfl
  | cons B Bs ih =>
    intro b x
    simp only [runFrom, qrunFrom]
    rw [block_cast B b n x]
    exact ih (b + 1) (qblock B n x)

theorem swRow_cast (d : ℕ → ℝ) (hd : ∀ j, d j = 0) :
    ∀ (r : List ℚ) (j : ℕ), swRow (fun x => x) r d j = r.map (fun q : ℚ => (q : ℝ)) := by
  intro r
  induction r with
  | nil => intro j; simp [swRow]
  | cons a r ih =>
    intro j
    simp only [swRow, List.map_cons]
    rw [sw0 _ _ (hd j), ih]

theorem q_bridge : QBridge := by
  intro N w i
  unfold TNet.out TNet.run qout
  have hi : N.init (fun x => x) pert0 w
      = fun j => (qinit N w j).map (fun q : ℚ => (q : ℝ)) := by
    funext j
    unfold TNet.init qinit
    rw [List.map_append, swRow_cast _ (fun _ => rfl)]
    simp [pos, qpos]
  rw [hi, run_cast pert0 (w.length + 1) N.blocks 0 (qinit N w)]
  have h1 := rdot_cast N.outW (qrunFrom (w.length + 1) N.blocks (qinit N w) i) pert0.oW
    (fun _ => rfl) 0 0
  simp only [Rat.cast_zero] at h1
  have e : sw (fun x => x) N.outB pert0.oB = (N.outB : ℝ) := sw0 _ _ rfl
  simp only [h1, e]
  push_cast
  rfl

end Lane4.Case
