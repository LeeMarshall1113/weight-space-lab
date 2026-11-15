-- The rational mirror and its bridge theorem (Lane4/QRSeq.lean, inlined)
namespace Lane4.QR
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

/-! A computable rational mirror of the rung-4 network of `RSeq.lean`, for exact
arithmetic (`fl = id`) and no weight perturbation. Every definition below follows the
corresponding `RSeq` definition with `fl` removed and all perturbations set to 0. -/

def qrdot : List ℚ → List ℚ → ℚ → ℚ
  | a :: w, v :: x, acc => qrdot w x (acc + a * v)
  | _, _, acc => acc

def qrmat (M : List (List ℚ)) (x : List ℚ) : List ℚ := M.map (fun r => qrdot r x 0)

def qraffine : List (List ℚ) → List ℚ → List ℚ → List ℚ
  | r :: M, c :: b, x => (qrdot r x 0 + c) :: qraffine M b x
  | _, _, _ => []

def qradd : List ℚ → List ℚ → List ℚ
  | a :: x, b :: y => (a + b) :: qradd x y
  | _, _ => []

def qpos (i n : ℕ) : List ℚ := [1, (i : ℚ), (n : ℚ)]

def qscore (h : Head) (xi xj : List ℚ) : ℚ := qrdot xi (qrmat h.A xj) 0

def qsel (c : List ℕ) (s : ℕ → ℚ) : List ℕ :=
  c.filter (fun j => decide (∀ k ∈ c, s k ≤ s j))

def qrsum : List ℚ → ℚ → ℚ
  | a :: l, acc => qrsum l (acc + a)
  | [], acc => acc

def qavg (S : List ℕ) (f : ℕ → ℚ) : ℚ := qrsum (S.map f) 0 / (S.length : ℚ)

def qattn (h : Head) (n : ℕ) (x : ℕ → List ℚ) (i : ℕ) : List ℚ :=
  h.V.map (fun r =>
    qavg (qsel (cand h.mask n i) (fun j => qscore h (x i) (x j))) (fun j => qrdot r (x j) 0))

def qheads : List Head → ℕ → (ℕ → List ℚ) → ℕ → List ℚ → List ℚ
  | h :: hs, n, x, i, acc => qheads hs n x i (qradd acc (qattn h n x i))
  | [], _, _, _, acc => acc

def qblock (B : Block) (n : ℕ) (x : ℕ → List ℚ) : ℕ → List ℚ := fun i =>
  qradd (qheads B.heads n x i (x i))
    (qraffine B.W2 B.b2 ((qraffine B.W1 B.b1 (qheads B.heads n x i (x i))).map (fun v => max v 0)))

def qinit (N : TNet) (w : List ℕ) : ℕ → List ℚ := fun i =>
  N.embed.getD (tokAt w i) [] ++ qpos i (w.length + 1)

def qrunFrom (n : ℕ) : List Block → (ℕ → List ℚ) → (ℕ → List ℚ)
  | B :: Bs, x => qrunFrom n Bs (qblock B n x)
  | [], x => x

def qout (N : TNet) (w : List ℕ) (i : ℕ) : ℚ :=
  qrdot N.outW (qrunFrom (w.length + 1) N.blocks (qinit N w) i) 0 + N.outB

/-- The zero perturbation. -/
def pert0 : Pert :=
  { E := fun _ _ => 0, A := fun _ _ _ _ => 0, V := fun _ _ _ _ => 0, W1 := fun _ _ _ => 0,
    b1 := fun _ _ => 0, W2 := fun _ _ _ => 0, b2 := fun _ _ => 0, oW := fun _ => 0, oB := 0 }

/-- With exact arithmetic and no perturbation, the `RSeq` network's output is the cast of
the rational mirror's output. -/
def QBridge : Prop :=
  ∀ (N : TNet) (w : List ℕ) (i : ℕ), N.out (fun x => x) pert0 w i = ((qout N w i : ℚ) : ℝ)

set_option linter.unusedVariables false
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
  rw [h1]
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
    rw [List.map_append, swRow_cast (pert0.E (tokAt w j)) (fun _ => rfl)]
    simp [pos, qpos]
  rw [hi, run_cast pert0 (w.length + 1) N.blocks 0 (qinit N w)]
  have h1 := rdot_cast N.outW (qrunFrom (w.length + 1) N.blocks (qinit N w) i) pert0.oW
    (fun _ => rfl) 0 0
  simp only [Rat.cast_zero] at h1
  have e : sw (fun x => x) N.outB pert0.oB = (N.outB : ℝ) := sw0 _ _ rfl
  simp only [h1, e]
  push_cast
  rfl

end Lane4.QR

namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

def cls (t : ℕ) : ℕ := if t = 1 then 2 else if t = 2 then 0 else if t = 3 then 0 else if t = 4 then 0 else if t = 5 then 1 else 0
def dg (t : ℕ) : ℕ := if t = 1 then 2 else if t = 2 then 0 else if t = 3 then 1 else if t = 4 then 1 else if t = 5 then 0 else 0
def carry (p : List ℕ) : ℕ := p.foldl (fun c t => if cls t = 2 then c else cls t) 0
def target (w : List ℕ) (i : ℕ) : ℕ :=
  (dg (w.getD (i - 1) 0) + carry (w.take (i - 1))) % 3

def Statement (N : TNet) : Prop :=
  ∀ (u : ℝ) (fl : ℝ → ℝ), Rounding u fl → 0 ≤ u → u ≤ 1 / 16777216 →
  ∀ p : Pert, p.Within (1 / 200) →
  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) → u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 →
  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → |N.out fl p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4


/-- `b` is within an absolute 1/1000 of `a`. -/
def qNear (a b : ℚ) : Bool := decide (|b - a| ≤ 1 / 1000)
def vNear (a b : List ℚ) : Bool := a.length == b.length && (List.zipWith qNear a b).all id
def mNear (A B : List (List ℚ)) : Bool := A.length == B.length && (List.zipWith vNear A B).all id
def hNear (h g : Head) : Bool := mNear h.A g.A && mNear h.V g.V && decide (h.mask = g.mask)
def bNear (B C : Block) : Bool :=
  B.heads.length == C.heads.length && (List.zipWith hNear B.heads C.heads).all id &&
  mNear B.W1 C.W1 && vNear B.b1 C.b1 && mNear B.W2 C.W2 && vNear B.b2 C.b2
/-- Every weight of `N'` is within an absolute 1/1000 of the corresponding weight of `N`. -/
def netNear (N N' : TNet) : Bool :=
  mNear N.embed N'.embed && N.blocks.length == N'.blocks.length &&
  (List.zipWith bNear N.blocks N'.blocks).all id && vNear N.outW N'.outW && qNear N.outB N'.outB

end Lane4.Case
