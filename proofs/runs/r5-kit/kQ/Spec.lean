namespace Lane4.Case
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

end Lane4.Case
