import Lane4.AGateAll
namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

/-! The difference of two networks of the same shape, as an additive perturbation.
`W` is the skeleton (the network a ball theorem is about), `T` the other network. -/

/-- Entry `c` of `b - a` (0 beyond either list), as a real. -/
def dq (a b : List ℚ) (c : ℕ) : ℝ := ((b.getD c 0 - a.getD c 0 : ℚ) : ℝ)
/-- Entry `(r, c)` of `B - A`. -/
def dm (A B : List (List ℚ)) (r c : ℕ) : ℝ := dq (A.getD r []) (B.getD r []) c

def nilHead : AHead := ⟨[], [], Mask.all, 0, [], 0⟩
def nilBlock : ABlock := ⟨[], [], [], [], []⟩
def blk (N : ANet) (b : ℕ) : ABlock := N.blocks.getD b nilBlock
def hd (N : ANet) (b h : ℕ) : AHead := (blk N b).heads.getD h nilHead

/-- `T - W`, weight by weight. -/
noncomputable def diffP (W T : ANet) : APert where
  E := fun t c => dm W.embed T.embed t c
  A := fun b h r c => dm (hd W b h).A (hd T b h).A r c
  V := fun b h r c => dm (hd W b h).V (hd T b h).V r c
  m := fun b h => (((hd T b h).m - (hd W b h).m : ℚ) : ℝ)
  g := fun b h c => dq (hd W b h).g (hd T b h).g c
  gb := fun b h => (((hd T b h).gb - (hd W b h).gb : ℚ) : ℝ)
  W1 := fun b r c => dm (blk W b).W1 (blk T b).W1 r c
  b1 := fun b r => dq (blk W b).b1 (blk T b).b1 r
  W2 := fun b r c => dm (blk W b).W2 (blk T b).W2 r c
  b2 := fun b r => dq (blk W b).b2 (blk T b).b2 r
  oW := fun c => dq W.outW T.outW c
  oB := ((T.outB - W.outB : ℚ) : ℝ)

/-- The zero perturbation. -/
def zeroP : APert :=
  ⟨fun _ _ => 0, fun _ _ _ _ => 0, fun _ _ _ _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun _ _ => 0,
   fun _ _ _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun _ _ => 0, fun _ => 0, 0⟩

/-! Same shape (a Boolean, so it is decided by evaluation). -/
def sameRows (A B : List (List ℚ)) : Bool :=
  A.length == B.length && (List.zipWith (fun a b => a.length == b.length) A B).all id
def sameHead (h k : AHead) : Bool :=
  sameRows h.A k.A && sameRows h.V k.V && decide (h.mask = k.mask) && h.g.length == k.g.length
def sameBlock (B C : ABlock) : Bool :=
  B.heads.length == C.heads.length && (List.zipWith sameHead B.heads C.heads).all id &&
  sameRows B.W1 C.W1 && B.b1.length == C.b1.length && sameRows B.W2 C.W2 &&
  B.b2.length == C.b2.length
def sameShape (W T : ANet) : Bool :=
  sameRows W.embed T.embed && W.blocks.length == T.blocks.length &&
  (List.zipWith sameBlock W.blocks T.blocks).all id && W.outW.length == T.outW.length

/-! Entrywise closeness (a Boolean on rationals; no absolute value, so it evaluates). -/
def nearQ (δ a b : ℚ) : Bool := decide (b - a ≤ δ) && decide (a - b ≤ δ)
def nearL (δ : ℚ) (a b : List ℚ) : Bool := (List.zipWith (nearQ δ) a b).all id
def nearM (δ : ℚ) (A B : List (List ℚ)) : Bool := (List.zipWith (nearL δ) A B).all id
def nearHead (δ : ℚ) (h k : AHead) : Bool :=
  nearM δ h.A k.A && nearM δ h.V k.V && nearQ δ h.m k.m && nearL δ h.g k.g && nearQ δ h.gb k.gb
def nearBlock (δ : ℚ) (B C : ABlock) : Bool :=
  (List.zipWith (nearHead δ) B.heads C.heads).all id && nearM δ B.W1 C.W1 && nearL δ B.b1 C.b1 &&
  nearM δ B.W2 C.W2 && nearL δ B.b2 C.b2
def nearNet (δ : ℚ) (W T : ANet) : Bool :=
  nearM δ W.embed T.embed && (List.zipWith (nearBlock δ) W.blocks T.blocks).all id &&
  nearL δ W.outW T.outW && nearQ δ W.outB T.outB

/-- Statement 1: the skeleton `W` perturbed by `T - W` IS the network `T` with no
perturbation: same output for every rounding function, exponential, input and position. -/
def OutShift : Prop :=
  ∀ (W T : ANet), sameShape W T = true → ∀ (fl ex : ℝ → ℝ) (w : List ℕ) (i : ℕ),
    ANet.out W fl ex (diffP W T) w i = ANet.out T fl ex zeroP w i

/-- Statement 2: if the two networks have the same shape and are entrywise within `δ`,
then `T - W` is a perturbation within `δ`. -/
def DiffWithin : Prop :=
  ∀ (W T : ANet) (δ : ℚ), 0 ≤ δ → sameShape W T = true → nearNet δ W T = true →
    (diffP W T).Within (δ : ℝ)

end Lane4.Case

namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)
def nW : ANet := ⟨[[0, 1/1024], [3/1024, -5/1024]],
  [⟨[⟨[[0, 0], [1/1024, 0]], [[1, 0], [0, 0]], Mask.strict, 24, [0, 0], -1⟩], [[1, 2]], [-3/1024], [[1], [0]], [0, 0]⟩], [0, 1], 0⟩
def nT : ANet := ⟨[[1/16777216, 8589935/8589934592], [3145729/1073741824, -5/1024]],
  [⟨[⟨[[0, 0], [1/1024, 0]], [[1, 0], [0, 0]], Mask.strict, 24, [0, 0], -1⟩], [[1, 2]], [-3/1024], [[1], [0]], [0, 0]⟩], [0, 1], 1/4096⟩
example : sameShape nW nT = true := by decide
example : nearNet (1 / 1000) nW nT = true := by decide
example : nearNet (1 / 100000) nW nT = false := by decide
example : nearNet (1 / 1000) nW nT = true := by decide +kernel
end Lane4.Case
