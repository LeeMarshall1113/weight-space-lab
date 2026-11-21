namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

/-! coordinates: 0 mk, 1 a, 2 c, 3 f (=F/4), 4 A, 5 y -/

def z6 : List ℚ := [0, 0, 0, 0, 0, 0]
def z2 : List ℚ := [0, 0]

def head0 : AHead :=
  { A := [z6, z6, z6, z6, z6, z6],
    V := [z6, z6, z6, [1/4, 0, 0, 0, 0, 0], z6, z6],
    mask := Mask.strict, m := 24, g := [-1, 0, 0, 0, 0, 0], gb := 1/2 }

def head1 : AHead :=
  { A := [z6, z6, z6, z6, z6, z6],
    V := [z6, z6, z6, z6, [0, 1, 0, 0, 0, 0], z6],
    mask := Mask.causal, m := 24, g := [-1, 0, 0, 4, 0, 0], gb := 1/2 }

def blk0 : ABlock :=
  { heads := [head0], W1 := [], b1 := [], W2 := [[], [], [], [], [], []], b2 := z6 }

def blk1 : ABlock :=
  { heads := [head1], W1 := [[0, 0, 1, 0, -1, 0], [0, 0, -1, 0, 1, 0]], b1 := z2,
    W2 := [z2, z2, z2, z2, z2, [1, 1]], b2 := z6 }

def net : ANet :=
  { embed := [z6, [0, 0, 1, 0, 0, 0], z6, z6, [1, 1, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0]],
    blocks := [blk0, blk1], outW := [0, 0, 0, 0, 0, 1], outB := 0 }

theorem embed_row_chk (t : ℕ) (h : t ≤ 5) : (net.embed.getD t []).length = 6 := by
  interval_cases t <;> rfl

theorem net_ok : Statement net := by
  sorry_placeholder

end Lane4.Case
