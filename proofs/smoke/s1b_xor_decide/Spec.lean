namespace Lane4.Case
def bit (b : Bool) : ℚ := if b then 1 else 0
def spec (b0 b1 : Bool) : ℚ := if xor b0 b1 then 1 else 0
def Statement (N : Lane4.Net) : Prop :=
  ∀ b0 b1 : Bool, N.eval [bit b0, bit b1] = [spec b0 b1]
end Lane4.Case
