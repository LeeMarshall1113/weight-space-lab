namespace Lane4Final
theorem final : (Lane4.Case.RsumErr → Lane4.Case.GeomDist → Lane4.Case.SavgNear) ∧ Lane4.Case.SavgZeros :=
  ⟨Lane4.Case.savg_near, Lane4.Case.savg_zeros⟩
end Lane4Final
#print axioms Lane4Final.final
