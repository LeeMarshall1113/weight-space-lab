namespace Lane4Final
theorem final : (Lane4.TB.Collision → Lane4.TB.ParityBound) ∧ (Lane4.TB.Collision → Lane4.TB.SortBound) :=
  ⟨Lane4.Case.parity_of_collision, Lane4.Case.sort_of_collision⟩
end Lane4Final
#print axioms Lane4Final.final
