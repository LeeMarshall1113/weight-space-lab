namespace Lane4Final
theorem shape : Lane4.Net.shapeOK Lane4.Case.twin 1 1 = true := by decide
theorem final : Lane4.Case.StatementTwin := Lane4.Case.twin_correct
end Lane4Final
#print axioms Lane4Final.final
#print axioms Lane4Final.shape
