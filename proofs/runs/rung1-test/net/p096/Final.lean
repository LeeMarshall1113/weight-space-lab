namespace Lane4Final
theorem shape : Lane4.Net.shapeOK Lane4.Case.net 2 1 = true := by decide
theorem final : Lane4.Case.Statement Lane4.Case.net := Lane4.Case.net_correct
end Lane4Final
#print axioms Lane4Final.final
#print axioms Lane4Final.shape
