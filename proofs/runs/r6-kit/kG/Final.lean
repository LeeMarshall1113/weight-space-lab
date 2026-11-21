namespace Lane4Final
theorem final : Lane4.Case.ArdotNear ∧ Lane4.Case.PdotNear ∧ Lane4.Case.BiasGap :=
  ⟨Lane4.Case.ardot_near, Lane4.Case.pdot_near, Lane4.Case.bias_gap⟩
end Lane4Final
#print axioms Lane4Final.final
