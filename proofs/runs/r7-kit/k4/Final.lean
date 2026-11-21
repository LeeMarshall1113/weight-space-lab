namespace Lane4Final
theorem final : Lane4.Case.AbsClosed ∧ Lane4.Case.AbsLen ∧ Lane4.Case.AbsTarget ∧ Lane4.Case.AbsPick :=
  ⟨Lane4.Case.abs_closed, Lane4.Case.abs_len, Lane4.Case.abs_target, Lane4.Case.abs_pick⟩
end Lane4Final
#print axioms Lane4Final.final
