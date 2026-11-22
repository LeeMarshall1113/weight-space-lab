namespace Lane4Final
theorem final : Lane4.LNC.FrameFF ∧ Lane4.LNC.ZeroFacts ∧ Lane4.LNC.BoxSound ∧ Lane4.LNC.AddFSound ∧ Lane4.LNC.ReluFSound ∧ Lane4.LNC.ResFSound ∧ Lane4.LNC.HoFSound :=
  ⟨Lane4.Case.frame_ff, Lane4.Case.zero_facts, Lane4.Case.box_sound, Lane4.Case.add_f_sound, Lane4.Case.relu_f_sound, Lane4.Case.res_f_sound, Lane4.Case.ho_f_sound⟩
end Lane4Final
#print axioms Lane4Final.final
