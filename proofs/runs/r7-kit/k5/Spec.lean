namespace Lane4.Case
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.R7K2

/-- The statement to prove is `Lane4.Cert.Sound` of R7Cert.lean, unchanged. -/
abbrev Goal : Prop := Lane4.Cert.Sound

end Lane4.Case
