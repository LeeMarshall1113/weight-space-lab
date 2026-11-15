import Bridge.IBP
open Lane4 Bridge

def net_ORD_w8_s2 : Net :=
  { hidden := [⟨[[(270/256 : ℚ), (-595/256 : ℚ), (270/256 : ℚ), (-542/256 : ℚ), (270/256 : ℚ), (178/256 : ℚ)], [(168/256 : ℚ), (-367/256 : ℚ), (190/256 : ℚ), (-403/256 : ℚ), (190/256 : ℚ), (222/256 : ℚ)], [(-351/256 : ℚ), (335/256 : ℚ), (-343/256 : ℚ), (76/256 : ℚ), (-343/256 : ℚ), (60/256 : ℚ)], [(-185/256 : ℚ), (325/256 : ℚ), (-172/256 : ℚ), (-149/256 : ℚ), (-172/256 : ℚ), (342/256 : ℚ)], [(-152/256 : ℚ), (-124/256 : ℚ), (-125/256 : ℚ), (-153/256 : ℚ), (-125/256 : ℚ), (-125/256 : ℚ)], [(-213/256 : ℚ), (-278/256 : ℚ), (106/256 : ℚ), (249/256 : ℚ), (106/256 : ℚ), (-213/256 : ℚ)], [(252/256 : ℚ), (-126/256 : ℚ), (-126/256 : ℚ), (-126/256 : ℚ), (-126/256 : ℚ), (-126/256 : ℚ)], [(423/256 : ℚ), (224/256 : ℚ), (238/256 : ℚ), (536/256 : ℚ), (238/256 : ℚ), (-128/256 : ℚ)]], [(403/256 : ℚ), (0/256 : ℚ), (283/256 : ℚ), (0/256 : ℚ), (402/256 : ℚ), (0/256 : ℚ), (0/256 : ℚ), (-184/256 : ℚ)]⟩, ⟨[[(-565/256 : ℚ), (1069/256 : ℚ), (-293/256 : ℚ), (547/256 : ℚ), (743/256 : ℚ), (314/256 : ℚ), (498/256 : ℚ), (337/256 : ℚ)], [(-492/256 : ℚ), (1069/256 : ℚ), (-301/256 : ℚ), (373/256 : ℚ), (697/256 : ℚ), (453/256 : ℚ), (389/256 : ℚ), (300/256 : ℚ)], [(-60/256 : ℚ), (29/256 : ℚ), (-3/256 : ℚ), (16/256 : ℚ), (9/256 : ℚ), (-85/256 : ℚ), (-19/256 : ℚ), (-57/256 : ℚ)], [(761/256 : ℚ), (-1035/256 : ℚ), (515/256 : ℚ), (-377/256 : ℚ), (-795/256 : ℚ), (-506/256 : ℚ), (-610/256 : ℚ), (24/256 : ℚ)], [(-529/256 : ℚ), (888/256 : ℚ), (-378/256 : ℚ), (497/256 : ℚ), (760/256 : ℚ), (468/256 : ℚ), (573/256 : ℚ), (349/256 : ℚ)], [(-112/256 : ℚ), (-109/256 : ℚ), (-19/256 : ℚ), (-59/256 : ℚ), (-33/256 : ℚ), (28/256 : ℚ), (-88/256 : ℚ), (1/256 : ℚ)], [(657/256 : ℚ), (-579/256 : ℚ), (352/256 : ℚ), (652/256 : ℚ), (-1235/256 : ℚ), (114/256 : ℚ), (-145/256 : ℚ), (-267/256 : ℚ)], [(-598/256 : ℚ), (-1386/256 : ℚ), (-319/256 : ℚ), (-609/256 : ℚ), (-770/256 : ℚ), (724/256 : ℚ), (-250/256 : ℚ), (539/256 : ℚ)]], [(47/256 : ℚ), (12/256 : ℚ), (-79/256 : ℚ), (243/256 : ℚ), (55/256 : ℚ), (-99/256 : ℚ), (-197/256 : ℚ), (448/256 : ℚ)]⟩],
    out := ⟨[[(-857/256 : ℚ), (-872/256 : ℚ), (-61/256 : ℚ), (792/256 : ℚ), (-886/256 : ℚ), (-51/256 : ℚ), (813/256 : ℚ), (1054/256 : ℚ)]], [(166/256 : ℚ)]⟩ }

theorem c0_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 0, 0, 0, 0, 0] = true := by decide +kernel
theorem c1_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 0, 0, 0, 0, 1] = true := by decide +kernel
theorem c2_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 0, 0, 0, 1, 0] = true := by decide +kernel
theorem c3_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 0, 0, 0, 1, 1] = true := by decide +kernel
theorem c4_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 0, 0, 1, 0, 0] = true := by decide +kernel
theorem c5_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 0, 0, 1, 0, 1] = true := by decide +kernel
theorem c6_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 0, 0, 1, 1, 0] = true := by decide +kernel
theorem c7_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 0, 0, 1, 1, 1] = true := by decide +kernel
theorem c8_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 0, 1, 0, 0, 0] = true := by decide +kernel
theorem c9_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 0, 1, 0, 0, 1] = true := by decide +kernel
theorem c10_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 0, 1, 0, 1, 0] = true := by decide +kernel
theorem c11_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 0, 1, 0, 1, 1] = true := by decide +kernel
theorem c12_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 0, 1, 1, 0, 0] = true := by decide +kernel
theorem c13_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 0, 1, 1, 0, 1] = true := by decide +kernel
theorem c14_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 0, 1, 1, 1, 0] = true := by decide +kernel
theorem c15_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 0, 1, 1, 1, 1] = true := by decide +kernel
theorem c16_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 1, 0, 0, 0, 0] = true := by decide +kernel
theorem c17_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 1, 0, 0, 0, 1] = true := by decide +kernel
theorem c18_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 1, 0, 0, 1, 0] = true := by decide +kernel
theorem c19_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 1, 0, 0, 1, 1] = true := by decide +kernel
theorem c20_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 1, 0, 1, 0, 0] = true := by decide +kernel
theorem c21_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 1, 0, 1, 0, 1] = true := by decide +kernel
theorem c22_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 1, 0, 1, 1, 0] = true := by decide +kernel
theorem c23_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 1, 0, 1, 1, 1] = true := by decide +kernel
theorem c24_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 1, 1, 0, 0, 0] = true := by decide +kernel
theorem c25_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 1, 1, 0, 0, 1] = true := by decide +kernel
theorem c26_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 1, 1, 0, 1, 0] = true := by decide +kernel
theorem c27_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 1, 1, 0, 1, 1] = true := by decide +kernel
theorem c28_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 1, 1, 1, 0, 0] = true := by decide +kernel
theorem c29_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 1, 1, 1, 0, 1] = true := by decide +kernel
theorem c30_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 1, 1, 1, 1, 0] = true := by decide +kernel
theorem c31_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [0, 1, 1, 1, 1, 1] = true := by decide +kernel
theorem c32_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 0, 0, 0, 0, 0] = true := by decide +kernel
theorem c33_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 0, 0, 0, 0, 1] = true := by decide +kernel
theorem c34_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 0, 0, 0, 1, 0] = true := by decide +kernel
theorem c35_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 0, 0, 0, 1, 1] = true := by decide +kernel
theorem c36_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 0, 0, 1, 0, 0] = true := by decide +kernel
theorem c37_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 0, 0, 1, 0, 1] = true := by decide +kernel
theorem c38_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 0, 0, 1, 1, 0] = true := by decide +kernel
theorem c39_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 0, 0, 1, 1, 1] = true := by decide +kernel
theorem c40_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 0, 1, 0, 0, 0] = true := by decide +kernel
theorem c41_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 0, 1, 0, 0, 1] = true := by decide +kernel
theorem c42_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 0, 1, 0, 1, 0] = true := by decide +kernel
theorem c43_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 0, 1, 0, 1, 1] = true := by decide +kernel
theorem c44_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 0, 1, 1, 0, 0] = true := by decide +kernel
theorem c45_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 0, 1, 1, 0, 1] = true := by decide +kernel
theorem c46_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 0, 1, 1, 1, 0] = true := by decide +kernel
theorem c47_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 0, 1, 1, 1, 1] = true := by decide +kernel
theorem c48_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 1, 0, 0, 0, 0] = true := by decide +kernel
theorem c49_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 1, 0, 0, 0, 1] = true := by decide +kernel
theorem c50_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 1, 0, 0, 1, 0] = true := by decide +kernel
theorem c51_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 1, 0, 0, 1, 1] = true := by decide +kernel
theorem c52_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 1, 0, 1, 0, 0] = true := by decide +kernel
theorem c53_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 1, 0, 1, 0, 1] = true := by decide +kernel
theorem c54_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 1, 0, 1, 1, 0] = true := by decide +kernel
theorem c55_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 1, 0, 1, 1, 1] = true := by decide +kernel
theorem c56_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 1, 1, 0, 0, 0] = true := by decide +kernel
theorem c57_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 1, 1, 0, 0, 1] = true := by decide +kernel
theorem c58_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 1, 1, 0, 1, 0] = true := by decide +kernel
theorem c59_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 1, 1, 0, 1, 1] = true := by decide +kernel
theorem c60_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 1, 1, 1, 0, 0] = true := by decide +kernel
theorem c61_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 1, 1, 1, 0, 1] = true := by decide +kernel
theorem c62_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 1, 1, 1, 1, 0] = true := by decide +kernel
theorem c63_ORD_w8_s2 : checkOneF net_ORD_w8_s2 (1/1000 : ℚ) [1, 1, 1, 1, 1, 1] = true := by decide +kernel

theorem all_ORD_w8_s2 : checkNF 6 net_ORD_w8_s2 (1/1000 : ℚ) = true := by
  rw [checkNF, show boolVecs 6 = [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 1], [0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 1, 1], [0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 1, 0], [0, 0, 1, 0, 1, 1], [0, 0, 1, 1, 0, 0], [0, 0, 1, 1, 0, 1], [0, 0, 1, 1, 1, 0], [0, 0, 1, 1, 1, 1], [0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1], [0, 1, 0, 0, 1, 0], [0, 1, 0, 0, 1, 1], [0, 1, 0, 1, 0, 0], [0, 1, 0, 1, 0, 1], [0, 1, 0, 1, 1, 0], [0, 1, 0, 1, 1, 1], [0, 1, 1, 0, 0, 0], [0, 1, 1, 0, 0, 1], [0, 1, 1, 0, 1, 0], [0, 1, 1, 0, 1, 1], [0, 1, 1, 1, 0, 0], [0, 1, 1, 1, 0, 1], [0, 1, 1, 1, 1, 0], [0, 1, 1, 1, 1, 1], [1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1], [1, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 1], [1, 0, 0, 1, 1, 0], [1, 0, 0, 1, 1, 1], [1, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 1], [1, 0, 1, 0, 1, 0], [1, 0, 1, 0, 1, 1], [1, 0, 1, 1, 0, 0], [1, 0, 1, 1, 0, 1], [1, 0, 1, 1, 1, 0], [1, 0, 1, 1, 1, 1], [1, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1], [1, 1, 0, 0, 1, 0], [1, 1, 0, 0, 1, 1], [1, 1, 0, 1, 0, 0], [1, 1, 0, 1, 0, 1], [1, 1, 0, 1, 1, 0], [1, 1, 0, 1, 1, 1], [1, 1, 1, 0, 0, 0], [1, 1, 1, 0, 0, 1], [1, 1, 1, 0, 1, 0], [1, 1, 1, 0, 1, 1], [1, 1, 1, 1, 0, 0], [1, 1, 1, 1, 0, 1], [1, 1, 1, 1, 1, 0], [1, 1, 1, 1, 1, 1]] from rfl]
  simp only [List.all_cons, List.all_nil, c0_ORD_w8_s2, c1_ORD_w8_s2, c2_ORD_w8_s2, c3_ORD_w8_s2, c4_ORD_w8_s2, c5_ORD_w8_s2, c6_ORD_w8_s2, c7_ORD_w8_s2, c8_ORD_w8_s2, c9_ORD_w8_s2, c10_ORD_w8_s2, c11_ORD_w8_s2, c12_ORD_w8_s2, c13_ORD_w8_s2, c14_ORD_w8_s2, c15_ORD_w8_s2, c16_ORD_w8_s2, c17_ORD_w8_s2, c18_ORD_w8_s2, c19_ORD_w8_s2, c20_ORD_w8_s2, c21_ORD_w8_s2, c22_ORD_w8_s2, c23_ORD_w8_s2, c24_ORD_w8_s2, c25_ORD_w8_s2, c26_ORD_w8_s2, c27_ORD_w8_s2, c28_ORD_w8_s2, c29_ORD_w8_s2, c30_ORD_w8_s2, c31_ORD_w8_s2, c32_ORD_w8_s2, c33_ORD_w8_s2, c34_ORD_w8_s2, c35_ORD_w8_s2, c36_ORD_w8_s2, c37_ORD_w8_s2, c38_ORD_w8_s2, c39_ORD_w8_s2, c40_ORD_w8_s2, c41_ORD_w8_s2, c42_ORD_w8_s2, c43_ORD_w8_s2, c44_ORD_w8_s2, c45_ORD_w8_s2, c46_ORD_w8_s2, c47_ORD_w8_s2, c48_ORD_w8_s2, c49_ORD_w8_s2, c50_ORD_w8_s2, c51_ORD_w8_s2, c52_ORD_w8_s2, c53_ORD_w8_s2, c54_ORD_w8_s2, c55_ORD_w8_s2, c56_ORD_w8_s2, c57_ORD_w8_s2, c58_ORD_w8_s2, c59_ORD_w8_s2, c60_ORD_w8_s2, c61_ORD_w8_s2, c62_ORD_w8_s2, c63_ORD_w8_s2, Bool.and_self]

theorem cert_ORD_w8_s2 : SpecN 6 net_ORD_w8_s2 (1/1000 : ℚ) :=
  certF 6 net_ORD_w8_s2 (1/1000 : ℚ) all_ORD_w8_s2

#print axioms cert_ORD_w8_s2
