import GGMCollatz.MainB
import GGMCollatz.Corollary
import GGMCollatz.MatveevBridge

/-! Axiom report for the main theorems (run: `lake env lean verify/Axioms.lean`). -/

#check @GGMCollatz.FamilyGen.mainA_gen
#check @GGMCollatz.FamilyGen.mainB_gen
#check @GGMCollatz.FamilyGen.corollaries
#check @GGMCollatz.FamilyGen.density_one
#check @GGMCollatz.Family.mainA
#check @GGMCollatz.Family.mainB
#check @GGMCollatz.Matveev.hyp_of_B13
#print axioms GGMCollatz.FamilyGen.mainA_gen
#print axioms GGMCollatz.FamilyGen.mainB_gen
#print axioms GGMCollatz.FamilyGen.corollaries
#print axioms GGMCollatz.FamilyGen.density_one
#print axioms GGMCollatz.Family.mainA
#print axioms GGMCollatz.Family.mainB
#print axioms GGMCollatz.Family.prop33
#print axioms GGMCollatz.Family.prop35
#print axioms GGMCollatz.Family.prop51
#print axioms GGMCollatz.Matveev.hyp_of_B13
