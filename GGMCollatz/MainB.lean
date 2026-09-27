import GGMCollatz.NatDen.Main
import GGMCollatz.General

/-!
# The top level of (B): the whole family of GGM's Theorem 1.3

* `Family.mainB` (`NatDen/Main.lean`): for the families with (d) and `q > p`, a power rate for the natural density,
  assuming only `MatveevHyp F.p F.q`.
* `FamilyGen.mainB_gen_of` (`General.lean`): (B) for the families without (d) and `q > p`, from (B) for the families
  with (d) (the conjugation `C(dN) = d C*(N)` reduces to a family with the same `p, q`, so the hypothesis
  `MatveevHyp` carries over unchanged).

Together these give `FamilyGen.mainB_gen`: for every family of GGM's Theorem 1.3 ((a)(b)(c)), under
`MatveevHyp G.p G.q`, `#{N ≤ X | C_min(N) > N₀} ≤ K X N₀^{-c}`. `MatveevHyp` is the case of two logarithms of
Matveev (2000) Cor. 2.3, and for `p, q ≥ 2` it is not stronger than the original (`Matveev.hyp_of_B13` in
`MatveevBridge.lean`).
-/

namespace GGMCollatz

namespace FamilyGen

/-- **The top level of (B) (the whole family)**: for every family of GGM's Theorem 1.3, a power rate for the
natural density, assuming only `MatveevHyp`. -/
theorem mainB_gen (G : FamilyGen) (hM : MatveevHyp G.p G.q) : G.mainB_gen_statement :=
  FamilyGen.mainB_gen_of (fun F hF => F.mainB hF) G hM

end FamilyGen

end GGMCollatz
