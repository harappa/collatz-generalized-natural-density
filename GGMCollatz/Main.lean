import GGMCollatz.Assembly
import GGMCollatz.Tao.Syracuse.ValuationDist
import GGMCollatz.Tao.Sec6.FromDecay
import GGMCollatz.Tao.Sec5.Stabilization
import GGMCollatz.Tao.Sec7.Decay

/-!
# The top level of (A): the form with only GGM's Proposition 5.1 left

Connects the finished parts: Proposition 3.1 (`prop33`), Proposition 5.1 ⇒ 4.1 (`prop41_of_prop51`),
Propositions 3.1 ∧ 4.1 ⇒ 3.5 (`prop35_of_inter`), and Proposition 3.5 ⇒ (A) (`mainA_of_prop35`, using the seed
`seed`). GGM's Proposition 5.1 (decay of the characteristic function) is proved in Sec7 (`prop51`), so **the
top-level statement `mainA` of (A) holds with no hypotheses** (Mathlib only).
-/

namespace GGMCollatz

namespace Family

/-- **The top-level statement of (A) follows from GGM's Proposition 5.1.** -/
theorem mainA_of_prop51 (F : Family) (h51 : F.prop51_statement) : F.mainA_statement :=
  F.mainA_of_prop35 (F.prop35_of_inter F.prop33 (F.prop41_of_prop51 h51))

/-- Proposition 3.5 also follows from Proposition 5.1. -/
theorem prop35_of_prop51 (F : Family) (h51 : F.prop51_statement) : F.prop35_statement :=
  F.prop35_of_inter F.prop33 (F.prop41_of_prop51 h51)

/-- **(A) The top-level statement of Theorem 5.7 (ii) of the paper (no hypotheses)**: for every GGM family there are `K, c' > 0`
such that for all `N₀ ≥ 1` and `x ≥ 3`, `∑_{N ≤ x, C_min(N) > N₀} 1/N ≤ K N₀^{-c'} log x`. -/
theorem mainA (F : Family) : F.mainA_statement := F.mainA_of_prop51 F.prop51

/-- GGM's Proposition 3.5 (in the form used here, `prop35_statement`) also holds with no hypotheses. -/
theorem prop35 (F : Family) : F.prop35_statement := F.prop35_of_prop51 F.prop51

/-- The one-step recursion (Lemma 5.3 of the paper) also holds with no hypotheses. -/
theorem oneStep (F : Family) : F.oneStep_statement := F.oneStep_of_prop35 F.prop35

end Family

end GGMCollatz
