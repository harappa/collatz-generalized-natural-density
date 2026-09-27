import GGMCollatz.NatDen.Irr
import GGMCollatz.NatDen.Kron
import GGMCollatz.NatDen.LCLT
import GGMCollatz.NatDen.SumCF
import GGMCollatz.NatDen.SumMix
import GGMCollatz.NatDen.NoHit
import GGMCollatz.NatDen.UProf
import GGMCollatz.NatDen.TV
import GGMCollatz.NatDen.StarB

/-!
# The top level of (B)

`GGMCollatz.Family.mainB`: from the single hypothesis `MatveevHyp F.p F.q` (the two-logarithm case of Matveev (2000) Cor. 2.3),
the power rate in natural density `#{N ≤ X | C_min(N) > N₀} ≤ K X N₀^{-c}` for every member of the GGM family (`mainB_statement`).

Assembly (the intermediate statements are in `NatDen/Statements.lean`):

```
MatveevHyp ─▶ (IRR) ─▶ (KRON) ─▶ (KRON-W) ─────────────┐
(LCLT) ─▶ (SUMCF) ─▶ (SUMMIX a) ─┐                      │
(LCLT) ─▶ (SUMMIX b) ────────────┴▶ (SUMMIX c) ─────────┴▶ (UPROF) ─▶ (D.2') ─┐
GGM Prop. 3.1 ─▶ (D.1) ──────────────────────────────────────────────────────┴▶ (B)
```
-/

namespace GGMCollatz

namespace ND

variable (F : Family)

/-- Assembly of Sections 6 and 7 of the paper: (D.2') (Proposition 7.2 of the paper) from `MatveevHyp`. -/
theorem tvPass_of_matveev (hM : MatveevHyp F.p F.q) : tvPass_statement F := by
  obtain ⟨c, μ, hc, hμ, hirr⟩ := irr_of_matveev F hM
  have hkw : kronW_statement (lam F) μ := kronW_of_kron (kron hc hμ hirr)
  have hL : lclt_statement F.p := lclt F.two_le_p
  have hC : summixC_statement F :=
    summixC_of_AB F (summixA_of F (sumcf_of_lclt F hL) hL) (summixB_of F hL)
  exact tvPass_of_uprof F (uprof_of_parts F hμ hkw hL hC)

end ND

namespace Family

/-- **The top-level statement of (B)** (Theorem 8.4 of the paper): assuming only `MatveevHyp`, there are `K, c > 0` such that
for all `N₀ ≥ 1` and `X ≥ 1`, `#{N ≤ X | C_min(N) > N₀} ≤ K X N₀^{-c}`. -/
theorem mainB (F : GGMCollatz.Family) (hM : GGMCollatz.MatveevHyp F.p F.q) : F.mainB_statement :=
  ND.mainB_of_D F (ND.noHit F) (ND.tvPass_of_matveev F hM)

end Family

end GGMCollatz
