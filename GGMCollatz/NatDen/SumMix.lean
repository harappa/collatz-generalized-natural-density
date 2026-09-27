import GGMCollatz.NatDen.Statements
import GGMCollatz.Tao.Sec6.FromDecay
import GGMCollatz.NatDen.SumMixC.Compose
import GGMCollatz.NatDen.SumMixA.Main
import GGMCollatz.NatDen.SumMixB.Large

/-!
# (SUMMIX) Mixing at fine scales conditioned on the valuation sum (Proposition 6.12 of the paper)

* `summixA_of`: (a) the conditioned oscillation (the decomposition and key identity of GGM §5, Proposition 6.7 of the paper for the head
  factor, telescoping).
* `summixB_of`: (b) stability at coarse scales (the Radon–Nikodym derivative is bounded by the local limit theorem).
* `summixC_of_AB`: (c) the product formula (combining (a) and (b)).
-/

namespace GGMCollatz

namespace ND

variable (F : Family)

/-- **Proposition 6.12 (a) of the paper**. -/
theorem summixA_of (hcf : sumcf_statement F) (hL : lclt_statement F.p) : summixA_statement F :=
  SumMixAAux.summixA F hcf hL

/-- **Proposition 6.12 (b) of the paper**. -/
theorem summixB_of (hL : lclt_statement F.p) : summixB_statement F := by
  -- reduce the left-hand side to `Σ_σ P(s_m = σ)|P(s_k = s - σ) - P(s_n = s)|` (`lhs_le_reduced`, `n = m + k`)
  -- and apply the negative binomial bound `reduced_bound` (local limit theorem, tails, exponential moments).
  intro C hC
  obtain ⟨K, hK, hbound⟩ := SumMixBAux.reduced_bound F.two_le_p hL C hC
  refine ⟨K, hK, ?_⟩
  intro n m hmn hn2 hm4 hm9 s hs
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have h2 := hbound (m + k) m hmn hn2 hm4 hm9 s hs
  rw [Nat.add_sub_cancel_left] at h2
  exact (SumMixBAux.lhs_le_reduced F m k hmn s).trans h2

/-- **Proposition 6.12 (c) of the paper**: from (a) and (b). -/
theorem summixC_of_AB (hA : summixA_statement F) (hB : summixB_statement F) :
    summixC_statement F :=
  SumMixCAux.summixC_of_AB' F hA hB

end ND

end GGMCollatz
