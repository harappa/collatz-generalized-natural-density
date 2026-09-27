import GGMCollatz.NatDen.Statements
import GGMCollatz.Tao.Sec7.Decay
import GGMCollatz.NatDen.SumCF.Joint
import GGMCollatz.NatDen.SumCF.Lower

/-!
# (SUMCF) Decay of the characteristic function conditioned on the valuation sum (Proposition 6.7 of the paper)

The pairing argument of GGM §6 Step 1 (`cexpect_pairing`) is a pointwise bound conditioned on the pair sums `𝒫_j`,
so multiplying by the event `{s_n = s}` (which is determined by the pair sums) keeps the same majorant. The expectation
of the majorant is `≪ n^{-A}` by GGM Thm. 1.9 (`renewal_white` in Sec7). Then divide by the local-limit lower bound
`P(s_n = s) ≥ c n^{-1/2-C'}`.

Assembly (auxiliary lemmas in `NatDen/SumCF/`, namespace `GGMCollatz.ND.SumCFAux`):

```
Σ_Y P(𝒮_n = Y, s_n = s) e(-ξY/q^n) = E[χ(𝒮_n) 1_{s_n = s}]           (sum_jp_chi_eq)
‖E[χ(𝒮_n) 1_{s_n = s}]‖ ≤ E_{b ~ Pascal^{n/2}} ∏_j ‖f(…)‖ ≤ C₁ n^{-A'}  (cexpect_h_decay)
P(s_n = s) ≥ c₀ n^{-(1/2 + C²/(2σ²))} (n ≥ n₀)                          (nb_lower, from (LCLT))
‖…‖ ≤ P(s_n = s) (small n)                                              (norm_sum_jp_chi_le)
```
`A' = A + 1/2 + C²/(2σ²)`, `K = max(n₀^A, C₁/c₀)`.
-/

namespace GGMCollatz

namespace ND

variable (F : Family)

/-- **Proposition 6.7 of the paper** (from the local limit theorem). -/
theorem sumcf_of_lclt (hL : lclt_statement F.p) : sumcf_statement F := by
  intro A C hA hC
  have hp := F.two_le_p
  obtain ⟨n₀, hn₀, c₀, hc₀, hlow⟩ := SumCFAux.nb_lower hp hL C hC
  set β : ℝ := C ^ 2 / (2 * sig2 F.p) with hβ
  have hσ := SumCFAux.sig2_pos hp
  have hβ0 : 0 ≤ β := div_nonneg (sq_nonneg C) (by linarith)
  obtain ⟨C₁, hC₁, hdec⟩ := SumCFAux.cexpect_h_decay F (A + (1 / 2 + β)) (by linarith)
  refine ⟨max ((n₀ : ℝ) ^ A) (C₁ / c₀), lt_max_of_lt_right (by positivity), ?_⟩
  intro n hn2 s hs ξ hξ
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnb0 : 0 ≤ nb F.p n s := ENNReal.toReal_nonneg
  have hnA : 0 ≤ (n : ℝ) ^ (-A) := Real.rpow_nonneg hnR.le _
  rcases lt_or_ge n n₀ with hsmall | hbig
  · -- small `n`: the trivial bound `‖…‖ ≤ P(s_n = s)`
    have h1 : (1 : ℝ) ≤ (n₀ : ℝ) ^ A * (n : ℝ) ^ (-A) := by
      have hle : (n : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hsmall.le
      have h2 : (1 : ℝ) = (n : ℝ) ^ A * (n : ℝ) ^ (-A) := by
        rw [← Real.rpow_add hnR, add_neg_cancel, Real.rpow_zero]
      rw [h2]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hnR.le hle hA.le) hnA
    calc ‖∑ Y : ZMod (F.q ^ n), (jp F n Y s : ℂ) * eC (-(ξ.val * Y.val : ℚ) / (F.q : ℚ) ^ n)‖
        ≤ nb F.p n s := SumCFAux.norm_sum_jp_chi_le F n s ξ
      _ = 1 * nb F.p n s := (one_mul _).symm
      _ ≤ ((n₀ : ℝ) ^ A * (n : ℝ) ^ (-A)) * nb F.p n s := mul_le_mul_of_nonneg_right h1 hnb0
      _ ≤ max ((n₀ : ℝ) ^ A) (C₁ / c₀) * (n : ℝ) ^ (-A) * nb F.p n s := by
          refine mul_le_mul_of_nonneg_right ?_ hnb0
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hnA
  · -- large `n`: decay of the pair majorant and the lower bound on `P(s_n = s)`
    have hlo := hlow n hbig s hs
    calc ‖∑ Y : ZMod (F.q ^ n), (jp F n Y s : ℂ) * eC (-(ξ.val * Y.val : ℚ) / (F.q : ℚ) ^ n)‖
        = ‖(PMF.iid (stepLaw F.p) n).cexpect fun v =>
            F.chiC n ξ.val (F.offsetIn (F.q ^ n) v) * SumCFAux.indC s (∑ i, (v i).1)‖ := by
          rw [SumCFAux.sum_jp_chi_eq]
      _ ≤ C₁ * (n : ℝ) ^ (-(A + (1 / 2 + β))) :=
          hdec n hn1 ξ hξ (SumCFAux.indC s) (SumCFAux.norm_indC_le s)
      _ = (C₁ / c₀) * (n : ℝ) ^ (-A) * (c₀ * (n : ℝ) ^ (-(1 / 2 + β))) := by
          rw [neg_add, Real.rpow_add hnR]
          field_simp
      _ ≤ (C₁ / c₀) * (n : ℝ) ^ (-A) * nb F.p n s :=
          mul_le_mul_of_nonneg_left hlo (by positivity)
      _ ≤ max ((n₀ : ℝ) ^ A) (C₁ / c₀) * (n : ℝ) ^ (-A) * nb F.p n s := by
          refine mul_le_mul_of_nonneg_right ?_ hnb0
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hnA

end ND

end GGMCollatz
