import GGMCollatz.Assembly.Step
import GGMCollatz.Assembly.LogDensity

/-!
# The assembly of (A) (see the accompanying paper)

Assuming the form `prop35_statement` of GGM's Proposition 3.5, we prove

* `oneStep_of_prop35`: the one-step recursion (Lemma 5.3 of the paper),
* `mainA_of_prop35`: the top-level statement of (A) (Theorem 5.7 (ii) of the paper).

The ingredients are the six files in `GGMCollatz/Assembly/` (auxiliary lemmas live in the namespace
`GGMCollatz.Asm`):

* `Prob.lean`: expectations of indicator functions, pushforward laws, total variation (derived from
  tao-collatz's `abs_expect_indicator_sub_le_dTV`).
* `Orbit.lean`: attainment of `S_min`, `C_min`, the decomposition by first passage, comparison of the
  orbits of `S`, `C`, `C~`, and `N = p^k N'`.
* `Step.lean`: Lemma 5.3 of the paper (window width `α = 1 + min(c, 1)/3`).
* `Window.lean`: the ratio form of window probabilities, a lower bound for the window mass, an upper
  bound for the mass of bad points from the seed, and the estimate of the bottom window ((o)(i)).
* `Uniform.lean`: a power rate uniform over windows (Theorem 5.7 (i) of the paper). A generalization of
  the assembly of the companion manuscript for the Collatz map.
* `LogDensity.lean`: the logarithmic-density corollary, via a covering by windows and the decomposition by
  powers of `p`.

The seed theorem (`GGMCollatz.Family.seed`) is used as already proved.
-/

namespace GGMCollatz

namespace Family

/-- **Lemma 5.3 of the paper**: the one-step recursion from the form of GGM's Proposition 3.5. -/
theorem oneStep_of_prop35 (F : Family) (h : F.prop35_statement) : F.oneStep_statement :=
  Asm.oneStep_of_prop35' F h

/-- **(A)** (Theorem 5.7 (ii) of the paper): from the form of GGM's Proposition 3.5, there are
`K, c' > 0` such that for all `N₀ ≥ 1` and `x ≥ 3`, `∑_{N ≤ x, C_min(N) > N₀} 1/N ≤ K N₀^{-c'} log x`. -/
theorem mainA_of_prop35 (F : Family) (h : F.prop35_statement) : F.mainA_statement := by
  obtain ⟨α, c, Cs, Xs, hα, hc, hCs, hS⟩ := Asm.stepHyp_of_oneStep F (oneStep_of_prop35 F h)
  obtain ⟨K, c', hK, hc', hU⟩ := Asm.uniform F hα hc hCs hS
  have hα1 : 0 < α - 1 := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨K3, hK3def⟩ : ∃ K3 : ℝ,
      K3 = 1 / ((α - 1) * Real.log 2) + 1 / Real.log 3 + α ^ 2 / (α - 1) := ⟨_, rfl⟩
  have hK3 : 0 ≤ K3 := by rw [hK3def]; positivity
  have hp1 : (1 : ℝ) < F.p := by exact_mod_cast F.one_lt_p
  have hpp : 0 ≤ (F.p : ℝ) / ((F.p : ℝ) - 1) := div_nonneg (by linarith) (by linarith)
  refine ⟨max ((F.p : ℝ) / ((F.p : ℝ) - 1) * (K * K3)) 1, c',
    lt_of_lt_of_le one_pos (le_max_right _ _), hc', ?_⟩
  intro N₀ hN₀ x hx
  have h1 := Asm.logDensity_C F (N₀ := N₀) ⌊x⌋₊
  have h2 := Asm.logDensity_Np F hα hK.le hU hN₀ hx
  rw [← hK3def] at h2
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hNp : 0 ≤ (N₀ : ℝ) ^ (-c') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  simp only [one_div]
  calc ∑ N ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun N => N₀ < F.Cmin N), (N : ℝ)⁻¹
      ≤ (F.p : ℝ) / ((F.p : ℝ) - 1) * (K * K3 * (N₀ : ℝ) ^ (-c') * Real.log x) :=
        le_trans h1 (mul_le_mul_of_nonneg_left h2 hpp)
    _ = ((F.p : ℝ) / ((F.p : ℝ) - 1) * (K * K3)) * (N₀ : ℝ) ^ (-c') * Real.log x := by ring
    _ ≤ max ((F.p : ℝ) / ((F.p : ℝ) - 1) * (K * K3)) 1 * (N₀ : ℝ) ^ (-c') * Real.log x := by
        gcongr; exact le_max_left _ _

end Family

end GGMCollatz
