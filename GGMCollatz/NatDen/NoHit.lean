import GGMCollatz.NatDen.NoHitAux

/-!
# (D.1) The probability of not hitting, for the uniform window

`noHit`: from GGM Prop. 3.1 (`Family.prop33`, applied to the equidistribution of residues in the uniform window) and
the deterministic descent that brings the orbit below `x` once the valuation sum is large
(`passes_of_large_val` in `Tao/Sec5/FirstPassage.lean`). This is the uniform-window version of `nonescape` on the
logarithmic side. The lemmas are in `NatDen/NoHitAux.lean` (namespace `ND.NH`):

* the form independent of the window measure, `NH.noPass_of_equidist` (the bodies of `Family.valuation_law` and
  `Family.nonescape` rewritten for any `X` supported on `ℕ_p ∩ [1, x^{θ₀}]` whose `ℓ¹` distance modulo `p^k`, for
  `p^{2k+1} ≤ x`, is at most `10 p^{-k}`);
* the equidistribution of the uniform window `NH.unifWin_equidist` (`ℓ¹ ≤ 10 p^k / #W`) and the number of window
  points `NH.card_window_ge` (`#W ≥ (hi-lo)/μ - 2`).

Difference from the accompanying paper: the paper writes `k₀ = ⌈2μn₀⌉` and the window top `x^{α³}`; here we use the
same `n₀ = ⌊log x/(5 log q)⌋`, `k = ⌈(μ + 1/4)n₀⌉`, `γ = (λ + μ)/2` (`gammaLow`) as the logarithmic side (`Tao/Sec5`),
and take `α₀ = √θ₀` so that the top of the window `[x^α, x^{α²}]` is at most `x^{θ₀}`
(`θ₀ = 1 + d/(20 log q)`, `Family.thetaMax`).
-/

namespace GGMCollatz

namespace ND

variable (F : Family)

/-- **(D.1)**: `α₀ = √θ₀` (`α² ≤ θ₀`, so the window top `x^{α²}` lies in the range of the deterministic descent).
The constants `c, K` are those of `NH.noPass_of_equidist` (independent of `α`). For large `x` the window
`W = ℕ_p ∩ [x^α, x^{α²}]` has at least `x` points (`NH.card_window_ge`), and modulo `p^k` with `p^{2k+1} ≤ x`
the `ℓ¹` distance is `10 p^k / #W ≤ 10 p^{-k}` (`NH.unifWin_equidist`). -/
theorem noHit : noHit_statement F := by
  obtain ⟨c, K, hc, hK, hgen⟩ := NH.noPass_of_equidist F
  have hθ := F.one_lt_thetaMax
  refine ⟨Real.sqrt F.thetaMax, ?_, fun α hα hαle => ⟨c, K, hc, hK, ?_⟩⟩
  · rw [Real.lt_sqrt zero_le_one]; simpa using hθ
  have hα0 : 0 ≤ α := by linarith
  have hαα : α * α ≤ F.thetaMax := by
    calc α * α ≤ Real.sqrt F.thetaMax * Real.sqrt F.thetaMax :=
          mul_le_mul hαle hαle hα0 (Real.sqrt_nonneg _)
      _ = F.thetaMax := Real.mul_self_sqrt (by linarith)
  have hα1 : 0 < α - 1 := by linarith
  have hμ := F.mu_pos
  have hμ2 := F.mu_le_two
  filter_upwards [hgen, (tendsto_rpow_atTop hα1).eventually_ge_atTop (4 : ℝ),
    Filter.eventually_ge_atTop (4 : ℝ)] with x hx hx4 hx4'
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  set y := x ^ α with hy
  have hxy : x ≤ y := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ α := Real.rpow_le_rpow_of_exponent_le hx1 hα.le
  have hy0 : 0 < y := by linarith
  have hy4 : 4 ≤ y ^ (α - 1) := le_trans hx4 (Real.rpow_le_rpow hx0.le hxy hα1.le)
  have hsplit : y ^ α = y * y ^ (α - 1) := by
    rw [← Real.rpow_one_add' hy0.le (by linarith)]; ring_nf
  have hhi : 4 * y ≤ y ^ α := by rw [hsplit]; nlinarith
  have hle : y ≤ y ^ α := by linarith
  have hW : (F.logWindow y (y ^ α)).Nonempty := F.logWindow_nonempty_of (by linarith) (by linarith)
  -- the window has at least `x` points
  have hcard := NH.card_window_ge F hy0 hle
  have hWx : x ≤ ((F.logWindow y (y ^ α)).card : ℝ) := by
    have h1 : (y ^ α - y) / 2 ≤ (y ^ α - y) / F.mu :=
      div_le_div_of_nonneg_left (by linarith) hμ hμ2
    linarith
  -- the window top is at most `x^{θ₀}`
  have hwθ : y ^ α ≤ x ^ F.thetaMax := by
    rw [hy, ← Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx1 hαα
  apply hx
  · intro N hN
    obtain ⟨hNp, _, hNy⟩ := (F.mem_logWindow_iff).mp (NH.mem_window_of_mem_support F hW hN)
    exact ⟨hNp, le_trans hNy hwθ⟩
  · intro k hk hpk
    refine le_trans (NH.unifWin_equidist F (by linarith) hle hW hk) ?_
    have hpkR : (0 : ℝ) < (F.p : ℝ) ^ k := pow_pos F.p_real_pos k
    have hWpos : (0 : ℝ) < (F.logWindow y (y ^ α)).card := by exact_mod_cast hW.card_pos
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, div_le_iff₀ hWpos]
    -- `p^k · p^k ≤ p^{2k+1} ≤ x ≤ #W`
    have h2 : (F.p : ℝ) ^ k * (F.p : ℝ) ^ k ≤ (F.logWindow y (y ^ α)).card := by
      have e : (F.p : ℝ) ^ k * (F.p : ℝ) ^ k ≤ (F.p : ℝ) ^ (2 * k + 1) := by
        rw [← pow_add, show k + k = 2 * k by ring]
        exact pow_le_pow_right₀ F.one_lt_p_real.le (by omega)
      linarith
    calc 10 * (F.p : ℝ) ^ k = 10 * ((F.p : ℝ) ^ k)⁻¹ * ((F.p : ℝ) ^ k * (F.p : ℝ) ^ k) := by
          field_simp
      _ ≤ 10 * ((F.p : ℝ) ^ k)⁻¹ * (F.logWindow y (y ^ α)).card :=
          mul_le_mul_of_nonneg_left h2 (by positivity)

end ND

end GGMCollatz
