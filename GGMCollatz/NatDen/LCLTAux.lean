import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Auxiliaries for (LCLT): two-sided Stirling bounds, the cubic remainder of `log(1+t)`, and a logarithmic identity

Lemmas of real analysis, independent of `p` and of probabilities, used in `LCLT.lean`.

* `stir x = x log x - x + log(2πx)/2` and `|log k! - stir k| ≤ 1/(12k)` (`k ≥ 1`; the lower side is Mathlib's
  `Stirling.le_log_factorial_stirling`; the upper side uses Robbins' bound `Stirling.log_stirlingSeq_sdiff_le`, from which
  `log S(k) - 1/(12k)` is increasing and converges to `log √π`).
* `phi t = (1+t)log(1+t) - t - t²/2` with `|phi t| ≤ 4|t|³` and `|log(1+t)| ≤ 2|t|` (`|t| ≤ 1/2`).
* `lclt_log_identity`: an identity, at the level of the Stirling main parts, for the difference between the logarithm of the
  negative binomial and the logarithm of the Gaussian main term.
-/

open Real

namespace GGMCollatz

namespace ND

namespace LCLTAux

/-- The Stirling main part `x log x - x + log(2πx)/2`. -/
noncomputable def stir (x : ℝ) : ℝ := x * Real.log x - x + Real.log (2 * π * x) / 2

/-- `log S(k) ≤ log √π + 1/(12k)` (`k ≥ 1`, from Robbins' bound). -/
theorem log_stirlingSeq_le (k : ℕ) (hk : 1 ≤ k) :
    Real.log (Stirling.stirlingSeq k) ≤ Real.log (√π) + 1 / (12 * (k : ℝ)) := by
  set a : ℕ → ℝ := fun j =>
    Real.log (Stirling.stirlingSeq (j + 1)) - 1 / (12 * ((j : ℝ) + 1)) with ha
  have hmono : Monotone a := by
    apply monotone_nat_of_le_succ
    intro j
    have h := Stirling.log_stirlingSeq_sdiff_le (j + 1)
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have e : (1 : ℝ) / (12 * ((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) + 1))
        = 1 / (12 * ((j : ℝ) + 1)) - 1 / (12 * (((j + 1 : ℕ) : ℝ) + 1)) := by
      push_cast
      field_simp
      ring
    rw [e] at h
    simp only [ha]
    push_cast at h ⊢
    linarith
  have hlim : Filter.Tendsto a Filter.atTop (nhds (Real.log (√π))) := by
    have h1 : Filter.Tendsto (fun j : ℕ => Real.log (Stirling.stirlingSeq (j + 1)))
        Filter.atTop (nhds (Real.log √π)) :=
      ((Real.continuousAt_log (by positivity)).tendsto).comp
        (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (Filter.tendsto_add_atTop_nat 1))
    have h2 : Filter.Tendsto (fun j : ℕ => 1 / (12 * ((j : ℝ) + 1))) Filter.atTop (nhds 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / 12 : ℝ)
      rw [mul_zero] at this
      refine this.congr (fun j => ?_)
      field_simp
    have := h1.sub h2
    rw [sub_zero] at this
    exact this
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have := hmono.ge_of_tendsto hlim j
  simp only [ha] at this
  push_cast
  linarith

/-- The formula for `log S(k)` written in terms of `stir`. -/
theorem log_factorial_eq (k : ℕ) (hk : 1 ≤ k) :
    Real.log (k.factorial : ℝ) = Real.log (Stirling.stirlingSeq k) + stir k - Real.log (√π) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Stirling.log_stirlingSeq_formula, stir, Real.log_sqrt Real.pi_pos.le,
    Real.log_mul (x := 2 * π) (by positivity) hk'.ne',
    Real.log_mul (x := 2) (by norm_num) Real.pi_pos.ne',
    Real.log_mul (x := 2) (by norm_num) hk'.ne', Real.log_div hk'.ne' (Real.exp_pos 1).ne', Real.log_exp]
  ring

/-- **Two-sided Stirling**: `0 ≤ log k! - stir k ≤ 1/(12k)` (`k ≥ 1`). -/
theorem log_factorial_sub_stir (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ Real.log (k.factorial : ℝ) - stir k ∧
      Real.log (k.factorial : ℝ) - stir k ≤ 1 / (12 * (k : ℝ)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · have h := Stirling.le_log_factorial_stirling (n := k) (by omega)
    have e : stir k = k * Real.log k - k + Real.log k / 2 + Real.log (2 * π) / 2 := by
      rw [stir, Real.log_mul (by positivity) hk'.ne']
      ring
    linarith
  · rw [log_factorial_eq k hk]
    have := log_stirlingSeq_le k hk
    linarith

/-- `|log k! - stir k| ≤ 1/k` (`k ≥ 1`). -/
theorem abs_log_factorial_sub_stir (k : ℕ) (hk : 1 ≤ k) :
    |Real.log (k.factorial : ℝ) - stir k| ≤ 1 / (k : ℝ) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨h0, h1⟩ := log_factorial_sub_stir k hk
  rw [abs_of_nonneg h0]
  refine h1.trans ?_
  rw [div_le_div_iff₀ (by positivity) hk']
  linarith


/-- `(1+t)log(1+t) - t - t²/2` (the cubic Taylor remainder). -/
noncomputable def phi (t : ℝ) : ℝ := (1 + t) * Real.log (1 + t) - t - t ^ 2 / 2

/-- `|log(1+t)| ≤ 2|t|` (`|t| ≤ 1/2`). -/
theorem abs_log_one_add_le {t : ℝ} (ht : |t| ≤ 1 / 2) : |Real.log (1 + t)| ≤ 2 * |t| := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -t) (by rw [abs_neg]; linarith) 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, sub_neg_eq_add, abs_neg,
    pow_one] at h
  have hpos : (0 : ℝ) < 1 - |t| := by linarith
  refine h.trans ?_
  rw [div_le_iff₀ hpos]
  nlinarith [abs_nonneg t]

/-- `|log(1+t) - t + t²/2| ≤ 2|t|³` (`|t| ≤ 1/2`). -/
theorem abs_log_one_add_sub_le {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |Real.log (1 + t) - t + t ^ 2 / 2| ≤ 2 * |t| ^ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -t) (by rw [abs_neg]; linarith) 2
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    sub_neg_eq_add, abs_neg] at h
  have e : (-t) ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) + (-t) ^ (1 + 1) / ((1 : ℕ) + 1 : ℝ) + Real.log (1 + t)
      = Real.log (1 + t) - t + t ^ 2 / 2 := by
    push_cast
    ring
  rw [e, show (2 : ℕ) + 1 = 3 from rfl] at h
  have hpos : (0 : ℝ) < 1 - |t| := by linarith
  refine h.trans ?_
  rw [div_le_iff₀ hpos]
  have h3 : (0 : ℝ) ≤ |t| ^ 3 := by positivity
  nlinarith [abs_nonneg t]

/-- `|phi t| ≤ 4|t|³` (`|t| ≤ 1/2`). -/
theorem abs_phi_le {t : ℝ} (ht : |t| ≤ 1 / 2) : |phi t| ≤ 4 * |t| ^ 3 := by
  set R := Real.log (1 + t) - t + t ^ 2 / 2 with hR
  have hRb := abs_log_one_add_sub_le ht
  rw [← hR] at hRb
  have e : phi t = -t ^ 3 / 2 + (1 + t) * R := by
    rw [phi, hR]
    ring
  rw [e]
  have h1 : |-t ^ 3 / 2| = |t| ^ 3 / 2 := by
    rw [abs_div, abs_neg, abs_pow]
    norm_num
  have h2 : |(1 + t) * R| ≤ (3 / 2) * (2 * |t| ^ 3) := by
    rw [abs_mul]
    have : |1 + t| ≤ 3 / 2 := by
      calc |1 + t| ≤ |1| + |t| := abs_add_le _ _
        _ ≤ 3 / 2 := by rw [abs_one]; linarith
    exact mul_le_mul this hRb (abs_nonneg _) (by norm_num)
  calc |-t ^ 3 / 2 + (1 + t) * R| ≤ |-t ^ 3 / 2| + |(1 + t) * R| := abs_add_le _ _
    _ ≤ |t| ^ 3 / 2 + (3 / 2) * (2 * |t| ^ 3) := by rw [h1]; linarith
    _ ≤ 4 * |t| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg t) 3]

/-- **Logarithmic identity**: with `s = n + m`, `μ = P/(P-1)`, `σ² = P/(P-1)²`, `d = s - μn`, `u = d/(μn)`,
`v = d(P-1)/n`,
`stir s - stir n - stir m + log n - log s + n log(P-1) - s log P - (-(1/2)log(2πσ²n) - d²/(2σ²n))`
`= μn·phi(u) - (1/(P-1))n·phi(v) - log(1+u)/2 - log(1+v)/2`. -/
theorem lclt_log_identity (P n m μ σ2 d u v : ℝ) (hP : 1 < P) (hn : 0 < n) (hm : 0 < m)
    (hμ : μ = P / (P - 1)) (hσ : σ2 = P / (P - 1) ^ 2) (hd : d = (n + m) - μ * n)
    (hu : u = d / (μ * n)) (hv : v = d * (P - 1) / n) :
    stir (n + m) - stir n - stir m + Real.log n - Real.log (n + m) + n * Real.log (P - 1)
        - (n + m) * Real.log P
        - (-(1 / 2) * Real.log (2 * π * σ2 * n) - d ^ 2 / (2 * σ2 * n))
      = μ * n * phi u - (1 / (P - 1)) * n * phi v
          - Real.log (1 + u) / 2 - Real.log (1 + v) / 2 := by
  have hP0 : (0 : ℝ) < P := by linarith
  have hP1 : (0 : ℝ) < P - 1 := by linarith
  have hμpos : 0 < μ := by rw [hμ]; positivity
  have hs : 0 < n + m := by linarith
  -- `s = μn(1+u)`, `m = (1/(P-1)) n (1+v)`
  have hsu : n + m = μ * n * (1 + u) := by
    rw [hu, hd]; field_simp; ring
  have hmv : m = (1 / (P - 1)) * n * (1 + v) := by
    rw [hv, hd, hμ]; field_simp; ring
  have h1u : 0 < 1 + u := by
    have h : 0 < μ * n * (1 + u) := hsu ▸ hs
    exact pos_of_mul_pos_right h (by positivity)
  have h1v : 0 < 1 + v := by
    have h : 0 < (1 / (P - 1)) * n * (1 + v) := hmv ▸ hm
    exact pos_of_mul_pos_right h (by positivity)
  -- decomposition of the logarithms
  have hlogμ : Real.log μ = Real.log P - Real.log (P - 1) := by
    rw [hμ, Real.log_div hP0.ne' hP1.ne']
  have hlogs : Real.log (n + m) = Real.log P - Real.log (P - 1) + Real.log n + Real.log (1 + u) := by
    rw [hsu, Real.log_mul (by positivity) h1u.ne', Real.log_mul hμpos.ne' hn.ne', hlogμ]
  have hlogm : Real.log m = -Real.log (P - 1) + Real.log n + Real.log (1 + v) := by
    conv_lhs => rw [hmv]
    rw [Real.log_mul (by positivity) h1v.ne', Real.log_mul (by positivity) hn.ne', one_div,
      Real.log_inv]
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hstir : ∀ x : ℝ, 0 < x →
      stir x = x * Real.log x - x + (Real.log (2 * π) + Real.log x) / 2 := by
    intro x hx
    rw [stir, Real.log_mul h2π.ne' hx.ne']
  have hlogσ : Real.log (2 * π * σ2 * n)
      = Real.log (2 * π) + (Real.log P - 2 * Real.log (P - 1)) + Real.log n := by
    rw [Real.log_mul (by rw [hσ]; positivity) hn.ne', Real.log_mul h2π.ne' (by rw [hσ]; positivity),
      hσ, Real.log_div hP0.ne' (by positivity), Real.log_pow]
    push_cast
    ring
  rw [hstir _ hs, hstir _ hn, hstir _ hm, hlogσ, hlogs, hlogm, phi, phi]
  -- the rest is an identity of rational expressions (the `log` atoms appear linearly)
  subst hμ hσ
  rw [hu, hv, hd]
  field_simp
  ring

/-- **Bound for the remainder**: under `2(P-1)|d| ≤ n`, the right-hand side of the identity is at most
`(4 + 4(P-1)²)|d|³/n² + P|d|/n`. -/
theorem lclt_rem_bound (P n μ d u v : ℝ) (hP : 1 < P) (hn : 0 < n)
    (hμ : μ = P / (P - 1)) (hu : u = d / (μ * n)) (hv : v = d * (P - 1) / n)
    (hsmall : 2 * (P - 1) * |d| ≤ n) :
    |μ * n * phi u - (1 / (P - 1)) * n * phi v - Real.log (1 + u) / 2 - Real.log (1 + v) / 2|
      ≤ (4 + 4 * (P - 1) ^ 2) * (|d| ^ 3 / n ^ 2) + P * (|d| / n) := by
  have hP0 : (0 : ℝ) < P := by linarith
  have hP1 : (0 : ℝ) < P - 1 := by linarith
  have hμn : 0 < μ * n := by rw [hμ]; positivity
  have hau : |u| = |d| * (P - 1) / (P * n) := by
    rw [hu, abs_div, abs_of_pos hμn, hμ]
    field_simp
  have hav : |v| = |d| * (P - 1) / n := by
    rw [hv, abs_div, abs_mul, abs_of_pos hP1, abs_of_pos hn]
  have hD : 0 ≤ |d| := abs_nonneg d
  have hv2 : |v| ≤ 1 / 2 := by
    rw [hav, div_le_iff₀ hn]
    nlinarith
  have huv : |u| ≤ |v| := by
    rw [hau, hav, div_le_div_iff₀ (by positivity) hn]
    have : 0 ≤ |d| * (P - 1) * n := by positivity
    nlinarith
  have hu2 : |u| ≤ 1 / 2 := huv.trans hv2
  have hX : 0 ≤ |d| ^ 3 / n ^ 2 := by positivity
  -- each term
  have t1 : |μ * n * phi u| ≤ 4 * (|d| ^ 3 / n ^ 2) := by
    rw [abs_mul, abs_of_pos hμn]
    calc μ * n * |phi u| ≤ μ * n * (4 * |u| ^ 3) :=
          mul_le_mul_of_nonneg_left (abs_phi_le hu2) hμn.le
      _ = 4 * ((P - 1) ^ 2 / P ^ 2) * (|d| ^ 3 / n ^ 2) := by
          rw [hau, hμ]; field_simp
      _ ≤ 4 * (|d| ^ 3 / n ^ 2) := by
          have h1 : (P - 1) ^ 2 / P ^ 2 ≤ 1 := by
            rw [div_le_one (by positivity)]; nlinarith
          nlinarith
  have t2 : |(1 / (P - 1)) * n * phi v| ≤ 4 * (P - 1) ^ 2 * (|d| ^ 3 / n ^ 2) := by
    have hc : 0 < (1 / (P - 1)) * n := by positivity
    rw [abs_mul, abs_of_pos hc]
    calc (1 / (P - 1)) * n * |phi v| ≤ (1 / (P - 1)) * n * (4 * |v| ^ 3) :=
          mul_le_mul_of_nonneg_left (abs_phi_le hv2) hc.le
      _ = 4 * (P - 1) ^ 2 * (|d| ^ 3 / n ^ 2) := by
          rw [hav]; field_simp
  have t3 : |Real.log (1 + u) / 2| ≤ |d| / n := by
    rw [abs_div, abs_two]
    have h := abs_log_one_add_le hu2
    have : |u| ≤ |d| / n := by
      rw [hau, div_le_div_iff₀ (by positivity) hn]
      have : 0 ≤ |d| * n := by positivity
      nlinarith
    linarith
  have t4 : |Real.log (1 + v) / 2| ≤ (P - 1) * (|d| / n) := by
    rw [abs_div, abs_two]
    have h := abs_log_one_add_le hv2
    have : |v| = (P - 1) * (|d| / n) := by rw [hav]; ring
    linarith
  have a1 := abs_le.mp t1
  have a2 := abs_le.mp t2
  have a3 := abs_le.mp t3
  have a4 := abs_le.mp t4
  rw [abs_le]
  constructor <;> nlinarith

/-- `|e^x - 1| ≤ |x| e^{|x|}`. -/
theorem abs_exp_sub_one_le_mul (x : ℝ) : |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg (by linarith [Real.add_one_le_exp x])]
    -- `e^x - 1 ≤ x e^x` ⇔ `1 - x ≤ e^{-x}`
    have h := Real.add_one_le_exp (-x)
    have he : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos x]
  · rw [abs_of_neg hx, abs_of_nonpos (by linarith [Real.exp_le_one_iff.mpr hx.le])]
    have h := Real.add_one_le_exp x
    have h1 : 1 ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
    nlinarith

end LCLTAux

end ND

end GGMCollatz
