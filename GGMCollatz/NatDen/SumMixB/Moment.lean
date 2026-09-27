import GGMCollatz.NatDen.SumMixB.Decomp

/-!
# Probabilistic tools for (SUMMIX b): exponential moments and tails of `s_m` ((T1))

* `expMoment`: for `|λ| ≤ 1/200`, `E e^{λ(s_m - μm)} ≤ e^{8mλ²}` (from `tiltZ_geomP_le_quad` and `tiltZ_iidSum`).
* `coshMoment`: for `m ≥ 200²`, `E (e^{e/√m} + e^{-e/√m}) ≤ 2e^8` (`e = s_m - μm`).
* `one_add_abs_add_sq_le`: `1 + |z| + z² ≤ 2(e^z + e^{-z})` (bounding the second and first moments by exponential moments).
* `tail_le`: `P(|s_m - μm| ≥ λ) ≤ 2 G_{1+m}(λ/400)` (the `nb` form of `geomP_tail_bound_atC`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace SumMixBAux

/-- **Exponential moment**: for `|λ| ≤ 1/200`, `Σ_σ P(s_m = σ) e^{λ(σ - μm)} ≤ e^{8mλ²}` (summable). -/
theorem expMoment {p : ℕ} (hp : 2 ≤ p) (m : ℕ) {lam : ℝ} (hlo : -(1 / 200) ≤ lam)
    (hhi : lam ≤ 1 / 200) :
    Summable (fun σ : ℕ => nb p m σ * Real.exp (lam * ((σ : ℝ) - muP p * m))) ∧
      ∑' σ : ℕ, nb p m σ * Real.exp (lam * ((σ : ℝ) - muP p * m))
        ≤ Real.exp (8 * m * lam ^ 2) := by
  have hq := tiltZ_geomP_le_quad hp hlo hhi
  have hZt : tiltZ (geomP p) (expW lam) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hq
  have hpow := tiltZ_iidSum (geomP p) (expW_zero lam) (expW_add lam)
    (tiltZ_expW_ne_zero _ _) hZt m
  have hμ2 : muP p ≤ 2 := muP_le_two hp
  have hμ0 : 0 < muP p := muP_pos hp
  have hbase : 0 ≤ 1 + muP p * lam + 8 * lam ^ 2 := by nlinarith [sq_nonneg lam]
  -- the real sum and the ℝ≥0∞ partition function
  have hfin : tiltZ (iidSum (geomP p) m) (expW lam) ≠ ∞ := by
    rw [hpow]; exact ENNReal.pow_ne_top hZt
  have hterm : ∀ σ : ℕ, ((iidSum (geomP p) m) σ * expW lam σ).toReal
      = nb p m σ * Real.exp (lam * σ) := by
    intro σ
    rw [ENNReal.toReal_mul, expW, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rfl
  have hsum0 : Summable fun σ : ℕ => nb p m σ * Real.exp (lam * σ) := by
    have := ENNReal.summable_toReal hfin
    exact this.congr hterm
  have heq0 : ∑' σ : ℕ, nb p m σ * Real.exp (lam * σ)
      = (tiltZ (iidSum (geomP p) m) (expW lam)).toReal := by
    rw [tiltZ, ENNReal.tsum_toReal_eq (fun σ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (by rw [expW]; exact ENNReal.ofReal_ne_top))]
    exact tsum_congr fun σ => (hterm σ).symm
  have hbound : (tiltZ (iidSum (geomP p) m) (expW lam)).toReal
      ≤ Real.exp (m * (muP p * lam + 8 * lam ^ 2)) := by
    rw [hpow, ENNReal.toReal_pow]
    calc (tiltZ (geomP p) (expW lam)).toReal ^ m
        ≤ (1 + muP p * lam + 8 * lam ^ 2) ^ m := by
          gcongr
          exact ENNReal.toReal_le_of_le_ofReal hbase hq
      _ ≤ Real.exp (muP p * lam + 8 * lam ^ 2) ^ m := by
          gcongr
          have := Real.add_one_le_exp (muP p * lam + 8 * lam ^ 2)
          linarith
      _ = Real.exp (m * (muP p * lam + 8 * lam ^ 2)) := by rw [← Real.exp_nat_mul]
  have hsplit : ∀ σ : ℕ, nb p m σ * Real.exp (lam * ((σ : ℝ) - muP p * m))
      = nb p m σ * Real.exp (lam * σ) * Real.exp (-(lam * muP p * m)) := by
    intro σ
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  refine ⟨(hsum0.mul_right _).congr fun σ => (hsplit σ).symm, ?_⟩
  rw [tsum_congr hsplit, tsum_mul_right, heq0]
  calc (tiltZ (iidSum (geomP p) m) (expW lam)).toReal * Real.exp (-(lam * muP p * m))
      ≤ Real.exp (m * (muP p * lam + 8 * lam ^ 2)) * Real.exp (-(lam * muP p * m)) :=
        mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le
    _ = Real.exp (8 * m * lam ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- **Two-sided exponential moment**: if `200 ≤ √m`, then `Σ_σ P(s_m = σ)(e^{e/√m} + e^{-e/√m}) ≤ 2e^8`. -/
theorem coshMoment {p : ℕ} (hp : 2 ≤ p) (m : ℕ) (hm : 200 ≤ Real.sqrt m) :
    Summable (fun σ : ℕ => nb p m σ * (Real.exp (((σ : ℝ) - muP p * m) / Real.sqrt m)
        + Real.exp (-(((σ : ℝ) - muP p * m) / Real.sqrt m)))) ∧
      ∑' σ : ℕ, nb p m σ * (Real.exp (((σ : ℝ) - muP p * m) / Real.sqrt m)
        + Real.exp (-(((σ : ℝ) - muP p * m) / Real.sqrt m))) ≤ 2 * Real.exp 8 := by
  have hs0 : 0 < Real.sqrt m := by linarith
  set lam := 1 / Real.sqrt m with hlam
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hlam1 : lam ≤ 1 / 200 := by
    rw [hlam]
    exact one_div_le_one_div_of_le (by norm_num) hm
  have hm8 : 8 * (m : ℝ) * lam ^ 2 = 8 := by
    rw [hlam, div_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    have : (m : ℝ) ≠ 0 := by
      intro h0
      rw [h0, Real.sqrt_zero] at hm
      norm_num at hm
    field_simp
  obtain ⟨hA, hA'⟩ := expMoment hp m (lam := lam) (by linarith) hlam1
  obtain ⟨hB, hB'⟩ := expMoment hp m (lam := -lam) (by linarith) (by linarith)
  have hrw : ∀ σ : ℕ, nb p m σ * (Real.exp (((σ : ℝ) - muP p * m) / Real.sqrt m)
      + Real.exp (-(((σ : ℝ) - muP p * m) / Real.sqrt m)))
      = nb p m σ * Real.exp (lam * ((σ : ℝ) - muP p * m))
        + nb p m σ * Real.exp (-lam * ((σ : ℝ) - muP p * m)) := by
    intro σ
    rw [mul_add, hlam]
    congr 3 <;> ring
  refine ⟨(hA.add hB).congr fun σ => (hrw σ).symm, ?_⟩
  rw [tsum_congr hrw, hA.tsum_add hB]
  have h2 : 8 * (m : ℝ) * (-lam) ^ 2 = 8 := by rw [neg_sq]; exact hm8
  rw [hm8] at hA'
  rw [h2] at hB'
  linarith

/-- `1 + |z| + z² ≤ 2(e^z + e^{-z})`. -/
theorem one_add_abs_add_sq_le (z : ℝ) :
    1 + |z| + z ^ 2 ≤ 2 * (Real.exp z + Real.exp (-z)) := by
  have key : ∀ w : ℝ, 0 ≤ w → 1 + w + w ^ 2 ≤ 2 * Real.exp w := by
    intro w hw
    have := Real.quadratic_le_exp_of_nonneg hw
    nlinarith
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    have := key z hz
    have := Real.exp_pos (-z)
    linarith
  · rw [abs_of_nonpos hz]
    have h1 := key (-z) (by linarith)
    have h2 := Real.exp_pos z
    rw [neg_sq] at h1
    linarith

/-- **Tail** (the `nb` form of `geomP_tail_bound_atC`): `P(|s_m - μm| ≥ λ) ≤ 2 G_{1+m}(λ/400)`. -/
theorem tail_le {p : ℕ} (hp : 2 ≤ p) (m : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∑' σ : ℕ, (if lam ≤ |(σ : ℝ) - muP p * m| then nb p m σ else 0)
      ≤ 2 * Gweight (1 + m) (1 / 400 * lam) := by
  have := geomP_tail_bound_atC hp m lam hlam
  unfold C_geomTail c_geomTail at this
  exact this

/-- Summability of the sum of tails. -/
theorem summable_tail (p m : ℕ) (lam : ℝ) :
    Summable fun σ : ℕ => (if lam ≤ |(σ : ℝ) - muP p * m| then nb p m σ else 0) :=
  Summable.of_nonneg_of_le (fun σ => by split_ifs <;> simp [nb_nonneg])
    (fun σ => by split_ifs <;> simp [nb_nonneg]) (summable_nb p m)

end SumMixBAux

end ND

end GGMCollatz
