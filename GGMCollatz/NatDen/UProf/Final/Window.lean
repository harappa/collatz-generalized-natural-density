import GGMCollatz.NatDen.UProf.Final.Count

/-!
# Auxiliary for (UF): the ratio `Y/Z` of the window `[y, Y]` (`y = x^α`, `Y = y^α`), and how the three errors are combined

* `window_facts`: if `x ≥ 8` and `x^{α-1} ≥ 4` then `Z ≥ Y/(2μ) > 0`, `|Y - μZ| ≤ 2y`, `y/Y ≤ x^{-(α-1)}`.
  (In the form `Y/(dZ) = μ/d + O(y^{1-α})`.)
* `combine`: combination via `kernSum/Z - (μ/d)ψ = (kernSum - (Y/d)Ψ₁)/Z + (Y - μZ)Ψ₁/(dZ) + (μ/d)(Ψ₁ - ψ)`.
* `mZero_le_nZero`: if `α ≤ θ₀` then `m₀ ≤ n₀`.
-/

namespace GGMCollatz

namespace ND

namespace FinalAux

variable (F : Family)

/-- **The window ratio**: if `1 < α`, `8 ≤ x`, `4 ≤ x^{α-1}`, then for `y = x^α`, `Y = y^α`, `Z = wCard`,
`Y/(2μ) ≤ Z`, `|Y - μZ| ≤ 2y`, `y/Y ≤ x^{-(α-1)}`. -/
theorem window_facts {α x : ℝ} (hα : 1 < α) (hx : 8 ≤ x) (hxa : 4 ≤ x ^ (α - 1)) :
    (x ^ α) ^ α / (2 * F.mu) ≤ wCard F α x ∧
      |(x ^ α) ^ α - F.mu * wCard F α x| ≤ 2 * x ^ α ∧
      x ^ α / (x ^ α) ^ α ≤ x ^ (-(α - 1)) := by
  have hμ0 : 0 < F.mu := F.mu_pos
  have hμ2 : F.mu ≤ 2 := F.mu_le_two
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set y := x ^ α with hy
  set Y := y ^ α with hY
  have hyx : x ≤ y := Real.self_le_rpow_of_one_le hx1 hα.le
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hYsplit : Y = y * y ^ (α - 1) := by
    rw [hY, ← Real.rpow_one_add' hy0.le (by linarith)]; ring_nf
  have hyxa : x ^ (α - 1) ≤ y ^ (α - 1) := Real.rpow_le_rpow hx0.le hyx (by linarith)
  have hyα : 4 ≤ y ^ (α - 1) := le_trans hxa hyxa
  have hY4 : 4 * y ≤ Y := by rw [hYsplit]; nlinarith
  have hyY : y ≤ Y := by linarith
  have hcnt := card_logWindow_approx F hy1 hyY
  have hZdef : wCard F α x = ((F.logWindow y Y).card : ℝ) := rfl
  rw [← hZdef] at hcnt
  set Z := wCard F α x with hZ
  have hmul : F.mu * ((Y - y) / F.mu) = Y - y := by field_simp
  have hcnt' : |F.mu * Z - (Y - y)| ≤ 3 * F.mu := by
    rw [← hmul, ← mul_sub, abs_mul, abs_of_pos hμ0, mul_comm]
    exact mul_le_mul_of_nonneg_right hcnt hμ0.le
  rw [abs_le] at hcnt'
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    nlinarith
  · rw [abs_le]; constructor <;> nlinarith
  · have hxa0 : 0 < x ^ (α - 1) := Real.rpow_pos_of_pos hx0 _
    rw [Real.rpow_neg hx0.le, hYsplit, div_le_iff₀ (by positivity)]
    rw [show (x ^ (α - 1))⁻¹ * (y * y ^ (α - 1)) = y * (y ^ (α - 1) / x ^ (α - 1)) by
      field_simp]
    have : 1 ≤ y ^ (α - 1) / x ^ (α - 1) := by rw [le_div_iff₀ hxa0]; linarith
    nlinarith

/-- **Combining the three errors**:
`kS/Z - (μ/d)ψ = (kS - (Y/d)Ψ₁)/Z + (Y - μZ)Ψ₁/(dZ) + (μ/d)(Ψ₁ - ψ)`. -/
theorem combine {kS Z Y d μ Ψ₁ ψ A₁ A₂ A₃ P : ℝ} (hZ : 0 < Z) (hd : 0 < d) (hμ : 0 ≤ μ)
    (h1 : |kS - Y / d * Ψ₁| ≤ A₁) (h2 : |Y - μ * Z| ≤ A₂) (h3 : |Ψ₁ - ψ| ≤ A₃)
    (hP0 : 0 ≤ Ψ₁) (hP : Ψ₁ ≤ P) :
    |kS / Z - μ / d * ψ| ≤ A₁ / Z + A₂ * P / (d * Z) + μ / d * A₃ := by
  have hA₂ : 0 ≤ A₂ := le_trans (abs_nonneg _) h2
  have hid : kS / Z - μ / d * ψ
      = (kS - Y / d * Ψ₁) / Z + (Y - μ * Z) * Ψ₁ / (d * Z) + μ / d * (Ψ₁ - ψ) := by
    field_simp; ring
  rw [hid]
  have e1 : |(kS - Y / d * Ψ₁) / Z| ≤ A₁ / Z := by
    rw [abs_div, abs_of_pos hZ]; exact div_le_div_of_nonneg_right h1 hZ.le
  have e2 : |(Y - μ * Z) * Ψ₁ / (d * Z)| ≤ A₂ * P / (d * Z) := by
    rw [abs_div, abs_mul, abs_of_nonneg hP0, abs_of_pos (by positivity : 0 < d * Z)]
    exact div_le_div_of_nonneg_right (mul_le_mul h2 hP hP0 hA₂) (by positivity)
  have e3 : |μ / d * (Ψ₁ - ψ)| ≤ μ / d * A₃ := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ μ / d)]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  calc _ ≤ |(kS - Y / d * Ψ₁) / Z + (Y - μ * Z) * Ψ₁ / (d * Z)| + |μ / d * (Ψ₁ - ψ)| :=
        abs_add_le _ _
    _ ≤ |(kS - Y / d * Ψ₁) / Z| + |(Y - μ * Z) * Ψ₁ / (d * Z)| + |μ / d * (Ψ₁ - ψ)| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- If `α ≤ θ₀ = 1 + d/(20 log q)` then `m₀ ≤ n₀` (`log x ≥ 0`). -/
theorem mZero_le_nZero {α x : ℝ} (hαθ : α ≤ F.thetaMax) (hL : 0 ≤ Real.log x) :
    F.mZero α x ≤ F.nZero x := by
  unfold Family.mZero Family.nZero
  apply Nat.floor_le_floor
  have hd := F.drift_pos
  have hq := F.log_q_pos
  have hα1 : α - 1 ≤ F.drift / (20 * Real.log F.q) := by unfold Family.thetaMax at hαθ; linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (α - 1) * (5 * Real.log F.q) ≤ F.drift / 4 := by
    calc (α - 1) * (5 * Real.log F.q) ≤ F.drift / (20 * Real.log F.q) * (5 * Real.log F.q) :=
          mul_le_mul_of_nonneg_right hα1 (by positivity)
      _ = F.drift / 4 := by field_simp; ring
  have h2 : (α - 1) * Real.log x * (5 * Real.log F.q) ≤ Real.log x * (F.drift / 4) := by
    calc (α - 1) * Real.log x * (5 * Real.log F.q)
        = Real.log x * ((α - 1) * (5 * Real.log F.q)) := by ring
      _ ≤ Real.log x * (F.drift / 4) := mul_le_mul_of_nonneg_left h1 hL
  have h3 : Real.log x * (F.drift / 4) ≤ Real.log x * (4 * F.drift) :=
    mul_le_mul_of_nonneg_left (by linarith) hL
  linarith

end FinalAux

end ND

end GGMCollatz
