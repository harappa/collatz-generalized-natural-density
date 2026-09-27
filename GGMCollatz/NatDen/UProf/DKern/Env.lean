import GGMCollatz.NatDen.UProf.DKern.Gauss

/-!
# Pieces (c)(d) of (DK): comparison with the Gauss envelope in the central window, and the tail outside the window ((c), (E1))

Notation: `μ = muP p`, `σ² = sig2 p`, `c = k_* = u/(μ - λ)`, `S = ⌊kλ + u⌋`, `θ = kλ + u - S`,
`δ = S - μk = -(μ-λ)(k - c) - θ`.

* `env_rel` (form of (E1)): if the relative error `e₁` of (LCLT), `e₂ = |δ|/(μk)`, `e₃ = |c - k|/k`, and
  `e₄` (the difference of exponents) are at most `1/2`, then `|Hs(k, S) - g(k)| ≤ 8(e₁ + e₂ + e₃ + e₄) g(k)`, where
  `g(k) = μ(2πσ²c)^{-1/2} exp(-(μ-λ)²(k-c)²/(2σ²c))` (`gau`).
  Write `Hs = (S/k) P(s_k = S)` (hockey stick), `S/k = μ(1 + δ/(μk))`, `P(s_k = S) = gauss(1 + η)`,
  `gauss/(g/μ) = √(c/k) exp(E)`, and multiply the four factors.
* `Hs_tail` (the tail in (c)): `Hs(k, S) ≤ (S/k) C G_{1+k}(c(S - μk))` (`geomP_local_bound`).
-/

namespace GGMCollatz

namespace ND

namespace DKernAux

/-- The upper bound `e₄ = ((μ-λ)²|k-c|³/c + 2(μ-λ)|k-c| + 1)/(2σ²k)` for the difference of exponents. -/
noncomputable def e4 (dl σ2 c k : ℝ) : ℝ :=
  (dl ^ 2 * |k - c| ^ 3 / c + 2 * dl * |k - c| + 1) / (2 * σ2 * k)

/-- The prefactor `A = μ/√(2πσ²c)` of the Gaussian of the central window. -/
noncomputable def gA (p : ℕ) (c : ℝ) : ℝ := muP p / Real.sqrt (2 * Real.pi * sig2 p * c)

/-- The coefficient `B = (μ-λ)²/(2σ²c)` in the exponent of the Gaussian of the central window. -/
noncomputable def gB (p : ℕ) (lam c : ℝ) : ℝ := (muP p - lam) ^ 2 / (2 * sig2 p * c)

/-- Relative error of a product: if `|y - 1| ≤ 1`, then `|xy - 1| ≤ 2(|x - 1| + |y - 1|)`. -/
theorem abs_mul_sub_one_le {x y : ℝ} (hy : |y - 1| ≤ 1) :
    |x * y - 1| ≤ 2 * (|x - 1| + |y - 1|) := by
  have e : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by ring
  rw [e]
  have h1 : |(x - 1) * (y - 1)| ≤ |x - 1| := by
    rw [abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_left hy (abs_nonneg _)) (le_of_eq (mul_one _))
  have h2 := abs_add_le ((x - 1) * (y - 1) + (x - 1)) (y - 1)
  have h3 := abs_add_le ((x - 1) * (y - 1)) (x - 1)
  have := abs_nonneg (y - 1)
  linarith

/-- If `ρ ≥ 0`, then `|ρ - 1| ≤ |ρ² - 1|`. -/
theorem abs_sub_one_le_sq {ρ : ℝ} (hρ : 0 ≤ ρ) : |ρ - 1| ≤ |ρ ^ 2 - 1| := by
  have e : ρ ^ 2 - 1 = (ρ - 1) * (ρ + 1) := by ring
  rw [e, abs_mul]
  have : 1 ≤ |ρ + 1| := by rw [abs_of_nonneg (by linarith)]; linarith
  nlinarith [abs_nonneg (ρ - 1)]

/-- The bound `|E| ≤ e₄` for the difference of exponents `E = B(k-c)² - (S-μk)²/(2σ²k)`. -/
theorem abs_E_le {μ lam σ2 c k θ S : ℝ} (hσ : 0 < σ2) (hc : 0 < c) (hk : 0 < k)
    (hdl : 0 ≤ μ - lam) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hS : S = k * lam + (μ - lam) * c - θ) :
    |(μ - lam) ^ 2 / (2 * σ2 * c) * (k - c) ^ 2 - (S - μ * k) ^ 2 / (2 * σ2 * k)|
      ≤ e4 (μ - lam) σ2 c k := by
  have hden : 0 < 2 * σ2 * k := by positivity
  have hE : (μ - lam) ^ 2 / (2 * σ2 * c) * (k - c) ^ 2 - (S - μ * k) ^ 2 / (2 * σ2 * k)
      = ((μ - lam) ^ 2 * (k - c) ^ 3 / c - 2 * (μ - lam) * (k - c) * θ - θ ^ 2) / (2 * σ2 * k) := by
    rw [hS]
    field_simp
    ring
  rw [hE, abs_div, abs_of_pos hden]
  unfold e4
  apply div_le_div_of_nonneg_right _ hden.le
  have h1 : |(μ - lam) ^ 2 * (k - c) ^ 3 / c| = (μ - lam) ^ 2 * |k - c| ^ 3 / c := by
    rw [abs_div, abs_mul, abs_of_pos hc, abs_of_nonneg (sq_nonneg (μ - lam)), abs_pow]
  have h2 : |2 * (μ - lam) * (k - c) * θ| ≤ 2 * (μ - lam) * |k - c| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (μ - lam)),
      abs_of_nonneg hθ0]
    have := abs_nonneg (k - c)
    have h := mul_le_mul_of_nonneg_left hθ1.le
      (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * (μ - lam)) this)
    linarith
  have h3 : |θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]; nlinarith
  calc |(μ - lam) ^ 2 * (k - c) ^ 3 / c - 2 * (μ - lam) * (k - c) * θ - θ ^ 2|
      ≤ |(μ - lam) ^ 2 * (k - c) ^ 3 / c - 2 * (μ - lam) * (k - c) * θ| + |θ ^ 2| :=
        abs_sub _ _
    _ ≤ |(μ - lam) ^ 2 * (k - c) ^ 3 / c| + |2 * (μ - lam) * (k - c) * θ| + |θ ^ 2| := by
        linarith [abs_sub ((μ - lam) ^ 2 * (k - c) ^ 3 / c) (2 * (μ - lam) * (k - c) * θ)]
    _ ≤ _ := by rw [h1]; linarith

/-- **Form of (E1)**: the relative error between `Hs` and the Gauss envelope in the central window. -/
theorem env_rel {p : ℕ} (hp : 2 ≤ p) {lam c : ℝ} (hlam : lam < muP p) (hc : 0 < c) {k S : ℕ}
    (hk : 1 ≤ k) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hS : (S : ℝ) = k * lam + (muP p - lam) * c - θ)
    {e₁ : ℝ} (hlclt : |nb p k S - gauss p k S| ≤ e₁ * gauss p k S)
    (he₁ : e₁ ≤ 1 / 2) (he₂ : |(S : ℝ) - muP p * k| / (muP p * k) ≤ 1 / 2)
    (he₃ : |c - k| / k ≤ 1 / 2) (he₄ : e4 (muP p - lam) (sig2 p) c k ≤ 1 / 2) :
    |Hs p k S - gau (gA p c) (gB p lam c) c k|
      ≤ 8 * (e₁ + |(S : ℝ) - muP p * k| / (muP p * k) + |c - k| / k +
          e4 (muP p - lam) (sig2 p) c k) * gau (gA p c) (gB p lam c) c k := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hμ : 1 < muP p := one_lt_muP hp
  have hσ : 0 < sig2 p := by unfold sig2; apply div_pos <;> nlinarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hμk : 0 < muP p * k := by positivity
  set μ := muP p with hμdef
  set σ2 := sig2 p with hσdef
  set e₂ := |(S : ℝ) - μ * k| / (μ * k) with he₂def
  set e₃ := |c - k| / k with he₃def
  set e₄ := e4 (μ - lam) σ2 c k with he₄def
  -- `S ≥ 1`
  have hS1 : 1 ≤ S := by
    have h := he₂
    rw [div_le_iff₀ hμk] at h
    have : (0 : ℝ) < S := by
      have := neg_abs_le ((S : ℝ) - μ * k)
      linarith
    exact_mod_cast this
  -- the form of `gauss`
  set X := 2 * Real.pi * σ2 * c with hX
  set Y := 2 * Real.pi * σ2 * k with hY
  have hX0 : 0 < X := by positivity
  have hY0 : 0 < Y := by positivity
  set Q := ((S : ℝ) - μ * k) ^ 2 / (2 * σ2 * k) with hQ
  set B := gB p lam c with hBdef
  set E := B * ((k : ℝ) - c) ^ 2 - Q with hEdef
  have hG : gauss p k S = (Real.sqrt Y)⁻¹ * Real.exp (-Q) := by
    unfold gauss
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, neg_div]
  have hG0 : 0 < gauss p k S := by rw [hG]; positivity
  -- the four factors
  set a₁ := (S : ℝ) / (μ * k) with ha₁
  set a₂ := nb p k S / gauss p k S with ha₂
  set ρ := Real.sqrt X / Real.sqrt Y with hρ
  set a₄ := Real.exp E with ha₄
  have hkey : Hs p k S = gau (gA p c) B c k * (a₁ * a₂ * ρ * a₄) := by
    rw [Hs_eq_mul_nb hp hk hS1]
    have hnb : nb p k S = gauss p k S * a₂ := by
      rw [ha₂]; field_simp
    rw [hnb, hG]
    unfold gau gA
    rw [← hμdef, ← hσdef, ← hX, ha₁, hρ, ha₄, hEdef]
    have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
    have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
    have hexp : Real.exp (-B * ((k : ℝ) - c) ^ 2) * Real.exp (B * ((k : ℝ) - c) ^ 2 - Q)
        = Real.exp (-Q) := by rw [← Real.exp_add]; ring_nf
    rw [← hexp]
    have hμ0 : μ ≠ 0 := by linarith
    field_simp
  -- the error of each factor
  have h1 : |a₁ - 1| = e₂ := by
    rw [ha₁, he₂def, div_sub_one hμk.ne', abs_div, abs_of_pos hμk]
  have h2 : |a₂ - 1| ≤ e₁ := by
    rw [ha₂, div_sub_one hG0.ne', abs_div, abs_of_pos hG0, div_le_iff₀ hG0]
    exact hlclt
  have h3 : |ρ - 1| ≤ e₃ := by
    have hρ0 : 0 ≤ ρ := by positivity
    refine le_trans (abs_sub_one_le_sq hρ0) (le_of_eq ?_)
    rw [hρ, div_pow, Real.sq_sqrt hX0.le, Real.sq_sqrt hY0.le, hX, hY, he₃def]
    rw [show 2 * Real.pi * σ2 * c / (2 * Real.pi * σ2 * k) = c / k by field_simp]
    rw [div_sub_one hk0.ne', abs_div, abs_of_pos hk0]
  have hEb : |E| ≤ e₄ := by
    have := abs_E_le hσ hc hk0 (by linarith) hθ0 hθ1 hS
    rw [hEdef, hBdef, hQ]
    unfold gB
    exact this
  have h4 : |a₄ - 1| ≤ 2 * e₄ := by
    rw [ha₄]
    refine le_trans (Real.abs_exp_sub_one_le (by linarith)) ?_
    linarith
  -- the product
  have he₂' : e₂ ≤ 1 / 2 := he₂
  have hx1 : |a₁ * a₂ - 1| ≤ 2 * (e₂ + e₁) := by
    refine le_trans (abs_mul_sub_one_le (by linarith)) ?_
    rw [h1]; linarith
  have hx2 : |a₁ * a₂ * ρ - 1| ≤ 2 * (2 * (e₂ + e₁) + e₃) := by
    refine le_trans (abs_mul_sub_one_le (by linarith)) ?_
    linarith
  have hx3 : |a₁ * a₂ * ρ * a₄ - 1| ≤ 2 * (2 * (2 * (e₂ + e₁) + e₃) + 2 * e₄) := by
    refine le_trans (abs_mul_sub_one_le (by linarith)) ?_
    linarith
  have hg0 : 0 ≤ gau (gA p c) B c k := by
    apply gau_nonneg; unfold gA; positivity
  rw [hkey]
  have e : gau (gA p c) B c k * (a₁ * a₂ * ρ * a₄) - gau (gA p c) B c k
      = gau (gA p c) B c k * (a₁ * a₂ * ρ * a₄ - 1) := by ring
  rw [e, abs_mul, abs_of_nonneg hg0, mul_comm]
  apply mul_le_mul_of_nonneg_right _ hg0
  have : 0 ≤ e₃ := by positivity
  have : 0 ≤ e₂ := by positivity
  have : 0 ≤ e₄ := by
    rw [he₄def]; unfold e4
    have hdl : 0 ≤ μ - lam := by linarith
    apply div_nonneg _ (by positivity)
    have : 0 ≤ (μ - lam) ^ 2 * |(k : ℝ) - c| ^ 3 / c := by positivity
    have : 0 ≤ 2 * (μ - lam) * |(k : ℝ) - c| := by positivity
    linarith
  linarith

/-- **The tail in (c)**: `Hs(k, S) ≤ (S/k) C G_{1+k}(c(S - μk))`. -/
theorem Hs_tail {p : ℕ} (hp : 2 ≤ p) : ∃ cG : ℝ, 0 < cG ∧ ∃ CG : ℝ, 0 < CG ∧ ∀ k S : ℕ, 1 ≤ k →
    Hs p k S ≤ (S : ℝ) / k * CG * Gweight (1 + k) (cG * ((S : ℝ) - muP p * k)) := by
  obtain ⟨cG, hcG, CG, hCG, hloc⟩ := geomP_local_bound hp
  refine ⟨cG, hcG, CG, hCG, fun k S hk => ?_⟩
  rcases Nat.eq_zero_or_pos S with rfl | hS
  · unfold Hs
    simp [nb_zero hp hk]
  rw [Hs_eq_mul_nb hp hk hS]
  have h1 := hloc k S
  have hsq : 1 ≤ Real.sqrt (1 + k) := by
    rw [Real.one_le_sqrt]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have h2 : CG / Real.sqrt (1 + k) * Gweight (1 + k) (cG * ((S : ℝ) - muP p * k))
      ≤ CG * Gweight (1 + k) (cG * ((S : ℝ) - muP p * k)) := by
    apply mul_le_mul_of_nonneg_right _ (Gweight_nonneg _ _)
    exact div_le_self hCG.le hsq
  have h3 : nb p k S ≤ CG * Gweight (1 + k) (cG * ((S : ℝ) - muP p * k)) := le_trans h1 h2
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

end DKernAux

end ND

end GGMCollatz
