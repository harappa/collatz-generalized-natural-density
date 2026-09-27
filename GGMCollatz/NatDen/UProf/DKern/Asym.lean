import GGMCollatz.NatDen.UProf.DKern.Kron

/-!
# Asymptotic auxiliaries for (DK): the central window at `t = L^{1/20}` and the Gaussian constants

All errors of `mainSum` are written as integer powers of `t = L^{1/20}` (`L = t^{20}`, radius `R = L^{11/20} = t^{11}`,
Kronecker scale `ℓ = ⌊t²⌋`, rate `L^{-1/(10μ_irr)} = t^{-2/μ_irr}`).

* The central window `J = [ja, jb) = [⌊c - t^{11}⌋, ⌈c + t^{11}⌉)`, `gg = gau (gA p c) (gB p λ c) c`, `Wt = Σ_J gg`.
* For `c ∈ [c₁ t^{20}, t^{20}]`: `A = gA ≤ A₀/t^{10}`, `B₁/t^{20} ≤ B = gB ≤ B₀/t^{20}`, `A√(π/B) = μ/(μ-λ)`.
* `exp_small`: `C t^m e^{-at²} ≤ 1` (for `t` large).
-/

namespace GGMCollatz

namespace ND

namespace DKernAux

/-! ### The central window -/

/-- The left end `⌊c - t^{11}⌋` of the central window. -/
noncomputable def ja (c t : ℝ) : ℕ := ⌊c - t ^ 11⌋₊

/-- The right end (excluded) `⌈c + t^{11}⌉` of the central window. -/
noncomputable def jb (c t : ℝ) : ℕ := ⌈c + t ^ 11⌉₊

/-- The Gauss envelope of the central window `g(k) = μ(2πσ²c)^{-1/2} exp(-(μ-λ)²(k-c)²/(2σ²c))`. -/
noncomputable def gg (p : ℕ) (lam c k : ℝ) : ℝ := gau (gA p c) (gB p lam c) c k

/-- The Gaussian mass of the central window `W = Σ_J g(k)`. -/
noncomputable def Wt (p : ℕ) (lam c t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico (ja c t) (jb c t), gg p lam c k

section Window

variable {c t : ℝ}

theorem ja_le (h : 0 ≤ c - t ^ 11) : (ja c t : ℝ) ≤ c - t ^ 11 := Nat.floor_le h

theorem ja_gt : c - t ^ 11 - 1 < ja c t := Nat.sub_one_lt_floor _

theorem jb_ge : c + t ^ 11 ≤ jb c t := Nat.le_ceil _

theorem jb_lt (h : 0 ≤ c + t ^ 11) : (jb c t : ℝ) < c + t ^ 11 + 1 := Nat.ceil_lt_add_one h

theorem ja_le_jb (ht : 0 ≤ t) (h : 0 ≤ c - t ^ 11) : ja c t ≤ jb c t := by
  have h1 := ja_le h
  have h2 : c + t ^ 11 ≤ (jb c t : ℝ) := jb_ge
  have : 0 ≤ t ^ 11 := pow_nonneg ht 11
  exact_mod_cast (show (ja c t : ℝ) ≤ jb c t by linarith)

/-- Points in the window satisfy `|k - c| < t^{11} + 1`. -/
theorem abs_sub_lt_of_mem (ht : 0 ≤ t) {k : ℕ} (hk : k ∈ Finset.Ico (ja c t) (jb c t)) :
    |(k : ℝ) - c| < t ^ 11 + 1 := by
  rw [Finset.mem_Ico] at hk
  have h1 : (ja c t : ℝ) ≤ k := by exact_mod_cast hk.1
  have h2 : (k : ℝ) + 1 ≤ jb c t := by exact_mod_cast hk.2
  have h3 := ja_gt (c := c) (t := t)
  have h0 : 0 ≤ t ^ 11 := pow_nonneg ht 11
  by_cases hc : 0 ≤ c + t ^ 11
  · have h4 := jb_lt hc
    rw [abs_lt]; constructor <;> linarith
  · -- if `c + t^{11} < 0`, then `jb = 0` and the window is empty
    exfalso
    have : jb c t = 0 := by unfold jb; exact Nat.ceil_eq_zero.mpr (by linarith)
    omega

/-- Points outside the window satisfy `t^{11} ≤ |k - c|`. -/
theorem le_abs_sub_of_not_mem (h : 0 ≤ c - t ^ 11) {k : ℕ}
    (hk : k ∉ Finset.Ico (ja c t) (jb c t)) : t ^ 11 ≤ |(k : ℝ) - c| := by
  rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
  rcases hk with hk | hk
  · have h1 : (k : ℝ) + 1 ≤ ja c t := by exact_mod_cast hk
    have h2 := ja_le h
    rw [abs_sub_comm, le_abs]; left; linarith
  · have h1 : (jb c t : ℝ) ≤ k := by exact_mod_cast hk
    have h2 := jb_ge (c := c) (t := t)
    rw [le_abs]; left; linarith

end Window

/-! ### The Gaussian constants -/

theorem sig2_pos {p : ℕ} (hp : 2 ≤ p) : 0 < sig2 p := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold sig2; apply div_pos <;> nlinarith

theorem gA_pos {p : ℕ} (hp : 2 ≤ p) {c : ℝ} (hc : 0 < c) : 0 < gA p c := by
  have := sig2_pos hp
  have := muP_pos hp
  unfold gA; positivity

theorem gB_pos {p : ℕ} (hp : 2 ≤ p) {lam c : ℝ} (hlam : lam < muP p) (hc : 0 < c) :
    0 < gB p lam c := by
  have := sig2_pos hp
  have : 0 < muP p - lam := by linarith
  unfold gB; positivity

/-- `A√(π/B) = μ/(μ-λ)`. -/
theorem gA_mul_sqrt {p : ℕ} (hp : 2 ≤ p) {lam c : ℝ} (hlam : lam < muP p) (hc : 0 < c) :
    gA p c * Real.sqrt (Real.pi / gB p lam c) = muP p / (muP p - lam) := by
  have hσ := sig2_pos hp
  have hdl : 0 < muP p - lam := by linarith
  have hX : 0 < 2 * Real.pi * sig2 p * c := by positivity
  unfold gA gB
  have e : Real.pi / ((muP p - lam) ^ 2 / (2 * sig2 p * c))
      = (2 * Real.pi * sig2 p * c) / (muP p - lam) ^ 2 := by field_simp
  rw [e, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hdl.le]
  have : 0 < Real.sqrt (2 * Real.pi * sig2 p * c) := Real.sqrt_pos.mpr hX
  field_simp

/-- `A√(2π/B) = √2 μ/(μ-λ)`. -/
theorem gA_mul_sqrt2 {p : ℕ} (hp : 2 ≤ p) {lam c : ℝ} (hlam : lam < muP p) (hc : 0 < c) :
    gA p c * Real.sqrt (2 * Real.pi / gB p lam c) = Real.sqrt 2 * (muP p / (muP p - lam)) := by
  rw [← gA_mul_sqrt hp hlam hc, show 2 * Real.pi / gB p lam c = 2 * (Real.pi / gB p lam c) by ring,
    Real.sqrt_mul (by norm_num)]
  ring

/-- If `c ≥ c₁ t^{20}`, then `A ≤ A₀/t^{10}` (`A₀ = μ/√(2πσ²c₁)`). -/
theorem gA_le {p : ℕ} (hp : 2 ≤ p) {c₁ c t : ℝ} (hc₁ : 0 < c₁) (ht : 0 < t)
    (hc : c₁ * t ^ 20 ≤ c) :
    gA p c ≤ muP p / Real.sqrt (2 * Real.pi * sig2 p * c₁) / t ^ 10 := by
  have hσ := sig2_pos hp
  have hμ := muP_pos hp
  have hY : 0 < 2 * Real.pi * sig2 p * c₁ := by positivity
  have hsq : Real.sqrt (2 * Real.pi * sig2 p * c₁) * t ^ 10
      ≤ Real.sqrt (2 * Real.pi * sig2 p * c) := by
    have e : Real.sqrt (2 * Real.pi * sig2 p * c₁) * t ^ 10
        = Real.sqrt (2 * Real.pi * sig2 p * (c₁ * t ^ 20)) := by
      rw [show 2 * Real.pi * sig2 p * (c₁ * t ^ 20) = (2 * Real.pi * sig2 p * c₁) * (t ^ 10) ^ 2
        by ring, Real.sqrt_mul hY.le, Real.sqrt_sq (by positivity)]
    rw [e]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
  unfold gA
  rw [div_div]
  exact div_le_div_of_nonneg_left hμ.le (by positivity) hsq

/-- If `c ≥ c₁ t^{20}`, then `B ≤ B₀/t^{20}` (`B₀ = (μ-λ)²/(2σ²c₁)`). -/
theorem gB_le {p : ℕ} (hp : 2 ≤ p) {lam c₁ c t : ℝ} (hc₁ : 0 < c₁) (ht : 0 < t)
    (hc : c₁ * t ^ 20 ≤ c) :
    gB p lam c ≤ (muP p - lam) ^ 2 / (2 * sig2 p * c₁) / t ^ 20 := by
  have hσ := sig2_pos hp
  unfold gB
  rw [div_div]
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  nlinarith

/-- If `c ≤ t^{20}`, then `B₁/t^{20} ≤ B` (`B₁ = (μ-λ)²/(2σ²)`). -/
theorem gB_ge {p : ℕ} (hp : 2 ≤ p) {lam c t : ℝ} (hc0 : 0 < c) (hc : c ≤ t ^ 20) :
    (muP p - lam) ^ 2 / (2 * sig2 p) / t ^ 20 ≤ gB p lam c := by
  have hσ := sig2_pos hp
  unfold gB
  rw [div_div]
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  nlinarith

/-! ### Exponentially small terms -/

/-- `C t^m e^{-at²} ≤ 1` (for `t` large). -/
theorem exp_small {a : ℝ} (ha : 0 < a) (C : ℝ) (m : ℕ) :
    ∀ᶠ t : ℝ in Filter.atTop, C * t ^ m * Real.exp (-(a * t ^ 2)) ≤ 1 := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m : ℝ) a ha
  have hev := h.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / (|C| + 1) by positivity))
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with t ht ht1
  have ht0 : 0 ≤ t := by linarith
  rw [Real.rpow_natCast] at ht
  have hexp : Real.exp (-(a * t ^ 2)) ≤ Real.exp (-a * t) := by
    apply Real.exp_le_exp.mpr
    have : t ≤ t ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left this ha.le
    linarith
  have h1 : t ^ m * Real.exp (-(a * t ^ 2)) ≤ 1 / (|C| + 1) :=
    le_trans (mul_le_mul_of_nonneg_left hexp (by positivity)) ht
  have h2 : C * (t ^ m * Real.exp (-(a * t ^ 2))) ≤ |C| * (t ^ m * Real.exp (-(a * t ^ 2))) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  calc C * t ^ m * Real.exp (-(a * t ^ 2)) = C * (t ^ m * Real.exp (-(a * t ^ 2))) := by ring
    _ ≤ |C| * (t ^ m * Real.exp (-(a * t ^ 2))) := h2
    _ ≤ |C| * (1 / (|C| + 1)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]; linarith

/-- The substitution `t = L^{1/20}`: `L = t^{20}`. -/
theorem rpow20 {L : ℝ} (hL : 0 ≤ L) : (L ^ (1 / 20 : ℝ)) ^ 20 = L := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL]; norm_num

/-- `L^{11/20} = t^{11}`. -/
theorem rpow1120 {L : ℝ} (hL : 0 ≤ L) : L ^ (11 / 20 : ℝ) = (L ^ (1 / 20 : ℝ)) ^ 11 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL]; norm_num

/-- `L^{-1/(10μ)} = t^{-2/μ}`. -/
theorem rpow_rate {L : ℝ} (hL : 0 ≤ L) (μi : ℝ) :
    L ^ (-(1 / (10 * μi))) = (L ^ (1 / 20 : ℝ)) ^ (-(2 / μi)) := by
  rw [← Real.rpow_mul hL]; congr 1; ring

end DKernAux

end ND

end GGMCollatz
