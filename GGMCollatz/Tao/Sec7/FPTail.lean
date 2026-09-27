import GGMCollatz.Tao.Sec7.HoldLocal

/-!
# Tails of the first-passage endpoint and of the `ℋ` walk (components for the tails (7.61) in `FpPlus.lean`)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, files `TaoCollatz/Sec7/FpLocation.lean`
(the ideas of `fpDist_height_tail_le_sixteenth_sharp`, `renewal_level_le_one`, and `gaussExp_col_tail`) and
`TaoCollatz/Sec7/ManyTriangles.lean` (`fpDist_col_dev` and the row-sum tools); generalized to the GGM family (p, q, r). Modified.
Instead of the explicit constants of tao-collatz, only existence is shown.

* `FP.tsum_exp_tail`, `FP.tsum_gauss_tail`: exponential and Gaussian tail sums over `ℕ`.
* `FP.Gweight_le_two_exp`: if `x ≥ κ t` then `G_t(x) ≤ 2 e^{-min(κ,1) x}`.
* `Family.FP.iidSum_height_tail`, `Family.FP.iidSum_col_tail`: height and column tails of the sum of `p` steps of `ℋ`
  (from `hold_tail_bound`).
* `Family.FP.hold_height_tail`: the height tail of `ℋ` (for all real thresholds).
* `Family.FP.fpDist_overshoot_tail`: the tail of the first-passage overshoot `e₂ - s` (induction on the budget; the height visits each level
  at most once, so `P(e₂ - s ≥ h) ≤ Σ_{u ≤ s} P(ℋ₂ ≥ h + u)`).
* `Family.FP.fpDist_col_tail`: the column tail of the first passage (from `fpDist_col_le`).
* `FP.tsum_conv_le`: splitting the tail sum of a convolution (a union bound).
-/

open scoped ENNReal

namespace GGMCollatz

namespace FP

/-- `1/(1 - e^{-x}) ≤ 1 + 1/x` (`x > 0`). -/
theorem one_sub_exp_neg_inv_le {x : ℝ} (hx : 0 < x) :
    (1 - Real.exp (-x))⁻¹ ≤ 1 + 1 / x := by
  have hex : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [Real.add_one_le_exp x])
  have h3 : x / (1 + x) ≤ 1 - Real.exp (-x) := by
    have : 1 - 1 / (1 + x) = x / (1 + x) := by field_simp; ring
    linarith
  calc (1 - Real.exp (-x))⁻¹ ≤ (x / (1 + x))⁻¹ := inv_anti₀ (by positivity) h3
    _ = 1 + 1 / x := by field_simp; ring

/-- `0 ≤ e^{-b} < 1` (`b > 0`). -/
theorem exp_neg_lt_one {b : ℝ} (hb : 0 < b) : Real.exp (-b) < 1 := by
  rw [Real.exp_lt_one_iff]; linarith

/-- **Exponential tail sum over `ℕ`**: `Σ_{j : |j - x₀| ≥ D} e^{-b|j - x₀|} ≤ 2 e^{-bD}/(1 - e^{-b})`. -/
theorem tsum_exp_tail (x₀ D b : ℝ) (hb : 0 < b) :
    Summable (fun j : ℕ => if D ≤ |(j : ℝ) - x₀| then Real.exp (-b * |(j : ℝ) - x₀|) else 0) ∧
    ∑' j : ℕ, (if D ≤ |(j : ℝ) - x₀| then Real.exp (-b * |(j : ℝ) - x₀|) else 0)
      ≤ 2 * Real.exp (-b * D) / (1 - Real.exp (-b)) := by
  set ρ : ℝ := Real.exp (-b) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := exp_neg_lt_one hb
  have hρpow : ∀ k : ℕ, ρ ^ k = Real.exp (-b * k) := by
    intro k; rw [hρ, ← Real.exp_nat_mul]; ring_nf
  set E : ℝ := Real.exp (-b * D) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set j₀ : ℕ := ⌈x₀ + D⌉₊ with hj₀
  set j₁ : ℕ := ⌊x₀ - D⌋₊ with hj₁
  set g₁ : ℕ → ℝ := fun j => if j₀ ≤ j then E * ρ ^ (j - j₀) else 0 with hg₁
  set g₂ : ℕ → ℝ := fun j => if j ≤ j₁ then E * ρ ^ (j₁ - j) else 0 with hg₂
  have hg₁0 : ∀ j, 0 ≤ g₁ j := fun j => by
    simp only [hg₁]; split_ifs <;> positivity
  have hg₂0 : ∀ j, 0 ≤ g₂ j := fun j => by
    simp only [hg₂]; split_ifs <;> positivity
  -- pointwise bound
  have hpt : ∀ j : ℕ,
      (if D ≤ |(j : ℝ) - x₀| then Real.exp (-b * |(j : ℝ) - x₀|) else 0) ≤ g₁ j + g₂ j := by
    intro j
    split_ifs with hD
    · rcases le_abs.mp hD with h | h
      · -- `j - x₀ ≥ D`
        have hjj : j₀ ≤ j := Nat.ceil_le.mpr (by linarith)
        have hceil : x₀ + D ≤ (j₀ : ℝ) := Nat.le_ceil _
        have hcast : ((j - j₀ : ℕ) : ℝ) = (j : ℝ) - j₀ := by
          rw [Nat.cast_sub hjj]
        have hkey : Real.exp (-b * |(j : ℝ) - x₀|) ≤ E * ρ ^ (j - j₀) := by
          rw [hρpow, hE, ← Real.exp_add, hcast]
          apply Real.exp_le_exp.mpr
          have : (j : ℝ) - x₀ ≤ |(j : ℝ) - x₀| := le_abs_self _
          nlinarith
        have : g₁ j = E * ρ ^ (j - j₀) := by simp only [hg₁]; rw [if_pos hjj]
        linarith [hg₂0 j]
      · -- `x₀ - j ≥ D`
        have hxD : (j : ℝ) ≤ x₀ - D := by linarith
        have hjj : j ≤ j₁ := Nat.le_floor hxD
        have hfloor : (j₁ : ℝ) ≤ x₀ - D := Nat.floor_le (le_trans (Nat.cast_nonneg j) hxD)
        have hcast : ((j₁ - j : ℕ) : ℝ) = (j₁ : ℝ) - j := by
          rw [Nat.cast_sub hjj]
        have hkey : Real.exp (-b * |(j : ℝ) - x₀|) ≤ E * ρ ^ (j₁ - j) := by
          rw [hρpow, hE, ← Real.exp_add, hcast]
          apply Real.exp_le_exp.mpr
          have : x₀ - (j : ℝ) ≤ |(j : ℝ) - x₀| := by
            rw [abs_sub_comm]; exact le_abs_self _
          nlinarith
        have : g₂ j = E * ρ ^ (j₁ - j) := by simp only [hg₂]; rw [if_pos hjj]
        linarith [hg₁0 j]
    · linarith [hg₁0 j, hg₂0 j]
  -- the sum of `g₁`
  have hg₁shift : ∀ i : ℕ, g₁ (i + j₀) = E * ρ ^ i := by
    intro i; simp only [hg₁]; rw [if_pos (by omega)]; congr 2; omega
  have hgeo : Summable fun i : ℕ => E * ρ ^ i :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left E
  have hg₁sum : Summable g₁ := by
    rw [← summable_nat_add_iff j₀]
    exact hgeo.congr fun i => (hg₁shift i).symm
  have hg₁tsum : ∑' j, g₁ j = E * (1 - ρ)⁻¹ := by
    rw [← hg₁sum.sum_add_tsum_nat_add j₀]
    have hzero : ∑ i ∈ Finset.range j₀, g₁ i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        simp only [hg₁]; rw [if_neg (by simp at hi; omega)]
    rw [hzero, zero_add, tsum_congr hg₁shift, tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
  -- the sum of `g₂` (finite)
  have hg₂supp : ∀ j ∉ Finset.range (j₁ + 1), g₂ j = 0 := by
    intro j hj; simp only [hg₂]; rw [if_neg (by simp at hj; omega)]
  have hg₂sum : Summable g₂ := summable_of_ne_finset_zero hg₂supp
  have hg₂tsum : ∑' j, g₂ j ≤ E * (1 - ρ)⁻¹ := by
    rw [tsum_eq_sum hg₂supp]
    have h1 : ∑ j ∈ Finset.range (j₁ + 1), g₂ j
        = E * ∑ j ∈ Finset.range (j₁ + 1), ρ ^ (j₁ - j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [hg₂]; rw [if_pos (by simp at hj; omega)]
    have h2 : ∑ j ∈ Finset.range (j₁ + 1), ρ ^ (j₁ - j)
        = ∑ i ∈ Finset.range (j₁ + 1), ρ ^ i := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp at hi
      congr 1; omega
    have h3 : ∑ i ∈ Finset.range (j₁ + 1), ρ ^ i ≤ (1 - ρ)⁻¹ := by
      rw [Finset.range_eq_Ico]
      have := geom_sum_Ico_le_of_lt_one (m := 0) (n := j₁ + 1) hρ0 hρ1
      simpa using this
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left h3 hE0
  have hsum12 : Summable fun j => g₁ j + g₂ j := hg₁sum.add hg₂sum
  have hLnn : ∀ j : ℕ,
      0 ≤ (if D ≤ |(j : ℝ) - x₀| then Real.exp (-b * |(j : ℝ) - x₀|) else 0) := fun j => by
    split_ifs <;> positivity
  have hLsum := Summable.of_nonneg_of_le hLnn hpt hsum12
  refine ⟨hLsum, ?_⟩
  calc ∑' j : ℕ, (if D ≤ |(j : ℝ) - x₀| then Real.exp (-b * |(j : ℝ) - x₀|) else 0)
      ≤ ∑' j, (g₁ j + g₂ j) := hLsum.tsum_le_tsum hpt hsum12
    _ = ∑' j, g₁ j + ∑' j, g₂ j := hg₁sum.tsum_add hg₂sum
    _ ≤ E * (1 - ρ)⁻¹ + E * (1 - ρ)⁻¹ := by rw [hg₁tsum]; linarith
    _ = 2 * E / (1 - ρ) := by rw [div_eq_mul_inv]; ring

/-- **Gaussian tail sum over `ℕ`**: for `D > 0`, `a > 0`,
`Σ_{j : |j - x₀| ≥ D} e^{-a (j - x₀)²} ≤ 2 e^{-a D²}(1 + 1/(aD))`. -/
theorem tsum_gauss_tail (x₀ D a : ℝ) (ha : 0 < a) (hD : 0 < D) :
    Summable (fun j : ℕ => if D ≤ |(j : ℝ) - x₀| then Real.exp (-(a * ((j : ℝ) - x₀) ^ 2)) else 0) ∧
    ∑' j : ℕ, (if D ≤ |(j : ℝ) - x₀| then Real.exp (-(a * ((j : ℝ) - x₀) ^ 2)) else 0)
      ≤ 2 * Real.exp (-(a * D ^ 2)) * (1 + 1 / (a * D)) := by
  have hb : 0 < a * D := mul_pos ha hD
  obtain ⟨hs, hle⟩ := tsum_exp_tail x₀ D (a * D) hb
  have hpt : ∀ j : ℕ,
      (if D ≤ |(j : ℝ) - x₀| then Real.exp (-(a * ((j : ℝ) - x₀) ^ 2)) else 0)
        ≤ (if D ≤ |(j : ℝ) - x₀| then Real.exp (-(a * D) * |(j : ℝ) - x₀|) else 0) := by
    intro j
    split_ifs with h
    · apply Real.exp_le_exp.mpr
      have hsq : ((j : ℝ) - x₀) ^ 2 = |(j : ℝ) - x₀| ^ 2 := (sq_abs _).symm
      rw [hsq]
      have : D * |(j : ℝ) - x₀| ≤ |(j : ℝ) - x₀| ^ 2 := by nlinarith [abs_nonneg ((j : ℝ) - x₀)]
      nlinarith
    · exact le_refl _
  have hnn : ∀ j : ℕ,
      0 ≤ (if D ≤ |(j : ℝ) - x₀| then Real.exp (-(a * ((j : ℝ) - x₀) ^ 2)) else 0) :=
    fun j => by split_ifs <;> positivity
  have hs' := Summable.of_nonneg_of_le hnn hpt hs
  refine ⟨hs', ?_⟩
  calc _ ≤ ∑' j : ℕ, (if D ≤ |(j : ℝ) - x₀| then Real.exp (-(a * D) * |(j : ℝ) - x₀|) else 0) :=
        hs'.tsum_le_tsum hpt hs
    _ ≤ 2 * Real.exp (-(a * D) * D) / (1 - Real.exp (-(a * D))) := hle
    _ = 2 * Real.exp (-(a * D ^ 2)) * (1 - Real.exp (-(a * D)))⁻¹ := by
        rw [div_eq_mul_inv]; congr 3; ring
    _ ≤ 2 * Real.exp (-(a * D ^ 2)) * (1 + 1 / (a * D)) :=
        mul_le_mul_of_nonneg_left (one_sub_exp_neg_inv_le hb) (by positivity)

/-- If `x ≥ κ t` then `G_t(x) ≤ 2 e^{-min(κ,1) x}`. -/
theorem Gweight_le_two_exp {t x κ : ℝ} (ht : 0 < t) (hκ : 0 < κ) (hx : κ * t ≤ x) :
    Sec7.Gweight t x ≤ 2 * Real.exp (-(min κ 1) * x) := by
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  have hm1 : min κ 1 ≤ κ := min_le_left _ _
  have hm2 : min κ 1 ≤ 1 := min_le_right _ _
  have h1 : Real.exp (-(x ^ 2) / t) ≤ Real.exp (-(min κ 1) * x) := by
    apply Real.exp_le_exp.mpr
    have hdiv : min κ 1 * x ≤ x ^ 2 / t := by
      rw [le_div_iff₀ ht]
      have : κ * x * t ≤ x ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hm1 (mul_nonneg hx0 ht.le)]
    rw [neg_div]
    linarith
  have h2 : Real.exp (-|x|) ≤ Real.exp (-(min κ 1) * x) := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg hx0]
    nlinarith
  unfold Sec7.Gweight
  linarith

/-- `G_t(x) ≤ (e^{t/4} + 1) e^{-x}` (`x ≥ 0`, `t > 0`). -/
theorem Gweight_le_exp {t x : ℝ} (ht : 0 < t) (hx0 : 0 ≤ x) :
    Sec7.Gweight t x ≤ (Real.exp (t / 4) + 1) * Real.exp (-x) := by
  have h1 : Real.exp (-(x ^ 2) / t) ≤ Real.exp (t / 4) * Real.exp (-x) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [neg_div, div_eq_mul_inv]
    have hsq : 0 ≤ (x - t / 2) ^ 2 := sq_nonneg _
    have : x - t / 4 ≤ x ^ 2 * t⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ ht]; nlinarith
    linarith
  unfold Sec7.Gweight
  rw [abs_of_nonneg hx0]
  nlinarith [Real.exp_pos (-x)]

/-- **Splitting the tail of a convolution**: if `g(e + w) ≤ g₁(e) + g₂(w)` (values in `[0,1]`), then
`Σ_x P(e + w = x) g(x) ≤ Σ_e μ(e) g₁(e) + Σ_w ν(w) g₂(w)`. -/
theorem tsum_conv_le (μ ν : PMF (ℕ × ℤ)) (g g₁ g₂ : ℕ × ℤ → ℝ)
    (hg0 : ∀ x, 0 ≤ g x) (hg₁0 : ∀ x, 0 ≤ g₁ x) (hg₂0 : ∀ x, 0 ≤ g₂ x)
    (hg₁1 : ∀ x, g₁ x ≤ 1) (hg₂1 : ∀ x, g₂ x ≤ 1)
    (hle : ∀ e w, g (e + w) ≤ g₁ e + g₂ w) :
    ∑' x : ℕ × ℤ, ((μ.bind fun e => ν.map fun w => e + w) x).toReal * g x
      ≤ ∑' e : ℕ × ℤ, (μ e).toReal * g₁ e + ∑' w : ℕ × ℤ, (ν w).toReal * g₂ w := by
  rw [← PMF.toReal_tsum_mul_ofReal _ _ hg0, ← PMF.toReal_tsum_mul_ofReal _ _ hg₁0,
    ← PMF.toReal_tsum_mul_ofReal _ _ hg₂0]
  have hfin₁ : ∑' e, μ e * ENNReal.ofReal (g₁ e) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.tsum_mul_ofReal_le_one μ _ hg₁1)
  have hfin₂ : ∑' w, ν w * ENNReal.ofReal (g₂ w) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.tsum_mul_ofReal_le_one ν _ hg₂1)
  rw [← ENNReal.toReal_add hfin₁ hfin₂]
  apply ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin₁, hfin₂⟩)
  rw [PMF.tsum_bind_mul]
  calc ∑' e, μ e * ∑' x, ((ν.map fun w => e + w) x) * ENNReal.ofReal (g x)
      = ∑' e, μ e * ∑' w, ν w * ENNReal.ofReal (g (e + w)) :=
        tsum_congr fun e => by rw [PMF.tsum_map_mul]
    _ ≤ ∑' e, μ e * ∑' w, ν w * (ENNReal.ofReal (g₁ e) + ENNReal.ofReal (g₂ w)) := by
        refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
        refine ENNReal.tsum_le_tsum fun w => mul_le_mul_right ?_ _
        rw [← ENNReal.ofReal_add (hg₁0 e) (hg₂0 w)]
        exact ENNReal.ofReal_le_ofReal (hle e w)
    _ = ∑' e, μ e * (ENNReal.ofReal (g₁ e) + ∑' w, ν w * ENNReal.ofReal (g₂ w)) := by
        refine tsum_congr fun e => ?_
        congr 1
        rw [tsum_congr fun w => mul_add (ν w) _ _, ENNReal.tsum_add, ENNReal.tsum_mul_right,
          ν.tsum_coe, one_mul]
    _ = ∑' e, μ e * ENNReal.ofReal (g₁ e) + ∑' w, ν w * ENNReal.ofReal (g₂ w) := by
        rw [tsum_congr fun e => mul_add (μ e) _ _, ENNReal.tsum_add, ENNReal.tsum_mul_right,
          μ.tsum_coe, one_mul]

/-- `Σ μ(e) 1_S(e)` (real) is `toReal` of the sum in `ℝ≥0∞`. -/
theorem tsum_indicator_toReal {α : Type*} (μ : PMF α) (S : Set α) :
    ∑' e, (μ e).toReal * S.indicator (1 : α → ℝ) e
      = (∑' e, μ e * S.indicator (1 : α → ℝ≥0∞) e).toReal := by
  rw [← PMF.toReal_tsum_mul_ofReal μ (S.indicator 1)
    (fun e => Set.indicator_nonneg (fun _ _ => zero_le_one) e)]
  congr 1
  refine tsum_congr fun e => ?_
  congr 1
  by_cases h : e ∈ S
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- `Σ μ(e) 1_S(e) ≤ 1` (real). -/
theorem tsum_indicator_le_one {α : Type*} (μ : PMF α) (S : Set α) :
    ∑' e, (μ e).toReal * S.indicator (1 : α → ℝ) e ≤ 1 := by
  rw [tsum_indicator_toReal]
  have h : ∑' e, μ e * S.indicator (1 : α → ℝ≥0∞) e ≤ 1 := by
    calc ∑' e, μ e * S.indicator (1 : α → ℝ≥0∞) e ≤ ∑' e, μ e * 1 := by
          refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
          by_cases he : e ∈ S
          · simp [Set.indicator_of_mem he]
          · simp [Set.indicator_of_notMem he]
      _ = 1 := by rw [tsum_congr fun e => mul_one (μ e), μ.tsum_coe]
  have := ENNReal.toReal_mono ENNReal.one_ne_top h
  simpa using this

/-- `Σ μ(e) 1_S(e) ≠ ⊤` (in `ℝ≥0∞`). -/
theorem tsum_indicator_ne_top {α : Type*} (μ : PMF α) (S : Set α) :
    ∑' e, μ e * S.indicator (1 : α → ℝ≥0∞) e ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  calc ∑' e, μ e * S.indicator (1 : α → ℝ≥0∞) e ≤ ∑' e, μ e * 1 := by
        refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
        by_cases he : e ∈ S
        · simp [Set.indicator_of_mem he]
        · simp [Set.indicator_of_notMem he]
    _ = 1 := by rw [tsum_congr fun e => mul_one (μ e), μ.tsum_coe]

/-- A sum of one variable is the original law (`iidSum μ 1 = μ`). -/
theorem iidSum_one {M : Type*} [AddCommMonoid M] (μ : PMF M) : Sec7.iidSum μ 1 = μ := by
  unfold Sec7.iidSum
  rw [show μ.iid 1 = μ.bind fun a => (μ.iid 0).map (Fin.cons a) from rfl, PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure μ]
  congr 1
  funext a
  rw [show μ.iid 0 = PMF.pure (fun i => i.elim0) from rfl, PMF.pure_map, PMF.pure_map]
  simp

end FP

namespace Family

namespace FP

variable (F : Family)

theorem holdSum_eq_iidSum (n : ℕ) : F.holdSum n = Sec7.iidSum F.hold n := by
  unfold Family.holdSum Sec7.iidSum
  congr 1
  funext v
  exact Prod.ext (by simp [Prod.fst_sum]) (by simp [Prod.snd_sum])

theorem holdMean1_nonneg : 0 ≤ F.holdMean1 := by
  have hp : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  unfold Family.holdMean1
  have : (0 : ℝ) < (F.p : ℝ) - 1 := by linarith
  positivity

theorem holdMean2_nonneg : 0 ≤ F.holdMean2 := by
  have hp : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  unfold Family.holdMean2
  have : (0 : ℝ) < (F.p : ℝ) - 1 := by linarith
  positivity

/-- Transferring `hold_tail_bound` to an arbitrary subset: if every point of `S` is at distance `≥ λ'` from the center, then
`P(S) ≤ C G_{1+n}(c λ')`. -/
theorem iidSum_tail_of_norm {c C : ℝ}
    (hbd : ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' d : ℕ × ℤ,
          if lam ≤ ‖(((d.1 : ℝ) - F.holdMean1 * n, (d.2 : ℝ) - F.holdMean2 * n) : ℝ × ℝ)‖
          then ((F.holdSum n) d).toReal else 0)
        ≤ C * Sec7.Gweight (1 + n) (c * lam))
    (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (S : Set (ℕ × ℤ))
    (hS : ∀ d ∈ S, lam ≤ ‖(((d.1 : ℝ) - F.holdMean1 * n, (d.2 : ℝ) - F.holdMean2 * n) : ℝ × ℝ)‖) :
    ∑' w : ℕ × ℤ, (Sec7.iidSum F.hold n w).toReal * S.indicator (1 : ℕ × ℤ → ℝ) w
      ≤ C * Sec7.Gweight (1 + n) (c * lam) := by
  classical
  rw [← holdSum_eq_iidSum]
  have hsumP : Summable fun d => ((F.holdSum n) d).toReal :=
    ENNReal.summable_toReal (F.holdSum n).tsum_coe_ne_top
  have hpt : ∀ d : ℕ × ℤ, ((F.holdSum n) d).toReal * S.indicator (1 : ℕ × ℤ → ℝ) d
      ≤ (if lam ≤ ‖(((d.1 : ℝ) - F.holdMean1 * n, (d.2 : ℝ) - F.holdMean2 * n) : ℝ × ℝ)‖
          then ((F.holdSum n) d).toReal else 0) := by
    intro d
    by_cases hd : d ∈ S
    · rw [Set.indicator_of_mem hd, Pi.one_apply, mul_one, if_pos (hS d hd)]
    · rw [Set.indicator_of_notMem hd, mul_zero]
      split_ifs <;> simp
  have hR0 : ∀ d : ℕ × ℤ, 0 ≤ (if lam ≤ ‖(((d.1 : ℝ) - F.holdMean1 * n,
      (d.2 : ℝ) - F.holdMean2 * n) : ℝ × ℝ)‖ then ((F.holdSum n) d).toReal else 0) :=
    fun d => by split_ifs <;> simp
  have hRsum : Summable fun d : ℕ × ℤ => (if lam ≤ ‖(((d.1 : ℝ) - F.holdMean1 * n,
      (d.2 : ℝ) - F.holdMean2 * n) : ℝ × ℝ)‖ then ((F.holdSum n) d).toReal else 0) :=
    Summable.of_nonneg_of_le hR0 (fun d => by split_ifs <;> simp) hsumP
  have hL0 : ∀ d : ℕ × ℤ, 0 ≤ ((F.holdSum n) d).toReal * S.indicator (1 : ℕ × ℤ → ℝ) d :=
    fun d => mul_nonneg ENNReal.toReal_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) d)
  have hLsum := Summable.of_nonneg_of_le hL0 hpt hRsum
  exact le_trans (hLsum.tsum_le_tsum hpt hRsum) (hbd n lam hlam)

/-- **Height tail of the sum of `p` steps**: if `t ≥ K(1+p)` then `P(W₂ ≥ t) ≤ C e^{-ct}`. -/
theorem iidSum_height_tail :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 0 < K ∧ ∀ (p : ℕ) (t : ℝ), K * (1 + p) ≤ t →
      ∑' w : ℕ × ℤ, (Sec7.iidSum F.hold p w).toReal
          * Set.indicator {q : ℕ × ℤ | t ≤ (q.2 : ℝ)} 1 w
        ≤ C * Real.exp (-c * t) := by
  obtain ⟨c₀, hc₀, C₀, hC₀, hbd⟩ := F.hold_tail_bound
  have hν := holdMean2_nonneg F
  set K : ℝ := 2 * F.holdMean2 + 2 with hK
  have hKpos : 0 < K := by rw [hK]; linarith
  set κ : ℝ := c₀ * K / 2 with hκ
  have hκpos : 0 < κ := by rw [hκ]; positivity
  refine ⟨min κ 1 * c₀ / 2, by positivity, 2 * C₀, by positivity, K, hKpos, ?_⟩
  intro p t hKt
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  set lam : ℝ := t - F.holdMean2 * p with hlam
  have hlam_ge : t / 2 ≤ lam := by
    rw [hlam]; nlinarith
  have hlam0 : 0 ≤ lam := by nlinarith
  have hS : ∀ d ∈ {q : ℕ × ℤ | t ≤ (q.2 : ℝ)},
      lam ≤ ‖(((d.1 : ℝ) - F.holdMean1 * p, (d.2 : ℝ) - F.holdMean2 * p) : ℝ × ℝ)‖ := by
    intro d hd
    simp only [Set.mem_ofPred_eq] at hd
    calc lam ≤ (d.2 : ℝ) - F.holdMean2 * p := by rw [hlam]; linarith
      _ ≤ |(d.2 : ℝ) - F.holdMean2 * p| := le_abs_self _
      _ = ‖((((d.1 : ℝ) - F.holdMean1 * p, (d.2 : ℝ) - F.holdMean2 * p) : ℝ × ℝ)).2‖ := by
          simp [Real.norm_eq_abs]
      _ ≤ _ := norm_snd_le _
  have h1 := iidSum_tail_of_norm F hbd p lam hlam0 _ hS
  have ht1 : (0 : ℝ) < 1 + p := by positivity
  have hG : Sec7.Gweight (1 + p) (c₀ * lam) ≤ 2 * Real.exp (-(min κ 1) * (c₀ * lam)) := by
    apply _root_.GGMCollatz.FP.Gweight_le_two_exp ht1 hκpos
    rw [hκ]
    have : K * (1 + p) / 2 ≤ lam := by linarith
    nlinarith
  have hexp : Real.exp (-(min κ 1) * (c₀ * lam)) ≤ Real.exp (-(min κ 1 * c₀ / 2) * t) := by
    apply Real.exp_le_exp.mpr
    have hm : 0 < min κ 1 := lt_min hκpos one_pos
    nlinarith [mul_le_mul_of_nonneg_left hlam_ge (le_of_lt (mul_pos hm hc₀))]
  calc _ ≤ C₀ * Sec7.Gweight (1 + p) (c₀ * lam) := h1
    _ ≤ C₀ * (2 * Real.exp (-(min κ 1 * c₀ / 2) * t)) :=
        mul_le_mul_of_nonneg_left (hG.trans (by linarith)) hC₀.le
    _ = 2 * C₀ * Real.exp (-(min κ 1 * c₀ / 2) * t) := by ring

/-- **Column tail of the sum of `p` steps**: if `D ≥ K(1+p)` then `P(W₁ ≥ D) ≤ C e^{-cD}`. -/
theorem iidSum_col_tail :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 0 < K ∧ ∀ (p : ℕ) (D : ℝ), K * (1 + p) ≤ D →
      ∑' w : ℕ × ℤ, (Sec7.iidSum F.hold p w).toReal
          * Set.indicator {q : ℕ × ℤ | D ≤ (q.1 : ℝ)} 1 w
        ≤ C * Real.exp (-c * D) := by
  obtain ⟨c₀, hc₀, C₀, hC₀, hbd⟩ := F.hold_tail_bound
  have hmean1 := holdMean1_nonneg F
  set K : ℝ := 2 * F.holdMean1 + 2 with hK
  have hKpos : 0 < K := by rw [hK]; linarith
  set κ : ℝ := c₀ * K / 2 with hκ
  have hκpos : 0 < κ := by rw [hκ]; positivity
  refine ⟨min κ 1 * c₀ / 2, by positivity, 2 * C₀, by positivity, K, hKpos, ?_⟩
  intro p t hKt
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  set lam : ℝ := t - F.holdMean1 * p with hlam
  have hlam_ge : t / 2 ≤ lam := by
    rw [hlam]; nlinarith
  have hlam0 : 0 ≤ lam := by nlinarith
  have hS : ∀ d ∈ {q : ℕ × ℤ | t ≤ (q.1 : ℝ)},
      lam ≤ ‖(((d.1 : ℝ) - F.holdMean1 * p, (d.2 : ℝ) - F.holdMean2 * p) : ℝ × ℝ)‖ := by
    intro d hd
    simp only [Set.mem_ofPred_eq] at hd
    calc lam ≤ (d.1 : ℝ) - F.holdMean1 * p := by rw [hlam]; linarith
      _ ≤ |(d.1 : ℝ) - F.holdMean1 * p| := le_abs_self _
      _ = ‖((((d.1 : ℝ) - F.holdMean1 * p, (d.2 : ℝ) - F.holdMean2 * p) : ℝ × ℝ)).1‖ := by
          simp [Real.norm_eq_abs]
      _ ≤ _ := norm_fst_le _
  have h1 := iidSum_tail_of_norm F hbd p lam hlam0 _ hS
  have ht1 : (0 : ℝ) < 1 + p := by positivity
  have hG : Sec7.Gweight (1 + p) (c₀ * lam) ≤ 2 * Real.exp (-(min κ 1) * (c₀ * lam)) := by
    apply _root_.GGMCollatz.FP.Gweight_le_two_exp ht1 hκpos
    rw [hκ]
    have : K * (1 + p) / 2 ≤ lam := by linarith
    nlinarith
  have hexp : Real.exp (-(min κ 1) * (c₀ * lam)) ≤ Real.exp (-(min κ 1 * c₀ / 2) * t) := by
    apply Real.exp_le_exp.mpr
    have hm : 0 < min κ 1 := lt_min hκpos one_pos
    nlinarith [mul_le_mul_of_nonneg_left hlam_ge (le_of_lt (mul_pos hm hc₀))]
  calc _ ≤ C₀ * Sec7.Gweight (1 + p) (c₀ * lam) := h1
    _ ≤ C₀ * (2 * Real.exp (-(min κ 1 * c₀ / 2) * t)) :=
        mul_le_mul_of_nonneg_left (hG.trans (by linarith)) hC₀.le
    _ = 2 * C₀ * Real.exp (-(min κ 1 * c₀ / 2) * t) := by ring

/-- **Height tail of `ℋ`** (for all real thresholds): `P(ℋ₂ ≥ x) ≤ C e^{-cx}`, `C ≥ 1`. -/
theorem hold_height_tail :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ,
      ∑' d : ℕ × ℤ, (F.hold d).toReal * Set.indicator {q : ℕ × ℤ | x ≤ (q.2 : ℝ)} 1 d
        ≤ C * Real.exp (-c * x) := by
  obtain ⟨c, hc, C, hC, K, hK, htail⟩ := iidSum_height_tail F
  have hE1 : 1 ≤ Real.exp (c * (K * 2)) := Real.one_le_exp (by positivity)
  refine ⟨c, hc, C + Real.exp (c * (K * 2)), by linarith, ?_⟩
  intro x
  have hex : 0 < Real.exp (-c * x) := Real.exp_pos _
  by_cases hx : K * 2 ≤ x
  · have h := htail 1 x (by norm_num; linarith)
    rw [_root_.GGMCollatz.FP.iidSum_one] at h
    calc _ ≤ C * Real.exp (-c * x) := h
      _ ≤ (C + Real.exp (c * (K * 2))) * Real.exp (-c * x) := by
          nlinarith [Real.exp_pos (c * (K * 2))]
  · have h1 := _root_.GGMCollatz.FP.tsum_indicator_le_one F.hold {q : ℕ × ℤ | x ≤ (q.2 : ℝ)}
    have h2 : 1 ≤ Real.exp (c * (K * 2)) * Real.exp (-c * x) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; push Not at hx; nlinarith
    calc _ ≤ 1 := h1
      _ ≤ Real.exp (c * (K * 2)) * Real.exp (-c * x) := h2
      _ ≤ (C + Real.exp (c * (K * 2))) * Real.exp (-c * x) := by nlinarith

/-- **Recursive bound for the overshoot** (in `ℝ≥0∞`): since the height visits each level at most once,
`P(e₂ ≥ s + h) ≤ Σ_{u ≤ s} P(ℋ₂ ≥ h + u)`. -/
theorem fpDist_overshoot_enn (h : ℝ) : ∀ s : ℕ,
    ∑' e : ℕ × ℤ, F.fpDist s e
        * Set.indicator {q : ℕ × ℤ | (s : ℝ) + h ≤ (q.2 : ℝ)} (1 : ℕ × ℤ → ℝ≥0∞) e
      ≤ ∑ u ∈ Finset.range (s + 1), ∑' d : ℕ × ℤ, F.hold d
          * Set.indicator {q : ℕ × ℤ | h + (u : ℝ) ≤ (q.2 : ℝ)} (1 : ℕ × ℤ → ℝ≥0∞) d := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    set Tn : ℕ → ℝ≥0∞ := fun u => ∑' d : ℕ × ℤ, F.hold d
      * Set.indicator {q : ℕ × ℤ | h + (u : ℝ) ≤ (q.2 : ℝ)} (1 : ℕ × ℤ → ℝ≥0∞) d with hTn
    rw [Family.fpDist, PMF.tsum_bind_mul]
    have hper : ∀ d : ℕ × ℤ,
        (∑' e : ℕ × ℤ, (if _h : d.2 ≤ 0 ∨ (s : ℤ) < d.2 then PMF.pure d
            else (F.fpDist (s - d.2.toNat)).map fun e => (d.1 + e.1, d.2 + e.2)) e
          * Set.indicator {q : ℕ × ℤ | (s : ℝ) + h ≤ (q.2 : ℝ)} (1 : ℕ × ℤ → ℝ≥0∞) e)
        ≤ Set.indicator {q : ℕ × ℤ | (s : ℝ) + h ≤ (q.2 : ℝ)} (1 : ℕ × ℤ → ℝ≥0∞) d
          + ∑ u ∈ Finset.range s, Tn u := by
      intro d
      split_ifs with hcond
      · rw [tsum_eq_single d (fun e he => by rw [PMF.pure_apply, if_neg he, zero_mul]),
          PMF.pure_apply, if_pos rfl, one_mul]
        exact le_self_add
      · push Not at hcond
        rw [PMF.tsum_map_mul]
        have hd2 : (d.2.toNat : ℤ) = d.2 := Int.toNat_of_nonneg (by omega)
        have hle : d.2.toNat ≤ s := by omega
        have hs' : s - d.2.toNat < s := by omega
        have hIH := IH (s - d.2.toNat) hs'
        have hcast : ((s - d.2.toNat : ℕ) : ℝ) = (s : ℝ) - (d.2 : ℝ) := by
          rw [Nat.cast_sub hle]
          have : ((d.2.toNat : ℕ) : ℝ) = ((d.2.toNat : ℤ) : ℝ) := by push_cast; rfl
          rw [this, hd2]
        have hind : ∀ e : ℕ × ℤ,
            Set.indicator {q : ℕ × ℤ | (s : ℝ) + h ≤ (q.2 : ℝ)} (1 : ℕ × ℤ → ℝ≥0∞)
                (d.1 + e.1, d.2 + e.2)
              = Set.indicator {q : ℕ × ℤ | ((s - d.2.toNat : ℕ) : ℝ) + h ≤ (q.2 : ℝ)}
                  (1 : ℕ × ℤ → ℝ≥0∞) e := by
          intro e
          have hiff : (s : ℝ) + h ≤ ((d.2 + e.2 : ℤ) : ℝ)
              ↔ ((s - d.2.toNat : ℕ) : ℝ) + h ≤ (e.2 : ℝ) := by
            rw [hcast]; push_cast; constructor <;> intro <;> linarith
          by_cases hm : ((s - d.2.toNat : ℕ) : ℝ) + h ≤ (e.2 : ℝ)
          · rw [Set.indicator_of_mem (show (d.1 + e.1, d.2 + e.2) ∈ {q : ℕ × ℤ |
                (s : ℝ) + h ≤ (q.2 : ℝ)} from hiff.mpr hm),
              Set.indicator_of_mem (show e ∈ {q : ℕ × ℤ |
                ((s - d.2.toNat : ℕ) : ℝ) + h ≤ (q.2 : ℝ)} from hm)]
            rfl
          · rw [Set.indicator_of_notMem (show (d.1 + e.1, d.2 + e.2) ∉ {q : ℕ × ℤ |
                (s : ℝ) + h ≤ (q.2 : ℝ)} from fun h' => hm (hiff.mp h')),
              Set.indicator_of_notMem (show e ∉ {q : ℕ × ℤ |
                ((s - d.2.toNat : ℕ) : ℝ) + h ≤ (q.2 : ℝ)} from hm)]
        rw [tsum_congr fun e => by rw [hind e]]
        calc _ ≤ ∑ u ∈ Finset.range (s - d.2.toNat + 1), Tn u := hIH
          _ ≤ ∑ u ∈ Finset.range s, Tn u :=
              Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
          _ ≤ _ := le_add_self
    have hind_eq : ∀ d : ℕ × ℤ,
        Set.indicator {q : ℕ × ℤ | (s : ℝ) + h ≤ (q.2 : ℝ)} (1 : ℕ × ℤ → ℝ≥0∞) d
          = Set.indicator {q : ℕ × ℤ | h + ((s : ℕ) : ℝ) ≤ (q.2 : ℝ)}
              (1 : ℕ × ℤ → ℝ≥0∞) d := by
      intro d
      congr 1
      ext q
      simp only [Set.mem_ofPred_eq]
      constructor <;> intro <;> linarith
    calc ∑' d : ℕ × ℤ, F.hold d * _
        ≤ ∑' d : ℕ × ℤ, F.hold d
            * (Set.indicator {q : ℕ × ℤ | (s : ℝ) + h ≤ (q.2 : ℝ)} (1 : ℕ × ℤ → ℝ≥0∞) d
              + ∑ u ∈ Finset.range s, Tn u) :=
          ENNReal.tsum_le_tsum fun d => mul_le_mul_right (hper d) _
      _ = Tn s + ∑ u ∈ Finset.range s, Tn u := by
          rw [tsum_congr fun d => mul_add (F.hold d) _ _, ENNReal.tsum_add,
            ENNReal.tsum_mul_right, F.hold.tsum_coe, one_mul, hTn]
          congr 1
          exact tsum_congr fun d => by rw [hind_eq d]
      _ = ∑ u ∈ Finset.range (s + 1), Tn u := by rw [Finset.sum_range_succ, add_comm]

/-- **Tail of the first-passage overshoot**: `P(e₂ ≥ s + h) ≤ C e^{-ch}` (for all `s` and real `h`). -/
theorem fpDist_overshoot_tail :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ (s : ℕ) (h : ℝ),
      ∑' e : ℕ × ℤ, (F.fpDist s e).toReal
          * Set.indicator {q : ℕ × ℤ | (s : ℝ) + h ≤ (q.2 : ℝ)} 1 e
        ≤ C * Real.exp (-c * h) := by
  obtain ⟨c, hc, C, hC1, hT⟩ := hold_height_tail F
  have hρ1 := _root_.GGMCollatz.FP.exp_neg_lt_one hc
  have hρpos : 0 < 1 - Real.exp (-c) := by linarith
  refine ⟨c, hc, C * (1 - Real.exp (-c))⁻¹, by positivity, ?_⟩
  intro s h
  rw [_root_.GGMCollatz.FP.tsum_indicator_toReal]
  have hE := fpDist_overshoot_enn F h s
  have hTu : ∀ u : ℕ, (∑' d : ℕ × ℤ, F.hold d
      * Set.indicator {q : ℕ × ℤ | h + (u : ℝ) ≤ (q.2 : ℝ)} (1 : ℕ × ℤ → ℝ≥0∞) d)
        ≤ ENNReal.ofReal (C * Real.exp (-c * (h + u))) := by
    intro u
    have h1 := hT (h + u)
    rw [_root_.GGMCollatz.FP.tsum_indicator_toReal] at h1
    rw [← ENNReal.ofReal_toReal (_root_.GGMCollatz.FP.tsum_indicator_ne_top F.hold _)]
    exact ENNReal.ofReal_le_ofReal h1
  have hsumR : ∑ u ∈ Finset.range (s + 1), C * Real.exp (-c * (h + u))
      ≤ C * (1 - Real.exp (-c))⁻¹ * Real.exp (-c * h) := by
    have hterm : ∀ u : ℕ, C * Real.exp (-c * (h + u))
        = C * Real.exp (-c * h) * Real.exp (-c) ^ u := by
      intro u
      rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      congr 2; ring
    rw [Finset.sum_congr rfl fun u _ => hterm u, ← Finset.mul_sum]
    have hgeo : ∑ i ∈ Finset.range (s + 1), Real.exp (-c) ^ i ≤ (1 - Real.exp (-c))⁻¹ := by
      rw [Finset.range_eq_Ico]
      have := geom_sum_Ico_le_of_lt_one (m := 0) (n := s + 1) (Real.exp_pos (-c)).le hρ1
      simpa using this
    calc C * Real.exp (-c * h) * ∑ i ∈ Finset.range (s + 1), Real.exp (-c) ^ i
        ≤ C * Real.exp (-c * h) * (1 - Real.exp (-c))⁻¹ :=
          mul_le_mul_of_nonneg_left hgeo (by positivity)
      _ = C * (1 - Real.exp (-c))⁻¹ * Real.exp (-c * h) := by ring
  have hbound : ∑' e : ℕ × ℤ, F.fpDist s e
        * Set.indicator {q : ℕ × ℤ | (s : ℝ) + h ≤ (q.2 : ℝ)} (1 : ℕ × ℤ → ℝ≥0∞) e
      ≤ ENNReal.ofReal (C * (1 - Real.exp (-c))⁻¹ * Real.exp (-c * h)) := by
    calc _ ≤ _ := hE
      _ ≤ ∑ u ∈ Finset.range (s + 1), ENNReal.ofReal (C * Real.exp (-c * (h + u))) :=
          Finset.sum_le_sum fun u _ => hTu u
      _ = ENNReal.ofReal (∑ u ∈ Finset.range (s + 1), C * Real.exp (-c * (h + u))) :=
          (ENNReal.ofReal_sum_of_nonneg fun u _ => by positivity).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hsumR
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbound

/-- **Column tail of the first passage** (from `fpDist_col_le`):
`P(|e₁ - s·slopeInv| ≥ D) ≤ C(e^{-cD²/(1+s)} + e^{-cD})` (`D > 0`). -/
theorem fpDist_col_tail :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ (s : ℕ) (D : ℝ), 0 < D →
      ∑' e : ℕ × ℤ, (F.fpDist s e).toReal
          * Set.indicator {q : ℕ × ℤ | D ≤ |(q.1 : ℝ) - (s : ℝ) * F.slopeInv|} 1 e
        ≤ C * (Real.exp (-c * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-c * D)) := by
  obtain ⟨c₁, hc₁, C₁, hC₁, hcol⟩ := F.fpDist_col_le
  have hρ1 := _root_.GGMCollatz.FP.exp_neg_lt_one hc₁
  have hρpos : 0 < 1 - Real.exp (-c₁) := by linarith
  set c : ℝ := min (c₁ ^ 2) c₁ with hcdef
  have hcpos : 0 < c := lt_min (by positivity) hc₁
  have hcle1 : c ≤ c₁ ^ 2 := min_le_left _ _
  have hcle2 : c ≤ c₁ := min_le_right _ _
  set C : ℝ := Real.exp (c₁ ^ 2) + 2 * C₁ * (1 + 1 / c₁ ^ 2) + 2 * C₁ / (1 - Real.exp (-c₁))
    with hCdef
  have hCpos : 0 < C := by positivity
  refine ⟨c, hcpos, C, hCpos, ?_⟩
  intro s D hD
  set x₀ : ℝ := (s : ℝ) * F.slopeInv with hx₀
  set t : ℝ := 1 + (s : ℝ) with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith [Nat.cast_nonneg (α := ℝ) s]
  have ht0 : 0 < t := by linarith
  set S : Set (ℕ × ℤ) := {q : ℕ × ℤ | D ≤ |(q.1 : ℝ) - x₀|} with hS
  have hE1 : 0 ≤ Real.exp (-c * D ^ 2 / t) := (Real.exp_pos _).le
  have hE2 : 0 ≤ Real.exp (-c * D) := (Real.exp_pos _).le
  have hcmp1 : Real.exp (-(c₁ ^ 2 * D ^ 2 / t)) ≤ Real.exp (-c * D ^ 2 / t) := by
    apply Real.exp_le_exp.mpr
    have : c * D ^ 2 / t ≤ c₁ ^ 2 * D ^ 2 / t := by
      apply div_le_div_of_nonneg_right _ ht0.le
      exact mul_le_mul_of_nonneg_right hcle1 (sq_nonneg D)
    rw [neg_mul, neg_div]; linarith
  have hcmp2 : Real.exp (-c₁ * D) ≤ Real.exp (-c * D) := by
    apply Real.exp_le_exp.mpr; nlinarith
  by_cases hDt : D ^ 2 ≤ t
  · -- trivial case: probability `≤ 1`
    have h1 := _root_.GGMCollatz.FP.tsum_indicator_le_one (F.fpDist s) S
    have h2 : 1 ≤ Real.exp (c₁ ^ 2) * Real.exp (-(c₁ ^ 2 * D ^ 2 / t)) := by
      rw [← Real.exp_add]; apply Real.one_le_exp
      have : D ^ 2 / t ≤ 1 := (div_le_one ht0).mpr hDt
      have : c₁ ^ 2 * D ^ 2 / t ≤ c₁ ^ 2 := by
        rw [mul_div_assoc]; nlinarith [sq_nonneg c₁]
      linarith
    calc _ ≤ 1 := h1
      _ ≤ Real.exp (c₁ ^ 2) * Real.exp (-(c₁ ^ 2 * D ^ 2 / t)) := h2
      _ ≤ Real.exp (c₁ ^ 2) * Real.exp (-c * D ^ 2 / t) :=
          mul_le_mul_of_nonneg_left hcmp1 (Real.exp_pos _).le
      _ ≤ C * (Real.exp (-c * D ^ 2 / t) + Real.exp (-c * D)) := by
          have : Real.exp (c₁ ^ 2) ≤ C := by
            have hA1 : 0 ≤ 2 * C₁ * (1 + 1 / c₁ ^ 2) := by positivity
            have hA2 : 0 ≤ 2 * C₁ / (1 - Real.exp (-c₁)) := by positivity
            rw [hCdef]; linarith
          nlinarith
  · push Not at hDt
    have hsqrt1 : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht1
    have hsqrtD : Real.sqrt t ≤ D := by
      have := Real.sqrt_le_sqrt hDt.le
      rwa [Real.sqrt_sq hD.le] at this
    have hsqrt0 : 0 < Real.sqrt t := by linarith
    set a : ℝ := c₁ ^ 2 / t with ha
    have hapos : 0 < a := by positivity
    obtain ⟨hG1s, hG1⟩ := _root_.GGMCollatz.FP.tsum_gauss_tail x₀ D a hapos hD
    obtain ⟨hG2s, hG2⟩ := _root_.GGMCollatz.FP.tsum_exp_tail x₀ D c₁ hc₁
    -- bound for each column
    set f : ℕ × ℤ → ℝ := fun e => (F.fpDist s e).toReal * S.indicator 1 e with hf
    have hf0 : ∀ e, 0 ≤ f e := fun e =>
      mul_nonneg ENNReal.toReal_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) e)
    have hsumP : Summable fun e : ℕ × ℤ => (F.fpDist s e).toReal :=
      ENNReal.summable_toReal (F.fpDist s).tsum_coe_ne_top
    have hfs : Summable f := Summable.of_nonneg_of_le hf0
      (fun e => mul_le_of_le_one_right ENNReal.toReal_nonneg (by
        by_cases he : e ∈ S
        · simp [Set.indicator_of_mem he]
        · simp [Set.indicator_of_notMem he])) hsumP
    set B : ℕ → ℝ := fun j => C₁ / Real.sqrt t *
      ((if D ≤ |(j : ℝ) - x₀| then Real.exp (-(a * ((j : ℝ) - x₀) ^ 2)) else 0)
        + (if D ≤ |(j : ℝ) - x₀| then Real.exp (-c₁ * |(j : ℝ) - x₀|) else 0)) with hB
    have hBs : Summable B := (hG1s.add hG2s).mul_left _
    have hrow : ∀ j : ℕ, ∑' l : ℤ, f (j, l) ≤ B j := by
      intro j
      have hind : ∀ l : ℤ, S.indicator (1 : ℕ × ℤ → ℝ) (j, l)
          = if D ≤ |(j : ℝ) - x₀| then 1 else 0 := by
        intro l
        by_cases h : D ≤ |(j : ℝ) - x₀|
        · rw [if_pos h, Set.indicator_of_mem (show (j, l) ∈ S from h)]; rfl
        · rw [if_neg h, Set.indicator_of_notMem (show (j, l) ∉ S from h)]
      have heq : ∑' l : ℤ, f (j, l)
          = (∑' l : ℤ, (F.fpDist s (j, l)).toReal) * (if D ≤ |(j : ℝ) - x₀| then 1 else 0) := by
        rw [← tsum_mul_right]
        exact tsum_congr fun l => by simp only [hf, hind l]
      rw [heq]
      have hc := hcol s j
      by_cases h : D ≤ |(j : ℝ) - x₀|
      · rw [if_pos h, mul_one]
        simp only [hB, if_pos h]
        refine le_trans hc (le_of_eq ?_)
        unfold Sec7.Gweight
        have e1 : -((c₁ * ((j : ℝ) - (s : ℝ) * F.slopeInv)) ^ 2) / (1 + (s : ℝ))
            = -(a * ((j : ℝ) - x₀) ^ 2) := by rw [ha, ht, hx₀]; ring
        have e2 : |c₁ * ((j : ℝ) - (s : ℝ) * F.slopeInv)| = c₁ * |(j : ℝ) - x₀| := by
          rw [abs_mul, abs_of_pos hc₁, hx₀]
        rw [e1, e2, ← ht]
        ring_nf
      · rw [if_neg h, mul_zero]
        simp only [hB, if_neg h, add_zero, mul_zero, le_refl]
    have htsum : ∑' e : ℕ × ℤ, f e = ∑' j : ℕ, ∑' l : ℤ, f (j, l) :=
      hfs.tsum_prod' (fun j => hfs.prod_factor j)
    have hrows : Summable fun j : ℕ => ∑' l : ℤ, f (j, l) :=
      Summable.of_nonneg_of_le (fun j => tsum_nonneg fun l => hf0 _) hrow hBs
    have hBsum : ∑' j : ℕ, B j ≤ C₁ / Real.sqrt t *
        (2 * Real.exp (-(a * D ^ 2)) * (1 + 1 / (a * D))
          + 2 * Real.exp (-c₁ * D) / (1 - Real.exp (-c₁))) := by
      simp only [hB]
      rw [tsum_mul_left, hG1s.tsum_add hG2s]
      exact mul_le_mul_of_nonneg_left (add_le_add hG1 hG2) (by positivity)
    -- tidying the constants
    have hA1 : C₁ / Real.sqrt t * (2 * Real.exp (-(a * D ^ 2)) * (1 + 1 / (a * D)))
        ≤ 2 * C₁ * (1 + 1 / c₁ ^ 2) * Real.exp (-(c₁ ^ 2 * D ^ 2 / t)) := by
      have hexpeq : Real.exp (-(a * D ^ 2)) = Real.exp (-(c₁ ^ 2 * D ^ 2 / t)) := by
        rw [ha]; congr 1; ring
      rw [hexpeq]
      have hfac : 1 / Real.sqrt t * (1 + 1 / (a * D)) ≤ 1 + 1 / c₁ ^ 2 := by
        have h1 : 1 / Real.sqrt t ≤ 1 := by rw [div_le_one hsqrt0]; exact hsqrt1
        have h2 : 1 / Real.sqrt t * (1 / (a * D)) ≤ 1 / c₁ ^ 2 := by
          obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt t := ⟨_, rfl⟩
          rw [← hr]
          have hr0 : 0 < r := by rw [hr]; exact hsqrt0
          have hrD : r ≤ D := by rw [hr]; exact hsqrtD
          have hrt : r * r = t := by rw [hr]; exact Real.mul_self_sqrt ht0.le
          rw [one_div_mul_one_div]
          apply one_div_le_one_div_of_le (by positivity)
          have heq : r * (a * D) = c₁ ^ 2 * (D / r) := by
            rw [ha, ← hrt]; field_simp
          have hDs : 1 ≤ D / r := by rw [le_div_iff₀ hr0]; linarith
          rw [heq]; nlinarith [pow_pos hc₁ 2]
        nlinarith
      have hpos : 0 ≤ 2 * C₁ * Real.exp (-(c₁ ^ 2 * D ^ 2 / t)) := by positivity
      calc C₁ / Real.sqrt t * (2 * Real.exp (-(c₁ ^ 2 * D ^ 2 / t)) * (1 + 1 / (a * D)))
          = 2 * C₁ * Real.exp (-(c₁ ^ 2 * D ^ 2 / t))
              * (1 / Real.sqrt t * (1 + 1 / (a * D))) := by ring
        _ ≤ 2 * C₁ * Real.exp (-(c₁ ^ 2 * D ^ 2 / t)) * (1 + 1 / c₁ ^ 2) :=
            mul_le_mul_of_nonneg_left hfac hpos
        _ = _ := by ring
    have hA2 : C₁ / Real.sqrt t * (2 * Real.exp (-c₁ * D) / (1 - Real.exp (-c₁)))
        ≤ 2 * C₁ / (1 - Real.exp (-c₁)) * Real.exp (-c₁ * D) := by
      have h1 : C₁ / Real.sqrt t ≤ C₁ := div_le_self hC₁.le hsqrt1
      calc C₁ / Real.sqrt t * (2 * Real.exp (-c₁ * D) / (1 - Real.exp (-c₁)))
          ≤ C₁ * (2 * Real.exp (-c₁ * D) / (1 - Real.exp (-c₁))) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = _ := by ring
    have hmain : ∑' e : ℕ × ℤ, f e
        ≤ 2 * C₁ * (1 + 1 / c₁ ^ 2) * Real.exp (-(c₁ ^ 2 * D ^ 2 / t))
          + 2 * C₁ / (1 - Real.exp (-c₁)) * Real.exp (-c₁ * D) := by
      rw [htsum]
      calc ∑' j : ℕ, ∑' l : ℤ, f (j, l) ≤ ∑' j, B j := hrows.tsum_le_tsum hrow hBs
        _ ≤ _ := hBsum
        _ ≤ _ := by rw [mul_add]; exact add_le_add hA1 hA2
    have hfeq : ∑' e : ℕ × ℤ, (F.fpDist s e).toReal * S.indicator 1 e = ∑' e, f e := rfl
    calc ∑' e : ℕ × ℤ, (F.fpDist s e).toReal * S.indicator 1 e = ∑' e, f e := hfeq
      _ ≤ _ := hmain
      _ ≤ 2 * C₁ * (1 + 1 / c₁ ^ 2) * Real.exp (-c * D ^ 2 / t)
          + 2 * C₁ / (1 - Real.exp (-c₁)) * Real.exp (-c * D) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hcmp1 (by positivity)
          · exact mul_le_mul_of_nonneg_left hcmp2 (by positivity)
      _ ≤ C * Real.exp (-c * D ^ 2 / t) + C * Real.exp (-c * D) := by
          have hA2' : 0 ≤ 2 * C₁ / (1 - Real.exp (-c₁)) := div_nonneg (by positivity) hρpos.le
          have hA1' : 0 ≤ 2 * C₁ * (1 + 1 / c₁ ^ 2) := by positivity
          have hex := (Real.exp_pos (c₁ ^ 2)).le
          have hA1C : 2 * C₁ * (1 + 1 / c₁ ^ 2) ≤ C := by rw [hCdef]; linarith
          have hA2C : 2 * C₁ / (1 - Real.exp (-c₁)) ≤ C := by rw [hCdef]; linarith
          exact add_le_add (mul_le_mul_of_nonneg_right hA1C hE1)
            (mul_le_mul_of_nonneg_right hA2C hE2)
      _ = C * (Real.exp (-c * D ^ 2 / t) + Real.exp (-c * D)) := (mul_add _ _ _).symm

end FP

end Family

end GGMCollatz
