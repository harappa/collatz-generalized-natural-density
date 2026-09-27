import GGMCollatz.NatDen.UProf.DKern.Core

/-!
# The parameters of (DK) (the part depending on the family `F`: inclusion of the central window)

`y = x^α`, `Y = (x^α)^α = x^{α²}`, `M ∈ [Mlo, Mhi]` (`log M = d m₀ + L + O(L^{0.7})`),
`u = log(Y/M)/log p`, `c = u/(μ - λ) = log(Y/M)/d` (the paper's `n'_*`).
Since `c = (α²-1)L/d - m₀ + O(L^{0.7})`, `m₀ = ⌊(α-1)L/(4d)⌋`, `n₀ = ⌊L/(5 log q)⌋`,
if `α ≤ α₀ = 1 + d/(30 log q)` (`α² - 1 ≤ d/(10 log q)`), then the central window `[c - L^{11/20}, c + L^{11/20}]`
lies in the row range `[m₀, n₀ - m₀]`.
-/

namespace GGMCollatz

namespace ND

namespace DKernAux

theorem lam_pos (F : Family) : 0 < lam F := by
  unfold lam
  exact div_pos F.log_q_pos F.log_p_pos

/-- `(μ - λ) log p = d`. -/
theorem dl_mul_log (F : Family) : (muP F.p - lam F) * Real.log F.p = F.drift := by
  unfold lam Family.drift Family.mu muP
  have := F.log_p_pos
  field_simp

theorem lam_lt_mu (F : Family) : lam F < muP F.p := by
  have h := dl_mul_log F
  have hd := F.drift_pos
  have hp := F.log_p_pos
  by_contra hc
  push Not at hc
  have : (muP F.p - lam F) * Real.log F.p ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hp.le
  linarith

set_option maxHeartbeats 1000000 in
/-- **Conditions on the parameters** (for `x` large, uniformly in `M ∈ [Mlo, Mhi]`). -/
theorem params (F : Family) {α : ℝ} (hα : 1 < α) (hα₀ : α ≤ 1 + F.drift / (30 * Real.log F.q)) :
    ∀ᶠ x : ℝ in Filter.atTop, 0 < x ^ α ∧ x ^ α ≤ (x ^ α) ^ α ∧ 1 ≤ F.mZero α x ∧
      2 * F.mZero α x ≤ F.nZero x ∧ ((F.nZero x - F.mZero α x : ℕ) : ℝ) ≤ Real.log x ∧
      (((F.nZero x - F.mZero α x : ℕ) : ℝ) + 1) * (x ^ α / (x ^ α) ^ α) ≤ Real.log x ^ (-(1 : ℝ)) ∧
      ∀ M : ℝ, F.Mlo α x ≤ M → M ≤ F.Mhi α x →
        0 < Real.log ((x ^ α) ^ α / M) / Real.log F.p ∧
        (α - 1) / F.drift * Real.log x
          ≤ Real.log ((x ^ α) ^ α / M) / Real.log F.p / (muP F.p - lam F) ∧
        (F.mZero α x : ℝ)
          ≤ Real.log ((x ^ α) ^ α / M) / Real.log F.p / (muP F.p - lam F)
            - Real.log x ^ (11 / 20 : ℝ) ∧
        Real.log ((x ^ α) ^ α / M) / Real.log F.p / (muP F.p - lam F)
            + Real.log x ^ (11 / 20 : ℝ) ≤ ((F.nZero x - F.mZero α x : ℕ) : ℝ) := by
  have hd := F.drift_pos
  have hlq := F.log_q_pos
  have hlp := F.log_p_pos
  have hpq := F.log_p_lt_log_q
  have hμ2 := F.mu_le_two
  have hdlt := F.drift_lt
  set d := F.drift with hddef
  set lq := Real.log F.q with hlqdef
  set δ := α - 1 with hδdef
  have hδ : 0 < δ := by linarith
  -- `d < 2 log q`, `δ ≤ d/(30 log q) ≤ 1/15`, `α² - 1 ≤ d/(14 log q)`
  have hd2 : d < 2 * lq := by nlinarith
  have hδ1 : δ ≤ d / (30 * lq) := by linarith
  have hδ2 : δ ≤ 1 / 15 := by
    refine le_trans hδ1 ?_
    rw [div_le_iff₀ (by positivity)]; linarith
  have hα2 : α * α - 1 ≤ d / (14 * lq) := by
    have e : α * α - 1 = δ * (2 + δ) := by rw [hδdef]; ring
    rw [e]
    calc δ * (2 + δ) ≤ d / (30 * lq) * (2 + 1 / 15) :=
          mul_le_mul hδ1 (by linarith) (by linarith) (by positivity)
      _ ≤ d / (14 * lq) := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  -- asymptotic facts
  have hlq5 : (1 : ℝ) / 5 < lq := by
    have h2 : Real.log 2 ≤ Real.log F.p :=
      Real.log_le_log (by norm_num) (by exact_mod_cast F.two_le_p)
    have := Real.log_two_gt_d9
    linarith
  set ε₀ : ℝ := min (δ / 2) (9 / (70 * lq)) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min (by positivity) (by positivity)
  set K₀ : ℝ := 1 / d + d + 2 with hK₀
  have hev1 := Family.eventually_add_mul_rpow_le (show (0.7 : ℝ) < 1 by norm_num) one_pos 1 K₀ hε₀0
  have hev2 := Family.eventually_mul_rpow_neg_le_log (show 0 < α * α - α by nlinarith) 3 1
  filter_upwards [hev1, hev2, F.eventually_mZero_ge hα, Family.eventually_log_ge 2,
    Filter.eventually_gt_atTop 1] with x h1 h2 hm hL2 hx1
  set L := Real.log x with hLdef
  rw [Real.rpow_one] at h1
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  have h07 : 0 ≤ L ^ (0.7 : ℝ) := Real.rpow_nonneg hL0.le _
  have h1120 : L ^ (11 / 20 : ℝ) ≤ L ^ (0.7 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hsmall : K₀ * L ^ (0.7 : ℝ) + 1 ≤ ε₀ * L := by linarith
  have hε₁ : ε₀ ≤ δ / 2 := min_le_left _ _
  have hε₂ : ε₀ ≤ 9 / (70 * lq) := min_le_right _ _
  have hK₀L : (1 / d + d + 2) * L ^ (0.7 : ℝ) = K₀ * L ^ (0.7 : ℝ) := rfl
  have hd1 : 0 < 1 / d := by positivity
  -- `m₀`, `n₀`
  set m₀ := F.mZero α x with hm₀
  set n₀ := F.nZero x with hn₀
  obtain ⟨-, hm1⟩ := hm
  have hm0le : (m₀ : ℝ) ≤ δ * L / (4 * d) := by
    rw [hm₀]; unfold Family.mZero; exact Nat.floor_le (by positivity)
  have hdm : d * m₀ ≤ δ * L / 4 := by
    have := mul_le_mul_of_nonneg_left hm0le hd.le
    rw [show d * (δ * L / (4 * d)) = δ * L / 4 by field_simp] at this
    exact this
  have hn0le : (n₀ : ℝ) ≤ L / (5 * lq) := by
    rw [hn₀]; unfold Family.nZero; exact Nat.floor_le (by positivity)
  have hn0ge : L / (5 * lq) - 1 < n₀ := by
    rw [hn₀]; unfold Family.nZero; exact Nat.sub_one_lt_floor _
  -- inequalities in a convenient form
  have hKexp : K₀ * L ^ (0.7 : ℝ) = 1 / d * L ^ (0.7 : ℝ) + d * L ^ (0.7 : ℝ) + 2 * L ^ (0.7 : ℝ) := by
    rw [hK₀]; ring
  have hdL : 0 ≤ 1 / d * L ^ (0.7 : ℝ) := by positivity
  have hdL' : 0 ≤ d * L ^ (0.7 : ℝ) := by positivity
  have hε₁L : ε₀ * L ≤ δ / 2 * L := mul_le_mul_of_nonneg_right hε₁ hL0.le
  have hε₂L : ε₀ * L ≤ 9 / (70 * lq) * L := mul_le_mul_of_nonneg_right hε₂ hL0.le
  have h9 : 9 / (70 * lq) * L = L / (5 * lq) - L / (14 * lq) := by field_simp; ring
  have h11 : L / (60 * lq) ≤ L / (5 * lq) - L / (14 * lq) := by
    rw [← h9, div_le_iff₀ (by positivity)]
    have : 0 ≤ L := hL0.le
    field_simp
    nlinarith
  have hδL : δ * L ≤ d * L / (30 * lq) := by
    have := mul_le_mul_of_nonneg_right hδ1 hL0.le
    rwa [div_mul_eq_mul_div] at this
  have h1460 : L / (60 * lq) ≤ L / (14 * lq) :=
    div_le_div_of_nonneg_left hL0.le (by positivity) (by nlinarith)
  have hm2 : 2 * m₀ ≤ n₀ := by
    have : (2 * m₀ : ℝ) ≤ n₀ := by
      have h60 : 2 * (δ * L / (4 * d)) ≤ L / (60 * lq) := by
        have e : 2 * (δ * L / (4 * d)) = δ * L / (2 * d) := by field_simp; ring
        rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
        rw [le_div_iff₀ (by positivity)] at hδL
        nlinarith
      have h07' : 0 ≤ 2 * L ^ (0.7 : ℝ) := by positivity
      linarith
    exact_mod_cast this
  have hmn : m₀ ≤ n₀ := le_trans (Nat.le_mul_of_pos_left m₀ (by norm_num)) hm2
  have hcast : ((n₀ - m₀ : ℕ) : ℝ) = n₀ - m₀ := by rw [Nat.cast_sub hmn]
  have hnL : (n₀ : ℝ) ≤ L := by
    refine le_trans hn0le ?_
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hm00 : (0 : ℝ) ≤ m₀ := Nat.cast_nonneg _
  -- the window ratio `y/Y`
  have hxa : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  have hxa1 : 1 ≤ x ^ α := Real.one_le_rpow (by linarith) (by linarith)
  have hYeq : (x ^ α) ^ α = x ^ (α * α) := by rw [← Real.rpow_mul hx0.le]
  have hratio : x ^ α / (x ^ α) ^ α = x ^ (-(α * α - α)) := by
    rw [hYeq, ← Real.rpow_sub hx0]; ring_nf
  have hlogY : Real.log ((x ^ α) ^ α) = α * α * L := by
    rw [hYeq, Real.log_rpow hx0]
  refine ⟨hxa, ?_, hm1, hm2, ?_, ?_, ?_⟩
  · calc x ^ α = (x ^ α) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (x ^ α) ^ α := Real.rpow_le_rpow_of_exponent_le hxa1 hα.le
  · rw [hcast]; linarith
  · rw [hratio]
    rw [one_mul] at h2
    have hL2' : L ^ (2 : ℝ) = L ^ 2 := Real.rpow_two L
    have hL3 : L ^ (-(3 : ℝ)) = L ^ (-(1 : ℝ)) * (L ^ 2)⁻¹ := by
      rw [← hL2', ← Real.rpow_neg hL0.le, ← Real.rpow_add hL0]; norm_num
    have hLL : L + 1 ≤ L ^ 2 := by nlinarith
    have hinv : 0 < L ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos hL0 _
    calc (((n₀ - m₀ : ℕ) : ℝ) + 1) * x ^ (-(α * α - α)) ≤ (L + 1) * L ^ (-(3 : ℝ)) := by
          apply mul_le_mul _ h2 (Real.rpow_nonneg hx0.le _) (by linarith)
          rw [hcast]; linarith
      _ = L ^ (-(1 : ℝ)) * ((L + 1) / L ^ 2) := by rw [hL3]; ring
      _ ≤ L ^ (-(1 : ℝ)) * 1 := by
          apply mul_le_mul_of_nonneg_left _ hinv.le
          rw [div_le_one (by positivity)]; exact hLL
      _ = L ^ (-(1 : ℝ)) := mul_one _
  · intro M hM1 hM2
    have hMpos : 0 < M := lt_of_lt_of_le (Real.exp_pos _) hM1
    have hlogM1 : d * m₀ + L - L ^ (0.7 : ℝ) ≤ Real.log M := by
      have := Real.log_le_log (Real.exp_pos _) hM1
      rwa [Real.log_exp] at this
    have hlogM2 : Real.log M ≤ d * m₀ + L + L ^ (0.7 : ℝ) := by
      have := Real.log_le_log hMpos hM2
      unfold Family.Mhi at this
      rwa [Real.log_exp] at this
    have hlogYM : Real.log ((x ^ α) ^ α / M) = α * α * L - Real.log M := by
      rw [Real.log_div (by positivity) hMpos.ne', hlogY]
    have hc : Real.log ((x ^ α) ^ α / M) / Real.log F.p / (muP F.p - lam F)
        = (α * α * L - Real.log M) / d := by
      rw [div_div, mul_comm (Real.log F.p), dl_mul_log, hlogYM]
    rw [hc]
    have hA1 : 2 * δ * L ≤ α * α * L - L := by
      have e : α * α * L - L = δ * (α + 1) * L := by rw [hδdef]; ring
      rw [e]
      have : 2 * δ ≤ δ * (α + 1) := by nlinarith
      exact mul_le_mul_of_nonneg_right this hL0.le
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- `u > 0`
      apply div_pos _ hlp
      linarith
    · -- `c ≥ (α-1)L/d`
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hd]
      linarith
    · -- `m₀ ≤ c - L^{11/20}`
      rw [le_sub_iff_add_le, le_div_iff₀ hd]
      have : d * L ^ (11 / 20 : ℝ) ≤ d * L ^ (0.7 : ℝ) := mul_le_mul_of_nonneg_left h1120 hd.le
      linarith
    · -- `c + L^{11/20} ≤ n₀ - m₀`
      rw [hcast]
      have hA : (α * α - 1) * L ≤ d / (14 * lq) * L := mul_le_mul_of_nonneg_right hα2 hL0.le
      have hcu : (α * α * L - Real.log M) / d ≤ L / (14 * lq) - m₀ + 1 / d * L ^ (0.7 : ℝ) := by
        rw [div_le_iff₀ hd]
        have e : (L / (14 * lq) - m₀ + 1 / d * L ^ (0.7 : ℝ)) * d
            = d / (14 * lq) * L - d * m₀ + L ^ (0.7 : ℝ) := by field_simp
        rw [e]; linarith
      linarith

end DKernAux

end ND

end GGMCollatz
