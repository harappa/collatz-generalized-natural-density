import GGMCollatz.NatDen.SumMixA.Basic

/-!
# Auxiliary (6) for Proposition 6.12 (a) of the paper: a polynomial lower bound for `P(s_n = s)` from the local limit theorem

A corollary of (T2) (the negative binomial local limit theorem): for `|s - μn| ≤ C √(n log n)`, `P(s_n = s) ≥ c₀ n^{-E}`
(`E = 1/2 + C²/(2σ_G²)`, `c₀ = (2πσ_G²)^{-1/2}/2`, for `n` large). The hypothesis is `lclt_statement`.

For `n` large, with `D := |s - μn|`, from `log n ≤ 10 n^{1/10}` we get `D² ≤ 10C² n^{11/10} ≤ n^{6/5}`
(so `D ≤ n^{3/5}`, the range of (LCLT)) and `D³/n² ≤ 10C² n^{-3/10}`, which makes the error of (LCLT) at most `1/2`.
-/

open scoped BigOperators ENNReal
open Filter Topology

namespace GGMCollatz

namespace ND

namespace SumMixAAux

open Family

variable (F : Family)

theorem sig2_pos : 0 < sig2 F.p := by
  have hp : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  unfold sig2
  apply div_pos (by linarith)
  have : (0 : ℝ) < (F.p : ℝ) - 1 := by linarith
  positivity

/-- **A polynomial lower bound for `P(s_n = s)`** (from (LCLT)). -/
theorem nb_lower (hL : lclt_statement F.p) (C : ℝ) (hC : 0 < C) :
    ∃ c₀ E : ℝ, 0 < c₀ ∧ 0 ≤ E ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ s : ℕ,
      |(s : ℝ) - muP F.p * n| ≤ C * Real.sqrt (n * Real.log n) →
        c₀ * (n : ℝ) ^ (-E) ≤ nb F.p n s := by
  obtain ⟨CL, hCL, hlclt⟩ := hL
  set σ2 : ℝ := sig2 F.p with hσ2def
  have hσ2 : 0 < σ2 := sig2_pos F
  set E : ℝ := 1 / 2 + C ^ 2 / (2 * σ2) with hEdef
  set c₀ : ℝ := (1 / 2) * (2 * Real.pi * σ2) ^ (-(1 / 2 : ℝ)) with hc₀def
  have hc₀ : 0 < c₀ := by positivity
  have hE : 0 ≤ E := by positivity
  -- the condition that `n` is large
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  have ev1 : ∀ᶠ n : ℕ in atTop, 10 * C ^ 2 ≤ (n : ℝ) ^ (1 / 10 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp hnat).eventually_ge_atTop _
  have ev2 : ∀ᶠ n : ℕ in atTop, CL * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 4 := by
    have h := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hnat).const_mul CL
    rw [mul_zero] at h
    exact h.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have ev3 : ∀ᶠ n : ℕ in atTop, CL * (10 * C ^ 2) * (n : ℝ) ^ (-(3 / 10 : ℝ)) ≤ 1 / 4 := by
    have h := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 10)).comp hnat).const_mul
      (CL * (10 * C ^ 2))
    rw [mul_zero] at h
    exact h.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have ev4 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (ev1.and (ev2.and (ev3.and ev4)))
  refine ⟨c₀, E, hc₀, hE, N₀, fun n hn s hs => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hN₀ n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast h4
  have hn0 : (0 : ℝ) < n := by linarith
  set D : ℝ := |(s : ℝ) - muP F.p * n| with hDdef
  have hD0 : 0 ≤ D := abs_nonneg _
  -- `D² ≤ 10 C² n n^{1/10}`
  have hlog : Real.log n ≤ 10 * (n : ℝ) ^ (1 / 10 : ℝ) := by
    have := Real.log_le_rpow_div hn0.le (by norm_num : (0 : ℝ) < 1 / 10)
    linarith [show (n : ℝ) ^ (1 / 10 : ℝ) / (1 / 10) = 10 * (n : ℝ) ^ (1 / 10 : ℝ) by ring]
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hr : 0 ≤ (n : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_nonneg hn0.le _
  have hD2 : D ^ 2 ≤ 10 * C ^ 2 * ((n : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ)) := by
    have hsq : D ^ 2 ≤ (C * Real.sqrt (n * Real.log n)) ^ 2 :=
      pow_le_pow_left₀ hD0 hs 2
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hn0.le hlog0)] at hsq
    calc D ^ 2 ≤ C ^ 2 * (n * Real.log n) := hsq
      _ ≤ C ^ 2 * (n * (10 * (n : ℝ) ^ (1 / 10 : ℝ))) := by gcongr
      _ = 10 * C ^ 2 * ((n : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ)) := by ring
  -- computing the exponent
  have e35 : ((n : ℝ) ^ (3 / 5 : ℝ)) ^ 2
      = (n : ℝ) ^ (1 / 10 : ℝ) * ((n : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    conv_rhs => rw [show (n : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ)
      = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
    norm_num
  have hDle : D ≤ (n : ℝ) ^ (3 / 5 : ℝ) := by
    have hle : D ^ 2 ≤ ((n : ℝ) ^ (3 / 5 : ℝ)) ^ 2 := by
      rw [e35]
      calc D ^ 2 ≤ 10 * C ^ 2 * ((n : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ)) := hD2
        _ ≤ (n : ℝ) ^ (1 / 10 : ℝ) * ((n : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ)) := by gcongr
    exact (sq_le_sq₀ hD0 (Real.rpow_nonneg hn0.le _)).mp hle
  -- `D³/n² ≤ 10 C² n^{-3/10}`
  have e310 : (n : ℝ) ^ (3 / 5 : ℝ) * ((n : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ)) / (n : ℝ) ^ 2
      = (n : ℝ) ^ (-(3 / 10 : ℝ)) := by
    rw [div_eq_iff (by positivity)]
    rw [show (n : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ)
      = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ) by rw [Real.rpow_one],
      ← Real.rpow_natCast (n : ℝ) 2]
    rw [← Real.rpow_add hn0, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
    norm_num
  have hD3 : D ^ 3 / (n : ℝ) ^ 2 ≤ 10 * C ^ 2 * (n : ℝ) ^ (-(3 / 10 : ℝ)) := by
    rw [← e310, div_le_iff₀ (by positivity)]
    have : D ^ 3 = D * D ^ 2 := by ring
    rw [this]
    calc D * D ^ 2 ≤ (n : ℝ) ^ (3 / 5 : ℝ) * (10 * C ^ 2 * ((n : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ))) :=
          mul_le_mul hDle hD2 (sq_nonneg _) (Real.rpow_nonneg hn0.le _)
      _ = 10 * C ^ 2 * ((n : ℝ) ^ (3 / 5 : ℝ) * ((n : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ)) /
            (n : ℝ) ^ 2) * (n : ℝ) ^ 2 := by
          field_simp
  -- (LCLT)
  have hl := hlclt n h4 s hDle
  set g : ℝ := gauss F.p n s with hgdef
  have hg0 : 0 ≤ g := by
    rw [hgdef]; unfold gauss
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
  have herr : CL * ((n : ℝ) ^ (-(1 / 2 : ℝ)) + D ^ 3 / (n : ℝ) ^ 2) ≤ 1 / 2 := by
    have : CL * (D ^ 3 / (n : ℝ) ^ 2) ≤ CL * (10 * C ^ 2) * (n : ℝ) ^ (-(3 / 10 : ℝ)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hD3 hCL.le
    rw [mul_add]; linarith
  have hnbg : g / 2 ≤ nb F.p n s := by
    have habs := (abs_le.mp hl).1
    have : CL * g * ((n : ℝ) ^ (-(1 / 2 : ℝ)) + D ^ 3 / (n : ℝ) ^ 2) ≤ g / 2 := by
      calc CL * g * ((n : ℝ) ^ (-(1 / 2 : ℝ)) + D ^ 3 / (n : ℝ) ^ 2)
          = g * (CL * ((n : ℝ) ^ (-(1 / 2 : ℝ)) + D ^ 3 / (n : ℝ) ^ 2)) := by ring
        _ ≤ g * (1 / 2) := mul_le_mul_of_nonneg_left herr hg0
        _ = g / 2 := by ring
    rw [← hDdef] at habs
    linarith
  -- lower bound for the Gaussian main term
  have hexp : Real.exp (-(C ^ 2 * Real.log n) / (2 * σ2)) ≤
      Real.exp (-((s : ℝ) - muP F.p * n) ^ 2 / (2 * σ2 * n)) := by
    apply Real.exp_le_exp.mpr
    have hsq : ((s : ℝ) - muP F.p * n) ^ 2 = D ^ 2 := (sq_abs _).symm
    rw [hsq]
    have hD2' : D ^ 2 ≤ C ^ 2 * (n * Real.log n) := by
      have := pow_le_pow_left₀ hD0 hs 2
      rwa [mul_pow, Real.sq_sqrt (mul_nonneg hn0.le hlog0)] at this
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hexp' : Real.exp (-(C ^ 2 * Real.log n) / (2 * σ2)) = (n : ℝ) ^ (-(C ^ 2 / (2 * σ2))) := by
    rw [Real.rpow_def_of_pos hn0]; congr 1; ring
  have hpre : (2 * Real.pi * σ2 * n) ^ (-(1 / 2 : ℝ))
      = (2 * Real.pi * σ2) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.mul_rpow (by positivity) hn0.le
  have hgl : (2 * Real.pi * σ2) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-E) ≤ g := by
    rw [hgdef]; unfold gauss
    rw [← hσ2def, hpre, hEdef, neg_add, Real.rpow_add hn0, ← mul_assoc, ← hexp']
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  calc c₀ * (n : ℝ) ^ (-E) = (1 / 2) * ((2 * Real.pi * σ2) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-E)) := by
        rw [hc₀def]; ring
    _ ≤ (1 / 2) * g := by gcongr
    _ = g / 2 := by ring
    _ ≤ nb F.p n s := hnbg

end SumMixAAux

end ND

end GGMCollatz
