import GGMCollatz.NatDen.UProf.Master.Asymp

/-!
# Asymptotic ingredients of (UM): bounding the sum of the four errors

`L = log x`, `c = (α-1)/(8d)` (`m₀ ≥ cL`).

* `epsX_le`: `ε(x) ≤ K (2 + √(10/c)) L^{-1/4}` (`m₁ ≍ L^{0.4}`, `log n₀ ≤ 10 L^{0.1}`).
* `beta_le`: `C/√(1+m₀) ≤ (C/√c) L^{-1/2}`.
* `NR_le`: `N_R(R_{n₀}) ≤ A_N L^{0.55}` (`R_{n₀} = 1600 √(n₀ log n₀) ≤ 1600 √10 L^{0.55}`).
* `half_factor_le`: `x^{1/2} q^{n₀}/Mlo ≤ x^{-1/5}` (`q^{n₀} ≤ x^{1/5}`, `Mlo ≥ x e^{-L^{0.7}}`).
* `asymp`: the sum of the four errors is at most `K' L^{-1/5}`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace MasterAux

variable (F : Family)

/-- `L · L^a = L^{1+a}`. -/
theorem mul_rpow_eq {L a : ℝ} (hL : 0 < L) : L * L ^ a = L ^ (1 + a) := by
  rw [Real.rpow_add hL, Real.rpow_one]

/-- `log n₀ ≤ 10 L^{0.1}`. -/
theorem log_nZero_le {x : ℝ} (hx1 : 1 ≤ x) :
    Real.log (F.nZero x) ≤ 10 * Real.log x ^ (0.1 : ℝ) := by
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hn0 : (F.nZero x : ℝ) ≤ Real.log x := by have := F.nZero_le hx1; linarith
  have hr := Real.log_le_rpow_div hL0 (by norm_num : (0 : ℝ) < 0.1)
  have hr' : Real.log x ^ (0.1 : ℝ) / 0.1 = 10 * Real.log x ^ (0.1 : ℝ) := by ring
  rcases Nat.eq_zero_or_pos (F.nZero x) with h | h
  · rw [h, Nat.cast_zero, Real.log_zero]
    positivity
  · have := Real.log_le_log (by exact_mod_cast h) hn0
    linarith

/-- `ε(x) ≤ K (2 + √(10/c)) L^{-1/4}`. -/
theorem epsX_le {Kc α x c : ℝ} (hKc : 0 ≤ Kc) (hc0 : 0 < c) (hx1 : 1 ≤ x)
    (hL1 : 1 ≤ Real.log x) (hcL : c * Real.log x ≤ F.mZero α x)
    (hm1ge : Real.log x ^ (0.4 : ℝ) / 2 ≤ m1 x) (hm1le : (m1 x : ℝ) ≤ Real.log x ^ (0.4 : ℝ)) :
    epsX F Kc α x ≤ Kc * (2 + Real.sqrt (10 / c)) * Real.log x ^ (-(1 / 4 : ℝ)) := by
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hm0pos : (0 : ℝ) < F.mZero α x := lt_of_lt_of_le (by positivity) hcL
  have hL04 : 0 < L ^ (0.4 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hm1pos : (0 : ℝ) < m1 x := lt_of_lt_of_le (by positivity) hm1ge
  -- first term
  have t1 : (m1 x : ℝ) ^ (-1 : ℝ) ≤ 2 * L ^ (-(1 / 4 : ℝ)) := by
    rw [Real.rpow_neg_one]
    have e1 : (m1 x : ℝ)⁻¹ ≤ (L ^ (0.4 : ℝ) / 2)⁻¹ := inv_anti₀ (by positivity) hm1ge
    have e2 : (L ^ (0.4 : ℝ) / 2)⁻¹ = 2 * L ^ (-(0.4 : ℝ)) := by
      rw [Real.rpow_neg hL0.le]; field_simp
    have e3 : L ^ (-(0.4 : ℝ)) ≤ L ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    linarith
  -- second term
  have hlog := log_nZero_le F hx1
  have hq : (m1 x : ℝ) * Real.log (F.nZero x) / F.mZero α x ≤ 10 / c * L ^ (-(1 / 2 : ℝ)) := by
    rw [div_le_iff₀ hm0pos]
    have hh : L ^ (-(1 / 2 : ℝ)) * L = L ^ (0.5 : ℝ) := by
      have : L ^ (-(1 / 2 : ℝ)) * L ^ (1 : ℝ) = L ^ (0.5 : ℝ) := by
        rw [← Real.rpow_add hL0]; norm_num
      rwa [Real.rpow_one] at this
    calc (m1 x : ℝ) * Real.log (F.nZero x) ≤ L ^ (0.4 : ℝ) * (10 * L ^ (0.1 : ℝ)) :=
          mul_le_mul hm1le hlog (Real.log_natCast_nonneg _) hL04.le
      _ = 10 * L ^ (0.5 : ℝ) := by
          rw [mul_left_comm, ← Real.rpow_add hL0]; norm_num
      _ = 10 / c * L ^ (-(1 / 2 : ℝ)) * (c * L) := by
          rw [← hh]; field_simp
      _ ≤ 10 / c * L ^ (-(1 / 2 : ℝ)) * F.mZero α x :=
          mul_le_mul_of_nonneg_left hcL (by positivity)
  have t2 : Real.sqrt ((m1 x : ℝ) * Real.log (F.nZero x) / F.mZero α x)
      ≤ Real.sqrt (10 / c) * L ^ (-(1 / 4 : ℝ)) := by
    calc _ ≤ Real.sqrt (10 / c * L ^ (-(1 / 2 : ℝ))) := Real.sqrt_le_sqrt hq
      _ = Real.sqrt (10 / c) * Real.sqrt (L ^ (-(1 / 2 : ℝ))) := Real.sqrt_mul (by positivity) _
      _ = _ := by
          rw [Real.sqrt_eq_rpow (L ^ _), ← Real.rpow_mul hL0.le]; norm_num
  unfold epsX
  calc Kc * ((m1 x : ℝ) ^ (-1 : ℝ) + Real.sqrt ((m1 x : ℝ) * Real.log (F.nZero x) / F.mZero α x))
      ≤ Kc * (2 * L ^ (-(1 / 4 : ℝ)) + Real.sqrt (10 / c) * L ^ (-(1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add t1 t2) hKc
    _ = _ := by ring

/-- `C/√(1+m₀) ≤ (C/√c) L^{-1/2}`. -/
theorem beta_le {Cl α x c : ℝ} (hCl : 0 ≤ Cl) (hc0 : 0 < c) (hL0 : 0 < Real.log x)
    (hcL : c * Real.log x ≤ F.mZero α x) :
    Cl / Real.sqrt (1 + F.mZero α x) ≤ Cl / Real.sqrt c * Real.log x ^ (-(1 / 2 : ℝ)) := by
  set L := Real.log x
  have hsq : 0 < Real.sqrt (c * L) := Real.sqrt_pos.mpr (by positivity)
  have h1 : Real.sqrt (c * L) ≤ Real.sqrt (1 + F.mZero α x) := Real.sqrt_le_sqrt (by linarith)
  calc Cl / Real.sqrt (1 + F.mZero α x) ≤ Cl / Real.sqrt (c * L) :=
        div_le_div_of_nonneg_left hCl hsq h1
    _ = Cl / Real.sqrt c * Real.log x ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_mul hc0.le, Real.rpow_neg hL0.le, ← Real.sqrt_eq_rpow]
        field_simp

/-- `N_R(R_{n₀}) ≤ A_N L^{0.55}`. -/
theorem NR_le {x : ℝ} (hx1 : 1 ≤ x) (hL1 : 1 ≤ Real.log x) :
    NR F (rad (F.nZero x)) ≤
      (3200 * Real.sqrt 10 * Real.log F.p / F.drift + 1
        + Real.exp F.drift / (Real.exp F.drift - 1)) * Real.log x ^ (0.55 : ℝ) := by
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  have hd := F.drift_pos
  have hlp := F.log_p_pos
  have hed : 1 < Real.exp F.drift := by have := Real.add_one_lt_exp hd.ne'; linarith
  have hEd : 0 ≤ Real.exp F.drift / (Real.exp F.drift - 1) :=
    div_nonneg (Real.exp_pos _).le (by linarith)
  have hn0 : (F.nZero x : ℝ) ≤ L := by have := F.nZero_le hx1; linarith
  have hlog := log_nZero_le F hx1
  have hL55 : 1 ≤ L ^ (0.55 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hrad : rad (F.nZero x) ≤ 1600 * Real.sqrt 10 * L ^ (0.55 : ℝ) := by
    unfold rad
    have e1 : (F.nZero x : ℝ) * Real.log (F.nZero x) ≤ 10 * L ^ (1.1 : ℝ) := by
      calc (F.nZero x : ℝ) * Real.log (F.nZero x) ≤ L * (10 * L ^ (0.1 : ℝ)) :=
            mul_le_mul hn0 hlog (Real.log_natCast_nonneg _) hL0.le
        _ = 10 * L ^ (1.1 : ℝ) := by
            have : L * L ^ (0.1 : ℝ) = L ^ (1.1 : ℝ) := by
              rw [mul_rpow_eq hL0]; norm_num
            rw [← this]; ring
    have e2 : Real.sqrt (10 * L ^ (1.1 : ℝ)) = Real.sqrt 10 * L ^ (0.55 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (L ^ _), ← Real.rpow_mul hL0.le]
      norm_num
    calc 1600 * Real.sqrt ((F.nZero x : ℝ) * Real.log (F.nZero x))
        ≤ 1600 * Real.sqrt (10 * L ^ (1.1 : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt e1) (by norm_num)
      _ = _ := by rw [e2]; ring
  unfold NR
  have e3 : 2 * rad (F.nZero x) * Real.log F.p / F.drift
      ≤ 3200 * Real.sqrt 10 * Real.log F.p / F.drift * L ^ (0.55 : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hd]
    nlinarith
  have e4 : 1 + Real.exp F.drift / (Real.exp F.drift - 1)
      ≤ (1 + Real.exp F.drift / (Real.exp F.drift - 1)) * L ^ (0.55 : ℝ) := by
    nlinarith
  nlinarith

/-- `x^{1/2} q^{n₀}/Mlo ≤ x^{-1/5}` (when `10 L^{0.7} ≤ L`). -/
theorem half_factor_le {α x : ℝ} (hx : 0 < x) (hL0 : 0 ≤ Real.log x)
    (h7 : 10 * Real.log x ^ (0.7 : ℝ) ≤ Real.log x) :
    x ^ (1 / 2 : ℝ) * (F.q : ℝ) ^ F.nZero x / F.Mlo α x ≤ x ^ (-(1 / 5 : ℝ)) := by
  set L := Real.log x with hLdef
  have hlq := F.log_q_pos
  have hd := F.drift_pos
  have hq : (F.q : ℝ) ^ F.nZero x ≤ Real.exp (L / 5) := by
    have e1 : (F.q : ℝ) ^ F.nZero x = Real.exp ((F.nZero x : ℝ) * Real.log F.q) := by
      rw [Real.exp_nat_mul, Real.exp_log F.q_real_pos]
    have e2 : (F.nZero x : ℝ) * Real.log F.q ≤ L / 5 := by
      have : (F.nZero x : ℝ) ≤ L / (5 * Real.log F.q) := Nat.floor_le (by positivity)
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    rw [e1]; exact Real.exp_le_exp.mpr e2
  have hM : Real.exp (L - L ^ (0.7 : ℝ)) ≤ F.Mlo α x := by
    unfold Family.Mlo
    apply Real.exp_le_exp.mpr
    have : 0 ≤ F.drift * (F.mZero α x : ℝ) := mul_nonneg hd.le (Nat.cast_nonneg _)
    linarith
  have hx12 : x ^ (1 / 2 : ℝ) = Real.exp (L / 2) := by
    rw [Real.rpow_def_of_pos hx, ← hLdef]; ring_nf
  have hx15 : x ^ (-(1 / 5 : ℝ)) = Real.exp (-(L / 5)) := by
    rw [Real.rpow_def_of_pos hx, ← hLdef]; ring_nf
  rw [hx12, hx15, div_le_iff₀ (lt_of_lt_of_le (Real.exp_pos _) hM)]
  calc Real.exp (L / 2) * (F.q : ℝ) ^ F.nZero x ≤ Real.exp (L / 2) * Real.exp (L / 5) :=
        mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
    _ = Real.exp (-(L / 5)) * Real.exp (L - L / 10) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(L / 5)) * Real.exp (L - L ^ (0.7 : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
    _ ≤ Real.exp (-(L / 5)) * F.Mlo α x := mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le

/-- **The sum of the four errors** is at most `K' L^{-1/5}`. -/
theorem asymp {α : ℝ} (hα : 1 < α) {K₁ Kc Cl : ℝ} (hK₁ : 0 ≤ K₁) (hKc : 0 ≤ Kc) (hCl : 0 ≤ Cl) :
    ∃ K' : ℝ, 0 < K' ∧ ∀ᶠ x : ℝ in Filter.atTop,
      K₁ * ((F.nZero x : ℝ) + 1) * Real.log x ^ (-4 : ℝ)
          + 2 * K₁ * ((F.nZero x : ℝ) + 1) * (4 / (F.mZero α x : ℝ) ^ 2)
          + epsX F Kc α x * (Cl / Real.sqrt (1 + F.mZero α x)) * ((F.p : ℝ) / ((F.p : ℝ) - 1))
              * NR F (rad (F.nZero x)) * K₁
          + epsX F Kc α x * (Cl / Real.sqrt (1 + F.mZero α x)) * x ^ (1 / 2 : ℝ)
              * ((F.nZero x : ℝ) + 1) * ((F.p : ℝ) / ((F.p : ℝ) - 1))
              * (F.q : ℝ) ^ F.nZero x / F.Mlo α x
        ≤ K' * Real.log x ^ (-(1 / 5 : ℝ)) := by
  have hd := F.drift_pos
  set c := (α - 1) / (8 * F.drift) with hc
  have hc0 : 0 < c := div_pos (by linarith) (by linarith)
  set Pp := (F.p : ℝ) / ((F.p : ℝ) - 1) with hPp
  have hPp0 : 0 < Pp := div_pos F.p_real_pos (by linarith [F.one_lt_p_real])
  set Aε := Kc * (2 + Real.sqrt (10 / c)) with hAε
  have hAε0 : 0 ≤ Aε := mul_nonneg hKc (by positivity)
  set Aβ := Cl / Real.sqrt c with hAβ
  have hAβ0 : 0 ≤ Aβ := div_nonneg hCl (Real.sqrt_nonneg _)
  set AN := 3200 * Real.sqrt 10 * Real.log F.p / F.drift + 1
    + Real.exp F.drift / (Real.exp F.drift - 1) with hAN
  have hed : 1 < Real.exp F.drift := by have := Real.add_one_lt_exp hd.ne'; linarith
  have hAN0 : 0 ≤ AN := by
    have h1 : 0 ≤ 3200 * Real.sqrt 10 * Real.log F.p / F.drift :=
      div_nonneg (mul_nonneg (by positivity) F.log_p_pos.le) hd.le
    have h2 : 0 ≤ Real.exp F.drift / (Real.exp F.drift - 1) :=
      div_nonneg (Real.exp_pos _).le (by linarith)
    linarith
  set C3 := Aε * Aβ * Pp * AN * K₁ with hC3
  have hC30 : 0 ≤ C3 := by positivity
  set C4 := Aε * Cl * Pp with hC4
  have hC40 : 0 ≤ C4 := by positivity
  refine ⟨K₁ + 8 * K₁ / c ^ 2 + C3 + 1, by positivity, ?_⟩
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ), Filter.eventually_ge_atTop (1 : ℝ),
    F.eventually_mZero_ge hα, Family.eventually_log_ge 2,
    Family.eventually_mul_log_rpow_le (show (0 : ℝ) < 0.4 by norm_num) 2,
    Family.eventually_mul_log_rpow_le (show (0.7 : ℝ) < 1 by norm_num) 10,
    Family.eventually_mul_rpow_neg_le_log (show (0 : ℝ) < 1 / 5 by norm_num) (6 / 5) C4]
    with x hx hx1 hm0 hL2 h04 h07 hx5
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  rw [Real.rpow_zero, mul_one] at h04
  rw [Real.rpow_one] at h07
  obtain ⟨hm0c, hm01⟩ := hm0
  have hcL : c * L ≤ F.mZero α x := by
    have : c * L = (α - 1) * L / (8 * F.drift) := by rw [hc]; ring
    rw [this]; exact hm0c
  have hn1 : (F.nZero x : ℝ) + 1 ≤ L := by have := F.nZero_le hx1; linarith
  have hm1le : (m1 x : ℝ) ≤ L ^ (0.4 : ℝ) := Nat.floor_le (Real.rpow_nonneg hL0.le _)
  have hm1ge : L ^ (0.4 : ℝ) / 2 ≤ (m1 x : ℝ) := by
    have := Nat.lt_floor_add_one (L ^ (0.4 : ℝ))
    unfold m1; linarith
  -- each factor
  have hε := epsX_le F hKc hc0 hx1 hL1 hcL hm1ge hm1le
  have hβ := beta_le F hCl hc0 hL0 hcL
  have hβ0 : 0 ≤ Cl / Real.sqrt (1 + F.mZero α x) := div_nonneg hCl (Real.sqrt_nonneg _)
  have hN := NR_le F hx1 hL1
  have hN0 : 0 ≤ NR F (rad (F.nZero x)) := by
    unfold NR
    have h1 : 0 ≤ 2 * rad (F.nZero x) * Real.log F.p / F.drift := by
      unfold rad
      exact div_nonneg (mul_nonneg (by positivity) F.log_p_pos.le) hd.le
    have h2 : 0 ≤ Real.exp F.drift / (Real.exp F.drift - 1) :=
      div_nonneg (Real.exp_pos _).le (by linarith)
    linarith
  have hL14 : L ^ (-(1 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  -- (1) good tuples
  have T1 : K₁ * ((F.nZero x : ℝ) + 1) * L ^ (-4 : ℝ) ≤ K₁ * L ^ (-(1 / 5 : ℝ)) := by
    have e1 : L * L ^ (-4 : ℝ) = L ^ (-3 : ℝ) := by
      rw [mul_rpow_eq hL0]; norm_num
    have e2 : L ^ (-3 : ℝ) ≤ L ^ (-(1 / 5 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have e3 : ((F.nZero x : ℝ) + 1) * L ^ (-4 : ℝ) ≤ L * L ^ (-4 : ℝ) :=
      mul_le_mul_of_nonneg_right hn1 (Real.rpow_nonneg hL0.le _)
    calc K₁ * ((F.nZero x : ℝ) + 1) * L ^ (-4 : ℝ)
        = K₁ * (((F.nZero x : ℝ) + 1) * L ^ (-4 : ℝ)) := by ring
      _ ≤ K₁ * L ^ (-(1 / 5 : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) hK₁
  -- (2) non-central `s`
  have T2 : 2 * K₁ * ((F.nZero x : ℝ) + 1) * (4 / (F.mZero α x : ℝ) ^ 2)
      ≤ 8 * K₁ / c ^ 2 * L ^ (-(1 / 5 : ℝ)) := by
    have e1 : 4 / (F.mZero α x : ℝ) ^ 2 ≤ 4 / (c * L) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ (by positivity) hcL 2)
    have e2 : L ^ (-(1 : ℝ)) ≤ L ^ (-(1 / 5 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have e3 : L ^ (-(1 : ℝ)) = 1 / L := by rw [Real.rpow_neg hL0.le, Real.rpow_one, one_div]
    have h4 : 0 ≤ 4 / (F.mZero α x : ℝ) ^ 2 := by positivity
    calc 2 * K₁ * ((F.nZero x : ℝ) + 1) * (4 / (F.mZero α x : ℝ) ^ 2)
        ≤ 2 * K₁ * L * (4 / (F.mZero α x : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn1 (by positivity)) h4
      _ ≤ 2 * K₁ * L * (4 / (c * L) ^ 2) := mul_le_mul_of_nonneg_left e1 (by positivity)
      _ = 8 * K₁ / c ^ 2 * L ^ (-(1 : ℝ)) := by rw [e3]; field_simp; ring
      _ ≤ 8 * K₁ / c ^ 2 * L ^ (-(1 / 5 : ℝ)) :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
  -- (3) the main part of the product-formula error
  have T3 : epsX F Kc α x * (Cl / Real.sqrt (1 + F.mZero α x)) * Pp * NR F (rad (F.nZero x)) * K₁
      ≤ C3 * L ^ (-(1 / 5 : ℝ)) := by
    have hexp : L ^ (-(1 / 4 : ℝ)) * L ^ (-(1 / 2 : ℝ)) * L ^ (0.55 : ℝ)
        = L ^ (-(1 / 5 : ℝ)) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
    have hA : epsX F Kc α x * (Cl / Real.sqrt (1 + F.mZero α x))
        ≤ (Aε * L ^ (-(1 / 4 : ℝ))) * (Aβ * L ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul hε hβ hβ0 (by positivity)
    have hB : epsX F Kc α x * (Cl / Real.sqrt (1 + F.mZero α x)) * Pp * NR F (rad (F.nZero x))
        ≤ (Aε * L ^ (-(1 / 4 : ℝ))) * (Aβ * L ^ (-(1 / 2 : ℝ))) * Pp * (AN * L ^ (0.55 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hA hPp0.le) hN hN0 (by positivity)
    calc _ ≤ (Aε * L ^ (-(1 / 4 : ℝ))) * (Aβ * L ^ (-(1 / 2 : ℝ))) * Pp
            * (AN * L ^ (0.55 : ℝ)) * K₁ :=
          mul_le_mul_of_nonneg_right hB hK₁
      _ = C3 * (L ^ (-(1 / 4 : ℝ)) * L ^ (-(1 / 2 : ℝ)) * L ^ (0.55 : ℝ)) := by
          rw [hC3]; ring
      _ = C3 * L ^ (-(1 / 5 : ℝ)) := by rw [hexp]
  -- (4) the `x^{1/2}` part of (EP2)
  have T4 : epsX F Kc α x * (Cl / Real.sqrt (1 + F.mZero α x)) * x ^ (1 / 2 : ℝ)
        * ((F.nZero x : ℝ) + 1) * Pp * (F.q : ℝ) ^ F.nZero x / F.Mlo α x
      ≤ 1 * L ^ (-(1 / 5 : ℝ)) := by
    have hhalf := half_factor_le F (α := α) hx hL0.le h07
    have hβ1 : Cl / Real.sqrt (1 + F.mZero α x) ≤ Cl :=
      div_le_self hCl (Real.one_le_sqrt.mpr (by
        have : (0 : ℝ) ≤ F.mZero α x := Nat.cast_nonneg _
        linarith))
    have hε1 : epsX F Kc α x ≤ Aε := hε.trans (mul_le_of_le_one_right hAε0 hL14)
    have hε0 : 0 ≤ epsX F Kc α x := by
      unfold epsX
      have : (0 : ℝ) ≤ (m1 x : ℝ) ^ (-1 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have := Real.sqrt_nonneg ((m1 x : ℝ) * Real.log (F.nZero x) / (F.mZero α x))
      positivity
    have hMlo : 0 < F.Mlo α x := Real.exp_pos _
    have hfac0 : 0 ≤ x ^ (1 / 2 : ℝ) * (F.q : ℝ) ^ F.nZero x / F.Mlo α x := by
      have : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx.le _
      have : 0 ≤ (F.q : ℝ) ^ F.nZero x := (pow_pos F.q_real_pos _).le
      positivity
    have e1 : epsX F Kc α x * (Cl / Real.sqrt (1 + F.mZero α x)) * x ^ (1 / 2 : ℝ)
        * ((F.nZero x : ℝ) + 1) * Pp * (F.q : ℝ) ^ F.nZero x / F.Mlo α x
        = (epsX F Kc α x * (Cl / Real.sqrt (1 + F.mZero α x)) * Pp) * ((F.nZero x : ℝ) + 1)
          * (x ^ (1 / 2 : ℝ) * (F.q : ℝ) ^ F.nZero x / F.Mlo α x) := by ring
    have e2 : epsX F Kc α x * (Cl / Real.sqrt (1 + F.mZero α x)) * Pp ≤ C4 := by
      rw [hC4]
      exact mul_le_mul_of_nonneg_right (mul_le_mul hε1 hβ1 hβ0 hAε0) hPp0.le
    have hL65 : L * L ^ (-(6 / 5 : ℝ)) = L ^ (-(1 / 5 : ℝ)) := by
      rw [mul_rpow_eq hL0]; norm_num
    rw [e1]
    calc _ ≤ C4 * L * (x ^ (1 / 2 : ℝ) * (F.q : ℝ) ^ F.nZero x / F.Mlo α x) :=
          mul_le_mul_of_nonneg_right (mul_le_mul e2 hn1 (by positivity) hC40) hfac0
      _ ≤ C4 * L * x ^ (-(1 / 5 : ℝ)) := mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ = L * (C4 * x ^ (-(1 / 5 : ℝ))) := by ring
      _ ≤ L * L ^ (-(6 / 5 : ℝ)) := mul_le_mul_of_nonneg_left hx5 hL0.le
      _ = 1 * L ^ (-(1 / 5 : ℝ)) := by rw [hL65, one_mul]
  have hsum : K₁ * L ^ (-(1 / 5 : ℝ)) + 8 * K₁ / c ^ 2 * L ^ (-(1 / 5 : ℝ))
      + C3 * L ^ (-(1 / 5 : ℝ)) + 1 * L ^ (-(1 / 5 : ℝ))
      = (K₁ + 8 * K₁ / c ^ 2 + C3 + 1) * L ^ (-(1 / 5 : ℝ)) := by ring
  linarith

end MasterAux

end ND

end GGMCollatz
