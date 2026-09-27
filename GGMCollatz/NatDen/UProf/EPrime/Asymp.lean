import GGMCollatz.NatDen.UProf.EPrime.Class

/-!
# The condition `Good` holds for large `x` (`α ≤ α₀ = 1 + d/(3 log q)`)

If `α - 1 ≤ d/(3 log q)`, then `m₀ ≤ (α-1)L/(4d) ≤ L/(12 log q)`, where `L = log x`. Hence
`q^{m₀} ≤ x^{1/12}`, `W ≤ 2 exp(m₀ (log q + d) + L^{0.7}) ≤ 2 exp(L/6 + L^{0.7})` (`d < log q`),
`Bmax ≤ 3L/log p`, `Mlo ≥ exp(L - L^{0.7})`. The rest is `L^{0.7} = o(L)` and `L = o(e^{L/6})`.
-/

namespace GGMCollatz

namespace ND

namespace EPrimeAux

open Family

variable (F : Family)

/-- The upper limit of the window exponent, `α₀ = 1 + d/(3 log q)`. -/
noncomputable def alpha0 : ℝ := 1 + F.drift / (3 * Real.log F.q)

theorem one_lt_alpha0 : 1 < alpha0 F := by
  have := F.drift_pos
  have := F.log_q_pos
  unfold alpha0
  have : 0 < F.drift / (3 * Real.log F.q) := by positivity
  linarith

/-- `d < log q` (`μ ≤ 2`, `log p < log q`). -/
theorem drift_lt_log_q : F.drift < Real.log F.q := by
  have h1 := F.mu_le_two
  have h2 := F.log_p_lt_log_q
  have h3 := F.log_p_pos
  unfold Family.drift
  nlinarith

/-- **`Good` eventually holds**. -/
theorem eventually_good {α : ℝ} (hα : 1 < α) (hα₀ : α ≤ alpha0 F) :
    ∀ᶠ x : ℝ in Filter.atTop, Good F α x := by
  have hd := F.drift_pos
  have hlq := F.log_q_pos
  have hlp := F.log_p_pos
  have hdq := drift_lt_log_q F
  have hR := Rb_nonneg F
  have hq1 : (1 : ℝ) ≤ F.q := by exact_mod_cast F.q_pos
  set C₁ : ℝ := 6 * ((F.p : ℝ) - 1) ^ 2 / Real.log F.p with hC₁
  have hC₁0 : 0 ≤ C₁ := div_nonneg (by positivity) hlp.le
  filter_upwards [F.eventually_mZero_ge hα, Filter.eventually_ge_atTop (1 : ℝ),
    eventually_log_ge (3 * Rb F + 1), eventually_log_ge (72 * C₁ + 1), eventually_log_ge 2,
    eventually_mul_log_rpow_le (show (0.7 : ℝ) < 1 by norm_num) 6] with x hm hx1 hL1 hL2 hL3 h07
  rw [Real.rpow_one] at h07
  obtain ⟨-, hm1⟩ := hm
  have hx0 : 0 < x := by linarith
  have hL0 : 0 ≤ Real.log x := by linarith
  -- `m₀ log q ≤ L/12`
  have hmle : (F.mZero α x : ℝ) ≤ (α - 1) * Real.log x / (4 * F.drift) := by
    unfold Family.mZero
    exact Nat.floor_le (div_nonneg (mul_nonneg (by linarith) hL0) (by linarith))
  have hαq : (α - 1) * Real.log F.q ≤ F.drift / 3 := by
    have h := hα₀
    unfold alpha0 at h
    have h' : α - 1 ≤ F.drift / (3 * Real.log F.q) := by linarith
    calc (α - 1) * Real.log F.q ≤ F.drift / (3 * Real.log F.q) * Real.log F.q :=
          mul_le_mul_of_nonneg_right h' hlq.le
      _ = F.drift / 3 := by field_simp
  have hmlq : (F.mZero α x : ℝ) * Real.log F.q ≤ Real.log x / 12 := by
    calc (F.mZero α x : ℝ) * Real.log F.q
        ≤ (α - 1) * Real.log x / (4 * F.drift) * Real.log F.q :=
          mul_le_mul_of_nonneg_right hmle hlq.le
      _ = ((α - 1) * Real.log F.q) * Real.log x / (4 * F.drift) := by ring
      _ ≤ (F.drift / 3) * Real.log x / (4 * F.drift) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hαq hL0) (by linarith)
      _ = Real.log x / 12 := by field_simp; ring
  have hmd : F.drift * (F.mZero α x : ℝ) ≤ Real.log x / 12 := by
    have : F.drift * (F.mZero α x : ℝ) ≤ (F.mZero α x : ℝ) * Real.log F.q := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left hdq.le (Nat.cast_nonneg _)
    linarith
  have hmd0 : 0 ≤ F.drift * (F.mZero α x : ℝ) := mul_nonneg hd.le (Nat.cast_nonneg _)
  set L := Real.log x with hLdef
  set t := L ^ (0.7 : ℝ) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hL0 _
  have hxL : Real.exp L = x := Real.exp_log hx0
  have hqm : Real.exp ((F.mZero α x : ℝ) * Real.log F.q) = (F.q : ℝ) ^ F.mZero α x := by
    rw [Real.exp_nat_mul, Real.exp_log F.q_real_pos]
  have hqmL : (F.q : ℝ) ^ F.mZero α x ≤ Real.exp (L / 12) := by
    rw [← hqm]; exact Real.exp_le_exp.mpr hmlq
  have hR2 : 2 * Rb F ≤ Real.exp (11 * L / 12) := by
    have := Real.add_one_le_exp (11 * L / 12)
    nlinarith
  have hMhi_eq : F.Mhi α x = Real.exp (F.drift * F.mZero α x + L + t) := rfl
  have hMlo_eq : F.Mlo α x = Real.exp (F.drift * F.mZero α x + L - t) := rfl
  have hMhi1 : Real.exp L ≤ F.Mhi α x := by
    rw [hMhi_eq]; apply Real.exp_le_exp.mpr; linarith
  refine ⟨hx1, hm1, ?_, ?_, ?_⟩
  -- (G2) `q^{m₀} R ≤ x/2`
  · have e : Real.exp (L / 12) * Real.exp (11 * L / 12) = x := by
      rw [← Real.exp_add, show L / 12 + 11 * L / 12 = L by ring, hxL]
    calc (F.q : ℝ) ^ F.mZero α x * Rb F ≤ Real.exp (L / 12) * Rb F :=
          mul_le_mul_of_nonneg_right hqmL hR
      _ ≤ Real.exp (L / 12) * (Real.exp (11 * L / 12) / 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = x / 2 := by rw [← e]; ring
  -- (G3) `W (p-1)^2 Bmax ≤ x^{1/2}`
  · have hWb : Wb F α x ≤ 2 * Real.exp (L / 6 + t) := by
      unfold Wb
      rw [div_le_iff₀ hx0]
      have h1 : (F.q : ℝ) ^ (F.mZero α x - 1) ≤ Real.exp ((F.mZero α x : ℝ) * Real.log F.q) := by
        rw [hqm]; exact pow_le_pow_right₀ hq1 (Nat.sub_le _ _)
      have h2 : Real.exp ((F.mZero α x : ℝ) * Real.log F.q) * F.Mhi α x
          ≤ Real.exp (L / 6 + t) * x := by
        rw [hMhi_eq, ← Real.exp_add]
        calc Real.exp ((F.mZero α x : ℝ) * Real.log F.q + (F.drift * F.mZero α x + L + t))
            ≤ Real.exp (L / 6 + t + L) := Real.exp_le_exp.mpr (by linarith)
          _ = Real.exp (L / 6 + t) * x := by rw [Real.exp_add, hxL]
      have hMhi0 : 0 ≤ F.Mhi α x := (Real.exp_pos _).le
      calc 2 * (F.q : ℝ) ^ (F.mZero α x - 1) * F.Mhi α x
          ≤ 2 * Real.exp ((F.mZero α x : ℝ) * Real.log F.q) * F.Mhi α x := by
            apply mul_le_mul_of_nonneg_right _ hMhi0
            linarith
        _ = 2 * (Real.exp ((F.mZero α x : ℝ) * Real.log F.q) * F.Mhi α x) := by ring
        _ ≤ 2 * (Real.exp (L / 6 + t) * x) := by linarith
        _ = 2 * Real.exp (L / 6 + t) * x := by ring
    have hV1 : 1 ≤ (F.q : ℝ) ^ F.mZero α x * (F.Mhi α x + 2 * Rb F) := by
      have h1 : 1 ≤ (F.q : ℝ) ^ F.mZero α x := one_le_pow₀ hq1
      have h2 : 1 ≤ F.Mhi α x := le_trans (Real.one_le_exp hL0) hMhi1
      nlinarith
    have hVle : (F.q : ℝ) ^ F.mZero α x * (F.Mhi α x + 2 * Rb F) ≤ Real.exp (3 * L) := by
      have h2R : 2 * Rb F ≤ F.Mhi α x :=
        le_trans hR2 (le_trans (Real.exp_le_exp.mpr (by linarith)) hMhi1)
      have he1 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith
      calc (F.q : ℝ) ^ F.mZero α x * (F.Mhi α x + 2 * Rb F)
          ≤ Real.exp ((F.mZero α x : ℝ) * Real.log F.q) * (2 * F.Mhi α x) := by
            rw [hqm]
            apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 2 * Real.exp ((F.mZero α x : ℝ) * Real.log F.q
              + (F.drift * F.mZero α x + L + t)) := by
            rw [hMhi_eq, Real.exp_add ((F.mZero α x : ℝ) * Real.log F.q)]; ring
        _ ≤ Real.exp 1 * Real.exp ((F.mZero α x : ℝ) * Real.log F.q
              + (F.drift * F.mZero α x + L + t)) :=
            mul_le_mul_of_nonneg_right he1 (Real.exp_pos _).le
        _ = Real.exp (1 + ((F.mZero α x : ℝ) * Real.log F.q
              + (F.drift * F.mZero α x + L + t))) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (3 * L) := Real.exp_le_exp.mpr (by linarith)
    have hBmax : (Bmax F α x : ℝ) ≤ 3 * L / Real.log F.p := by
      unfold Bmax
      have hlogV : Real.log ((F.q : ℝ) ^ F.mZero α x * (F.Mhi α x + 2 * Rb F)) ≤ 3 * L := by
        have := Real.log_le_log (by linarith) hVle
        rwa [Real.log_exp] at this
      have hnn : 0 ≤ Real.log ((F.q : ℝ) ^ F.mZero α x * (F.Mhi α x + 2 * Rb F)) / Real.log F.p :=
        div_nonneg (Real.log_nonneg hV1) hlp.le
      exact le_trans (Nat.floor_le hnn) (div_le_div_of_nonneg_right hlogV hlp.le)
    have hC1L : C₁ * L ≤ Real.exp (L / 6) := by
      have hq := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ L / 6)
      have hCL : C₁ ≤ L / 72 := by linarith
      have : C₁ * L ≤ (L / 6) ^ 2 / 2 := by
        calc C₁ * L = L * C₁ := mul_comm _ _
          _ ≤ L * (L / 72) := mul_le_mul_of_nonneg_left hCL hL0
          _ = (L / 6) ^ 2 / 2 := by ring
      linarith
    have hp1sq : 0 ≤ ((F.p : ℝ) - 1) ^ 2 := sq_nonneg _
    have hB0 : (0 : ℝ) ≤ Bmax F α x := Nat.cast_nonneg _
    rw [Real.rpow_def_of_pos hx0]
    calc Wb F α x * ((F.p : ℝ) - 1) ^ 2 * (Bmax F α x : ℝ)
        ≤ (2 * Real.exp (L / 6 + t)) * ((F.p : ℝ) - 1) ^ 2 * (3 * L / Real.log F.p) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hWb hp1sq) hBmax hB0 (by positivity)
      _ = (C₁ * L) * Real.exp (L / 6 + t) := by rw [hC₁]; field_simp; ring
      _ ≤ Real.exp (L / 6) * Real.exp (L / 6 + t) :=
          mul_le_mul_of_nonneg_right hC1L (Real.exp_pos _).le
      _ = Real.exp (L / 6 + (L / 6 + t)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (L * (1 / 2)) := Real.exp_le_exp.mpr (by linarith)
  -- (G4) `x^{1/2} x^{1/5} ≤ Mlo`
  · rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hx0, ← Real.exp_add, ← hLdef, hMlo_eq]
    apply Real.exp_le_exp.mpr
    linarith

end EPrimeAux

end ND

end GGMCollatz
