import GGMCollatz.Tao.Sec7.HLDefs
import GGMCollatz.Tao.Prob.Mgf

/-!
# Basic quantities of `ℋ`: success probability, atoms, exponential moments (counterpart of the `Hold` part of `Prob/Mgf.lean` of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, files `TaoCollatz/Prob/Mgf.lean` (`tiltZ_hold_factor`,
`tiltZ_hold_le`, `tiltZ_hold_ne_zero`) and `TaoCollatz/Sec7/Holding.lean` (atom masses);
generalized to the GGM family (p, q, r). Modified: the concrete numerical values of tao-collatz (`1/4`, the box `1/50`, `221/25`) were replaced by
the existence of constants depending on `p` (continuity).

* `sR = P(Pascal = 3) = 2(p-1)²/p³` (the success probability of `𝒥`, as a real).
* `hold_atoms_pos`: the four nondegenerate atoms `(1,3), (2,5), (2,7), (2,8)` have positive mass.
* `tiltZ_hold_factor`: `Z_ℋ(λ₁, λ₂) = Σ_k P(𝒥 = k) e^{λ₁k + 3λ₂} Z_{≠3}(λ₂)^{k-1}`.
* `hold_expMoment`: `Z_ℋ(β, β) < ∞` for some `β > 0` (`e^β (Z_P(β) - s e^{3β}) → 1 - s < 1`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

namespace HL

variable (F : Family)

/-! ### The success probability `s` -/

/-- `s = P(Pascal = 3)` (as a real). -/
noncomputable def sR : ℝ := (pascalP F.p 3).toReal

theorem sR_eq : sR F = 2 * ((F.p : ℝ) - 1) ^ 2 / (F.p : ℝ) ^ 3 := by
  have hp := F.two_le_p
  unfold sR
  rw [pascalP_three hp, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    Nat.cast_sub (by omega : 1 ≤ F.p)]
  norm_num
  ring

theorem p_real_ge_two : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p

theorem sR_pos : 0 < sR F := by
  rw [sR_eq]
  have := p_real_ge_two F
  apply div_pos
  · nlinarith
  · positivity

theorem sR_lt_one : sR F < 1 := by
  rw [sR_eq, div_lt_one (by have := p_real_ge_two F; positivity)]
  have := p_real_ge_two F
  nlinarith

theorem pascal3_ne_top : pascalP F.p 3 ≠ ⊤ := PMF.apply_ne_top _ _

theorem ofReal_sR : ENNReal.ofReal (sR F) = pascalP F.p 3 := by
  unfold sR
  exact ENNReal.ofReal_toReal (pascal3_ne_top F)

theorem one_sub_pascal3_eq : (1 : ℝ≥0∞) - pascalP F.p 3 = ENNReal.ofReal (1 - sR F) := by
  rw [← ofReal_sR F, ← ENNReal.ofReal_one, ENNReal.ofReal_sub _ (sR_pos F).le]

theorem one_sub_pascal3_ne_zero : (1 : ℝ≥0∞) - pascalP F.p 3 ≠ 0 := by
  rw [one_sub_pascal3_eq]
  exact (ENNReal.ofReal_pos.mpr (by linarith [sR_lt_one F])).ne'

theorem one_sub_pascal3_ne_top : (1 : ℝ≥0∞) - pascalP F.p 3 ≠ ⊤ := by
  rw [one_sub_pascal3_eq]; exact ENNReal.ofReal_ne_top

/-- `P(𝒥 = k) = s(1-s)^{k-1}` (`k ≥ 1`). -/
theorem holdGeom_succ (k : ℕ) :
    holdGeom F.p (k + 1) = pascalP F.p 3 * (1 - pascalP F.p 3) ^ k := by
  unfold holdGeom
  rw [geomS_apply (holdGeom_prob F.two_le_p), if_neg (by omega), Nat.add_sub_cancel]

/-! ### Nondegenerate atoms -/

theorem hold_one_three : F.hold (1, 3) = pascalP F.p 3 := by
  rw [F.hold_apply_pin, holdGeom_succ F 0, pow_zero, mul_one]
  have h0 : (pascalNe3P F.p).iid (1 - 1) = PMF.pure (fun i : Fin 0 => i.elim0) := rfl
  rw [h0, PMF.pure_map]
  have hval : ((3 : ℤ) + ∑ i : Fin 0, ((((fun i : Fin 0 => i.elim0) i : ℕ)) : ℤ)) = 3 := by
    simp
  rw [hval, PMF.pure_apply, if_pos rfl, mul_one]

/-- `ℋ(2, 3+b) ≥ P(𝒥 = 2) P_{≠3}(b)`. -/
theorem hold_two_ge (b : ℕ) :
    holdGeom F.p 2 * pascalNe3P F.p b ≤ F.hold (2, 3 + (b : ℤ)) := by
  rw [F.hold_apply_pin]
  refine mul_le_mul_right ?_ _
  have h := PMF.apply_le_map_apply ((pascalNe3P F.p).iid (2 - 1))
    (fun v => ((3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ))) (fun _ => b)
  have hv : ((3 : ℤ) + ∑ i : Fin (2 - 1), ((((fun _ => b) : Fin (2 - 1) → ℕ) i : ℕ) : ℤ))
      = 3 + (b : ℤ) := by simp
  rw [hv] at h
  refine le_trans ?_ h
  rw [PMF.iid_apply_eq_prod]
  simp

theorem pascalNe3P_pos {b : ℕ} (hb2 : 2 ≤ b) (hb3 : b ≠ 3) : 0 < pascalNe3P F.p b := by
  have hp := F.two_le_p
  rw [pascalNe3P_apply hp, if_neg hb3]
  apply ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr (one_sub_pascal3_ne_top F))
  rw [pascalP_apply hp, if_neg (by omega)]
  exact (ENNReal.mul_pos (mul_ne_zero (by exact_mod_cast (by omega : b - 1 ≠ 0))
    (pow_ne_zero _ (natCast_sub_one_ne_zero hp)))
    (pow_ne_zero _ (natCast_inv_ne_zero F.p))).ne'

theorem holdGeom_two_pos : 0 < holdGeom F.p 2 := by
  rw [holdGeom_succ F 1, pow_one]
  exact ENNReal.mul_pos (pascalP_three_pos F.two_le_p).ne' (one_sub_pascal3_ne_zero F)

theorem hold_two_pos {b : ℕ} (hb2 : 2 ≤ b) (hb3 : b ≠ 3) : 0 < F.hold (2, 3 + (b : ℤ)) :=
  lt_of_lt_of_le (ENNReal.mul_pos (holdGeom_two_pos F).ne' (pascalNe3P_pos F hb2 hb3).ne')
    (hold_two_ge F b)

/-- The four atoms have positive mass (as reals). -/
theorem hold_atoms_pos :
    0 < (F.hold (1, 3)).toReal ∧ 0 < (F.hold (2, 5)).toReal ∧
      0 < (F.hold (2, 7)).toReal ∧ 0 < (F.hold (2, 8)).toReal := by
  have hne : ∀ y, 0 < F.hold y → 0 < (F.hold y).toReal := fun y h =>
    ENNReal.toReal_pos h.ne' (PMF.apply_ne_top _ _)
  refine ⟨hne _ ?_, ?_, ?_, ?_⟩
  · rw [hold_one_three]; exact pascalP_three_pos F.two_le_p
  · have := hold_two_pos F (b := 2) (by norm_num) (by norm_num)
    exact hne _ (by simpa using this)
  · have := hold_two_pos F (b := 4) (by norm_num) (by norm_num)
    exact hne _ (by simpa using this)
  · have := hold_two_pos F (b := 5) (by norm_num) (by norm_num)
    exact hne _ (by simpa using this)

/-! ### Factorization of the moment generating function and exponential moments -/

theorem tiltZ_ne3_ne_zero (l2 : ℝ) : tiltZ (pascalNe3P F.p) (expW l2) ≠ 0 :=
  tiltZ_expW_ne_zero _ l2

/-- **Factorization of the moment generating function of `ℋ`** (`tiltZ_hold_factor` of tao-collatz). -/
theorem tiltZ_hold_factor (l1 l2 : ℝ)
    (hZt : tiltZ (pascalNe3P F.p) (expW l2) ≠ ∞) :
    tiltZ F.hold (expW2 l1 l2)
      = ∑' k : ℕ, holdGeom F.p k
          * (ENNReal.ofReal (Real.exp (l1 * k + 3 * l2))
            * (tiltZ (pascalNe3P F.p) (expW l2)) ^ (k - 1)) := by
  rw [tiltZ]
  unfold hold
  rw [PMF.tsum_bind_mul]
  refine tsum_congr fun k => ?_
  congr 1
  rw [PMF.tsum_map_mul]
  have hterm : ∀ v : Fin (k - 1) → ℕ,
      ((pascalNe3P F.p).iid (k - 1)) v
          * expW2 l1 l2 ((k : ℕ), ((3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ)))
        = ENNReal.ofReal (Real.exp (l1 * k + 3 * l2))
          * (((pascalNe3P F.p).iid (k - 1)) v * expW l2 (∑ i, v i)) := by
    intro v
    simp only [expW2, expW]
    rw [show l1 * (((k : ℕ), ((3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ))).1 : ℕ)
          + l2 * ((((k : ℕ), ((3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ))).2 : ℤ) : ℝ)
        = (l1 * k + 3 * l2) + l2 * ((∑ i, v i : ℕ) : ℝ) from by
      push_cast
      ring]
    rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring
  rw [tsum_congr hterm, ENNReal.tsum_mul_left]
  congr 1
  have hiid : ∑' v, ((pascalNe3P F.p).iid (k - 1)) v * expW l2 (∑ i, v i)
      = tiltZ (iidSum (pascalNe3P F.p) (k - 1)) (expW l2) := by
    rw [tiltZ, iidSum, PMF.tsum_map_mul]
  rw [hiid, tiltZ_iidSum (pascalNe3P F.p) (expW_zero l2) (expW_add l2)
    (tiltZ_ne3_ne_zero F l2) hZt]

/-- `(1-s) Z_{≠3}(λ) + s e^{3λ} = Z_P(λ)`. -/
theorem tiltZ_ne3_decomp (l2 : ℝ) :
    (1 - pascalP F.p 3) * tiltZ (pascalNe3P F.p) (expW l2) + pascalP F.p 3 * expW l2 3
      = tiltZ (pascalP F.p) (expW l2) := by
  have hp := F.two_le_p
  rw [tiltZ, tiltZ, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_eq_add_tsum_ite (f := fun b => pascalP F.p b * expW l2 b) 3, add_comm]
  congr 1
  refine tsum_congr fun b => ?_
  rw [pascalNe3P_apply hp]
  by_cases hb : b = 3
  · simp [hb]
  · rw [if_neg hb, if_neg hb, ← mul_assoc, ← mul_assoc,
      ENNReal.mul_inv_cancel (one_sub_pascal3_ne_zero F) (one_sub_pascal3_ne_top F), one_mul]

/-- The real ratio `ρ(β) = e^β (G(β)² - s e^{3β})`, `G(β) = (p-1)e^β/(p - e^β)`. -/
noncomputable def ratioR (β : ℝ) : ℝ :=
  Real.exp β * ((((F.p : ℝ) - 1) * Real.exp β / ((F.p : ℝ) - Real.exp β)) ^ 2
    - sR F * Real.exp (3 * β))

theorem ratioR_zero : ratioR F 0 = 1 - sR F := by
  have := p_real_ge_two F
  have h1 : (F.p : ℝ) - 1 ≠ 0 := by linarith
  unfold ratioR
  simp only [Real.exp_zero, mul_zero, mul_one, one_mul]
  rw [div_self h1]
  ring

theorem ratioR_tendsto : Filter.Tendsto (ratioR F) (nhds 0) (nhds (1 - sR F)) := by
  rw [← ratioR_zero F]
  have hp := p_real_ge_two F
  have hden : (F.p : ℝ) - Real.exp 0 ≠ 0 := by rw [Real.exp_zero]; linarith
  have hc : ContinuousAt (ratioR F) 0 := by
    unfold ratioR
    have h1 : ContinuousAt (fun β : ℝ => Real.exp β) 0 := Real.continuous_exp.continuousAt
    have h3 : ContinuousAt (fun β : ℝ => Real.exp (3 * β)) 0 :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt
    have hq : ContinuousAt (fun β : ℝ => ((F.p : ℝ) - 1) * Real.exp β / ((F.p : ℝ) - Real.exp β))
        0 := ContinuousAt.div (continuousAt_const.mul h1) (continuousAt_const.sub h1) hden
    exact h1.mul ((hq.pow 2).sub (continuousAt_const.mul h3))
  exact hc.tendsto

/-- For some `β ∈ (0, 1/2]`, the ratio satisfies `ρ(β) ≤ 1 - s/2`. -/
theorem exists_beta : ∃ β : ℝ, 0 < β ∧ β ≤ 1 / 2 ∧ ratioR F β ≤ 1 - sR F / 2 := by
  have hs := sR_pos F
  have hev := (ratioR_tendsto F).eventually (gt_mem_nhds (show 1 - sR F < 1 - sR F / 2 by
    linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min (δ / 2) (1 / 2), lt_min (by linarith) (by norm_num), min_le_right _ _, ?_⟩
  refine (hball ?_).le
  rw [Real.dist_eq, sub_zero, abs_of_pos (lt_min (by linarith) (by norm_num))]
  exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

theorem exp_lt_p {β : ℝ} (hβ : β ≤ 1 / 2) : Real.exp β < F.p := by
  have hp := p_real_ge_two F
  calc Real.exp β ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hβ
    _ < 2 := by
        have := Real.exp_one_lt_d9
        have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; norm_num
        nlinarith [Real.exp_pos (1 / 2)]
    _ ≤ F.p := hp

/-- Closed form of `G(β)`: `Z_G(β) = ofReal((p-1)e^β/(p - e^β))` (`e^β < p`). -/
theorem tiltZ_geom_eq {β : ℝ} (hβ : Real.exp β < F.p) :
    tiltZ (geomP F.p) (expW β)
      = ENNReal.ofReal (((F.p : ℝ) - 1) * Real.exp β / ((F.p : ℝ) - Real.exp β)) := by
  have hp := p_real_ge_two F
  have hp0 : (0 : ℝ) < F.p := by linarith
  rw [tiltZ_geomP_frac F.two_le_p]
  have hr : Real.exp β / F.p < 1 := (div_lt_one hp0).mpr hβ
  have hr0 : 0 ≤ Real.exp β / F.p := by positivity
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hr0,
    ← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_mul (by
      exact div_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) hp0.le)]
  congr 1
  field_simp

/-- The ratio `(1-s) e^β Z_{≠3}(β) = ofReal(ρ(β))` (`e^β < p`). -/
theorem ratio_eq {β : ℝ} (hβ : Real.exp β < F.p) :
    ENNReal.ofReal (Real.exp β) * ((1 - pascalP F.p 3) * tiltZ (pascalNe3P F.p) (expW β))
      = ENNReal.ofReal (ratioR F β) := by
  have hp := p_real_ge_two F
  have hdec := tiltZ_ne3_decomp F β
  rw [tiltZ_pascalP F.two_le_p hβ, tiltZ_geom_eq F hβ,
    ← ENNReal.ofReal_pow (by
      have := Real.exp_pos β
      apply div_nonneg <;> nlinarith)] at hdec
  have h3 : pascalP F.p 3 * expW β 3 = ENNReal.ofReal (sR F * Real.exp (3 * β)) := by
    rw [← ofReal_sR F, expW, ← ENNReal.ofReal_mul (sR_pos F).le,
      show β * ((3 : ℕ) : ℝ) = 3 * β by push_cast; ring]
  rw [h3] at hdec
  have hfin : ENNReal.ofReal (sR F * Real.exp (3 * β)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsub : (1 - pascalP F.p 3) * tiltZ (pascalNe3P F.p) (expW β)
      = ENNReal.ofReal ((((F.p : ℝ) - 1) * Real.exp β / ((F.p : ℝ) - Real.exp β)) ^ 2)
        - ENNReal.ofReal (sR F * Real.exp (3 * β)) :=
    ENNReal.eq_sub_of_add_eq hfin hdec
  rw [hsub, ← ENNReal.ofReal_sub _ (by have := sR_pos F; positivity),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  rfl

/-- **Exponential moment**: `Z_ℋ(β, β) < ∞` for some `β ∈ (0, 1/2]`. -/
theorem hold_expMoment : ∃ β : ℝ, 0 < β ∧ β ≤ 1 / 2 ∧ tiltZ F.hold (expW2 β β) ≠ ⊤ := by
  obtain ⟨β, hβ0, hβ1, hρ⟩ := exists_beta F
  refine ⟨β, hβ0, hβ1, ?_⟩
  have hexp := exp_lt_p F hβ1
  have hs := sR_pos F
  set Zn := tiltZ (pascalNe3P F.p) (expW β) with hZn
  set R := ENNReal.ofReal (ratioR F β) with hR
  have hR1 : R < 1 := by
    rw [hR, ENNReal.ofReal_lt_one]; linarith
  have hratio := ratio_eq F hexp
  -- `Z_{≠3}(β) < ∞`, since the ratio is finite
  have hZnt : Zn ≠ ⊤ := by
    intro htop
    rw [← hZn, htop, ENNReal.mul_top (one_sub_pascal3_ne_zero F),
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.exp_pos β)).ne'] at hratio
    exact ENNReal.ofReal_ne_top hratio.symm
  rw [tiltZ_hold_factor F β β hZnt]
  have hbound : ∀ k : ℕ, holdGeom F.p k
        * (ENNReal.ofReal (Real.exp (β * k + 3 * β)) * Zn ^ (k - 1))
      ≤ ENNReal.ofReal (Real.exp (4 * β)) * R ^ (k - 1) := by
    intro k
    rcases k with _ | k
    · have h0 : holdGeom F.p 0 = 0 := F.holdGeom_zero
      rw [h0, zero_mul]; exact zero_le
    · rw [holdGeom_succ, Nat.add_sub_cancel]
      have hsplit : ENNReal.ofReal (Real.exp (β * (k + 1 : ℕ) + 3 * β))
          = ENNReal.ofReal (Real.exp (4 * β)) * ENNReal.ofReal (Real.exp β) ^ k := by
        rw [← ENNReal.ofReal_pow (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 2
        push_cast
        ring
      rw [hsplit, hR, ← hratio]
      have hs1 : pascalP F.p 3 ≤ 1 := PMF.coe_le_one _ _
      calc pascalP F.p 3 * (1 - pascalP F.p 3) ^ k
            * (ENNReal.ofReal (Real.exp (4 * β)) * ENNReal.ofReal (Real.exp β) ^ k * Zn ^ k)
          = pascalP F.p 3 * (ENNReal.ofReal (Real.exp (4 * β))
            * (ENNReal.ofReal (Real.exp β) * ((1 - pascalP F.p 3) * Zn)) ^ k) := by
            rw [mul_pow, mul_pow]; ring
        _ ≤ 1 * (ENNReal.ofReal (Real.exp (4 * β))
            * (ENNReal.ofReal (Real.exp β) * ((1 - pascalP F.p 3) * Zn)) ^ k) := by
            gcongr
        _ = _ := one_mul _
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
  rw [ENNReal.tsum_mul_left, tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.zero_sub, pow_zero, Nat.add_sub_cancel]
  rw [ENNReal.tsum_geometric]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨by simp, ?_⟩)
  exact ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hR1).ne'

end HL

end Family

end GGMCollatz
