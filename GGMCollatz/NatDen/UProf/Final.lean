import GGMCollatz.NatDen.UProf.Statements
import GGMCollatz.NatDen.UProf.Final.Profile
import GGMCollatz.NatDen.UProf.Final.Window
import GGMCollatz.Tao.Sec6.FromDecay
import GGMCollatz.Tao.Sec7.Decay

/-!
# (UF) Conclusion for the profile on the uniform side

`kernSum(E)/Z = Σ_{M ∈ E'(E)} q^{m₁} ω_{m₁}(M) D(M) / Z`. By (DK), `D(M) = (1/d)(Y/M)(1 + O(L^{-c}))`;
the number of points of the window is `Z = Y/μ (1 + O(y/Y))` (`ℕ_p` has density `1/μ`); by (EP1), `q^{m₁} Σ_{M ∈ E'} ω_{m₁}(M)/M ≪ 1`.
The difference between the profile at scale `m₁`, `q^{m₁} Σ ω_{m₁}(M)/M`, and the profile at `m₀`, `ψ = q^{m₀} Σ ω_{m₀}(M)/M`, is
`max_X C_{m₀}(X) · Osc_{m₁, m₀}(ω_{m₀}) ≪ m₁^{-A}` (GGM Prop. 4.1, (EP1)).

Ingredients of the proof (`NatDen/UProf/Final/`): the number of points of the window `card_logWindow_approx` (`Count.lean`); the profile at scale `m`
`psiAt`, the change of scale `psiAt_scale`, and the substitution of the kernel values `kernSum_sub_le` (`Profile.lean`); the window ratio `window_facts`,
the combination `combine`, and `m₀ ≤ n₀` (`Window.lean`). GGM Prop. 4.1 is used with `A = 1` (`Family.prop41_of_prop51`).
-/

namespace GGMCollatz

namespace ND

open FinalAux

variable (F : Family)

/-- Properties of `m₁ = ⌊L^{0.4}⌋`: if `L ≥ 1` then `1 ≤ m₁ ≤ L^{0.4}` and `m₁^{-1} ≤ 2 L^{-0.4}`. -/
theorem FinalAux.m1_facts {x : ℝ} (hL : 1 ≤ Real.log x) :
    1 ≤ m1 x ∧ (m1 x : ℝ) ≤ Real.log x ^ (0.4 : ℝ) ∧
      ((m1 x : ℕ) : ℝ) ^ (-1 : ℝ) ≤ 2 * Real.log x ^ (-(2 / 5 : ℝ)) := by
  have hLpos : 0 < Real.log x := by linarith
  set t := Real.log x ^ (0.4 : ℝ) with ht
  have ht1 : 1 ≤ t := Real.one_le_rpow hL (by norm_num)
  have hm1 : 1 ≤ m1 x := by
    unfold m1; exact Nat.le_floor (by simpa using ht1)
  have hmle : (m1 x : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hmlt : t < (m1 x : ℝ) + 1 := Nat.lt_floor_add_one t
  have hm1r : (1 : ℝ) ≤ m1 x := by exact_mod_cast hm1
  refine ⟨hm1, hmle, ?_⟩
  have hneg : Real.log x ^ (-(2 / 5 : ℝ)) = t⁻¹ := by
    rw [Real.rpow_neg hLpos.le, ht]; norm_num
  rw [Real.rpow_neg_one, hneg]
  have htpos : 0 < t := by linarith
  have hmpos : (0 : ℝ) < m1 x := by linarith
  rw [inv_le_iff_one_le_mul₀ hmpos]
  rw [show 2 * t⁻¹ * (m1 x : ℝ) = 2 * (m1 x : ℝ) / t by field_simp]
  rw [le_div_iff₀ htpos]
  linarith

/-- **(UF)**. -/
theorem ufinal (hDK : dkern_statement F) (h1 : eprimeC_statement F) : ufinal_statement F := by
  obtain ⟨aD, haD, hD⟩ := hDK
  obtain ⟨aE, haE, hE⟩ := h1
  refine ⟨min (min aD aE) F.thetaMax, lt_min (lt_min haD haE) F.one_lt_thetaMax, ?_⟩
  intro α hα hαa
  have hαD : α ≤ aD := le_trans hαa (le_trans (min_le_left _ _) (min_le_left _ _))
  have hαE : α ≤ aE := le_trans hαa (le_trans (min_le_left _ _) (min_le_right _ _))
  have hαθ : α ≤ F.thetaMax := le_trans hαa (min_le_right _ _)
  obtain ⟨cD, KD, hcD, hKD, evD⟩ := hD α hα hαD
  obtain ⟨KE, hKE, evE⟩ := hE α hα hαE
  obtain ⟨C₄, hC₄, hosc⟩ := (F.prop41_of_prop51 F.prop51) 1 one_pos
  have hμ0 : 0 < F.mu := F.mu_pos
  have hd : 0 < F.drift := F.drift_pos
  have hα1 : 0 < α - 1 := by linarith
  set c : ℝ := min cD (2 / 5) with hc
  have hcpos : 0 < c := lt_min hcD (by norm_num)
  set K : ℝ := 2 * F.mu * KD * KE + 4 * F.mu * KE / F.drift + 2 * (F.mu / F.drift) * KE * C₄
    with hK
  refine ⟨c, K, hcpos, by positivity, ?_⟩
  filter_upwards [evD, evE, F.eventually_mZero_ge hα, Family.eventually_log_ge 1,
    Family.eventually_mul_log_rpow_le (show (0.4 : ℝ) < 1 by norm_num) (8 * F.drift / (α - 1)),
    (tendsto_rpow_atTop hα1).eventually_ge_atTop 4, Filter.eventually_ge_atTop 8,
    Family.eventually_mul_rpow_neg_le_log hα1 c 1] with x hDx hEx hm0 hL h04 hxa hx8 hxc
  have hLpos : 0 < Real.log x := by linarith
  -- the window
  obtain ⟨hZlow, hYZ, hyY⟩ := window_facts F hα hx8 hxa
  set y := x ^ α with hy
  set Y := y ^ α with hY
  set Z := wCard F α x with hZ
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := Real.rpow_pos_of_pos hx0 _
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hy0 _
  have hZpos : 0 < Z := lt_of_lt_of_le (by positivity) hZlow
  refine ⟨hZpos, fun E => ?_⟩
  -- the scales
  obtain ⟨hm1, hm1le, hm1inv⟩ := FinalAux.m1_facts hL
  set m₀ := F.mZero α x with hm₀
  set m₁ := m1 x with hm₁def
  have hm0n0 : m₀ ≤ F.nZero x := mZero_le_nZero F hαθ hLpos.le
  have hm10 : m₁ ≤ m₀ := by
    have h1 : 8 * F.drift / (α - 1) * Real.log x ^ (0.4 : ℝ) ≤ Real.log x := by
      simpa using h04
    have h2 : Real.log x ^ (0.4 : ℝ) ≤ (α - 1) * Real.log x / (8 * F.drift) := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left h1 hα1.le
      rw [show (α - 1) * (8 * F.drift / (α - 1) * Real.log x ^ (0.4 : ℝ))
        = Real.log x ^ (0.4 : ℝ) * (8 * F.drift) by field_simp] at this
      linarith
    have : (m₁ : ℝ) ≤ m₀ := le_trans hm1le (le_trans h2 hm0.1)
    exact_mod_cast this
  have hm1n0 : m₁ ≤ F.nZero x := le_trans hm10 hm0n0
  -- consequences of (EP1)
  have hCE0 : ∀ Y' : ZMod (F.q ^ m₀), F.cE α x E m₀ Y' ≤ KE := fun Y' =>
    le_trans (cE_mono F α x (Set.subset_univ E) m₀ Y') (hEx m₀ hm0n0 Y')
  have hP : psiAt F α x E m₁ ≤ KE :=
    le_trans (psiAt_mono F α x (Set.subset_univ E) m₁)
      (psiAt_le_of_cE_le F α x Set.univ m₁ KE (hEx m₁ hm1n0))
  have hP0 : 0 ≤ psiAt F α x E m₁ := psiAt_nonneg F α x E m₁
  -- the three errors
  have e1 := kernSum_sub_le F α x E KD (Real.log x ^ (-cD)) hDx
  have e3 : |psiAt F α x E m₁ - F.psi α x E| ≤ KE * (C₄ * (m₁ : ℝ) ^ (-(1 : ℝ))) := by
    rw [psi_eq_psiAt, abs_sub_comm]
    refine le_trans (psiAt_scale F α x E hm10 KE hCE0) ?_
    exact mul_le_mul_of_nonneg_left (hosc m₀ m₁ hm10 hm1) hKE.le
  have hcomb := combine hZpos hd hμ0.le e1 hYZ e3 hP0 hP
  -- bound each term by `L^{-c}`
  have hLc1 : Real.log x ^ (-cD) ≤ Real.log x ^ (-c) :=
    Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg (min_le_left _ _))
  have hLc2 : Real.log x ^ (-(2 / 5 : ℝ)) ≤ Real.log x ^ (-c) :=
    Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg (min_le_right _ _))
  have hLc0 : 0 ≤ Real.log x ^ (-c) := Real.rpow_nonneg hLpos.le _
  have hLD0 : 0 ≤ Real.log x ^ (-cD) := Real.rpow_nonneg hLpos.le _
  have hinvZ : 1 / Z ≤ 2 * F.mu / Y := by
    rw [div_le_div_iff₀ hZpos hY0]
    rw [div_le_iff₀ (by positivity)] at hZlow
    linarith
  -- first term
  have t1 : KD * Y * Real.log x ^ (-cD) * psiAt F α x E m₁ / Z
      ≤ 2 * F.mu * KD * KE * Real.log x ^ (-c) := by
    have hA : KD * Y * Real.log x ^ (-cD) * psiAt F α x E m₁
        ≤ KD * Y * Real.log x ^ (-c) * KE := by
      have h0 : 0 ≤ KD * Y := by positivity
      calc KD * Y * Real.log x ^ (-cD) * psiAt F α x E m₁
          ≤ KD * Y * Real.log x ^ (-c) * psiAt F α x E m₁ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLc1 h0) hP0
        _ ≤ KD * Y * Real.log x ^ (-c) * KE :=
            mul_le_mul_of_nonneg_left hP (by positivity)
    calc KD * Y * Real.log x ^ (-cD) * psiAt F α x E m₁ / Z
        ≤ KD * Y * Real.log x ^ (-c) * KE / Z := div_le_div_of_nonneg_right hA hZpos.le
      _ = KD * Y * Real.log x ^ (-c) * KE * (1 / Z) := by ring
      _ ≤ KD * Y * Real.log x ^ (-c) * KE * (2 * F.mu / Y) :=
          mul_le_mul_of_nonneg_left hinvZ (by positivity)
      _ = 2 * F.mu * KD * KE * Real.log x ^ (-c) := by field_simp
  -- second term
  have t2 : 2 * y * KE / (F.drift * Z) ≤ 4 * F.mu * KE / F.drift * Real.log x ^ (-c) := by
    have hyY' : y / Y ≤ Real.log x ^ (-c) := by
      have := hxc; rw [one_mul] at this; exact le_trans hyY this
    calc 2 * y * KE / (F.drift * Z) = 2 * y * KE / F.drift * (1 / Z) := by
          field_simp
      _ ≤ 2 * y * KE / F.drift * (2 * F.mu / Y) :=
          mul_le_mul_of_nonneg_left hinvZ (by positivity)
      _ = 4 * F.mu * KE / F.drift * (y / Y) := by ring
      _ ≤ 4 * F.mu * KE / F.drift * Real.log x ^ (-c) :=
          mul_le_mul_of_nonneg_left hyY' (by positivity)
  -- third term
  have t3 : F.mu / F.drift * (KE * (C₄ * (m₁ : ℝ) ^ (-(1 : ℝ))))
      ≤ 2 * (F.mu / F.drift) * KE * C₄ * Real.log x ^ (-c) := by
    have h := le_trans hm1inv (mul_le_mul_of_nonneg_left hLc2 (by norm_num : (0 : ℝ) ≤ 2))
    calc F.mu / F.drift * (KE * (C₄ * (m₁ : ℝ) ^ (-(1 : ℝ))))
        = F.mu / F.drift * KE * C₄ * (m₁ : ℝ) ^ (-(1 : ℝ)) := by ring
      _ ≤ F.mu / F.drift * KE * C₄ * (2 * Real.log x ^ (-c)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring
  calc _ ≤ KD * Y * Real.log x ^ (-cD) * psiAt F α x E m₁ / Z
        + 2 * y * KE / (F.drift * Z) + F.mu / F.drift * (KE * (C₄ * (m₁ : ℝ) ^ (-(1 : ℝ)))) :=
        hcomb
    _ ≤ 2 * F.mu * KD * KE * Real.log x ^ (-c) + 4 * F.mu * KE / F.drift * Real.log x ^ (-c)
        + 2 * (F.mu / F.drift) * KE * C₄ * Real.log x ^ (-c) := by linarith
    _ = K * Real.log x ^ (-c) := by rw [hK]; ring

end ND

end GGMCollatz
