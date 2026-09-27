import GGMCollatz.NatDen.UProf.Statements

/-!
# Auxiliary for (UF): the profile `Ψ_m(E)` at scale `m` and the kernel-weighted sum (including the comparison with GGM's `Q'`)

`psiAt β x E m = q^m Σ_{M ∈ E'(E)} ω_m(M)/M` (`ω_m` = the law of `𝒮_m`). `ψ = psiAt (m₀)` (by definition);
the profile on the uniform side is `Ψ₁ = psiAt (m₁)`.

* `psiAt_eq_sum_cE`: `Ψ_k(E) = Σ_{Y mod q^k} ω_k(Y) C^E_k(Y)`.
* `psiAt_scale`: if `m ≤ k` and `C^E_k ≤ B` then `|Ψ_k(E) - Ψ_m(E)| ≤ B · Osc_{m,k}(ω_k)`
  (the coarse scale of `expect_syracZ_cE` in `Tao/Sec5/ApproxFormula.lean` made an arbitrary `m`).
* `kernSum_sub_le`: from a pointwise bound of the form (DK), `|kernSum(E) - (Y/d) Ψ_{m₁}(E)| ≤ K Y ε Ψ_{m₁}(E)`.
-/

namespace GGMCollatz

namespace ND

namespace FinalAux

variable (F : Family)

/-- The profile at scale `m`: `Ψ_m(E) = q^m Σ_{M ∈ E'(E)} P(𝒮_m = M mod q^m)/M`. -/
noncomputable def psiAt (β x : ℝ) (E : Set ℕ) (m : ℕ) : ℝ :=
  (F.q : ℝ) ^ m * ∑ M ∈ F.Eprime β x E,
    ((F.syracZ m) (M : ZMod (F.q ^ m))).toReal * (M : ℝ)⁻¹

/-- `ψ = Ψ_{m₀}` (by definition). -/
theorem psi_eq_psiAt (β x : ℝ) (E : Set ℕ) : F.psi β x E = psiAt F β x E (F.mZero β x) := rfl

theorem psiAt_nonneg (β x : ℝ) (E : Set ℕ) (m : ℕ) : 0 ≤ psiAt F β x E m := by
  unfold psiAt
  exact mul_nonneg (by have := F.q_real_pos; positivity) (Finset.sum_nonneg fun M _ =>
    mul_nonneg ENNReal.toReal_nonneg (by positivity))

theorem psiAt_mono (β x : ℝ) {E E' : Set ℕ} (h : E ⊆ E') (m : ℕ) :
    psiAt F β x E m ≤ psiAt F β x E' m := by
  unfold psiAt
  refine mul_le_mul_of_nonneg_left ?_ (by have := F.q_real_pos; positivity)
  exact Finset.sum_le_sum_of_subset_of_nonneg (F.Eprime_mono β x h) (fun M _ _ =>
    mul_nonneg ENNReal.toReal_nonneg (by positivity))

/-- `C^E_k` is monotone in `E`. -/
theorem cE_mono (β x : ℝ) {E E' : Set ℕ} (h : E ⊆ E') (k : ℕ) (Y : ZMod (F.q ^ k)) :
    F.cE β x E k Y ≤ F.cE β x E' k Y := by
  classical
  unfold Family.cE
  refine mul_le_mul_of_nonneg_left ?_ (by have := F.q_real_pos; positivity)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun M _ _ => by positivity)
  intro M hM
  rw [Finset.mem_filter] at hM ⊢
  exact ⟨F.Eprime_mono β x h hM.1, hM.2⟩

/-- `Ψ_k(E) = Σ_{Y mod q^k} ω_k(Y) C^E_k(Y)`. -/
theorem psiAt_eq_sum_cE (β x : ℝ) (E : Set ℕ) (k : ℕ) :
    psiAt F β x E k = ∑ Y : ZMod (F.q ^ k), ((F.syracZ k) Y).toReal * F.cE β x E k Y := by
  classical
  unfold psiAt Family.cE
  rw [Finset.mul_sum]
  rw [← Finset.sum_fiberwise (F.Eprime β x E) (fun M : ℕ => ((M : ℕ) : ZMod (F.q ^ k)))]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun M hM => ?_)
  have hMY : ((M : ℕ) : ZMod (F.q ^ k)) = Y := (Finset.mem_filter.mp hM).2
  rw [hMY]
  ring

/-- If `C^E_k ≤ B` then `Ψ_k(E) ≤ B` (`Σ ω_k = 1`). -/
theorem psiAt_le_of_cE_le (β x : ℝ) (E : Set ℕ) (k : ℕ) (B : ℝ)
    (hB : ∀ Y, F.cE β x E k Y ≤ B) : psiAt F β x E k ≤ B := by
  rw [psiAt_eq_sum_cE]
  calc ∑ Y : ZMod (F.q ^ k), ((F.syracZ k) Y).toReal * F.cE β x E k Y
      ≤ ∑ Y : ZMod (F.q ^ k), ((F.syracZ k) Y).toReal * B :=
        Finset.sum_le_sum (fun Y _ => mul_le_mul_of_nonneg_left (hB Y) ENNReal.toReal_nonneg)
    _ = B := by rw [← Finset.sum_mul, F.sum_syracZ_toReal_eq_one, one_mul]

/-- **Change of scale**: if `m ≤ k` and `C^E_k ≤ B` then `|Ψ_k(E) - Ψ_m(E)| ≤ B · Osc_{m,k}(ω_k)`. -/
theorem psiAt_scale (β x : ℝ) (E : Set ℕ) {m k : ℕ} (hmk : m ≤ k) (B : ℝ)
    (hB : ∀ Y, F.cE β x E k Y ≤ B) :
    |psiAt F β x E k - psiAt F β x E m|
      ≤ B * F.osc m k hmk (fun Y => ((F.syracZ k) Y).toReal) := by
  classical
  set φ := ZMod.castHom (pow_dvd_pow F.q hmk) (ZMod (F.q ^ m)) with hφ
  -- the sum over a fibre is the law at the coarse scale
  have hfib : ∀ Y : ZMod (F.q ^ k),
      (∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (F.q ^ k) => φ Y' = φ Y), ((F.syracZ k) Y').toReal)
        = ((F.syracZ m) (φ Y)).toReal := by
    intro Y
    rw [← ENNReal.toReal_sum (fun Y' _ => PMF.apply_ne_top _ _)]
    congr 1
    rw [← F.syracZ_map_cast hmk, PMF.map_apply, tsum_fintype, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases hc : φ a = φ Y
    · rw [if_pos hc, if_pos hc.symm]
    · rw [if_neg hc, if_neg (fun h => hc h.symm)]
  have hosc : F.osc m k hmk (fun Y => ((F.syracZ k) Y).toReal)
      = ∑ Y : ZMod (F.q ^ k), |((F.syracZ k) Y).toReal
          - (F.q : ℝ) ^ ((m : ℤ) - (k : ℤ)) * ((F.syracZ m) (φ Y)).toReal| := by
    unfold Family.osc
    refine Finset.sum_congr rfl (fun Y _ => ?_)
    rw [← hfib Y]
  -- rewrite `Ψ_m` in terms of the fine classes
  have hq0 : (F.q : ℝ) ≠ 0 := F.q_real_pos.ne'
  have hpow : (F.q : ℝ) ^ m = (F.q : ℝ) ^ ((m : ℤ) - (k : ℤ)) * (F.q : ℝ) ^ k := by
    rw [← zpow_natCast (F.q : ℝ) k, ← zpow_add₀ hq0, ← zpow_natCast (F.q : ℝ) m]
    congr 1; ring
  have hpsi : psiAt F β x E m = ∑ Y : ZMod (F.q ^ k),
      (F.q : ℝ) ^ ((m : ℤ) - (k : ℤ)) * ((F.syracZ m) (φ Y)).toReal * F.cE β x E k Y := by
    unfold psiAt Family.cE
    rw [Finset.mul_sum]
    rw [← Finset.sum_fiberwise (F.Eprime β x E) (fun M : ℕ => ((M : ℕ) : ZMod (F.q ^ k)))]
    refine Finset.sum_congr rfl (fun Y _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun M hM => ?_)
    have hMY : ((M : ℕ) : ZMod (F.q ^ k)) = Y := (Finset.mem_filter.mp hM).2
    have hcast : ((M : ℕ) : ZMod (F.q ^ m)) = φ Y := by
      rw [← hMY, map_natCast]
    rw [hcast, hpow]
    ring
  rw [psiAt_eq_sum_cE F β x E k, hpsi, hosc, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun Y _ => ?_))
  rw [show ((F.syracZ k) Y).toReal * F.cE β x E k Y
      - (F.q : ℝ) ^ ((m : ℤ) - (k : ℤ)) * ((F.syracZ m) (φ Y)).toReal * F.cE β x E k Y
      = (((F.syracZ k) Y).toReal
          - (F.q : ℝ) ^ ((m : ℤ) - (k : ℤ)) * ((F.syracZ m) (φ Y)).toReal) * F.cE β x E k Y
      by ring, abs_mul, abs_of_nonneg (F.cE_nonneg β x E k Y), mul_comm B]
  exact mul_le_mul_of_nonneg_left (hB Y) (abs_nonneg _)

/-- The elements of `E'(E)` lie in `[Mlo, Mhi]`. -/
theorem mem_Eprime_bounds {β x : ℝ} {E : Set ℕ} {M : ℕ} (hM : M ∈ F.Eprime β x E) :
    F.Mlo β x ≤ (M : ℝ) ∧ (M : ℝ) ≤ F.Mhi β x := by
  unfold Family.Eprime at hM
  simp only [Finset.mem_filter, Finset.mem_range] at hM
  refine ⟨hM.2.2.1, ?_⟩
  have hMhi : 0 < F.Mhi β x := Real.exp_pos _
  have : M ≤ ⌊F.Mhi β x⌋₊ := by omega
  exact le_trans (by exact_mod_cast this) (Nat.floor_le hMhi.le)

/-- **Substituting the kernel values** (step (1) of the conclusion of the uniform side): if `|D(M) - Y/(dM)| ≤ K (Y/M) ε` on `[Mlo, Mhi]`, then
`|kernSum(E) - (Y/d) Ψ_{m₁}(E)| ≤ K Y ε Ψ_{m₁}(E)` (`Y = (x^α)^α`). -/
theorem kernSum_sub_le (α x : ℝ) (E : Set ℕ) (K ε : ℝ)
    (hK : ∀ M : ℝ, F.Mlo α x ≤ M → M ≤ F.Mhi α x →
      |kern F α x M - (x ^ α) ^ α / (F.drift * M)| ≤ K * ((x ^ α) ^ α / M) * ε) :
    |kernSum F α x E - (x ^ α) ^ α / F.drift * psiAt F α x E (m1 x)|
      ≤ K * (x ^ α) ^ α * ε * psiAt F α x E (m1 x) := by
  classical
  set Y := (x ^ α) ^ α with hY
  set m := m1 x with hm
  have hsplit : kernSum F α x E - Y / F.drift * psiAt F α x E m
      = ∑ M ∈ F.Eprime α x E, (F.q : ℝ) ^ m * ((F.syracZ m) (M : ZMod (F.q ^ m))).toReal *
          (kern F α x M - Y / (F.drift * M)) := by
    unfold kernSum psiAt
    rw [← hm, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun M _ => ?_)
    ring
  have hrhs : K * Y * ε * psiAt F α x E m
      = ∑ M ∈ F.Eprime α x E, (F.q : ℝ) ^ m * ((F.syracZ m) (M : ZMod (F.q ^ m))).toReal *
          (K * (Y / M) * ε) := by
    unfold psiAt
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun M _ => ?_)
    ring
  rw [hsplit, hrhs]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun M hM => ?_))
  have hw : 0 ≤ (F.q : ℝ) ^ m * ((F.syracZ m) (M : ZMod (F.q ^ m))).toReal :=
    mul_nonneg (by have := F.q_real_pos; positivity) ENNReal.toReal_nonneg
  obtain ⟨h1, h2⟩ := mem_Eprime_bounds F hM
  rw [abs_mul, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_left (hK M h1 h2) hw

end FinalAux

end ND

end GGMCollatz
