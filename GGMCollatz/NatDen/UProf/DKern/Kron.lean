import GGMCollatz.NatDen.UProf.DKern.Env

/-!
# Piece (e) of (DK): weighted equidistribution of the Kronecker orbit

`f(θ) = p^{-θ} = exp(-θ log p)` is decreasing on `[0,1]` with values in `[1/p, 1]`, and
`∫₀¹ f = (1 - 1/p)/log p = 1/(μ log p)`. We apply (KRON-W) (`kronW_statement`) to this `f`.
-/

namespace GGMCollatz

namespace ND

namespace DKernAux

/-- `∫₀¹ exp(-θ log P) dθ = (1 - 1/P)/log P`. -/
theorem integral_exp_neg_mul_log {P : ℝ} (hP : 1 < P) :
    ∫ θ in (0 : ℝ)..1, Real.exp (-θ * Real.log P) = (1 - P⁻¹) / Real.log P := by
  have hl : 0 < Real.log P := Real.log_pos hP
  have hP0 : 0 < P := by linarith
  have e : (fun θ : ℝ => Real.exp (-θ * Real.log P)) = fun θ => Real.exp (-Real.log P * θ) := by
    funext θ; ring_nf
  rw [e, intervalIntegral.integral_comp_mul_left (fun t => Real.exp t) (neg_ne_zero.mpr hl.ne'),
    integral_exp, mul_zero, mul_one, Real.exp_zero, Real.exp_neg, Real.exp_log hP0, smul_eq_mul]
  field_simp
  ring

/-- (KRON-W) applied to `f(θ) = exp(-θ log P)`. -/
theorem kron_apply {lam μi : ℝ} (hkw : kronW_statement lam μi) {P : ℝ} (hP : 1 < P) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ) (a : ℤ) (N : ℕ) (w : ℤ → ℝ), (∀ n, 0 ≤ w n) →
      (∀ n, n ∉ Finset.Ico a (a + N) → w n = 0) → ∀ ℓ : ℕ, 1 ≤ ℓ →
      |∑ n ∈ Finset.Ico a (a + N), w n * Real.exp (-(Int.fract ((n : ℝ) * lam + u)) * Real.log P)
          - (∑ n ∈ Finset.Ico a (a + N), w n) * ((1 - P⁻¹) / Real.log P)|
        ≤ 3 * ℓ * (∑ n ∈ Finset.Ico (a - 1) (a + N), |w (n + 1) - w n|)
          + C * ((∑ n ∈ Finset.Ico a (a + N), w n) * (ℓ : ℝ) ^ (-(1 / μi))
            + (∑ n ∈ Finset.Ico (a - 1) (a + N), |w (n + 1) - w n|) * (ℓ : ℝ) ^ (1 - 1 / μi)) := by
  obtain ⟨C, hC, hk⟩ := hkw
  refine ⟨C, hC, fun u a N w hw0 hwout ℓ hℓ => ?_⟩
  have hl : 0 < Real.log P := Real.log_pos hP
  have hanti : AntitoneOn (fun θ : ℝ => Real.exp (-θ * Real.log P)) (Set.Icc 0 1) := by
    intro s _ t _ hst
    apply Real.exp_le_exp.mpr
    nlinarith
  have hval : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ Real.exp (-θ * Real.log P) ∧ Real.exp (-θ * Real.log P) ≤ 1 := by
    intro θ hθ
    refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
    nlinarith [hθ.1]
  have h := hk (fun θ => Real.exp (-θ * Real.log P)) hanti hval u a N w hw0 hwout ℓ hℓ
  rw [integral_exp_neg_mul_log hP] at h
  exact h

/-- A sum over an interval of `ℕ` as a sum over an interval of `ℤ`. -/
theorem sum_Ico_natCast (a N : ℕ) (G : ℤ → ℝ) :
    ∑ n ∈ Finset.Ico (a : ℤ) ((a : ℤ) + N), G n = ∑ k ∈ Finset.Ico a (a + N), G k := by
  symm
  apply Finset.sum_nbij' (fun k : ℕ => (k : ℤ)) (fun n : ℤ => n.toNat)
  · intro k hk
    simp only [Finset.mem_Ico] at hk ⊢
    omega
  · intro n hn
    simp only [Finset.mem_Ico] at hn ⊢
    omega
  · intro k _
    simp
  · intro n hn
    simp only [Finset.mem_Ico] at hn
    omega
  · intro k _
    rfl

end DKernAux

end ND

end GGMCollatz
