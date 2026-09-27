import GGMCollatz.NatDen.Statements
import GGMCollatz.Tao.Sec5.Stabilization

/-!
# The first-passage profile of the logarithmic window, with a name (the logarithmic side of (D.2'))

`passLoc_approx` in `Tao/Sec5/Stabilization.lean` hides the profile `Φ` behind an `∃`, so it cannot be used for (D.2').
Here the same argument (the `key` step inside the proof of `passLoc_approx`: `window_formula` and `Iy_ratio`, bounding `Ψ(ℕ)`
via the normalization at `E = ℕ`, and `psi_mono`) is written on the window `[y, y^α]` (`y = x^α`, `β = α`) with the profile
named explicitly as `(μ/d) ψ_α(x, E)`.

The `key` part of the proof of `passLoc_approx` (derived from `TaoCollatz/Sec5/Stabilization.lean` of gotrevor/tao-collatz
(Apache-2.0), commit 15efca2, and generalized to the GGM family) is adapted, specialized to `β = α` and `y = x^α`, and changed to
the form in which `Φ` is explicitly `(μ/d) ψ`.
-/

namespace GGMCollatz

namespace ND

namespace TVAux

open Family

variable (F : Family)

/-- **Profile of the logarithmic window**: if `1 < α` and `α³ ≤ θ₀`, then the law of the first-passage location for the logarithmic
distribution on the window `[x^α, (x^α)^α]` is close, uniformly in `E`, to `(μ/d) ψ_α(x, E)` (error `K log^{-1/5} x`). -/
theorem logProf (α : ℝ) (hα : 1 < α) (hθ : α ^ 2 * α ≤ F.thetaMax) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop, ∀ E : Set ℕ,
      |Family.expect (F.logUnif (x ^ α) ((x ^ α) ^ α))
          (Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ E} 1) - F.mu / F.drift * F.psi α x E|
        ≤ K * Real.log x ^ (-(1 / 5 : ℝ)) := by
  have h33 := F.prop33
  have h41 := F.prop41_of_prop51 F.prop51
  obtain ⟨K, hK, hW⟩ := F.window_formula h33 h41 α α hα hα hθ
  obtain ⟨K₃, hK₃, h3⟩ := F.Iy_ratio α α hα hα hθ
  have hμ := F.mu_pos
  have hd := F.drift_pos
  have hμd : 0 < F.mu / F.drift := div_pos hμ hd
  set B : ℝ := (1 + K) * (2 * F.drift / F.mu) with hBdef
  have hB : 0 < B := by positivity
  refine ⟨K + K₃ * B, by positivity, ?_⟩
  have hsmall := eventually_log_rpow_neg_le (a := 1 / 5) (by norm_num)
    (show 0 < F.mu / F.drift / (2 * K₃) by positivity)
  filter_upwards [hW, h3, hsmall, eventually_log_ge 1, Filter.eventually_ge_atTop 1]
    with x hxW hx3 hxs hL hx1
  intro E
  have hLpos : 0 < Real.log x := by linarith
  set L5 := Real.log x ^ (-(1 / 5 : ℝ)) with hL5def
  have hL5nn : 0 ≤ L5 := Real.rpow_nonneg hLpos.le _
  have hL5le : L5 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by norm_num)
  -- window `y = x^α`
  have hαα : α ≤ α * α := by nlinarith
  have hy1 : x ^ α ≤ x ^ α := le_refl _
  have hy2 : x ^ α ≤ x ^ (α * α) := Real.rpow_le_rpow_of_exponent_le hx1 hαα
  obtain ⟨hZ, hratio⟩ := hx3 (x ^ α) hy1 hy2
  set y := x ^ α with hydef
  set r := ((F.Iy x y α).card : ℝ) / F.windowMass y (y ^ α) with hrdef
  have hrlo : F.mu / F.drift / 2 ≤ r := by
    have h1 := (abs_le.mp hratio).1
    have h2 : K₃ * L5 ≤ F.mu / F.drift / 2 := by
      have := mul_le_mul_of_nonneg_left hxs hK₃.le
      rw [show K₃ * (F.mu / F.drift / (2 * K₃)) = F.mu / F.drift / 2 by field_simp] at this
      exact this
    linarith
  have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hrlo
  -- normalization: at `E = ℕ` the probability is 1
  have huniv := hxW y hy1 hy2 Set.univ
  have hone : Family.expect (F.logUnif y (y ^ α))
      (Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ Set.univ} 1) = 1 := by
    have hset : {N | F.passLoc ⌊x⌋₊ N ∈ (Set.univ : Set ℕ)} = Set.univ := by
      ext N; simp
    rw [hset]
    unfold Family.expect
    simp only [Set.indicator_univ, Pi.one_apply, mul_one]
    exact tsum_toReal_eq_one _
  rw [hone, ← hrdef] at huniv
  have hΨu : F.psi α x Set.univ ≤ B := by
    have h1 : r * F.psi α x Set.univ ≤ 1 + K := by
      have := (abs_le.mp huniv).1
      nlinarith
    have h2 : F.psi α x Set.univ ≤ (1 + K) / r := by
      rw [le_div_iff₀ hrpos]; linarith
    calc F.psi α x Set.univ ≤ (1 + K) / r := h2
      _ ≤ (1 + K) / (F.mu / F.drift / 2) := by
          apply div_le_div_of_nonneg_left (by linarith) (by positivity) hrlo
      _ = B := by rw [hBdef]; field_simp
  have hΨ0 := F.psi_nonneg α x E
  have hΨB : F.psi α x E ≤ B := le_trans (F.psi_mono α x (Set.subset_univ E)) hΨu
  have hE := hxW y hy1 hy2 E
  calc _ ≤ |Family.expect (F.logUnif y (y ^ α)) (Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ E} 1)
            - r * F.psi α x E| + |r * F.psi α x E - F.mu / F.drift * F.psi α x E| :=
          abs_sub_le _ _ _
    _ ≤ K * L5 + K₃ * L5 * B := by
        apply add_le_add hE
        rw [← sub_mul, abs_mul, abs_of_nonneg hΨ0]
        exact mul_le_mul hratio hΨB hΨ0 (by positivity)
    _ = (K + K₃ * B) * L5 := by ring

end TVAux

end ND

end GGMCollatz
