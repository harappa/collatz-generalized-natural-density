import GGMCollatz.NatDen.Statements
import GGMCollatz.Tao.Sec5.Stabilization
import GGMCollatz.NatDen.TV.LogProf

/-!
# (D.2') Total variation between the uniform and logarithmic first-passage laws on the same window

`tvPass_of_uprof`: from the profile of the uniform side `uprof_statement` and the profile of the logarithmic side
(`window_formula` and `Iy_ratio` of `Tao/Sec5/Stabilization.lean`, with the same `ψ`; the named form is `TVAux.logProf`
in `NatDen/TV/LogProf.lean`).

Proof: `α₀ = min(α₀^{uprof}, θ₀^{1/3})`. If `1 < α ≤ α₀`, then `α³ ≤ θ₀`, so the profile of the logarithmic side applies.
For each event `E`, the probability under the pushforward is the probability of the preimage (`expect_map_indicator`), so by the
triangle inequality `|P_unif(Pass ∈ E) - P_log(Pass ∈ E)| ≤ K_u L^{-c} + K_l L^{-1/5}`; the total variation is at most twice the
upper bound for the differences over events (`dTV_le_of_forall_event`).
-/

namespace GGMCollatz

namespace ND

namespace TVAux

open Family

/-- If `1 < α ≤ θ^{1/3}` (`1 < θ`), then `α² α ≤ θ`. -/
theorem cube_le_of_le_rpow {α θ : ℝ} (hα : 1 < α) (hθ : 1 < θ) (h : α ≤ θ ^ (1 / 3 : ℝ)) :
    α ^ 2 * α ≤ θ := by
  have hα0 : 0 ≤ α := by linarith
  have h3 : α ^ 3 ≤ (θ ^ (1 / 3 : ℝ)) ^ 3 := pow_le_pow_left₀ hα0 h 3
  have hθ3 : (θ ^ (1 / 3 : ℝ)) ^ 3 = θ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  calc α ^ 2 * α = α ^ 3 := by ring
    _ ≤ θ := by rw [hθ3] at h3; exact h3

end TVAux

variable (F : Family)

/-- **(D.2')**: from the profile of the uniform side. -/
theorem tvPass_of_uprof (h : uprof_statement F) : tvPass_statement F := by
  obtain ⟨α₁, hα₁, hU⟩ := h
  have hθ := F.one_lt_thetaMax
  have hθ3 : 1 < F.thetaMax ^ (1 / 3 : ℝ) := Real.one_lt_rpow hθ (by norm_num)
  refine ⟨min α₁ (F.thetaMax ^ (1 / 3 : ℝ)), lt_min hα₁ hθ3, ?_⟩
  intro α hα hαα₀
  have hαcube : α ^ 2 * α ≤ F.thetaMax :=
    TVAux.cube_le_of_le_rpow hα hθ (le_trans hαα₀ (min_le_right _ _))
  obtain ⟨c, K, hc, hK, hev⟩ := hU α hα (le_trans hαα₀ (min_le_left _ _))
  obtain ⟨K', hK', hev'⟩ := TVAux.logProf F α hα hαcube
  set c' : ℝ := min c (1 / 5) with hc'def
  have hc' : 0 < c' := lt_min hc (by norm_num)
  refine ⟨c', 2 * (K + K'), hc', by positivity, ?_⟩
  filter_upwards [hev, hev', Family.eventually_log_ge 1] with x hx hx' hL
  have hLpos : 0 < Real.log x := by linarith
  have hm1 : Real.log x ^ (-c) ≤ Real.log x ^ (-c') :=
    Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg (min_le_left _ _))
  have hm2 : Real.log x ^ (-(1 / 5 : ℝ)) ≤ Real.log x ^ (-c') :=
    Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg (min_le_right _ _))
  have hev2 : ∀ E : Set ℕ,
      |Family.expect ((unifWin F (x ^ α) ((x ^ α) ^ α)).map (F.passLoc ⌊x⌋₊)) (Set.indicator E 1)
        - Family.expect ((F.logUnif (x ^ α) ((x ^ α) ^ α)).map (F.passLoc ⌊x⌋₊))
            (Set.indicator E 1)| ≤ (K + K') * Real.log x ^ (-c') := by
    intro E
    rw [Family.expect_map_indicator, Family.expect_map_indicator]
    have hA := hx E
    have hB := hx' E
    have htri := abs_sub_le
      (Family.expect (unifWin F (x ^ α) ((x ^ α) ^ α))
        (Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ E} 1))
      (F.mu / F.drift * F.psi α x E)
      (Family.expect (F.logUnif (x ^ α) ((x ^ α) ^ α))
        (Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ E} 1))
    rw [abs_sub_comm (F.mu / F.drift * F.psi α x E)] at htri
    have h1 : K * Real.log x ^ (-c) ≤ K * Real.log x ^ (-c') :=
      mul_le_mul_of_nonneg_left hm1 hK.le
    have h2 : K' * Real.log x ^ (-(1 / 5 : ℝ)) ≤ K' * Real.log x ^ (-c') :=
      mul_le_mul_of_nonneg_left hm2 hK'.le
    linarith
  have hd := Family.dTV_le_of_forall_event _ _ _ hev2
  calc _ ≤ 2 * ((K + K') * Real.log x ^ (-c')) := hd
    _ = 2 * (K + K') * Real.log x ^ (-c') := by ring

end ND

end GGMCollatz
