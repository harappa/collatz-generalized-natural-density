import GGMCollatz.Tao.Sec7.HLMoment

/-!
# Quadratic bound for the moment generating function of `ℋ`, and lower bounds for the atoms of the tilted law

Counterpart of gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Prob/Mgf.lean` (`tiltZ_hold_le_quad`,
`tiltZ_hold_ne_zero`, `tilt_hold_apply_ge`); derived from it and generalized to the GGM family (p, q, r). Modified. tao-collatz proved these from the closed form and
numerical values (the box `1/200`, `1000`). Here they are proved in existential form from the exponential moment (`HLBase`), the exact mean (`HLMoment`) and
the pointwise bound `e^u ≤ 1 + u + 2u² e^{|u|}`.

* `hold_mgf_quad`: there are `b > 0`, `K ≥ 0` such that, if `|λᵢ| ≤ b`,
  `Z_ℋ(λ₁, λ₂) ≤ 1 + λλ₁ + νλ₂ + K(λ₁² + λ₂²)` (finite).
* `holdTilt`: the tilted `ℋ` (formally `ℋ` itself when `Z` is not finite).
* `holdTilt_atom_ge`: for `|λᵢ| ≤ b`, the tilted masses of the four atoms are at least a uniform positive `μ₀`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

namespace HL

/-- `e^u ≤ 1 + u + 2u² e^{|u|}`. -/
theorem exp_le_quad (u : ℝ) : Real.exp u ≤ 1 + u + 2 * u ^ 2 * Real.exp |u| := by
  have he1 : 1 ≤ Real.exp |u| := Real.one_le_exp (abs_nonneg u)
  rcases le_or_gt |u| 1 with h | h
  · have := Real.abs_exp_sub_one_sub_id_le h
    have h2 := (abs_le.mp this).2
    nlinarith [sq_nonneg u]
  · have hu2 : 1 ≤ u ^ 2 := by
      have := sq_abs u
      nlinarith
    have hexp : Real.exp u ≤ Real.exp |u| := Real.exp_le_exp.mpr (le_abs_self u)
    have habs : |u| + 1 ≤ Real.exp |u| := Real.add_one_le_exp _
    have hneg : -|u| ≤ u := neg_abs_le u
    nlinarith

/-- For `x ≥ 0`, `b > 0`: `x² e^{bx} ≤ (2/b²) e^{2bx}`. -/
theorem sq_mul_exp_le {b x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (b * x) ≤ 2 / b ^ 2 * Real.exp (2 * b * x) := by
  have hq := Real.quadratic_le_exp_of_nonneg (mul_nonneg hb.le hx)
  have hx2 : x ^ 2 ≤ 2 / b ^ 2 * Real.exp (b * x) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg hb.le hx, sq_nonneg (b * x)]
  calc x ^ 2 * Real.exp (b * x) ≤ 2 / b ^ 2 * Real.exp (b * x) * Real.exp (b * x) :=
        mul_le_mul_of_nonneg_right hx2 (Real.exp_pos _).le
    _ = 2 / b ^ 2 * Real.exp (2 * b * x) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf

variable (F : Family)

theorem tiltZ_hold_ne_zero (l1 l2 : ℝ) : tiltZ F.hold (expW2 l1 l2) ≠ 0 := by
  intro h0
  have hle : F.hold (1, 3) * expW2 l1 l2 (1, 3) ≤ tiltZ F.hold (expW2 l1 l2) :=
    ENNReal.le_tsum _
  rw [h0, le_zero_iff, mul_eq_zero] at hle
  rcases hle with h | h
  · rw [hold_one_three] at h
    exact (pascalP_three_pos F.two_le_p).ne' h
  · rw [expW2, ENNReal.ofReal_eq_zero] at h
    exact absurd h (not_le.mpr (Real.exp_pos _))

/-- Pointwise values of the weight. -/
theorem hold_mul_expW2 (l1 l2 : ℝ) (d : ℕ × ℤ) :
    F.hold d * expW2 l1 l2 d
      = ENNReal.ofReal ((F.hold d).toReal * Real.exp (l1 * d.1 + l2 * d.2)) := by
  rw [expW2, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

/-- **Quadratic bound for the moment generating function** (with the exact mean). -/
theorem hold_mgf_quad :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 / 4 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ l1 l2 : ℝ, |l1| ≤ b → |l2| ≤ b →
      tiltZ F.hold (expW2 l1 l2)
        ≤ ENNReal.ofReal (1 + F.holdMean1 * l1 + F.holdMean2 * l2 + K * (l1 ^ 2 + l2 ^ 2)) := by
  obtain ⟨β, hβ0, hβ1, hβtop⟩ := hold_expMoment F
  set b : ℝ := β / 2 with hbdef
  have hb0 : 0 < b := by positivity
  set h : ℕ × ℤ → ℝ := fun d => (F.hold d).toReal with hhdef
  set E : ℕ × ℤ → ℝ := fun d => Real.exp (β * d.1 + β * d.2) with hEdef
  have hh0 : ∀ d, 0 ≤ h d := fun d => ENNReal.toReal_nonneg
  -- `Σ h E` is summable
  have hsumE : Summable (fun d => h d * E d) := by
    have hs := ENNReal.summable_toReal hβtop
    refine hs.congr fun d => ?_
    rw [hold_mul_expW2]
    exact ENNReal.toReal_ofReal (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
  set M : ℝ := ∑' d, h d * E d with hM
  have hM0 : 0 ≤ M := tsum_nonneg fun d => mul_nonneg (hh0 d) (Real.exp_pos _).le
  -- facts on the support
  have hsupp : ∀ d, h d ≠ 0 → 1 ≤ d.1 ∧ 3 ≤ d.2 := fun d hd =>
    hold_support F (fun h0 => hd (by simp [hhdef, h0]))
  -- summability of the first moments
  have hsum1 : Summable (fun d => h d * (d.1 : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun d => mul_nonneg (hh0 d) (Nat.cast_nonneg _))
      (fun d => ?_) (hsumE.mul_left (1 / β))
    by_cases hd : h d = 0
    · rw [hd]; simp
    · have hs := hsupp d hd
      have h2 : (0 : ℝ) ≤ d.2 := by exact_mod_cast (by omega : (0 : ℤ) ≤ d.2)
      have hx := Real.add_one_le_exp (β * d.1 + β * d.2)
      have : (d.1 : ℝ) ≤ 1 / β * E d := by
        rw [hEdef, div_mul_eq_mul_div, le_div_iff₀ hβ0]; nlinarith
      calc h d * (d.1 : ℝ) ≤ h d * (1 / β * E d) := mul_le_mul_of_nonneg_left this (hh0 d)
        _ = 1 / β * (h d * E d) := by ring
  have hsum2 : Summable (fun d => h d * (d.2 : ℝ)) := by
    refine Summable.of_norm_bounded (hsumE.mul_left (1 / β)) (fun d => ?_)
    by_cases hd : h d = 0
    · rw [hd]; simp only [zero_mul, norm_zero]; positivity
    · have hs := hsupp d hd
      have h2 : (0 : ℝ) ≤ d.2 := by exact_mod_cast (by omega : (0 : ℤ) ≤ d.2)
      have h1 : (0 : ℝ) ≤ d.1 := Nat.cast_nonneg _
      have hx := Real.add_one_le_exp (β * d.1 + β * d.2)
      have : (d.2 : ℝ) ≤ 1 / β * E d := by
        rw [hEdef, div_mul_eq_mul_div, le_div_iff₀ hβ0]; nlinarith
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hh0 d) h2)]
      calc h d * (d.2 : ℝ) ≤ h d * (1 / β * E d) := mul_le_mul_of_nonneg_left this (hh0 d)
        _ = 1 / β * (h d * E d) := by ring
  set K : ℝ := 4 / b ^ 2 * M with hK
  refine ⟨b, hb0, by rw [hbdef]; linarith, K, by positivity, ?_⟩
  intro l1 l2 hl1 hl2
  set u : ℕ × ℤ → ℝ := fun d => l1 * d.1 + l2 * d.2 with hudef
  -- pointwise bound
  have hpt : ∀ d, h d * Real.exp (u d)
      ≤ h d + l1 * (h d * (d.1 : ℝ)) + l2 * (h d * (d.2 : ℝ))
        + 4 / b ^ 2 * (l1 ^ 2 + l2 ^ 2) * (h d * E d) := by
    intro d
    by_cases hd : h d = 0
    · rw [hd]; simp
    · have hs := hsupp d hd
      have h2 : (0 : ℝ) ≤ d.2 := by exact_mod_cast (by omega : (0 : ℤ) ≤ d.2)
      have h1 : (0 : ℝ) ≤ d.1 := Nat.cast_nonneg _
      set σ : ℝ := (d.1 : ℝ) + d.2 with hσ
      have hσ0 : 0 ≤ σ := by positivity
      have hu_abs : |u d| ≤ b * σ := by
        rw [hudef]
        calc |l1 * (d.1 : ℝ) + l2 * d.2| ≤ |l1 * (d.1 : ℝ)| + |l2 * d.2| := abs_add_le _ _
          _ = |l1| * d.1 + |l2| * d.2 := by
              rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h2]
          _ ≤ b * d.1 + b * d.2 := by
              gcongr
          _ = b * σ := by ring
      have hu_sq : u d ^ 2 ≤ (l1 ^ 2 + l2 ^ 2) * σ ^ 2 := by
        rw [hudef]
        nlinarith [sq_nonneg (l1 * d.2 - l2 * d.1), mul_nonneg h1 h2,
          mul_nonneg (mul_nonneg h1 h2) (sq_nonneg l1), mul_nonneg (mul_nonneg h1 h2) (sq_nonneg l2)]
      have hexpq := exp_le_quad (u d)
      have hexp_abs : Real.exp |u d| ≤ Real.exp (b * σ) := Real.exp_le_exp.mpr hu_abs
      have hsqe := sq_mul_exp_le hb0 hσ0
      have hEd : Real.exp (2 * b * σ) = E d := by
        rw [hEdef, hσ, hbdef]; congr 1; ring
      rw [hEd] at hsqe
      have hl2 : 0 ≤ l1 ^ 2 + l2 ^ 2 := by positivity
      have hquad : 2 * u d ^ 2 * Real.exp |u d| ≤ 4 / b ^ 2 * (l1 ^ 2 + l2 ^ 2) * E d := by
        calc 2 * u d ^ 2 * Real.exp |u d|
            ≤ 2 * ((l1 ^ 2 + l2 ^ 2) * σ ^ 2) * Real.exp (b * σ) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left hu_sq (by norm_num)) hexp_abs
                (Real.exp_pos _).le (by positivity)
          _ = 2 * (l1 ^ 2 + l2 ^ 2) * (σ ^ 2 * Real.exp (b * σ)) := by ring
          _ ≤ 2 * (l1 ^ 2 + l2 ^ 2) * (2 / b ^ 2 * E d) :=
              mul_le_mul_of_nonneg_left hsqe (by positivity)
          _ = 4 / b ^ 2 * (l1 ^ 2 + l2 ^ 2) * E d := by ring
      have hmain : Real.exp (u d) ≤ 1 + u d + 4 / b ^ 2 * (l1 ^ 2 + l2 ^ 2) * E d := by
        linarith
      calc h d * Real.exp (u d)
          ≤ h d * (1 + u d + 4 / b ^ 2 * (l1 ^ 2 + l2 ^ 2) * E d) :=
            mul_le_mul_of_nonneg_left hmain (hh0 d)
        _ = _ := by rw [hudef]; ring
  -- summability and the sum
  have hsumR : Summable (fun d => h d + l1 * (h d * (d.1 : ℝ)) + l2 * (h d * (d.2 : ℝ))
        + 4 / b ^ 2 * (l1 ^ 2 + l2 ^ 2) * (h d * E d)) :=
    (((ENNReal.summable_toReal F.hold.tsum_coe_ne_top).add (hsum1.mul_left l1)).add
      (hsum2.mul_left l2)).add (hsumE.mul_left _)
  have hsumL : Summable (fun d => h d * Real.exp (u d)) := by
    refine Summable.of_nonneg_of_le (fun d => mul_nonneg (hh0 d) (Real.exp_pos _).le)
      (fun d => ?_) hsumE
    by_cases hd : h d = 0
    · rw [hd]; simp
    · have hs := hsupp d hd
      have h2 : (0 : ℝ) ≤ d.2 := by exact_mod_cast (by omega : (0 : ℤ) ≤ d.2)
      have h1 : (0 : ℝ) ≤ d.1 := Nat.cast_nonneg _
      apply mul_le_mul_of_nonneg_left _ (hh0 d)
      apply Real.exp_le_exp.mpr
      rw [hudef]
      have e1 : l1 * (d.1 : ℝ) ≤ β * d.1 :=
        mul_le_mul_of_nonneg_right (le_trans (le_abs_self _) (by linarith)) h1
      have e2 : l2 * (d.2 : ℝ) ≤ β * d.2 :=
        mul_le_mul_of_nonneg_right (le_trans (le_abs_self _) (by linarith)) h2
      linarith
  have hval : ∑' d, (h d + l1 * (h d * (d.1 : ℝ)) + l2 * (h d * (d.2 : ℝ))
        + 4 / b ^ 2 * (l1 ^ 2 + l2 ^ 2) * (h d * E d))
      = 1 + F.holdMean1 * l1 + F.holdMean2 * l2 + K * (l1 ^ 2 + l2 ^ 2) := by
    rw [Summable.tsum_add (((ENNReal.summable_toReal F.hold.tsum_coe_ne_top).add
        (hsum1.mul_left l1)).add (hsum2.mul_left l2)) (hsumE.mul_left _),
      Summable.tsum_add ((ENNReal.summable_toReal F.hold.tsum_coe_ne_top).add
        (hsum1.mul_left l1)) (hsum2.mul_left l2),
      Summable.tsum_add (ENNReal.summable_toReal F.hold.tsum_coe_ne_top) (hsum1.mul_left l1),
      tsum_mul_left, tsum_mul_left, tsum_mul_left, hold_mean1R, hold_mean2R]
    have h1 : ∑' d, h d = 1 := by
      rw [hhdef, ← ENNReal.tsum_toReal_eq (fun d => PMF.apply_ne_top _ _), F.hold.tsum_coe,
        ENNReal.toReal_one]
    rw [h1, hK, ← hM]
    ring
  have hZ : tiltZ F.hold (expW2 l1 l2) = ENNReal.ofReal (∑' d, h d * Real.exp (u d)) := by
    rw [tiltZ, ENNReal.ofReal_tsum_of_nonneg (fun d => mul_nonneg (hh0 d) (Real.exp_pos _).le)
      hsumL]
    exact tsum_congr fun d => hold_mul_expW2 F l1 l2 d
  rw [hZ, ← hval]
  exact ENNReal.ofReal_le_ofReal (hsumL.tsum_le_tsum hpt hsumR)

/-- Exponential form: `Z_ℋ(λ) ≤ exp(λλ₁ + νλ₂ + K|λ|²)`. -/
theorem hold_mgf_exp :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 / 4 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ l1 l2 : ℝ, |l1| ≤ b → |l2| ≤ b →
      tiltZ F.hold (expW2 l1 l2)
        ≤ ENNReal.ofReal (Real.exp (F.holdMean1 * l1 + F.holdMean2 * l2
            + K * (l1 ^ 2 + l2 ^ 2))) := by
  obtain ⟨b, hb0, hb1, K, hK, h⟩ := hold_mgf_quad F
  refine ⟨b, hb0, hb1, K, hK, fun l1 l2 h1 h2 => le_trans (h l1 l2 h1 h2) ?_⟩
  apply ENNReal.ofReal_le_ofReal
  have := Real.add_one_le_exp (F.holdMean1 * l1 + F.holdMean2 * l2 + K * (l1 ^ 2 + l2 ^ 2))
  linarith

open Classical in
/-- The tilted `ℋ` (formally `ℋ` itself when `Z` is not finite). -/
noncomputable def holdTilt (l1 l2 : ℝ) : PMF (ℕ × ℤ) :=
  if h : tiltZ F.hold (expW2 l1 l2) ≠ ⊤ then
    tilt F.hold (expW2 l1 l2) (tiltZ_hold_ne_zero F l1 l2) h
  else F.hold

theorem holdTilt_eq {l1 l2 : ℝ} (h : tiltZ F.hold (expW2 l1 l2) ≠ ⊤) :
    holdTilt F l1 l2 = tilt F.hold (expW2 l1 l2) (tiltZ_hold_ne_zero F l1 l2) h := by
  unfold holdTilt; rw [dif_pos h]

/-- **Lower bound for tilted atoms**: if `|λᵢ| ≤ b`, `y₁ ≤ 2`, `0 ≤ y₂ ≤ 8`, then
`P_λ(y) ≥ ℋ(y) e^{-10b}/exp(λb + νb + 2Kb²)`. -/
theorem holdTilt_apply_ge {b K : ℝ} (hb0 : 0 < b)
    (hZ : ∀ l1 l2 : ℝ, |l1| ≤ b → |l2| ≤ b →
      tiltZ F.hold (expW2 l1 l2)
        ≤ ENNReal.ofReal (Real.exp (F.holdMean1 * l1 + F.holdMean2 * l2
            + K * (l1 ^ 2 + l2 ^ 2))))
    (hK : 0 ≤ K) {l1 l2 : ℝ} (hl1 : |l1| ≤ b) (hl2 : |l2| ≤ b) (y : ℕ × ℤ)
    (hy1 : (y.1 : ℝ) ≤ 2) (hy2 : (0 : ℝ) ≤ y.2) (hy2' : (y.2 : ℝ) ≤ 8) :
    (F.hold y).toReal * Real.exp (-(10 * b))
        / Real.exp (F.holdMean1 * b + F.holdMean2 * b + 2 * K * b ^ 2)
      ≤ (holdTilt F l1 l2 y).toReal := by
  have hZl := hZ l1 l2 hl1 hl2
  have hZt : tiltZ F.hold (expW2 l1 l2) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hZl
  have hZ0 := tiltZ_hold_ne_zero F l1 l2
  rw [holdTilt_eq F hZt, tilt_apply, ENNReal.toReal_mul, ENNReal.toReal_mul, expW2,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_inv]
  have hm1 : 0 ≤ F.holdMean1 := by rw [holdMean1]; have := p_real_ge_two F; positivity
  have hm2 : 0 ≤ F.holdMean2 := by
    rw [holdMean2]; have := p_real_ge_two F
    apply div_nonneg (by positivity) (pow_nonneg (by linarith) 3)
  have hZr : (tiltZ F.hold (expW2 l1 l2)).toReal
      ≤ Real.exp (F.holdMean1 * b + F.holdMean2 * b + 2 * K * b ^ 2) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hZl
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at h
    refine le_trans h (Real.exp_le_exp.mpr ?_)
    have e1 : F.holdMean1 * l1 ≤ F.holdMean1 * b :=
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hl1) hm1
    have e2 : F.holdMean2 * l2 ≤ F.holdMean2 * b :=
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hl2) hm2
    have e3 : l1 ^ 2 ≤ b ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hl1 2
    have e4 : l2 ^ 2 ≤ b ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hl2 2
    nlinarith
  have hZpos : 0 < (tiltZ F.hold (expW2 l1 l2)).toReal := ENNReal.toReal_pos hZ0 hZt
  have hw : Real.exp (-(10 * b)) ≤ Real.exp (l1 * y.1 + l2 * y.2) := by
    apply Real.exp_le_exp.mpr
    have h1 : 0 ≤ (y.1 : ℝ) := Nat.cast_nonneg _
    have a1 : -(b * y.1) ≤ l1 * y.1 := by
      have := neg_abs_le l1
      nlinarith
    have a2 : -(b * y.2) ≤ l2 * y.2 := by
      have := neg_abs_le l2
      nlinarith
    nlinarith
  rw [div_eq_mul_inv]
  apply mul_le_mul (mul_le_mul_of_nonneg_left hw ENNReal.toReal_nonneg)
    (inv_anti₀ hZpos hZr) (inv_nonneg.mpr (Real.exp_pos _).le)
    (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)

end HL

end Family

end GGMCollatz
