import GGMCollatz.Tao.Prob.Tilt

/-!
# Moment generating functions of `G(μ)`, `P(μ)` (counterpart of node S3 of tao-collatz, step (F2))

Derived from `TaoCollatz/Prob/Mgf.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2;
generalized to the GGM family (p, q, r): `geomHalf` (`p = 2`) is replaced by `geomP p`.
The moment generating function of the `Hold` distribution (two-dimensional, used only in GGM §7 and in
tao-collatz's Sec7) is handled separately and is not carried over here
(the two-dimensional weight `expW2` and the Cauchy–Schwarz splitting `tiltZ_expW2_sq_le` are general PMF lemmas,
so they were carried over).

* `expW λ a = e^{λa}`: the exponential weight on ℕ.
* `tiltZ_geomP`: `Z(λ) = (p-1)·r(1-r)⁻¹`, `r = e^λ/p` (geometric series; outside the band `e^λ < p` both sides are `∞`).
* `tiltZ_pascalP`: `Z_{P(μ)} = Z_{G(μ)}²` (on the band).
* `exp_le_one_add_add_two_sq`, `frac_closed_le`, etc.: numerical envelopes (independent of `p`).
-/

open scoped ENNReal

namespace GGMCollatz

/-- The exponential tilting weight `a ↦ e^{λa}` on ℕ. -/
noncomputable def expW (lam : ℝ) : ℕ → ℝ≥0∞ :=
  fun a => ENNReal.ofReal (Real.exp (lam * a))

theorem expW_zero (lam : ℝ) : expW lam 0 = 1 := by
  rw [expW]
  norm_num

theorem expW_add (lam : ℝ) (a b : ℕ) :
    expW lam (a + b) = expW lam a * expW lam b := by
  rw [expW, expW, expW, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  push_cast
  ring

/-- A positive weight does not make the partition function vanish: `Z(λ) ≠ 0` for any PMF on ℕ. -/
theorem tiltZ_expW_ne_zero (p : PMF ℕ) (lam : ℝ) : tiltZ p (expW lam) ≠ 0 := by
  intro h
  rw [tiltZ, ENNReal.tsum_eq_zero] at h
  have hp : ∀ a : ℕ, p a = 0 := fun a => by
    have ha := h a
    rcases mul_eq_zero.mp ha with h0 | h0
    · exact h0
    · exact absurd h0 (by
        rw [expW]
        exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
  have := p.tsum_coe
  rw [tsum_congr hp, tsum_zero] at this
  exact zero_ne_one this

/-- **Moment generating function of `G(μ)` (exact)**: `Z(λ) = (p-1)·r(1-r)⁻¹`, `r = e^λ/p`. Holds for all `λ`
(outside the band `e^λ < p` both sides are `∞`). Generalizes tao-collatz's `tiltZ_geomHalf`. -/
theorem tiltZ_geomP {p : ℕ} (hp : 2 ≤ p) (lam : ℝ) :
    tiltZ (geomP p) (expW lam)
      = ((p - 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (Real.exp lam / p)
          * (1 - ENNReal.ofReal (Real.exp lam / p))⁻¹) := by
  set r := ENNReal.ofReal (Real.exp lam / p) with hr
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hterm : ∀ a : ℕ, geomP p a * expW lam a
      = if a = 0 then 0 else ((p - 1 : ℕ) : ℝ≥0∞) * r ^ a := by
    intro a
    rw [geomP_apply hp, expW]
    split_ifs with h
    · rw [zero_mul]
    · rw [mul_assoc]
      congr 1
      rw [hr, ENNReal.ofReal_div_of_pos hp0, ENNReal.ofReal_natCast, div_eq_mul_inv, mul_pow,
        ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul, mul_comm]
      congr 3
      ring
  rw [tiltZ, tsum_congr hterm,
    tsum_ite_zero_eq_succ (fun a => ((p - 1 : ℕ) : ℝ≥0∞) * r ^ a),
    ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]

theorem tiltZ_geomP_ne_zero {p : ℕ} (lam : ℝ) : tiltZ (geomP p) (expW lam) ≠ 0 :=
  tiltZ_expW_ne_zero _ lam

theorem tiltZ_geomP_ne_top {p : ℕ} (hp : 2 ≤ p) {lam : ℝ} (hlam : Real.exp lam < p) :
    tiltZ (geomP p) (expW lam) ≠ ∞ := by
  rw [tiltZ_geomP hp]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hr1 : ENNReal.ofReal (Real.exp lam / p) < 1 :=
    ENNReal.ofReal_lt_one.mpr ((div_lt_one hp0).mpr hlam)
  refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.mpr ?_))
  rw [Ne, tsub_eq_zero_iff_le, not_le]
  exact hr1

/-- **The moment generating function of `P(μ)` is the square of that of `G(μ)`** (on the band). -/
theorem tiltZ_pascalP {p : ℕ} (hp : 2 ≤ p) {lam : ℝ} (hlam : Real.exp lam < p) :
    tiltZ (pascalP p) (expW lam) = (tiltZ (geomP p) (expW lam)) ^ 2 := by
  rw [pascalP_eq_iidSum]
  exact tiltZ_iidSum (geomP p) (expW_zero lam) (expW_add lam)
    (tiltZ_geomP_ne_zero lam) (tiltZ_geomP_ne_top hp hlam) 2

/-! ### Numerical envelopes (independent of `p`) -/

/-- On `[0, 1)`, `e^x ≤ (1-x)⁻¹` (from `1 - x ≤ e^{-x}`). -/
theorem exp_le_inv_one_sub {x : ℝ} (h1 : x < 1) :
    Real.exp x ≤ (1 - x)⁻¹ := by
  have hpos : 0 < 1 - x := by linarith
  have hexp : 0 < Real.exp x := Real.exp_pos x
  have h : 1 - x ≤ (Real.exp x)⁻¹ := by
    have := Real.add_one_le_exp (-x)
    rw [Real.exp_neg] at this
    linarith
  have hmul : Real.exp x * (1 - x) ≤ 1 := by
    have h2 := mul_le_mul_of_nonneg_left h hexp.le
    rwa [mul_inv_cancel₀ hexp.ne'] at h2
  calc Real.exp x = Real.exp x * (1 - x) * (1 - x)⁻¹ := by field_simp
    _ ≤ 1 * (1 - x)⁻¹ := mul_le_mul_of_nonneg_right hmul (by positivity)
    _ = (1 - x)⁻¹ := one_mul _

/-- Monotone bound on the closed form `r(1-r)⁻¹` of the geometric series in terms of a rational upper bound on the ratio. -/
theorem geom_closed_le {q q' : ℝ} (h0 : 0 ≤ q) (hqq : q ≤ q') (h1 : q' < 1) :
    ENNReal.ofReal q * (1 - ENNReal.ofReal q)⁻¹
      ≤ ENNReal.ofReal (q' / (1 - q')) := by
  have h1q' : 0 < 1 - q' := by linarith
  have h0' : 0 ≤ q' := le_trans h0 hqq
  have hstep : ENNReal.ofReal q * (1 - ENNReal.ofReal q)⁻¹
      ≤ ENNReal.ofReal q' * (1 - ENNReal.ofReal q')⁻¹ := by
    gcongr
  refine le_trans hstep (le_of_eq ?_)
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
    ← ENNReal.ofReal_sub 1 h0', ← ENNReal.ofReal_inv_of_pos h1q',
    ← ENNReal.ofReal_mul h0', div_eq_mul_inv]

/-- Quadratic upper envelope of the exponential: for `u ≤ 1/2`, `e^u ≤ 1 + u + 2u²` (from `e^u ≤ (1-u)⁻¹`). -/
theorem exp_le_one_add_add_two_sq {u : ℝ} (hu : u ≤ 1 / 2) :
    Real.exp u ≤ 1 + u + 2 * u ^ 2 := by
  have h1u : 0 < 1 - u := by linarith
  have hexp : Real.exp u ≤ (1 - u)⁻¹ := by
    have h : 1 - u ≤ Real.exp (-u) := by
      have := Real.add_one_le_exp (-u)
      linarith
    have h2 := inv_anti₀ h1u h
    rwa [Real.exp_neg, inv_inv] at h2
  refine le_trans hexp ?_
  rw [inv_eq_one_div, div_le_iff₀ h1u]
  nlinarith [sq_nonneg u]

/-- Monotone bound on `a·(1-r)⁻¹` in terms of rational upper bounds (the form of `geom_closed_le` with a free numerator). -/
theorem frac_closed_le {a a' r r' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') (hr : 0 ≤ r)
    (hrr : r ≤ r') (h1 : r' < 1) :
    ENNReal.ofReal a * (1 - ENNReal.ofReal r)⁻¹
      ≤ ENNReal.ofReal (a' / (1 - r')) := by
  have h1r : 0 < 1 - r' := by linarith
  have hstep : ENNReal.ofReal a * (1 - ENNReal.ofReal r)⁻¹
      ≤ ENNReal.ofReal a' * (1 - ENNReal.ofReal r')⁻¹ := by
    have h1 := ENNReal.ofReal_le_ofReal haa
    have h2 := ENNReal.ofReal_le_ofReal hrr
    gcongr
  refine le_trans hstep (le_of_eq ?_)
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
    ← ENNReal.ofReal_sub 1 (le_trans hr hrr), ← ENNReal.ofReal_inv_of_pos h1r,
    ← ENNReal.ofReal_mul (le_trans ha haa), div_eq_mul_inv]

/-- The moment generating function of `G(μ)` written as a real fraction: `Z(λ) = ofReal((p-1)e^λ/p)·(1 - ofReal(e^λ/p))⁻¹`. -/
theorem tiltZ_geomP_frac {p : ℕ} (hp : 2 ≤ p) (lam : ℝ) :
    tiltZ (geomP p) (expW lam)
      = ENNReal.ofReal (((p : ℝ) - 1) * Real.exp lam / p)
          * (1 - ENNReal.ofReal (Real.exp lam / p))⁻¹ := by
  rw [tiltZ_geomP hp, ← mul_assoc]
  congr 1
  have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  rw [mul_div_assoc, ENNReal.ofReal_mul hp1]
  congr 1
  rw [show ((p : ℝ) - 1) = ((p - 1 : ℕ) : ℝ) by
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one], ENNReal.ofReal_natCast]

/-! ### Two-dimensional weights (independent of `p`; the entry point for the moment generating function of the `Hold` distribution) -/

/-- The two-dimensional exponential weight on the renewal lattice `ℕ × ℤ`. -/
noncomputable def expW2 (l1 l2 : ℝ) : ℕ × ℤ → ℝ≥0∞ :=
  fun d => ENNReal.ofReal (Real.exp (l1 * d.1 + l2 * d.2))

theorem expW2_zero (l1 l2 : ℝ) : expW2 l1 l2 0 = 1 := by
  simp [expW2]

theorem expW2_add (l1 l2 : ℝ) (a b : ℕ × ℤ) :
    expW2 l1 l2 (a + b) = expW2 l1 l2 a * expW2 l1 l2 b := by
  simp only [expW2]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  ring

/-- `expW2` is the product of the weights of the two coordinates. -/
theorem expW2_eq_mul (l1 l2 : ℝ) (d : ℕ × ℤ) :
    expW2 l1 l2 d = expW2 l1 0 d * expW2 0 l2 d := by
  simp only [expW2]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

/-- The square of the weight is the weight with doubled tilt. -/
theorem expW2_sq (l1 l2 : ℝ) (d : ℕ × ℤ) :
    expW2 l1 l2 d ^ 2 = expW2 (2 * l1) (2 * l2) d := by
  simp only [expW2]
  rw [sq, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

/-- **Cauchy–Schwarz splitting of the two-dimensional moment generating function**: `Z(λ₁,λ₂)² ≤ Z(2λ₁,0)·Z(0,2λ₂)`. -/
theorem tiltZ_expW2_sq_le (p : PMF (ℕ × ℤ)) (l1 l2 : ℝ) :
    tiltZ p (expW2 l1 l2) ^ 2
      ≤ tiltZ p (expW2 (2 * l1) 0) * tiltZ p (expW2 0 (2 * l2)) := by
  rw [tiltZ]
  calc (∑' d, p d * expW2 l1 l2 d) ^ 2
      = (∑' d, p d * (expW2 l1 0 d * expW2 0 l2 d)) ^ 2 := by
        congr 1
        exact tsum_congr fun d => by rw [expW2_eq_mul]
    _ ≤ (∑' d, p d * (expW2 l1 0 d) ^ 2) * (∑' d, p d * (expW2 0 l2 d) ^ 2) :=
        tsum_mul_mul_sq_le (fun d : ℕ × ℤ => p d) (expW2 l1 0) (expW2 0 l2)
    _ = tiltZ p (expW2 (2 * l1) 0) * tiltZ p (expW2 0 (2 * l2)) := by
        rw [tiltZ, tiltZ]
        congr 1
        · exact tsum_congr fun d => by
            rw [expW2_sq, show (2 : ℝ) * 0 = 0 from by norm_num]
        · exact tsum_congr fun d => by
            rw [expW2_sq, show (2 : ℝ) * 0 = 0 from by norm_num]

end GGMCollatz
