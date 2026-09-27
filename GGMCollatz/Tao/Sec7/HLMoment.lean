import GGMCollatz.Tao.Sec7.HLBase
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The mean of `ℋ` (exact): `E𝒥 = λ = p³/(2(p-1)²)`, `E𝒫_{1,𝒥} = ν = p⁴/(p-1)³`

Lean proof of GGM §6 Step 1 (`E ℋ = λ(1, 2μ)`). tao-collatz obtained the mean `(4, 16)` as the first-order term of the
closed form of the moment generating function (`tiltZ_hold_fst`, `tiltZ_hold_snd` in `TaoCollatz/Prob/Mgf.lean`). Here it is
derived directly from linearity of sums in `ℝ≥0∞` (the mean of a sum of i.i.d. variables) and geometric series. Generalized to the GGM family (p, q, r).

* `tsum_iid_sum_mul`: `E[Σᵢ f(vᵢ)] = n E[f]` (i.i.d., in `ℝ≥0∞`).
* `geomP_mean = μ`, `pascalP_mean = 2μ`, `ne3_mean = (2μ - 3s)/(1-s)`, `holdGeom_mean = 1/s`.
* `hold_mean1R`, `hold_mean2R`: the real means `λ`, `ν`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

namespace HL

/-! ### General lemmas -/

/-- Mean of a sum of i.i.d. variables: `∑' v, iid n v · Σᵢ f(vᵢ) = n · ∑' a, μ a · f a`. -/
theorem tsum_iid_sum_mul {α : Type*} (μ : PMF α) (f : α → ℝ≥0∞) :
    ∀ n : ℕ, ∑' v : Fin n → α, μ.iid n v * ∑ i, f (v i) = n * ∑' a, μ a * f a := by
  intro n
  induction n with
  | zero =>
    rw [PMF.tsum_iid_zero_mul μ (fun v => ∑ i, f (v i))]
    simp
  | succ n IH =>
    rw [PMF.tsum_iid_succ_mul μ n (fun v => ∑ i, f (v i))]
    have h1 : ∀ a : α, μ a * ∑' w : Fin n → α, μ.iid n w * ∑ i, f ((Fin.cons a w : Fin (n+1) → α) i)
        = μ a * f a + μ a * (n * ∑' b, μ b * f b) := by
      intro a
      have hsplit : ∀ w : Fin n → α, μ.iid n w * ∑ i, f ((Fin.cons a w : Fin (n+1) → α) i)
          = μ.iid n w * f a + μ.iid n w * ∑ i, f (w i) := by
        intro w
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        ring
      rw [tsum_congr hsplit, ENNReal.tsum_add, ENNReal.tsum_mul_right, (μ.iid n).tsum_coe,
        one_mul, IH, mul_add]
    rw [tsum_congr h1, ENNReal.tsum_add, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
    push_cast
    ring

/-- `Σ k r^k k = r/(1-r)²` (in `ℝ≥0∞`). -/
theorem tsum_ofReal_pow_mul_nat {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    ∑' k : ℕ, ENNReal.ofReal r ^ k * (k : ℝ≥0∞) = ENNReal.ofReal (r / (1 - r) ^ 2) := by
  have hr : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have hs : Summable (fun k : ℕ => (k : ℝ) * r ^ k) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  rw [← tsum_coe_mul_geometric_of_norm_lt_one hr,
    ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs]
  refine tsum_congr fun k => ?_
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_pow h0,
    mul_comm]

/-- `Σ r^k = (1-r)⁻¹` (in `ℝ≥0∞`). -/
theorem tsum_ofReal_pow {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    ∑' k : ℕ, ENNReal.ofReal r ^ k = ENNReal.ofReal ((1 - r)⁻¹) := by
  rw [ENNReal.tsum_geometric, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ h0,
    ENNReal.ofReal_inv_of_pos (by linarith)]

variable (F : Family)

theorem p_inv_eq : ((F.p : ℝ≥0∞))⁻¹ = ENNReal.ofReal (1 / (F.p : ℝ)) := by
  have := p_real_ge_two F
  rw [one_div, ENNReal.ofReal_inv_of_pos (by linarith), ENNReal.ofReal_natCast]

theorem pm1_eq : ((F.p - 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((F.p : ℝ) - 1) := by
  rw [← ENNReal.ofReal_natCast, Nat.cast_sub (by have := F.two_le_p; omega), Nat.cast_one]

/-! ### Means -/

/-- `E G(μ) = μ = p/(p-1)`. -/
theorem geomP_mean :
    ∑' k, geomP F.p k * (k : ℝ≥0∞) = ENNReal.ofReal ((F.p : ℝ) / ((F.p : ℝ) - 1)) := by
  have hp := p_real_ge_two F
  have hterm : ∀ k : ℕ, geomP F.p k * (k : ℝ≥0∞)
      = ((F.p - 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (1 / (F.p : ℝ)) ^ k * (k : ℝ≥0∞)) := by
    intro k
    rw [geomP_apply F.two_le_p, ← p_inv_eq]
    split_ifs with h
    · subst h; simp
    · ring
  rw [tsum_congr hterm, ENNReal.tsum_mul_left,
    tsum_ofReal_pow_mul_nat (by positivity) (by rw [div_lt_one (by linarith)]; linarith),
    pm1_eq, ← ENNReal.ofReal_mul (by linarith)]
  congr 1
  have h1 : (F.p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (F.p : ℝ) ≠ 0 := by linarith
  field_simp

/-- `E P(μ) = 2μ`. -/
theorem pascalP_mean :
    ∑' b, pascalP F.p b * (b : ℝ≥0∞) = ENNReal.ofReal (2 * ((F.p : ℝ) / ((F.p : ℝ) - 1))) := by
  have hp := p_real_ge_two F
  rw [pascal_eq_map_iid, PMF.tsum_map_mul]
  have h := tsum_iid_sum_mul (geomP F.p) (fun k => (k : ℝ≥0∞)) 2
  have hcongr : ∀ v : Fin 2 → ℕ, (PMF.iid (geomP F.p) 2) v * ((v 0 + v 1 : ℕ) : ℝ≥0∞)
      = (PMF.iid (geomP F.p) 2) v * ∑ i, ((v i : ℕ) : ℝ≥0∞) := by
    intro v
    rw [Fin.sum_univ_two]
    push_cast
    ring
  rw [tsum_congr hcongr, h, geomP_mean, ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- `(1-s) Σ_b P_{≠3}(b) g(b) + s g(3) = Σ_b P(b) g(b)`. -/
theorem ne3_decomp (g : ℕ → ℝ≥0∞) :
    (1 - pascalP F.p 3) * ∑' b, pascalNe3P F.p b * g b + pascalP F.p 3 * g 3
      = ∑' b, pascalP F.p b * g b := by
  have hp := F.two_le_p
  rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_eq_add_tsum_ite (f := fun b => pascalP F.p b * g b) 3, add_comm]
  congr 1
  refine tsum_congr fun b => ?_
  rw [pascalNe3P_apply hp]
  by_cases hb : b = 3
  · simp [hb]
  · rw [if_neg hb, if_neg hb, ← mul_assoc, ← mul_assoc,
      ENNReal.mul_inv_cancel (one_sub_pascal3_ne_zero F) (one_sub_pascal3_ne_top F), one_mul]

/-- `3s ≤ 2μ`. -/
theorem three_s_le : 3 * sR F ≤ 2 * ((F.p : ℝ) / ((F.p : ℝ) - 1)) := by
  have hp := p_real_ge_two F
  rw [sR_eq]
  rw [show 3 * (2 * ((F.p : ℝ) - 1) ^ 2 / (F.p : ℝ) ^ 3) = 6 * ((F.p : ℝ) - 1) ^ 2 / (F.p : ℝ) ^ 3
    by ring, show 2 * ((F.p : ℝ) / ((F.p : ℝ) - 1)) = 2 * (F.p : ℝ) / ((F.p : ℝ) - 1) by ring,
    div_le_div_iff₀ (by positivity) (by linarith)]
  nlinarith [sq_nonneg ((F.p : ℝ) ^ 2 - 2 * (F.p : ℝ)), sq_nonneg ((F.p : ℝ) - 3 / 2),
    mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg ((F.p : ℝ) - 1)),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hp)) (sq_nonneg (F.p : ℝ))]

/-- `E P_{≠3} = (2μ - 3s)/(1-s)`. -/
theorem ne3_mean :
    ∑' b, pascalNe3P F.p b * (b : ℝ≥0∞)
      = ENNReal.ofReal ((2 * ((F.p : ℝ) / ((F.p : ℝ) - 1)) - 3 * sR F) / (1 - sR F)) := by
  have hs := sR_pos F
  have hs1 := sR_lt_one F
  have hdec := ne3_decomp F (fun b => (b : ℝ≥0∞))
  rw [pascalP_mean] at hdec
  have h3 : pascalP F.p 3 * ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (3 * sR F) := by
    rw [← ofReal_sR F, ENNReal.ofReal_mul (by positivity)]
    push_cast
    rw [ENNReal.ofReal_ofNat]
    ring
  rw [h3] at hdec
  have hsub := ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top hdec
  rw [← ENNReal.ofReal_sub _ (by positivity), one_sub_pascal3_eq] at hsub
  have hne0 : ENNReal.ofReal (1 - sR F) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hX : ∑' b, pascalNe3P F.p b * (b : ℝ≥0∞)
      = (ENNReal.ofReal (1 - sR F))⁻¹
        * ENNReal.ofReal (2 * ((F.p : ℝ) / ((F.p : ℝ) - 1)) - 3 * sR F) := by
    rw [← hsub, ← mul_assoc, ENNReal.inv_mul_cancel hne0 ENNReal.ofReal_ne_top, one_mul]
  rw [hX, ← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_mul (by
    have := (inv_pos.mpr (show 0 < 1 - sR F by linarith)); positivity)]
  congr 1
  ring

/-- `E𝒥 = 1/s`. -/
theorem holdGeom_mean : ∑' k, holdGeom F.p k * (k : ℝ≥0∞) = ENNReal.ofReal (1 / sR F) := by
  have hs := sR_pos F
  have hs1 := sR_lt_one F
  rw [tsum_eq_zero_add' ENNReal.summable, F.holdGeom_zero, zero_mul, zero_add]
  have hterm : ∀ j : ℕ, holdGeom F.p (j + 1) * ((j + 1 : ℕ) : ℝ≥0∞)
      = pascalP F.p 3 * (ENNReal.ofReal (1 - sR F) ^ j * (j : ℝ≥0∞))
        + pascalP F.p 3 * ENNReal.ofReal (1 - sR F) ^ j := by
    intro j
    rw [holdGeom_succ, one_sub_pascal3_eq]
    push_cast
    ring
  rw [tsum_congr hterm, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
    tsum_ofReal_pow_mul_nat (by linarith) (by linarith), tsum_ofReal_pow (by linarith)
    (by linarith), ← ofReal_sR F, ← ENNReal.ofReal_mul hs.le, ← ENNReal.ofReal_mul hs.le,
    ← ENNReal.ofReal_add (by
      have : 0 ≤ (1 - sR F) / (1 - (1 - sR F)) ^ 2 := div_nonneg (by linarith) (by positivity)
      positivity) (by
      have : 0 ≤ (1 - (1 - sR F))⁻¹ := inv_nonneg.mpr (by linarith)
      positivity)]
  congr 1
  have hsne : sR F ≠ 0 := hs.ne'
  rw [sub_sub_cancel]
  field_simp
  ring

/-- **`E𝒥 = λ`** (in `ℝ≥0∞`). -/
theorem hold_mean1 : ∑' d, F.hold d * (d.1 : ℝ≥0∞) = ENNReal.ofReal F.holdMean1 := by
  have hs := sR_pos F
  rw [hold, PMF.tsum_bind_mul]
  have hk : ∀ k : ℕ, holdGeom F.p k * ∑' d,
      (((pascalNe3P F.p).iid (k - 1)).map
        fun v => (k, (3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ))) d * (d.1 : ℝ≥0∞)
      = holdGeom F.p k * (k : ℝ≥0∞) := by
    intro k
    rw [PMF.tsum_map_mul]
    dsimp only
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rw [tsum_congr hk, holdGeom_mean]
  congr 1
  rw [sR_eq, holdMean1]
  have := p_real_ge_two F
  have h1 : (F.p : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/-- **`E𝒫_{1,𝒥} = ν`** (in `ℝ≥0∞`; the second coordinate via `toNat`). -/
theorem hold_mean2 :
    ∑' d, F.hold d * ((d.2.toNat : ℕ) : ℝ≥0∞) = ENNReal.ofReal F.holdMean2 := by
  have hs := sR_pos F
  have hs1 := sR_lt_one F
  have hp := p_real_ge_two F
  set X := ∑' b, pascalNe3P F.p b * (b : ℝ≥0∞) with hX
  rw [hold, PMF.tsum_bind_mul]
  have hk : ∀ k : ℕ, holdGeom F.p k * ∑' d,
      (((pascalNe3P F.p).iid (k - 1)).map
        fun v => (k, (3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ))) d * ((d.2.toNat : ℕ) : ℝ≥0∞)
      = 3 * holdGeom F.p k + X * (holdGeom F.p k * ((k - 1 : ℕ) : ℝ≥0∞)) := by
    intro k
    rw [PMF.tsum_map_mul]
    have hv : ∀ v : Fin (k - 1) → ℕ,
        ((pascalNe3P F.p).iid (k - 1)) v
            * ((((k, (3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ)) : ℕ × ℤ).2.toNat : ℕ) : ℝ≥0∞)
          = 3 * ((pascalNe3P F.p).iid (k - 1)) v
            + ((pascalNe3P F.p).iid (k - 1)) v * ∑ i, ((v i : ℕ) : ℝ≥0∞) := by
      intro v
      have htn : (((3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ)).toNat) = 3 + ∑ i, v i := by
        have : ((3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ)) = ((3 + ∑ i, v i : ℕ) : ℤ) := by push_cast; rfl
        rw [this, Int.toNat_natCast]
      simp only
      rw [htn]
      push_cast
      ring
    rw [tsum_congr hv, ENNReal.tsum_add, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one,
      tsum_iid_sum_mul]
    ring
  rw [tsum_congr hk, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
    PMF.tsum_coe, mul_one]
  -- `Σ P(𝒥 = k)(k-1) = 1/s - 1`
  have hkm1 : ∑' k, holdGeom F.p k * ((k - 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (1 / sR F - 1) := by
    have hsum : ∑' k, holdGeom F.p k * ((k - 1 : ℕ) : ℝ≥0∞) + 1
        = ∑' k, holdGeom F.p k * (k : ℝ≥0∞) := by
      rw [← (holdGeom F.p).tsum_coe, ← ENNReal.tsum_add]
      refine tsum_congr fun k => ?_
      rcases k with _ | k
      · rw [F.holdGeom_zero]; simp
      · rw [Nat.add_sub_cancel]; push_cast; ring
    rw [holdGeom_mean] at hsum
    have h := ENNReal.eq_sub_of_add_eq ENNReal.one_ne_top hsum
    rw [h, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ zero_le_one]
  rw [hkm1, hX, ne3_mean, ← ENNReal.ofReal_mul (by
      apply div_nonneg (by linarith [three_s_le F]) (by linarith)),
    show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by rw [ENNReal.ofReal_ofNat],
    ← ENNReal.ofReal_add (by norm_num) (by
      apply mul_nonneg (div_nonneg (by linarith [three_s_le F]) (by linarith))
      rw [sub_nonneg, le_div_iff₀ hs]; linarith)]
  congr 1
  have key : ∀ s m : ℝ, s ≠ 0 → 1 - s ≠ 0 →
      3 + (2 * m - 3 * s) / (1 - s) * (1 / s - 1) = 2 * m / s := by
    intro s m h1 h2
    field_simp
    ring
  rw [key _ _ hs.ne' (by linarith), holdMean2, sR_eq]
  have h1 : (F.p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (F.p : ℝ) ≠ 0 := by linarith
  field_simp

/-! ### Real means -/

theorem hold_support {d : ℕ × ℤ} (hd : F.hold d ≠ 0) : 1 ≤ d.1 ∧ 3 ≤ d.2 :=
  ⟨F.hold_support_fst_pos d ((PMF.mem_support_iff _ _).mpr hd),
    F.hold_support_snd_ge d ((PMF.mem_support_iff _ _).mpr hd)⟩

theorem hold_mean1R : ∑' d, (F.hold d).toReal * (d.1 : ℝ) = F.holdMean1 := by
  have h := congrArg ENNReal.toReal (hold_mean1 F)
  rw [ENNReal.tsum_toReal_eq (fun d => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    (ENNReal.natCast_ne_top _)), ENNReal.toReal_ofReal (by
      rw [holdMean1]; have := p_real_ge_two F; positivity)] at h
  rw [← h]
  refine tsum_congr fun d => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]

theorem hold_mean2R : ∑' d, (F.hold d).toReal * (d.2 : ℝ) = F.holdMean2 := by
  have h := congrArg ENNReal.toReal (hold_mean2 F)
  rw [ENNReal.tsum_toReal_eq (fun d => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    (ENNReal.natCast_ne_top _)), ENNReal.toReal_ofReal (by
      rw [holdMean2]; have := p_real_ge_two F
      apply div_nonneg (by positivity) (pow_nonneg (by linarith) 3))] at h
  rw [← h]
  refine tsum_congr fun d => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  by_cases h0 : F.hold d = 0
  · rw [h0]; simp
  · have h3 := (hold_support F h0).2
    congr 1
    have : ((d.2.toNat : ℕ) : ℤ) = d.2 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this.symm

end HL

end Family

end GGMCollatz
