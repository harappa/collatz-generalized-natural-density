import GGMCollatz.Tao.Sec7.HLRenew

/-!
# Gaussian bound for the renewal measure of `ℋ` and the exponential one-step bound

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/FpLocation.lean` (`iidSum_hold_snd_zero`,
`renewalMass_eq_sum`, `renewalMass_toReal_eq`, `renewalMass_ne_top`, `renewalMass_zero_of_snd_neg`,
`renewalMass_bound_explicitC`, `hold_step_bound_explicitC`); generalized to the GGM family (p, q, r). Modified:
the mean `(4, 16)` became `(λ, ν)` and the center `l/4` became `l · slopeInv` (`slopeInv · ν = λ`, `slopeInv ≤ 1/2`).
The one-step bound is taken from the exponential moment `hold_expMoment`. No explicit constants (existential form).
-/

open scoped ENNReal

namespace GGMCollatz

open GGMCollatz.HL

namespace Family

namespace HL

variable (F : Family)

/-! ### Relation between `(λ, ν)` and the slope `slopeInv` -/

theorem slopeInv_mul_holdMean2 : F.slopeInv * F.holdMean2 = F.holdMean1 := by
  have hp : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have h1 : (F.p : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < F.p - 1).ne'
  have h0 : (F.p : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < F.p).ne'
  unfold slopeInv holdMean2 holdMean1
  field_simp

theorem slopeInv_nonneg : 0 ≤ F.slopeInv := by
  have hp : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  unfold slopeInv
  exact div_nonneg (by linarith) (by positivity)

theorem slopeInv_le_half : F.slopeInv ≤ 1 / 2 := by
  have hp : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  unfold slopeInv
  rw [div_le_iff₀ (by positivity)]
  linarith

theorem one_le_holdMean2 : 1 ≤ F.holdMean2 := by
  have hp : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hu : (1 : ℝ) ≤ F.p - 1 := by linarith
  unfold holdMean2
  rw [le_div_iff₀ (pow_pos (by linarith) 3), one_mul]
  have h3 : ((F.p : ℝ) - 1) ^ 3 ≤ (F.p : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have h4 : (F.p : ℝ) ^ 3 ≤ (F.p : ℝ) ^ 4 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  linarith

/-! ### The renewal measure as a finite sum -/

/-- One step of `ℋ` raises the height by at least `3`, so `k` steps cannot reach a height `< 3k`. -/
theorem iidSum_hold_snd_zero : ∀ (k : ℕ) (q : ℕ × ℤ), q.2 < 3 * (k : ℤ) →
    iidSum F.hold k q = 0 := by
  intro k
  induction k with
  | zero =>
    intro q hq
    rw [iidSum_zero, PMF.pure_apply, if_neg]
    intro h
    subst h
    simp at hq
  | succ k ih =>
    intro q hq
    rw [iidSum_succ_apply F]
    refine ENNReal.tsum_eq_zero.mpr fun d => ?_
    by_cases hd : F.hold d = 0
    · rw [hd, zero_mul]
    · have hd2 : 3 ≤ d.2 := F.hold_support_snd_ge d (by rwa [PMF.mem_support_iff])
      have hz : (∑' q' : ℕ × ℤ, if q = d + q' then iidSum F.hold k q' else 0) = 0 := by
        refine ENNReal.tsum_eq_zero.mpr fun q' => ?_
        by_cases he : q = d + q'
        · rw [if_pos he]
          refine ih q' ?_
          have hsnd : q.2 = d.2 + q'.2 := by rw [he]; rfl
          push_cast at hq ⊢
          omega
        · rw [if_neg he]
      rw [hz, mul_zero]

/-- The renewal measure at height `l ≥ 0` is a finite sum over `k ≤ ⌊l/3⌋`. -/
theorem renewalMass_eq_sum (j : ℕ) (l : ℤ) :
    renewalMass F (j, l)
      = ∑ k ∈ Finset.range (l.toNat / 3 + 1), iidSum F.hold k (j, l) := by
  rw [renewalMass]
  refine tsum_eq_sum fun k hk => iidSum_hold_snd_zero F k (j, l) ?_
  have hk' : l.toNat / 3 + 1 ≤ k := Nat.le_of_not_lt fun h => hk (Finset.mem_range.mpr h)
  show l < 3 * (k : ℤ)
  omega

theorem renewalMass_toReal_eq (j : ℕ) (l : ℤ) :
    (renewalMass F (j, l)).toReal
      = ∑ k ∈ Finset.range (l.toNat / 3 + 1), (iidSum F.hold k (j, l)).toReal := by
  rw [renewalMass_eq_sum, ENNReal.toReal_sum fun k _ => PMF.apply_ne_top _ _]

/-- The renewal measure is finite. -/
theorem renewalMass_ne_top (p : ℕ × ℤ) : renewalMass F p ≠ ⊤ := by
  obtain ⟨j, l⟩ := p
  rw [renewalMass_eq_sum]
  exact (ENNReal.sum_lt_top.mpr fun k _ =>
    lt_of_le_of_lt (PMF.coe_le_one _ _) ENNReal.one_lt_top).ne

/-- The renewal measure vanishes at negative heights. -/
theorem renewalMass_zero_of_snd_neg {p : ℕ × ℤ} (hp : p.2 < 0) : renewalMass F p = 0 := by
  rw [renewalMass]
  refine ENNReal.tsum_eq_zero.mpr fun k => iidSum_hold_snd_zero F k p ?_
  have : (0 : ℤ) ≤ 3 * (k : ℤ) := by positivity
  omega

/-! ### Gaussian bound for the renewal measure -/

/-- **Gaussian bound for the renewal measure** (the `ℋ` version of `renewalMass_bound` of tao-collatz, the first formula in the proof of
Lemma 7.7): `U(j,l) ≤ C₆/√(1+l) · G_{1+l}(c₆(j - l·slopeInv))`. Apply Lemma 2.2(i) (`hold_local_boundHL`) to each `k`,
peel off the weight of the height offset with `Gweight_factor_half`, and close the sum over `k` with `renewal_weight_sum_gen`. -/
theorem renewalMass_boundHL :
    ∃ c6 : ℝ, 0 < c6 ∧ ∃ C6 : ℝ, 0 < C6 ∧ ∀ (j : ℕ) (l : ℤ), 0 ≤ l →
      (renewalMass F (j, l)).toReal
        ≤ C6 / Real.sqrt (1 + (l : ℝ))
            * Gweight (1 + (l : ℝ)) (c6 * ((j : ℝ) - (l : ℝ) * F.slopeInv)) := by
  obtain ⟨c0, hc0, C0, hC0, hloc⟩ := hold_local_boundHL F
  set c1 : ℝ := c0 / 2 with hc1def
  have hc1 : 0 < c1 := by positivity
  obtain ⟨C5, hC5, hsum⟩ := renewal_weight_sum_gen (a := c1 ^ 2 / 4) (b := c1 / 2)
    (ν := F.holdMean2) (by positivity) (by positivity) (one_le_holdMean2 F)
  refine ⟨c1 / 2, by positivity, C0 * C5, mul_pos hC0 hC5, ?_⟩
  intro j l hl
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hι0 := slopeInv_nonneg F
  have hι1 := slopeInv_le_half F
  have hιν := slopeInv_mul_holdMean2 F
  set G : ℝ := Gweight (1 + (l : ℝ)) (c1 / 2 * ((j : ℝ) - (l : ℝ) * F.slopeInv)) with hGdef
  have hG : 0 ≤ G := Gweight_nonneg _ _
  set N : ℕ := l.toNat / 3 + 1 with hN
  have hkl : ∀ k ∈ Finset.range N, (k : ℝ) ≤ (l : ℝ) := by
    intro k hk
    have hk3 : k ≤ l.toNat := by
      have := Finset.mem_range.mp hk
      omega
    have h : ((k : ℕ) : ℝ) ≤ ((l.toNat : ℕ) : ℝ) := Nat.cast_le.mpr hk3
    rwa [show ((l.toNat : ℕ) : ℝ) = (l : ℝ) by
      exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg hl)] at h
  have hterm : ∀ k ∈ Finset.range N,
      (iidSum F.hold k (j, l)).toReal
        ≤ C0 * G * (1 / (1 + (k : ℝ))
            * (Real.exp (-(c1 ^ 2 / 4) * |(l : ℝ) - F.holdMean2 * k| ^ 2 / (1 + (k : ℝ)))
              + Real.exp (-(c1 / 2) * |(l : ℝ) - F.holdMean2 * k|))) := by
    intro k hk
    have h1 := hloc k j l
    rw [holdSum_eq_iidSum] at h1
    refine h1.trans ?_
    set u : ℝ := (j : ℝ) - F.holdMean1 * k with hu
    set v : ℝ := (l : ℝ) - F.holdMean2 * k with hv
    have h1k : (0 : ℝ) < 1 + (k : ℝ) := by positivity
    have h1kl : 1 + (k : ℝ) ≤ 1 + (l : ℝ) := by linarith [hkl k hk]
    have hnorm : ‖((u, v) : ℝ × ℝ)‖ = max |u| |v| := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    have hstep1 : Gweight (1 + (k : ℝ)) (c0 * ‖((u, v) : ℝ × ℝ)‖)
        ≤ Gweight (1 + (k : ℝ)) (c1 * (|u| + |v|)) := by
      apply Gweight_anti h1k (by positivity)
      rw [hnorm, hc1def]
      rcases max_cases |u| |v| with ⟨hm, hle⟩ | ⟨hm, hle⟩ <;> rw [hm] <;>
        nlinarith [abs_nonneg u, abs_nonneg v, hc0.le]
    have hxe : (j : ℝ) - (l : ℝ) * F.slopeInv = u - F.slopeInv * v := by
      rw [hu, hv]
      linear_combination (-(k : ℝ)) * hιν
    have hxabs : |(j : ℝ) - (l : ℝ) * F.slopeInv| ≤ |u| + |v| / 2 := by
      rw [hxe, abs_le]
      have h5 := mul_le_mul_of_nonneg_left (le_abs_self v) hι0
      have h6 := mul_le_mul_of_nonneg_left (neg_abs_le v) hι0
      have h7 := mul_le_mul_of_nonneg_right hι1 (abs_nonneg v)
      have h8 := le_abs_self u
      have h9 := neg_abs_le u
      constructor <;> nlinarith
    have hy : |(j : ℝ) - (l : ℝ) * F.slopeInv| + |v| / 2 ≤ |u| + |v| := by linarith
    have hstep2 := Gweight_factor_half (x := (j : ℝ) - (l : ℝ) * F.slopeInv) (z := |v|)
      (y := |u| + |v|) hc1 h1k h1kl (abs_nonneg v) hy
    calc C0 / (1 + (k : ℝ)) * Sec7.Gweight (1 + (k : ℝ)) (c0 * ‖((u, v) : ℝ × ℝ)‖)
        ≤ C0 / (1 + (k : ℝ)) * (G
            * (Real.exp (-(c1 ^ 2 / 4) * |v| ^ 2 / (1 + (k : ℝ)))
              + Real.exp (-(c1 / 2) * |v|))) := by
          apply mul_le_mul_of_nonneg_left (hstep1.trans hstep2) (by positivity)
      _ = C0 * G * (1 / (1 + (k : ℝ))
            * (Real.exp (-(c1 ^ 2 / 4) * |v| ^ 2 / (1 + (k : ℝ)))
              + Real.exp (-(c1 / 2) * |v|))) := by ring
  calc (renewalMass F (j, l)).toReal
      = ∑ k ∈ Finset.range N, (iidSum F.hold k (j, l)).toReal := renewalMass_toReal_eq F j l
    _ ≤ ∑ k ∈ Finset.range N, C0 * G * (1 / (1 + (k : ℝ))
          * (Real.exp (-(c1 ^ 2 / 4) * |(l : ℝ) - F.holdMean2 * k| ^ 2 / (1 + (k : ℝ)))
            + Real.exp (-(c1 / 2) * |(l : ℝ) - F.holdMean2 * k|))) := Finset.sum_le_sum hterm
    _ = C0 * G * ∑ k ∈ Finset.range N, 1 / (1 + (k : ℝ))
          * (Real.exp (-(c1 ^ 2 / 4) * |(l : ℝ) - F.holdMean2 * k| ^ 2 / (1 + (k : ℝ)))
            + Real.exp (-(c1 / 2) * |(l : ℝ) - F.holdMean2 * k|)) := by
        rw [Finset.mul_sum]
    _ ≤ C0 * G * (C5 / Real.sqrt (1 + (l : ℝ))) := by
        apply mul_le_mul_of_nonneg_left (hsum l hl) (by positivity)
    _ = C0 * C5 / Real.sqrt (1 + (l : ℝ)) * G := by ring

/-! ### Exponential one-step bound -/

/-- **One-step bound** (the `ℋ` version of `hold_step_bound` of tao-collatz): from the exponential moment `hold_expMoment`,
`ℋ(d) ≤ C₇ e^{-γ d₁} e^{-γ d₂}` (for all `d`). -/
theorem hold_step_boundHL :
    ∃ γ : ℝ, 0 < γ ∧ ∃ C7 : ℝ, 0 < C7 ∧ ∀ d : ℕ × ℤ,
      (F.hold d).toReal ≤ C7 * Real.exp (-γ * (d.1 : ℝ)) * Real.exp (-γ * (d.2 : ℝ)) := by
  obtain ⟨β, hβ0, -, hfin⟩ := hold_expMoment F
  set M : ℝ := (tiltZ F.hold (expW2 β β)).toReal with hM
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  refine ⟨β, hβ0, M + 1, by linarith, fun d => ?_⟩
  have hle : F.hold d * expW2 β β d ≤ tiltZ F.hold (expW2 β β) :=
    ENNReal.le_tsum (f := fun d => F.hold d * expW2 β β d) d
  have hw : expW2 β β d = ENNReal.ofReal (Real.exp (β * (d.1 : ℝ) + β * (d.2 : ℝ))) := rfl
  have hle' : (F.hold d).toReal * Real.exp (β * (d.1 : ℝ) + β * (d.2 : ℝ)) ≤ M := by
    have h := ENNReal.toReal_mono hfin hle
    rwa [ENNReal.toReal_mul, hw, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h
  have hE : Real.exp (-β * (d.1 : ℝ)) * Real.exp (-β * (d.2 : ℝ))
      * Real.exp (β * (d.1 : ℝ) + β * (d.2 : ℝ)) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]
    congr 1
    ring
  have hpos : 0 < Real.exp (-β * (d.1 : ℝ)) * Real.exp (-β * (d.2 : ℝ)) := by positivity
  have key : (F.hold d).toReal
      = (F.hold d).toReal * Real.exp (β * (d.1 : ℝ) + β * (d.2 : ℝ))
          * (Real.exp (-β * (d.1 : ℝ)) * Real.exp (-β * (d.2 : ℝ))) := by
    calc (F.hold d).toReal
        = (F.hold d).toReal * (Real.exp (-β * (d.1 : ℝ)) * Real.exp (-β * (d.2 : ℝ))
            * Real.exp (β * (d.1 : ℝ) + β * (d.2 : ℝ))) := by rw [hE, mul_one]
      _ = _ := by ring
  calc (F.hold d).toReal
      = (F.hold d).toReal * Real.exp (β * (d.1 : ℝ) + β * (d.2 : ℝ))
          * (Real.exp (-β * (d.1 : ℝ)) * Real.exp (-β * (d.2 : ℝ))) := key
    _ ≤ M * (Real.exp (-β * (d.1 : ℝ)) * Real.exp (-β * (d.2 : ℝ))) :=
        mul_le_mul_of_nonneg_right hle' hpos.le
    _ ≤ (M + 1) * (Real.exp (-β * (d.1 : ℝ)) * Real.exp (-β * (d.2 : ℝ))) :=
        mul_le_mul_of_nonneg_right (by linarith) hpos.le
    _ = (M + 1) * Real.exp (-β * (d.1 : ℝ)) * Real.exp (-β * (d.2 : ℝ)) := by ring

end HL

end Family

end GGMCollatz
