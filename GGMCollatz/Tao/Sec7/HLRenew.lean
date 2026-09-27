import GGMCollatz.Tao.Sec7.HLFpConv
import GGMCollatz.Tao.Sec7.HLAnal

/-!
# Gaussian bound for the renewal measure and the one-step bound (components of the proof of Lemma 7.7)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/FpLocation.lean` (`sum_abs_AP_le`,
`Gweight_factor`, `renewal_weight_sum_le_explicitC`, `iidSum_hold_snd_zero`, `renewalMass_eq_sum`,
`renewalMass_toReal_eq`, `renewalMass_ne_top`, `renewalMass_zero_of_snd_neg`, `renewalMass_bound_explicitC`,
`hold_step_bound_explicitC`); generalized to the GGM family (p, q, r). Modified: the mean `(4, 16)` of the walk became
`(λ, ν) = (holdMean1, holdMean2)`, the central slope `1/4` became `slopeInv = λ/ν`, and the common difference `16` of the
arithmetic progression became a real `ν ≥ 1`. No explicit constants (existential form). The one-step bound is taken not from
the case `n = 1` of Lemma 2.2(i) but from the exponential moment `hold_expMoment` (in the form `e^{-γ d₁} e^{-γ d₂}`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace HL

/-- **Arithmetic-progression sums** (real common difference `ν > 0`, center `x ≥ 0`): the values `|x - νk|` (`k < N`) cover each `νm` at most twice
(once on each side of `x/ν`). The bound `S` on the sum is one that applies to every partial sum. -/
theorem sum_abs_AP_gen {f : ℝ → ℝ} (hnn : ∀ u, 0 ≤ f u)
    (hanti : ∀ ⦃u v : ℝ⦄, 0 ≤ u → u ≤ v → f v ≤ f u)
    {ν x S : ℝ} (hν : 0 < ν) (hx : 0 ≤ x)
    (hS : ∀ M : ℕ, ∑ m ∈ Finset.range M, f (ν * m) ≤ S) (N : ℕ) :
    ∑ k ∈ Finset.range N, f |x - ν * k| ≤ 2 * S := by
  set q : ℕ := ⌊x / ν⌋₊ with hq
  have hq1 : ν * q ≤ x := by
    have h := Nat.floor_le (div_nonneg hx hν.le)
    rw [← hq, le_div_iff₀ hν] at h
    linarith
  have hq2 : x < ν * (q + 1) := by
    have h := Nat.lt_floor_add_one (x / ν)
    rw [← hq, div_lt_iff₀ hν] at h
    linarith
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun k => k ≤ q)]
  have hA : ∑ k ∈ (Finset.range N).filter (fun k => k ≤ q), f |x - ν * k| ≤ S := by
    have hstep : ∀ k ∈ (Finset.range N).filter (fun k => k ≤ q),
        f |x - ν * k| ≤ f (ν * ((q - k : ℕ) : ℝ)) := by
      intro k hk
      have hkq : k ≤ q := (Finset.mem_filter.mp hk).2
      have hkq' : (k : ℝ) ≤ q := by exact_mod_cast hkq
      refine hanti (mul_nonneg hν.le (Nat.cast_nonneg _)) ?_
      have hνk := mul_le_mul_of_nonneg_left hkq' hν.le
      have h0 : 0 ≤ x - ν * k := by linarith
      rw [abs_of_nonneg h0, Nat.cast_sub hkq, mul_sub]
      linarith
    have hinj : ∀ a ∈ (Finset.range N).filter (fun k => k ≤ q),
        ∀ b ∈ (Finset.range N).filter (fun k => k ≤ q), q - a = q - b → a = b := by
      intro a ha b hb hab
      have := (Finset.mem_filter.mp ha).2
      have := (Finset.mem_filter.mp hb).2
      omega
    calc ∑ k ∈ (Finset.range N).filter (fun k => k ≤ q), f |x - ν * k|
        ≤ ∑ k ∈ (Finset.range N).filter (fun k => k ≤ q), f (ν * ((q - k : ℕ) : ℝ)) :=
          Finset.sum_le_sum hstep
      _ = ∑ m ∈ ((Finset.range N).filter (fun k => k ≤ q)).image (fun k => q - k),
            f (ν * (m : ℝ)) := (Finset.sum_image (f := fun m : ℕ => f (ν * (m : ℝ))) hinj).symm
      _ ≤ ∑ m ∈ Finset.range (q + 1), f (ν * m) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => hnn _
          intro m hm
          obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hm
          exact Finset.mem_range.mpr (by omega)
      _ ≤ S := hS _
  have hB : ∑ k ∈ (Finset.range N).filter (fun k => ¬ k ≤ q), f |x - ν * k| ≤ S := by
    have hstep : ∀ k ∈ (Finset.range N).filter (fun k => ¬ k ≤ q),
        f |x - ν * k| ≤ f (ν * ((k - (q + 1) : ℕ) : ℝ)) := by
      intro k hk
      have hkq : q < k := Nat.lt_of_not_le (Finset.mem_filter.mp hk).2
      have hkq' : (q : ℝ) + 1 ≤ k := by exact_mod_cast hkq
      refine hanti (mul_nonneg hν.le (Nat.cast_nonneg _)) ?_
      have hνk := mul_le_mul_of_nonneg_left hkq' hν.le
      have h0 : x - ν * k ≤ 0 := by linarith
      rw [abs_of_nonpos h0, Nat.cast_sub (by omega : q + 1 ≤ k)]
      push_cast
      rw [mul_sub]
      linarith
    have hinj : ∀ a ∈ (Finset.range N).filter (fun k => ¬ k ≤ q),
        ∀ b ∈ (Finset.range N).filter (fun k => ¬ k ≤ q),
          a - (q + 1) = b - (q + 1) → a = b := by
      intro a ha b hb hab
      have := Nat.lt_of_not_le (Finset.mem_filter.mp ha).2
      have := Nat.lt_of_not_le (Finset.mem_filter.mp hb).2
      omega
    calc ∑ k ∈ (Finset.range N).filter (fun k => ¬ k ≤ q), f |x - ν * k|
        ≤ ∑ k ∈ (Finset.range N).filter (fun k => ¬ k ≤ q),
            f (ν * ((k - (q + 1) : ℕ) : ℝ)) := Finset.sum_le_sum hstep
      _ = ∑ m ∈ ((Finset.range N).filter (fun k => ¬ k ≤ q)).image (fun k => k - (q + 1)),
            f (ν * (m : ℝ)) := (Finset.sum_image (f := fun m : ℕ => f (ν * (m : ℝ))) hinj).symm
      _ ≤ ∑ m ∈ Finset.range N, f (ν * m) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => hnn _
          intro m hm
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
          have := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
          exact Finset.mem_range.mpr (by omega)
      _ ≤ S := hS _
  linarith

/-- **Splitting `Gweight`** (the hypothesis of `Gweight_factor` of tao-collatz replaced by `|x| + z/2 ≤ y`):
split into the product of the target weight (in `x`, with half the decay constant) and a weight in the height offset `z`. -/
theorem Gweight_factor_half {c1 t1 t2 x z y : ℝ} (hc1 : 0 < c1) (ht1 : 0 < t1)
    (ht : t1 ≤ t2) (hz : 0 ≤ z) (hy : |x| + z / 2 ≤ y) :
    Gweight t1 (c1 * y)
      ≤ Gweight t2 (c1 / 2 * x)
        * (Real.exp (-(c1 ^ 2 / 4) * z ^ 2 / t1) + Real.exp (-(c1 / 2) * z)) := by
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hy0 : 0 ≤ y := by linarith
  have ht2 : 0 < t2 := lt_of_lt_of_le ht1 ht
  set A := Real.exp (-(c1 / 2 * x) ^ 2 / t2) with hA
  set B := Real.exp (-(c1 ^ 2 / 4) * z ^ 2 / t1) with hB
  set C := Real.exp (-|c1 / 2 * x|) with hC
  set D := Real.exp (-(c1 / 2) * z) with hD
  have hquad : Real.exp (-(c1 * y) ^ 2 / t1) ≤ A * B := by
    rw [hA, hB, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hy2 : x ^ 2 + z ^ 2 / 4 ≤ y ^ 2 := by
      have h2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      nlinarith [mul_nonneg hx0 hz, sq_nonneg z]
    have h1 : (c1 / 2 * x) ^ 2 / t2 ≤ c1 ^ 2 * x ^ 2 / t1 := by
      rw [div_le_div_iff₀ ht2 ht1]
      nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg (c1 * x)),
        mul_nonneg (sq_nonneg (c1 * x)) ht1.le]
    have h2 : c1 ^ 2 * x ^ 2 / t1 + c1 ^ 2 / 4 * z ^ 2 / t1 ≤ (c1 * y) ^ 2 / t1 := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ ht1.le
      nlinarith [mul_le_mul_of_nonneg_left hy2 (sq_nonneg c1)]
    have e1 : -(c1 / 2 * x) ^ 2 / t2 = -((c1 / 2 * x) ^ 2 / t2) := by ring
    have e2 : -(c1 ^ 2 / 4) * z ^ 2 / t1 = -(c1 ^ 2 / 4 * z ^ 2 / t1) := by ring
    have e3 : -(c1 * y) ^ 2 / t1 = -((c1 * y) ^ 2 / t1) := by ring
    rw [e1, e2, e3]
    linarith
  have hlin : Real.exp (-|c1 * y|) ≤ C * D := by
    rw [hC, hD, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg (mul_nonneg hc1.le hy0), abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < c1 / 2)]
    nlinarith [mul_le_mul_of_nonneg_left hy hc1.le, mul_nonneg hc1.le hx0,
      mul_nonneg hc1.le hz]
  have hABCD : A * B + C * D ≤ (A + C) * (B + D) := by
    nlinarith [mul_nonneg (Real.exp_pos (-(c1 / 2 * x) ^ 2 / t2)).le
        (Real.exp_pos (-(c1 / 2) * z)).le,
      mul_nonneg (Real.exp_pos (-|c1 / 2 * x|)).le
        (Real.exp_pos (-(c1 ^ 2 / 4) * z ^ 2 / t1)).le]
  calc Gweight t1 (c1 * y) = Real.exp (-(c1 * y) ^ 2 / t1) + Real.exp (-|c1 * y|) := rfl
    _ ≤ A * B + C * D := add_le_add hquad hlin
    _ ≤ (A + C) * (B + D) := hABCD
    _ = Gweight t2 (c1 / 2 * x) * (B + D) := rfl

/-- **Edge zone of the renewal sum over `k`** (the first half of `renewal_weight_sum_le_explicitC` of tao-collatz, generalized to a real
common difference `ν ≥ 1`): for `k < ⌊l/(2ν)⌋` the height offset is at least `l/2`, and `W_k` is exponentially small in `l`. -/
theorem renewal_edge_le {a b ν : ℝ} (ha : 0 < a) (hb : 0 < b) (hν : 1 ≤ ν) (l : ℤ) (hl : 0 ≤ l) :
    ∑ k ∈ (Finset.range (l.toNat / 3 + 1)).filter (fun k => k < ⌊(l : ℝ) / (2 * ν)⌋₊),
      1 / (1 + (k : ℝ))
        * (Real.exp (-a * |(l : ℝ) - ν * k| ^ 2 / (1 + (k : ℝ)))
          + Real.exp (-b * |(l : ℝ) - ν * k|))
      ≤ (32 / min (a / 8) (b / 2) ^ 2) / Real.sqrt (1 + (l : ℝ)) := by
  set ε : ℝ := min (a / 8) (b / 2) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hν0 : 0 < ν := by linarith
  set t : ℕ := l.toNat with hts
  have hcast : ((t : ℕ) : ℝ) = (l : ℝ) := by
    have := Int.toNat_of_nonneg hl
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) this
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have h1l : (0 : ℝ) < 1 + (l : ℝ) := by linarith
  set s : ℝ := Real.sqrt (1 + (l : ℝ)) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr h1l
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr (by linarith)
  have hss : s * s = 1 + (l : ℝ) := Real.mul_self_sqrt h1l.le
  set N : ℕ := t / 3 + 1 with hN
  set T : ℕ := ⌊(l : ℝ) / (2 * ν)⌋₊ with hT
  have hTle : (T : ℝ) ≤ (l : ℝ) / (2 * ν) := Nat.floor_le (by positivity)
  have hTlt : (l : ℝ) / (2 * ν) < T + 1 := Nat.lt_floor_add_one _
  have hkl : ∀ k ∈ Finset.range N, (k : ℝ) ≤ (l : ℝ) := by
    intro k hk
    have hk' : k ≤ t := by
      have := Finset.mem_range.mp hk
      omega
    rw [← hcast]
    exact_mod_cast hk'
  by_cases hT0 : T = 0
  · rw [Finset.filter_false_of_mem (fun k _ => by omega), Finset.sum_empty]
    positivity
  · have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hT0
    have hl1 : (1 : ℝ) ≤ (l : ℝ) := by
      have h2 := le_trans hT1 hTle
      rw [le_div_iff₀ (by positivity), one_mul] at h2
      linarith
    have hbound : ∀ k ∈ (Finset.range N).filter (fun k => k < T),
        1 / (1 + (k : ℝ))
          * (Real.exp (-a * |(l : ℝ) - ν * k| ^ 2 / (1 + (k : ℝ)))
            + Real.exp (-b * |(l : ℝ) - ν * k|))
        ≤ 2 * Real.exp (-(ε * (l : ℝ))) := by
      intro k hk
      have hkT : k < T := (Finset.mem_filter.mp hk).2
      have hkN := (Finset.mem_filter.mp hk).1
      have hνk : ν * (k : ℝ) ≤ (l : ℝ) / 2 := by
        have h1 : (k : ℝ) + 1 ≤ T := by exact_mod_cast hkT
        have h2 : (k : ℝ) ≤ (l : ℝ) / (2 * ν) := by linarith
        rw [le_div_iff₀ (by positivity)] at h2
        linarith
      have hzl : (l : ℝ) / 2 ≤ |(l : ℝ) - ν * k| := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      have h1k : (0 : ℝ) < 1 + (k : ℝ) := by positivity
      have h1kl : 1 + (k : ℝ) ≤ 1 + (l : ℝ) := by
        linarith [hkl k hkN]
      have hq : ε * (l : ℝ) ≤ a * |(l : ℝ) - ν * k| ^ 2 / (1 + (k : ℝ)) := by
        have h1 : a * ((l : ℝ) / 2) ^ 2 / (1 + (l : ℝ))
            ≤ a * |(l : ℝ) - ν * k| ^ 2 / (1 + (k : ℝ)) := by
          calc a * ((l : ℝ) / 2) ^ 2 / (1 + (l : ℝ))
              ≤ a * |(l : ℝ) - ν * k| ^ 2 / (1 + (l : ℝ)) := by
                gcongr
            _ ≤ a * |(l : ℝ) - ν * k| ^ 2 / (1 + (k : ℝ)) :=
                div_le_div_of_nonneg_left (by positivity) h1k h1kl
        have h2 : ε * (l : ℝ) ≤ a * ((l : ℝ) / 2) ^ 2 / (1 + (l : ℝ)) := by
          rw [le_div_iff₀ h1l]
          have hεa : ε ≤ a / 8 := min_le_left _ _
          nlinarith [mul_nonneg ha.le (mul_nonneg hl0 (sub_nonneg.mpr hl1)),
            mul_le_mul_of_nonneg_right hεa (mul_nonneg hl0 h1l.le)]
        linarith
      have hlin : ε * (l : ℝ) ≤ b * |(l : ℝ) - ν * k| := by
        have hεb : ε ≤ b / 2 := min_le_right _ _
        nlinarith [mul_le_mul_of_nonneg_left hzl hb.le,
          mul_le_mul_of_nonneg_right hεb hl0]
      have hE1 : Real.exp (-a * |(l : ℝ) - ν * k| ^ 2 / (1 + (k : ℝ)))
          ≤ Real.exp (-(ε * (l : ℝ))) := by
        apply Real.exp_le_exp.mpr
        rw [neg_mul, neg_div]
        linarith
      have hE2 : Real.exp (-b * |(l : ℝ) - ν * k|)
          ≤ Real.exp (-(ε * (l : ℝ))) := by
        apply Real.exp_le_exp.mpr
        rw [neg_mul]
        linarith
      have hfr : 1 / (1 + (k : ℝ)) ≤ 1 := by
        rw [div_le_one h1k]
        linarith
      calc 1 / (1 + (k : ℝ))
          * (Real.exp (-a * |(l : ℝ) - ν * k| ^ 2 / (1 + (k : ℝ)))
            + Real.exp (-b * |(l : ℝ) - ν * k|))
          ≤ 1 * (Real.exp (-(ε * (l : ℝ))) + Real.exp (-(ε * (l : ℝ)))) := by
            apply mul_le_mul hfr (add_le_add hE1 hE2) (by positivity) one_pos.le
        _ = 2 * Real.exp (-(ε * (l : ℝ))) := by ring
    have hcard : ∑ k ∈ (Finset.range N).filter (fun k => k < T),
        1 / (1 + (k : ℝ))
          * (Real.exp (-a * |(l : ℝ) - ν * k| ^ 2 / (1 + (k : ℝ)))
            + Real.exp (-b * |(l : ℝ) - ν * k|))
        ≤ (1 + (l : ℝ)) * (2 * Real.exp (-(ε * (l : ℝ)))) := by
      calc ∑ k ∈ (Finset.range N).filter (fun k => k < T),
          1 / (1 + (k : ℝ))
            * (Real.exp (-a * |(l : ℝ) - ν * k| ^ 2 / (1 + (k : ℝ)))
              + Real.exp (-b * |(l : ℝ) - ν * k|))
          ≤ ∑ _k ∈ (Finset.range N).filter (fun k => k < T),
            2 * Real.exp (-(ε * (l : ℝ))) := Finset.sum_le_sum hbound
        _ = (((Finset.range N).filter (fun k => k < T)).card : ℝ)
            * (2 * Real.exp (-(ε * (l : ℝ)))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (1 + (l : ℝ)) * (2 * Real.exp (-(ε * (l : ℝ)))) := by
            apply mul_le_mul_of_nonneg_right ?_ (by positivity)
            have hc1 : ((Finset.range N).filter (fun k => k < T)).card ≤ N :=
              le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_range])
            have hc2 : ((N : ℕ) : ℝ) ≤ 1 + (l : ℝ) := by
              have hN3 : ((t / 3 : ℕ) : ℝ) ≤ (t : ℝ) / 3 := Nat.cast_div_le
              have : (N : ℝ) = ((t / 3 : ℕ) : ℝ) + 1 := by
                rw [hN]; push_cast; ring
              rw [this, ← hcast] at *
              nlinarith [Nat.cast_nonneg (α := ℝ) t]
            exact le_trans (Nat.cast_le.mpr hc1) hc2
    refine hcard.trans ?_
    rw [le_div_iff₀ hs0]
    have hsle : s ≤ 1 + (l : ℝ) := by
      calc s ≤ s * s := le_mul_of_one_le_left hs0.le hs1
        _ = 1 + (l : ℝ) := hss
    have hεl : 0 < ε * (l : ℝ) := mul_pos hε0 (by linarith)
    have hexp : Real.exp (-(ε * (l : ℝ))) ≤ 4 / (ε * (l : ℝ)) ^ 2 :=
      exp_neg_le_four_div_sq hεl
    have h2l : 1 + (l : ℝ) ≤ 2 * (l : ℝ) := by linarith
    calc (1 + (l : ℝ)) * (2 * Real.exp (-(ε * (l : ℝ)))) * s
        ≤ (1 + (l : ℝ)) * (2 * Real.exp (-(ε * (l : ℝ)))) * (1 + (l : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hsle (by positivity)
      _ = 2 * ((1 + (l : ℝ)) ^ 2 * Real.exp (-(ε * (l : ℝ)))) := by ring
      _ ≤ 2 * ((2 * (l : ℝ)) ^ 2 * (4 / (ε * (l : ℝ)) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
          apply mul_le_mul (by nlinarith) hexp (Real.exp_pos _).le (by positivity)
      _ = 32 / ε ^ 2 := by
          field_simp
          ring

/-- **Central zone of the renewal sum over `k`** (the second half of `renewal_weight_sum_le_explicitC` of tao-collatz, generalized to a real
common difference `ν ≥ 1`): for `k ≥ ⌊l/(2ν)⌋`, `(1+k)⁻¹ ≤ (2ν+1)/(1+l)`, and the sum of the height offsets is an arithmetic-progression sum. -/
theorem renewal_central_le {a b ν : ℝ} (ha : 0 < a) (hb : 0 < b) (hν : 1 ≤ ν) (l : ℤ)
    (hl : 0 ≤ l) :
    ∑ k ∈ (Finset.range (l.toNat / 3 + 1)).filter (fun k => ¬ k < ⌊(l : ℝ) / (2 * ν)⌋₊),
      1 / (1 + (k : ℝ))
        * (Real.exp (-a * |(l : ℝ) - ν * k| ^ 2 / (1 + (k : ℝ)))
          + Real.exp (-b * |(l : ℝ) - ν * k|))
      ≤ (2 * ν + 1) * ((8 + 2 / (b * ν)) + 4 / (ν * Real.sqrt a)) / Real.sqrt (1 + (l : ℝ)) := by
  set ε : ℝ := min (a / 8) (b / 2) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hν0 : 0 < ν := by linarith
  set t : ℕ := l.toNat with hts
  have hcast : ((t : ℕ) : ℝ) = (l : ℝ) := by
    have := Int.toNat_of_nonneg hl
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) this
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have h1l : (0 : ℝ) < 1 + (l : ℝ) := by linarith
  set s : ℝ := Real.sqrt (1 + (l : ℝ)) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr h1l
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr (by linarith)
  have hss : s * s = 1 + (l : ℝ) := Real.mul_self_sqrt h1l.le
  set N : ℕ := t / 3 + 1 with hN
  set T : ℕ := ⌊(l : ℝ) / (2 * ν)⌋₊ with hT
  have hTle : (T : ℝ) ≤ (l : ℝ) / (2 * ν) := Nat.floor_le (by positivity)
  have hTlt : (l : ℝ) / (2 * ν) < T + 1 := Nat.lt_floor_add_one _
  have hkl : ∀ k ∈ Finset.range N, (k : ℝ) ≤ (l : ℝ) := by
    intro k hk
    have hk' : k ≤ t := by
      have := Finset.mem_range.mp hk
      omega
    rw [← hcast]
    exact_mod_cast hk'
  set P : ℝ := 8 + 2 / (b * ν) with hP
  set Q : ℝ := 4 / (ν * Real.sqrt a) with hQ
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hper : ∀ k ∈ (Finset.range N).filter (fun k => ¬ k < T),
      1 / (1 + (k : ℝ))
        * (Real.exp (-a * |(l : ℝ) - ν * k| ^ 2 / (1 + (k : ℝ)))
          + Real.exp (-b * |(l : ℝ) - ν * k|))
      ≤ (2 * ν + 1) / (1 + (l : ℝ))
        * (Real.exp (-a * |(l : ℝ) - ν * k| ^ 2 / (1 + (l : ℝ)))
          + Real.exp (-b * |(l : ℝ) - ν * k|)) := by
    intro k hk
    have hkT : T ≤ k := Nat.le_of_not_lt (Finset.mem_filter.mp hk).2
    have hkN := (Finset.mem_filter.mp hk).1
    have h1k : (0 : ℝ) < 1 + (k : ℝ) := by positivity
    have h1kl : 1 + (k : ℝ) ≤ 1 + (l : ℝ) := by linarith [hkl k hkN]
    have hlk : 1 + (l : ℝ) ≤ (2 * ν + 1) * (1 + (k : ℝ)) := by
      have hTk : (T : ℝ) ≤ k := by exact_mod_cast hkT
      have h1 : (l : ℝ) / (2 * ν) < k + 1 := by linarith
      rw [div_lt_iff₀ (by positivity)] at h1
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    have hfrac : 1 / (1 + (k : ℝ)) ≤ (2 * ν + 1) / (1 + (l : ℝ)) := by
      rw [div_le_div_iff₀ h1k h1l]
      linarith
    have hquad : Real.exp (-a * |(l : ℝ) - ν * k| ^ 2 / (1 + (k : ℝ)))
        ≤ Real.exp (-a * |(l : ℝ) - ν * k| ^ 2 / (1 + (l : ℝ))) := by
      apply Real.exp_le_exp.mpr
      rw [neg_mul, neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (by positivity) h1k h1kl
    apply mul_le_mul hfrac (add_le_add hquad le_rfl) (by positivity) (by positivity)
  have hf1nn : ∀ u : ℝ, 0 ≤ Real.exp (-a * u ^ 2 / (1 + (l : ℝ))) :=
    fun u => (Real.exp_pos _).le
  have hf1anti : ∀ ⦃u v : ℝ⦄, 0 ≤ u → u ≤ v →
      Real.exp (-a * v ^ 2 / (1 + (l : ℝ))) ≤ Real.exp (-a * u ^ 2 / (1 + (l : ℝ))) := by
    intro u v hu huv
    apply Real.exp_le_exp.mpr
    rw [neg_mul, neg_div, neg_mul, neg_div, neg_le_neg_iff]
    apply div_le_div_of_nonneg_right ?_ h1l.le
    nlinarith [mul_self_le_mul_self hu huv, ha.le]
  have hf2nn : ∀ u : ℝ, 0 ≤ Real.exp (-b * u) := fun u => (Real.exp_pos _).le
  have hf2anti : ∀ ⦃u v : ℝ⦄, 0 ≤ u → u ≤ v →
      Real.exp (-b * v) ≤ Real.exp (-b * u) := by
    intro u v hu huv
    apply Real.exp_le_exp.mpr
    nlinarith
  set β : ℝ := a * ν ^ 2 / (1 + (l : ℝ)) with hβdef
  have hβ : 0 < β := by positivity
  have hS1 : ∀ M : ℕ, ∑ m ∈ Finset.range M,
      Real.exp (-a * (ν * (m : ℝ)) ^ 2 / (1 + (l : ℝ))) ≤ 3 + 2 / Real.sqrt β := by
    intro M
    calc ∑ m ∈ Finset.range M, Real.exp (-a * (ν * (m : ℝ)) ^ 2 / (1 + (l : ℝ)))
        = ∑ m ∈ Finset.range M, Real.exp (-β * (m : ℝ) ^ 2) := by
          refine Finset.sum_congr rfl fun m _ => congrArg Real.exp ?_
          rw [hβdef]
          ring
      _ ≤ 3 + 2 / Real.sqrt β := sum_range_exp_neg_sq_le hβ M
  have hS2 : ∀ M : ℕ, ∑ m ∈ Finset.range M, Real.exp (-b * (ν * (m : ℝ)))
      ≤ 1 + 1 / (b * ν) := by
    intro M
    calc ∑ m ∈ Finset.range M, Real.exp (-b * (ν * (m : ℝ)))
        = ∑ m ∈ Finset.range M, Real.exp (-(b * ν) * m) := by
          refine Finset.sum_congr rfl fun m _ => congrArg Real.exp ?_
          ring
      _ ≤ 1 + 1 / (b * ν) := sum_exp_geom_le (by positivity) M
  have hAP1 := sum_abs_AP_gen hf1nn hf1anti hν0 hl0 hS1 N
  have hAP2 := sum_abs_AP_gen hf2nn hf2anti hν0 hl0 hS2 N
  have hβs : Real.sqrt β * s = ν * Real.sqrt a := by
    rw [hs, ← Real.sqrt_mul hβ.le]
    rw [show β * (1 + (l : ℝ)) = ν ^ 2 * a by rw [hβdef, div_mul_cancel₀ _ h1l.ne']; ring]
    rw [Real.sqrt_mul (sq_nonneg ν), Real.sqrt_sq hν0.le]
  have hβpos : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have h4β : 4 / Real.sqrt β = Q * s := by
    rw [hQ, div_mul_eq_mul_div, div_eq_div_iff hβpos.ne' (by positivity)]
    linarith [hβs]
  calc ∑ k ∈ (Finset.range N).filter (fun k => ¬ k < T),
      1 / (1 + (k : ℝ))
        * (Real.exp (-a * |(l : ℝ) - ν * k| ^ 2 / (1 + (k : ℝ)))
          + Real.exp (-b * |(l : ℝ) - ν * k|))
      ≤ ∑ k ∈ (Finset.range N).filter (fun k => ¬ k < T),
        (2 * ν + 1) / (1 + (l : ℝ))
          * (Real.exp (-a * |(l : ℝ) - ν * k| ^ 2 / (1 + (l : ℝ)))
            + Real.exp (-b * |(l : ℝ) - ν * k|)) := Finset.sum_le_sum hper
    _ ≤ ∑ k ∈ Finset.range N,
        (2 * ν + 1) / (1 + (l : ℝ))
          * (Real.exp (-a * |(l : ℝ) - ν * k| ^ 2 / (1 + (l : ℝ)))
            + Real.exp (-b * |(l : ℝ) - ν * k|)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun k _ _ => by positivity
    _ = (2 * ν + 1) / (1 + (l : ℝ))
        * (∑ k ∈ Finset.range N, Real.exp (-a * |(l : ℝ) - ν * k| ^ 2 / (1 + (l : ℝ)))
          + ∑ k ∈ Finset.range N, Real.exp (-b * |(l : ℝ) - ν * k|)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (2 * ν + 1) / (1 + (l : ℝ)) * (P + Q * s) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        have e2 : 2 * (1 / (b * ν)) = 2 / (b * ν) := by ring
        have e4 : 2 * (2 / Real.sqrt β) = 4 / Real.sqrt β := by ring
        rw [hP]
        linarith [hAP1, hAP2, h4β, e2, e4]
    _ ≤ (2 * ν + 1) * (P + Q) / s := by
        rw [← hss, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hs0]
        have h21 : 0 ≤ 2 * ν + 1 := by linarith
        nlinarith [mul_nonneg (mul_nonneg h21 hP0) (mul_nonneg hs0.le (sub_nonneg.mpr hs1))]

/-- **Envelope of the renewal sum over `k`** (`renewal_weight_sum_le_explicitC` of tao-collatz, generalized to a real common difference `ν ≥ 1`,
in existential form): the sum of `(1+k)⁻¹ W_k` over `k ≤ ⌊l/3⌋` is `C₅/√(1+l)`. -/
theorem renewal_weight_sum_gen {a b ν : ℝ} (ha : 0 < a) (hb : 0 < b) (hν : 1 ≤ ν) :
    ∃ C5 : ℝ, 0 < C5 ∧ ∀ (l : ℤ), 0 ≤ l →
      ∑ k ∈ Finset.range (l.toNat / 3 + 1),
      1 / (1 + (k : ℝ))
        * (Real.exp (-a * |(l : ℝ) - ν * k| ^ 2 / (1 + (k : ℝ)))
          + Real.exp (-b * |(l : ℝ) - ν * k|))
        ≤ C5 / Real.sqrt (1 + (l : ℝ)) := by
  have hε0 : 0 < min (a / 8) (b / 2) := lt_min (by positivity) (by positivity)
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hν0 : 0 < ν := by linarith
  refine ⟨32 / min (a / 8) (b / 2) ^ 2
      + (2 * ν + 1) * ((8 + 2 / (b * ν)) + 4 / (ν * Real.sqrt a)), by positivity, ?_⟩
  intro l hl
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (l.toNat / 3 + 1))
    (fun k => k < ⌊(l : ℝ) / (2 * ν)⌋₊), add_div]
  exact add_le_add (renewal_edge_le ha hb hν l hl) (renewal_central_le ha hb hν l hl)

end HL

end GGMCollatz
