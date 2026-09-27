import GGMCollatz.NatDen.UProf.DKern.Hockey

/-!
# Piece (d) of (DK): sum and variation of the Gauss envelope ((E2)(E3))

`gau A B c t = A exp(-B(t - c)²)` (the true Gaussian obtained from the paper's `w̃` by replacing `n'` in the prefactor
and the denominator by `n'_*`; the cost of the replacement goes into the relative error in `Env.lean`).

* `gau_sum` (form of (E3)): for `a ∈ [c-R-1, c-R]` and `a + N ∈ [c+R, c+R+1]`,
  `|Σ_{i<N} gau(a+i) - A√(π/B)| ≤ N·AB(2R+2) + A√(2π/B) e^{-BR²/2}`. Compare the sum with the integral on each unit
  interval (`|e^{-s} - e^{-t}| ≤ |s - t|`), and bound the integral outside the window by
  `e^{-B(t-c)²} ≤ e^{-BR²/2} e^{-B(t-c)²/2}`.
* `wt_var` (form of (E2)): the variation of the Gaussian weight `wt` truncated to the window `[a, a+N)`
  (including the jumps at both ends of the support) is at most `(N+1)(AB(2R+1) + A e^{-B(R-1)²})`.
-/

namespace GGMCollatz

namespace ND

namespace DKernAux

/-- `|e^{-x} - e^{-y}| ≤ |x - y|` (`x, y ≥ 0`). -/
theorem abs_exp_neg_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  wlog hxy : x ≤ y generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x y]
    exact this hy hx (le_of_not_ge hxy)
  have h1 : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  have h2 : Real.exp (-y) = Real.exp (-x) * Real.exp (-(y - x)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : 1 - (y - x) ≤ Real.exp (-(y - x)) := by linarith [Real.add_one_le_exp (-(y - x))]
  have h4 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h5 : 0 < Real.exp (-x) := Real.exp_pos _
  rw [h2]
  nlinarith [mul_le_mul_of_nonneg_left h3 h5.le, mul_le_mul_of_nonneg_right h4 (by linarith : (0:ℝ) ≤ y - x)]

/-- The Gaussian function `A exp(-B(t - c)²)`. -/
noncomputable def gau (A B c t : ℝ) : ℝ := A * Real.exp (-B * (t - c) ^ 2)

theorem gau_nonneg {A : ℝ} (hA : 0 ≤ A) (B c t : ℝ) : 0 ≤ gau A B c t :=
  mul_nonneg hA (Real.exp_pos _).le

theorem gau_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (c t : ℝ) : gau A B c t ≤ A := by
  unfold gau
  have : Real.exp (-B * (t - c) ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg (t - c)]
  nlinarith

/-- `|g(s) - g(t)| ≤ AB|(s-c)² - (t-c)²|`. -/
theorem gau_sub_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (c s t : ℝ) :
    |gau A B c s - gau A B c t| ≤ A * B * |(s - c) ^ 2 - (t - c) ^ 2| := by
  unfold gau
  rw [← mul_sub, abs_mul, abs_of_nonneg hA, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hA
  have h := abs_exp_neg_sub_le (mul_nonneg hB (sq_nonneg (s - c))) (mul_nonneg hB (sq_nonneg (t - c)))
  rw [neg_mul, neg_mul]
  refine le_trans h (le_of_eq ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg hB]

theorem gau_continuous (A B c : ℝ) : Continuous (gau A B c) := by
  unfold gau; fun_prop

/-- **Form of (E3)**: the Riemann sum of the Gaussian. -/
theorem gau_sum {A B c R a : ℝ} (N : ℕ) (hA : 0 ≤ A) (hB : 0 < B) (hR : 0 ≤ R)
    (ha1 : c - R - 1 ≤ a) (ha2 : a ≤ c - R) (hb1 : c + R ≤ a + N) (hb2 : a + N ≤ c + R + 1) :
    |∑ i ∈ Finset.range N, gau A B c (a + i) - A * Real.sqrt (Real.pi / B)|
      ≤ N * (A * B * (2 * R + 2)) +
        A * Real.sqrt (2 * Real.pi / B) * Real.exp (-(B * R ^ 2 / 2)) := by
  set g : ℝ → ℝ := gau A B c with hgdef
  have hgc : Continuous g := gau_continuous A B c
  -- step 1: the sum and the integral over [a, a+N]
  have hsumint : ∑ i ∈ Finset.range N, ∫ t in (a + (i : ℕ))..(a + ((i + 1 : ℕ) : ℝ)), g t
      = ∫ t in a..(a + N), g t := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := g)
      (μ := MeasureTheory.volume) (a := fun i : ℕ => a + (i : ℝ)) (n := N)
      (fun k _ => hgc.intervalIntegrable _ _)
    simpa using h
  have hpt : ∀ i ∈ Finset.range N,
      |g (a + i) - ∫ t in (a + (i : ℕ))..(a + ((i + 1 : ℕ) : ℝ)), g t| ≤ A * B * (2 * R + 2) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
    have hconst : g (a + i) = ∫ t in (a + (i : ℕ))..(a + ((i + 1 : ℕ) : ℝ)), g (a + i) := by
      rw [intervalIntegral.integral_const]; push_cast; simp
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const
      (hgc.intervalIntegrable _ _)]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a + (i : ℕ)) (b := a + ((i + 1 : ℕ) : ℝ)) (C := A * B * (2 * R + 2))
      (f := fun t => g (a + i) - g t) ?_
    · rw [Real.norm_eq_abs] at hb
      refine le_trans hb (le_of_eq ?_)
      push_cast
      rw [show a + ((i : ℝ) + 1) - (a + i) = 1 by ring, abs_one, mul_one]
    · intro t ht
      rw [Set.uIoc_of_le (by push_cast; linarith)] at ht
      obtain ⟨ht1, ht2⟩ := ht
      push_cast at ht1 ht2
      rw [Real.norm_eq_abs]
      refine le_trans (gau_sub_le hA hB.le c _ _) ?_
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA hB.le)
      have e : (a + i - c) ^ 2 - (t - c) ^ 2 = (a + i - t) * (a + i + t - 2 * c) := by ring
      rw [e, abs_mul]
      have h1 : |a + i - t| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have h2 : |a + i + t - 2 * c| ≤ 2 * R + 2 := by rw [abs_le]; constructor <;> linarith
      calc |a + i - t| * |a + i + t - 2 * c| ≤ 1 * (2 * R + 2) :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = 2 * R + 2 := one_mul _
  have hstep1 : |∑ i ∈ Finset.range N, g (a + i) - ∫ t in a..(a + N), g t|
      ≤ N * (A * B * (2 * R + 2)) := by
    rw [← hsumint, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- step 2: the whole integral and the part outside the window
  have hint : MeasureTheory.Integrable g := by
    have h := (integrable_exp_neg_mul_sq hB).comp_sub_right c
    exact (h.const_mul A).congr (Filter.Eventually.of_forall fun t => by simp [hgdef, gau])
  have hB2 : 0 < B / 2 := by positivity
  set h2 : ℝ → ℝ := fun t => A * Real.exp (-(B * R ^ 2 / 2)) * Real.exp (-(B / 2) * (t - c) ^ 2)
    with hh2
  have hint2 : MeasureTheory.Integrable h2 := by
    have h := (integrable_exp_neg_mul_sq hB2).comp_sub_right c
    exact (h.const_mul (A * Real.exp (-(B * R ^ 2 / 2)))).congr
      (Filter.Eventually.of_forall fun t => by simp [hh2])
  have hfull : ∫ t, g t = A * Real.sqrt (Real.pi / B) := by
    simp only [hgdef, gau]
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_sub_right_eq_self (fun t => Real.exp (-B * t ^ 2)) c,
      integral_gaussian]
  have hfull2 : ∫ t, h2 t = A * Real.sqrt (2 * Real.pi / B) * Real.exp (-(B * R ^ 2 / 2)) := by
    simp only [hh2]
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_sub_right_eq_self (fun t => Real.exp (-(B / 2) * t ^ 2)) c,
      integral_gaussian]
    rw [show Real.pi / (B / 2) = 2 * Real.pi / B by field_simp]
    ring
  have hN0 : a ≤ a + N := by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
                             linarith
  have hsplit := MeasureTheory.integral_add_compl (μ := MeasureTheory.volume)
    (measurableSet_Ioc (a := a) (b := a + N)) hint
  rw [← intervalIntegral.integral_of_le hN0] at hsplit
  have hc0 : 0 ≤ ∫ t in (Set.Ioc a (a + N))ᶜ, g t :=
    MeasureTheory.setIntegral_nonneg (measurableSet_Ioc.compl) fun t _ => gau_nonneg hA _ _ _
  have hc1 : ∫ t in (Set.Ioc a (a + N))ᶜ, g t ≤ ∫ t in (Set.Ioc a (a + N))ᶜ, h2 t := by
    refine MeasureTheory.setIntegral_mono_on hint.integrableOn hint2.integrableOn
      measurableSet_Ioc.compl fun t ht => ?_
    rw [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
    have hR2 : R ^ 2 ≤ (t - c) ^ 2 := by
      rcases ht with ht | ht
      · nlinarith
      · nlinarith
    simp only [hgdef, hh2, gau]
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    nlinarith
  have hc2 : ∫ t in (Set.Ioc a (a + N))ᶜ, h2 t ≤ ∫ t, h2 t :=
    MeasureTheory.setIntegral_le_integral hint2
      (Filter.Eventually.of_forall fun t => by
        simp only [hh2, Pi.zero_apply]; positivity)
  have hstep2 : |(∫ t in a..(a + N), g t) - A * Real.sqrt (Real.pi / B)|
      ≤ A * Real.sqrt (2 * Real.pi / B) * Real.exp (-(B * R ^ 2 / 2)) := by
    have key := hsplit.trans hfull
    rw [abs_le]
    constructor <;> linarith
  calc |∑ i ∈ Finset.range N, g (a + i) - A * Real.sqrt (Real.pi / B)|
      = |(∑ i ∈ Finset.range N, g (a + i) - ∫ t in a..(a + N), g t)
          + ((∫ t in a..(a + N), g t) - A * Real.sqrt (Real.pi / B))| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add hstep1 hstep2

/-- The Gaussian weight truncated to the window `[a, a+N)` (on `ℤ`). -/
noncomputable def wt (A B c : ℝ) (a : ℤ) (N : ℕ) (n : ℤ) : ℝ :=
  if a ≤ n ∧ n < a + N then gau A B c n else 0

theorem wt_nonneg {A : ℝ} (hA : 0 ≤ A) (B c : ℝ) (a : ℤ) (N : ℕ) (n : ℤ) : 0 ≤ wt A B c a N n := by
  unfold wt; split_ifs
  · exact gau_nonneg hA _ _ _
  · exact le_rfl

theorem wt_out (A B c : ℝ) (a : ℤ) (N : ℕ) (n : ℤ) (hn : n ∉ Finset.Ico a (a + N)) :
    wt A B c a N n = 0 := by
  unfold wt
  rw [Finset.mem_Ico] at hn
  rw [if_neg hn]

/-- **Form of (E2)**: the variation of the truncated Gaussian weight. -/
theorem wt_var {A B c R : ℝ} {a : ℤ} {N : ℕ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 1 ≤ R)
    (ha1 : c - R - 1 ≤ a) (ha2 : (a : ℝ) ≤ c - R) (hb1 : c + R ≤ (a : ℝ) + N)
    (hb2 : (a : ℝ) + N ≤ c + R + 1) :
    ∑ n ∈ Finset.Ico (a - 1) (a + N), |wt A B c a N (n + 1) - wt A B c a N n|
      ≤ ((N : ℝ) + 1) * (A * B * (2 * R + 1) + A * Real.exp (-(B * (R - 1) ^ 2))) := by
  have hE : 0 ≤ A * Real.exp (-(B * (R - 1) ^ 2)) := mul_nonneg hA (Real.exp_pos _).le
  have hAB : 0 ≤ A * B * (2 * R + 1) := by
    have : 0 ≤ 2 * R + 1 := by linarith
    positivity
  -- values at the endpoints
  have hedge : ∀ t : ℝ, (R - 1) ^ 2 ≤ (t - c) ^ 2 → gau A B c t ≤ A * Real.exp (-(B * (R - 1) ^ 2)) := by
    intro t ht
    unfold gau
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpt : ∀ n ∈ Finset.Ico (a - 1) (a + N),
      |wt A B c a N (n + 1) - wt A B c a N n|
        ≤ A * B * (2 * R + 1) + A * Real.exp (-(B * (R - 1) ^ 2)) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hnR : ((n : ℤ) : ℝ) + 1 = ((n + 1 : ℤ) : ℝ) := by push_cast; ring
    unfold wt
    split_ifs with h1 h2 h2
    · -- both in the window
      have hn1 : (a : ℝ) ≤ n := by exact_mod_cast h2.1
      have hn2 : (n : ℝ) + 1 < a + N := by
        have := h1.2
        have : ((n + 1 : ℤ) : ℝ) < ((a + N : ℤ) : ℝ) := by exact_mod_cast this
        push_cast at this; linarith
      refine le_trans (gau_sub_le hA hB c _ _) ?_
      have e : (((n + 1 : ℤ) : ℝ) - c) ^ 2 - ((n : ℝ) - c) ^ 2 = 2 * ((n : ℝ) - c) + 1 := by
        push_cast; ring
      rw [e]
      have : |2 * ((n : ℝ) - c) + 1| ≤ 2 * R + 1 := by
        rw [abs_le]; constructor <;> linarith
      have := mul_le_mul_of_nonneg_left this (mul_nonneg hA hB)
      linarith
    · -- `n + 1 = a` (left end)
      have hn1 : ((n + 1 : ℤ) : ℝ) ≤ a := by
        have : n < a := by
          by_contra hc
          exact h2 ⟨by omega, by omega⟩
        have : n + 1 ≤ a := by omega
        exact_mod_cast this
      rw [sub_zero, abs_of_nonneg (gau_nonneg hA _ _ _)]
      refine le_trans (hedge _ ?_) (le_add_of_nonneg_left hAB)
      have h3 : ((n + 1 : ℤ) : ℝ) - c ≤ -R := by linarith
      nlinarith
    · -- `n = a + N - 1` (right end)
      have hn1 : (a : ℝ) + N ≤ ((n + 1 : ℤ) : ℝ) := by
        have : a + N ≤ n + 1 := by
          by_contra hc
          exact h1 ⟨by omega, by omega⟩
        exact_mod_cast this
      push_cast at hn1
      rw [zero_sub, abs_neg, abs_of_nonneg (gau_nonneg hA _ _ _)]
      refine le_trans (hedge _ ?_) (le_add_of_nonneg_left hAB)
      have h3 : R - 1 ≤ (n : ℝ) - c := by linarith
      nlinarith
    · rw [sub_zero, abs_zero]
      exact add_nonneg hAB hE
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_const, nsmul_eq_mul, Int.card_Ico]
  apply le_of_eq
  congr 1
  have : a + N - (a - 1) = (N : ℤ) + 1 := by ring
  rw [this]
  have : ((N : ℤ) + 1).toNat = N + 1 := by omega
  rw [this]
  push_cast; ring

end DKernAux

end ND

end GGMCollatz
