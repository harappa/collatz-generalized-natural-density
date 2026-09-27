import GGMCollatz.NatDen.SumMixB.Ratio

/-!
# The bound for the reduced quantity of (SUMMIX b)

`Σ_σ P(s_m = σ) |P(s_{n-m} = s - σ) - P(s_n = s)| ≤ K √(m log n / n) P(s_n = s)` (`reduced_bound`).

Split σ into typical `|σ - μm| < √m log n` and atypical.

* Typical: the pointwise bound `point_core` and the two-sided exponential moment `coshMoment` (`1 + z + z² ≤ 2(e^z + e^{-z})`).
* Atypical: `|·| ≤ 1`, the tail `tail_le` (`≤ 4 e^{-L²/320000}`) and the local limit lower bound `P(s_n = s) ≥ g_n/2` give
  `≤ t · P(s_n = s)`.
* Small `n`: the trivial upper bound `reduced_le_two` and `t ≥ √(log 2 / N)`.

The conditions for large `n` are collected into two: `log n ≥ L₀` and `log⁶ n ≤ δ n^{1/10}` (`isLittleO_log_rpow_rpow_atTop`).
-/

open scoped ENNReal
open Filter

namespace GGMCollatz

namespace ND

namespace SumMixBAux

/-! ### Asymptotic tools -/

/-- `log n` diverges to ∞. -/
theorem eventually_log_ge (L₀ : ℝ) : ∀ᶠ n : ℕ in atTop, L₀ ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop L₀

/-- `log⁶ n = o(n^{1/10})`. -/
theorem eventually_log_six_le {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, Real.log n ^ 6 ≤ δ * (n : ℝ) ^ (1 / 10 : ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop (6 : ℝ) (by norm_num : (0 : ℝ) < 1 / 10)).bound hδ
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h, eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1'
  have e1 : ‖Real.log n ^ (6 : ℝ)‖ = Real.log n ^ 6 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog _)]
    exact_mod_cast Real.rpow_natCast (Real.log n) 6
  have e2 : ‖(n : ℝ) ^ (1 / 10 : ℝ)‖ = (n : ℝ) ^ (1 / 10 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  rw [e1, e2] at hn
  exact hn

/-! ### Power computations -/

theorem rpow_nine_tenths_mul {n : ℝ} (hn : 0 < n) :
    n ^ (9 / 10 : ℝ) * n ^ (1 / 10 : ℝ) = n := by
  rw [← Real.rpow_add hn]; norm_num

theorem rpow_three_fifths_sq {n : ℝ} (hn : 0 < n) :
    (n ^ (3 / 5 : ℝ)) ^ 2 = n * n ^ (1 / 5 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le,
    show n * n ^ (1 / 5 : ℝ) = n ^ (1 : ℝ) * n ^ (1 / 5 : ℝ) by rw [Real.rpow_one],
    ← Real.rpow_add hn]
  norm_num

theorem rpow_tenth_le_fifth {n : ℝ} (hn : 1 ≤ n) : n ^ (1 / 10 : ℝ) ≤ n ^ (1 / 5 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le hn (by norm_num)

theorem rpow_fifth_le {n : ℝ} (hn : 1 ≤ n) : n ^ (1 / 5 : ℝ) ≤ n := by
  conv_rhs => rw [← Real.rpow_one n]
  exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num)

/-- Range of the local limit theorem (denominator): if `|x| ≤ C n a` and `4(C+1)² L ≤ n^{1/5}`, then `|x| ≤ n^{3/5}`. -/
theorem range_n {n a L C x : ℝ} (hn : 0 < n) (ha : 0 ≤ a) (hna : n * a ^ 2 = L) (hC : 0 ≤ C)
    (hx : |x| ≤ C * n * a) (h5 : 4 * (C + 1) ^ 2 * L ≤ n ^ (1 / 5 : ℝ)) :
    |x| ≤ n ^ (3 / 5 : ℝ) := by
  refine hx.trans ((sq_le_sq₀ (by positivity) (Real.rpow_nonneg hn.le _)).mp ?_)
  rw [rpow_three_fifths_sq hn, show (C * n * a) ^ 2 = C ^ 2 * n * (n * a ^ 2) by ring, hna]
  have hL : 0 ≤ L := by rw [← hna]; positivity
  have : C ^ 2 * L ≤ n ^ (1 / 5 : ℝ) := by
    have : C ^ 2 ≤ 4 * (C + 1) ^ 2 := by nlinarith
    nlinarith
  calc C ^ 2 * n * L = n * (C ^ 2 * L) := by ring
    _ ≤ n * n ^ (1 / 5 : ℝ) := mul_le_mul_of_nonneg_left this hn.le

/-- Range of the local limit theorem (numerator): if `|w| ≤ (C+1) n a`, `n ≤ 2k`, `4(C+1)² L ≤ n^{1/5}`, then `|w| ≤ k^{3/5}`. -/
theorem range_k {n k a L C w : ℝ} (hn : 0 < n) (hk2 : n ≤ 2 * k) (ha : 0 ≤ a)
    (hna : n * a ^ 2 = L) (hC : 0 ≤ C) (hw : |w| ≤ (C + 1) * n * a)
    (h5 : 4 * (C + 1) ^ 2 * L ≤ n ^ (1 / 5 : ℝ)) :
    |w| ≤ k ^ (3 / 5 : ℝ) := by
  have hL : 0 ≤ L := by rw [← hna]; positivity
  have hk : 0 < k := by linarith
  -- `k^{3/5} ≥ (n/2)^{3/5} = n^{3/5}/2^{3/5} ≥ n^{3/5}/2`
  have h1 : (n / 2) ^ (3 / 5 : ℝ) ≤ k ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have h2 : (2 : ℝ) ^ (3 / 5 : ℝ) ≤ 2 := by
    conv_rhs => rw [← Real.rpow_one (2 : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h2' : 0 < (2 : ℝ) ^ (3 / 5 : ℝ) := by positivity
  have h3 : n ^ (3 / 5 : ℝ) / 2 ≤ (n / 2) ^ (3 / 5 : ℝ) := by
    rw [Real.div_rpow hn.le (by norm_num)]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hn.le _) h2' h2
  refine hw.trans (le_trans ?_ (h3.trans h1))
  refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
  rw [div_pow, rpow_three_fifths_sq hn,
    show ((C + 1) * n * a) ^ 2 = (C + 1) ^ 2 * n * (n * a ^ 2) by ring, hna]
  rw [le_div_iff₀ (by norm_num)]
  calc (C + 1) ^ 2 * n * L * 2 ^ 2 = n * (4 * (C + 1) ^ 2 * L) := by ring
    _ ≤ n * n ^ (1 / 5 : ℝ) := mul_le_mul_of_nonneg_left h5 hn.le

/-- `√(nL) = n √(L/n)`. -/
theorem sqrt_mul_log_eq {n L : ℝ} (hn : 0 < n) :
    Real.sqrt (n * L) = n * Real.sqrt (L / n) := by
  rw [show n * L = n ^ 2 * (L / n) by field_simp, Real.sqrt_mul (by positivity),
    Real.sqrt_sq hn.le]

/-- `√(mL/n) = √m √(L/n)`. -/
theorem sqrt_t_eq {m n L : ℝ} (hm : 0 ≤ m) :
    Real.sqrt (m * L / n) = Real.sqrt m * Real.sqrt (L / n) := by
  rw [mul_div_assoc, Real.sqrt_mul hm]

/-- `√m L ≤ n a` (`mL ≤ n`). -/
theorem smL_le_na {n m L a sm : ℝ} (hn : 0 < n) (hL1 : 1 ≤ L) (ha : 0 ≤ a)
    (hna : n * a ^ 2 = L) (hsm : 0 ≤ sm) (hsm2 : sm ^ 2 = m) (hmL : m * L ≤ n) :
    sm * L ≤ n * a := by
  refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
  rw [mul_pow, mul_pow, hsm2, show n ^ 2 * a ^ 2 = n * (n * a ^ 2) by ring, hna]
  have : m * L * L ≤ n * L := mul_le_mul_of_nonneg_right hmL (by linarith)
  calc m * L ^ 2 = m * L * L := by ring
    _ ≤ n * L := this

/-- Splitting a sum: if `f ≤ g` on `P` and `f ≤ h` outside (all nonnegative), then `Σ f ≤ Σ g + Σ h`. -/
theorem tsum_le_of_split {f g h : ℕ → ℝ} (P : ℕ → Prop) [DecidablePred P]
    (hf0 : ∀ σ, 0 ≤ f σ) (hg0 : ∀ σ, 0 ≤ g σ) (hh0 : ∀ σ, 0 ≤ h σ)
    (hg : Summable g) (hh : Summable h) (h1 : ∀ σ, P σ → f σ ≤ g σ)
    (h2 : ∀ σ, ¬ P σ → f σ ≤ h σ) :
    ∑' σ, f σ ≤ ∑' σ, g σ + ∑' σ, h σ := by
  have hle : ∀ σ, f σ ≤ g σ + h σ := by
    intro σ
    by_cases hP : P σ
    · linarith [h1 σ hP, hh0 σ]
    · linarith [h2 σ hP, hg0 σ]
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hle (hg.add hh)
  rw [← hg.tsum_add hh]
  exact hf.tsum_le_tsum hle (hg.add hh)

/-- Lower bound for the local limit denominator: `P(s_n = s) ≥ g_n/2`. -/
theorem gn_le_two_nb {CL gn NBn εn : ℝ} (hgn0 : 0 ≤ gn) (hNBn : |NBn - gn| ≤ CL * gn * εn)
    (hε : CL * εn ≤ 1 / 2) : gn ≤ 2 * NBn := by
  have h1 := (abs_le.mp hNBn).1
  have h2 : CL * gn * εn ≤ gn / 2 := by
    calc CL * gn * εn = gn * (CL * εn) := by ring
      _ ≤ gn * (1 / 2) := mul_le_mul_of_nonneg_left hε hgn0
      _ = gn / 2 := by ring
  linarith

/-- Lower bound for `t · P(s_n = s)`: from `t ≥ n^{-1/2}`, `P(s_n = s) ≥ g_n/2`, `|x| ≤ C n a`,
`t · P(s_n = s) ≥ (P/2) e^{-(1 + C²/(2v)) L}` (`P = (2πv)^{-1/2}`, `n = e^L`). -/
theorem tb_lower {v n L a t x b C : ℝ} (hv : 0 < v) (hn : 0 < n) (hL : Real.log n = L)
    (hna : n * a ^ 2 = L) (hx : |x| ≤ C * n * a) (ht : n ^ (-(1 / 2 : ℝ)) ≤ t)
    (hb : gaussR v n x ≤ 2 * b) :
    (2 * Real.pi * v) ^ (-(1 / 2 : ℝ)) / 2 * Real.exp (-(1 + C ^ 2 / (2 * v)) * L) ≤ t * b := by
  have hP : 0 < (2 * Real.pi * v) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  have hr : 0 < n ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hn _
  have hg : gaussR v n x
      = (2 * Real.pi * v) ^ (-(1 / 2 : ℝ)) * n ^ (-(1 / 2 : ℝ)) * Real.exp (-x ^ 2 / (2 * v * n)) := by
    unfold gaussR
    rw [Real.mul_rpow (by positivity) hn.le]
  have hx2 : x ^ 2 ≤ C ^ 2 * n * L := by
    have := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rw [sq_abs, show (C * n * a) ^ 2 = C ^ 2 * n * (n * a ^ 2) by ring, hna] at this
    exact this
  have hE : Real.exp (-(C ^ 2 / (2 * v)) * L) ≤ Real.exp (-x ^ 2 / (2 * v * n)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_mul, neg_le_neg_iff, div_le_iff₀ (by positivity)]
    calc x ^ 2 ≤ C ^ 2 * n * L := hx2
      _ = C ^ 2 / (2 * v) * L * (2 * v * n) := by field_simp
  have hsq : n ^ (-(1 / 2 : ℝ)) * n ^ (-(1 / 2 : ℝ)) = Real.exp (-L) := by
    rw [← sq, rpow_neg_half_sq hn, ← hL, Real.exp_neg, Real.exp_log hn]
  have hb0 : 0 ≤ b := by
    have := gaussR_nonneg v n x hv.le hn.le
    linarith
  calc (2 * Real.pi * v) ^ (-(1 / 2 : ℝ)) / 2 * Real.exp (-(1 + C ^ 2 / (2 * v)) * L)
      = (2 * Real.pi * v) ^ (-(1 / 2 : ℝ)) / 2 *
          (n ^ (-(1 / 2 : ℝ)) * n ^ (-(1 / 2 : ℝ))) * Real.exp (-(C ^ 2 / (2 * v)) * L) := by
        rw [hsq, mul_assoc ((2 * Real.pi * v) ^ (-(1 / 2 : ℝ)) / 2), ← Real.exp_add]
        congr 2
        ring
    _ ≤ (2 * Real.pi * v) ^ (-(1 / 2 : ℝ)) / 2 *
          (n ^ (-(1 / 2 : ℝ)) * n ^ (-(1 / 2 : ℝ))) * Real.exp (-x ^ 2 / (2 * v * n)) := by
        gcongr
    _ = n ^ (-(1 / 2 : ℝ)) * (gaussR v n x / 2) := by rw [hg]; ring
    _ ≤ t * (gaussR v n x / 2) :=
        mul_le_mul_of_nonneg_right ht (by have := gaussR_nonneg v n x hv.le hn.le; linarith)
    _ ≤ t * b := by
        apply mul_le_mul_of_nonneg_left (by linarith) (le_trans hr.le ht)

/-- Tail bound: if `√m ≥ L ≥ 1` and `m ≥ 1`, then `2 G_{1+m}(√m L / 400) ≤ 4 e^{-L²/320000}`. -/
theorem gweight_tail_le {m sm L : ℝ} (hm1 : 1 ≤ m) (hsm : 0 ≤ sm) (hsm2 : sm ^ 2 = m)
    (hL1 : 1 ≤ L) (hLs : L ≤ sm) :
    2 * Gweight (1 + m) (1 / 400 * (sm * L)) ≤ 4 * Real.exp (-(L ^ 2 / 320000)) := by
  unfold Gweight
  have h1 : Real.exp (-(1 / 400 * (sm * L)) ^ 2 / (1 + m)) ≤ Real.exp (-(L ^ 2 / 320000)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by linarith),
      show (1 / 400 * (sm * L)) ^ 2 = sm ^ 2 * L ^ 2 / 160000 by ring, hsm2]
    have : 0 ≤ L ^ 2 := sq_nonneg L
    nlinarith
  have h2 : Real.exp (-|1 / 400 * (sm * L)|) ≤ Real.exp (-(L ^ 2 / 320000)) := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg (by positivity), neg_le_neg_iff]
    have : L * L ≤ sm * L := mul_le_mul_of_nonneg_right hLs (by linarith)
    nlinarith
  linarith

/-- An exponential inequality: if `L ≥ 320000(B + D)`, `D > 0`, `L ≥ 1`, then `D ≤ e^{L²/320000 - BL}`. -/
theorem exp_quad_ge {L B D : ℝ} (hD : 0 < D) (hL1 : 1 ≤ L)
    (hL : 320000 * (B + D) ≤ L) : D ≤ Real.exp (L ^ 2 / 320000 - B * L) := by
  have h1 : D ≤ L ^ 2 / 320000 - B * L := by
    have : D ≤ L / 320000 - B := by linarith
    have h2 : L / 320000 - B ≤ L * (L / 320000 - B) := le_mul_of_one_le_left (by linarith) hL1
    calc D ≤ L * (L / 320000 - B) := this.trans h2
      _ = L ^ 2 / 320000 - B * L := by ring
  have := Real.add_one_le_exp (L ^ 2 / 320000 - B * L)
  linarith

end SumMixBAux

end ND

end GGMCollatz
