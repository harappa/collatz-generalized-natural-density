import GGMCollatz.Tao.Sec6.Sep

/-!
# Tails of the exceptional events (Chernoff-type estimates used for `P(Ē_n) ≲ n^{-A}` in GGM §5 Step 1)

GGM §5 Step 1 bounds the probability of deviations of `𝒢_{i,j}` by the Chernoff-type tail of GGM (2.2).
Here only the two one-sided tails that we need are proved, directly, without relying on the general
probability toolkit. Their role corresponds to the family `g1`, `g2`, `g3` in `Sec6/MixingError.lean` of
gotrevor/tao-collatz (Apache-2.0, commit 15efca2), but the proofs in this file are not derived from there,
and no Gaussian weight (tao-collatz's `Gweight`) is used. Written for the GGM family (`G(μ)`,
`μ = p/(p-1)`):

* `sufSum_lower_tail`: **lower tail of the suffix sum** (linear deviation): if `s < μ = p/(p-1)`, there is
  `t > 0` such that for all `r ≤ n` and real `x`, `P(sum of the last r entries of 𝒢 ≤ s r - x) ≤ e^{-t x}`.
* `coord_upper_tail`: **upper tail of a single component**: `P(𝒢_i > y) ≤ p e^{-y log p}` (`y ≥ 0`).

Both follow from "on an i.i.d. vector, the expectation of a product of componentwise functions is the
product of the expectations" (`Mix.tsum_iid_mul_prod`, in `ℝ≥0∞` with no summability condition) and
Markov's inequality.
-/

open scoped BigOperators ENNReal

namespace GGMCollatz

namespace Mix

/-- **Expectation of a product on an i.i.d. vector**: `E[∏_i g_i(v_i)] = ∏_i E[g_i]` (`ℝ≥0∞`). -/
theorem tsum_iid_mul_prod {α : Type*} (μ : PMF α) : ∀ (n : ℕ) (g : Fin n → α → ℝ≥0∞),
    ∑' v : Fin n → α, (μ.iid n) v * ∏ i, g i (v i) = ∏ i, ∑' x, μ x * g i x := by
  intro n
  induction n with
  | zero =>
    intro g
    rw [PMF.tsum_iid_zero_mul μ (fun v => ∏ i, g i (v i))]
    simp
  | succ n ih =>
    intro g
    rw [PMF.tsum_iid_succ_mul μ n (fun v => ∏ i, g i (v i)), Fin.prod_univ_succ]
    have hinner : ∀ a : α, (∑' w : Fin n → α, (μ.iid n) w * ∏ i : Fin (n + 1),
        g i ((Fin.cons a w : Fin (n + 1) → α) i))
        = g 0 a * ∏ i : Fin n, ∑' x, μ x * g i.succ x := by
      intro a
      rw [← ih (fun i => g i.succ), ← ENNReal.tsum_mul_left]
      refine tsum_congr (fun w => ?_)
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring
    simp_rw [hinner]
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr (fun a => ?_)
    ring

/-- Shift a sum with the terms up to index `m` removed: `∑' a, [m < a] g a = ∑' b, g (b + m + 1)`. -/
theorem tsum_ite_lt_eq_shift : ∀ (m : ℕ) (g : ℕ → ℝ≥0∞),
    ∑' a : ℕ, (if m < a then g a else 0) = ∑' b : ℕ, g (b + m + 1) := by
  intro m
  induction m with
  | zero =>
    intro g
    rw [← tsum_ite_zero_eq_succ g]
    refine tsum_congr (fun a => ?_)
    by_cases h : a = 0
    · simp [h]
    · rw [if_pos (Nat.pos_of_ne_zero h), if_neg h]
  | succ m ih =>
    intro g
    have h0 : ∑' a : ℕ, (if m + 1 < a then g a else 0)
        = ∑' a : ℕ, (if a = 0 then 0 else (if m + 1 < a then g a else 0)) := by
      refine tsum_congr (fun a => ?_)
      by_cases h : a = 0
      · simp [h]
      · rw [if_neg h]
    rw [h0, tsum_ite_zero_eq_succ (fun a => if m + 1 < a then g a else 0)]
    have h1 : ∀ n : ℕ, (if m + 1 < n + 1 then g (n + 1) else 0)
        = (if m < n then (fun k => g (k + 1)) n else 0) := by
      intro n
      by_cases h : m < n
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    simp_rw [h1]
    rw [ih (fun k => g (k + 1))]
    refine tsum_congr (fun b => ?_)
    congr 1

/-- If `0 ≤ x ≤ 1` then `e^x ≤ 1 + x + x²`. -/
theorem exp_le_one_add_add_sq {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := x) (by rw [abs_of_nonneg h0]; exact h1)
  have := (abs_le.mp h).2
  linarith

/-- If `0 ≤ y < 1` then `∑_{a ≥ 1} y^a = y / (1 - y)`. -/
theorem hasSum_geometric_pos {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) :
    HasSum (fun a : ℕ => if a = 0 then (0 : ℝ) else y ^ a) (y / (1 - y)) := by
  have hg := hasSum_geometric_of_lt_one h0 h1
  have hd : HasSum (fun a : ℕ => if a = 0 then (1 : ℝ) else 0) 1 := by
    have := hasSum_ite_eq (0 : ℕ) (1 : ℝ)
    convert this using 1
  have hs := hg.sub hd
  have hfun : (fun a : ℕ => y ^ a - (if a = 0 then (1 : ℝ) else 0))
      = (fun a : ℕ => if a = 0 then (0 : ℝ) else y ^ a) := by
    funext a
    by_cases h : a = 0
    · simp [h]
    · simp [h]
  rw [hfun] at hs
  have hne : (1 : ℝ) - y ≠ 0 := by linarith
  have hval : (1 - y)⁻¹ - 1 = y / (1 - y) := by
    rw [eq_div_iff hne, sub_mul, inv_mul_cancel₀ hne]; ring
  rwa [hval] at hs

end Mix

namespace Family

variable (F : Family)

/-! ### Suffix sums -/

/-- The sum of the last `r` components (tao-collatz's `sufSum`). -/
def sufSum {n : ℕ} (a : Fin n → ℕ) (r : ℕ) : ℕ := pre a n - pre a (n - r)

/-- `pre a m = ∑_{i < m} a_i` (as a sum over `Fin n` with an indicator, `m ≤ n`). -/
theorem pre_eq_sum_ite_lt {n : ℕ} (a : Fin n → ℕ) {m : ℕ} (hm : m ≤ n) :
    pre a m = ∑ i : Fin n, if (i : ℕ) < m then a i else 0 := by
  unfold pre
  set f : ℕ → ℕ := fun i => if h : i < n then a ⟨i, h⟩ else 0 with hf
  have h1 : ∑ i : Fin n, (if (i : ℕ) < m then a i else 0)
      = ∑ i ∈ Finset.range n, if i < m then f i else 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => if i < m then f i else 0) n]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hf, dif_pos i.isLt]
  rw [h1, ← Finset.sum_range_add_sum_Ico _ hm, Finset.sum_eq_zero (s := Finset.Ico m n)
    (fun i hi => by rw [if_neg (by rw [Finset.mem_Ico] at hi; omega)]), add_zero]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [if_pos (Finset.mem_range.mp hi)]

/-- `sufSum a r = ∑_{i ≥ n - r} a_i`. -/
theorem sufSum_eq_sum_ite {n : ℕ} (a : Fin n → ℕ) (r : ℕ) :
    sufSum a r = ∑ i : Fin n, if n - r ≤ (i : ℕ) then a i else 0 := by
  unfold sufSum
  rw [pre_eq_sum_ite_lt a (le_refl n), pre_eq_sum_ite_lt a (Nat.sub_le n r)]
  have hsplit : (∑ i : Fin n, if (i : ℕ) < n then a i else 0)
      = (∑ i : Fin n, if (i : ℕ) < n - r then a i else 0)
        + ∑ i : Fin n, if n - r ≤ (i : ℕ) then a i else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [if_pos i.isLt]
    by_cases h : (i : ℕ) < n - r
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  omega

/-- There are `r` indices among the last `r`. -/
theorem card_filter_last {n r : ℕ} (hr : r ≤ n) :
    (Finset.univ.filter (fun i : Fin n => n - r ≤ (i : ℕ))).card = r := by
  have h := Fin.card_filter_val_lt (n := n) (m := n - r)
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n => (i : ℕ) < n - r)
  rw [Finset.card_univ, Fintype.card_fin, h, min_eq_right (Nat.sub_le n r)] at hsum
  have heq : (Finset.univ.filter (fun i : Fin n => n - r ≤ (i : ℕ)))
      = Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) < n - r) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  rw [heq]
  omega

/-! ### The valuation component of the one-step law and moments of `G(μ)` -/

/-- The expectation of a function of the valuation component of the one-step law is the expectation under `G(μ)`. -/
theorem stepLaw_tsum_fst (g : ℕ → ℝ≥0∞) :
    ∑' y : ℕ × ℕ, stepLaw F.p y * g y.1 = ∑' a, geomP F.p a * g a := by
  rw [← stepLaw_map_fst F.p, PMF.tsum_map_mul]

/-- For positive `s` smaller than `μ = p/(p-1)`, there is `t > 0` with `E[e^{t(s - G)}] ≤ 1`
(`G ~ G(μ)`). -/
theorem geomP_mgf_lower (s : ℝ) (hs0 : 0 < s) (hs : s < (F.p : ℝ) / ((F.p : ℝ) - 1)) :
    ∃ t : ℝ, 0 < t ∧
      ∑' a, geomP F.p a * ENNReal.ofReal (Real.exp (t * (s - a))) ≤ 1 := by
  have hp2 : (2 : ℝ) ≤ (F.p : ℝ) := by exact_mod_cast F.two_le_p
  have hp1 : (0 : ℝ) < (F.p : ℝ) - 1 := by linarith
  have hgap : 0 < (F.p : ℝ) - ((F.p : ℝ) - 1) * s := by
    have := (lt_div_iff₀ hp1).mp hs
    linarith
  set t : ℝ := min (1 / s) (((F.p : ℝ) - ((F.p : ℝ) - 1) * s) / (((F.p : ℝ) - 1) * s ^ 2))
    with htdef
  have ht0 : 0 < t := lt_min (by positivity) (by positivity)
  have hts : t * s ≤ 1 := by
    have := min_le_left (1 / s) (((F.p : ℝ) - ((F.p : ℝ) - 1) * s) / (((F.p : ℝ) - 1) * s ^ 2))
    rw [← htdef] at this
    calc t * s ≤ 1 / s * s := mul_le_mul_of_nonneg_right this hs0.le
      _ = 1 := by field_simp
  have ht2 : t * (((F.p : ℝ) - 1) * s ^ 2) ≤ (F.p : ℝ) - ((F.p : ℝ) - 1) * s := by
    have := min_le_right (1 / s) (((F.p : ℝ) - ((F.p : ℝ) - 1) * s) / (((F.p : ℝ) - 1) * s ^ 2))
    rw [← htdef] at this
    rwa [le_div_iff₀ (by positivity)] at this
  refine ⟨t, ht0, ?_⟩
  set y : ℝ := Real.exp (-t) / (F.p : ℝ) with hydef
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y < 1 := by
    rw [hydef, div_lt_one (by linarith)]
    have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  -- the terms in real form
  have hterm : ∀ a : ℕ, (geomP F.p a).toReal * Real.exp (t * (s - a))
      = ((F.p : ℝ) - 1) * Real.exp (t * s) * (if a = 0 then 0 else y ^ a) := by
    intro a
    rw [geomP_toReal F.two_le_p]
    by_cases h : a = 0
    · simp [h]
    · rw [if_neg h, if_neg h, hydef, div_pow, mul_sub, Real.exp_sub,
        show t * (a : ℝ) = (a : ℝ) * t by ring, Real.exp_nat_mul, inv_pow]
      rw [show Real.exp (-t) ^ a = (Real.exp t ^ a)⁻¹ by
        rw [Real.exp_neg, inv_pow]]
      have hpa : (F.p : ℝ) ^ a ≠ 0 := pow_ne_zero _ (by linarith)
      have hea : Real.exp t ^ a ≠ 0 := pow_ne_zero _ (Real.exp_pos _).ne'
      field_simp
  have hHas : HasSum (fun a : ℕ => (geomP F.p a).toReal * Real.exp (t * (s - a)))
      (((F.p : ℝ) - 1) * Real.exp (t * s) * (y / (1 - y))) := by
    simp_rw [hterm]
    exact (Mix.hasSum_geometric_pos hy0 hy1).mul_left _
  have hnn : ∀ a : ℕ, 0 ≤ (geomP F.p a).toReal * Real.exp (t * (s - a)) :=
    fun a => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  -- turn the `ℝ≥0∞` sum into a real sum
  have hENN : ∑' a, geomP F.p a * ENNReal.ofReal (Real.exp (t * (s - a)))
      = ENNReal.ofReal (((F.p : ℝ) - 1) * Real.exp (t * s) * (y / (1 - y))) := by
    rw [← hHas.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hnn hHas.summable]
    refine tsum_congr (fun a => ?_)
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
  rw [hENN, ENNReal.ofReal_le_one]
  -- the real inequality: `(p-1) e^{ts} y ≤ 1 - y`
  have h1y : 0 < 1 - y := by linarith
  rw [← mul_div_assoc, div_le_one h1y]
  have hets : Real.exp (t * s) ≤ 1 + t * s + (t * s) ^ 2 :=
    Mix.exp_le_one_add_add_sq (by positivity) hts
  have het : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hkey : ((F.p : ℝ) - 1) * Real.exp (t * s) ≤ (F.p : ℝ) * Real.exp t - 1 := by
    have h2 : ((F.p : ℝ) - 1) * (t * s + (t * s) ^ 2) ≤ (F.p : ℝ) * t := by
      have : ((F.p : ℝ) - 1) * (t * s + (t * s) ^ 2)
          = t * (((F.p : ℝ) - 1) * s + t * (((F.p : ℝ) - 1) * s ^ 2)) := by ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left ht2 ht0.le]
    nlinarith
  have hexpt : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have hp0 : (0 : ℝ) < (F.p : ℝ) := by linarith
  rw [hydef]
  rw [show ((F.p : ℝ) - 1) * Real.exp (t * s) * (Real.exp (-t) / (F.p : ℝ))
      = (((F.p : ℝ) - 1) * Real.exp (t * s)) * Real.exp (-t) / (F.p : ℝ) by ring,
    show 1 - Real.exp (-t) / (F.p : ℝ) = ((F.p : ℝ) * Real.exp t - 1) * Real.exp (-t) / (F.p : ℝ)
      by field_simp; linear_combination (-(F.p : ℝ)) * hexpt]
  apply div_le_div_of_nonneg_right _ hp0.le
  exact mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le

/-! ### The two one-sided tails -/

/-- **Lower tail of the suffix sum**: if `E[e^{t(s - G)}] ≤ 1`, then for all `r ≤ n` and real `x`,
`P(sum of the last r entries of 𝒢 ≤ s r - x) ≤ e^{-t x}`. -/
theorem sufSum_lower_tail (s t : ℝ) (ht : 0 ≤ t)
    (hmgf : ∑' a, geomP F.p a * ENNReal.ofReal (Real.exp (t * (s - a))) ≤ 1)
    (n r : ℕ) (hr : r ≤ n) (x : ℝ) :
    ∑' v : Fin n → ℕ × ℕ, ((stepLaw F.p).iid n) v
        * (if (sufSum (fun i => (v i).1) r : ℝ) ≤ s * r - x then 1 else 0)
      ≤ ENNReal.ofReal (Real.exp (-(t * x))) := by
  classical
  set g : Fin n → ℕ × ℕ → ℝ≥0∞ := fun i y =>
    if n - r ≤ (i : ℕ) then ENNReal.ofReal (Real.exp (t * (s - y.1))) else 1 with hgdef
  -- pointwise: indicator ≤ e^{-tx} ∏ g_i
  have hpt : ∀ v : Fin n → ℕ × ℕ,
      (if (sufSum (fun i => (v i).1) r : ℝ) ≤ s * r - x then (1 : ℝ≥0∞) else 0)
        ≤ ENNReal.ofReal (Real.exp (-(t * x))) * ∏ i, g i (v i) := by
    intro v
    have hprod : ∏ i, g i (v i)
        = ENNReal.ofReal (Real.exp (t * (s * r - (sufSum (fun i => (v i).1) r : ℝ)))) := by
      have hexp : Real.exp (t * (s * r - (sufSum (fun i => (v i).1) r : ℝ)))
          = ∏ i : Fin n, (if n - r ≤ (i : ℕ) then Real.exp (t * (s - (v i).1)) else 1) := by
        rw [show (∏ i : Fin n, (if n - r ≤ (i : ℕ) then Real.exp (t * (s - (v i).1)) else 1))
            = ∏ i : Fin n, Real.exp (if n - r ≤ (i : ℕ) then t * (s - (v i).1) else 0) from
          Finset.prod_congr rfl (fun i _ => by split_ifs <;> simp), ← Real.exp_sum]
        congr 1
        rw [sufSum_eq_sum_ite _ r]
        push_cast
        have hc : ∑ i : Fin n, (if n - r ≤ (i : ℕ) then t * (s - ((v i).1 : ℝ)) else 0)
            = t * s * ((Finset.univ.filter (fun i : Fin n => n - r ≤ (i : ℕ))).card : ℝ)
              - t * ∑ i : Fin n, (if n - r ≤ (i : ℕ) then ((v i).1 : ℝ) else 0) := by
          rw [Finset.mul_sum, Finset.card_filter, Nat.cast_sum, Finset.mul_sum,
            ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          split_ifs <;> push_cast <;> ring
        rw [hc, card_filter_last hr]
        ring
      rw [hexp, ENNReal.ofReal_prod_of_nonneg (fun i _ => by split_ifs <;> positivity)]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      simp only [hgdef]
      split_ifs <;> simp
    rw [hprod, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    split_ifs with h
    · rw [ENNReal.one_le_ofReal]
      apply Real.one_le_exp
      nlinarith
    · exact bot_le
  calc ∑' v : Fin n → ℕ × ℕ, ((stepLaw F.p).iid n) v
        * (if (sufSum (fun i => (v i).1) r : ℝ) ≤ s * r - x then 1 else 0)
      ≤ ∑' v : Fin n → ℕ × ℕ, ((stepLaw F.p).iid n) v
          * (ENNReal.ofReal (Real.exp (-(t * x))) * ∏ i, g i (v i)) :=
        ENNReal.tsum_le_tsum (fun v => mul_le_mul_right (hpt v) _)
    _ = ENNReal.ofReal (Real.exp (-(t * x)))
          * ∑' v : Fin n → ℕ × ℕ, ((stepLaw F.p).iid n) v * ∏ i, g i (v i) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr (fun v => ?_)
        ring
    _ = ENNReal.ofReal (Real.exp (-(t * x)))
          * ∏ i, ∑' y, stepLaw F.p y * g i y := by rw [Mix.tsum_iid_mul_prod]
    _ ≤ ENNReal.ofReal (Real.exp (-(t * x))) * 1 := by
        gcongr
        apply Finset.prod_le_one'
        intro i _
        simp only [hgdef]
        split_ifs
        · rw [F.stepLaw_tsum_fst (fun a => ENNReal.ofReal (Real.exp (t * (s - a))))]
          exact hmgf
        · rw [show (∑' y : ℕ × ℕ, stepLaw F.p y * 1) = ∑' y, stepLaw F.p y by simp,
            PMF.tsum_coe]
    _ = ENNReal.ofReal (Real.exp (-(t * x))) := mul_one _

/-- `P(G > m) = p^{-m}` (`G ~ G(μ)`, `m ∈ ℕ`). -/
theorem geomP_gt_mass (m : ℕ) :
    ∑' a, geomP F.p a * (if m < a then 1 else 0) = ((F.p : ℝ≥0∞)⁻¹) ^ m := by
  have hp := F.two_le_p
  have hsub : ((F.p - 1 : ℕ) : ℝ≥0∞) ≠ 0 := natCast_sub_one_ne_zero hp
  have hsubt : ((F.p - 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hinv : ((F.p : ℝ≥0∞)⁻¹) ≠ 0 := natCast_inv_ne_zero F.p
  have hinvt : ((F.p : ℝ≥0∞)⁻¹) ≠ ⊤ := natCast_inv_ne_top (by omega)
  have h1 : ∑' a, geomP F.p a * (if m < a then 1 else 0)
      = ∑' a, (if m < a then ((F.p - 1 : ℕ) : ℝ≥0∞) * ((F.p : ℝ≥0∞)⁻¹) ^ a else 0) := by
    refine tsum_congr (fun a => ?_)
    rw [geomP_apply hp]
    by_cases h : m < a
    · rw [if_pos h, if_pos h, if_neg (by omega), mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [h1, Mix.tsum_ite_lt_eq_shift m]
  simp_rw [show ∀ b : ℕ, ((F.p : ℝ≥0∞)⁻¹) ^ (b + m + 1)
      = ((F.p : ℝ≥0∞)⁻¹) ^ (m + 1) * ((F.p : ℝ≥0∞)⁻¹) ^ b from fun b => by ring]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
    one_sub_inv_natCast (by omega), ENNReal.mul_inv (Or.inl hsub) (Or.inl hsubt),
    inv_inv, pow_succ]
  have hpp : (F.p : ℝ≥0∞)⁻¹ * (F.p : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast F.p_ne_zero) (ENNReal.natCast_ne_top _)
  calc ((F.p - 1 : ℕ) : ℝ≥0∞) * (((F.p : ℝ≥0∞)⁻¹) ^ m * (F.p : ℝ≥0∞)⁻¹
        * (((F.p - 1 : ℕ) : ℝ≥0∞)⁻¹ * (F.p : ℝ≥0∞)))
      = (((F.p - 1 : ℕ) : ℝ≥0∞) * ((F.p - 1 : ℕ) : ℝ≥0∞)⁻¹)
          * ((F.p : ℝ≥0∞)⁻¹ * (F.p : ℝ≥0∞)) * ((F.p : ℝ≥0∞)⁻¹) ^ m := by ring
    _ = ((F.p : ℝ≥0∞)⁻¹) ^ m := by
        rw [ENNReal.mul_inv_cancel hsub hsubt, hpp, one_mul, one_mul]

/-- **Upper tail of a single component**: `P(𝒢_i > y) ≤ p e^{-y log p}` (`y ≥ 0`). -/
theorem coord_upper_tail (n : ℕ) (i : Fin n) (y : ℝ) (hy : 0 ≤ y) :
    ∑' v : Fin n → ℕ × ℕ, ((stepLaw F.p).iid n) v * (if y < ((v i).1 : ℝ) then 1 else 0)
      ≤ ENNReal.ofReal ((F.p : ℝ) * Real.exp (-(y * Real.log F.p))) := by
  classical
  set m : ℕ := ⌊y⌋₊ with hmdef
  set g : Fin n → ℕ × ℕ → ℝ≥0∞ := fun j z => if j = i then (if m < z.1 then 1 else 0) else 1
    with hgdef
  have hpt : ∀ v : Fin n → ℕ × ℕ,
      (if y < ((v i).1 : ℝ) then (1 : ℝ≥0∞) else 0) ≤ ∏ j, g j (v j) := by
    intro v
    rw [Finset.prod_eq_single i (fun j _ hj => by simp only [hgdef, if_neg hj])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp only [hgdef, if_true]
    split_ifs with h1 h2
    · exact le_refl _
    · exfalso; apply h2
      by_contra hc
      have : (v i).1 ≤ m := by omega
      have h3 : ((v i).1 : ℝ) ≤ y :=
        le_trans (by exact_mod_cast this) (Nat.floor_le hy)
      linarith
    · exact bot_le
    · exact le_refl _
  have hmain : ∑' v : Fin n → ℕ × ℕ, ((stepLaw F.p).iid n) v
        * (if y < ((v i).1 : ℝ) then 1 else 0) ≤ ((F.p : ℝ≥0∞)⁻¹) ^ m := by
    calc ∑' v : Fin n → ℕ × ℕ, ((stepLaw F.p).iid n) v
          * (if y < ((v i).1 : ℝ) then 1 else 0)
        ≤ ∑' v : Fin n → ℕ × ℕ, ((stepLaw F.p).iid n) v * ∏ j, g j (v j) :=
          ENNReal.tsum_le_tsum (fun v => mul_le_mul_right (hpt v) _)
      _ = ∏ j, ∑' z, stepLaw F.p z * g j z := Mix.tsum_iid_mul_prod _ n g
      _ = ∑' z, stepLaw F.p z * g i z := by
          rw [Finset.prod_eq_single i (fun j _ hj => by
            simp only [hgdef, if_neg hj, mul_one, PMF.tsum_coe])
            (fun h => absurd (Finset.mem_univ i) h)]
      _ = ((F.p : ℝ≥0∞)⁻¹) ^ m := by
          simp only [hgdef, if_true]
          rw [F.stepLaw_tsum_fst (fun a => if m < a then 1 else 0), F.geomP_gt_mass m]
  have hconv : ((F.p : ℝ≥0∞)⁻¹) ^ m = ENNReal.ofReal (((F.p : ℝ)⁻¹) ^ m) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast F.p_pos),
      ← ENNReal.ofReal_pow (by positivity)]
  refine le_trans hmain ?_
  rw [hconv]
  apply ENNReal.ofReal_le_ofReal
  · -- `(1/p)^m ≤ p e^{-y log p}` (`m > y - 1`)
    have hp1 : (1 : ℝ) < (F.p : ℝ) := by exact_mod_cast F.one_lt_p
    have hlogp : 0 < Real.log (F.p : ℝ) := Real.log_pos hp1
    have hm : y - 1 < (m : ℝ) := by
      have := Nat.lt_floor_add_one y
      rw [← hmdef] at this
      linarith
    have heq : ((F.p : ℝ)⁻¹) ^ m = Real.exp (-((m : ℝ) * Real.log F.p)) := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < (F.p : ℝ)),
        inv_pow]
    rw [heq, show (F.p : ℝ) * Real.exp (-(y * Real.log F.p))
        = Real.exp (Real.log F.p - y * Real.log F.p) by
      rw [Real.exp_sub, Real.exp_log (by positivity), Real.exp_neg]; ring]
    apply Real.exp_le_exp.mpr
    nlinarith

end Family

end GGMCollatz
