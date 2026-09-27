import GGMCollatz.Tao.Sec5.Generic

/-!
# Tails of sums of geometric distributions (counterpart of GGM `ineq:chernofftail` and Janson's bound)

Derived from `TaoCollatz/Prob/Mgf.lean`, `TaoCollatz/Sec5/ApproxFormula.lean` (`Gweight_prefix_decay`)
and `TaoCollatz/Sec5/FirstPassage.lean` (`geomHalf_underflow_le_Gweight`) of gotrevor/tao-collatz
(Apache-2.0), commit 15efca2: their role is restated for the GGM family's `G(μ)` (`geomP p`), generalized
to the GGM family (p, q, r).
The proof is Chernoff's method (the exponential Markov inequality and the moment generating function bound
`E e^{l(G-μ)} ≤ e^{K l²}`, `|l| ≤ 1/8`).

* `geom_lower_tail`: if `γ < μ` then `P(G_1 + ⋯ + G_n ≤ γ n) ≤ C e^{-cn}` (the lower tail of GGM §4 Step 1).
* `geom_dev_tail`: `P(|G_1 + ⋯ + G_j - μ j| ≥ t) ≤ C (e^{-ct²/(n+1)} + e^{-ct})` (`j ≤ n`; GGM
  `ineq:chernofftail`, Tao's Lemma 2.2).
* `geom_good_tail`: for `k ≤ n₀`, `P(G^{(k)} ∉ A^{(k)}) ≤ (log x)^{-4}` (for `x` large).
-/

open scoped ENNReal

namespace GGMCollatz

/-! ### Expectation of products under i.i.d. laws (ℝ≥0∞) -/

theorem tsum_iid_prod {α : Type*} (μ : PMF α) (g : α → ℝ≥0∞) (n : ℕ) :
    ∑' v : Fin n → α, (μ.iid n) v * ∏ i, g (v i) = (∑' a, μ a * g a) ^ n := by
  induction n with
  | zero => rw [PMF.tsum_iid_zero_mul]; simp
  | succ n ih =>
    rw [PMF.tsum_iid_succ_mul]
    simp_rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    calc ∑' a, μ a * ∑' w : Fin n → α, (μ.iid n) w * (g a * ∏ i, g (w i))
        = ∑' a, μ a * g a * ∑' w : Fin n → α, (μ.iid n) w * ∏ i, g (w i) := by
          refine tsum_congr fun a => ?_
          have h : ∑' w : Fin n → α, (μ.iid n) w * (g a * ∏ i, g (w i))
              = g a * ∑' w : Fin n → α, (μ.iid n) w * ∏ i, g (w i) := by
            rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun w => by ring
          rw [h, mul_assoc]
      _ = (∑' a, μ a * g a) * (∑' a, μ a * g a) ^ n := by
          rw [ih, ENNReal.tsum_mul_right]
      _ = (∑' a, μ a * g a) ^ (n + 1) := by rw [pow_succ']

/-! ### Inequalities for the exponential function -/

/-- `e^y ≤ 1 + y + y² e^{|y|}`. -/
theorem exp_le_one_add_add_sq_mul (y : ℝ) : Real.exp y ≤ 1 + y + y ^ 2 * Real.exp |y| := by
  rcases le_or_gt y 0 with hy | hy
  · -- `y ≤ 0`: `e^y ≤ 1 + y + y²`
    have h1 : Real.exp y ≤ 1 + y + y ^ 2 := by
      rcases le_or_gt (-1) y with hy1 | hy1
      · have := Real.abs_exp_sub_one_sub_id_le (show |y| ≤ 1 by rw [abs_le]; constructor <;> linarith)
        linarith [(abs_le.mp this).2]
      · have h2 : Real.exp y ≤ Real.exp (-1) := Real.exp_le_exp.mpr hy1.le
        have h3 : Real.exp (-1) ≤ 1 / 2 := by
          rw [Real.exp_neg]
          have := Real.exp_one_gt_d9
          rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
        nlinarith
    have h4 : y ^ 2 ≤ y ^ 2 * Real.exp |y| :=
      le_mul_of_one_le_right (sq_nonneg y) (Real.one_le_exp (abs_nonneg y))
    linarith
  · rw [abs_of_pos hy]
    rcases le_or_gt 1 y with hy1 | hy1
    · -- `y ≥ 1`: right-hand side ≥ e^y
      have : Real.exp y ≤ y ^ 2 * Real.exp y := le_mul_of_one_le_left (Real.exp_pos y).le (by nlinarith)
      linarith
    · -- `0 < y < 1`: `e^y ≤ 1/(1-y)`
      have h1 := Real.exp_bound_div_one_sub_of_interval' hy hy1
      have h2 : Real.exp y * (1 - y) < 1 := by
        rw [lt_div_iff₀ (by linarith)] at h1; linarith
      nlinarith [Real.exp_pos y]

namespace Family

variable (F : Family)

/-! ### Moments of the geometric distribution -/

theorem p_inv_lt_one : ‖((F.p : ℝ))⁻¹‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr F.p_real_pos)]
  exact inv_lt_one_of_one_lt₀ F.one_lt_p_real

/-- Mean: `E G = μ`. -/
theorem geomP_mean :
    HasSum (fun k : ℕ => (geomP F.p k).toReal * k) F.mu := by
  have hp1 : (F.p : ℝ) - 1 ≠ 0 := by have := F.one_lt_p_real; linarith
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one F.p_inv_lt_one).mul_left ((F.p : ℝ) - 1)
  have heq : (fun k : ℕ => (geomP F.p k).toReal * k)
      = fun k : ℕ => ((F.p : ℝ) - 1) * ((k : ℝ) * ((F.p : ℝ))⁻¹ ^ k) := by
    funext k
    rw [geomP_toReal F.two_le_p]
    split_ifs with hk
    · subst hk; simp
    · ring
  rw [heq]
  have hval : ((F.p : ℝ) - 1) * (((F.p : ℝ))⁻¹ / (1 - ((F.p : ℝ))⁻¹) ^ 2) = F.mu := by
    unfold mu
    have hp0 : (F.p : ℝ) ≠ 0 := F.p_real_pos.ne'
    field_simp
  rw [← hval]
  exact h

/-- Exponential moment: `E e^{G/4} ≤ M₀`. -/
noncomputable def expMomBound : ℝ := ((F.p : ℝ) - 1) / (1 - Real.exp (1 / 4) / F.p)

theorem exp_quarter_lt_two : Real.exp (1 / 4) < 2 := by
  have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 4) (by norm_num) (by norm_num)
  linarith [show (1 : ℝ) / (1 - 1 / 4) = 4 / 3 by norm_num]

theorem geomP_expMom :
    Summable (fun k : ℕ => (geomP F.p k).toReal * Real.exp (k / 4)) ∧
      ∑' k : ℕ, (geomP F.p k).toReal * Real.exp (k / 4) ≤ F.expMomBound := by
  set r : ℝ := Real.exp (1 / 4) / F.p with hr
  have hr0 : 0 ≤ r := div_nonneg (Real.exp_pos _).le F.p_real_pos.le
  have hr1 : r < 1 := by
    rw [hr, div_lt_one F.p_real_pos]
    linarith [exp_quarter_lt_two, F.p_real_two_le]
  have hp1 : (0 : ℝ) ≤ (F.p : ℝ) - 1 := by linarith [F.one_lt_p_real]
  have hle : ∀ k : ℕ, (geomP F.p k).toReal * Real.exp (k / 4) ≤ ((F.p : ℝ) - 1) * r ^ k := by
    intro k
    rw [geomP_toReal F.two_le_p]
    split_ifs with hk
    · subst hk; rw [zero_mul, pow_zero, mul_one]; exact hp1
    · rw [hr, div_pow, ← Real.exp_nat_mul, show (k : ℝ) * (1 / 4) = k / 4 by ring]
      rw [div_eq_mul_inv, inv_pow]
      ring_nf; rfl
  have hnn : ∀ k : ℕ, 0 ≤ (geomP F.p k).toReal * Real.exp (k / 4) := fun k =>
    mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  have hs : Summable (fun k : ℕ => ((F.p : ℝ) - 1) * r ^ k) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hs' := Summable.of_nonneg_of_le hnn hle hs
  refine ⟨hs', ?_⟩
  calc ∑' k : ℕ, (geomP F.p k).toReal * Real.exp (k / 4) ≤ ∑' k : ℕ, ((F.p : ℝ) - 1) * r ^ k :=
        hs'.tsum_le_tsum hle hs
    _ = ((F.p : ℝ) - 1) * (1 - r)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ = F.expMomBound := by unfold expMomBound; rw [div_eq_mul_inv]

theorem expMomBound_pos : 0 < F.expMomBound := by
  unfold expMomBound
  have h1 : 0 < (F.p : ℝ) - 1 := by linarith [F.one_lt_p_real]
  have h2 : Real.exp (1 / 4) / F.p < 1 := by
    rw [div_lt_one F.p_real_pos]; linarith [exp_quarter_lt_two, F.p_real_two_le]
  exact div_pos h1 (by linarith)

/-- The moment generating function constant `K = 128 e^{μ/4} M₀`. -/
noncomputable def mgfConst : ℝ := 128 * Real.exp (F.mu / 4) * F.expMomBound

theorem mgfConst_pos : 0 < F.mgfConst := by
  unfold mgfConst; have := F.expMomBound_pos; positivity

/-- **Moment generating function bound**: if `|l| ≤ 1/8` then `E e^{l(G-μ)} ≤ e^{K l²}` (ℝ≥0∞ form). -/
theorem geomP_mgf_le {l : ℝ} (hl : |l| ≤ 1 / 8) :
    ∑' k : ℕ, geomP F.p k * ENNReal.ofReal (Real.exp (l * (k - F.mu)))
      ≤ ENNReal.ofReal (Real.exp (F.mgfConst * l ^ 2)) := by
  set w : ℕ → ℝ := fun k => (geomP F.p k).toReal with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => ENNReal.toReal_nonneg
  obtain ⟨hs2, hS2⟩ := F.geomP_expMom
  have hS0 : HasSum w 1 := by
    have := (summable_toReal (geomP F.p)).hasSum
    rwa [tsum_toReal_eq_one] at this
  have hS1 := F.geomP_mean
  -- pointwise bound
  set Q : ℕ → ℝ := fun k => 1 + l * ((k : ℝ) - F.mu)
    + l ^ 2 * (128 * Real.exp (F.mu / 4) * Real.exp ((k : ℝ) / 4)) with hQ
  have hpt : ∀ k : ℕ, Real.exp (l * ((k : ℝ) - F.mu)) ≤ Q k := by
    intro k
    have h1 := exp_le_one_add_add_sq_mul (l * ((k : ℝ) - F.mu))
    set z := |(k : ℝ) - F.mu| with hz
    have hz0 : 0 ≤ z := abs_nonneg _
    have h2 : |l * ((k : ℝ) - F.mu)| ≤ z / 8 := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hl hz0 |>.trans (by linarith)
    have h3 : ((k : ℝ) - F.mu) ^ 2 ≤ 128 * Real.exp (z / 8) := by
      have := Real.quadratic_le_exp_of_nonneg (show 0 ≤ z / 8 by positivity)
      have hsq : ((k : ℝ) - F.mu) ^ 2 = z ^ 2 := by rw [hz, sq_abs]
      rw [hsq]; nlinarith
    have h4 : z ≤ (k : ℝ) + F.mu := by
      rw [hz, abs_le]; constructor <;> linarith [F.mu_pos, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h5 : (l * ((k : ℝ) - F.mu)) ^ 2 * Real.exp |l * ((k : ℝ) - F.mu)|
        ≤ l ^ 2 * (128 * Real.exp (F.mu / 4) * Real.exp ((k : ℝ) / 4)) := by
      rw [mul_pow]
      calc l ^ 2 * ((k : ℝ) - F.mu) ^ 2 * Real.exp |l * ((k : ℝ) - F.mu)|
          ≤ l ^ 2 * (128 * Real.exp (z / 8)) * Real.exp (z / 8) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left h3 (sq_nonneg l))
              (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le (by positivity)
        _ = l ^ 2 * (128 * Real.exp (z / 4)) := by
            rw [mul_assoc, mul_assoc, ← Real.exp_add]; ring_nf
        _ ≤ l ^ 2 * (128 * Real.exp (F.mu / 4) * Real.exp ((k : ℝ) / 4)) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg l)
            rw [mul_assoc, ← Real.exp_add]
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact Real.exp_le_exp.mpr (by linarith)
    rw [hQ]; linarith
  -- expectation of `Q`
  have hQsum : HasSum (fun k => w k * Q k) (1 + l ^ 2 * (128 * Real.exp (F.mu / 4)
      * ∑' k : ℕ, (geomP F.p k).toReal * Real.exp (k / 4))) := by
    have hA : HasSum (fun k => w k * 1) 1 := by simpa using hS0
    have hB : HasSum (fun k => w k * (l * ((k : ℝ) - F.mu))) 0 := by
      have h := (hS1.sub (hS0.mul_left F.mu)).mul_left l
      have e1 : (fun k : ℕ => w k * (l * ((k : ℝ) - F.mu)))
          = fun i => l * ((geomP F.p i).toReal * i - F.mu * w i) := by
        funext k; simp only [hw]; ring
      have e2 : l * (F.mu - F.mu * 1) = 0 := by ring
      rw [e1]; rw [e2] at h; exact h
    have hC : HasSum (fun k => w k * (l ^ 2 * (128 * Real.exp (F.mu / 4) * Real.exp ((k : ℝ) / 4))))
        (l ^ 2 * (128 * Real.exp (F.mu / 4) * ∑' k : ℕ, (geomP F.p k).toReal * Real.exp (k / 4))) := by
      have h := hs2.hasSum.mul_left (l ^ 2 * (128 * Real.exp (F.mu / 4)))
      have e1 : (fun k : ℕ => w k * (l ^ 2 * (128 * Real.exp (F.mu / 4) * Real.exp ((k : ℝ) / 4))))
          = fun i => l ^ 2 * (128 * Real.exp (F.mu / 4)) * ((geomP F.p i).toReal * Real.exp (i / 4)) := by
        funext k; simp only [hw]; ring
      have e2 : l ^ 2 * (128 * Real.exp (F.mu / 4) * ∑' k : ℕ, (geomP F.p k).toReal * Real.exp (k / 4))
          = l ^ 2 * (128 * Real.exp (F.mu / 4)) * ∑' k : ℕ, (geomP F.p k).toReal * Real.exp (k / 4) := by
        ring
      rw [e1, e2]; exact h
    have h := (hA.add hB).add hC
    have e1 : (fun k => w k * Q k) = fun k => w k * 1 + w k * (l * ((k : ℝ) - F.mu))
        + w k * (l ^ 2 * (128 * Real.exp (F.mu / 4) * Real.exp ((k : ℝ) / 4))) := by
      funext k; simp only [hQ]; ring
    have e2 : 1 + l ^ 2 * (128 * Real.exp (F.mu / 4)
        * ∑' k : ℕ, (geomP F.p k).toReal * Real.exp (k / 4))
        = 1 + 0 + l ^ 2 * (128 * Real.exp (F.mu / 4)
          * ∑' k : ℕ, (geomP F.p k).toReal * Real.exp (k / 4)) := by ring
    rw [e1, e2]; exact h
  have hQle : 1 + l ^ 2 * (128 * Real.exp (F.mu / 4)
      * ∑' k : ℕ, (geomP F.p k).toReal * Real.exp (k / 4)) ≤ Real.exp (F.mgfConst * l ^ 2) := by
    have h1 : 1 + l ^ 2 * (128 * Real.exp (F.mu / 4)
        * ∑' k : ℕ, (geomP F.p k).toReal * Real.exp (k / 4)) ≤ 1 + F.mgfConst * l ^ 2 := by
      unfold mgfConst
      have : 128 * Real.exp (F.mu / 4) * ∑' k : ℕ, (geomP F.p k).toReal * Real.exp (k / 4)
          ≤ 128 * Real.exp (F.mu / 4) * F.expMomBound :=
        mul_le_mul_of_nonneg_left hS2 (by positivity)
      nlinarith [sq_nonneg l]
    have h2 := Real.add_one_le_exp (F.mgfConst * l ^ 2)
    linarith
  -- conversion to ℝ≥0∞
  have hnn : ∀ k, 0 ≤ w k * Real.exp (l * ((k : ℝ) - F.mu)) := fun k =>
    mul_nonneg (hw0 k) (Real.exp_pos _).le
  have hle : ∀ k, w k * Real.exp (l * ((k : ℝ) - F.mu)) ≤ w k * Q k := fun k =>
    mul_le_mul_of_nonneg_left (hpt k) (hw0 k)
  have hsum := Summable.of_nonneg_of_le hnn hle hQsum.summable
  calc ∑' k : ℕ, geomP F.p k * ENNReal.ofReal (Real.exp (l * (k - F.mu)))
      = ∑' k : ℕ, ENNReal.ofReal (w k * Real.exp (l * ((k : ℝ) - F.mu))) := by
        refine tsum_congr fun k => ?_
        rw [ENNReal.ofReal_mul (hw0 k), hw, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
    _ = ENNReal.ofReal (∑' k : ℕ, w k * Real.exp (l * ((k : ℝ) - F.mu))) :=
        (ENNReal.ofReal_tsum_of_nonneg hnn hsum).symm
    _ ≤ ENNReal.ofReal (Real.exp (F.mgfConst * l ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        calc ∑' k : ℕ, w k * Real.exp (l * ((k : ℝ) - F.mu)) ≤ ∑' k, w k * Q k :=
              hsum.tsum_le_tsum hle hQsum.summable
          _ = _ := hQsum.tsum_eq
          _ ≤ _ := hQle

/-! ### Chernoff bounds -/

/-- If `|l| ≤ 1/8` then `P(t ≤ l (Σ_{i<n} G_i - μ n)) ≤ e^{-t + K l² n}`. -/
theorem iid_tail {l : ℝ} (hl : |l| ≤ 1 / 8) (n : ℕ) (t : ℝ) :
    expect (PMF.iid (geomP F.p) n)
        (Set.indicator {a | t ≤ l * ((pre a n : ℝ) - F.mu * n)} 1)
      ≤ Real.exp (-t + F.mgfConst * l ^ 2 * n) := by
  set μn := PMF.iid (geomP F.p) n with hμn
  set T : Set (Fin n → ℕ) := {a | t ≤ l * ((pre a n : ℝ) - F.mu * n)} with hT
  have hind : ∀ a : Fin n → ℕ, ENNReal.ofReal (Set.indicator T 1 a)
      ≤ ENNReal.ofReal (Real.exp (-t)) *
          ∏ i, ENNReal.ofReal (Real.exp (l * (((a i : ℕ) : ℝ) - F.mu))) := by
    intro a
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_sum, ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    have hsum : ∑ i : Fin n, l * (((a i : ℕ) : ℝ) - F.mu) = l * ((pre a n : ℝ) - F.mu * n) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, pre_eq_fin_sum, Nat.cast_sum]
      ring
    rw [hsum]
    by_cases ha : a ∈ T
    · rw [Set.indicator_of_mem ha, Pi.one_apply]
      apply Real.one_le_exp
      have : t ≤ l * ((pre a n : ℝ) - F.mu * n) := ha
      linarith
    · rw [Set.indicator_of_notMem ha]
      exact (Real.exp_pos _).le
  have htsum : ∑' a, μn a * ENNReal.ofReal (Set.indicator T 1 a)
      ≤ ENNReal.ofReal (Real.exp (-t)) * ENNReal.ofReal (Real.exp (F.mgfConst * l ^ 2)) ^ n := by
    calc ∑' a, μn a * ENNReal.ofReal (Set.indicator T 1 a)
        ≤ ∑' a, μn a * (ENNReal.ofReal (Real.exp (-t)) *
            ∏ i, ENNReal.ofReal (Real.exp (l * (((a i : ℕ) : ℝ) - F.mu)))) :=
          ENNReal.tsum_le_tsum fun a => by gcongr; exact hind a
      _ = ENNReal.ofReal (Real.exp (-t)) * ∑' a, μn a *
            ∏ i, ENNReal.ofReal (Real.exp (l * (((a i : ℕ) : ℝ) - F.mu))) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun a => ?_
          ring
      _ = ENNReal.ofReal (Real.exp (-t)) *
            (∑' k : ℕ, geomP F.p k * ENNReal.ofReal (Real.exp (l * (k - F.mu)))) ^ n := by
          have hprod := tsum_iid_prod (geomP F.p)
            (fun k : ℕ => ENNReal.ofReal (Real.exp (l * ((k : ℝ) - F.mu)))) n
          rw [hμn, hprod]
      _ ≤ ENNReal.ofReal (Real.exp (-t)) * ENNReal.ofReal (Real.exp (F.mgfConst * l ^ 2)) ^ n := by
          gcongr
          exact F.geomP_mgf_le hl
  have hfin : ENNReal.ofReal (Real.exp (-t)) * ENNReal.ofReal (Real.exp (F.mgfConst * l ^ 2)) ^ n
      ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  unfold expect
  rw [← PMF.toReal_tsum_mul_ofReal μn (Set.indicator T 1)
    (fun a => Set.indicator_nonneg (fun _ _ => zero_le_one) a)]
  calc (∑' a, μn a * ENNReal.ofReal (Set.indicator T 1 a)).toReal
      ≤ (ENNReal.ofReal (Real.exp (-t)) * ENNReal.ofReal (Real.exp (F.mgfConst * l ^ 2)) ^ n).toReal :=
        (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hfin htsum) hfin).mpr htsum
    _ = Real.exp (-t) * Real.exp (F.mgfConst * l ^ 2) ^ n := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.exp_pos _).le,
          ENNReal.toReal_ofReal (Real.exp_pos _).le]
    _ = Real.exp (-t + F.mgfConst * l ^ 2 * n) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf

/-- An event on the first `j` components can be measured with the i.i.d. law of length `j`. -/
theorem expect_prefix_event (n j : ℕ) (hj : j ≤ n) (P : ℕ → Prop) :
    expect (PMF.iid (geomP F.p) n) (Set.indicator {a | P (pre a j)} 1)
      = expect (PMF.iid (geomP F.p) j) (Set.indicator {a | P (pre a j)} 1) := by
  have hset : {a : Fin n → ℕ | (a ∘ Fin.castLE hj) ∈ {a : Fin j → ℕ | P (pre a j)}}
      = {a | P (pre a j)} := by
    ext a
    simp only [Set.mem_setOf_eq]
    rw [pre_castLE hj a le_rfl]
  rw [← iid_map_castLE (geomP F.p) j n hj, expect_map_indicator, hset]

/-- **Lower tail** (Chernoff): if `γ < μ` then `P(Σ_{i<n} G_i ≤ γ n) ≤ C e^{-cn}`. -/
theorem geom_lower_tail {γ : ℝ} (hγ : γ < F.mu) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ,
      expect (PMF.iid (geomP F.p) n) (Set.indicator {a | (pre a n : ℝ) ≤ γ * n} 1)
        ≤ C * Real.exp (-(c * n)) := by
  have hK := F.mgfConst_pos
  set δ := F.mu - γ with hδ
  have hδ0 : 0 < δ := by linarith
  set l : ℝ := min (1 / 8) (δ / (2 * F.mgfConst)) with hl
  have hl0 : 0 < l := lt_min (by norm_num) (by positivity)
  have hl8 : l ≤ 1 / 8 := min_le_left _ _
  have hlK : F.mgfConst * l ≤ δ / 2 := by
    have := min_le_right (1 / 8 : ℝ) (δ / (2 * F.mgfConst))
    rw [← hl] at this
    calc F.mgfConst * l ≤ F.mgfConst * (δ / (2 * F.mgfConst)) := mul_le_mul_of_nonneg_left this hK.le
      _ = δ / 2 := by field_simp
  refine ⟨l * δ / 2, 1, by positivity, one_pos, fun n => ?_⟩
  have habs : |(-l)| ≤ 1 / 8 := by rw [abs_neg, abs_of_pos hl0]; exact hl8
  have h := F.iid_tail habs n (l * δ * n)
  have hsub : {a : Fin n → ℕ | (pre a n : ℝ) ≤ γ * n}
      ⊆ {a | l * δ * n ≤ -l * ((pre a n : ℝ) - F.mu * n)} := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have : l * δ * n = l * (F.mu * n - γ * n) := by rw [hδ]; ring
    rw [this]
    nlinarith
  calc _ ≤ expect (PMF.iid (geomP F.p) n)
        (Set.indicator {a | l * δ * n ≤ -l * ((pre a n : ℝ) - F.mu * n)} 1) :=
        expect_indicator_mono _ hsub
    _ ≤ Real.exp (-(l * δ * n) + F.mgfConst * (-l) ^ 2 * n) := h
    _ ≤ 1 * Real.exp (-(l * δ / 2 * n)) := by
        rw [one_mul]
        apply Real.exp_le_exp.mpr
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have : F.mgfConst * (-l) ^ 2 = l * (F.mgfConst * l) := by ring
        rw [this]
        have : l * (F.mgfConst * l) * n ≤ l * (δ / 2) * n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlK hl0.le) hn
        nlinarith

/-- **Deviation tail** (Chernoff, GGM `ineq:chernofftail`): for `j ≤ n`, `t ≥ 0`,
`P(|Σ_{i<j} G_i - μ j| ≥ t) ≤ C (e^{-ct²/(n+1)} + e^{-ct})`. -/
theorem geom_dev_tail :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ) (t : ℝ), 0 ≤ t → ∀ j ≤ n,
      expect (PMF.iid (geomP F.p) n) (Set.indicator {a | t ≤ |(pre a j : ℝ) - F.mu * j|} 1)
        ≤ C * (Real.exp (-(c * t ^ 2 / (n + 1))) + Real.exp (-(c * t))) := by
  have hK := F.mgfConst_pos
  set K := F.mgfConst with hKdef
  refine ⟨min (1 / (4 * K)) (1 / 16), 2, lt_min (by positivity) (by norm_num), by norm_num, ?_⟩
  intro n t ht j hj
  set c := min (1 / (4 * K)) (1 / 16) with hc
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hjn : (j : ℝ) ≤ (n : ℝ) + 1 := by
    have : (j : ℝ) ≤ n := by exact_mod_cast hj
    linarith
  rw [F.expect_prefix_event n j hj (fun s => t ≤ |(s : ℝ) - F.mu * j|)]
  -- the exponent `l`
  set l : ℝ := min (1 / 8) (t / (2 * K * ((n : ℝ) + 1))) with hl
  have hl0 : 0 ≤ l := le_min (by norm_num) (by positivity)
  have hl8 : l ≤ 1 / 8 := min_le_left _ _
  have habs1 : |l| ≤ 1 / 8 := by rw [abs_of_nonneg hl0]; exact hl8
  have habs2 : |(-l)| ≤ 1 / 8 := by rw [abs_neg, abs_of_nonneg hl0]; exact hl8
  have h1 := F.iid_tail habs1 j (l * t)
  have h2 := F.iid_tail habs2 j (l * t)
  have hsub : {a : Fin j → ℕ | t ≤ |(pre a j : ℝ) - F.mu * j|}
      ⊆ {a | l * t ≤ l * ((pre a j : ℝ) - F.mu * j)} ∪
        {a | l * t ≤ -l * ((pre a j : ℝ) - F.mu * j)} := by
    intro a ha
    simp only [Set.mem_setOf_eq, Set.mem_union] at ha ⊢
    rcases le_or_gt 0 ((pre a j : ℝ) - F.mu * j) with h | h
    · left; rw [abs_of_nonneg h] at ha; exact mul_le_mul_of_nonneg_left ha hl0
    · right; rw [abs_of_neg h] at ha
      have := mul_le_mul_of_nonneg_left ha hl0
      linarith
  have hunion : expect (PMF.iid (geomP F.p) j) (Set.indicator {a : Fin j → ℕ |
      t ≤ |(pre a j : ℝ) - F.mu * j|} 1)
      ≤ Real.exp (-(l * t) + K * l ^ 2 * j) + Real.exp (-(l * t) + K * (-l) ^ 2 * j) := by
    calc _ ≤ expect (PMF.iid (geomP F.p) j) (fun a =>
            Set.indicator {a | l * t ≤ l * ((pre a j : ℝ) - F.mu * j)} (1 : (Fin j → ℕ) → ℝ) a +
            Set.indicator {a | l * t ≤ -l * ((pre a j : ℝ) - F.mu * j)} 1 a) := by
          apply expect_mono _ 2 (fun a => (abs_indicator_le_one _ a).trans (by norm_num))
          · intro a
            have e1 := abs_indicator_le_one {a : Fin j → ℕ | l * t ≤ l * ((pre a j : ℝ) - F.mu * j)} a
            have e2 := abs_indicator_le_one {a : Fin j → ℕ | l * t ≤ -l * ((pre a j : ℝ) - F.mu * j)} a
            exact (abs_add_le _ _).trans (by linarith)
          · intro a
            by_cases ha : a ∈ {a : Fin j → ℕ | t ≤ |(pre a j : ℝ) - F.mu * j|}
            · rw [Set.indicator_of_mem ha, Pi.one_apply]
              rcases hsub ha with h | h
              · rw [Set.indicator_of_mem h, Pi.one_apply]
                linarith [Set.indicator_nonneg (fun _ _ => zero_le_one) (s := {a : Fin j → ℕ |
                  l * t ≤ -l * ((pre a j : ℝ) - F.mu * j)}) (f := (1 : (Fin j → ℕ) → ℝ)) a]
              · rw [Set.indicator_of_mem h, Pi.one_apply]
                linarith [Set.indicator_nonneg (fun _ _ => zero_le_one) (s := {a : Fin j → ℕ |
                  l * t ≤ l * ((pre a j : ℝ) - F.mu * j)}) (f := (1 : (Fin j → ℕ) → ℝ)) a]
            · rw [Set.indicator_of_notMem ha]
              exact add_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) a)
                (Set.indicator_nonneg (fun _ _ => zero_le_one) a)
      _ = _ + _ := expect_add _ 1 (abs_indicator_le_one _) (abs_indicator_le_one _)
      _ ≤ _ := add_le_add h1 h2
  refine hunion.trans ?_
  rw [neg_sq]
  have hexp : -(l * t) + K * l ^ 2 * j ≤ -(c * t ^ 2 / ((n : ℝ) + 1)) ∨
      -(l * t) + K * l ^ 2 * j ≤ -(c * t) := by
    have hlj : K * l ^ 2 * j ≤ K * l ^ 2 * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hjn (by positivity)
    by_cases hcase : t / (2 * K * ((n : ℝ) + 1)) ≤ 1 / 8
    · left
      have hleq : l = t / (2 * K * ((n : ℝ) + 1)) := min_eq_right hcase
      have hc1 : c ≤ 1 / (4 * K) := min_le_left _ _
      have e : -(l * t) + K * l ^ 2 * ((n : ℝ) + 1) = -(t ^ 2 / (4 * K * ((n : ℝ) + 1))) := by
        rw [hleq]; field_simp; ring
      have h3 : c * t ^ 2 / ((n : ℝ) + 1) ≤ t ^ 2 / (4 * K * ((n : ℝ) + 1)) := by
        rw [div_le_div_iff₀ hn1 (by positivity)]
        have : c * (4 * K) ≤ 1 := by
          rw [le_div_iff₀ (by positivity)] at hc1; linarith
        have ht2 : 0 ≤ t ^ 2 * ((n : ℝ) + 1) := by positivity
        nlinarith
      linarith
    · right
      push_neg at hcase
      have hleq : l = 1 / 8 := min_eq_left hcase.le
      have hc2 : c ≤ 1 / 16 := min_le_right _ _
      have hKn : K * ((n : ℝ) + 1) < 4 * t := by
        rw [lt_div_iff₀ (by positivity)] at hcase; linarith
      have : c * t ≤ t / 16 := by
        have := mul_le_mul_of_nonneg_right hc2 ht
        linarith
      rw [hleq] at hlj ⊢
      linarith
  rcases hexp with h | h
  · have e1 : Real.exp (-(l * t) + K * l ^ 2 * j) ≤ Real.exp (-(c * t ^ 2 / ((n : ℝ) + 1))) :=
      Real.exp_le_exp.mpr h
    have e2 : 0 ≤ Real.exp (-(c * t)) := (Real.exp_pos _).le
    linarith
  · have e1 : Real.exp (-(l * t) + K * l ^ 2 * j) ≤ Real.exp (-(c * t)) := Real.exp_le_exp.mpr h
    have e2 : 0 ≤ Real.exp (-(c * t ^ 2 / ((n : ℝ) + 1))) := (Real.exp_pos _).le
    linarith

/-- `log q ≥ 1` since `q ≥ 3`. -/
theorem one_le_log_q : 1 ≤ Real.log F.q := by
  have hq : (3 : ℝ) ≤ F.q := by
    have := F.two_le_p; have := F.p_lt_q
    exact_mod_cast (show 3 ≤ F.q by omega)
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith))

/-- `n₀ ≤ log x / 3`. -/
theorem nZero_le {x : ℝ} (hx : 1 ≤ x) : (F.nZero x : ℝ) ≤ Real.log x / 3 := by
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlq := F.one_le_log_q
  unfold nZero
  calc (⌊Real.log x / (5 * Real.log F.q)⌋₊ : ℝ) ≤ Real.log x / (5 * Real.log F.q) :=
        Nat.floor_le (by positivity)
    _ ≤ Real.log x / 3 := by
        apply div_le_div_of_nonneg_left hL (by norm_num); linarith

/-- **Tail for good tuples**: if `x` is large, then for `k ≤ n₀`, `P(G^{(k)} ∉ A^{(k)}) ≤ (log x)^{-4}`
(the model side of GGM `eq: error for not in A`). -/
theorem geom_good_tail : ∀ᶠ x : ℝ in Filter.atTop, ∀ k ≤ F.nZero x,
    expect (PMF.iid (geomP F.p) k) (Set.indicator {a | ¬ F.goodVec x a} 1)
      ≤ Real.log x ^ (-4 : ℝ) := by
  obtain ⟨c, C, hc, hC, hdev⟩ := F.geom_dev_tail
  set D : ℝ := 2 * C * (Nat.factorial 30 : ℝ) / c ^ 30 with hD
  filter_upwards [eventually_log_ge (max 3 D), Filter.eventually_ge_atTop 1] with x hL hx1
  intro k hk
  set L := Real.log x with hLdef
  have hL3 : 3 ≤ L := le_trans (le_max_left _ _) hL
  have hLD : D ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 0 < L := by linarith
  set t := L ^ (0.6 : ℝ) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hLpos.le _
  set u := L ^ (0.2 : ℝ) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg hLpos.le _
  have hk1 : (k : ℝ) + 1 ≤ L := by
    have h1 : (k : ℝ) ≤ F.nZero x := by exact_mod_cast hk
    have h2 := F.nZero_le hx1
    rw [← hLdef] at h2
    linarith
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  -- upper bound on the sum (union bound)
  have hunion : expect (PMF.iid (geomP F.p) k) (Set.indicator {a | ¬ F.goodVec x a} 1)
      ≤ ∑ j ∈ Finset.range (k + 1), expect (PMF.iid (geomP F.p) k)
          (Set.indicator {a : Fin k → ℕ | t ≤ |(pre a j : ℝ) - F.mu * j|} 1) := by
    rw [← expect_finset_sum _ _ _ 1 (fun j _ a => abs_indicator_le_one _ a)]
    apply expect_mono _ ((k : ℝ) + 1) (fun a => (abs_indicator_le_one _ a).trans (by linarith))
    · intro a
      have h0 : 0 ≤ ∑ j ∈ Finset.range (k + 1),
          Set.indicator {a : Fin k → ℕ | t ≤ |(pre a j : ℝ) - F.mu * j|} (1 : (Fin k → ℕ) → ℝ) a :=
        Finset.sum_nonneg fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) a
      rw [abs_of_nonneg h0]
      calc _ ≤ ∑ _j ∈ Finset.range (k + 1), (1 : ℝ) :=
            Finset.sum_le_sum fun j _ => (le_abs_self _).trans (abs_indicator_le_one _ a)
        _ = (k : ℝ) + 1 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]; push_cast; ring
    · intro a
      by_cases hg : F.goodVec x a
      · rw [Set.indicator_of_notMem (by simpa using hg)]
        exact Finset.sum_nonneg fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) a
      · rw [Set.indicator_of_mem (by simpa using hg), Pi.one_apply]
        unfold goodVec at hg
        push_neg at hg
        obtain ⟨j, hj, hjt⟩ := hg
        have hmem : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
        have hone : Set.indicator {a : Fin k → ℕ | t ≤ |(pre a j : ℝ) - F.mu * j|}
            (1 : (Fin k → ℕ) → ℝ) a = 1 := by
          rw [Set.indicator_of_mem (show a ∈ {a : Fin k → ℕ | t ≤ |(pre a j : ℝ) - F.mu * j|}
            from hjt)]; rfl
        rw [← hone]
        exact Finset.single_le_sum (f := fun j => Set.indicator {a : Fin k → ℕ |
          t ≤ |(pre a j : ℝ) - F.mu * j|} (1 : (Fin k → ℕ) → ℝ) a)
          (fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) a) hmem
  -- each term
  have hexp1 : Real.exp (-(c * t ^ 2 / ((k : ℝ) + 1))) ≤ Real.exp (-(c * u)) := by
    apply Real.exp_le_exp.mpr
    have h1 : t ^ 2 = L ^ (1.2 : ℝ) := by
      rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; norm_num
    have h2 : L ^ (1.2 : ℝ) = L * u := by
      rw [hu, ← Real.rpow_one_add' hLpos.le (by norm_num)]; norm_num
    have h3 : u ≤ t ^ 2 / ((k : ℝ) + 1) := by
      rw [le_div_iff₀ hk0, h1, h2]
      nlinarith
    have h4 : c * u ≤ c * t ^ 2 / ((k : ℝ) + 1) := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h3 hc.le
    linarith
  have hexp2 : Real.exp (-(c * t)) ≤ Real.exp (-(c * u)) := by
    apply Real.exp_le_exp.mpr
    have : u ≤ t := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    nlinarith
  have hterm : ∀ j ∈ Finset.range (k + 1), expect (PMF.iid (geomP F.p) k)
      (Set.indicator {a : Fin k → ℕ | t ≤ |(pre a j : ℝ) - F.mu * j|} 1)
      ≤ 2 * C * Real.exp (-(c * u)) := by
    intro j hj
    have := hdev k t ht0 j (by rw [Finset.mem_range] at hj; omega)
    calc _ ≤ C * (Real.exp (-(c * t ^ 2 / (k + 1))) + Real.exp (-(c * t))) := this
      _ ≤ C * (Real.exp (-(c * u)) + Real.exp (-(c * u))) := by gcongr
      _ = 2 * C * Real.exp (-(c * u)) := by ring
  -- `2C L^5 e^{-c L^{0.2}} ≤ 1`
  have hfac : (c * u) ^ 30 / (Nat.factorial 30 : ℝ) ≤ Real.exp (c * u) :=
    Real.pow_div_factorial_le_exp (x := c * u) (by positivity) 30
  have hu30 : u ^ 30 = L ^ 6 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; norm_num
  have hkey : 2 * C * L ^ 5 * Real.exp (-(c * u)) ≤ 1 := by
    have hf30 : (0 : ℝ) < (Nat.factorial 30 : ℝ) := by positivity
    have hcu : 0 < c * u := by
      have : 0 < u := Real.rpow_pos_of_pos hLpos _
      positivity
    rw [Real.exp_neg]
    have hexp_pos : 0 < Real.exp (c * u) := Real.exp_pos _
    rw [← div_eq_mul_inv, div_le_one hexp_pos]
    have h1 : c ^ 30 * L ^ 6 / (Nat.factorial 30 : ℝ) ≤ Real.exp (c * u) := by
      rw [← hu30, ← mul_pow]; exact hfac
    have h2 : 2 * C * L ^ 5 ≤ c ^ 30 * L ^ 6 / (Nat.factorial 30 : ℝ) := by
      rw [le_div_iff₀ hf30]
      have hD' : 2 * C * (Nat.factorial 30 : ℝ) ≤ c ^ 30 * L := by
        have := hLD
        rw [hD, div_le_iff₀ (by positivity)] at this
        linarith
      have hL5 : 0 ≤ L ^ 5 := by positivity
      calc 2 * C * L ^ 5 * (Nat.factorial 30 : ℝ) = (2 * C * (Nat.factorial 30 : ℝ)) * L ^ 5 := by ring
        _ ≤ (c ^ 30 * L) * L ^ 5 := mul_le_mul_of_nonneg_right hD' hL5
        _ = c ^ 30 * L ^ 6 := by ring
    linarith
  calc _ ≤ _ := hunion
    _ ≤ ∑ _j ∈ Finset.range (k + 1), 2 * C * Real.exp (-(c * u)) := Finset.sum_le_sum hterm
    _ = ((k : ℝ) + 1) * (2 * C * Real.exp (-(c * u))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ L * (2 * C * Real.exp (-(c * u))) :=
        mul_le_mul_of_nonneg_right hk1 (by positivity)
    _ ≤ L ^ (-4 : ℝ) := by
        have hL4 : L ^ (-4 : ℝ) = (L ^ 4)⁻¹ := by
          rw [Real.rpow_neg hLpos.le]; norm_cast
        have e : L * (2 * C * Real.exp (-(c * u))) = (2 * C * L ^ 5 * Real.exp (-(c * u))) / L ^ 4 := by
          field_simp
        rw [e, hL4, div_le_iff₀ (by positivity), inv_mul_cancel₀ (by positivity)]
        exact hkey

end Family

end GGMCollatz
