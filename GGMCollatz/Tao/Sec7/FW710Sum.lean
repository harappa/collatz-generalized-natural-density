import GGMCollatz.Tao.Sec7.FWEnc

/-!
# Summation tools for Lemma 7.10: row sums of Gaussian weights, and sums over separated points

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/ManyTriangles.lean`
(the ideas of `sum_range_Gweight_le`, `tsum_int_Gweight_le`, `separated_Gweight_tsum_le`);
generalized to the GGM family (p, q, r). Modified: the explicit constants of tao-collatz are not carried over, and the proofs were rebuilt (with sums in `ℝ≥0∞`).

* `tsum_exp_abs_le`: `Σ_{k ∈ ℕ} e^{-a|k - μ|} ≤ 2/(1 - e^{-a})`.
* `tsum_indicator_abs_le`: `#{k ∈ ℕ : |k - μ| ≤ τ} ≤ 2τ + 1`.
* `tsum_Gweight_le`: `Σ_k G_t(c(k - μ)) ≤ K √t` (`t ≥ 1`, with `K` independent of `μ`).
* `sparse_sum_le`: for `f` decreasing in the distance from `μ`, the sum over a `d`-separated set of points is
  `≤ 2B + (2/d) Σ_k f(k)`.
* `Family.FW.T710.col_sparse_le`: the probability that the column of the first-passage endpoint lies in a `d`-separated set is
  `≤ K(1/√(1+s) + 1/d)` (from the column form `fpDist_col_le` of Lemma 7.7).
-/

open scoped ENNReal

namespace GGMCollatz

namespace T710

/-- `1/(1 - e^{-a}) ≤ 1 + 1/a` (`a > 0`). -/
theorem one_div_one_sub_exp_neg_le {a : ℝ} (ha : 0 < a) :
    1 / (1 - Real.exp (-a)) ≤ 1 + 1 / a := by
  have h1 : 1 + a ≤ Real.exp a := by linarith [Real.add_one_le_exp a]
  have hexp : Real.exp (-a) ≤ 1 / (1 + a) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by linarith) h1
  have hpos : a / (1 + a) ≤ 1 - Real.exp (-a) := by
    have : 1 - 1 / (1 + a) = a / (1 + a) := by field_simp; ring
    linarith
  have hapos : 0 < a / (1 + a) := by positivity
  calc 1 / (1 - Real.exp (-a)) ≤ 1 / (a / (1 + a)) :=
        one_div_le_one_div_of_le hapos hpos
    _ = 1 + 1 / a := by field_simp; ring

/-- Reversed finite geometric series: `Σ_{k < N} r^{N-1-k} ≤ 1/(1-r)`. -/
theorem geom_head_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, r ^ (N - 1 - k) ≤ 1 / (1 - r) := by
  rw [Finset.sum_range_reflect (fun i => r ^ i) N]
  have hs := summable_geometric_of_lt_one h0 h1
  calc ∑ i ∈ Finset.range N, r ^ i ≤ ∑' i, r ^ i :=
        hs.sum_le_tsum _ (fun i _ => pow_nonneg h0 i)
    _ = 1 / (1 - r) := by rw [tsum_geometric_of_lt_one h0 h1, one_div]

/-- **Exponential row sum**: `Σ_{k ∈ ℕ} e^{-a|k - μ|} ≤ 2/(1 - e^{-a})`. -/
theorem tsum_exp_abs_le {a : ℝ} (ha : 0 < a) (μ : ℝ) :
    ∑' k : ℕ, ENNReal.ofReal (Real.exp (-a * |(k : ℝ) - μ|))
      ≤ ENNReal.ofReal (2 / (1 - Real.exp (-a))) := by
  set r := Real.exp (-a) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by rw [hrdef, Real.exp_lt_one_iff]; linarith
  set N : ℕ := ⌈μ⌉₊ with hN
  have hpt : ∀ k : ℕ, ENNReal.ofReal (Real.exp (-a * |(k : ℝ) - μ|))
      ≤ ENNReal.ofReal (if μ ≤ (k : ℝ) then Real.exp (-a * ((k : ℝ) - μ)) else 0)
        + (if k < N then ENNReal.ofReal (r ^ (N - 1 - k)) else 0) := by
    intro k
    by_cases hk : μ ≤ (k : ℝ)
    · rw [if_pos hk, abs_of_nonneg (by linarith)]
      exact le_add_right le_rfl
    · push Not at hk
      have hkN : k < N := Nat.lt_ceil.mpr hk
      rw [if_neg (by linarith), if_pos hkN, ENNReal.ofReal_zero, zero_add]
      apply ENNReal.ofReal_le_ofReal
      rw [abs_of_neg (by linarith), hrdef, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hμ0 : 0 ≤ μ := le_trans (Nat.cast_nonneg k) hk.le
      have hNμ : (N : ℝ) < μ + 1 := Nat.ceil_lt_add_one hμ0
      have hcast : ((N - 1 - k : ℕ) : ℝ) = (N : ℝ) - 1 - k := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast; ring
      rw [hcast]
      nlinarith
  calc ∑' k : ℕ, ENNReal.ofReal (Real.exp (-a * |(k : ℝ) - μ|))
      ≤ ∑' k : ℕ, (ENNReal.ofReal (if μ ≤ (k : ℝ) then Real.exp (-a * ((k : ℝ) - μ)) else 0)
          + (if k < N then ENNReal.ofReal (r ^ (N - 1 - k)) else 0)) :=
        ENNReal.tsum_le_tsum hpt
    _ = ∑' k : ℕ, ENNReal.ofReal (if μ ≤ (k : ℝ) then Real.exp (-a * ((k : ℝ) - μ)) else 0)
          + ∑' k : ℕ, (if k < N then ENNReal.ofReal (r ^ (N - 1 - k)) else 0) :=
        ENNReal.tsum_add
    _ ≤ ENNReal.ofReal (1 / (1 - r)) + ENNReal.ofReal (1 / (1 - r)) := by
        apply add_le_add
        · rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by split_ifs <;> positivity)
            (Family.WE.geom_tail_summable ha μ)]
          exact ENNReal.ofReal_le_ofReal (Family.WE.geom_tail_le ha μ)
        · rw [tsum_eq_sum (s := Finset.range N) (fun k hk => by
            rw [if_neg (by simpa using hk)])]
          rw [Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk)),
            ← ENNReal.ofReal_sum_of_nonneg (fun k _ => pow_nonneg hr0 _)]
          exact ENNReal.ofReal_le_ofReal (geom_head_le hr0 hr1 N)
    _ = ENNReal.ofReal (2 / (1 - r)) := by
        have h1r : 0 < 1 - r := by linarith
        have h1r' : 0 ≤ 1 / (1 - r) := by positivity
        rw [← ENNReal.ofReal_add h1r' h1r']
        congr 1; ring

/-- **Number of nearby points**: `#{k ∈ ℕ : |k - μ| ≤ τ} ≤ 2τ + 1`. -/
theorem tsum_indicator_abs_le (μ τ : ℝ) (hτ : 0 ≤ τ) :
    ∑' k : ℕ, (if |(k : ℝ) - μ| ≤ τ then (1 : ℝ≥0∞) else 0) ≤ ENNReal.ofReal (2 * τ + 1) := by
  set a : ℕ := ⌈μ - τ⌉₊ with ha
  set b : ℕ := ⌊μ + τ⌋₊ + 1 with hb
  have hsupp : ∀ k ∉ Finset.Ico a b, (if |(k : ℝ) - μ| ≤ τ then (1 : ℝ≥0∞) else 0) = 0 := by
    intro k hk
    rw [if_neg]
    intro hle
    apply hk
    rw [abs_le] at hle
    rw [Finset.mem_Ico]
    constructor
    · exact Nat.ceil_le.mpr (by linarith)
    · have : k ≤ ⌊μ + τ⌋₊ := Nat.le_floor (by linarith)
      omega
  rw [tsum_eq_sum hsupp]
  calc ∑ k ∈ Finset.Ico a b, (if |(k : ℝ) - μ| ≤ τ then (1 : ℝ≥0∞) else 0)
      ≤ ∑ k ∈ Finset.Ico a b, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun k _ => by split_ifs <;> simp
    _ = ((b - a : ℕ) : ℝ≥0∞) := by rw [Finset.sum_const, Nat.card_Ico]; simp
    _ ≤ ENNReal.ofReal (2 * τ + 1) := by
        rw [← ENNReal.ofReal_natCast]
        apply ENNReal.ofReal_le_ofReal
        rcases le_or_gt b a with hba | hab
        · rw [Nat.sub_eq_zero_of_le hba]; push_cast; linarith
        · rw [Nat.cast_sub hab.le]
          have ha' : μ - τ ≤ (a : ℝ) := Nat.le_ceil _
          have hb' : ((⌊μ + τ⌋₊ : ℕ) : ℝ) ≤ max (μ + τ) 0 := by
            rcases le_or_gt 0 (μ + τ) with h | h
            · exact (Nat.floor_le h).trans (le_max_left _ _)
            · rw [Nat.floor_of_nonpos h.le]; simp
          have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
          rw [hb]; push_cast
          rcases le_or_gt 0 (μ + τ) with h | h
          · rw [max_eq_left h] at hb'; linarith
          · rw [max_eq_right h.le] at hb'; linarith

/-- **Row sum of Gaussian weights**: for `t ≥ 1`, `Σ_{k ∈ ℕ} G_t(c(k - μ)) ≤ K√t` (`K` depends only on `c`). -/
theorem tsum_Gweight_le {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → ∀ μ : ℝ,
      ∑' k : ℕ, ENNReal.ofReal (Sec7.Gweight t (c * ((k : ℝ) - μ)))
        ≤ ENNReal.ofReal (K * Real.sqrt t) := by
  have hr1 : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hr1' : 0 < 1 - Real.exp (-c) := by linarith
  refine ⟨4 / c + 3 + 2 / (1 - Real.exp (-c)), by positivity, ?_⟩
  intro t ht μ
  have ht0 : 0 < t := by linarith
  set st := Real.sqrt t with hst
  have hst1 : 1 ≤ st := by rw [hst, Real.one_le_sqrt]; exact ht
  have hstpos : 0 < st := by linarith
  have hstsq : st ^ 2 = t := Real.sq_sqrt ht0.le
  set a := c / st with hadef
  have hapos : 0 < a := by positivity
  -- pointwise decomposition: `G_t(cu) ≤ 1_{|u| ≤ √t/c} + e^{-a|u|} + e^{-c|u|}`
  have hpt : ∀ k : ℕ, ENNReal.ofReal (Sec7.Gweight t (c * ((k : ℝ) - μ)))
      ≤ ((if |(k : ℝ) - μ| ≤ st / c then (1 : ℝ≥0∞) else 0)
          + ENNReal.ofReal (Real.exp (-a * |(k : ℝ) - μ|)))
        + ENNReal.ofReal (Real.exp (-c * |(k : ℝ) - μ|)) := by
    intro k
    set u := (k : ℝ) - μ with hu
    unfold Sec7.Gweight
    rw [ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
    apply add_le_add
    · by_cases hsmall : |u| ≤ st / c
      · rw [if_pos hsmall]
        refine le_trans ?_ (le_add_right le_rfl)
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        rw [Real.exp_le_one_iff]
        have : 0 ≤ (c * u) ^ 2 / t := by positivity
        linarith [neg_div t ((c * u) ^ 2)]
      · rw [if_neg hsmall, zero_add]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        push Not at hsmall
        -- since `v = c|u|/√t > 1`, `v² ≥ v`
        set v := c * |u| / st with hv
        have hv1 : 1 < v := by
          rw [hv, lt_div_iff₀ hstpos]
          rw [div_lt_iff₀ hc] at hsmall
          linarith
        have hsq : (c * u) ^ 2 / t = v ^ 2 := by
          rw [hv, div_pow, hstsq, mul_pow, mul_pow, sq_abs]
        have hav : a * |u| = v := by rw [hadef, hv]; ring
        rw [neg_div, hsq, neg_mul, hav]
        nlinarith
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      rw [abs_mul, abs_of_pos hc]
      linarith
  calc ∑' k : ℕ, ENNReal.ofReal (Sec7.Gweight t (c * ((k : ℝ) - μ)))
      ≤ ∑' k : ℕ, (((if |(k : ℝ) - μ| ≤ st / c then (1 : ℝ≥0∞) else 0)
          + ENNReal.ofReal (Real.exp (-a * |(k : ℝ) - μ|)))
        + ENNReal.ofReal (Real.exp (-c * |(k : ℝ) - μ|))) := ENNReal.tsum_le_tsum hpt
    _ = (∑' k : ℕ, (if |(k : ℝ) - μ| ≤ st / c then (1 : ℝ≥0∞) else 0)
          + ∑' k : ℕ, ENNReal.ofReal (Real.exp (-a * |(k : ℝ) - μ|)))
        + ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * |(k : ℝ) - μ|)) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ (ENNReal.ofReal (2 * (st / c) + 1) + ENNReal.ofReal (2 / (1 - Real.exp (-a))))
        + ENNReal.ofReal (2 / (1 - Real.exp (-c))) :=
        add_le_add (add_le_add (tsum_indicator_abs_le μ (st / c) (by positivity))
          (tsum_exp_abs_le hapos μ)) (tsum_exp_abs_le hc μ)
    _ ≤ ENNReal.ofReal ((4 / c + 3 + 2 / (1 - Real.exp (-c))) * st) := by
        have hra : 0 < 1 - Real.exp (-a) := by
          have : Real.exp (-a) < 1 := by rw [Real.exp_lt_one_iff]; linarith
          linarith
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have h1 : 2 / (1 - Real.exp (-a)) ≤ 2 * (1 + st / c) := by
          have := one_div_one_sub_exp_neg_le hapos
          rw [hadef, one_div_div] at this
          calc 2 / (1 - Real.exp (-a)) = 2 * (1 / (1 - Real.exp (-a))) := by ring
            _ ≤ 2 * (1 + st / c) := by linarith
        have h2 : 2 / (1 - Real.exp (-c)) ≤ 2 / (1 - Real.exp (-c)) * st := by
          have : 0 ≤ 2 / (1 - Real.exp (-c)) := by positivity
          nlinarith
        have h3 : (3 : ℝ) ≤ 3 * st := by linarith
        have h4 : 2 * (st / c) + 2 * (st / c) = 4 / c * st := by ring
        nlinarith

/-- **Sum over separated points**: for `f ≤ B` decreasing in the distance from `μ`, the sum over a set `S` of points
mutually at distance `≥ d` is `≤ 2B + (2/d) Σ_k f(k)`. -/
theorem sparse_sum_le (f : ℕ → ℝ≥0∞) (μ : ℝ) (hμ : 0 ≤ μ) (B : ℝ≥0∞) (hB : ∀ k, f k ≤ B)
    (hmono : ∀ k k' : ℕ, |(k' : ℝ) - μ| ≤ |(k : ℝ) - μ| → f k ≤ f k')
    (d : ℕ) (hd : 1 ≤ d) (S : Set ℕ) (hS : ∀ a ∈ S, ∀ b ∈ S, a < b → a + d ≤ b) :
    ∑' k, S.indicator f k ≤ 2 * B + 2 * (d : ℝ≥0∞)⁻¹ * ∑' k, f k := by
  classical
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hdtop : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top d
  set SR : Set ℕ := {k | k ∈ S ∧ μ + d ≤ (k : ℝ)} with hSR
  set SL : Set ℕ := {k | k ∈ S ∧ (k : ℝ) + d ≤ μ} with hSL
  set I1 : Set ℕ := {k | k ∈ S ∧ μ - d < (k : ℝ) ∧ (k : ℝ) ≤ μ} with hI1
  set I2 : Set ℕ := {k | k ∈ S ∧ μ < (k : ℝ) ∧ (k : ℝ) < μ + d} with hI2
  -- pointwise decomposition
  have hpt : ∀ k, S.indicator f k
      ≤ SR.indicator f k + SL.indicator f k + (I1.indicator f k + I2.indicator f k) := by
    intro k
    by_cases hk : k ∈ S
    · rw [Set.indicator_of_mem hk]
      by_cases h1 : μ + d ≤ (k : ℝ)
      · rw [Set.indicator_of_mem (show k ∈ SR from ⟨hk, h1⟩)]
        exact le_trans (le_add_right le_rfl) (le_add_right le_rfl)
      by_cases h2 : (k : ℝ) + d ≤ μ
      · rw [Set.indicator_of_mem (show k ∈ SL from ⟨hk, h2⟩)]
        exact le_trans (le_add_left le_rfl) (le_add_right le_rfl)
      push Not at h1 h2
      by_cases h3 : (k : ℝ) ≤ μ
      · rw [Set.indicator_of_mem (show k ∈ I1 from ⟨hk, by linarith, h3⟩)]
        exact le_trans (le_add_right le_rfl) (le_add_left le_rfl)
      · push Not at h3
        rw [Set.indicator_of_mem (show k ∈ I2 from ⟨hk, h3, h1⟩)]
        exact le_trans (le_add_left le_rfl) (le_add_left le_rfl)
    · rw [Set.indicator_of_notMem hk]; exact zero_le
  -- if the subset has at most one point, the sum is `≤ B`
  have hsub : ∀ A : Set ℕ, A.Subsingleton → ∑' k, A.indicator f k ≤ B := by
    intro A hA
    rcases hA.eq_empty_or_singleton with h | ⟨a, rfl⟩
    · rw [h]; simp
    · rw [tsum_eq_single a (fun b hb => Set.indicator_of_notMem (by simpa using hb) f),
        Set.indicator_of_mem (Set.mem_singleton a)]
      exact hB a
  have hI1s : I1.Subsingleton := by
    intro a ha b hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hab
    · have := hS a ha.1 b hb.1 hab
      have : (a : ℝ) + d ≤ b := by exact_mod_cast this
      linarith [ha.2.1, hb.2.2]
    · have := hS b hb.1 a ha.1 hab
      have : (b : ℝ) + d ≤ a := by exact_mod_cast this
      linarith [hb.2.1, ha.2.2]
  have hI2s : I2.Subsingleton := by
    intro a ha b hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hab
    · have := hS a ha.1 b hb.1 hab
      have : (a : ℝ) + d ≤ b := by exact_mod_cast this
      linarith [ha.2.1, hb.2.2]
    · have := hS b hb.1 a ha.1 hab
      have : (b : ℝ) + d ≤ a := by exact_mod_cast this
      linarith [hb.2.1, ha.2.2]
  -- right part: `d f(k) ≤ Σ_{i<d} f(k-i)`; after rearranging, the multiplicity is at most 1
  have hR : ∑' k, SR.indicator f k ≤ (d : ℝ≥0∞)⁻¹ * ∑' k, f k := by
    have hpt' : ∀ k, SR.indicator f k
        ≤ (d : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range d, (if k ∈ SR then f (k - i) else 0) := by
      intro k
      by_cases hk : k ∈ SR
      · rw [Set.indicator_of_mem hk]
        simp only [if_pos hk]
        have hkd : d ≤ k := by
          have : (d : ℝ) ≤ k := by linarith [hk.2]
          exact_mod_cast this
        have hle : (d : ℝ≥0∞) * f k ≤ ∑ i ∈ Finset.range d, f (k - i) := by
          calc (d : ℝ≥0∞) * f k = ∑ i ∈ Finset.range d, f k := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            _ ≤ ∑ i ∈ Finset.range d, f (k - i) := by
                apply Finset.sum_le_sum
                intro i hi
                have hi' : i < d := Finset.mem_range.mp hi
                apply hmono
                rw [Nat.cast_sub (by omega)]
                have hk2 : μ + d ≤ (k : ℝ) := hk.2
                have hiR : (i : ℝ) < d := by exact_mod_cast hi'
                have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
                rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
                linarith
        calc f k = (d : ℝ≥0∞)⁻¹ * ((d : ℝ≥0∞) * f k) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel hd0 hdtop, one_mul]
          _ ≤ _ := by gcongr
      · rw [Set.indicator_of_notMem hk]; exact zero_le
    have hshift : ∀ i ∈ Finset.range d,
        ∑' k, (if k ∈ SR then f (k - i) else 0) = ∑' k', (if k' + i ∈ SR then f k' else 0) := by
      intro i hi
      have hi' : i < d := Finset.mem_range.mp hi
      have hinj : Function.Injective (fun k' : ℕ => k' + i) := fun a b h => by simpa using h
      have hsupp : Function.support (fun k => if k ∈ SR then f (k - i) else 0)
          ⊆ Set.range (fun k' : ℕ => k' + i) := by
        intro k hk
        have hk' : k ∈ SR := by
          by_contra hc
          exact hk (by simp [hc])
        have : d ≤ k := by
          have : (d : ℝ) ≤ k := by linarith [hk'.2]
          exact_mod_cast this
        exact ⟨k - i, by simp only; omega⟩
      rw [← hinj.tsum_eq hsupp]
      exact tsum_congr fun k' => by simp
    have hcount : ∀ k', ∑ i ∈ Finset.range d, (if k' + i ∈ SR then f k' else 0) ≤ f k' := by
      intro k'
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hc : (Finset.filter (fun i => k' + i ∈ SR) (Finset.range d)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        simp only [Finset.mem_filter, Finset.mem_range] at ha hb
        by_contra hne
        rcases lt_or_gt_of_ne hne with hab | hab
        · have := hS (k' + a) ha.2.1 (k' + b) hb.2.1 (by omega); omega
        · have := hS (k' + b) hb.2.1 (k' + a) ha.2.1 (by omega); omega
      calc ((Finset.filter (fun i => k' + i ∈ SR) (Finset.range d)).card : ℝ≥0∞) * f k'
          ≤ 1 * f k' := by gcongr; exact_mod_cast hc
        _ = f k' := one_mul _
    calc ∑' k, SR.indicator f k
        ≤ ∑' k, (d : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range d, (if k ∈ SR then f (k - i) else 0) :=
          ENNReal.tsum_le_tsum hpt'
      _ = (d : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range d, ∑' k, (if k ∈ SR then f (k - i) else 0) := by
          rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
      _ = (d : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range d, ∑' k', (if k' + i ∈ SR then f k' else 0) := by
          rw [Finset.sum_congr rfl hshift]
      _ = (d : ℝ≥0∞)⁻¹ * ∑' k', ∑ i ∈ Finset.range d, (if k' + i ∈ SR then f k' else 0) := by
          rw [Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
      _ ≤ (d : ℝ≥0∞)⁻¹ * ∑' k', f k' := by gcongr with k'; exact hcount k'
  -- left part: `d f(k) ≤ Σ_{i<d} f(k+i)`
  have hL : ∑' k, SL.indicator f k ≤ (d : ℝ≥0∞)⁻¹ * ∑' k, f k := by
    have hpt' : ∀ k, SL.indicator f k
        ≤ (d : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range d, (if k ∈ SL then f (k + i) else 0) := by
      intro k
      by_cases hk : k ∈ SL
      · rw [Set.indicator_of_mem hk]
        simp only [if_pos hk]
        have hle : (d : ℝ≥0∞) * f k ≤ ∑ i ∈ Finset.range d, f (k + i) := by
          calc (d : ℝ≥0∞) * f k = ∑ i ∈ Finset.range d, f k := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            _ ≤ ∑ i ∈ Finset.range d, f (k + i) := by
                apply Finset.sum_le_sum
                intro i hi
                have hi' : i < d := Finset.mem_range.mp hi
                apply hmono
                push_cast
                have hk2 : (k : ℝ) + d ≤ μ := hk.2
                have hiR : (i : ℝ) < d := by exact_mod_cast hi'
                have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
                rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
                linarith
        calc f k = (d : ℝ≥0∞)⁻¹ * ((d : ℝ≥0∞) * f k) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel hd0 hdtop, one_mul]
          _ ≤ _ := by gcongr
      · rw [Set.indicator_of_notMem hk]; exact zero_le
    have hshift : ∀ i ∈ Finset.range d,
        ∑' k, (if k ∈ SL then f (k + i) else 0)
          ≤ ∑' k', (if i ≤ k' ∧ k' - i ∈ SL then f k' else 0) := by
      intro i _
      have hinj : Function.Injective (fun k : ℕ => k + i) := fun a b h => by simpa using h
      calc ∑' k, (if k ∈ SL then f (k + i) else 0)
          = ∑' k, (fun k' => if i ≤ k' ∧ k' - i ∈ SL then f k' else 0) (k + i) := by
            refine tsum_congr fun k => ?_
            simp
        _ ≤ ∑' k', (if i ≤ k' ∧ k' - i ∈ SL then f k' else 0) :=
            ENNReal.tsum_comp_le_tsum_of_injective hinj _
    have hcount : ∀ k', ∑ i ∈ Finset.range d, (if i ≤ k' ∧ k' - i ∈ SL then f k' else 0)
        ≤ f k' := by
      intro k'
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hc : (Finset.filter (fun i => i ≤ k' ∧ k' - i ∈ SL) (Finset.range d)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        simp only [Finset.mem_filter, Finset.mem_range] at ha hb
        by_contra hne
        rcases lt_or_gt_of_ne hne with hab | hab
        · have := hS (k' - b) hb.2.2.1 (k' - a) ha.2.2.1 (by omega); omega
        · have := hS (k' - a) ha.2.2.1 (k' - b) hb.2.2.1 (by omega); omega
      calc ((Finset.filter (fun i => i ≤ k' ∧ k' - i ∈ SL) (Finset.range d)).card : ℝ≥0∞) * f k'
          ≤ 1 * f k' := by gcongr; exact_mod_cast hc
        _ = f k' := one_mul _
    calc ∑' k, SL.indicator f k
        ≤ ∑' k, (d : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range d, (if k ∈ SL then f (k + i) else 0) :=
          ENNReal.tsum_le_tsum hpt'
      _ = (d : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range d, ∑' k, (if k ∈ SL then f (k + i) else 0) := by
          rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
      _ ≤ (d : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range d,
            ∑' k', (if i ≤ k' ∧ k' - i ∈ SL then f k' else 0) :=
          mul_le_mul_right (Finset.sum_le_sum hshift) _
      _ = (d : ℝ≥0∞)⁻¹ * ∑' k', ∑ i ∈ Finset.range d,
            (if i ≤ k' ∧ k' - i ∈ SL then f k' else 0) := by
          rw [Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
      _ ≤ (d : ℝ≥0∞)⁻¹ * ∑' k', f k' := by gcongr with k'; exact hcount k'
  calc ∑' k, S.indicator f k
      ≤ ∑' k, (SR.indicator f k + SL.indicator f k + (I1.indicator f k + I2.indicator f k)) :=
        ENNReal.tsum_le_tsum hpt
    _ = ∑' k, SR.indicator f k + ∑' k, SL.indicator f k
          + (∑' k, I1.indicator f k + ∑' k, I2.indicator f k) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ (d : ℝ≥0∞)⁻¹ * ∑' k, f k + (d : ℝ≥0∞)⁻¹ * ∑' k, f k + (B + B) :=
        add_le_add (add_le_add hR hL) (add_le_add (hsub I1 hI1s) (hsub I2 hI2s))
    _ = 2 * B + 2 * (d : ℝ≥0∞)⁻¹ * ∑' k, f k := by ring

end T710

namespace Family

namespace FW

namespace T710

variable (F : Family)

/-- `G_t(x)` is decreasing in `|x|` and `≤ 2`. -/
theorem Gweight_anti {t : ℝ} (ht : 0 < t) {x y : ℝ} (hxy : |x| ≤ |y|) :
    Sec7.Gweight t y ≤ Sec7.Gweight t x := by
  unfold Sec7.Gweight
  have hsq : x ^ 2 ≤ y ^ 2 := by
    rw [← sq_abs x, ← sq_abs y]
    exact pow_le_pow_left₀ (abs_nonneg x) hxy 2
  apply add_le_add
  · apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right hsq ht.le
  · apply Real.exp_le_exp.mpr
    linarith

theorem Gweight_le_two {t : ℝ} (ht : 0 < t) (x : ℝ) : Sec7.Gweight t x ≤ 2 := by
  unfold Sec7.Gweight
  have h1 : Real.exp (-(x ^ 2) / t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ x ^ 2 / t := by positivity
    rw [neg_div]; linarith
  have h2 : Real.exp (-|x|) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith [abs_nonneg x]
  linarith

/-- **Probability of lying in a separated set of columns** (from the column form of Lemma 7.7): the probability that the column of the first-passage endpoint
lies in a set `S` of points mutually at distance `≥ d` is `≤ K(1/√(1+s) + 1/d)` (`K` independent of `s`, `d`, `S`). -/
theorem col_sparse_le : ∃ K : ℝ, 0 < K ∧ ∀ (s d : ℕ), 1 ≤ d → ∀ (S : Set ℕ),
    (∀ a ∈ S, ∀ b ∈ S, a < b → a + d ≤ b) →
    ∑' e : ℕ × ℤ, F.fpDist s e * S.indicator (1 : ℕ → ℝ≥0∞) e.1
      ≤ ENNReal.ofReal (K * (1 / Real.sqrt (1 + s) + 1 / d)) := by
  obtain ⟨c, hc, C', hC', hcol⟩ := F.fpDist_col_le
  obtain ⟨Kr, hKr, hrow⟩ := GGMCollatz.T710.tsum_Gweight_le hc
  refine ⟨4 * C' + 2 * C' * Kr, by positivity, ?_⟩
  intro s d hd S hS
  set t : ℝ := 1 + (s : ℝ) with htdef
  have ht1 : 1 ≤ t := by rw [htdef]; linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
  have ht0 : 0 < t := by linarith
  set μ : ℝ := (s : ℝ) * F.slopeInv with hμ
  have hμ0 : 0 ≤ μ := mul_nonneg (Nat.cast_nonneg s) (Family.WE.slopeInv_nonneg F)
  set G : ℕ → ℝ := fun k => Sec7.Gweight t (c * ((k : ℝ) - μ)) with hG
  have hsqt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  set colm : ℕ → ℝ≥0∞ := fun k => ∑' l : ℤ, F.fpDist s (k, l) with hcolm
  -- the column marginal mass
  have hcolm_le : ∀ k, colm k ≤ ENNReal.ofReal (C' / Real.sqrt t) * ENNReal.ofReal (G k) := by
    intro k
    have hne : colm k ≠ ⊤ := by
      refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      calc colm k = ∑' l : ℤ, F.fpDist s (k, l) := rfl
        _ ≤ ∑' e : ℕ × ℤ, F.fpDist s e :=
            ENNReal.tsum_comp_le_tsum_of_injective (fun a b h => by simpa using h) _
        _ = 1 := (F.fpDist s).tsum_coe
    rw [← ENNReal.ofReal_toReal hne, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [hcolm, ENNReal.tsum_toReal_eq (fun l => PMF.apply_ne_top _ _)]
    refine (hcol s k).trans (le_of_eq ?_)
    simp only [hG, hμ, htdef]
    ring
  -- rewriting the sum
  have hsplit : ∑' e : ℕ × ℤ, F.fpDist s e * S.indicator (1 : ℕ → ℝ≥0∞) e.1
      = ∑' k : ℕ, S.indicator colm k := by
    rw [ENNReal.tsum_prod']
    refine tsum_congr fun k => ?_
    by_cases hk : k ∈ S
    · rw [Set.indicator_of_mem hk]
      refine tsum_congr fun b => ?_
      show F.fpDist s (k, b) * S.indicator 1 k = _
      rw [Set.indicator_of_mem hk, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem hk]
      refine ENNReal.tsum_eq_zero.mpr fun b => ?_
      show F.fpDist s (k, b) * S.indicator 1 k = 0
      rw [Set.indicator_of_notMem hk, mul_zero]
  rw [hsplit]
  set f : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (G k) with hf
  have hfB : ∀ k, f k ≤ ENNReal.ofReal 2 := fun k =>
    ENNReal.ofReal_le_ofReal (Gweight_le_two ht0 _)
  have hfmono : ∀ k k' : ℕ, |(k' : ℝ) - μ| ≤ |(k : ℝ) - μ| → f k ≤ f k' := by
    intro k k' h
    apply ENNReal.ofReal_le_ofReal
    apply Gweight_anti ht0
    rw [abs_mul, abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left h hc.le
  have hsparse := GGMCollatz.T710.sparse_sum_le f μ hμ0 (ENNReal.ofReal 2) hfB hfmono d hd S hS
  have hrowS : ∑' k, f k ≤ ENNReal.ofReal (Kr * Real.sqrt t) := hrow t ht1 μ
  have hind : ∀ k, S.indicator colm k
      ≤ ENNReal.ofReal (C' / Real.sqrt t) * S.indicator f k := by
    intro k
    by_cases hk : k ∈ S
    · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]; exact hcolm_le k
    · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, mul_zero]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdinv : ((d : ℝ≥0∞))⁻¹ = ENNReal.ofReal (1 / d) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos hdR, ENNReal.ofReal_natCast]
  calc ∑' k, S.indicator colm k
      ≤ ∑' k, ENNReal.ofReal (C' / Real.sqrt t) * S.indicator f k := ENNReal.tsum_le_tsum hind
    _ = ENNReal.ofReal (C' / Real.sqrt t) * ∑' k, S.indicator f k := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (C' / Real.sqrt t)
          * (2 * ENNReal.ofReal 2 + 2 * ((d : ℝ≥0∞))⁻¹ * ENNReal.ofReal (Kr * Real.sqrt t)) := by
        gcongr
        exact hsparse.trans (by gcongr)
    _ = ENNReal.ofReal (C' / Real.sqrt t * (2 * 2 + 2 * (1 / d) * (Kr * Real.sqrt t))) := by
        have hin : 2 * ENNReal.ofReal 2 + 2 * ((d : ℝ≥0∞))⁻¹ * ENNReal.ofReal (Kr * Real.sqrt t)
            = ENNReal.ofReal (2 * 2 + 2 * (1 / d) * (Kr * Real.sqrt t)) := by
          rw [hdinv, ENNReal.ofReal_add (by norm_num) (by positivity),
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (1 / d)),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        rw [hin, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal ((4 * C' + 2 * C' * Kr) * (1 / Real.sqrt t + 1 / d)) := by
        apply ENNReal.ofReal_le_ofReal
        have e1 : C' / Real.sqrt t * (2 * 2 + 2 * (1 / d) * (Kr * Real.sqrt t))
            = 4 * C' * (1 / Real.sqrt t) + 2 * C' * Kr * (1 / d) := by
          field_simp
          ring
        rw [e1]
        have h1 : 0 ≤ 1 / Real.sqrt t := by positivity
        have h2 : 0 ≤ 1 / (d : ℝ) := by positivity
        nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hC'.le) hKr.le,
          mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hC'.le]

end T710

end FW

end Family

end GGMCollatz
