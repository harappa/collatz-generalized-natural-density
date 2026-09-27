import GGMCollatz.Tao.Sec7.HLFpConv
import GGMCollatz.Tao.Prob.LocalInstances

/-!
# Analytic lemmas: arithmetic of `Gweight`, arithmetic-progression sums, convolution of exponentials with `1/√(1+m)`

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/FpLocation.lean`, general lemmas
(`Gweight_anti`, `exp_neg_le_four_div_sq`, `one_sub_exp_neg_inv_le_one_add`, `sum_range_geom_le`,
`sum_range_exp_neg_sq_le`, `exp_neg_abs_le_Gweight`, `Gweight_mono_t`, `Gweight_two_le`, `sum_abs_int_le`,
`sum_exp_geom_le`, `Gweight_shift`, `conv_Gweight_exp`, `K_sqrtExp`, `sum_sqrt_exp_le_explicitC`). Modified: the proofs
are unchanged (they do not depend on `p`, `q`, `r`); used for Lemma 7.7 in the generalization to the GGM family. Placed in
the namespace `GGMCollatz.HL` to avoid name clashes (`Gweight` is `GGMCollatz.Gweight`, definitionally equal to `Sec7.Gweight`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace HL

/-- `Gweight t` is antitone in the (nonnegative) argument. -/
theorem Gweight_anti {t x y : ℝ} (ht : 0 < t) (hx : 0 ≤ x) (hxy : x ≤ y) :
    Gweight t y ≤ Gweight t x := by
  unfold Gweight
  have hy : 0 ≤ y := hx.trans hxy
  have h1 : Real.exp (-(y ^ 2) / t) ≤ Real.exp (-(x ^ 2) / t) := by
    apply Real.exp_le_exp.mpr
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hinv : 0 < t⁻¹ := inv_pos.mpr ht
    nlinarith [mul_self_le_mul_self hx hxy, hinv]
  have h2 : Real.exp (-|y|) ≤ Real.exp (-|x|) := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg hx, abs_of_nonneg hy]
    linarith
  exact add_le_add h1 h2

/-- Crude super-polynomial decay: `e^{-u} ≤ 4/u²` (from `e^{u/2} ≥ 1 + u/2`). -/
theorem exp_neg_le_four_div_sq {u : ℝ} (hu : 0 < u) :
    Real.exp (-u) ≤ 4 / u ^ 2 := by
  have h2 : u ^ 2 / 4 ≤ Real.exp u := by
    have h1 : 1 + u / 2 ≤ Real.exp (u / 2) := by
      linarith [Real.add_one_le_exp (u / 2)]
    calc u ^ 2 / 4 = (u / 2) ^ 2 := by ring
      _ ≤ (1 + u / 2) ^ 2 := by nlinarith
      _ ≤ Real.exp (u / 2) ^ 2 := by nlinarith [Real.exp_pos (u / 2)]
      _ = Real.exp (u / 2) * Real.exp (u / 2) := sq _
      _ = Real.exp u := by rw [← Real.exp_add]; ring_nf
  rw [Real.exp_neg, le_div_iff₀ (by positivity : (0 : ℝ) < u ^ 2)]
  calc (Real.exp u)⁻¹ * u ^ 2 ≤ (Real.exp u)⁻¹ * (4 * Real.exp u) := by
        have hnn := inv_nonneg.mpr (Real.exp_pos u).le
        nlinarith
    _ = 4 := by field_simp

/-- Tail of the geometric-comparison bound: `(1 - e^{-u})⁻¹ ≤ 1 + 1/u`. -/
theorem one_sub_exp_neg_inv_le_one_add {u : ℝ} (hu : 0 < u) :
    (1 - Real.exp (-u))⁻¹ ≤ 1 + 1 / u := by
  have hlt : Real.exp (-u) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hkey : u / (u + 1) ≤ 1 - Real.exp (-u) := by
    have h1 : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
    have h2 : Real.exp (-u) ≤ (u + 1)⁻¹ := by
      rw [Real.exp_neg]
      exact inv_anti₀ (by linarith) h1
    have h3 : u / (u + 1) = 1 - (u + 1)⁻¹ := by
      field_simp
      ring
    linarith
  rw [inv_le_comm₀ (by linarith) (by positivity)]
  calc (1 + 1 / u)⁻¹ = u / (u + 1) := by
        rw [one_add_div hu.ne', inv_div]
    _ ≤ 1 - Real.exp (-u) := hkey


/-- Partial geometric sums are bounded by `(1-r)⁻¹`. -/
theorem sum_range_geom_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (N : ℕ) :
    ∑ m ∈ Finset.range N, r ^ m ≤ (1 - r)⁻¹ := by
  have hsum : Summable fun m : ℕ => r ^ m := summable_geometric_of_lt_one h0 h1
  calc ∑ m ∈ Finset.range N, r ^ m
      ≤ ∑' m : ℕ, r ^ m :=
        hsum.sum_le_tsum _ (fun m _ => pow_nonneg h0 m)
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one h0 h1

/-- **Gaussian AP sum, elementary form**: `∑_{m<N} e^{-βm²} ≤ 3 + 2/√β`.
`M`-split: `≍ 1/√β` unit terms, then `m² ≥ Mm` turns the tail geometric. -/
theorem sum_range_exp_neg_sq_le {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    ∑ m ∈ Finset.range N, Real.exp (-β * (m : ℝ) ^ 2) ≤ 3 + 2 / Real.sqrt β := by
  set M : ℕ := ⌊1 / Real.sqrt β⌋₊ + 1 with hM
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have hMge : 1 / Real.sqrt β ≤ (M : ℝ) := by
    rw [hM]
    push_cast
    exact (Nat.lt_floor_add_one _).le
  have hMle : (M : ℝ) ≤ 1 / Real.sqrt β + 1 := by
    rw [hM]
    push_cast
    have := Nat.floor_le (by positivity : (0:ℝ) ≤ 1 / Real.sqrt β)
    linarith
  have hM0 : (0:ℝ) < (M : ℝ) := by
    rw [hM]
    push_cast
    positivity
  set r : ℝ := Real.exp (-(β * M)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    nlinarith [mul_pos hβ hM0]
  have hterm : ∀ m : ℕ, Real.exp (-β * (m : ℝ) ^ 2)
      ≤ (if m ≤ M then 1 else 0) + r ^ m := by
    intro m
    by_cases hm : m ≤ M
    · rw [if_pos hm]
      have hle1 : Real.exp (-β * (m : ℝ) ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (m : ℝ)])
      have hrm : (0:ℝ) ≤ r ^ m := pow_nonneg hr0 m
      linarith
    · rw [if_neg hm]
      have hMm : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.le_of_not_lt (by omega)
      have hexp : Real.exp (-β * (m : ℝ) ^ 2) ≤ r ^ m := by
        rw [hr, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have hm0 : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        nlinarith [mul_le_mul_of_nonneg_left hMm
          (mul_nonneg hβ.le hm0)]
      linarith
  calc ∑ m ∈ Finset.range N, Real.exp (-β * (m : ℝ) ^ 2)
      ≤ ∑ m ∈ Finset.range N, ((if m ≤ M then 1 else 0) + r ^ m) :=
        Finset.sum_le_sum fun m _ => hterm m
    _ = (∑ m ∈ Finset.range N, if m ≤ M then (1:ℝ) else 0)
        + ∑ m ∈ Finset.range N, r ^ m := Finset.sum_add_distrib
    _ ≤ ((M : ℝ) + 1) + (1 - r)⁻¹ := by
        gcongr
        · calc (∑ m ∈ Finset.range N, if m ≤ M then (1:ℝ) else 0)
              = (((Finset.range N).filter fun m => m ≤ M).card : ℝ) := by
                rw [Finset.sum_boole]
            _ ≤ ((Finset.range (M + 1)).card : ℝ) := by
                have hsub : (Finset.range N).filter (fun m => m ≤ M)
                    ⊆ Finset.range (M + 1) := by
                  intro m hm
                  have := (Finset.mem_filter.mp hm).2
                  exact Finset.mem_range.mpr (by omega)
                exact_mod_cast Finset.card_le_card hsub
            _ = (M : ℝ) + 1 := by
                rw [Finset.card_range]
                push_cast
                ring
        · exact sum_range_geom_le hr0 hr1 N
    _ ≤ (1 / Real.sqrt β + 1 + 1) + (1 + 1 / (β * M)) := by
        have hβM : (0:ℝ) < β * M := mul_pos hβ hM0
        have hinv := one_sub_exp_neg_inv_le_one_add hβM
        rw [hr]
        linarith
    _ ≤ 3 + 2 / Real.sqrt β := by
        have hsq : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ.le
        have hβM : Real.sqrt β ≤ β * M := by
          have hmul := mul_le_mul_of_nonneg_left hMge hβ.le
          calc Real.sqrt β = β * (1 / Real.sqrt β) := by
                rw [mul_one_div, eq_div_iff hsβ.ne']
                exact hsq
            _ ≤ β * M := hmul
        have h1 : 1 / (β * M) ≤ 1 / Real.sqrt β :=
          one_div_le_one_div_of_le hsβ hβM
        calc 1 / Real.sqrt β + 1 + 1 + (1 + 1 / (β * M))
            = 3 + (1 / Real.sqrt β + 1 / (β * M)) := by ring
          _ ≤ 3 + (1 / Real.sqrt β + 1 / Real.sqrt β) := by linarith
          _ = 3 + 2 / Real.sqrt β := by ring


/-- The exponential part alone lower-bounds `Gweight`. -/
theorem exp_neg_abs_le_Gweight (t x : ℝ) : Real.exp (-|x|) ≤ Gweight t x := by
  unfold Gweight
  linarith [(Real.exp_pos (-x ^ 2 / t)).le]

/-- `Gweight` is monotone in the time scale. -/
theorem Gweight_mono_t {t1 t2 : ℝ} (ht1 : 0 < t1) (ht : t1 ≤ t2) (x : ℝ) :
    Gweight t1 x ≤ Gweight t2 x := by
  unfold Gweight
  have ht2 : 0 < t2 := lt_of_lt_of_le ht1 ht
  have h1 : Real.exp (-x ^ 2 / t1) ≤ Real.exp (-x ^ 2 / t2) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg x) ht1 ht
  linarith

/-- At time scale `2` the Gaussian part is dominated by the exponential:
`Gweight 2 x ≤ 4·e^{-x/2}` for `x ≥ 0`. -/
theorem Gweight_two_le {x : ℝ} (hx : 0 ≤ x) : Gweight 2 x ≤ 4 * Real.exp (-x / 2) := by
  unfold Gweight
  have hg : Real.exp (-x ^ 2 / 2) ≤ 3 * Real.exp (-x / 2) := by
    rcases le_total x 1 with h1 | h1
    · have hhalf : (1 : ℝ) / 2 ≤ Real.exp (-x / 2) := by
        have := Real.add_one_le_exp (-x / 2)
        linarith
      have h1 : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      linarith
    · calc Real.exp (-x ^ 2 / 2) ≤ Real.exp (-x / 2) :=
            Real.exp_le_exp.mpr (by nlinarith)
        _ ≤ 3 * Real.exp (-x / 2) := by linarith [(Real.exp_pos (-x / 2)).le]
  have he : Real.exp (-|x|) ≤ Real.exp (-x / 2) := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg hx]
    linarith
  linarith

/-- Step-1 analogue of `sum_abs_AP_le`, with an integer (possibly negative)
centre: the offsets `|w - k|`, `k < J`, cover each value `m` at most twice. -/
theorem sum_abs_int_le {f : ℝ → ℝ} (hnn : ∀ u, 0 ≤ f u)
    (hanti : ∀ ⦃u v : ℝ⦄, 0 ≤ u → u ≤ v → f v ≤ f u)
    (w : ℤ) (J : ℕ) (hw : w.toNat < J) :
    ∑ k ∈ Finset.range J, f |(w : ℝ) - k| ≤ 2 * ∑ m ∈ Finset.range J, f m := by
  set q : ℕ := w.toNat with hq
  have hcast : ∀ k : ℕ, ∀ n : ℕ, ((n : ℤ) ≤ |w - (k : ℤ)|) →
      ((n : ℝ) ≤ |(w : ℝ) - (k : ℝ)|) := by
    intro k n h
    have h2 : ((n : ℤ) : ℝ) ≤ ((|w - (k : ℤ)| : ℤ) : ℝ) := Int.cast_le.mpr h
    push_cast at h2
    exact h2
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range J) (fun k => k ≤ q)]
  have hA : ∑ k ∈ (Finset.range J).filter (fun k => k ≤ q), f |(w : ℝ) - k|
      ≤ ∑ m ∈ Finset.range J, f m := by
    have hstep : ∀ k ∈ (Finset.range J).filter (fun k => k ≤ q),
        f |(w : ℝ) - k| ≤ f ((q - k : ℕ) : ℝ) := by
      intro k hk
      have hkq : k ≤ q := (Finset.mem_filter.mp hk).2
      refine hanti (by positivity) (hcast k _ ?_)
      rcases abs_cases (w - (k : ℤ)) with ⟨he, h0⟩ | ⟨he, h0⟩ <;> omega
    have hinj : ∀ x ∈ (Finset.range J).filter (fun k => k ≤ q),
        ∀ y ∈ (Finset.range J).filter (fun k => k ≤ q), q - x = q - y → x = y := by
      intro x hx y hy hxy
      have := (Finset.mem_filter.mp hx).2
      have := (Finset.mem_filter.mp hy).2
      omega
    have key : ∑ m ∈ ((Finset.range J).filter (fun k => k ≤ q)).image (fun k => q - k),
        f (m : ℝ)
        = ∑ k ∈ (Finset.range J).filter (fun k => k ≤ q), f ((q - k : ℕ) : ℝ) :=
      Finset.sum_image hinj
    calc ∑ k ∈ (Finset.range J).filter (fun k => k ≤ q), f |(w : ℝ) - k|
        ≤ ∑ k ∈ (Finset.range J).filter (fun k => k ≤ q), f ((q - k : ℕ) : ℝ) :=
          Finset.sum_le_sum hstep
      _ = ∑ m ∈ ((Finset.range J).filter (fun k => k ≤ q)).image (fun k => q - k),
            f (m : ℝ) := key.symm
      _ ≤ ∑ m ∈ Finset.range J, f m := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => hnn _
          intro m hm
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
          exact Finset.mem_range.mpr (by omega)
  have hB : ∑ k ∈ (Finset.range J).filter (fun k => ¬ k ≤ q), f |(w : ℝ) - k|
      ≤ ∑ m ∈ Finset.range J, f m := by
    have hstep : ∀ k ∈ (Finset.range J).filter (fun k => ¬ k ≤ q),
        f |(w : ℝ) - k| ≤ f ((k - (q + 1) : ℕ) : ℝ) := by
      intro k hk
      have hkq : q < k := Nat.lt_of_not_le (Finset.mem_filter.mp hk).2
      refine hanti (by positivity) (hcast k _ ?_)
      rcases abs_cases (w - (k : ℤ)) with ⟨he, h0⟩ | ⟨he, h0⟩ <;> omega
    have hinj : ∀ x ∈ (Finset.range J).filter (fun k => ¬ k ≤ q),
        ∀ y ∈ (Finset.range J).filter (fun k => ¬ k ≤ q),
          x - (q + 1) = y - (q + 1) → x = y := by
      intro x hx y hy hxy
      have := Nat.lt_of_not_le (Finset.mem_filter.mp hx).2
      have := Nat.lt_of_not_le (Finset.mem_filter.mp hy).2
      omega
    have key : ∑ m ∈ ((Finset.range J).filter (fun k => ¬ k ≤ q)).image
          (fun k => k - (q + 1)), f (m : ℝ)
        = ∑ k ∈ (Finset.range J).filter (fun k => ¬ k ≤ q), f ((k - (q + 1) : ℕ) : ℝ) :=
      Finset.sum_image hinj
    calc ∑ k ∈ (Finset.range J).filter (fun k => ¬ k ≤ q), f |(w : ℝ) - k|
        ≤ ∑ k ∈ (Finset.range J).filter (fun k => ¬ k ≤ q), f ((k - (q + 1) : ℕ) : ℝ) :=
          Finset.sum_le_sum hstep
      _ = ∑ m ∈ ((Finset.range J).filter (fun k => ¬ k ≤ q)).image
            (fun k => k - (q + 1)), f (m : ℝ) := key.symm
      _ ≤ ∑ m ∈ Finset.range J, f m := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => hnn _
          intro m hm
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
          have := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
          exact Finset.mem_range.mpr (by omega)
  linarith

/-- Geometric comparison: `∑_{m<J} e^{-γm} ≤ 1 + 1/γ`. -/
theorem sum_exp_geom_le {γ : ℝ} (hγ : 0 < γ) (J : ℕ) :
    ∑ m ∈ Finset.range J, Real.exp (-γ * m) ≤ 1 + 1 / γ := by
  have hterm : ∀ m : ℕ, Real.exp (-γ * m) = Real.exp (-γ) ^ m := by
    intro m
    rw [← Real.exp_nat_mul]
    exact congrArg Real.exp (by ring)
  rw [Finset.sum_congr rfl fun m _ => hterm m]
  have hr1 : Real.exp (-γ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  calc ∑ m ∈ Finset.range J, Real.exp (-γ) ^ m
      ≤ (1 - Real.exp (-γ))⁻¹ := sum_range_geom_le (Real.exp_pos _).le hr1 J
    _ ≤ 1 + 1 / γ := one_sub_exp_neg_inv_le_one_add hγ

/-- **Shift absorption**: recentring the `Gweight` argument by `δ` (and
widening the time scale) costs a factor `2·e^{c|δ|}` and half the decay
constant. -/
theorem Gweight_shift {t1 t2 c : ℝ} (ht1 : 0 < t1) (ht : t1 ≤ t2) (hc : 0 < c)
    (X δ : ℝ) :
    Gweight t1 (c * (X + δ)) ≤ 2 * Real.exp (c * |δ|) * Gweight t2 (c / 2 * X) := by
  have hE1 : (1 : ℝ) ≤ Real.exp (c * |δ|) :=
    Real.one_le_exp (by positivity)
  rcases le_total |X| (2 * |δ|) with hcase | hcase
  · -- near: crude bound 2, matched by the shift factor
    calc Gweight t1 (c * (X + δ)) ≤ 2 := Gweight_le_two _ _ ht1.le
      _ ≤ 2 * Real.exp (c * |δ|) * Real.exp (-|c / 2 * X|) := by
          rw [mul_assoc, ← Real.exp_add]
          have hle : 0 ≤ c * |δ| - |c / 2 * X| := by
            rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < c / 2)]
            nlinarith [abs_nonneg X, abs_nonneg δ]
          have := Real.one_le_exp (by linarith : (0:ℝ) ≤ c * |δ| + -|c / 2 * X|)
          linarith
      _ ≤ 2 * Real.exp (c * |δ|) * Gweight t2 (c / 2 * X) := by
          apply mul_le_mul_of_nonneg_left (exp_neg_abs_le_Gweight _ _) (by positivity)
  · -- far: |X + δ| ≥ |X|/2, use antitonicity and time-scale monotonicity
    have habs : |X| / 2 ≤ |X + δ| := by
      have := abs_add_le (X + δ) (-δ)
      simp only [add_neg_cancel_right, abs_neg] at this
      linarith
    calc Gweight t1 (c * (X + δ))
        = Gweight t1 (c * |X + δ|) := by rw [← Gweight_abs, abs_mul, abs_of_pos hc]
      _ ≤ Gweight t1 (c / 2 * |X|) := by
          apply Gweight_anti ht1 (by positivity)
          nlinarith [abs_nonneg (X + δ)]
      _ ≤ Gweight t2 (c / 2 * |X|) := Gweight_mono_t ht1 ht _
      _ = Gweight t2 (c / 2 * X) := by
          rw [show c / 2 * |X| = |c / 2 * X| by
            rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < c / 2)], Gweight_abs]
      _ ≤ 2 * Real.exp (c * |δ|) * Gweight t2 (c / 2 * X) := by
          nlinarith [Gweight_nonneg t2 (c / 2 * X)]

/-- **Discrete Gaussian × exponential convolution** (the `j₁`-sum of the
Lemma 7.7 assembly): summing the renewal Gaussian at centre `μ` against an
exponential window at centre `w` reproduces a Gaussian at centre `w`, with
decay constant `min(c/2, γ/4)`. -/
theorem conv_Gweight_exp {t c γ : ℝ} (ht : 0 < t) (hc : 0 < c) (hγ : 0 < γ)
    (μ : ℝ) (w : ℤ) (J : ℕ) (hw : w.toNat < J) :
    ∑ k ∈ Finset.range J, Gweight t (c * (k - μ)) * Real.exp (-γ * |(w : ℝ) - k|)
      ≤ (4 + 8 / γ) * Gweight t (min (c / 2) (γ / 4) * ((w : ℝ) - μ)) := by
  set c9 : ℝ := min (c / 2) (γ / 4) with hc9def
  have hc9 : 0 < c9 := lt_min (by positivity) (by positivity)
  set G : ℝ := Gweight t (c9 * ((w : ℝ) - μ)) with hGdef
  have hG : 0 ≤ G := Gweight_nonneg _ _
  -- pointwise: each term ≤ 2·G·e^{-(γ/2)|w-k|}
  have hpt : ∀ k : ℕ, Gweight t (c * (k - μ)) * Real.exp (-γ * |(w : ℝ) - k|)
      ≤ 2 * G * Real.exp (-(γ / 2) * |(w : ℝ) - k|) := by
    intro k
    rcases le_total (|(w : ℝ) - μ| / 2) |(k : ℝ) - μ| with hfar | hnear
    · -- far from the Gaussian centre: the Gaussian factor is already small
      have h1 : Gweight t (c * (k - μ)) ≤ G := by
        rw [hGdef, ← Gweight_abs t (c9 * _), ← Gweight_abs t (c * _)]
        rw [abs_mul, abs_mul, abs_of_pos hc, abs_of_pos hc9]
        apply Gweight_anti ht (by positivity)
        have hc92 : c9 ≤ c / 2 := min_le_left _ _
        nlinarith [abs_nonneg ((w : ℝ) - μ), abs_nonneg ((k : ℝ) - μ)]
      have h2 : Real.exp (-γ * |(w : ℝ) - k|) ≤ Real.exp (-(γ / 2) * |(w : ℝ) - k|) := by
        apply Real.exp_le_exp.mpr
        nlinarith [abs_nonneg ((w : ℝ) - k)]
      calc Gweight t (c * (k - μ)) * Real.exp (-γ * |(w : ℝ) - k|)
          ≤ G * Real.exp (-(γ / 2) * |(w : ℝ) - k|) :=
            mul_le_mul h1 h2 (Real.exp_pos _).le hG
        _ ≤ 2 * G * Real.exp (-(γ / 2) * |(w : ℝ) - k|) := by
            nlinarith [(Real.exp_pos (-(γ / 2) * |(w : ℝ) - k|)).le, hG]
    · -- near the Gaussian centre: the exponential window is small there
      have hwk : |(w : ℝ) - μ| / 2 ≤ |(w : ℝ) - k| := by
        have := abs_add_le ((w : ℝ) - k) ((k : ℝ) - μ)
        have heq : (w : ℝ) - k + ((k : ℝ) - μ) = (w : ℝ) - μ := by ring
        rw [heq] at this
        linarith
      have h1 : Gweight t (c * (k - μ)) ≤ 2 := Gweight_le_two _ _ ht.le
      have h2 : Real.exp (-γ * |(w : ℝ) - k|)
          ≤ Real.exp (-(γ / 2) * |(w : ℝ) - k|) * Real.exp (-(γ / 4) * |(w : ℝ) - μ|) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [abs_nonneg ((w : ℝ) - k), abs_nonneg ((w : ℝ) - μ)]
      have h3 : Real.exp (-(γ / 4) * |(w : ℝ) - μ|) ≤ G := by
        rw [hGdef]
        calc Real.exp (-(γ / 4) * |(w : ℝ) - μ|)
            ≤ Real.exp (-|c9 * ((w : ℝ) - μ)|) := by
              apply Real.exp_le_exp.mpr
              rw [abs_mul, abs_of_pos hc9]
              have hc94 : c9 ≤ γ / 4 := min_le_right _ _
              nlinarith [abs_nonneg ((w : ℝ) - μ)]
          _ ≤ Gweight t (c9 * ((w : ℝ) - μ)) := exp_neg_abs_le_Gweight _ _
      calc Gweight t (c * (k - μ)) * Real.exp (-γ * |(w : ℝ) - k|)
          ≤ 2 * (Real.exp (-(γ / 2) * |(w : ℝ) - k|)
              * Real.exp (-(γ / 4) * |(w : ℝ) - μ|)) := by
            apply mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num)
        _ ≤ 2 * G * Real.exp (-(γ / 2) * |(w : ℝ) - k|) := by
            have := mul_le_mul_of_nonneg_left h3 (Real.exp_pos (-(γ / 2) * |(w : ℝ) - k|)).le
            nlinarith
  calc ∑ k ∈ Finset.range J, Gweight t (c * (k - μ)) * Real.exp (-γ * |(w : ℝ) - k|)
      ≤ ∑ k ∈ Finset.range J, 2 * G * Real.exp (-(γ / 2) * |(w : ℝ) - k|) :=
        Finset.sum_le_sum fun k _ => hpt k
    _ = 2 * G * ∑ k ∈ Finset.range J, Real.exp (-(γ / 2) * |(w : ℝ) - k|) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * G * (2 * (1 + 1 / (γ / 2))) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∑ k ∈ Finset.range J, Real.exp (-(γ / 2) * |(w : ℝ) - k|)
            ≤ 2 * ∑ m ∈ Finset.range J, Real.exp (-(γ / 2) * m) :=
              sum_abs_int_le (fun u => (Real.exp_pos _).le)
                (fun u v hu huv => Real.exp_le_exp.mpr (by nlinarith)) w J hw
          _ ≤ 2 * (1 + 1 / (γ / 2)) := by
              have := sum_exp_geom_le (by positivity : (0:ℝ) < γ / 2) J
              linarith
    _ = (4 + 8 / γ) * G := by
        field_simp
        ring


/-- The constant of `sum_sqrt_exp_le`, symbolic (big-C campaign, step 2). -/
noncomputable def K_sqrtExp (γ : ℝ) : ℝ := 2 * (1 + 1 / γ) + 64 / γ ^ 2

theorem K_sqrtExp_pos {γ : ℝ} (hγ : 0 < γ) : 0 < K_sqrtExp γ := by
  unfold K_sqrtExp; positivity

/-- The `l₁`-sum envelope for the Lemma 7.7 assembly, `_explicitC` sibling: the
exponential window at the budget line beats the `1/√(1+l₁)` renewal prefactor, at
cost `1/√(1+s)`, with constant `K_sqrtExp γ`. -/
theorem sum_sqrt_exp_le_explicitC {γ : ℝ} (hγ : 0 < γ) :
    ∀ s : ℕ,
      ∑ m ∈ Finset.range (s + 1), Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
        ≤ K_sqrtExp γ / Real.sqrt (1 + s) := by
  unfold K_sqrtExp
  intro s
  have h1s : (0 : ℝ) < 1 + (s : ℝ) := by positivity
  have hs0 : 0 < Real.sqrt (1 + (s : ℝ)) := Real.sqrt_pos.mpr h1s
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (s + 1)) (fun m => s ≤ 2 * m)]
  have hhigh : ∑ m ∈ (Finset.range (s + 1)).filter (fun m => s ≤ 2 * m),
      Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
      ≤ (2 * (1 + 1 / γ)) / Real.sqrt (1 + s) := by
    have hpt : ∀ m ∈ (Finset.range (s + 1)).filter (fun m => s ≤ 2 * m),
        Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
          ≤ Real.exp (-γ * ((s : ℝ) - m)) * (2 / Real.sqrt (1 + s)) := by
      intro m hm
      have hm2 : s ≤ 2 * m := (Finset.mem_filter.mp hm).2
      have h1m : (0 : ℝ) < 1 + (m : ℝ) := by positivity
      have hsm : Real.sqrt (1 + (s : ℝ)) ≤ 2 * Real.sqrt (1 + (m : ℝ)) := by
        calc Real.sqrt (1 + (s : ℝ)) ≤ Real.sqrt (4 * (1 + (m : ℝ))) := by
              apply Real.sqrt_le_sqrt
              have : (s : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hm2
              linarith
          _ = 2 * Real.sqrt (1 + (m : ℝ)) := by
              rw [show (4 : ℝ) * (1 + (m : ℝ)) = 2 ^ 2 * (1 + (m : ℝ)) by ring,
                Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2 ^ 2),
                Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
      have hfrac : 1 / Real.sqrt (1 + (m : ℝ)) ≤ 2 / Real.sqrt (1 + (s : ℝ)) := by
        rw [div_le_div_iff₀ (Real.sqrt_pos.mpr h1m) hs0]
        linarith
      calc Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
          = Real.exp (-γ * ((s : ℝ) - m)) * (1 / Real.sqrt (1 + (m : ℝ))) := by ring
        _ ≤ Real.exp (-γ * ((s : ℝ) - m)) * (2 / Real.sqrt (1 + (s : ℝ))) :=
            mul_le_mul_of_nonneg_left hfrac (Real.exp_pos _).le
    calc ∑ m ∈ (Finset.range (s + 1)).filter (fun m => s ≤ 2 * m),
        Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
        ≤ ∑ m ∈ (Finset.range (s + 1)).filter (fun m => s ≤ 2 * m),
          Real.exp (-γ * ((s : ℝ) - m)) * (2 / Real.sqrt (1 + s)) :=
          Finset.sum_le_sum hpt
      _ ≤ ∑ m ∈ Finset.range (s + 1),
          Real.exp (-γ * ((s : ℝ) - m)) * (2 / Real.sqrt (1 + s)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun m _ _ => by positivity
      _ = (∑ m ∈ Finset.range (s + 1), Real.exp (-γ * ((s : ℝ) - m)))
          * (2 / Real.sqrt (1 + s)) := by rw [← Finset.sum_mul]
      _ ≤ (1 + 1 / γ) * (2 / Real.sqrt (1 + s)) := by
          apply mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hre : ∑ m ∈ Finset.range (s + 1), Real.exp (-γ * ((s : ℝ) - m))
              = ∑ m ∈ Finset.range (s + 1), Real.exp (-γ * (m : ℝ)) := by
            rw [← Finset.sum_range_reflect (fun m => Real.exp (-γ * (m : ℝ))) (s + 1)]
            refine Finset.sum_congr rfl fun m hm => ?_
            have hm' : m ≤ s := by
              have := Finset.mem_range.mp hm
              omega
            congr 1
            rw [show s + 1 - 1 - m = s - m by omega, Nat.cast_sub hm']
          rw [hre]
          exact sum_exp_geom_le hγ (s + 1)
      _ = (2 * (1 + 1 / γ)) / Real.sqrt (1 + s) := by ring
  have hlow : ∑ m ∈ (Finset.range (s + 1)).filter (fun m => ¬ s ≤ 2 * m),
      Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
      ≤ (64 / γ ^ 2) / Real.sqrt (1 + s) := by
    rcases Nat.eq_zero_or_pos s with rfl | hs1
    · rw [Finset.filter_false_of_mem (fun m hm => by
        have := Finset.mem_range.mp hm
        omega), Finset.sum_empty]
      positivity
    · have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
      have hpt : ∀ m ∈ (Finset.range (s + 1)).filter (fun m => ¬ s ≤ 2 * m),
          Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
            ≤ Real.exp (-(γ * s / 2)) := by
        intro m hm
        have hm2 : 2 * m < s := Nat.lt_of_not_le (Finset.mem_filter.mp hm).2
        have hm2R : 2 * (m : ℝ) < (s : ℝ) := by exact_mod_cast hm2
        have hsq1 : (1 : ℝ) ≤ Real.sqrt (1 + (m : ℝ)) :=
          Real.one_le_sqrt.mpr (le_add_of_nonneg_right (Nat.cast_nonneg m))
        calc Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
            ≤ Real.exp (-γ * ((s : ℝ) - m)) / 1 := by
              exact div_le_div_of_nonneg_left (Real.exp_pos _).le one_pos hsq1
          _ = Real.exp (-γ * ((s : ℝ) - m)) := by rw [div_one]
          _ ≤ Real.exp (-(γ * s / 2)) := by
              apply Real.exp_le_exp.mpr
              nlinarith
      calc ∑ m ∈ (Finset.range (s + 1)).filter (fun m => ¬ s ≤ 2 * m),
          Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
          ≤ ∑ _m ∈ (Finset.range (s + 1)).filter (fun m => ¬ s ≤ 2 * m),
            Real.exp (-(γ * s / 2)) := Finset.sum_le_sum hpt
        _ = (((Finset.range (s + 1)).filter (fun m => ¬ s ≤ 2 * m)).card : ℝ)
            * Real.exp (-(γ * s / 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (1 + (s : ℝ)) * Real.exp (-(γ * s / 2)) := by
            apply mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            have hc : ((Finset.range (s + 1)).filter (fun m => ¬ s ≤ 2 * m)).card ≤ s + 1 :=
              le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_range])
            calc (((Finset.range (s + 1)).filter (fun m => ¬ s ≤ 2 * m)).card : ℝ)
                ≤ ((s + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hc
              _ = 1 + (s : ℝ) := by push_cast; ring
        _ ≤ (64 / γ ^ 2) / Real.sqrt (1 + s) := by
            rw [le_div_iff₀ hs0]
            have hsle : Real.sqrt (1 + (s : ℝ)) ≤ 1 + (s : ℝ) := by
              have h := Real.sqrt_le_sqrt (show (1:ℝ) + s ≤ (1 + s) ^ 2 by nlinarith)
              rwa [Real.sqrt_sq h1s.le] at h
            have hexp : Real.exp (-(γ * s / 2)) ≤ 4 / (γ * s / 2) ^ 2 :=
              exp_neg_le_four_div_sq (by positivity)
            calc (1 + (s : ℝ)) * Real.exp (-(γ * s / 2)) * Real.sqrt (1 + s)
                ≤ (1 + (s : ℝ)) * Real.exp (-(γ * s / 2)) * (1 + (s : ℝ)) := by
                  apply mul_le_mul_of_nonneg_left hsle (by positivity)
              _ = (1 + (s : ℝ)) ^ 2 * Real.exp (-(γ * s / 2)) := by ring
              _ ≤ (2 * (s : ℝ)) ^ 2 * (4 / (γ * s / 2) ^ 2) := by
                  apply mul_le_mul (by nlinarith) hexp (Real.exp_pos _).le (by positivity)
              _ = 64 / γ ^ 2 := by
                  field_simp
                  ring
  calc ∑ m ∈ (Finset.range (s + 1)).filter (fun m => s ≤ 2 * m),
        Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
      + ∑ m ∈ (Finset.range (s + 1)).filter (fun m => ¬ s ≤ 2 * m),
        Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
      ≤ (2 * (1 + 1 / γ)) / Real.sqrt (1 + s) + (64 / γ ^ 2) / Real.sqrt (1 + s) :=
        add_le_add hhigh hlow
    _ = (2 * (1 + 1 / γ) + 64 / γ ^ 2) / Real.sqrt (1 + s) := (add_div _ _ _).symm

/-- `sum_sqrt_exp_le`, original `∃`-form: delegates to the `_explicitC` sibling. -/
theorem sum_sqrt_exp_le {γ : ℝ} (hγ : 0 < γ) :
    ∃ K > (0 : ℝ), ∀ s : ℕ,
      ∑ m ∈ Finset.range (s + 1), Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
        ≤ K / Real.sqrt (1 + s) :=
  ⟨K_sqrtExp γ, K_sqrtExp_pos hγ, sum_sqrt_exp_le_explicitC hγ⟩

end HL

end GGMCollatz
