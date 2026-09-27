/- Portions Copyright (c) 2026 Idris Ali Shaik (FirstPassageLinearTransport, Apache License 2.0).
   Modified: generalized to the maps of Goncalves, Greenfeld and Madrid. See NOTICE. -/
import GGMCollatz.Seed.Step

/-!
# Seed (Theorem 4.1 of the paper), part 2: the average of the θ-th power and the density of the bad set

Plays the role of items 1 and 2 of the seed argument in the accompanying paper, in a form that uses
**only the upper envelope**. Instead of the Chernoff + Doob argument of Shaik's `Envelope` and `Density`
(Idris Ali Shaik's `FirstPassageLinearTransport`, Apache-2.0), we estimate the average of `x ↦ x^θ`
(`0 < θ ≤ 1`) one step at a time (Markov's inequality).

* `Ct_rpow_le`: `C~(x)^θ ≤ ω_θ(x mod p) x^θ + (R/p)^θ`. The sign of `r` is not used.
* `iterate_rpow_le`: the affine-form estimate over `m` steps (the θ-th power version of (i) in the
  accompanying paper).
* `exists_theta`: from condition (b), a `θ ∈ (0, 1]` with `1 + (p-1)q^θ < p·p^θ`.
* `bad m`: the numbers in the shell `I_m` with `C~^m(n) ≥ p^m`.
* `bad_density`: `#bad m ≤ K p^m ξ^m` (for some `ξ < 1`). The counterpart of the bad-set density
  estimate in the accompanying paper.
-/

namespace GGMCollatz

namespace Family

variable (F : Family)

open Finset

/-- Weights `ω_θ(0) = p^{-θ}`, `ω_θ(j) = (q/p)^θ` (`j ≠ 0`). -/
noncomputable def wt (θ : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then ((F.p : ℝ)⁻¹) ^ θ else ((F.q : ℝ) / F.p) ^ θ

lemma wt_nonneg (θ : ℝ) (j : ℕ) : 0 ≤ F.wt θ j := by
  unfold wt; split_ifs <;> positivity

/-- One-step estimate of the θ-th power. -/
lemma Ct_rpow_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (x : ℕ) :
    (F.Ct x : ℝ) ^ θ ≤ F.wt θ (x % F.p) * (x : ℝ) ^ θ + ((F.Rb : ℝ) / F.p) ^ θ := by
  have hp : (0 : ℝ) < F.p := by exact_mod_cast F.p_pos
  by_cases h : x % F.p = 0
  · have e := F.p_mul_Ct_real_of_mod_eq_zero h
    have hx : (F.Ct x : ℝ) = (F.p : ℝ)⁻¹ * x := by
      rw [← e]; field_simp
    rw [hx, Real.mul_rpow (by positivity) (by positivity)]
    simp only [wt, h, if_true]
    have : 0 ≤ ((F.Rb : ℝ) / F.p) ^ θ := by positivity
    linarith
  · have e := F.p_mul_Ct_real_of_mod_ne_zero h
    have hr := F.abs_r_le_real (F.mod_lt_p x)
    have hr' : (F.r (x % F.p) : ℝ) ≤ F.Rb := le_trans (le_abs_self _) hr
    have hle : (F.Ct x : ℝ) ≤ (F.q : ℝ) / F.p * x + (F.Rb : ℝ) / F.p := by
      have h2 : (F.p : ℝ) * ((F.q : ℝ) / F.p * x + (F.Rb : ℝ) / F.p) = F.q * x + F.Rb := by
        field_simp
      have h3 : (F.p : ℝ) * (F.Ct x : ℝ) ≤ (F.p : ℝ) * ((F.q : ℝ) / F.p * x + (F.Rb : ℝ) / F.p) := by
        rw [h2, e]; linarith
      exact le_of_mul_le_mul_left h3 hp
    calc (F.Ct x : ℝ) ^ θ ≤ ((F.q : ℝ) / F.p * x + (F.Rb : ℝ) / F.p) ^ θ :=
          Real.rpow_le_rpow (by positivity) hle hθ0
      _ ≤ ((F.q : ℝ) / F.p * x) ^ θ + ((F.Rb : ℝ) / F.p) ^ θ :=
          Real.rpow_add_le_add_rpow (by positivity) (by positivity) hθ0 hθ1
      _ = F.wt θ (x % F.p) * (x : ℝ) ^ θ + ((F.Rb : ℝ) / F.p) ^ θ := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
          simp [wt, h]

/-- Estimate over `m` steps: `C~^m(n)^θ ≤ (∏_{k<m} ω(ℓ_k)) n^θ + (R/p)^θ ∑_{i<m} ∏_{i<k<m} ω(ℓ_k)`. -/
lemma iterate_rpow_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (n : ℕ) : ∀ m : ℕ,
    (F.Ct^[m] n : ℝ) ^ θ ≤ (∏ k ∈ range m, F.wt θ (F.Ct^[k] n % F.p)) * (n : ℝ) ^ θ
      + ((F.Rb : ℝ) / F.p) ^ θ *
        ∑ i ∈ range m, ∏ k ∈ Ico (i + 1) m, F.wt θ (F.Ct^[k] n % F.p) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    set c := ((F.Rb : ℝ) / F.p) ^ θ with hc
    set w := F.wt θ (F.Ct^[m] n % F.p) with hwdef
    set P := ∏ k ∈ range m, F.wt θ (F.Ct^[k] n % F.p) with hP
    set Q := ∑ i ∈ range m, ∏ k ∈ Ico (i + 1) m, F.wt θ (F.Ct^[k] n % F.p) with hQ
    have hw : 0 ≤ w := F.wt_nonneg _ _
    have h1 := F.Ct_rpow_le hθ0 hθ1 (F.Ct^[m] n)
    have hsum : ∑ i ∈ range (m + 1), ∏ k ∈ Ico (i + 1) (m + 1), F.wt θ (F.Ct^[k] n % F.p)
        = Q * w + 1 := by
      rw [sum_range_succ, Ico_self, prod_empty, hQ, sum_mul]
      congr 1
      refine sum_congr rfl (fun i hi => ?_)
      rw [prod_Ico_succ_top (by simp at hi; omega)]
    rw [prod_range_succ, hsum]
    calc (F.Ct (F.Ct^[m] n) : ℝ) ^ θ ≤ w * (F.Ct^[m] n : ℝ) ^ θ + c := h1
      _ ≤ w * (P * (n : ℝ) ^ θ + c * Q) + c := by
          have := mul_le_mul_of_nonneg_left ih hw
          linarith
      _ = P * w * (n : ℝ) ^ θ + c * (Q * w + 1) := by ring

/-- From condition (b): a `θ ∈ (0, 1]` with `1 + (p-1) q^θ < p · p^θ`. -/
lemma exists_theta : ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
    1 + ((F.p : ℝ) - 1) * (F.q : ℝ) ^ θ < (F.p : ℝ) * (F.p : ℝ) ^ θ := by
  have hp2 : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hp : (0 : ℝ) < F.p := by linarith
  have hpq : (F.p : ℝ) < F.q := by exact_mod_cast F.p_lt_q
  have hq1 : (1 : ℝ) < F.q := by linarith
  set a := Real.log F.q with ha
  set b := Real.log F.p with hb
  have ha0 : 0 < a := Real.log_pos hq1
  have hb0 : 0 < b := Real.log_pos (by linarith)
  -- (b): log q < (p/(p-1)) log p
  have hsub := F.subcritical
  have hlog : a < ((F.p : ℝ) / ((F.p : ℝ) - 1)) * b := by
    have := Real.log_lt_log (by linarith) hsub
    rwa [Real.log_rpow hp] at this
  have hp1 : (0 : ℝ) < (F.p : ℝ) - 1 := by linarith
  have hkey : ((F.p : ℝ) - 1) * a < (F.p : ℝ) * b := by
    have := mul_lt_mul_of_pos_left hlog hp1
    rwa [← mul_assoc, mul_div_cancel₀ _ hp1.ne'] at this
  set δ := (F.p : ℝ) * b - ((F.p : ℝ) - 1) * a with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set θ := min 1 (min (1 / a) (δ / (2 * ((F.p : ℝ) - 1) * a ^ 2))) with hθ
  have hθ0 : 0 < θ := by
    rw [hθ]; apply lt_min one_pos; apply lt_min (by positivity); positivity
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθa : θ ≤ 1 / a := le_trans (min_le_right _ _) (min_le_left _ _)
  have hθδ : θ ≤ δ / (2 * ((F.p : ℝ) - 1) * a ^ 2) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨θ, hθ0, hθ1, ?_⟩
  have haθ : a * θ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hθa ha0.le
    rwa [mul_one_div_cancel ha0.ne'] at this
  have hqθ : (F.q : ℝ) ^ θ = Real.exp (a * θ) := Real.rpow_def_of_pos (by linarith) θ
  have hpθ : (F.p : ℝ) ^ θ = Real.exp (b * θ) := Real.rpow_def_of_pos hp θ
  have habs : |a * θ| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]; exact haθ
  have hexpa : Real.exp (a * θ) ≤ 1 + a * θ + (a * θ) ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le habs
    have := le_abs_self (Real.exp (a * θ) - 1 - a * θ)
    linarith
  have hexpb : b * θ + 1 ≤ Real.exp (b * θ) := Real.add_one_le_exp _
  have hsmall : ((F.p : ℝ) - 1) * a ^ 2 * θ ≤ δ / 2 := by
    have h2 : 0 < 2 * ((F.p : ℝ) - 1) * a ^ 2 := by positivity
    have := (le_div_iff₀ h2).1 hθδ
    nlinarith
  rw [hqθ, hpθ]
  have e1 : ((F.p : ℝ) - 1) * Real.exp (a * θ)
      ≤ ((F.p : ℝ) - 1) * (1 + a * θ + (a * θ) ^ 2) :=
    mul_le_mul_of_nonneg_left hexpa hp1.le
  have e2 : (F.p : ℝ) * (b * θ + 1) ≤ (F.p : ℝ) * Real.exp (b * θ) :=
    mul_le_mul_of_nonneg_left hexpb hp.le
  have e3 : θ * (((F.p : ℝ) - 1) * a ^ 2 * θ) ≤ θ * (δ / 2) :=
    mul_le_mul_of_nonneg_left hsmall hθ0.le
  have e4 : 0 < θ * δ := mul_pos hθ0 hδ0
  nlinarith

/-- The bad numbers of the shell `I_m`: `C~^m(n) ≥ p^m`. -/
def bad (m : ℕ) : Finset ℕ :=
  (Ico (F.p ^ m) (F.p ^ (m + 1))).filter (fun n => F.p ^ m ≤ F.Ct^[m] n)

lemma mem_bad {m n : ℕ} : n ∈ F.bad m ↔ (F.p ^ m ≤ n ∧ n < F.p ^ (m + 1)) ∧ F.p ^ m ≤ F.Ct^[m] n := by
  simp [bad]

/-- Sum of the weights: `∑_{j<p} ω_θ(j) = p^{-θ} + (p - 1)(q/p)^θ`. -/
lemma sum_wt (θ : ℝ) :
    ∑ j ∈ range F.p, F.wt θ j = ((F.p : ℝ) ^ θ)⁻¹ * (1 + ((F.p : ℝ) - 1) * (F.q : ℝ) ^ θ) := by
  have hp : (0 : ℝ) < F.p := by exact_mod_cast F.p_pos
  obtain ⟨p', hp'⟩ : ∃ p', F.p = p' + 1 := ⟨F.p - 1, by have := F.two_le_p; omega⟩
  rw [hp', sum_range_succ']
  have : ∀ i ∈ range p', F.wt θ (i + 1) = ((F.q : ℝ) / F.p) ^ θ := by
    intro i _; simp [wt]
  rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul]
  simp only [wt, if_true]
  rw [← hp', Real.inv_rpow hp.le, Real.div_rpow (by positivity) hp.le]
  have hpθ : 0 < (F.p : ℝ) ^ θ := Real.rpow_pos_of_pos hp θ
  have hp'r : ((p' : ℕ) : ℝ) = (F.p : ℝ) - 1 := by rw [hp']; push_cast; ring
  rw [hp'r]
  field_simp
  ring

/-- Sum of the products over the window `(i, m)`: `∑_{n∈I_m} ∏_{i<k<m} ω(ℓ_k) ≤ (p-1) p^{i+1} W^{m-1-i}`,
`W = ∑_j ω(j)`. -/
lemma sum_window_le (θ : ℝ) {m i : ℕ} (hi : i < m) :
    ∑ n ∈ Ico (F.p ^ m) (F.p ^ (m + 1)), ∏ k ∈ Ico (i + 1) m, F.wt θ (F.Ct^[k] n % F.p)
      ≤ ((F.p : ℝ) - 1) * ((F.p : ℝ) ^ (i + 1) * (∑ j ∈ range F.p, F.wt θ j) ^ (m - 1 - i)) := by
  classical
  have hsub : Ico (i + 1) m ⊆ range m := by
    intro k hk; simp only [mem_Ico, mem_range] at hk ⊢; omega
  have key := F.sum_prod_chars_le m (fun k j => if k ∈ Ico (i + 1) m then F.wt θ j else 1)
    (by intro k j; split_ifs
        · exact F.wt_nonneg _ _
        · exact zero_le_one)
  have lhs_eq : ∀ n, ∏ k ∈ range m, (fun k j => if k ∈ Ico (i + 1) m then F.wt θ j else (1 : ℝ))
      k (F.Ct^[k] n % F.p) = ∏ k ∈ Ico (i + 1) m, F.wt θ (F.Ct^[k] n % F.p) := by
    intro n
    simp only
    rw [prod_ite_mem, inter_eq_right.2 hsub]
  have rhs_eq : ∏ k ∈ range m, ∑ j ∈ range F.p,
      (fun k j => if k ∈ Ico (i + 1) m then F.wt θ j else (1 : ℝ)) k j
      = (F.p : ℝ) ^ (i + 1) * (∑ j ∈ range F.p, F.wt θ j) ^ (m - 1 - i) := by
    rw [← prod_range_mul_prod_Ico _ (show i + 1 ≤ m by omega)]
    have h1 : ∀ k ∈ range (i + 1), ∑ j ∈ range F.p,
        (fun k j => if k ∈ Ico (i + 1) m then F.wt θ j else (1 : ℝ)) k j = (F.p : ℝ) := by
      intro k hk
      have : k ∉ Ico (i + 1) m := by simp only [mem_Ico, mem_range] at hk ⊢; omega
      simp [this]
    have h2 : ∀ k ∈ Ico (i + 1) m, ∑ j ∈ range F.p,
        (fun k j => if k ∈ Ico (i + 1) m then F.wt θ j else (1 : ℝ)) k j
          = ∑ j ∈ range F.p, F.wt θ j := by
      intro k hk
      simp [hk]
    rw [prod_congr rfl h1, prod_congr rfl h2, prod_const, prod_const, card_range, Nat.card_Ico]
    rw [show m - (i + 1) = m - 1 - i by omega]
  rw [rhs_eq] at key
  simp_rw [lhs_eq] at key
  exact key

/-- Estimate of the sum of the θ-th powers over a shell. -/
lemma sum_rpow_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (m : ℕ) :
    ∑ n ∈ Ico (F.p ^ m) (F.p ^ (m + 1)), (F.Ct^[m] n : ℝ) ^ θ
      ≤ ((F.p : ℝ) - 1) * (((F.p : ℝ) ^ θ) ^ (m + 1) * (∑ j ∈ range F.p, F.wt θ j) ^ m
        + ((F.Rb : ℝ) / F.p) ^ θ * ∑ i ∈ range m,
            (F.p : ℝ) ^ (i + 1) * (∑ j ∈ range F.p, F.wt θ j) ^ (m - 1 - i)) := by
  have hp : (0 : ℝ) < F.p := by exact_mod_cast F.p_pos
  have hp1 : (0 : ℝ) ≤ (F.p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
    linarith
  have hc0 : 0 ≤ ((F.Rb : ℝ) / F.p) ^ θ := by positivity
  have hterm : ∀ n ∈ Ico (F.p ^ m) (F.p ^ (m + 1)), (F.Ct^[m] n : ℝ) ^ θ
      ≤ (∏ k ∈ range m, F.wt θ (F.Ct^[k] n % F.p)) * ((F.p : ℝ) ^ θ) ^ (m + 1)
        + ((F.Rb : ℝ) / F.p) ^ θ *
          ∑ i ∈ range m, ∏ k ∈ Ico (i + 1) m, F.wt θ (F.Ct^[k] n % F.p) := by
    intro n hn
    have h := F.iterate_rpow_le hθ0 hθ1 n m
    have hn' : (n : ℝ) ≤ (F.p : ℝ) ^ (m + 1) := by
      have := (mem_Ico.1 hn).2; exact_mod_cast this.le
    have hnθ : (n : ℝ) ^ θ ≤ ((F.p : ℝ) ^ θ) ^ (m + 1) := by
      rw [Real.rpow_pow_comm hp.le]
      exact Real.rpow_le_rpow (by positivity) hn' hθ0
    have hprod : 0 ≤ ∏ k ∈ range m, F.wt θ (F.Ct^[k] n % F.p) :=
      prod_nonneg (fun _ _ => F.wt_nonneg _ _)
    have := mul_le_mul_of_nonneg_left hnθ hprod
    linarith
  refine le_trans (sum_le_sum hterm) ?_
  rw [sum_add_distrib, ← sum_mul, ← mul_sum]
  have hA : ∑ n ∈ Ico (F.p ^ m) (F.p ^ (m + 1)), ∏ k ∈ range m, F.wt θ (F.Ct^[k] n % F.p)
      ≤ ((F.p : ℝ) - 1) * (∑ j ∈ range F.p, F.wt θ j) ^ m := by
    have := F.sum_prod_chars_le m (fun _ j => F.wt θ j) (fun _ _ => F.wt_nonneg _ _)
    simpa only [prod_const, card_range] using this
  have hB : ∑ n ∈ Ico (F.p ^ m) (F.p ^ (m + 1)),
      ∑ i ∈ range m, ∏ k ∈ Ico (i + 1) m, F.wt θ (F.Ct^[k] n % F.p)
      ≤ ((F.p : ℝ) - 1) * ∑ i ∈ range m,
          (F.p : ℝ) ^ (i + 1) * (∑ j ∈ range F.p, F.wt θ j) ^ (m - 1 - i) := by
    rw [sum_comm, mul_sum]
    exact sum_le_sum (fun i hi => F.sum_window_le θ (mem_range.1 hi))
  have hA' := mul_le_mul_of_nonneg_right hA (by positivity : (0 : ℝ) ≤ ((F.p : ℝ) ^ θ) ^ (m + 1))
  have hB' := mul_le_mul_of_nonneg_left hB hc0
  calc _ ≤ ((F.p : ℝ) - 1) * (∑ j ∈ range F.p, F.wt θ j) ^ m * ((F.p : ℝ) ^ θ) ^ (m + 1)
        + ((F.Rb : ℝ) / F.p) ^ θ * (((F.p : ℝ) - 1) * ∑ i ∈ range m,
          (F.p : ℝ) ^ (i + 1) * (∑ j ∈ range F.p, F.wt θ j) ^ (m - 1 - i)) := add_le_add hA' hB'
    _ = _ := by ring

/-- Markov: `#bad m · (p^θ)^m ≤ ∑_{n∈I_m} C~^m(n)^θ`. -/
lemma card_bad_mul_le {θ : ℝ} (hθ0 : 0 ≤ θ) (m : ℕ) :
    ((F.bad m).card : ℝ) * ((F.p : ℝ) ^ θ) ^ m
      ≤ ∑ n ∈ Ico (F.p ^ m) (F.p ^ (m + 1)), (F.Ct^[m] n : ℝ) ^ θ := by
  have hp : (0 : ℝ) < F.p := by exact_mod_cast F.p_pos
  calc ((F.bad m).card : ℝ) * ((F.p : ℝ) ^ θ) ^ m = ∑ _n ∈ F.bad m, ((F.p : ℝ) ^ θ) ^ m := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ F.bad m, (F.Ct^[m] n : ℝ) ^ θ := by
        apply sum_le_sum
        intro n hn
        have h := ((F.mem_bad).1 hn).2
        have h' : ((F.p : ℝ) ^ m) ≤ (F.Ct^[m] n : ℝ) := by exact_mod_cast h
        rw [Real.rpow_pow_comm hp.le]
        exact Real.rpow_le_rpow (by positivity) h' hθ0
    _ ≤ ∑ n ∈ Ico (F.p ^ m) (F.p ^ (m + 1)), (F.Ct^[m] n : ℝ) ^ θ :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)

/-- Geometric sum: `∑_{i<m} p^{i+1} (pν)^{m-1-i} ≤ p^m / (1 - ν)`. -/
lemma sum_geom_window_le {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν < 1) (m : ℕ) :
    ∑ i ∈ range m, (F.p : ℝ) ^ (i + 1) * ((F.p : ℝ) * ν) ^ (m - 1 - i)
      ≤ (F.p : ℝ) ^ m / (1 - ν) := by
  have heq : ∀ i ∈ range m, (F.p : ℝ) ^ (i + 1) * ((F.p : ℝ) * ν) ^ (m - 1 - i)
      = (F.p : ℝ) ^ m * ν ^ (m - 1 - i) := by
    intro i hi
    have hi' := mem_range.1 hi
    rw [mul_pow, ← mul_assoc, ← pow_add, show i + 1 + (m - 1 - i) = m by omega]
  rw [sum_congr rfl heq, ← mul_sum, div_eq_mul_one_div]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hrefl : ∑ i ∈ range m, ν ^ (m - 1 - i) = ∑ i ∈ range m, ν ^ i :=
    sum_range_reflect (fun i => ν ^ i) m
  rw [hrefl, range_eq_Ico]
  have := geom_sum_Ico_le_of_lt_one (m := 0) (n := m) hν0 hν1
  simpa using this

/-- Density of the bad set (the counterpart of the estimate in the accompanying paper): for some
`ξ ∈ (0,1)` and `K ≥ 0`, `#bad m ≤ K p^m ξ^m`. -/
theorem bad_density : ∃ ξ : ℝ, 0 < ξ ∧ ξ < 1 ∧ ∃ K : ℝ, 0 ≤ K ∧
    ∀ m : ℕ, ((F.bad m).card : ℝ) ≤ K * (F.p : ℝ) ^ m * ξ ^ m := by
  obtain ⟨θ, hθ0, hθ1, hθ⟩ := F.exists_theta
  have hp2 : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hp : (0 : ℝ) < F.p := by linarith
  have hp1 : (0 : ℝ) ≤ (F.p : ℝ) - 1 := by linarith
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = (F.p : ℝ) ^ θ := ⟨_, rfl⟩
  have hP1 : 1 < P := by rw [hPdef]; exact Real.one_lt_rpow (by linarith) hθ0
  have hP0 : 0 < P := by linarith
  obtain ⟨ν, hνdef⟩ : ∃ ν : ℝ, ν = (1 + ((F.p : ℝ) - 1) * (F.q : ℝ) ^ θ) / ((F.p : ℝ) * P) :=
    ⟨_, rfl⟩
  have hν0 : 0 < ν := by
    rw [hνdef]; apply div_pos _ (by positivity)
    have : 0 ≤ ((F.p : ℝ) - 1) * (F.q : ℝ) ^ θ := mul_nonneg hp1 (by positivity)
    linarith
  have hν1 : ν < 1 := by
    rw [hνdef, div_lt_one (by positivity), hPdef]; exact hθ
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((F.Rb : ℝ) / F.p) ^ θ := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hW : ∑ j ∈ range F.p, F.wt θ j = (F.p : ℝ) * ν := by
    rw [F.sum_wt θ, hνdef, ← hPdef]; field_simp
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℝ, ξ = max ν P⁻¹ := ⟨_, rfl⟩
  have hξ0 : 0 < ξ := by rw [hξ]; exact lt_of_lt_of_le hν0 (le_max_left _ _)
  have hξ1 : ξ < 1 := by rw [hξ]; exact max_lt hν1 (inv_lt_one_of_one_lt₀ hP1)
  have hcν : 0 ≤ c / (1 - ν) := div_nonneg hc0 (by linarith)
  refine ⟨ξ, hξ0, hξ1, ((F.p : ℝ) - 1) * (P + c / (1 - ν)), ?_, ?_⟩
  · apply mul_nonneg hp1; linarith
  intro m
  have hsum := F.sum_rpow_le hθ0.le hθ1 m
  rw [← hPdef, ← hc, hW] at hsum
  have hgeom := F.sum_geom_window_le hν0.le hν1 m
  have hbad := F.card_bad_mul_le hθ0.le m
  rw [← hPdef] at hbad
  have hPm : 0 < P ^ m := pow_pos hP0 m
  -- #bad · P^m ≤ (p-1) (P^{m+1} p^m ν^m + c p^m/(1-ν))
  have h1 : ((F.bad m).card : ℝ) * P ^ m
      ≤ ((F.p : ℝ) - 1) * (P ^ (m + 1) * ((F.p : ℝ) ^ m * ν ^ m) + c * ((F.p : ℝ) ^ m / (1 - ν))) := by
    refine le_trans hbad (le_trans hsum ?_)
    apply mul_le_mul_of_nonneg_left _ hp1
    rw [mul_pow]
    have := mul_le_mul_of_nonneg_left hgeom hc0
    linarith
  have hνξ : ν ^ m ≤ ξ ^ m := pow_le_pow_left₀ hν0.le (by rw [hξ]; exact le_max_left _ _) m
  have hPξ : (P⁻¹) ^ m ≤ ξ ^ m :=
    pow_le_pow_left₀ (by positivity) (by rw [hξ]; exact le_max_right _ _) m
  have hpm : 0 ≤ (F.p : ℝ) ^ m := by positivity
  -- Divide the right-hand side by P^m
  have h2 : ((F.p : ℝ) - 1) * (P ^ (m + 1) * ((F.p : ℝ) ^ m * ν ^ m) + c * ((F.p : ℝ) ^ m / (1 - ν)))
      = (((F.p : ℝ) - 1) * (P * ((F.p : ℝ) ^ m * ν ^ m)
          + c / (1 - ν) * ((F.p : ℝ) ^ m * (P⁻¹) ^ m))) * P ^ m := by
    rw [inv_pow]
    field_simp
    ring
  rw [h2] at h1
  have h3 := le_of_mul_le_mul_right h1 hPm
  refine le_trans h3 ?_
  have e1 : P * ((F.p : ℝ) ^ m * ν ^ m) ≤ P * ((F.p : ℝ) ^ m * ξ ^ m) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hνξ hpm) hP0.le
  have e2 : c / (1 - ν) * ((F.p : ℝ) ^ m * (P⁻¹) ^ m) ≤ c / (1 - ν) * ((F.p : ℝ) ^ m * ξ ^ m) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPξ hpm) hcν
  have e4 := mul_le_mul_of_nonneg_left (add_le_add e1 e2) hp1
  refine le_trans e4 (le_of_eq ?_)
  ring

end Family

end GGMCollatz
