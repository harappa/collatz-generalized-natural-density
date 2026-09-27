import GGMCollatz.NatDen.UProf.Statements

/-!
# Pieces (a)(b) of (DK): the negative binomial hockey stick and the inner sum of each row

* `Hs p k S = Σ_{s ≤ S} p^{-(S-s)} P(s_k = s)` (the paper's `Σ_j p^{-j} P(s_k = S - j)`).
* `Hs_eq`: for `k ≥ 1`, `Hs p k S = C(S, k) (p-1)^k p^{-S}` (hockey stick).
* `Hs_eq_mul_nb`: for `k, S ≥ 1`, `Hs p k S = (S/k) P(s_k = S)` ((a)).
* `Hs_le_one`: `0 ≤ Hs ≤ 1`.
* `row_bound`: the inner sum of row `k` (window `y < p^s M/q^k ≤ Y`) agrees with `(Y/M) p^{-θ(k)} Hs(k, ⌊kλ+u⌋)`
  up to `y/M` ((b); the truncation at the lower end is bounded using `Hs ≤ 1`).

Notation: `λ = log q/log p`, `u = log(Y/M)/log p`, `θ(k) = kλ + u - ⌊kλ + u⌋`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace DKernAux

/-! ### Basic properties of the negative binomial `nb` -/

theorem nb_nonneg (p k s : ℕ) : 0 ≤ nb p k s := ENNReal.toReal_nonneg

theorem nb_le_one (p k s : ℕ) : nb p k s ≤ 1 := by
  unfold nb
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one _ _)

/-- If `k ≥ 1`, then `P(s_k = 0) = 0`. -/
theorem nb_zero {p : ℕ} (hp : 2 ≤ p) {k : ℕ} (hk : 1 ≤ k) : nb p k 0 = 0 := by
  unfold nb iidSum
  rw [map_sum_apply]
  have : ∀ v : Fin k → ℕ, (PMF.iid (geomP p) k) v * (if 0 = ∑ i, v i then 1 else 0) = 0 := by
    intro v
    split_ifs with h
    · rw [iid_geomP_sum_zero hp hk v h.symm, zero_mul]
    · rw [mul_zero]
  simp [this]

/-- For `k, s ≥ 1`, `P(s_k = s) = C(s-1, k-1) (p-1)^k p^{-s}`. -/
theorem nb_formula {p : ℕ} (hp : 2 ≤ p) {k s : ℕ} (hk : 1 ≤ k) (hs : 1 ≤ s) :
    nb p k s = ((s - 1).choose (k - 1) : ℝ) * ((p : ℝ) - 1) ^ k * ((p : ℝ)⁻¹) ^ s := by
  unfold nb
  rw [iidSum_geomP_apply hp k s hk hs]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    Nat.cast_sub (by omega), Nat.cast_one]

/-- A finite sum of values of `nb` is at most 1. -/
theorem sum_nb_le_one (p k : ℕ) (T : Finset ℕ) : ∑ s ∈ T, nb p k s ≤ 1 := by
  unfold nb
  rw [← ENNReal.toReal_sum (fun s _ => PMF.apply_ne_top _ _)]
  apply ENNReal.toReal_le_of_le_ofReal zero_le_one
  rw [ENNReal.ofReal_one, ← PMF.tsum_coe (iidSum (geomP p) k)]
  exact ENNReal.sum_le_tsum T

/-! ### hockey stick -/

/-- `Hs p k S = Σ_{s ≤ S} p^{-(S-s)} P(s_k = s)`. -/
noncomputable def Hs (p k S : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (S + 1), ((p : ℝ)⁻¹) ^ (S - s) * nb p k s

theorem Hs_nonneg (p k S : ℕ) : 0 ≤ Hs p k S := by
  unfold Hs
  refine Finset.sum_nonneg fun s _ => mul_nonneg (pow_nonneg ?_ _) (nb_nonneg _ _ _)
  positivity

theorem Hs_le_one {p : ℕ} (hp : 2 ≤ p) (k S : ℕ) : Hs p k S ≤ 1 := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold Hs
  refine le_trans (Finset.sum_le_sum fun s _ => ?_) (sum_nb_le_one p k _)
  have h1 : ((p : ℝ)⁻¹) ^ (S - s) ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith))
  exact le_trans (mul_le_mul_of_nonneg_right h1 (nb_nonneg _ _ _)) (by rw [one_mul])

/-- **hockey stick** ((a)): for `k ≥ 1`, `Hs p k S = C(S, k) (p-1)^k p^{-S}`. -/
theorem Hs_eq {p : ℕ} (hp : 2 ≤ p) {k : ℕ} (hk : 1 ≤ k) (S : ℕ) :
    Hs p k S = (S.choose k : ℝ) * ((p : ℝ) - 1) ^ k * ((p : ℝ)⁻¹) ^ S := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  unfold Hs
  rw [Finset.sum_range_succ', nb_zero hp hk, mul_zero, add_zero]
  have hterm : ∀ j ∈ Finset.range S, ((p : ℝ)⁻¹) ^ (S - (j + 1)) * nb p k (j + 1)
      = ((j.choose (k - 1) : ℕ) : ℝ) * (((p : ℝ) - 1) ^ k * ((p : ℝ)⁻¹) ^ S) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [nb_formula hp hk (by omega), Nat.add_sub_cancel]
    have hpow : ((p : ℝ)⁻¹) ^ (S - (j + 1)) * ((p : ℝ)⁻¹) ^ (j + 1) = ((p : ℝ)⁻¹) ^ S := by
      rw [← pow_add]; congr 1; omega
    rw [← hpow]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Nat.cast_sum, sum_range_choose_col,
    Nat.sub_add_cancel hk]
  ring

/-- **(a)**: for `k, S ≥ 1`, `Hs p k S = (S/k) P(s_k = S)`. -/
theorem Hs_eq_mul_nb {p : ℕ} (hp : 2 ≤ p) {k S : ℕ} (hk : 1 ≤ k) (hS : 1 ≤ S) :
    Hs p k S = (S : ℝ) / k * nb p k S := by
  rw [Hs_eq hp hk, nb_formula hp hk hS]
  have hc : (S.choose k : ℝ) * k = S * ((S - 1).choose (k - 1) : ℝ) := by
    have := Nat.add_one_mul_choose_eq (S - 1) (k - 1)
    rw [Nat.sub_add_cancel hS, Nat.sub_add_cancel hk] at this
    exact_mod_cast this.symm
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff hk0]
  linear_combination ((p : ℝ) - 1) ^ k * ((p : ℝ)⁻¹) ^ S * hc

/-! ### The inner sum of each row ((b)) -/

/-- `⌊kλ + u⌋` (a natural number). -/
noncomputable def fl (lam u : ℝ) (k : ℕ) : ℕ := ⌊(k : ℝ) * lam + u⌋₊

/-- The phase `θ(k) = kλ + u - ⌊kλ + u⌋`. -/
noncomputable def th (lam u : ℝ) (k : ℕ) : ℝ := (k : ℝ) * lam + u - fl lam u k

/-- The main term of row `k`: `p^{-θ(k)} Hs(k, ⌊kλ + u⌋)`. -/
noncomputable def Phi (p : ℕ) (lam u : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-(th lam u k) * Real.log p) * Hs p k (fl lam u k)

theorem th_nonneg {lam u : ℝ} {k : ℕ} (h : 0 ≤ (k : ℝ) * lam + u) : 0 ≤ th lam u k := by
  unfold th fl; linarith [Nat.floor_le h]

theorem th_lt_one (lam u : ℝ) (k : ℕ) : th lam u k < 1 := by
  unfold th fl; linarith [Nat.lt_floor_add_one ((k : ℝ) * lam + u)]

theorem Phi_nonneg (p : ℕ) (lam u : ℝ) (k : ℕ) : 0 ≤ Phi p lam u k :=
  mul_nonneg (Real.exp_pos _).le (Hs_nonneg _ _ _)

/-- The sum over the window in closed form: `z(s) = p^s/q^k`, `S = ⌊kλ + u⌋`, `z(S) = (Y/M) p^{-θ}`. -/
theorem pow_div_pow_eq {p q : ℕ} (hp : 2 ≤ p) (hq : 1 ≤ q) (s k : ℕ) :
    (p : ℝ) ^ s / (q : ℝ) ^ k =
      Real.exp (((s : ℝ) - k * (Real.log q / Real.log p)) * Real.log p) := by
  have hP : (0 : ℝ) < p := by have : (2 : ℝ) ≤ p := by exact_mod_cast hp
                              linarith
  have hQ : (0 : ℝ) < q := by exact_mod_cast hq
  have hlp : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp)).ne'
  rw [show ((s : ℝ) - k * (Real.log q / Real.log p)) * Real.log p
      = s * Real.log p - k * Real.log q by field_simp, Real.exp_sub,
    Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hP, Real.exp_log hQ]

/-- **Row sum** ((b)): if `M, y > 0`, `y ≤ Y`, `kλ + u ≥ 0`, then
`|Σ_{s: y < p^s M/q^k ≤ Y} p^s/q^k P(s_k = s) - (Y/M) Phi(k)| ≤ y/M`. -/
theorem row_bound {p q : ℕ} (hp : 2 ≤ p) (hq : 1 ≤ q) {y Y M : ℝ} (hM : 0 < M) (hy : 0 < y)
    (hyY : y ≤ Y) {k : ℕ}
    (hpos : 0 ≤ (k : ℝ) * (Real.log q / Real.log p) + Real.log (Y / M) / Real.log p) :
    |(∑' s : ℕ, if y < (p : ℝ) ^ s * M / (q : ℝ) ^ k ∧ (p : ℝ) ^ s * M / (q : ℝ) ^ k ≤ Y then
        (p : ℝ) ^ s / (q : ℝ) ^ k * nb p k s else 0)
      - Y / M * Phi p (Real.log q / Real.log p) (Real.log (Y / M) / Real.log p) k| ≤ y / M := by
  classical
  set lam := Real.log q / Real.log p with hlam
  set u := Real.log (Y / M) / Real.log p with hu
  have hP2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hP : (0 : ℝ) < p := by linarith
  have hQ : (0 : ℝ) < q := by exact_mod_cast hq
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have hY : 0 < Y := lt_of_lt_of_le hy hyY
  have hYM : 0 < Y / M := div_pos hY hM
  set z : ℕ → ℝ := fun s => (p : ℝ) ^ s / (q : ℝ) ^ k with hz
  have hz0 : ∀ s, 0 < z s := fun s => by simp only [hz]; positivity
  have hzexp : ∀ s : ℕ, z s = Real.exp (((s : ℝ) - k * lam) * Real.log p) :=
    fun s => pow_div_pow_eq hp hq s k
  have hYMexp : Y / M = Real.exp (u * Real.log p) := by
    rw [hu, div_mul_cancel₀ _ hlp.ne', Real.exp_log hYM]
  set S := fl lam u k with hSdef
  -- upper end: `z(s) M ≤ Y ⟺ s ≤ S`
  have hup : ∀ s : ℕ, (p : ℝ) ^ s * M / (q : ℝ) ^ k ≤ Y ↔ s ≤ S := by
    intro s
    rw [show (p : ℝ) ^ s * M / (q : ℝ) ^ k = z s * M by simp only [hz]; ring,
      ← le_div_iff₀ hM, hzexp, hYMexp, Real.exp_le_exp, mul_le_mul_iff_of_pos_right hlp, hSdef,
      fl, Nat.le_floor_iff hpos]
    constructor <;> intro h <;> linarith
  -- the series is a finite sum
  set term : ℕ → ℝ := fun s => if y < (p : ℝ) ^ s * M / (q : ℝ) ^ k ∧
      (p : ℝ) ^ s * M / (q : ℝ) ^ k ≤ Y then (p : ℝ) ^ s / (q : ℝ) ^ k * nb p k s else 0 with hterm
  have htsum : ∑' s : ℕ, term s = ∑ s ∈ Finset.range (S + 1), term s := by
    apply tsum_eq_sum
    intro s hs
    rw [Finset.mem_range, not_lt] at hs
    simp only [hterm]
    rw [if_neg]
    rintro ⟨-, h⟩
    have := (hup s).mp h
    omega
  -- truncation at the lower end
  set lo : ℕ → ℝ := fun s => if (p : ℝ) ^ s * M / (q : ℝ) ^ k ≤ y then z s * nb p k s else 0
    with hlo
  have hterm' : ∀ s ∈ Finset.range (S + 1), term s = z s * nb p k s - lo s := by
    intro s hs
    rw [Finset.mem_range] at hs
    have hup' := (hup s).mpr (by omega)
    simp only [hterm, hlo, hz]
    by_cases h : (p : ℝ) ^ s * M / (q : ℝ) ^ k ≤ y
    · rw [if_neg (fun h' => absurd h'.1 (not_lt.mpr h)), if_pos h, sub_self]
    · rw [if_pos ⟨not_le.mp h, hup'⟩, if_neg h, sub_zero]
  -- the main term
  have hmain : ∑ s ∈ Finset.range (S + 1), z s * nb p k s = z S * Hs p k S := by
    unfold Hs
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mem_range] at hs
    have hpow : (p : ℝ) ^ S * ((p : ℝ)⁻¹) ^ (S - s) = (p : ℝ) ^ s := by
      have h1 : (p : ℝ) ^ S = (p : ℝ) ^ s * (p : ℝ) ^ (S - s) := by
        rw [← pow_add, Nat.add_sub_cancel' (by omega)]
      rw [h1, mul_assoc, ← mul_pow, mul_inv_cancel₀ hP.ne', one_pow, mul_one]
    simp only [hz]
    rw [← hpow]
    ring
  have hzS : z S = Y / M * Real.exp (-(th lam u k) * Real.log p) := by
    rw [hzexp, hYMexp, ← Real.exp_add]
    congr 1
    unfold th
    rw [← hSdef]
    ring
  have hlo0 : ∀ s, 0 ≤ lo s := by
    intro s; simp only [hlo]; split_ifs
    · exact mul_nonneg (hz0 s).le (nb_nonneg _ _ _)
    · exact le_rfl
  have hlo1 : ∀ s, lo s ≤ y / M * nb p k s := by
    intro s; simp only [hlo]; split_ifs with h
    · apply mul_le_mul_of_nonneg_right _ (nb_nonneg _ _ _)
      rw [le_div_iff₀ hM]
      calc z s * M = (p : ℝ) ^ s * M / (q : ℝ) ^ k := by simp only [hz]; ring
        _ ≤ y := h
    · exact mul_nonneg (div_nonneg hy.le hM.le) (nb_nonneg _ _ _)
  have hLo : ∑ s ∈ Finset.range (S + 1), lo s ≤ y / M := by
    calc ∑ s ∈ Finset.range (S + 1), lo s ≤ ∑ s ∈ Finset.range (S + 1), y / M * nb p k s :=
          Finset.sum_le_sum fun s _ => hlo1 s
      _ = y / M * ∑ s ∈ Finset.range (S + 1), nb p k s := by rw [Finset.mul_sum]
      _ ≤ y / M * 1 := mul_le_mul_of_nonneg_left (sum_nb_le_one _ _ _) (div_nonneg hy.le hM.le)
      _ = y / M := mul_one _
  have hLo0 : 0 ≤ ∑ s ∈ Finset.range (S + 1), lo s := Finset.sum_nonneg fun s _ => hlo0 s
  have e : ∑' s : ℕ, term s - Y / M * Phi p lam u k = -∑ s ∈ Finset.range (S + 1), lo s := by
    rw [htsum, Finset.sum_congr rfl hterm', Finset.sum_sub_distrib, hmain, hzS]
    unfold Phi
    rw [← hSdef]
    ring
  change |∑' s : ℕ, term s - Y / M * Phi p lam u k| ≤ y / M
  rw [e, abs_neg, abs_of_nonneg hLo0]
  exact hLo

end DKernAux

end ND

end GGMCollatz
