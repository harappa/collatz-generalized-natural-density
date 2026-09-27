import GGMCollatz.StatementB

/-!
# Removing (d), reduction 2: general tools (ingredients of Lemma 3.6 of the paper)

* `one_le_log`, `sum_Icc_one_div_le`: for `x ≥ 3`, `log x ≥ 1` and `∑_{N ≤ n} 1/N ≤ 2 log x` (`n ≤ x`).
* `mainA_of_large`, `mainB_of_large`: it suffices to prove the rate for `N₀ ≥ N₁`; small `N₀` are absorbed into the
  constant by the trivial bounds (`∑ 1/N ≤ 2 log x`, `# ≤ X`) (in the accompanying paper: "`N₀ < 2h` is trivial
  with `K ≥ (2h)^c`").
* `sum_comp_le`: transferring a sum along a map whose fibres have size at most `m` (in the accompanying paper:
  "at most `p-1` points for each `M`").
* `geom_le_two`: `∑_k p^{-k} ≤ 2` (`p ≥ 2`).
* `rpow_div_le`: `⌊N₀/d⌋^{-c} ≤ (2d)^c N₀^{-c}` (`N₀ ≥ d`). The exponent does not change.
-/

namespace GGMCollatz

namespace Gen

open Finset

lemma one_le_log {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- Harmonic sum: if `n ≤ x` and `x ≥ 3`, then `∑_{1 ≤ N ≤ n} 1/N ≤ 2 log x`. -/
lemma sum_Icc_one_div_le (n : ℕ) {x : ℝ} (hx : 3 ≤ x) (hn : (n : ℝ) ≤ x) :
    ∑ N ∈ Finset.Icc 1 n, (1 / (N : ℝ)) ≤ 2 * Real.log x := by
  have h2 : ∑ N ∈ Finset.Icc 1 n, (1 / (N : ℝ)) = (harmonic n : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast; simp_rw [one_div]
  have h3 := harmonic_le_one_add_log n
  have h4 : Real.log n ≤ Real.log x := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg (by linarith)
    · exact Real.log_le_log (by exact_mod_cast hpos) hn
  have h5 := one_le_log hx
  linarith

/-- If `N₀ < N₁`, then `1 ≤ (N₁ + 1)^c N₀^{-c}`. -/
lemma one_le_rpow_mul {N₀ N₁ : ℕ} (hN₀ : 1 ≤ N₀) (hN : N₀ < N₁) {c : ℝ} (hc : 0 ≤ c) :
    1 ≤ ((N₁ : ℝ) + 1) ^ c * (N₀ : ℝ) ^ (-c) := by
  have hN₀pos : (0 : ℝ) < N₀ := by exact_mod_cast hN₀
  have hle : (N₀ : ℝ) ≤ (N₁ : ℝ) + 1 := by
    have : (N₀ : ℝ) < N₁ := by exact_mod_cast hN
    linarith
  have hmono : (N₀ : ℝ) ^ c ≤ ((N₁ : ℝ) + 1) ^ c := Real.rpow_le_rpow hN₀pos.le hle hc
  have hpow : 0 ≤ (N₀ : ℝ) ^ (-c) := Real.rpow_nonneg hN₀pos.le _
  calc (1 : ℝ) = (N₀ : ℝ) ^ c * (N₀ : ℝ) ^ (-c) := by
        rw [Real.rpow_neg hN₀pos.le, mul_inv_cancel₀ (by positivity)]
    _ ≤ ((N₁ : ℝ) + 1) ^ c * (N₀ : ℝ) ^ (-c) := mul_le_mul_of_nonneg_right hmono hpow

/-- **Absorbing small `N₀` in (A)**: if the rate holds for `N₀ ≥ N₁`, then `mainA_gen_statement` holds. -/
lemma mainA_of_large (G : FamilyGen) (N₁ : ℕ) {K c : ℝ} (hK : 0 < K) (hc : 0 < c)
    (h : ∀ N₀ : ℕ, 1 ≤ N₀ → N₁ ≤ N₀ → ∀ x : ℝ, 3 ≤ x →
      ∑ N ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun N => N₀ < G.Cmin N), (1 / (N : ℝ))
        ≤ K * (N₀ : ℝ) ^ (-c) * Real.log x) :
    G.mainA_gen_statement := by
  refine ⟨max K (2 * ((N₁ : ℝ) + 1) ^ c), c, lt_max_of_lt_left hK, hc, ?_⟩
  intro N₀ hN₀ x hx
  have hlog : 0 ≤ Real.log x := by linarith [one_le_log hx]
  have hpow : 0 ≤ (N₀ : ℝ) ^ (-c) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  by_cases hN : N₁ ≤ N₀
  · calc _ ≤ K * (N₀ : ℝ) ^ (-c) * Real.log x := h N₀ hN₀ hN x hx
      _ ≤ max K (2 * ((N₁ : ℝ) + 1) ^ c) * (N₀ : ℝ) ^ (-c) * Real.log x := by
          gcongr; exact le_max_left _ _
  · push Not at hN
    have hsub : ∑ N ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun N => N₀ < G.Cmin N), (1 / (N : ℝ)) ≤
        ∑ N ∈ Finset.Icc 1 ⌊x⌋₊, (1 / (N : ℝ)) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    have hH := sum_Icc_one_div_le ⌊x⌋₊ hx (Nat.floor_le (by linarith))
    have hone := one_le_rpow_mul hN₀ hN hc.le
    calc _ ≤ ∑ N ∈ Finset.Icc 1 ⌊x⌋₊, (1 / (N : ℝ)) := hsub
      _ ≤ 2 * Real.log x := hH
      _ ≤ 2 * (((N₁ : ℝ) + 1) ^ c * (N₀ : ℝ) ^ (-c)) * Real.log x := by nlinarith
      _ = (2 * ((N₁ : ℝ) + 1) ^ c) * (N₀ : ℝ) ^ (-c) * Real.log x := by ring
      _ ≤ max K (2 * ((N₁ : ℝ) + 1) ^ c) * (N₀ : ℝ) ^ (-c) * Real.log x := by
          gcongr; exact le_max_right _ _

/-- **Absorbing small `N₀` in (B)**. -/
lemma mainB_of_large (G : FamilyGen) (N₁ : ℕ) {K c : ℝ} (hK : 0 < K) (hc : 0 < c)
    (h : ∀ N₀ : ℕ, 1 ≤ N₀ → N₁ ≤ N₀ → ∀ X : ℝ, 1 ≤ X →
      (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => N₀ < G.Cmin N)).card : ℝ) ≤ K * X * (N₀ : ℝ) ^ (-c)) :
    G.mainB_gen_statement := by
  refine ⟨max K (((N₁ : ℝ) + 1) ^ c), c, lt_max_of_lt_left hK, hc, ?_⟩
  intro N₀ hN₀ X hX
  have hpow : 0 ≤ (N₀ : ℝ) ^ (-c) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hX0 : 0 ≤ X := by linarith
  by_cases hN : N₁ ≤ N₀
  · calc _ ≤ K * X * (N₀ : ℝ) ^ (-c) := h N₀ hN₀ hN X hX
      _ ≤ max K (((N₁ : ℝ) + 1) ^ c) * X * (N₀ : ℝ) ^ (-c) := by
          gcongr; exact le_max_left _ _
  · push Not at hN
    have hcard : (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => N₀ < G.Cmin N)).card : ℝ) ≤ X := by
      have h1 := card_filter_le (Finset.Icc 1 ⌊X⌋₊) (fun N => N₀ < G.Cmin N)
      rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
      calc _ ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast h1
        _ ≤ X := Nat.floor_le hX0
    have hone := one_le_rpow_mul hN₀ hN hc.le
    calc _ ≤ X := hcard
      _ ≤ X * (((N₁ : ℝ) + 1) ^ c * (N₀ : ℝ) ^ (-c)) := by nlinarith
      _ = ((N₁ : ℝ) + 1) ^ c * X * (N₀ : ℝ) ^ (-c) := by ring
      _ ≤ max K (((N₁ : ℝ) + 1) ^ c) * X * (N₀ : ℝ) ^ (-c) := by
          gcongr; exact le_max_right _ _

/-- Transferring a sum along a map `φ : s → t` whose fibres have size at most `m`. -/
lemma sum_comp_le {s t : Finset ℕ} (φ : ℕ → ℕ) (f : ℕ → ℝ) (hf : ∀ M ∈ t, 0 ≤ f M)
    (hmaps : ∀ N ∈ s, φ N ∈ t) (m : ℕ)
    (hfib : ∀ M ∈ t, (s.filter (fun N => φ N = M)).card ≤ m) :
    ∑ N ∈ s, f (φ N) ≤ m * ∑ M ∈ t, f M := by
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro M hM
  rw [Finset.sum_congr rfl (fun N hN => by rw [(Finset.mem_filter.mp hN).2]), Finset.sum_const,
    nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfib M hM) (hf M hM)

/-- `∑_{k < n} p^{-k} ≤ 2` (`p ≥ 2`). -/
lemma geom_le_two {p : ℕ} (hp : 2 ≤ p) (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 / (p : ℝ)) ^ k ≤ 2 := by
  have h12 : 1 / (p : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp)
  calc _ ≤ ∑ k ∈ Finset.range n, (1 / (2 : ℝ)) ^ k :=
        Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ (by positivity) h12 k)
    _ ≤ 2 := sum_geometric_two_le n

/-- If `N₀ ≥ d ≥ 1`, then `⌊N₀/d⌋^{-c} ≤ (2d)^c N₀^{-c}`. -/
lemma rpow_div_le {N₀ d : ℕ} (hd : 0 < d) (hdN₀ : d ≤ N₀) {c : ℝ} (hc : 0 ≤ c) :
    ((N₀ / d : ℕ) : ℝ) ^ (-c) ≤ (2 * (d : ℝ)) ^ c * (N₀ : ℝ) ^ (-c) := by
  set t := N₀ / d with ht
  have ht1 : 1 ≤ t := (Nat.one_le_div_iff hd).mpr hdN₀
  have hdiv := Nat.div_add_mod N₀ d
  have hmod := Nat.mod_lt N₀ hd
  have hdt : d ≤ d * t := Nat.le_mul_of_pos_right d ht1
  have hN₀le : N₀ ≤ 2 * (d * t) := by
    rw [← ht] at hdiv
    omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hN₀0 : (0 : ℝ) < N₀ := by exact_mod_cast (lt_of_lt_of_le hd hdN₀)
  have hle : (N₀ : ℝ) / (2 * d) ≤ (t : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have : (N₀ : ℝ) ≤ 2 * ((d : ℝ) * t) := by exact_mod_cast hN₀le
    linarith
  calc ((t : ℕ) : ℝ) ^ (-c) ≤ ((N₀ : ℝ) / (2 * d)) ^ (-c) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
    _ = (N₀ : ℝ) ^ (-c) / (2 * (d : ℝ)) ^ (-c) := Real.div_rpow hN₀0.le (by positivity) _
    _ = (2 * (d : ℝ)) ^ c * (N₀ : ℝ) ^ (-c) := by
        rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ)) c, div_inv_eq_mul, mul_comm]

/-- `log(Qx) ≤ (1 + log Q) log x` (`Q ≥ 1`, `x ≥ 3`). -/
lemma log_mul_le {Q x : ℝ} (hQ : 1 ≤ Q) (hx : 3 ≤ x) :
    Real.log (Q * x) ≤ (1 + Real.log Q) * Real.log x := by
  rw [Real.log_mul (by linarith) (by linarith)]
  have h1 := one_le_log hx
  have h2 := Real.log_nonneg hQ
  nlinarith

end Gen

end GGMCollatz
