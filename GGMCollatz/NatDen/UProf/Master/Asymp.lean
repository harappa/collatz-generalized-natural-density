import GGMCollatz.NatDen.UProf.Master.Prob
import GGMCollatz.NatDen.UProf.Master.Count

/-!
# Asymptotic ingredients of (UM) (`x → ∞`)

`L = log x`. `m₀ ≥ cL` (`c = (α-1)/(8d)`), `n₀ ≤ L/3`, `m₁ = ⌊L^{0.4}⌋`, `Mlo ≥ x e^{-L^{0.7}}`, `q^{n₀} ≤ x^{1/5}`.

* `eventually_side`: the applicability conditions of the core `core` and of the product formula (`2 ≤ k`, `k^{1/4} ≤ m₁ ≤ k^{1/2}`, `m₁ ≤ m₀`),
  and the lower bound `Y ≤ 2p Z` for the number of points of the window.
* `asymp`: the sum of the four errors is at most `K' L^{-1/5}`. The main term is the product-formula error
  `ε β N_R ≪ L^{-1/4} · L^{-1/2} · L^{0.55} = L^{-1/5}`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace MasterAux

variable (F : Family)

/-- The scale of the product-formula error `ε(x) = K (m₁^{-1} + √(m₁ log n₀ / m₀))`. -/
noncomputable def epsX (Kc α x : ℝ) : ℝ :=
  Kc * ((m1 x : ℝ) ^ (-1 : ℝ) + Real.sqrt ((m1 x : ℝ) * Real.log (F.nZero x) / (F.mZero α x)))

/-- `R_k` is monotone in `k`. -/
theorem rad_mono {k n : ℕ} (h : k ≤ n) : rad k ≤ rad n := by
  unfold rad
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, zero_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg n)
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast h
    exact mul_le_mul hkn (Real.log_le_log hk' hkn) (Real.log_natCast_nonneg k) (Nat.cast_nonneg n)

/-- The product-formula error `m₁^{-1} + √(m₁ log k / k)` is at most `ε(x)/K` for `k ∈ [m₀, n₀]`. -/
theorem mix_err_le {Kc α x : ℝ} (hKc : 0 ≤ Kc) {k : ℕ} (hm0 : 1 ≤ F.mZero α x) (hk0 : F.mZero α x ≤ k)
    (hk1 : k ≤ F.nZero x) :
    Kc * ((m1 x : ℝ) ^ (-1 : ℝ) + Real.sqrt ((m1 x : ℝ) * Real.log k / k)) ≤ epsX F Kc α x := by
  unfold epsX
  refine mul_le_mul_of_nonneg_left (add_le_add le_rfl (Real.sqrt_le_sqrt ?_)) hKc
  have hm0r : (1 : ℝ) ≤ F.mZero α x := by exact_mod_cast hm0
  have hkr : (F.mZero α x : ℝ) ≤ k := by exact_mod_cast hk0
  have hk1r : (k : ℝ) ≤ F.nZero x := by exact_mod_cast hk1
  have hkpos : (0 : ℝ) < k := by linarith
  have hlogk : 0 ≤ Real.log k := Real.log_natCast_nonneg k
  have hlog : Real.log k ≤ Real.log (F.nZero x) := Real.log_le_log hkpos hk1r
  exact div_le_div₀ (mul_nonneg (Nat.cast_nonneg _) (le_trans hlogk hlog))
    (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)) (by linarith) hkr

/-- Lower bound for the number of points of a window: `#(ℕ_p ∩ [lo, hi]) ≥ (hi - 1)/p - lo - 1` (counting only numbers of the form `p j + 1`). -/
theorem card_logWindow_ge {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : 1 ≤ hi) :
    (hi - 1) / F.p - lo - 1 ≤ ((F.logWindow lo hi).card : ℝ) := by
  have hp2 := F.two_le_p
  have hpr : (0 : ℝ) < F.p := F.p_real_pos
  set a := ⌈lo⌉₊ with ha
  set b := ⌊(hi - 1) / F.p⌋₊ with hb
  have hmaps : Set.MapsTo (fun j : ℕ => F.p * j + 1) ↑(Finset.Icc a b) ↑(F.logWindow lo hi) := by
    intro j hj
    rw [Finset.coe_Icc, Set.mem_Icc] at hj
    rw [Finset.mem_coe, F.mem_logWindow_iff]
    beta_reduce
    refine ⟨?_, ?_, ?_⟩
    · rw [show F.p * j + 1 = 1 + j * F.p by ring, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (by omega)]
      omega
    · have h1 : lo ≤ (j : ℝ) := Nat.ceil_le.mp hj.1
      have h2 : (j : ℝ) ≤ (F.p : ℝ) * j :=
        le_mul_of_one_le_left (Nat.cast_nonneg _) (by exact_mod_cast (show 1 ≤ F.p by omega))
      push_cast
      linarith
    · have h2 : (j : ℝ) ≤ (hi - 1) / F.p :=
        (Nat.le_floor_iff (div_nonneg (by linarith) hpr.le)).mp hj.2
      rw [le_div_iff₀ hpr] at h2
      push_cast
      linarith
  have hinj : Set.InjOn (fun j : ℕ => F.p * j + 1) ↑(Finset.Icc a b) := by
    intro j _ j' _ h
    simp only at h
    have : F.p * j = F.p * j' := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have hc := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Nat.card_Icc] at hc
  have h1 : (hi - 1) / F.p < (b : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2 : (a : ℝ) < lo + 1 := Nat.ceil_lt_add_one hlo
  rcases le_or_gt a (b + 1) with hle | hgt
  · have : ((b + 1 - a : ℕ) : ℝ) ≤ ((F.logWindow lo hi).card : ℝ) := by exact_mod_cast hc
    rw [Nat.cast_sub hle] at this
    push_cast at this
    linarith
  · have hba : (b : ℝ) + 1 < a := by exact_mod_cast hgt
    have : (0 : ℝ) ≤ (F.logWindow lo hi).card := Nat.cast_nonneg _
    linarith

/-- The number of points `Z` of the window is at least `Y/(2p)` (for large `x`). -/
theorem eventually_wCard {α : ℝ} (hα : 1 < α) : ∀ᶠ x : ℝ in Filter.atTop,
    (x ^ α) ^ α ≤ 2 * F.p * wCard F α x := by
  have hα0 : 0 < α := by linarith
  have ht1 : Filter.Tendsto (fun x : ℝ => x ^ α) Filter.atTop Filter.atTop := tendsto_rpow_atTop hα0
  have ht2 : Filter.Tendsto (fun x : ℝ => (x ^ α) ^ (α - 1)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp ht1
  have hP : (0 : ℝ) < F.p := F.p_real_pos
  filter_upwards [ht1.eventually_ge_atTop 1, ht2.eventually_ge_atTop (4 * F.p + 2)] with x h1 h2
  set y := x ^ α with hydef
  have hy0 : 0 < y := by linarith
  have hY : y * y ^ (α - 1) = y ^ α := by
    rw [← Real.rpow_one_add' hy0.le (by linarith)]
    congr 1; ring
  have hYge : (4 * F.p + 2) * y ≤ y ^ α := by
    rw [← hY]; nlinarith
  have hY1 : 1 ≤ y ^ α := by nlinarith
  have hc := card_logWindow_ge F hy0.le hY1
  unfold wCard
  rw [← hydef]
  have e : (y ^ α - 1) / F.p * F.p = y ^ α - 1 := div_mul_cancel₀ _ hP.ne'
  nlinarith

/-- The window conditions and the applicability conditions of the product formula. -/
theorem eventually_side {α : ℝ} (hα : 1 < α) : ∀ᶠ x : ℝ in Filter.atTop,
    0 < x ∧ 0 < (x ^ α) ^ α ∧ 0 < F.Mlo α x ∧ m1 x ≤ F.mZero α x ∧ 1 ≤ F.mZero α x ∧
    (∀ k : ℕ, F.mZero α x ≤ k → k ≤ F.nZero x →
      2 ≤ k ∧ (k : ℝ) ^ (1 / 4 : ℝ) ≤ m1 x ∧ (m1 x : ℝ) ≤ (k : ℝ) ^ (1 / 2 : ℝ)) ∧
    (x ^ α) ^ α ≤ 2 * F.p * wCard F α x := by
  have hd := F.drift_pos
  set c := (α - 1) / (8 * F.drift) with hc
  have hc0 : 0 < c := div_pos (by linarith) (by linarith)
  have hsqc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ), F.eventually_mZero_ge hα,
    Family.eventually_log_ge (max 2 (2 / c)),
    Family.eventually_mul_log_rpow_le (show (0.4 : ℝ) < 1 by norm_num) (1 / c),
    Family.eventually_add_mul_rpow_le (show (0.25 : ℝ) < 0.4 by norm_num) (by norm_num) 1 1 one_pos,
    Family.eventually_mul_log_rpow_le (show (0.4 : ℝ) < 0.5 by norm_num) (1 / Real.sqrt c),
    eventually_wCard F hα, Filter.eventually_ge_atTop (1 : ℝ)]
    with x hx hm0 hL h1 h2 h3 hW hx1
  set L := Real.log x with hLdef
  obtain ⟨hm0c, hm01⟩ := hm0
  have hcL : c * L ≤ F.mZero α x := by
    have : c * L = (α - 1) * L / (8 * F.drift) := by rw [hc]; ring
    rw [this]; exact hm0c
  have hL2 : 2 ≤ L := le_trans (le_max_left _ _) hL
  have hLc : 2 / c ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 0 < L := by linarith
  have hm1le : (m1 x : ℝ) ≤ L ^ (0.4 : ℝ) := Nat.floor_le (Real.rpow_nonneg hLpos.le _)
  have hm1ge : L ^ (0.4 : ℝ) - 1 < (m1 x : ℝ) := by
    have := Nat.lt_floor_add_one (L ^ (0.4 : ℝ))
    unfold m1; linarith
  rw [Real.rpow_one] at h1
  have hL04 : L ^ (0.4 : ℝ) ≤ c * L := by
    have := mul_le_mul_of_nonneg_left h1 hc0.le
    rwa [← mul_assoc, mul_one_div_cancel hc0.ne', one_mul] at this
  have hn0 : (F.nZero x : ℝ) ≤ L := by have := F.nZero_le hx1; linarith
  refine ⟨hx, by positivity, Real.exp_pos _, ?_, hm01, ?_, hW⟩
  · have : (m1 x : ℝ) ≤ F.mZero α x := by linarith
    exact_mod_cast this
  · intro k hk0 hk1
    have hkr0 : (F.mZero α x : ℝ) ≤ k := by exact_mod_cast hk0
    have hkr1 : (k : ℝ) ≤ F.nZero x := by exact_mod_cast hk1
    refine ⟨?_, ?_, ?_⟩
    · have h2c : 2 ≤ c * L := by rw [div_le_iff₀ hc0] at hLc; linarith
      have : (2 : ℝ) ≤ k := by linarith
      exact_mod_cast this
    · have e1 : (k : ℝ) ^ (1 / 4 : ℝ) ≤ L ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by norm_num)
      have e2 : L ^ (1 / 4 : ℝ) = L ^ (0.25 : ℝ) := by norm_num
      linarith
    · rw [← Real.sqrt_eq_rpow]
      have e1 : L ^ (0.4 : ℝ) ≤ Real.sqrt c * L ^ (0.5 : ℝ) := by
        have := mul_le_mul_of_nonneg_left h3 hsqc.le
        rwa [← mul_assoc, mul_one_div_cancel hsqc.ne', one_mul] at this
      have e2 : L ^ (0.5 : ℝ) = Real.sqrt L := by rw [Real.sqrt_eq_rpow]; norm_num
      have e3 : Real.sqrt c * Real.sqrt L = Real.sqrt (c * L) := (Real.sqrt_mul hc0.le L).symm
      have e4 : Real.sqrt (c * L) ≤ Real.sqrt k := Real.sqrt_le_sqrt (by linarith)
      rw [e2, e3] at e1
      linarith

end MasterAux

end ND

end GGMCollatz
