import GGMCollatz.NatDen.UProf.URD.Disc

/-!
# Auxiliary for (URD): bounds as `x → ∞`

* `wCard_ge`: the number of window points `Z = #(ℕ_p ∩ [y, Y]) ≥ Y/(2p)` (`y = x^α`, `Y = y^α`, `y^{α-1} ≥ 6p`, `y ≥ 1`).
  `N ↦ pN + 1` is an injection from `[⌈y⌉, ⌊(Y-1)/p⌋]` into the window.
* `eventually_Mlo_ge`: `Mlo ≥ x^{9/10}` (`log^{0.7} x ≤ log x/10`, `d m₀ ≥ 0`).
* `q_pow_le`: if `k ≤ n₀`, then `q^k ≤ x^{1/5}`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace URDAux

variable (F : Family)

/-- If `y ≥ 1` and `Y ≥ 6p y`, then `Z = #(ℕ_p ∩ [y, Y]) ≥ Y/(2p)`. -/
theorem card_logWindow_ge {y Y : ℝ} (hy : 1 ≤ y) (hY : 6 * (F.p : ℝ) * y ≤ Y) :
    Y / (2 * (F.p : ℝ)) ≤ ((F.logWindow y Y).card : ℝ) := by
  have hp2 := F.p_real_two_le
  have hp0 : (0 : ℝ) < F.p := by linarith
  have hY0 : 0 ≤ Y := by nlinarith
  have hA : 0 ≤ (Y - 1) / F.p := by
    apply div_nonneg _ hp0.le; nlinarith
  -- the injection `N ↦ pN + 1`
  have hmaps : ∀ N ∈ Finset.Icc ⌈y⌉₊ ⌊(Y - 1) / F.p⌋₊, F.p * N + 1 ∈ F.logWindow y Y := by
    intro N hN
    rw [Finset.mem_Icc] at hN
    obtain ⟨h1, h2⟩ := hN
    have hyN : y ≤ (N : ℝ) := Nat.ceil_le.mp h1
    have hNA : (N : ℝ) ≤ (Y - 1) / F.p := by
      have := Nat.floor_le hA
      exact le_trans (by exact_mod_cast h2) this
    have hup : ((F.p * N + 1 : ℕ) : ℝ) ≤ Y := by
      push_cast
      rw [le_div_iff₀ hp0] at hNA
      linarith
    have hlo : y ≤ ((F.p * N + 1 : ℕ) : ℝ) := by
      push_cast
      have : (N : ℝ) ≤ F.p * N := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
      linarith
    unfold Family.logWindow
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_, hlo, hup⟩
    · have := Nat.le_ceil Y
      have : ((F.p * N + 1 : ℕ) : ℝ) ≤ (⌈Y⌉₊ : ℝ) := le_trans hup this
      have : F.p * N + 1 ≤ ⌈Y⌉₊ := by exact_mod_cast this
      omega
    · rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod,
        Nat.mod_eq_of_lt (by have := F.two_le_p; omega)]
      omega
  have hinj : Set.InjOn (fun N => F.p * N + 1) (Finset.Icc ⌈y⌉₊ ⌊(Y - 1) / F.p⌋₊ : Set ℕ) := by
    intro a _ b _ hab
    simp only at hab
    have hp : 0 < F.p := by have := F.two_le_p; omega
    have : F.p * a = F.p * b := by omega
    exact Nat.eq_of_mul_eq_mul_left hp this
  have hcard := Finset.card_le_card_of_injOn (fun N => F.p * N + 1) hmaps hinj
  rw [Nat.card_Icc] at hcard
  have hc1 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one (by linarith)
  have hc2 : (Y - 1) / F.p - 1 < (⌊(Y - 1) / F.p⌋₊ : ℝ) := Nat.sub_one_lt_floor _
  have hkey : Y / (2 * (F.p : ℝ)) ≤ (⌊(Y - 1) / F.p⌋₊ : ℝ) + 1 - ⌈y⌉₊ := by
    have e1 : (Y - 1) / F.p = Y / F.p - 1 / F.p := by ring
    have e2 : Y / F.p = 2 * (Y / (2 * F.p)) := by field_simp
    have h3 : 1 / (F.p : ℝ) ≤ 1 := by rw [div_le_one hp0]; linarith
    have h4 : 3 * y ≤ Y / (2 * F.p) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  have hle : ⌈y⌉₊ ≤ ⌊(Y - 1) / F.p⌋₊ + 1 := by
    have h5 : (0 : ℝ) < (⌊(Y - 1) / F.p⌋₊ : ℝ) + 1 - ⌈y⌉₊ := by
      have : 0 < Y / (2 * (F.p : ℝ)) := by
        apply div_pos _ (by positivity); nlinarith
      linarith
    have : (⌈y⌉₊ : ℝ) < (⌊(Y - 1) / F.p⌋₊ : ℝ) + 1 := by linarith
    exact_mod_cast this.le
  calc Y / (2 * (F.p : ℝ)) ≤ (⌊(Y - 1) / F.p⌋₊ : ℝ) + 1 - ⌈y⌉₊ := hkey
    _ = ((⌊(Y - 1) / F.p⌋₊ + 1 - ⌈y⌉₊ : ℕ) : ℝ) := by rw [Nat.cast_sub hle]; push_cast; ring
    _ ≤ ((F.logWindow y Y).card : ℝ) := by exact_mod_cast hcard

/-- As `x → ∞`, `Z ≥ Y/(2p)` and `1 ≤ y ≤ Y` (`α > 1`). -/
theorem eventually_wCard_ge {α : ℝ} (hα : 1 < α) : ∀ᶠ x : ℝ in Filter.atTop,
    1 ≤ x ^ α ∧ x ^ α ≤ (x ^ α) ^ α ∧ (x ^ α) ^ α / (2 * (F.p : ℝ)) ≤ wCard F α x := by
  have hα0 : 0 < α := by linarith
  have ht : Filter.Tendsto (fun x : ℝ => (x ^ α) ^ (α - 1)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp (tendsto_rpow_atTop hα0)
  filter_upwards [ht.eventually_ge_atTop (6 * (F.p : ℝ)), Filter.eventually_ge_atTop (1 : ℝ)] with
    x hx hx1
  have hy1 : 1 ≤ x ^ α := Real.one_le_rpow hx1 hα0.le
  have hy0 : 0 < x ^ α := by linarith
  have hsplit : (x ^ α) ^ α = x ^ α * (x ^ α) ^ (α - 1) := by
    rw [Real.rpow_sub hy0, Real.rpow_one]; field_simp
  have hyY : x ^ α ≤ (x ^ α) ^ α := by
    rw [hsplit]
    have : 1 ≤ (x ^ α) ^ (α - 1) := by
      have := F.p_real_two_le
      linarith
    nlinarith
  refine ⟨hy1, hyY, ?_⟩
  unfold wCard
  apply card_logWindow_ge F hy1
  rw [hsplit]
  have : 6 * (F.p : ℝ) * x ^ α = x ^ α * (6 * F.p) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left hx hy0.le

/-- As `x → ∞`, `Mlo ≥ x^{9/10}`. -/
theorem eventually_Mlo_ge (α : ℝ) : ∀ᶠ x : ℝ in Filter.atTop,
    x ^ (9 / 10 : ℝ) ≤ F.Mlo α x := by
  have hd := F.drift_pos
  filter_upwards [Family.eventually_mul_log_rpow_le (show (0.7 : ℝ) < 1 by norm_num) 10,
    Filter.eventually_gt_atTop (0 : ℝ)] with x hW hx0
  rw [Real.rpow_one] at hW
  unfold Family.Mlo
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.mpr
  have hm : (0 : ℝ) ≤ F.drift * F.mZero α x := mul_nonneg hd.le (Nat.cast_nonneg _)
  linarith

/-- If `k ≤ n₀` and `x > 0`, then `q^k ≤ x^{1/5}`. -/
theorem q_pow_le {x : ℝ} (hx : 0 < x) (hx1 : 1 ≤ x) {k : ℕ} (hk : k ≤ F.nZero x) :
    (F.q : ℝ) ^ k ≤ x ^ (1 / 5 : ℝ) := by
  have hq := F.log_q_pos
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hn0 : (F.nZero x : ℝ) ≤ Real.log x / (5 * Real.log F.q) := by
    unfold Family.nZero; exact Nat.floor_le (by positivity)
  have hkR : (k : ℝ) ≤ F.nZero x := by exact_mod_cast hk
  rw [← Real.exp_log F.q_real_pos, ← Real.exp_nat_mul, Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  calc (k : ℝ) * Real.log F.q ≤ Real.log x / (5 * Real.log F.q) * Real.log F.q :=
        mul_le_mul_of_nonneg_right (le_trans hkR hn0) hq.le
    _ = Real.log x * (1 / 5) := by field_simp

end URDAux

end ND

end GGMCollatz
