import GGMCollatz.NatDen.UProf.Conc.Window

/-!
# Auxiliary for (UC): good tuples occur with high probability on the uniform window (the uniform-window side of the no-hit argument)

Source: `unif_valuation_law` and `unif_bad_le` are adapted from `valuation_law` and `good_whp` in
`Tao/Sec5/FirstPassage.lean` (derived from `TaoCollatz/Sec5/FirstPassage.lean` of gotrevor/tao-collatz (Apache-2.0),
commit 15efca2), with the logarithmic window `logUnif y (y^α)` (`y ≥ x`) replaced by the uniform window
`unifWin (x^α) ((x^α)^α)`, and the lower bound on the window mass replaced by a lower bound on the number of points
(`eventually_card_ge`).

Under the uniform distribution `Ñ` on the window `W = ℕ_p ∩ [x^α, (x^α)^α]`:

* `eventually_card_ge`: `Z = #W ≥ x` (for `x` large).
* `unif_valuation_law`: the `ℓ¹` distance between the law of the valuation sequence `a^{(n₀)}` and `G(μ)^{n₀}` is at most `C x^{-c}`
  (GGM Prop. 3.1 (`Family.prop33`) applied to the equidistribution mod `p^k` obtained from `unif_equidist`;
  `k = ⌈(μ + 1/4) n₀⌉`, `p^{2k+1} ≤ x ≤ Z`). The uniform-window version of `valuation_law` for the logarithmic window
  (`Tao/Sec5/FirstPassage.lean`).
* `unif_bad_le`: `P(a^{(n₀)}(Ñ) ∉ A^{(n₀)}) ≤ 2 (log x)^{-4}` (`geom_good_tail` and total variation).
  The uniform-window version of `good_whp` for the logarithmic window.
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace ConcAux

variable (F : Family)

open Family

/-- The number of points of the window `[x^α, (x^α)^α]` is at least `x` (for `x` large). -/
theorem eventually_card_ge {α : ℝ} (hα : 1 < α) : ∀ᶠ x : ℝ in Filter.atTop,
    x ≤ ((F.logWindow (x ^ α) ((x ^ α) ^ α)).card : ℝ) := by
  have ht := (tendsto_rpow_atTop (show 0 < α - 1 by linarith)).eventually_ge_atTop (4 * (F.p : ℝ))
  filter_upwards [ht, Filter.eventually_ge_atTop (F.p : ℝ), Filter.eventually_ge_atTop 1] with
    x hx hxp hx1
  have hx0 : 0 < x := by linarith
  have hp := F.p_real_pos
  have hp2 := F.p_real_two_le
  set y := x ^ α with hy
  have hxy : x ≤ y := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ α := Real.rpow_le_rpow_of_exponent_le hx1 hα.le
  have hy0 : 0 < y := by linarith
  have hya : 4 * (F.p : ℝ) ≤ y ^ (α - 1) := le_trans hx (Real.rpow_le_rpow hx0.le hxy (by linarith))
  have hsplit : y ^ α = y * y ^ (α - 1) := by
    rw [← Real.rpow_one_add' hy0.le (by linarith)]; ring_nf
  have hmul : y * (4 * (F.p : ℝ)) ≤ y * y ^ (α - 1) := mul_le_mul_of_nonneg_left hya hy0.le
  have hle : y ≤ y ^ α := by rw [hsplit]; nlinarith
  have h := card_window_ge F (le_trans hxp hxy) hle
  refine le_trans ?_ h
  rw [hsplit, le_sub_iff_add_le, le_div_iff₀ hp]
  nlinarith

/-- **The law of the valuations** (uniform window): `‖a^{(n₀)}(Ñ) - G(μ)^{n₀}‖_{ℓ¹} ≤ C x^{-c}`. `c`, `C` depend only on the family. -/
theorem unif_valuation_law :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ α : ℝ, 1 < α → ∀ᶠ x : ℝ in Filter.atTop,
      PMF.dTV ((unifWin F (x ^ α) ((x ^ α) ^ α)).map fun N => F.valVec N (F.nZero x))
        (PMF.iid (geomP F.p) (F.nZero x)) ≤ C * x ^ (-c) := by
  obtain ⟨c₁, C₁, hc₁, hC₁, h⟩ := F.prop33 (1 / 4) 10 (by norm_num) (by norm_num)
  have hp := F.log_p_pos
  have hq := F.log_q_pos
  have hpq := F.log_p_lt_log_q
  have hμ := F.mu_pos
  have hμ2 := F.mu_le_two
  refine ⟨c₁ * Real.log F.p / (5 * Real.log F.q), C₁ * Real.exp (c₁ * Real.log F.p),
    by positivity, by positivity, ?_⟩
  intro α hα
  filter_upwards [eventually_card_ge F hα, eventually_log_ge (30 * Real.log F.p),
    eventually_log_ge (10 * Real.log F.q), Filter.eventually_ge_atTop 1] with x hZ hL1 hL2 hx1
  have hx0 : 0 < x := by linarith
  set lo := x ^ α with hlo
  set hi := lo ^ α with hhi
  have hxlo : x ≤ lo := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ α := Real.rpow_le_rpow_of_exponent_le hx1 hα.le
  have hlo1 : 1 ≤ lo := le_trans hx1 hxlo
  have hle : lo ≤ hi := by
    calc lo = lo ^ (1 : ℝ) := (Real.rpow_one lo).symm
      _ ≤ lo ^ α := Real.rpow_le_rpow_of_exponent_le hlo1 hα.le
  set W := F.logWindow lo hi with hW
  have hZpos : (0 : ℝ) < W.card := by linarith
  have hWne : W.Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast hZpos
  set L := Real.log x with hLdef
  set n₀ := F.nZero x with hn₀
  have hL0 : 0 ≤ L := by linarith
  have hn0le : (n₀ : ℝ) ≤ L / (5 * Real.log F.q) := by
    rw [hn₀]; unfold nZero; exact Nat.floor_le (div_nonneg hL0 (by positivity))
  have hn0ge : L / (5 * Real.log F.q) - 1 ≤ n₀ := F.nZero_ge x
  have hn01 : 1 ≤ n₀ := by
    have : (1 : ℝ) ≤ n₀ := by
      have : 2 ≤ L / (5 * Real.log F.q) := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    exact_mod_cast this
  set k := ⌈(F.mu + 1 / 4) * n₀⌉₊ with hk
  have hkge : (F.mu + 1 / 4) * (n₀ : ℝ) ≤ k := Nat.le_ceil _
  have hk1 : 1 ≤ k := by
    have : (1 : ℝ) ≤ k := by
      have : (1 : ℝ) ≤ (F.mu + 1 / 4) * n₀ := by
        have : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn01
        nlinarith [F.one_lt_mu]
      linarith
    exact_mod_cast this
  have hkle : (k : ℝ) < (F.mu + 1 / 4) * n₀ + 1 := Nat.ceil_lt_add_one (by positivity)
  -- `p^{2k+1} ≤ x`
  have hpk : (F.p : ℝ) ^ (2 * k + 1) ≤ x := by
    rw [← Real.exp_log F.p_real_pos, ← Real.exp_nat_mul, ← Real.exp_log hx0]
    apply Real.exp_le_exp.mpr
    rw [← hLdef]
    push_cast
    have h2 : (F.mu + 1 / 4) * n₀ * Real.log F.p ≤ 9 / 20 * L := by
      have h3 : (F.mu + 1 / 4) * Real.log F.p ≤ 9 / 4 * Real.log F.q := by nlinarith
      calc (F.mu + 1 / 4) * n₀ * Real.log F.p = ((F.mu + 1 / 4) * Real.log F.p) * n₀ := by ring
        _ ≤ (9 / 4 * Real.log F.q) * (L / (5 * Real.log F.q)) :=
            mul_le_mul h3 hn0le (Nat.cast_nonneg _) (by positivity)
        _ = 9 / 20 * L := by field_simp; ring
    nlinarith
  have hpk0 : (0 : ℝ) < (F.p : ℝ) ^ k := pow_pos F.p_real_pos k
  have hpk1 : (1 : ℝ) ≤ (F.p : ℝ) ^ (k + 1) := one_le_pow₀ F.one_lt_p_real.le
  have hpklo : (F.p : ℝ) ^ k ≤ lo := by
    have : (F.p : ℝ) ^ k ≤ (F.p : ℝ) ^ (2 * k + 1) :=
      pow_le_pow_right₀ F.one_lt_p_real.le (by omega)
    linarith
  -- put the equidistribution of the window in the form of the hypothesis of Prop. 3.1
  have heq := unif_equidist F hWne hle hk1 hpklo
  have hW' : PMF.dTV ((unifWin F lo hi).map fun N => (N : ZMod (F.p ^ k))) (F.unifNpMod k)
      ≤ 10 * (F.p : ℝ) ^ (-(k : ℝ)) := by
    refine le_trans heq ?_
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, div_le_iff₀ hZpos]
    have hp2k : (F.p : ℝ) ^ (2 * k) ≤ W.card := by
      have : (F.p : ℝ) ^ (2 * k) ≤ (F.p : ℝ) ^ (2 * k + 1) :=
        pow_le_pow_right₀ F.one_lt_p_real.le (by omega)
      linarith
    calc 4 * (F.p : ℝ) ^ k ≤ 10 * (F.p : ℝ) ^ k := by linarith
      _ = 10 * ((F.p : ℝ) ^ k)⁻¹ * (F.p : ℝ) ^ (2 * k) := by
          rw [pow_mul', sq]; field_simp
      _ ≤ 10 * ((F.p : ℝ) ^ k)⁻¹ * W.card :=
          mul_le_mul_of_nonneg_left hp2k (by positivity)
  have hsupp : ∀ N ∈ (unifWin F lo hi).support, N % F.p ≠ 0 := by
    intro N hN
    rw [unifWin_eq F hWne, PMF.support_uniformOfFinset] at hN
    exact ((F.mem_logWindow_iff).mp hN).1
  have hkge' : ((F.p : ℝ) / ((F.p : ℝ) - 1) + 1 / 4) * (n₀ : ℝ) ≤ (k : ℝ) := hkge
  have hres := h n₀ k (unifWin F lo hi) hkge' hsupp hW'
  refine le_trans hres ?_
  have hexp := F.exp_neg_nZero_le (c := c₁ * Real.log F.p) (by positivity) hx0
  have hrw : (F.p : ℝ) ^ (-c₁ * (n₀ : ℝ)) = Real.exp (-(c₁ * Real.log F.p * n₀)) := by
    rw [Real.rpow_def_of_pos F.p_real_pos]; congr 1; ring
  rw [hrw]
  calc C₁ * Real.exp (-(c₁ * Real.log F.p * n₀))
      ≤ C₁ * (Real.exp (c₁ * Real.log F.p) * x ^ (-(c₁ * Real.log F.p / (5 * Real.log F.q)))) :=
        mul_le_mul_of_nonneg_left hexp hC₁.le
    _ = C₁ * Real.exp (c₁ * Real.log F.p) * x ^ (-(c₁ * Real.log F.p / (5 * Real.log F.q))) := by
        ring

/-- **Good tuples occur with high probability** (uniform window): `P(a^{(n₀)}(Ñ) ∉ A^{(n₀)}) ≤ 2 (log x)^{-4}`. -/
theorem unif_bad_le {α : ℝ} (hα : 1 < α) : ∀ᶠ x : ℝ in Filter.atTop,
    Family.expect (unifWin F (x ^ α) ((x ^ α) ^ α))
      (Set.indicator {N | ¬ F.goodVec x (F.valVec N (F.nZero x))} 1)
        ≤ 2 * Real.log x ^ (-4 : ℝ) := by
  obtain ⟨c, C, hc, hC, hval⟩ := unif_valuation_law F
  filter_upwards [hval α hα, F.geom_good_tail, eventually_mul_rpow_neg_le_log hc 4 C] with
    x hx hgt hxc
  have h1 := expect_indicator_le_add_dTV
    ((unifWin F (x ^ α) ((x ^ α) ^ α)).map fun N => F.valVec N (F.nZero x))
    (PMF.iid (geomP F.p) (F.nZero x)) {a | ¬ F.goodVec x a}
  rw [expect_map_indicator] at h1
  have h2 := hgt (F.nZero x) le_rfl
  calc _ ≤ _ := h1
    _ ≤ Real.log x ^ (-4 : ℝ) + C * x ^ (-c) := add_le_add h2 hx
    _ ≤ 2 * Real.log x ^ (-4 : ℝ) := by linarith

end ConcAux

end ND

end GGMCollatz
