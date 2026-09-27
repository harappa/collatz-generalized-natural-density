import GGMCollatz.Tao.Sec5.Tail

/-!
# Logarithmic windows, the law of the valuations, and non-escape (GGM §4 Step 1, tao-collatz's node C7)

Derived from `TaoCollatz/Sec5/FirstPassage.lean` (`windowMass_estimate`, `intTest_dTV_le`,
`valSum_lower_geom`, `first_passage_nonescape`) of gotrevor/tao-collatz (Apache-2.0), commit 15efca2;
generalized to the GGM family (p, q, r).

* `expect_logUnif`: the expectation under the logarithmic distribution on a window is a finite sum.
* `windowMass_approx`: `|Z - log(hi/lo)/μ| ≤ p/lo` (GGM `eq:logasymp`).
* `window_equidist`: the distribution of the window modulo `p^k` is close to the uniform distribution on
  the residues of `ℕ_p` (first half of GGM Step 1; GGM's `(p-1)p^{-k} + O(p^{-2k})` is a typo for
  `1/((p-1)p^{k-1})`, (G5) in the accompanying paper).
* `valuation_law`: the law of the valuation sequence `a^{(n₀)}` is close to `G(μ)^{n₀}` up to `x^{-c}`
  (from GGM's Proposition 3.1, GGM `ineq:tvaandgeom`).
* `passes_of_large_val`, `nonescape`: GGM `eq:passage time estimate` (first half of Proposition 3.5).
* `good_whp`: `P(a^{(n₀)} ∉ A^{(n₀)}) ≤ 2 (log x)^{-4}` (GGM `eq: error for not in A`).
* `edge_mass`: the logarithmic mass of the edge of the window is `O(log^{-1/5} x)` (the logarithmic side
  of (iv) in the accompanying paper).
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

variable (F : Family)

/-! ### The logarithmic distribution on a window -/

theorem mem_logWindow_iff {lo hi : ℝ} {N : ℕ} :
    N ∈ F.logWindow lo hi ↔ N % F.p ≠ 0 ∧ lo ≤ (N : ℝ) ∧ (N : ℝ) ≤ hi := by
  unfold logWindow
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have := Nat.le_ceil hi
    have h2 : (N : ℝ) ≤ (⌈hi⌉₊ : ℝ) := le_trans h.2.2 this
    have h3 : N ≤ ⌈hi⌉₊ := by exact_mod_cast h2
    omega

/-- If `1 ≤ lo` and `lo + 2 ≤ hi` then the window is nonempty (one of `⌈lo⌉` and `⌈lo⌉ + 1` is not
divisible by `p`). -/
theorem logWindow_nonempty_of {lo hi : ℝ} (hlo : 1 ≤ lo) (h : lo + 2 ≤ hi) :
    (F.logWindow lo hi).Nonempty := by
  set N₀ := ⌈lo⌉₊ with hN₀
  have h1 : lo ≤ (N₀ : ℝ) := Nat.le_ceil lo
  have h2 : (N₀ : ℝ) < lo + 1 := Nat.ceil_lt_add_one (by linarith)
  have hp := F.two_le_p
  by_cases hd : N₀ % F.p = 0
  · refine ⟨N₀ + 1, (F.mem_logWindow_iff).mpr ⟨?_, ?_, ?_⟩⟩
    · rw [Nat.add_mod, hd, zero_add, Nat.mod_mod_of_dvd, Nat.mod_eq_of_lt (by omega)]
      · omega
      · exact dvd_refl _
    · push_cast; linarith
    · push_cast; linarith
  · exact ⟨N₀, (F.mem_logWindow_iff).mpr ⟨hd, h1, by linarith⟩⟩

/-- If the window is nonempty, the support of the logarithmic distribution is contained in the window. -/
theorem mem_logWindow_of_mem_support {lo hi : ℝ} (h : (F.logWindow lo hi).Nonempty) {N : ℕ}
    (hN : N ∈ (F.logUnif lo hi).support) : N ∈ F.logWindow lo hi := by
  classical
  by_contra hn
  rw [PMF.mem_support_iff] at hN
  apply hN
  unfold logUnif
  simp only [dif_pos h, PMF.ofFinset_apply, if_neg hn]

/-- If `x` is large, the window `[y, y^α]` with `y ≥ x` is nonempty. -/
theorem eventually_window_nonempty {α : ℝ} (hα : 1 < α) : ∀ᶠ x : ℝ in Filter.atTop, ∀ y : ℝ, x ≤ y →
    (F.logWindow y (y ^ α)).Nonempty := by
  have ht := (tendsto_rpow_atTop (show 0 < α - 1 by linarith)).eventually_ge_atTop 2
  filter_upwards [ht, Filter.eventually_ge_atTop 2] with x hx hx2
  intro y hy
  have hy2 : 2 ≤ y := le_trans hx2 hy
  have hy0 : 0 < y := by linarith
  have hya : 2 ≤ y ^ (α - 1) := le_trans hx (Real.rpow_le_rpow (by linarith) hy (by linarith))
  have hsplit : y ^ α = y * y ^ (α - 1) := by
    rw [← Real.rpow_one_add' hy0.le (by linarith)]; ring_nf
  apply F.logWindow_nonempty_of (by linarith)
  rw [hsplit]; nlinarith

theorem ne_zero_of_mem_logWindow {lo hi : ℝ} {N : ℕ} (hN : N ∈ F.logWindow lo hi) : N ≠ 0 := by
  intro h0
  exact ((F.mem_logWindow_iff).mp hN).1 (by simp [h0])

/-- The mass of the logarithmic distribution on a nonempty window (ℝ≥0∞). -/
theorem logUnif_apply_of_nonempty {lo hi : ℝ} (h : (F.logWindow lo hi).Nonempty) (N : ℕ) :
    F.logUnif lo hi N
      = if N ∈ F.logWindow lo hi then
          (N : ℝ≥0∞)⁻¹ / (∑ M ∈ F.logWindow lo hi, (M : ℝ≥0∞)⁻¹) else 0 := by
  classical
  unfold logUnif
  simp only [dif_pos h, PMF.ofFinset_apply]

theorem toReal_sum_inv_window {lo hi : ℝ} (s : Finset ℕ) (hs : s ⊆ F.logWindow lo hi) :
    (∑ M ∈ s, (M : ℝ≥0∞)⁻¹).toReal = ∑ M ∈ s, (M : ℝ)⁻¹ := by
  rw [ENNReal.toReal_sum fun M hM => by
    rw [ne_eq, ENNReal.inv_eq_top, Nat.cast_eq_zero]
    exact F.ne_zero_of_mem_logWindow (hs hM)]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- The mass of the logarithmic distribution on a nonempty window (ℝ): `1/(N Z)`. -/
theorem logUnif_apply_toReal {lo hi : ℝ} (h : (F.logWindow lo hi).Nonempty) (N : ℕ) :
    (F.logUnif lo hi N).toReal
      = if N ∈ F.logWindow lo hi then (N : ℝ)⁻¹ / F.windowMass lo hi else 0 := by
  rw [F.logUnif_apply_of_nonempty h]
  by_cases hN : N ∈ F.logWindow lo hi
  · rw [if_pos hN, if_pos hN, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        windowMass, F.toReal_sum_inv_window _ (subset_refl _)]
  · rw [if_neg hN, if_neg hN]; simp

theorem windowMass_pos {lo hi : ℝ} (h : (F.logWindow lo hi).Nonempty) : 0 < F.windowMass lo hi := by
  unfold windowMass
  obtain ⟨N₀, hN₀⟩ := h
  have hpos : ∀ N ∈ F.logWindow lo hi, 0 < (N : ℝ)⁻¹ := fun N hN =>
    inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (F.ne_zero_of_mem_logWindow hN)))
  exact Finset.sum_pos hpos ⟨N₀, hN₀⟩

/-- If the window is nonempty, the expectation under the logarithmic distribution is the finite sum
`Σ_{N ∈ W} f(N)/N / Z`. -/
theorem expect_logUnif {lo hi : ℝ} (h : (F.logWindow lo hi).Nonempty) (f : ℕ → ℝ) :
    expect (F.logUnif lo hi) f
      = (∑ N ∈ F.logWindow lo hi, f N * (N : ℝ)⁻¹) / F.windowMass lo hi := by
  unfold expect
  rw [tsum_eq_sum (s := F.logWindow lo hi) (fun N hN => by
    rw [F.logUnif_apply_toReal h, if_neg hN, zero_mul])]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun N hN => ?_
  rw [F.logUnif_apply_toReal h, if_pos hN]
  ring

/-- Asymptotic form of the window mass (GGM `eq:logasymp`): if `1 ≤ lo ≤ hi` then
`|Z - log(hi/lo)/μ| ≤ p/lo`. -/
theorem windowMass_approx {lo hi : ℝ} (hlo : 1 ≤ lo) (hle : lo ≤ hi) :
    |F.windowMass lo hi - Real.log (hi / lo) / F.mu| ≤ F.p / lo := by
  classical
  have hp2 := F.p_real_two_le
  have hpos : 0 < F.p := F.p_pos
  have hlo0 : 0 < lo := by linarith
  have hhi0 : 0 < hi := by linarith
  set ℓ := Real.log (hi / lo) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by rw [le_div_iff₀ hlo0]; linarith)
  have hμinv : ℓ / F.mu = ℓ - ℓ / F.p := by
    unfold mu; field_simp
  rw [hμinv]
  set W := F.logWindow lo hi with hW
  -- upper bound: residue class by residue class modulo `p`
  have hup : F.windowMass lo hi ≤ (F.p - 1) * (lo⁻¹ + ℓ / F.p) := by
    unfold windowMass
    rw [← Finset.sum_fiberwise_of_maps_to (s := W) (t := Finset.Ioo 0 F.p) (g := fun N => N % F.p)
      (fun N hN => by
        obtain ⟨hNp, _, _⟩ := (F.mem_logWindow_iff).mp hN
        rw [Finset.mem_Ioo]; exact ⟨Nat.pos_of_ne_zero hNp, Nat.mod_lt _ hpos⟩)]
    calc ∑ j ∈ Finset.Ioo 0 F.p, ∑ N ∈ W with N % F.p = j, (N : ℝ)⁻¹
        ≤ ∑ _j ∈ Finset.Ioo 0 F.p, (lo⁻¹ + ℓ / F.p) := by
          refine Finset.sum_le_sum fun j _ => ?_
          apply sum_inv_le_of_modEq hpos hlo0 _ hi hle
          · intro N hN
            obtain ⟨_, h1, h2⟩ := (F.mem_logWindow_iff).mp (Finset.mem_filter.mp hN).1
            exact ⟨h1, h2⟩
          · intro N hN N' hN'
            rw [(Finset.mem_filter.mp hN).2, (Finset.mem_filter.mp hN').2]
      _ = (F.p - 1) * (lo⁻¹ + ℓ / F.p) := by
          rw [Finset.sum_const, Nat.card_Ioo, nsmul_eq_mul]
          congr 1
          rw [Nat.sub_zero, Nat.cast_sub (by omega)]; simp
  -- lower bound: subtract the multiples of `p` from the sum over consecutive integers
  set A := ⌈lo⌉₊ with hA
  set B := ⌊hi⌋₊ with hB
  have hA1 : 1 ≤ A := Nat.one_le_iff_ne_zero.mpr (by
    intro h0; have := Nat.le_ceil lo; rw [← hA, h0] at this; simp at this; linarith)
  have hWeq : W = (Finset.Icc A B).filter (fun N => N % F.p ≠ 0) := by
    ext N
    rw [F.mem_logWindow_iff, Finset.mem_filter, Finset.mem_Icc, hA, hB, Nat.ceil_le,
      Nat.le_floor_iff hhi0.le]
    tauto
  have hfull := log_le_sum_Icc_inv hA1 B
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc A B) (fun N => N % F.p ≠ 0)
    (fun N => (N : ℝ)⁻¹)
  have hmult : ∑ N ∈ (Finset.Icc A B).filter (fun N => ¬ (N % F.p ≠ 0)), (N : ℝ)⁻¹
      ≤ lo⁻¹ + ℓ / F.p := by
    apply sum_inv_le_of_modEq hpos hlo0 _ hi hle
    · intro N hN
      have hN' := (Finset.mem_filter.mp hN).1
      rw [Finset.mem_Icc, hA, hB, Nat.ceil_le, Nat.le_floor_iff hhi0.le] at hN'
      exact hN'
    · intro N hN N' hN'
      have h1 := (Finset.mem_filter.mp hN).2
      have h2 := (Finset.mem_filter.mp hN').2
      push_neg at h1 h2
      rw [h1, h2]
  have hlogB : Real.log (hi / lo) - lo⁻¹ ≤ Real.log (((B : ℝ) + 1) / A) := by
    have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
    have hAle : (A : ℝ) ≤ lo + 1 := (Nat.ceil_lt_add_one hlo0.le).le
    have hBge : hi ≤ (B : ℝ) + 1 := (Nat.lt_floor_add_one hi).le
    have h1 : Real.log (hi / (lo + 1)) ≤ Real.log (((B : ℝ) + 1) / A) :=
      Real.log_le_log (by positivity) (div_le_div₀ (by positivity) hBge hApos hAle)
    have h2 : Real.log (hi / (lo + 1)) = Real.log (hi / lo) - Real.log ((lo + 1) / lo) := by
      rw [← Real.log_div (by positivity) (by positivity)]; congr 1; field_simp
    have h3 : Real.log ((lo + 1) / lo) ≤ lo⁻¹ := by
      have := Real.log_le_sub_one_of_pos (show 0 < (lo + 1) / lo by positivity)
      have h4 : (lo + 1) / lo - 1 = lo⁻¹ := by field_simp; ring
      linarith
    linarith
  have hlow : ℓ - ℓ / F.p - 2 * lo⁻¹ ≤ F.windowMass lo hi := by
    unfold windowMass
    rw [← hW, hWeq]
    linarith
  have hlo_inv : lo⁻¹ = 1 / lo := by rw [one_div]
  rw [abs_le]
  constructor
  · have : 2 * lo⁻¹ ≤ F.p / lo := by
      rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right hp2 (by positivity)
    linarith
  · have : (F.p - 1) * (lo⁻¹ + ℓ / F.p) = (F.p - 1) / lo + (ℓ - ℓ / F.p) := by
      field_simp
    have h2 : ((F.p : ℝ) - 1) / lo ≤ F.p / lo := div_le_div_of_nonneg_right (by linarith) hlo0.le
    linarith

/-- Lower bound on the mass of large windows: if `y ≥ x` and `x` is large then
`Z_y ≥ (α-1) log x/(2μ)`. -/
theorem eventually_windowMass_ge {α : ℝ} (hα : 1 < α) : ∀ᶠ x : ℝ in Filter.atTop, ∀ y : ℝ, x ≤ y →
    (α - 1) * Real.log x / (2 * F.mu) ≤ F.windowMass y (y ^ α) := by
  have hμ := F.mu_pos
  have hα1 : 0 < α - 1 := by linarith
  filter_upwards [eventually_log_ge (2 * F.mu * F.p / (α - 1)), Filter.eventually_ge_atTop 1,
    eventually_log_ge 0] with x hL hx1 hL0
  intro y hy
  have hy1 : 1 ≤ y := le_trans hx1 hy
  have hy0 : 0 < y := by linarith
  have hyα : y ≤ y ^ α := by
    calc y = y ^ (1 : ℝ) := (Real.rpow_one y).symm
      _ ≤ y ^ α := Real.rpow_le_rpow_of_exponent_le hy1 hα.le
  have h := F.windowMass_approx hy1 hyα
  have hlog : Real.log (y ^ α / y) = (α - 1) * Real.log y := by
    rw [Real.log_div (by positivity) hy0.ne', Real.log_rpow hy0]; ring
  have hly : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hy
  have hpy : (F.p : ℝ) / y ≤ F.p := div_le_self (by positivity) hy1
  rw [hlog] at h
  have h1 := (abs_le.mp h).1
  have h2 : (α - 1) * Real.log x / F.mu ≤ (α - 1) * Real.log y / F.mu :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hly hα1.le) hμ.le
  have h3 : F.p ≤ (α - 1) * Real.log x / (2 * F.mu) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hL hα1.le
    rw [show (α - 1) * (2 * F.mu * F.p / (α - 1)) = F.p * (2 * F.mu) by field_simp] at this
    linarith
  have h4 : (α - 1) * Real.log x / F.mu = 2 * ((α - 1) * Real.log x / (2 * F.mu)) := by
    field_simp
  linarith

/-- `n₀ ≥ log x/(5 log q) - 1`. -/
theorem nZero_ge (x : ℝ) : Real.log x / (5 * Real.log F.q) - 1 ≤ F.nZero x := by
  unfold nZero
  exact le_of_lt (Nat.sub_one_lt_floor _)

/-- `e^{-c n₀} ≤ e^c x^{-c/(5 log q)}` (`x > 0`, `c ≥ 0`). -/
theorem exp_neg_nZero_le {c x : ℝ} (hc : 0 ≤ c) (hx : 0 < x) :
    Real.exp (-(c * F.nZero x)) ≤ Real.exp c * x ^ (-(c / (5 * Real.log F.q))) := by
  have h1 := F.nZero_ge x
  rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hq := F.log_q_pos
  have : c * (Real.log x / (5 * Real.log F.q) - 1) ≤ c * F.nZero x :=
    mul_le_mul_of_nonneg_left h1 hc
  have h2 : c * (Real.log x / (5 * Real.log F.q)) = Real.log x * (c / (5 * Real.log F.q)) := by
    field_simp
  nlinarith

/-- `X.map fun N => (N : ZMod m)` (the form in the statement of Proposition 3.1, a monadic lift) is the
ordinary pushforward. -/
theorem map_coe_eq (X : PMF ℕ) (m : ℕ) :
    (X.map fun N => (N : ZMod m)) = PMF.map (fun N : ℕ => (N : ZMod m)) X := by
  have hid : (fun N : ZMod m => N) = id := rfl
  rw [hid, PMF.map_id]
  exact PMF.bind_pure_comp _ _

/-- The mass of the pushforward of the logarithmic distribution on a window to residues modulo `p^k`
(tao-collatz's `map_res_apply_toReal`). -/
theorem map_cast_apply_toReal {lo hi : ℝ} (h : (F.logWindow lo hi).Nonempty) {k : ℕ}
    (z : ZMod (F.p ^ k)) :
    ((PMF.map (fun N : ℕ => (N : ZMod (F.p ^ k))) (F.logUnif lo hi)) z).toReal
      = (∑ N ∈ (F.logWindow lo hi).filter (fun N : ℕ => (N : ZMod (F.p ^ k)) = z), (N : ℝ)⁻¹)
          / F.windowMass lo hi := by
  classical
  have hmap : (PMF.map (fun N : ℕ => (N : ZMod (F.p ^ k))) (F.logUnif lo hi)) z
      = (∑ N ∈ (F.logWindow lo hi).filter (fun N : ℕ => (N : ZMod (F.p ^ k)) = z), (N : ℝ≥0∞)⁻¹)
          / (∑ M ∈ F.logWindow lo hi, (M : ℝ≥0∞)⁻¹) := by
    rw [PMF.map_apply]
    rw [tsum_eq_sum (s := F.logWindow lo hi) (fun N hN => by
      rw [F.logUnif_apply_of_nonempty h, if_neg hN]; split_ifs <;> rfl)]
    rw [Finset.sum_filter, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun N hN => ?_
    rw [F.logUnif_apply_of_nonempty h, if_pos hN]
    by_cases hc : (N : ZMod (F.p ^ k)) = z
    · rw [if_pos hc.symm, if_pos hc, div_eq_mul_inv]
    · rw [if_neg (fun hh => hc hh.symm), if_neg hc, zero_mul]
  rw [hmap, ENNReal.toReal_div, F.toReal_sum_inv_window _ (Finset.filter_subset _ _),
    F.toReal_sum_inv_window _ (subset_refl _)]
  rfl

/-- The number of classes modulo `p^k` not divisible by `p` is at most `p^k/μ = (p-1)p^{k-1}`. -/
theorem card_np_residues_le {k : ℕ} (hk : 1 ≤ k) :
    ((Finset.univ.filter fun z : ZMod (F.p ^ k) => z.val % F.p ≠ 0).card : ℝ)
      ≤ (F.p : ℝ) ^ k / F.mu := by
  classical
  have hp := F.p_pos
  set T := Finset.univ.filter fun z : ZMod (F.p ^ k) => z.val % F.p ≠ 0 with hT
  set T' := Finset.univ.filter fun z : ZMod (F.p ^ k) => ¬ (z.val % F.p ≠ 0) with hT'
  have hsum : T.card + T'.card = F.p ^ k := by
    rw [hT, hT', Finset.card_filter_add_card_filter_not, Finset.card_univ, ZMod.card]
  -- there are at least `p^{k-1}` classes with `p ∣ val` (`p j`, `j < p^{k-1}`)
  have hT'ge : F.p ^ (k - 1) ≤ T'.card := by
    have hinj : Set.InjOn (fun j : ℕ => ((F.p * j : ℕ) : ZMod (F.p ^ k)))
        (Finset.range (F.p ^ (k - 1)) : Set ℕ) := by
      intro j hj j' hj' hjj
      simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
      have hpk : F.p ^ k = F.p * F.p ^ (k - 1) := by
        rw [← pow_succ']; congr 1; omega
      have h1 : F.p * j < F.p ^ k := by rw [hpk]; exact Nat.mul_lt_mul_of_pos_left hj hp
      have h2 : F.p * j' < F.p ^ k := by rw [hpk]; exact Nat.mul_lt_mul_of_pos_left hj' hp
      have := congrArg ZMod.val hjj
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
      exact Nat.eq_of_mul_eq_mul_left hp this
    have hsub : (Finset.range (F.p ^ (k - 1))).image (fun j : ℕ => ((F.p * j : ℕ) : ZMod (F.p ^ k)))
        ⊆ T' := by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨j, hj, rfl⟩ := hz
      rw [hT', Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      push_neg
      rw [ZMod.val_natCast, Nat.mod_mod_of_dvd _ (dvd_pow_self F.p (by omega)), Nat.mul_mod_right]
    calc F.p ^ (k - 1) = ((Finset.range (F.p ^ (k - 1))).image
          (fun j : ℕ => ((F.p * j : ℕ) : ZMod (F.p ^ k)))).card := by
          rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      _ ≤ T'.card := Finset.card_le_card hsub
  have hTle : T.card ≤ F.p ^ k - F.p ^ (k - 1) := by omega
  have hpk : F.p ^ (k - 1) ≤ F.p ^ k := Nat.pow_le_pow_right hp (by omega)
  have hcast : (T.card : ℝ) ≤ (F.p : ℝ) ^ k - (F.p : ℝ) ^ (k - 1) := by
    have : ((F.p ^ k - F.p ^ (k - 1) : ℕ) : ℝ) = (F.p : ℝ) ^ k - (F.p : ℝ) ^ (k - 1) := by
      rw [Nat.cast_sub hpk]; push_cast; ring
    rw [← this]; exact_mod_cast hTle
  have hid : (F.p : ℝ) ^ k - (F.p : ℝ) ^ (k - 1) = (F.p : ℝ) ^ k / F.mu := by
    have hpk' : (F.p : ℝ) ^ k = F.p * (F.p : ℝ) ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    unfold mu
    have hp1 : (F.p : ℝ) - 1 ≠ 0 := by have := F.one_lt_p_real; linarith
    rw [hpk']; field_simp
  linarith

/-- Equidistribution of the window modulo `p^k`: the `ℓ¹` distance is at most `10 p^{k+1} / (lo · Z)`
(`k ≥ 1`). -/
theorem window_equidist {lo hi : ℝ} (hlo : 1 ≤ lo) (hle : lo ≤ hi)
    (h : (F.logWindow lo hi).Nonempty) {k : ℕ} (hk : 1 ≤ k) :
    PMF.dTV ((F.logUnif lo hi).map fun N => (N : ZMod (F.p ^ k))) (F.unifNpMod k)
      ≤ 10 * (F.p : ℝ) ^ (k + 1) / (lo * F.windowMass lo hi) := by
  classical
  have hp := F.p_pos
  have hμ := F.mu_pos
  have hμ2 := F.mu_le_two
  have hlo0 : 0 < lo := by linarith
  rw [map_coe_eq]
  set ν := PMF.map (fun N : ℕ => (N : ZMod (F.p ^ k))) (F.logUnif lo hi) with hν
  set u := F.unifNpMod k with hu
  set Z := F.windowMass lo hi with hZ
  have hZpos : 0 < Z := F.windowMass_pos h
  set T := Finset.univ.filter fun z : ZMod (F.p ^ k) => z.val % F.p ≠ 0 with hT
  have hpk1 : 1 < F.p ^ k := Nat.one_lt_pow (by omega) (by have := F.two_le_p; omega)
  have hTne : T.Nonempty := ⟨1, by
    rw [hT, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [ZMod.val_one'' (by omega)]
    rw [Nat.mod_eq_of_lt F.one_lt_p]; norm_num⟩
  have huval : ∀ z, (u z).toReal = if z ∈ T then ((T.card : ℝ))⁻¹ else 0 := by
    intro z
    rw [hu]; unfold unifNpMod
    rw [dif_pos hTne, PMF.uniformOfFinset_apply]
    by_cases hz : z ∈ T
    · rw [if_pos hz, if_pos (by simpa [hT] using hz), ENNReal.toReal_inv, ENNReal.toReal_natCast]
    · rw [if_neg hz, if_neg (by simpa [hT] using hz)]
      simp
  have hTcard := F.card_np_residues_le hk
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast hTne.card_pos
  set ℓ := Real.log (hi / lo) with hℓ
  have hZlow : ℓ / F.mu - F.p / lo ≤ Z := by
    have := (abs_le.mp (F.windowMass_approx hlo hle)).1; linarith
  -- bound for each class
  have hclass : ∀ z : ZMod (F.p ^ k), (ν z).toReal - (u z).toReal
      ≤ if z ∈ T then 5 * F.p / (lo * Z) else 0 := by
    intro z
    rw [hν, F.map_cast_apply_toReal h, huval]
    by_cases hz : z ∈ T
    · rw [if_pos hz, if_pos hz]
      -- harmonic sum over a class
      have hSz := sum_inv_le_of_modEq (pow_pos hp k) hlo0
        ((F.logWindow lo hi).filter (fun N : ℕ => (N : ZMod (F.p ^ k)) = z)) hi hle
        (fun N hN => by
          obtain ⟨_, h1, h2⟩ := (F.mem_logWindow_iff).mp (Finset.mem_filter.mp hN).1
          exact ⟨h1, h2⟩)
        (fun N hN N' hN' => (ZMod.natCast_eq_natCast_iff' N N' (F.p ^ k)).mp
          ((Finset.mem_filter.mp hN).2.trans (Finset.mem_filter.mp hN').2.symm))
      have hpkR : (0 : ℝ) < (F.p : ℝ) ^ k := by positivity
      push_cast at hSz
      have hinv : F.mu / (F.p : ℝ) ^ k ≤ (T.card : ℝ)⁻¹ := by
        rw [div_le_iff₀ hpkR, inv_mul_eq_div, le_div_iff₀ hTpos]
        have := mul_le_mul_of_nonneg_left hTcard hμ.le
        rwa [mul_div_cancel₀ _ hμ.ne'] at this
      have hmain : (∑ N ∈ (F.logWindow lo hi).filter (fun N : ℕ => (N : ZMod (F.p ^ k)) = z),
          (N : ℝ)⁻¹) / Z - F.mu / (F.p : ℝ) ^ k ≤ 5 * F.p / (lo * Z) := by
        rw [div_sub' hZpos.ne', div_le_div_iff₀ (by positivity) (by positivity)]
        -- `S ≤ 1/lo + ℓ/p^k`, `μ Z ≥ ℓ - μ p/lo`
        have e1 : F.mu * (ℓ / F.mu - F.p / lo) = ℓ - F.mu * F.p / lo := by field_simp
        have h1 := mul_le_mul_of_nonneg_left hZlow hμ.le
        rw [e1] at h1
        have h2 : lo⁻¹ + ℓ / (F.p : ℝ) ^ k - F.mu * Z / (F.p : ℝ) ^ k
            ≤ lo⁻¹ + F.mu * F.p / lo / (F.p : ℝ) ^ k := by
          have : ℓ / (F.p : ℝ) ^ k - F.mu * Z / (F.p : ℝ) ^ k ≤ F.mu * F.p / lo / (F.p : ℝ) ^ k := by
            rw [← sub_div]; apply div_le_div_of_nonneg_right _ hpkR.le; linarith
          linarith
        have h3 : F.mu * F.p / lo / (F.p : ℝ) ^ k ≤ 2 * F.p / lo := by
          rw [div_le_iff₀ hpkR]
          have hpk1' : (1 : ℝ) ≤ (F.p : ℝ) ^ k := one_le_pow₀ F.one_lt_p_real.le
          have : F.mu * F.p / lo ≤ 2 * F.p / lo :=
            div_le_div_of_nonneg_right (by nlinarith [F.p_real_pos]) hlo0.le
          nlinarith [div_nonneg (by positivity : (0:ℝ) ≤ 2 * F.p) hlo0.le]
        have h4 : lo⁻¹ ≤ F.p / lo := by
          rw [inv_eq_one_div]; exact div_le_div_of_nonneg_right (by linarith [F.p_real_two_le]) hlo0.le
        have hS2 : (∑ N ∈ (F.logWindow lo hi).filter (fun N : ℕ => (N : ZMod (F.p ^ k)) = z),
            (N : ℝ)⁻¹) - F.mu * Z / (F.p : ℝ) ^ k ≤ 3 * F.p / lo := by
          have : 3 * F.p / lo = F.p / lo + 2 * F.p / lo := by ring
          linarith
        have e2 : (∑ N ∈ (F.logWindow lo hi).filter (fun N : ℕ => (N : ZMod (F.p ^ k)) = z),
            (N : ℝ)⁻¹) - Z * (F.mu / (F.p : ℝ) ^ k)
            = (∑ N ∈ (F.logWindow lo hi).filter (fun N : ℕ => (N : ZMod (F.p ^ k)) = z),
            (N : ℝ)⁻¹) - F.mu * Z / (F.p : ℝ) ^ k := by ring
        rw [e2]
        have h5 : 3 * F.p / lo * (lo * Z) ≤ 5 * F.p * Z := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hlo0]
          have hpos : 0 < (F.p : ℝ) * Z * lo := by have := F.p_real_pos; positivity
          nlinarith [hpos]
        calc _ ≤ 3 * F.p / lo * (lo * Z) :=
              mul_le_mul_of_nonneg_right hS2 (by positivity)
          _ ≤ 5 * F.p * Z := h5
      linarith [hinv, hmain]
    · rw [if_neg hz, if_neg hz]
      have hempty : (F.logWindow lo hi).filter (fun N : ℕ => (N : ZMod (F.p ^ k)) = z) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro N hN hNz
        apply hz
        rw [hT, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hNz, ZMod.val_natCast, Nat.mod_mod_of_dvd _ (dvd_pow_self F.p (by omega))]
        exact ((F.mem_logWindow_iff).mp hN).1
      rw [hempty, Finset.sum_empty]; simp
  -- `ℓ¹ = 2 Σ (ν - u)⁺`
  have hsumν : ∑ z, (ν z).toReal = 1 := by
    have := tsum_toReal_eq_one ν; rwa [tsum_fintype] at this
  have hsumu : ∑ z, (u z).toReal = 1 := by
    have := tsum_toReal_eq_one u; rwa [tsum_fintype] at this
  unfold PMF.dTV
  rw [tsum_fintype]
  have hpt : ∀ z : ZMod (F.p ^ k), |(ν z).toReal - (u z).toReal|
      ≤ 2 * (if z ∈ T then 5 * F.p / (lo * Z) else 0) - ((ν z).toReal - (u z).toReal) := by
    intro z
    have h1 := hclass z
    rcases le_or_gt 0 ((ν z).toReal - (u z).toReal) with h0 | h0
    · rw [abs_of_nonneg h0]; linarith
    · rw [abs_of_neg h0]
      have : 0 ≤ (if z ∈ T then 5 * F.p / (lo * Z) else 0 : ℝ) := by
        split_ifs <;> positivity
      linarith
  calc ∑ z, |(ν z).toReal - (u z).toReal|
      ≤ ∑ z, (2 * (if z ∈ T then 5 * F.p / (lo * Z) else 0) - ((ν z).toReal - (u z).toReal)) :=
        Finset.sum_le_sum fun z _ => hpt z
    _ = 2 * (T.card * (5 * F.p / (lo * Z))) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsumν, hsumu, ← Finset.mul_sum,
          Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ 2 * ((F.p : ℝ) ^ k * (5 * F.p / (lo * Z))) := by
        gcongr
        exact le_trans hTcard (div_le_self (by positivity) F.one_lt_mu.le)
    _ = 10 * (F.p : ℝ) ^ (k + 1) / (lo * Z) := by ring

/-! ### The law of the valuations (from GGM's Proposition 3.1) -/

/-- **The law of the valuations** (GGM `ineq:tvaandgeom`): under the logarithmic distribution on the
window `[y, y^α]` (`y ≥ x`), the `ℓ¹` distance between the law of the valuation sequence `a^{(n₀)}` and
`G(μ)^{n₀}` is at most `C x^{-c}`. `c`, `C` depend only on the family. -/
theorem valuation_law (h33 : F.prop33_statement) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ α : ℝ, 1 < α → ∀ᶠ x : ℝ in Filter.atTop, ∀ y : ℝ, x ≤ y →
      PMF.dTV ((F.logUnif y (y ^ α)).map fun N => F.valVec N (F.nZero x))
        (PMF.iid (geomP F.p) (F.nZero x)) ≤ C * x ^ (-c) := by
  obtain ⟨c₁, C₁, hc₁, hC₁, h⟩ := h33 (1 / 4) 10 (by norm_num) (by norm_num)
  have hp := F.log_p_pos
  have hq := F.log_q_pos
  have hpq := F.log_p_lt_log_q
  have hμ := F.mu_pos
  have hμ2 := F.mu_le_two
  refine ⟨c₁ * Real.log F.p / (5 * Real.log F.q), C₁ * Real.exp (c₁ * Real.log F.p),
    by positivity, by positivity, ?_⟩
  intro α hα
  have hα1 : 0 < α - 1 := by linarith
  filter_upwards [F.eventually_windowMass_ge hα, F.eventually_window_nonempty hα,
    eventually_log_ge (30 * Real.log F.p), eventually_log_ge (10 * Real.log F.q),
    eventually_log_ge (2 * F.mu / (α - 1)), Filter.eventually_ge_atTop 1] with
    x hZ hne hL1 hL2 hL3 hx1
  intro y hy
  have hx0 : 0 < x := by linarith
  have hy1 : 1 ≤ y := le_trans hx1 hy
  have hy0 : 0 < y := by linarith
  have hyα : y ≤ y ^ α := by
    calc y = y ^ (1 : ℝ) := (Real.rpow_one y).symm
      _ ≤ y ^ α := Real.rpow_le_rpow_of_exponent_le hy1 hα.le
  set L := Real.log x with hLdef
  set n₀ := F.nZero x with hn₀
  have hW := hne y hy
  have hZ1 : 1 ≤ F.windowMass y (y ^ α) := by
    have h1 := hZ y hy
    have h2 : 1 ≤ (α - 1) * L / (2 * F.mu) := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hL3 hα1.le
      rw [show (α - 1) * (2 * F.mu / (α - 1)) = 2 * F.mu by field_simp] at this
      linarith
    linarith
  have hn0ge : L / (5 * Real.log F.q) - 1 ≤ n₀ := F.nZero_ge x
  have hL0 : 0 ≤ L := by linarith
  have hn0le : (n₀ : ℝ) ≤ L / (5 * Real.log F.q) := by
    rw [hn₀]; unfold nZero; exact Nat.floor_le (div_nonneg hL0 (by positivity))
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
  -- put the equidistribution of the window into the form of the hypothesis of Proposition 3.1
  have heq := F.window_equidist hy1 hyα hW hk1
  have hpk : (F.p : ℝ) ^ (2 * k + 1) ≤ y * F.windowMass y (y ^ α) := by
    have h1 : (F.p : ℝ) ^ (2 * k + 1) ≤ x := by
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
    calc (F.p : ℝ) ^ (2 * k + 1) ≤ x := h1
      _ ≤ y := hy
      _ ≤ y * F.windowMass y (y ^ α) := le_mul_of_one_le_right hy0.le hZ1
  have hW' : PMF.dTV ((F.logUnif y (y ^ α)).map fun N => (N : ZMod (F.p ^ k))) (F.unifNpMod k)
      ≤ 10 * (F.p : ℝ) ^ (-(k : ℝ)) := by
    refine le_trans heq ?_
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    have hZpos : 0 < y * F.windowMass y (y ^ α) := mul_pos hy0 (by linarith)
    have hpkpos : (0 : ℝ) < (F.p : ℝ) ^ k := pow_pos F.p_real_pos k
    rw [div_le_iff₀ hZpos]
    calc 10 * (F.p : ℝ) ^ (k + 1) = 10 * ((F.p : ℝ) ^ k)⁻¹ * (F.p : ℝ) ^ (2 * k + 1) := by
          field_simp; ring
      _ ≤ 10 * ((F.p : ℝ) ^ k)⁻¹ * (y * F.windowMass y (y ^ α)) :=
          mul_le_mul_of_nonneg_left hpk (by positivity)
  have hsupp : ∀ N ∈ (F.logUnif y (y ^ α)).support, N % F.p ≠ 0 := fun N hN =>
    ((F.mem_logWindow_iff).mp (F.mem_logWindow_of_mem_support hW hN)).1
  have hkge' : ((F.p : ℝ) / ((F.p : ℝ) - 1) + 1 / 4) * (n₀ : ℝ) ≤ (k : ℝ) := hkge
  have hres := h n₀ k (F.logUnif y (y ^ α)) hkge' hsupp hW'
  refine le_trans hres ?_
  have hexp := F.exp_neg_nZero_le (c := c₁ * Real.log F.p) (by positivity) hx0
  have hrw : (F.p : ℝ) ^ (-c₁ * (n₀ : ℝ)) = Real.exp (-(c₁ * Real.log F.p * n₀)) := by
    rw [Real.rpow_def_of_pos F.p_real_pos]; congr 1; ring
  rw [hrw]
  have : c₁ * Real.log F.p / (5 * Real.log F.q) = c₁ * Real.log F.p / (5 * Real.log F.q) := rfl
  calc C₁ * Real.exp (-(c₁ * Real.log F.p * n₀))
      ≤ C₁ * (Real.exp (c₁ * Real.log F.p) * x ^ (-(c₁ * Real.log F.p / (5 * Real.log F.q)))) :=
        mul_le_mul_of_nonneg_left hexp hC₁.le
    _ = C₁ * Real.exp (c₁ * Real.log F.p) * x ^ (-(c₁ * Real.log F.p / (5 * Real.log F.q))) := by
        ring

/-! ### Non-escape (GGM §4 Step 1) -/

theorem passes_of_le' {xn N n : ℕ} (h : F.S^[n] N ≤ xn) : F.passes xn N := ⟨n, h⟩

/-- The lower threshold `γ = (μ log p + log q)/(2 log p)` (`log_p q < γ < μ`, GGM's `γ`). -/
noncomputable def gammaLow : ℝ := (F.mu * Real.log F.p + Real.log F.q) / (2 * Real.log F.p)

/-- `γ < μ`. -/
theorem gammaLow_lt_mu : F.gammaLow < F.mu := by
  unfold gammaLow
  have hp := F.log_p_pos
  have hd := F.drift_pos
  unfold drift at hd
  rw [div_lt_iff₀ (by positivity)]
  linarith

/-- **A large sum of valuations implies passage** (the bound on the iteration formula in GGM Step 1): if
`x` is large, `N ≤ x^{θ₀}` and `|a^{(n₀)}(N)| > γ n₀`, then the orbit comes down to `x` or below. -/
theorem passes_of_large_val : ∀ᶠ x : ℝ in Filter.atTop, ∀ N : ℕ, N % F.p ≠ 0 →
    (N : ℝ) ≤ x ^ F.thetaMax →
    F.gammaLow * F.nZero x < (pre (F.valVec N (F.nZero x)) (F.nZero x) : ℝ) →
      F.passes ⌊x⌋₊ N := by
  have hp := F.log_p_pos
  have hq := F.log_q_pos
  have hd := F.drift_pos
  set R : ℝ := (F.rBound : ℝ) with hR
  have hR0 : 0 ≤ R := Int.cast_nonneg_iff.mpr F.rBound_nonneg
  filter_upwards [eventually_log_ge ((F.drift / 2 + Real.log 2) * (20 * Real.log F.q) / F.drift),
    eventually_log_ge (5 / 4 * Real.log (2 * R + 2)), eventually_log_ge 0,
    Filter.eventually_gt_atTop 0] with x h1 h2 hL0 hx0
  intro N hN hNθ hval
  set n₀ := F.nZero x with hn₀
  set L := Real.log x with hLdef
  have hkey := F.syr_iterate_key hN n₀
  set a := pre (F.valVec N n₀) n₀ with ha
  set f : ℤ := F.fint (F.valVec N n₀) (F.resVec N n₀) with hf
  have hkeyR : (F.p : ℝ) ^ a * (F.S^[n₀] N : ℝ) = (F.q : ℝ) ^ n₀ * N + (f : ℝ) := by
    exact_mod_cast hkey
  have hfb := F.abs_fint_le (F.valVec N n₀) (F.resVec N n₀) F.rBound_nonneg
    (fun m => F.abs_r_le_rBound (F.digVec_pos_lt hN n₀ m).2)
  have hfbR : |(f : ℝ)| ≤ (F.p : ℝ) ^ a * (F.q : ℝ) ^ n₀ * R := by
    rw [hR]; exact_mod_cast hfb
  have hpa0 : 0 < (F.p : ℝ) ^ a := pow_pos F.p_real_pos a
  have hS : (F.S^[n₀] N : ℝ) ≤ (F.q : ℝ) ^ n₀ * N / (F.p : ℝ) ^ a + (F.q : ℝ) ^ n₀ * R := by
    rw [div_add' _ _ _ hpa0.ne', le_div_iff₀ hpa0, mul_comm]
    have := le_abs_self (f : ℝ)
    nlinarith
  have hqn : (F.q : ℝ) ^ n₀ = Real.exp (n₀ * Real.log F.q) := by
    rw [Real.exp_nat_mul, Real.exp_log F.q_real_pos]
  have hpa : Real.exp (F.gammaLow * n₀ * Real.log F.p) ≤ (F.p : ℝ) ^ a := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos F.p_real_pos]
    apply Real.exp_le_exp.mpr
    rw [mul_comm (Real.log F.p)]
    exact mul_le_mul_of_nonneg_right hval.le hp.le
  have hγ : F.gammaLow * Real.log F.p = Real.log F.q + F.drift / 2 := by
    unfold gammaLow drift; field_simp; ring
  have hN0 : (0 : ℝ) < N := by
    have : 0 < N := Nat.pos_of_ne_zero (fun h0 => hN (by simp [h0]))
    exact_mod_cast this
  have hNx : Real.log N ≤ F.thetaMax * L := by
    rw [hLdef, ← Real.log_rpow hx0]; exact Real.log_le_log hN0 hNθ
  have hn0 := F.nZero_ge x
  have hn0le : (n₀ : ℝ) * Real.log F.q ≤ L / 5 := by
    have : (n₀ : ℝ) ≤ L / (5 * Real.log F.q) := by
      rw [hn₀]; unfold nZero; exact Nat.floor_le (by positivity)
    calc (n₀ : ℝ) * Real.log F.q ≤ L / (5 * Real.log F.q) * Real.log F.q :=
          mul_le_mul_of_nonneg_right this hq.le
      _ = L / 5 := by field_simp
  -- first term: `q^{n₀} N / p^a ≤ x / 2`
  have hterm1 : (F.q : ℝ) ^ n₀ * N / (F.p : ℝ) ^ a ≤ x / 2 := by
    rw [div_le_iff₀ hpa0]
    calc (F.q : ℝ) ^ n₀ * N = Real.exp (n₀ * Real.log F.q + Real.log N) := by
          rw [Real.exp_add, Real.exp_log hN0, hqn]
      _ ≤ Real.exp (Real.log (x / 2) + F.gammaLow * n₀ * Real.log F.p) := by
          apply Real.exp_le_exp.mpr
          rw [Real.log_div hx0.ne' (by norm_num), ← hLdef]
          have e1 : F.gammaLow * n₀ * Real.log F.p = n₀ * Real.log F.q + n₀ * (F.drift / 2) := by
            rw [mul_comm F.gammaLow, mul_assoc, hγ]; ring
          rw [e1]
          have e2 : F.thetaMax * L = L + F.drift * L / (20 * Real.log F.q) := by
            unfold thetaMax; field_simp
          have h3 : F.drift / 2 * (L / (5 * Real.log F.q) - 1) ≤ F.drift / 2 * n₀ :=
            mul_le_mul_of_nonneg_left hn0 (by positivity)
          have h4 : (F.drift / 2 + Real.log 2) ≤ F.drift * L / (20 * Real.log F.q) := by
            rw [le_div_iff₀ (by positivity)]
            have := mul_le_mul_of_nonneg_left h1 hd.le
            rw [show F.drift * ((F.drift / 2 + Real.log 2) * (20 * Real.log F.q) / F.drift)
              = (F.drift / 2 + Real.log 2) * (20 * Real.log F.q) by field_simp] at this
            linarith
          have e3 : F.drift / 2 * (L / (5 * Real.log F.q) - 1)
              = 2 * (F.drift * L / (20 * Real.log F.q)) - F.drift / 2 := by
            field_simp; ring
          nlinarith
      _ = x / 2 * Real.exp (F.gammaLow * n₀ * Real.log F.p) := by
          rw [Real.exp_add, Real.exp_log (by positivity)]
      _ ≤ x / 2 * (F.p : ℝ) ^ a := mul_le_mul_of_nonneg_left hpa (by positivity)
  -- second term: `q^{n₀} R ≤ x / 2`
  have hterm2 : (F.q : ℝ) ^ n₀ * R ≤ x / 2 := by
    have hRle : R ≤ Real.exp (4 * L / 5) / 2 := by
      have h5 : Real.log (2 * R + 2) ≤ 4 * L / 5 := by linarith
      have h6 : 2 * R + 2 ≤ Real.exp (4 * L / 5) := by
        rw [← Real.exp_log (show 0 < 2 * R + 2 by linarith)]; exact Real.exp_le_exp.mpr h5
      linarith
    have hq5 : (F.q : ℝ) ^ n₀ ≤ Real.exp (L / 5) := by
      rw [hqn]; exact Real.exp_le_exp.mpr hn0le
    calc (F.q : ℝ) ^ n₀ * R ≤ Real.exp (L / 5) * (Real.exp (4 * L / 5) / 2) :=
          mul_le_mul hq5 hRle hR0 (Real.exp_pos _).le
      _ = Real.exp L / 2 := by rw [mul_div_assoc', ← Real.exp_add]; ring_nf
      _ = x / 2 := by rw [hLdef, Real.exp_log hx0]
  have hSx : (F.S^[n₀] N : ℝ) ≤ x := by linarith
  exact F.passes_of_le' (Nat.le_floor hSx)

/-- **First half of GGM Proposition 3.5** (`eq:passage time estimate`): there is `c > 0` depending only on
the family such that if `αβ ≤ θ₀` then `P(T_x(L_{x^β, x^{αβ}}) = ∞) ≤ K x^{-c}` (for `x` large). -/
theorem nonescape (h33 : F.prop33_statement) :
    ∃ c : ℝ, 0 < c ∧ ∀ α β : ℝ, 1 < α → 1 < β → α * β ≤ F.thetaMax →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop,
        expect (F.logUnif (x ^ β) (x ^ (α * β))) (Set.indicator {N | ¬ F.passes ⌊x⌋₊ N} 1)
          ≤ K * x ^ (-c) := by
  obtain ⟨cL, CL, hcL, hCL, hlow⟩ := F.geom_lower_tail F.gammaLow_lt_mu
  obtain ⟨c, C, hc, hC, hval⟩ := F.valuation_law h33
  have hq := F.log_q_pos
  set c' : ℝ := cL / (5 * Real.log F.q) with hc'
  have hc'pos : 0 < c' := by positivity
  refine ⟨min c' c, lt_min hc'pos hc, ?_⟩
  intro α β hα hβ hθ
  refine ⟨CL * Real.exp cL + C, by positivity, ?_⟩
  filter_upwards [hval α hα, F.passes_of_large_val, F.eventually_window_nonempty hα,
    Filter.eventually_ge_atTop 1] with x hx hpass hne hx1
  have hx0 : 0 < x := by linarith
  have hxβ : x ≤ x ^ β := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ β := Real.rpow_le_rpow_of_exponent_le hx1 hβ.le
  have hw : (x ^ β) ^ α = x ^ (α * β) := by rw [← Real.rpow_mul hx0.le]; ring_nf
  rw [← hw]
  set y := x ^ β with hy
  have hW := hne y hxβ
  -- if there is no passage, the sum of valuations is small
  set T : Set (Fin (F.nZero x) → ℕ) := {a | (pre a (F.nZero x) : ℝ) ≤ F.gammaLow * F.nZero x}
    with hT
  have hsub : expect (F.logUnif y (y ^ α)) (Set.indicator {N | ¬ F.passes ⌊x⌋₊ N} 1)
      ≤ expect (F.logUnif y (y ^ α)) (Set.indicator {N | F.valVec N (F.nZero x) ∈ T} 1) := by
    apply expect_le_of_support _ 1 (abs_indicator_le_one _) (abs_indicator_le_one _)
    intro N hN
    have hNW := F.mem_logWindow_of_mem_support hW hN
    obtain ⟨hNp, _, hNy⟩ := (F.mem_logWindow_iff).mp hNW
    have hNθ : (N : ℝ) ≤ x ^ F.thetaMax := by
      calc (N : ℝ) ≤ y ^ α := hNy
        _ = x ^ (α * β) := hw
        _ ≤ x ^ F.thetaMax := Real.rpow_le_rpow_of_exponent_le hx1 hθ
    by_cases hp : F.passes ⌊x⌋₊ N
    · rw [Set.indicator_of_notMem (by simpa using hp)]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    · rw [Set.indicator_of_mem (by simpa using hp)]
      have hmem : F.valVec N (F.nZero x) ∈ T := by
        simp only [hT, Set.mem_setOf_eq]
        by_contra hlt
        exact hp (hpass N hNp hNθ (not_le.mp hlt))
      rw [Set.indicator_of_mem (by simpa using hmem)]
  have h1 := expect_indicator_le_add_dTV ((F.logUnif y (y ^ α)).map fun N => F.valVec N (F.nZero x))
    (PMF.iid (geomP F.p) (F.nZero x)) T
  rw [expect_map_indicator] at h1
  have h2 := hlow (F.nZero x)
  have h3 := hx y hxβ
  have h4 := F.exp_neg_nZero_le hcL.le hx0
  have hm1 : x ^ (-c') ≤ x ^ (-(min c' c)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (neg_le_neg (min_le_left _ _))
  have hm2 : x ^ (-c) ≤ x ^ (-(min c' c)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (neg_le_neg (min_le_right _ _))
  calc _ ≤ _ := hsub
    _ ≤ _ := h1
    _ ≤ CL * Real.exp (-(cL * F.nZero x)) + C * x ^ (-c) := add_le_add h2 h3
    _ ≤ CL * (Real.exp cL * x ^ (-c')) + C * x ^ (-(min c' c)) := by
        gcongr
    _ ≤ CL * (Real.exp cL * x ^ (-(min c' c))) + C * x ^ (-(min c' c)) := by
        gcongr
    _ = (CL * Real.exp cL + C) * x ^ (-(min c' c)) := by ring

/-! ### Good tuples and the edge of the window -/

/-- **Good tuples occur with high probability** (GGM `eq: error for not in A`). -/
theorem good_whp (h33 : F.prop33_statement) : ∀ α : ℝ, 1 < α → ∀ᶠ x : ℝ in Filter.atTop,
    ∀ y : ℝ, x ≤ y →
      expect (F.logUnif y (y ^ α)) (Set.indicator {N | ¬ F.goodVec x (F.valVec N (F.nZero x))} 1)
        ≤ 2 * Real.log x ^ (-4 : ℝ) := by
  intro α hα
  obtain ⟨c, C, hc, hC, hval⟩ := F.valuation_law h33
  filter_upwards [hval α hα, F.geom_good_tail, eventually_mul_rpow_neg_le_log hc 4 C] with
    x hx hgt hxc
  intro y hy
  have h1 := expect_indicator_le_add_dTV ((F.logUnif y (y ^ α)).map fun N => F.valVec N (F.nZero x))
    (PMF.iid (geomP F.p) (F.nZero x)) {a | ¬ F.goodVec x a}
  rw [expect_map_indicator] at h1
  have h2 := hgt (F.nZero x) le_rfl
  have h3 := hx y hy
  calc _ ≤ _ := h1
    _ ≤ Real.log x ^ (-4 : ℝ) + C * x ^ (-c) := add_le_add h2 h3
    _ ≤ 2 * Real.log x ^ (-4 : ℝ) := by linarith

/-- **Mass of the edge of the window**: `P(N ∈ edge) ≤ K log^{-1/5} x` (the logarithmic side of (iv) in
the accompanying paper). -/
theorem edge_mass : ∀ α : ℝ, 1 < α → ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop, ∀ y : ℝ, x ≤ y →
    expect (F.logUnif y (y ^ α)) (Set.indicator {N | F.edge x y α N} 1)
      ≤ K * Real.log x ^ (-(1 / 5 : ℝ)) := by
  classical
  intro α hα
  have hμ := F.mu_pos
  have hd := F.drift_pos
  have hα1 : 0 < α - 1 := by linarith
  set K : ℝ := (4 * F.drift + 4 * F.p) * (2 * F.mu) / ((α - 1) * F.mu) with hK
  refine ⟨K, by positivity, ?_⟩
  filter_upwards [F.eventually_windowMass_ge hα, F.eventually_window_nonempty hα,
    eventually_add_mul_rpow_le (show (0.8:ℝ) < 1 by norm_num) one_pos 0 (2 * F.drift)
      (show (0:ℝ) < 1 / 2 by norm_num),
    eventually_log_ge 1, Filter.eventually_ge_atTop 1] with x hZ hne hV hL hx1
  intro y hy
  rw [Real.rpow_one, zero_add] at hV
  have hy1 : 1 ≤ y := le_trans hx1 hy
  have hy0 : 0 < y := by linarith
  have hyα : y ≤ y ^ α := by
    calc y = y ^ (1 : ℝ) := (Real.rpow_one y).symm
      _ ≤ y ^ α := Real.rpow_le_rpow_of_exponent_le hy1 hα.le
  set L := Real.log x with hLdef
  set V := L ^ (0.8 : ℝ) with hVdef
  have hLpos : 0 < L := by linarith
  have hV0 : 0 ≤ V := Real.rpow_nonneg hLpos.le _
  have hly : L ≤ Real.log y := Real.log_le_log (by linarith) hy
  have hW := hne y hy
  set W := F.logWindow y (y ^ α) with hWdef
  have hZpos := F.windowMass_pos hW
  rw [F.expect_logUnif hW]
  -- the two small windows forming the edge
  set y₁ := y * Real.exp (2 * F.drift * V) with hy₁
  set y₂ := y ^ α * Real.exp (-(2 * F.drift * V)) with hy₂
  have hy₁ge : y ≤ y₁ := le_mul_of_one_le_right hy0.le (Real.one_le_exp (by positivity))
  have hy₂le : y₂ ≤ y ^ α := mul_le_of_le_one_right (by positivity)
    (Real.exp_le_one_iff.mpr (by linarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hd.le) hV0]))
  -- `y₂ ≥ 1`: `2dV ≤ L/2 ≤ α log y`
  have hy₂1 : 1 ≤ y₂ := by
    rw [hy₂, ← Real.exp_log (show 0 < y ^ α by positivity), ← Real.exp_add]
    apply Real.one_le_exp
    rw [Real.log_rpow hy0]
    nlinarith
  have hsub : ∑ N ∈ W, Set.indicator {N | F.edge x y α N} (1 : ℕ → ℝ) N * (N : ℝ)⁻¹
      ≤ F.windowMass y y₁ + F.windowMass y₂ (y ^ α) := by
    have h1 : ∑ N ∈ W, Set.indicator {N | F.edge x y α N} (1 : ℕ → ℝ) N * (N : ℝ)⁻¹
        = ∑ N ∈ W.filter (fun N => F.edge x y α N), (N : ℝ)⁻¹ := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun N _ => ?_
      by_cases h : F.edge x y α N
      · rw [Set.indicator_of_mem (by simpa using h), if_pos h]; simp
      · rw [Set.indicator_of_notMem (by simpa using h), if_neg h]; simp
    rw [h1]
    have hsubset : W.filter (fun N => F.edge x y α N) ⊆ F.logWindow y y₁ ∪ F.logWindow y₂ (y ^ α) := by
      intro N hN
      rw [Finset.mem_filter] at hN
      obtain ⟨hNW, hed⟩ := hN
      unfold edge at hed
      rw [← hLdef, ← hVdef] at hed
      obtain ⟨hNp, hyN, hNy⟩ := (F.mem_logWindow_iff).mp hNW
      have hN0 : (0 : ℝ) < N := by linarith
      rw [Finset.mem_union]
      rcases hed with h | h
      · left
        refine (F.mem_logWindow_iff).mpr ⟨hNp, hyN, ?_⟩
        rw [hy₁, ← Real.exp_log hN0, ← Real.exp_log hy0, ← Real.exp_add]
        apply Real.exp_le_exp.mpr; linarith
      · right
        refine (F.mem_logWindow_iff).mpr ⟨hNp, ?_, hNy⟩
        rw [hy₂, ← Real.exp_log hN0, ← Real.exp_log (show 0 < y ^ α by positivity), ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        rw [Real.log_rpow hy0]; linarith
    calc ∑ N ∈ W.filter (fun N => F.edge x y α N), (N : ℝ)⁻¹
        ≤ ∑ N ∈ F.logWindow y y₁ ∪ F.logWindow y₂ (y ^ α), (N : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
      _ ≤ ∑ N ∈ F.logWindow y y₁, (N : ℝ)⁻¹ + ∑ N ∈ F.logWindow y₂ (y ^ α), (N : ℝ)⁻¹ := by
          rw [← Finset.sum_union_inter]
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
      _ = F.windowMass y y₁ + F.windowMass y₂ (y ^ α) := rfl
  have hm1 := F.windowMass_approx hy1 hy₁ge
  have hm2 := F.windowMass_approx hy₂1 hy₂le
  have hl1 : Real.log (y₁ / y) = 2 * F.drift * V := by
    rw [hy₁, mul_div_cancel_left₀ _ hy0.ne', Real.log_exp]
  have hl2 : Real.log (y ^ α / y₂) = 2 * F.drift * V := by
    rw [hy₂, div_mul_eq_div_div, div_self (by positivity), one_div, Real.log_inv, Real.log_exp]
    ring
  rw [hl1] at hm1
  rw [hl2] at hm2
  have hpy : (F.p : ℝ) / y ≤ F.p := div_le_self (by positivity) hy1
  have hpy₂ : (F.p : ℝ) / y₂ ≤ F.p := div_le_self (by positivity) hy₂1
  have hnum : F.windowMass y y₁ + F.windowMass y₂ (y ^ α)
      ≤ (4 * F.drift + 4 * F.p) * V / F.mu := by
    have e1 := (abs_le.mp hm1).2
    have e2 := (abs_le.mp hm2).2
    have hV1 : 1 ≤ V := Real.one_le_rpow hL (by norm_num)
    have : 2 * F.drift * V / F.mu + 2 * F.drift * V / F.mu + 2 * F.p
        ≤ (4 * F.drift + 4 * F.p) * V / F.mu := by
      rw [show (4 * F.drift + 4 * F.p) * V / F.mu = 4 * F.drift * V / F.mu + 4 * F.p * V / F.mu by ring]
      have : 2 * F.p ≤ 4 * F.p * V / F.mu := by
        rw [le_div_iff₀ hμ]
        have := F.mu_le_two
        nlinarith [F.p_real_pos]
      have : 2 * F.drift * V / F.mu + 2 * F.drift * V / F.mu = 4 * F.drift * V / F.mu := by ring
      linarith
    linarith
  have hZy := hZ y hy
  have hZ' : 0 < (α - 1) * L / (2 * F.mu) := by positivity
  have hVL : V / L = L ^ (-(1 / 5 : ℝ)) := by
    rw [hVdef, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hLpos]; norm_num
  calc (∑ N ∈ W, Set.indicator {N | F.edge x y α N} (1 : ℕ → ℝ) N * (N : ℝ)⁻¹) / F.windowMass y (y ^ α)
      ≤ ((4 * F.drift + 4 * F.p) * V / F.mu) / ((α - 1) * L / (2 * F.mu)) := by
        apply div_le_div₀ (by positivity) (le_trans hsub hnum) hZ' hZy
    _ = K * (V / L) := by rw [hK]; field_simp
    _ = K * L ^ (-(1 / 5 : ℝ)) := by rw [hVL]

end Family

end GGMCollatz
