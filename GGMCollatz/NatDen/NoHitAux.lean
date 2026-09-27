import GGMCollatz.NatDen.Statements

/-!
# Lemmas for (D.1): equidistribution of the uniform window, and the bound on the probability of not hitting derived from equidistribution

* `card_le_of_modEq`: if natural numbers congruent modulo `Q` lie in `[a, b]`, their number is at most `(b-a)/Q + 1`
  (the counting version of `Family.sum_inv_le_of_modEq`, by induction on the largest element).
* `card_window_ge`: the window `ℕ_p ∩ [lo, hi]` has at least `(hi - lo)/μ - 2` points.
* `unifWin_equidist`: the `ℓ¹` distance between the distribution modulo `p^k` of the uniform window and the uniform
  distribution on the residues of `ℕ_p` is at most `10 p^k / #W` (the uniform-window version of
  `Family.window_equidist`).
* `valuation_law_of_equidist`, `noPass_of_equidist`: the bodies of `Family.valuation_law` and `Family.nonescape`
  rewritten, independently of the window measure, under the sole hypothesis "supported on `ℕ_p ∩ [1, x^{θ₀}]` and
  equidistributed modulo `p^k` for `p^{2k+1} ≤ x`" (from GGM Prop. 3.1 and the deterministic descent
  `Family.passes_of_large_val`). The constants do not depend on the window.

The namespace is `GGMCollatz.ND.NH` (to avoid name clashes with parallel work).
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace NH

open Family

variable (F : Family)

/-! ### Counting points of an arithmetic progression -/

/-- **Counting points of an arithmetic progression**: if a finite set of natural numbers congruent modulo `Q` lies in
`[a, b]` (`a ≤ b`), its cardinality is at most `(b - a)/Q + 1`. -/
theorem card_le_of_modEq {Q : ℕ} (hQ : 0 < Q) {a : ℝ} (S : Finset ℕ) :
    ∀ b : ℝ, a ≤ b → (∀ N ∈ S, a ≤ (N : ℝ) ∧ (N : ℝ) ≤ b) →
      (∀ N ∈ S, ∀ N' ∈ S, N % Q = N' % Q) →
      (S.card : ℝ) ≤ (b - a) / Q + 1 := by
  classical
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  induction S using Finset.induction_on_max with
  | empty =>
    intro b hab _ _
    rw [Finset.card_empty, Nat.cast_zero]
    have : 0 ≤ (b - a) / Q := div_nonneg (by linarith) hQR.le
    linarith
  | insert M S hlt ih =>
    intro b hab hmem hcong
    have hM := hmem M (Finset.mem_insert_self M S)
    rw [Finset.card_insert_of_notMem (fun h => lt_irrefl M (hlt M h))]
    push_cast
    by_cases hS : S = ∅
    · subst hS
      rw [Finset.card_empty, Nat.cast_zero, zero_add]
      have : 0 ≤ (b - a) / Q := div_nonneg (by linarith) hQR.le
      linarith
    · have hle : ∀ N ∈ S, (N : ℝ) ≤ M - Q := by
        intro N hN
        have h1 := hlt N hN
        have h2 := hcong M (Finset.mem_insert_self M S) N (Finset.mem_insert_of_mem hN)
        have h3 := Nat.sub_mod_eq_zero_of_mod_eq h2
        have h4 : Q ≤ M - N := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero h3)
        have h5 : N + Q ≤ M := by omega
        have : ((N + Q : ℕ) : ℝ) ≤ M := by exact_mod_cast h5
        push_cast at this; linarith
      obtain ⟨N₁, hN₁⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      have haMQ : a ≤ (M : ℝ) - Q :=
        le_trans (hmem N₁ (Finset.mem_insert_of_mem hN₁)).1 (hle N₁ hN₁)
      have ih' := ih (M - Q) haMQ
        (fun N hN => ⟨(hmem N (Finset.mem_insert_of_mem hN)).1, hle N hN⟩)
        (fun N hN N' hN' => hcong N (Finset.mem_insert_of_mem hN) N' (Finset.mem_insert_of_mem hN'))
      have e1 : ((M : ℝ) - Q - a) / Q + 1 + 1 = ((M : ℝ) - a) / Q + 1 := by
        field_simp; ring
      have e2 : ((M : ℝ) - a) / Q ≤ (b - a) / Q :=
        div_le_div_of_nonneg_right (by linarith [hM.2]) hQR.le
      linarith

/-! ### The number of window points -/

/-- **Lower bound on the number of window points**: if `0 < lo ≤ hi`, then `#(ℕ_p ∩ [lo, hi]) ≥ (hi - lo)/μ - 2`. -/
theorem card_window_ge {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi) :
    (hi - lo) / F.mu - 2 ≤ ((F.logWindow lo hi).card : ℝ) := by
  classical
  have hp2 := F.p_real_two_le
  have hpos : 0 < F.p := F.p_pos
  have hhi0 : 0 < hi := by linarith
  set A := ⌈lo⌉₊ with hA
  set B := ⌊hi⌋₊ with hB
  have hWeq : F.logWindow lo hi = (Finset.Icc A B).filter (fun N => N % F.p ≠ 0) := by
    ext N
    rw [F.mem_logWindow_iff, Finset.mem_filter, Finset.mem_Icc, hA, hB, Nat.ceil_le,
      Nat.le_floor_iff hhi0.le]
    tauto
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.Icc A B)
    (fun N => N % F.p ≠ 0)
  -- the number of multiples of `p`
  have hmult : (((Finset.Icc A B).filter (fun N => ¬ (N % F.p ≠ 0))).card : ℝ)
      ≤ (hi - lo) / F.p + 1 := by
    have := card_le_of_modEq hpos (a := lo) ((Finset.Icc A B).filter (fun N => ¬ (N % F.p ≠ 0)))
      hi hle
      (fun N hN => by
        have hN' := (Finset.mem_filter.mp hN).1
        rw [Finset.mem_Icc, hA, hB, Nat.ceil_le, Nat.le_floor_iff hhi0.le] at hN'
        exact hN')
      (fun N hN N' hN' => by
        have h1 := (Finset.mem_filter.mp hN).2
        have h2 := (Finset.mem_filter.mp hN').2
        push_neg at h1 h2
        rw [h1, h2])
    exact this
  -- the number of consecutive integers
  have hIcc : hi - lo - 1 ≤ ((Finset.Icc A B).card : ℝ) := by
    rw [Nat.card_Icc]
    have hB' : hi - 1 < (B : ℝ) := Nat.sub_one_lt_floor hi
    have hA' : (A : ℝ) < lo + 1 := Nat.ceil_lt_add_one hlo.le
    rcases le_or_gt A (B + 1) with h | h
    · rw [Nat.cast_sub h]; push_cast; linarith
    · have h2 : ((B + 2 : ℕ) : ℝ) ≤ A := by exact_mod_cast h
      push_cast at h2
      linarith
  have hμinv : (hi - lo) / F.mu = (hi - lo) - (hi - lo) / F.p := by
    unfold mu
    have : (F.p : ℝ) - 1 ≠ 0 := by linarith
    have : (F.p : ℝ) ≠ 0 := by linarith
    field_simp
  have hcast : (((Finset.Icc A B).filter (fun N => N % F.p ≠ 0)).card : ℝ)
      + (((Finset.Icc A B).filter (fun N => ¬ (N % F.p ≠ 0))).card : ℝ)
      = ((Finset.Icc A B).card : ℝ) := by exact_mod_cast hsplit
  rw [hWeq]
  linarith

/-! ### The uniform window -/

/-- If the window is nonempty, the support of the uniform window is contained in the window. -/
theorem mem_window_of_mem_support {lo hi : ℝ} (h : (F.logWindow lo hi).Nonempty) {N : ℕ}
    (hN : N ∈ (unifWin F lo hi).support) : N ∈ F.logWindow lo hi := by
  classical
  unfold unifWin at hN
  rw [dif_pos h, PMF.mem_support_uniformOfFinset_iff] at hN
  exact hN

/-- The mass (in ℝ) of a nonempty uniform window: `1_W / #W`. -/
theorem unifWin_apply_toReal {lo hi : ℝ} (h : (F.logWindow lo hi).Nonempty) (N : ℕ) :
    (unifWin F lo hi N).toReal
      = if N ∈ F.logWindow lo hi then ((F.logWindow lo hi).card : ℝ)⁻¹ else 0 := by
  classical
  unfold unifWin
  rw [dif_pos h, PMF.uniformOfFinset_apply]
  by_cases hN : N ∈ F.logWindow lo hi
  · rw [if_pos hN, if_pos hN, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · rw [if_neg hN, if_neg hN]; simp

/-- The mass of the push-forward of the uniform window modulo `p^k`: `#{N ∈ W | N ≡ z} / #W`. -/
theorem unifWin_map_cast_apply_toReal {lo hi : ℝ} (h : (F.logWindow lo hi).Nonempty) {k : ℕ}
    (z : ZMod (F.p ^ k)) :
    ((PMF.map (fun N : ℕ => (N : ZMod (F.p ^ k))) (unifWin F lo hi)) z).toReal
      = (((F.logWindow lo hi).filter (fun N : ℕ => (N : ZMod (F.p ^ k)) = z)).card : ℝ)
          / (F.logWindow lo hi).card := by
  classical
  rw [PMF.map_apply]
  rw [tsum_eq_sum (s := F.logWindow lo hi) (fun N hN => by
    have : unifWin F lo hi N = 0 := by
      unfold unifWin; rw [dif_pos h, PMF.uniformOfFinset_apply, if_neg hN]
    rw [this]; split_ifs <;> rfl)]
  rw [ENNReal.toReal_sum (fun N _ => by
    split_ifs
    · exact PMF.apply_ne_top _ _
    · exact ENNReal.zero_ne_top)]
  trans ∑ N ∈ F.logWindow lo hi,
    (if (N : ZMod (F.p ^ k)) = z then ((F.logWindow lo hi).card : ℝ)⁻¹ else 0)
  · refine Finset.sum_congr rfl fun N hN => ?_
    by_cases hc : (N : ZMod (F.p ^ k)) = z
    · rw [if_pos hc.symm, if_pos hc, unifWin_apply_toReal F h, if_pos hN]
    · rw [if_neg (fun hh => hc hh.symm), if_neg hc]; simp
  · rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- **Equidistribution of the uniform window modulo `p^k`**: if `1 ≤ lo ≤ hi`, the window is nonempty and
`k ≥ 1`, then the `ℓ¹` distance is at most `10 p^k / #W`. -/
theorem unifWin_equidist {lo hi : ℝ} (hlo : 1 ≤ lo) (hle : lo ≤ hi)
    (h : (F.logWindow lo hi).Nonempty) {k : ℕ} (hk : 1 ≤ k) :
    PMF.dTV ((unifWin F lo hi).map fun N => (N : ZMod (F.p ^ k))) (F.unifNpMod k)
      ≤ 10 * (F.p : ℝ) ^ k / (F.logWindow lo hi).card := by
  classical
  have hp := F.p_pos
  have hμ := F.mu_pos
  have hμ1 := F.one_lt_mu
  have hμ2 := F.mu_le_two
  have hlo0 : 0 < lo := by linarith
  rw [map_coe_eq]
  set ν := PMF.map (fun N : ℕ => (N : ZMod (F.p ^ k))) (unifWin F lo hi) with hν
  set u := F.unifNpMod k with hu
  set W := F.logWindow lo hi with hW
  set T := Finset.univ.filter fun z : ZMod (F.p ^ k) => z.val % F.p ≠ 0 with hT
  have hWpos : (0 : ℝ) < W.card := by exact_mod_cast h.card_pos
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
  have hpkR : (0 : ℝ) < (F.p : ℝ) ^ k := by positivity
  have hpk1R : (1 : ℝ) ≤ (F.p : ℝ) ^ k := one_le_pow₀ F.one_lt_p_real.le
  have hWlow := card_window_ge F hlo0 hle
  rw [← hW] at hWlow
  -- the bound for each class
  have hclass : ∀ z : ZMod (F.p ^ k), (ν z).toReal - (u z).toReal
      ≤ if z ∈ T then 5 / (W.card : ℝ) else 0 := by
    intro z
    rw [hν, unifWin_map_cast_apply_toReal F h, huval]
    by_cases hz : z ∈ T
    · rw [if_pos hz, if_pos hz]
      have hcnt := card_le_of_modEq (pow_pos hp k) (a := lo)
        (W.filter (fun N : ℕ => (N : ZMod (F.p ^ k)) = z)) hi hle
        (fun N hN => by
          obtain ⟨_, h1, h2⟩ := (F.mem_logWindow_iff).mp (Finset.mem_filter.mp hN).1
          exact ⟨h1, h2⟩)
        (fun N hN N' hN' => (ZMod.natCast_eq_natCast_iff' N N' (F.p ^ k)).mp
          ((Finset.mem_filter.mp hN).2.trans (Finset.mem_filter.mp hN').2.symm))
      push_cast at hcnt
      have hinv : F.mu / (F.p : ℝ) ^ k ≤ (T.card : ℝ)⁻¹ := by
        rw [div_le_iff₀ hpkR, inv_mul_eq_div, le_div_iff₀ hTpos]
        have := mul_le_mul_of_nonneg_left hTcard hμ.le
        rwa [mul_div_cancel₀ _ hμ.ne'] at this
      set cnt := ((W.filter (fun N : ℕ => (N : ZMod (F.p ^ k)) = z)).card : ℝ) with hcntdef
      -- `hi - lo ≤ μ (#W + 2)`
      have hl : hi - lo ≤ F.mu * (W.card + 2) := by
        have := mul_le_mul_of_nonneg_left hWlow hμ.le
        have e : F.mu * ((hi - lo) / F.mu - 2) = (hi - lo) - 2 * F.mu := by field_simp
        rw [e] at this; linarith
      have hmain : cnt / W.card - F.mu / (F.p : ℝ) ^ k ≤ 5 / W.card := by
        rw [div_sub' hWpos.ne', div_le_div_iff_of_pos_right hWpos]
        -- `cnt - #W μ/p^k ≤ (hi-lo)/p^k + 1 - #W μ/p^k ≤ 2μ/p^k + 1 ≤ 5`
        have h1 : (hi - lo) / (F.p : ℝ) ^ k - W.card * (F.mu / (F.p : ℝ) ^ k)
            ≤ 2 * F.mu / (F.p : ℝ) ^ k := by
          rw [mul_div_assoc', ← sub_div]
          apply div_le_div_of_nonneg_right _ hpkR.le
          linarith
        have h2 : 2 * F.mu / (F.p : ℝ) ^ k ≤ 4 := by
          rw [div_le_iff₀ hpkR]; nlinarith
        linarith
      linarith [hinv, hmain]
    · rw [if_neg hz, if_neg hz]
      have hempty : W.filter (fun N : ℕ => (N : ZMod (F.p ^ k)) = z) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro N hN hNz
        apply hz
        rw [hT, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hNz, ZMod.val_natCast, Nat.mod_mod_of_dvd _ (dvd_pow_self F.p (by omega))]
        exact ((F.mem_logWindow_iff).mp hN).1
      rw [hempty, Finset.card_empty]; simp
  -- `ℓ¹ = 2 Σ (ν - u)⁺`
  have hsumν : ∑ z, (ν z).toReal = 1 := by
    have := tsum_toReal_eq_one ν; rwa [tsum_fintype] at this
  have hsumu : ∑ z, (u z).toReal = 1 := by
    have := tsum_toReal_eq_one u; rwa [tsum_fintype] at this
  unfold PMF.dTV
  rw [tsum_fintype]
  have hpt : ∀ z : ZMod (F.p ^ k), |(ν z).toReal - (u z).toReal|
      ≤ 2 * (if z ∈ T then 5 / (W.card : ℝ) else 0) - ((ν z).toReal - (u z).toReal) := by
    intro z
    have h1 := hclass z
    rcases le_or_gt 0 ((ν z).toReal - (u z).toReal) with h0 | h0
    · rw [abs_of_nonneg h0]; linarith
    · rw [abs_of_neg h0]
      have : 0 ≤ (if z ∈ T then 5 / (W.card : ℝ) else 0 : ℝ) := by
        split_ifs <;> positivity
      linarith
  calc ∑ z, |(ν z).toReal - (u z).toReal|
      ≤ ∑ z, (2 * (if z ∈ T then 5 / (W.card : ℝ) else 0) - ((ν z).toReal - (u z).toReal)) :=
        Finset.sum_le_sum fun z _ => hpt z
    _ = 2 * (T.card * (5 / (W.card : ℝ))) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsumν, hsumu, ← Finset.mul_sum,
          Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ 2 * ((F.p : ℝ) ^ k * (5 / (W.card : ℝ))) := by
        gcongr
        exact le_trans hTcard (div_le_self (by positivity) F.one_lt_mu.le)
    _ = 10 * (F.p : ℝ) ^ k / W.card := by ring

/-! ### From equidistribution to the valuation law and the probability of not hitting -/

/-- **The valuation law** (the measure-independent form of `Family.valuation_law`): for large `x`, if `X` is
supported on `ℕ_p` and its distribution modulo `p^k` is uniform up to `10 p^{-k}` for all `k ≥ 1` with
`p^{2k+1} ≤ x`, then the `ℓ¹` distance between the law of the valuation vector `a^{(n₀)}` and `G(μ)^{n₀}` is at
most `C x^{-c}`. -/
theorem valuation_law_of_equidist :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ x : ℝ in Filter.atTop, ∀ X : PMF ℕ,
      (∀ N ∈ X.support, N % F.p ≠ 0) →
      (∀ k : ℕ, 1 ≤ k → (F.p : ℝ) ^ (2 * k + 1) ≤ x →
        PMF.dTV (X.map fun N => (N : ZMod (F.p ^ k))) (F.unifNpMod k)
          ≤ 10 * (F.p : ℝ) ^ (-(k : ℝ))) →
      PMF.dTV (X.map fun N => F.valVec N (F.nZero x)) (PMF.iid (geomP F.p) (F.nZero x))
        ≤ C * x ^ (-c) := by
  obtain ⟨c₁, C₁, hc₁, hC₁, h⟩ := F.prop33 (1 / 4) 10 (by norm_num) (by norm_num)
  have hp := F.log_p_pos
  have hq := F.log_q_pos
  have hpq := F.log_p_lt_log_q
  have hμ := F.mu_pos
  have hμ2 := F.mu_le_two
  refine ⟨c₁ * Real.log F.p / (5 * Real.log F.q), C₁ * Real.exp (c₁ * Real.log F.p),
    by positivity, by positivity, ?_⟩
  filter_upwards [eventually_log_ge (30 * Real.log F.p), eventually_log_ge (10 * Real.log F.q),
    Filter.eventually_ge_atTop 1] with x hL1 hL2 hx1
  intro X hsupp hequi
  have hx0 : 0 < x := by linarith
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
  have hkge' : ((F.p : ℝ) / ((F.p : ℝ) - 1) + 1 / 4) * (n₀ : ℝ) ≤ (k : ℝ) := hkge
  have hres := h n₀ k X hkge' hsupp (hequi k hk1 h1)
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

/-- **The probability of not hitting** (the measure-independent form of `Family.nonescape`, GGM §4 Step 1): there
are `c, K > 0` depending only on the family such that, for large `x`, every `X` supported on `ℕ_p ∩ [1, x^{θ₀}]`
satisfying the equidistribution of `valuation_law_of_equidist` has `P_X(T_x = ∞) ≤ K x^{-c}`. -/
theorem noPass_of_equidist :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop, ∀ X : PMF ℕ,
      (∀ N ∈ X.support, N % F.p ≠ 0 ∧ (N : ℝ) ≤ x ^ F.thetaMax) →
      (∀ k : ℕ, 1 ≤ k → (F.p : ℝ) ^ (2 * k + 1) ≤ x →
        PMF.dTV (X.map fun N => (N : ZMod (F.p ^ k))) (F.unifNpMod k)
          ≤ 10 * (F.p : ℝ) ^ (-(k : ℝ))) →
      Family.expect X (Set.indicator {N | ¬ F.passes ⌊x⌋₊ N} 1) ≤ K * x ^ (-c) := by
  obtain ⟨cL, CL, hcL, hCL, hlow⟩ := F.geom_lower_tail F.gammaLow_lt_mu
  obtain ⟨c, C, hc, hC, hval⟩ := valuation_law_of_equidist F
  have hq := F.log_q_pos
  set c' : ℝ := cL / (5 * Real.log F.q) with hc'
  have hc'pos : 0 < c' := by positivity
  refine ⟨min c' c, CL * Real.exp cL + C, lt_min hc'pos hc, by positivity, ?_⟩
  filter_upwards [hval, F.passes_of_large_val, Filter.eventually_ge_atTop 1] with x hx hpass hx1
  intro X hsupp hequi
  have hx0 : 0 < x := by linarith
  -- if the orbit does not pass, the valuation sum is small
  set T : Set (Fin (F.nZero x) → ℕ) := {a | (pre a (F.nZero x) : ℝ) ≤ F.gammaLow * F.nZero x}
    with hT
  have hsub : Family.expect X (Set.indicator {N | ¬ F.passes ⌊x⌋₊ N} 1)
      ≤ Family.expect X (Set.indicator {N | F.valVec N (F.nZero x) ∈ T} 1) := by
    apply expect_le_of_support _ 1 (abs_indicator_le_one _) (abs_indicator_le_one _)
    intro N hN
    obtain ⟨hNp, hNθ⟩ := hsupp N hN
    by_cases hp : F.passes ⌊x⌋₊ N
    · rw [Set.indicator_of_notMem (by simpa using hp)]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    · rw [Set.indicator_of_mem (by simpa using hp)]
      have hmem : F.valVec N (F.nZero x) ∈ T := by
        simp only [hT, Set.mem_setOf_eq]
        by_contra hlt
        exact hp (hpass N hNp hNθ (not_le.mp hlt))
      rw [Set.indicator_of_mem (by simpa using hmem)]
  have h1 := expect_indicator_le_add_dTV (X.map fun N => F.valVec N (F.nZero x))
    (PMF.iid (geomP F.p) (F.nZero x)) T
  rw [expect_map_indicator] at h1
  have h2 := hlow (F.nZero x)
  have h3 := hx X (fun N hN => (hsupp N hN).1) hequi
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

end NH

end ND

end GGMCollatz
