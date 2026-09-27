import GGMCollatz.Tao.Sec7.FpPlus

/-!
# GGM §7: the column tail after the passage (the bad columns of (7.54) of tao-collatz, `col_tail_mass_le`)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, from the statement in `TaoCollatz/Sec7/Case3.lean`
(`col_tail_mass_le`); generalized to the GGM family (p, q, r). Modified.

tao-collatz took the bad columns to be those with a `j`-advance `≥ 0.9m` (`log 9/(4 log 2) ≈ 0.79 < 0.9`). In GGM,
`η/(2μ) = (log q²/log p)·(p-1)/(2p)` can be close to 1 (e.g. `≈ 0.977` for `(p,q) = (3,5)`), so
the threshold is `colFrac = (1 + η/(2μ))/2 < 1` (condition (b) gives `η/(2μ) < 1`).

* `colFrac`, `colFrac_lt_one`, `colFrac_pos`.
* `col_tail_mass_le`: for the first passage with budget `s log p ≤ (m+2) log q²` followed by `P` steps, the probability that the `j`-advance is
  `≥ colFrac · m` is `≤ m^{-A}/2` (for large `m`). Proved (from `fpDistPlus_col_tail` in `FpPlus.lean`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- The bad-column threshold `colFrac = (1 + η/(2μ))/2` (`η = log_p q²`, `1/(2μ) = slopeInv`). -/
noncomputable def colFrac : ℝ :=
  (1 + Real.log ((F.q : ℝ) ^ 2) / Real.log F.p * F.slopeInv) / 2

/-- `η/(2μ) < 1` (condition (b)). -/
theorem eta_slopeInv_lt_one : Real.log ((F.q : ℝ) ^ 2) / Real.log F.p * F.slopeInv < 1 := by
  have hp : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hq : (0 : ℝ) < F.q := by exact_mod_cast F.q_pos
  have hlp : 0 < Real.log (F.p : ℝ) := Real.log_pos (by linarith)
  have hp1 : (0 : ℝ) < (F.p : ℝ) - 1 := by linarith
  -- logarithm of condition (b): `log q < (p/(p-1)) log p`
  have hb := F.subcritical
  have hlog : Real.log (F.q : ℝ) < (F.p : ℝ) / ((F.p : ℝ) - 1) * Real.log F.p := by
    have := Real.log_lt_log hq hb
    rwa [Real.log_rpow (by linarith)] at this
  unfold slopeInv
  rw [Real.log_pow]
  push_cast
  rw [div_mul_div_comm, div_lt_one (by positivity)]
  have h1 : Real.log (F.q : ℝ) * ((F.p : ℝ) - 1) < (F.p : ℝ) * Real.log F.p := by
    have := mul_lt_mul_of_pos_right hlog hp1
    have heq : (F.p : ℝ) / ((F.p : ℝ) - 1) * Real.log F.p * ((F.p : ℝ) - 1)
        = (F.p : ℝ) * Real.log F.p := by field_simp
    linarith
  nlinarith

theorem colFrac_lt_one : F.colFrac < 1 := by
  have := F.eta_slopeInv_lt_one
  unfold colFrac
  linarith

theorem colFrac_pos : 0 < F.colFrac := by
  have hp : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hq : (1 : ℝ) ≤ (F.q : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ F.q := by exact_mod_cast F.q_pos
    nlinarith
  have h1 : 0 ≤ Real.log ((F.q : ℝ) ^ 2) := Real.log_nonneg hq
  have h2 : 0 < Real.log (F.p : ℝ) := Real.log_pos (by linarith)
  have h3 : 0 ≤ F.slopeInv := by unfold slopeInv; apply div_nonneg <;> linarith
  unfold colFrac
  have : 0 ≤ Real.log ((F.q : ℝ) ^ 2) / Real.log F.p * F.slopeInv := by positivity
  linarith

/-- Exponentials beat polynomials: for `κ > 0`, `C > 0` there is `N` such that `m ≥ N` implies `2C e^{-κm} ≤ m^{-A}/2`. -/
theorem CT.exp_le_rpow (κ : ℝ) (hκ : 0 < κ) (A C : ℝ) (hC : 0 < C) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → 2 * C * Real.exp (-κ * m) ≤ (m : ℝ) ^ (-A) / 2 := by
  have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero A κ hκ
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (4 * C) by positivity))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  refine ⟨max ⌈N₀⌉₊ 1, fun m hm => ?_⟩
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmN : N₀ ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_left _ _) hm)
  have h := (hN₀ m hmN).le
  have hcancel : (m : ℝ) ^ (-A) * (m : ℝ) ^ A = 1 := by
    rw [← Real.rpow_add hmR, neg_add_cancel, Real.rpow_zero]
  have hmA : 0 < (m : ℝ) ^ (-A) := Real.rpow_pos_of_pos hmR _
  calc 2 * C * Real.exp (-κ * m)
      = 2 * C * (m : ℝ) ^ (-A) * ((m : ℝ) ^ A * Real.exp (-κ * m)) := by
        rw [show 2 * C * (m : ℝ) ^ (-A) * ((m : ℝ) ^ A * Real.exp (-κ * m))
            = 2 * C * ((m : ℝ) ^ (-A) * (m : ℝ) ^ A) * Real.exp (-κ * m) by ring, hcancel,
          mul_one]
    _ ≤ 2 * C * (m : ℝ) ^ (-A) * (1 / (4 * C)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (m : ℝ) ^ (-A) / 2 := by field_simp; ring

/-- **Column tail** (`col_tail_mass_le` of tao-collatz): for `A > 0` and `P` there is a threshold such that, if `m` is large and
the budget satisfies `s log p ≤ (m+2) log q²`, the probability that the `j`-advance over the first passage and the following `P` steps is `≥ colFrac · m`
is `≤ m^{-A}/2`. We have `s · slopeInv ≤ (m+2) η/(2μ)`, the gap to `colFrac · m` is `≥ (1 - η/(2μ)) m / 4`
(for large `m`), and `fpDistPlus_col_tail` (with `D ≍ m`) gives `≤ 2C e^{-κm}`. -/
theorem col_tail_mass_le (A : ℝ) (_hA : 0 < A) (P : ℕ) :
    ∃ Cthr : ℕ, ∀ m : ℕ, Cthr ≤ m → ∀ s : ℕ,
      (s : ℝ) * Real.log F.p ≤ ((m : ℝ) + 2) * Real.log ((F.q : ℝ) ^ 2) →
      (∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
          ENNReal.ofReal (if F.colFrac * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        ≤ ENNReal.ofReal ((m : ℝ) ^ (-A) / 2) := by
  obtain ⟨c, hc, C, hC, K, hK, hcol⟩ := F.fpDistPlus_col_tail
  have hp : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hLp : 0 < Real.log (F.p : ℝ) := Real.log_pos (by linarith)
  have hq1 : (1 : ℝ) ≤ (F.q : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ F.q := by exact_mod_cast F.q_pos
    nlinarith
  set L : ℝ := Real.log ((F.q : ℝ) ^ 2) / Real.log F.p with hLdef
  have hL0 : 0 ≤ L := div_nonneg (Real.log_nonneg hq1) hLp.le
  have hsl0 : 0 ≤ F.slopeInv := by unfold slopeInv; apply div_nonneg <;> linarith
  set r : ℝ := L * F.slopeInv with hrdef
  have hr1 : r < 1 := F.eta_slopeInv_lt_one
  have hr0 : 0 ≤ r := mul_nonneg hL0 hsl0
  have hcf : F.colFrac = (1 + r) / 2 := rfl
  set δ : ℝ := (1 - r) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set κ : ℝ := c * min (δ / 4) (δ ^ 2 / (16 * (1 + 3 * L))) with hκdef
  have hmin : 0 < min (δ / 4) (δ ^ 2 / (16 * (1 + 3 * L))) := lt_min (by positivity) (by positivity)
  have hκ : 0 < κ := mul_pos hc hmin
  obtain ⟨N, hN⟩ := CT.exp_le_rpow κ hκ A C hC
  refine ⟨max (max N 1) (max ⌈4 * r / δ⌉₊ ⌈4 * K * (1 + (P : ℝ)) / δ⌉₊), ?_⟩
  intro m hm s hs
  have hmN : N ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm1 : 1 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hmA : ⌈4 * r / δ⌉₊ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hmB : ⌈4 * K * (1 + (P : ℝ)) / δ⌉₊ ≤ m :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
  have hm2 : 4 * r / δ ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hmA)
  have hm3 : 4 * K * (1 + (P : ℝ)) / δ ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hmB)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  -- from the budget, `s · slopeInv ≤ (m+2) r`
  have hsL : (s : ℝ) ≤ ((m : ℝ) + 2) * L := by
    rw [hLdef, mul_div_assoc', le_div_iff₀ hLp]; exact hs
  have hsx : (s : ℝ) * F.slopeInv ≤ ((m : ℝ) + 2) * r := by
    rw [hrdef, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hsL hsl0
  set D : ℝ := (F.colFrac * (m : ℝ) - (s : ℝ) * F.slopeInv) / 2 with hDdef
  have hm2' : 4 * r ≤ δ * m := by have h := (div_le_iff₀ hδ).mp hm2; linarith
  have hm3' : 4 * K * (1 + (P : ℝ)) ≤ δ * m := by have h := (div_le_iff₀ hδ).mp hm3; linarith
  have hD : δ * m / 4 ≤ D := by
    rw [hDdef, hcf]
    have : (1 + r) / 2 * (m : ℝ) - ((m : ℝ) + 2) * r = 2 * δ * m / 2 - 2 * r := by
      rw [hδdef]; ring
    nlinarith
  have hDK : K * (1 + (P : ℝ)) ≤ D := by linarith
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hDm : δ * m / 4 ≤ D := hD
  have hmin1 : min (δ / 4) (δ ^ 2 / (16 * (1 + 3 * L))) ≤ δ / 4 := min_le_left _ _
  have hmin2 : min (δ / 4) (δ ^ 2 / (16 * (1 + 3 * L))) ≤ δ ^ 2 / (16 * (1 + 3 * L)) :=
    min_le_right _ _
  have hex1 : Real.exp (-c * D) ≤ Real.exp (-κ * m) := by
    apply Real.exp_le_exp.mpr
    have : κ * m ≤ c * D := by
      rw [hκdef]
      have h1 : min (δ / 4) (δ ^ 2 / (16 * (1 + 3 * L))) * m ≤ δ * m / 4 := by
        nlinarith
      nlinarith
    linarith
  have hex2 : Real.exp (-c * D ^ 2 / (1 + (s : ℝ))) ≤ Real.exp (-κ * m) := by
    apply Real.exp_le_exp.mpr
    have hs1 : 0 < 1 + (s : ℝ) := by linarith
    have hsm : 1 + (s : ℝ) ≤ (m : ℝ) * (1 + 3 * L) := by
      have h3 : ((m : ℝ) + 2) * L ≤ (3 * m) * L :=
        mul_le_mul_of_nonneg_right (by linarith) hL0
      have h4 : (m : ℝ) * (1 + 3 * L) = m + 3 * m * L := by ring
      linarith
    have hD0 : 0 ≤ δ * m / 4 := by positivity
    have hDsq : (δ * m / 4) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hD0 hDm 2
    have hkey : κ * m * (1 + (s : ℝ)) ≤ c * D ^ 2 := by
      have hL3 : 0 < 1 + 3 * L := by linarith
      have h1 : κ * m * (1 + (s : ℝ)) ≤ κ * m * ((m : ℝ) * (1 + 3 * L)) :=
        mul_le_mul_of_nonneg_left hsm (by positivity)
      have h2 : κ * m * ((m : ℝ) * (1 + 3 * L))
          ≤ c * (δ ^ 2 / (16 * (1 + 3 * L))) * m * ((m : ℝ) * (1 + 3 * L)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [hκdef]; exact mul_le_mul_of_nonneg_left hmin2 hc.le
      have h3 : c * (δ ^ 2 / (16 * (1 + 3 * L))) * m * ((m : ℝ) * (1 + 3 * L))
          = c * (δ * m / 4) ^ 2 := by field_simp; ring
      have h4 : c * (δ * m / 4) ^ 2 ≤ c * D ^ 2 := mul_le_mul_of_nonneg_left hDsq hc.le
      linarith
    have : κ * m ≤ c * D ^ 2 / (1 + (s : ℝ)) := by rw [le_div_iff₀ hs1]; exact hkey
    rw [neg_mul, neg_div]; linarith
  set g : ℕ × ℤ → ℝ := Set.indicator {q : ℕ × ℤ | F.colFrac * (m : ℝ) ≤ (q.1 : ℝ)} 1 with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => (FP.indicator_one_mem _ x).1
  have hg1 : ∀ x, g x ≤ 1 := fun x => (FP.indicator_one_mem _ x).2
  -- real bounds
  set g2 : ℕ × ℤ → ℝ :=
    Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) * F.slopeInv|} 1 with hg2
  have hpt : ∀ x, (F.fpDistPlus s P x).toReal * g x ≤ (F.fpDistPlus s P x).toReal * g2 x := by
    intro x
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    by_cases h : x ∈ {q : ℕ × ℤ | F.colFrac * (m : ℝ) ≤ (q.1 : ℝ)}
    · rw [hg, Set.indicator_of_mem h]
      have h' : x ∈ {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) * F.slopeInv|} := by
        simp only [Set.mem_ofPred_eq] at h ⊢
        have : 2 * D = F.colFrac * (m : ℝ) - (s : ℝ) * F.slopeInv := by rw [hDdef]; ring
        rw [this]
        exact le_trans (by linarith) (le_abs_self _)
      rw [hg2, Set.indicator_of_mem h']
    · rw [hg, Set.indicator_of_notMem h]
      exact (FP.indicator_one_mem _ x).1
  have hsumP : Summable fun x => (F.fpDistPlus s P x).toReal :=
    ENNReal.summable_toReal (F.fpDistPlus s P).tsum_coe_ne_top
  have hsum1 : Summable fun x => (F.fpDistPlus s P x).toReal * g x :=
    Summable.of_nonneg_of_le (fun x => mul_nonneg ENNReal.toReal_nonneg (hg0 x))
      (fun x => mul_le_of_le_one_right ENNReal.toReal_nonneg (hg1 x)) hsumP
  have hsum2 : Summable fun x => (F.fpDistPlus s P x).toReal * g2 x :=
    Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (FP.indicator_one_mem _ x).1)
      (fun x => mul_le_of_le_one_right ENNReal.toReal_nonneg (FP.indicator_one_mem _ x).2) hsumP
  have hcolb := hcol s P D hDK
  -- exponential bound
  have hreal : ∑' x : ℕ × ℤ, (F.fpDistPlus s P x).toReal * g x ≤ (m : ℝ) ^ (-A) / 2 := by
    calc ∑' x : ℕ × ℤ, (F.fpDistPlus s P x).toReal * g x
        ≤ ∑' x : ℕ × ℤ, (F.fpDistPlus s P x).toReal * g2 x := hsum1.tsum_le_tsum hpt hsum2
      _ ≤ C * (Real.exp (-c * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-c * D)) := hcolb
      _ ≤ C * (Real.exp (-κ * m) + Real.exp (-κ * m)) :=
          mul_le_mul_of_nonneg_left (add_le_add hex2 hex1) hC.le
      _ = 2 * C * Real.exp (-κ * m) := by ring
      _ ≤ (m : ℝ) ^ (-A) / 2 := hN m hmN
  -- put the left-hand side in `fpDistPlus` form
  have hwalk := F.fpDist_walk_eq_fpDistPlus s (le_refl P) (fun x => ENNReal.ofReal (g x))
  have hLHS : (∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
          ENNReal.ofReal (if F.colFrac * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
            then (1 : ℝ) else 0))
      = ∑' x : ℕ × ℤ, F.fpDistPlus s P x * ENNReal.ofReal (g x) := by
    rw [← hwalk]
    refine tsum_congr fun e => ?_
    congr 1
  clear hwalk
  rw [hLHS, ← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
      (PMF.tsum_mul_ofReal_le_one (F.fpDistPlus s P) g hg1)),
    PMF.toReal_tsum_mul_ofReal _ _ hg0]
  exact ENNReal.ofReal_le_ofReal hreal

end Family

end GGMCollatz
