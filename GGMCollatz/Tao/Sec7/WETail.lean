import GGMCollatz.Tao.Sec7.HoldLocal

/-!
# Tails of the first-passage endpoint (tools for the white exit and the degradation of the weight)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, files `TaoCollatz/Sec7/BlackEdge.lean`
(tail sums of the type of `exp_neg_mul_le_of_large`, `one_sub_rpow_neg_le_exp`, `hasSum_nat_tail_exp`) and
`TaoCollatz/Sec7/FpLocation.lean` (the idea of the first-passage height tails `fpDist_height_tail_*`);
generalized to the GGM family (p, q, r). Modified: the explicit constants and numerical bounds of tao-collatz are not carried over, and the proofs were rebuilt:

* `colTail`: from the column form of Lemma 7.7 (`fpDist_col_le`), the probability that the endpoint column lies
  at least `D ≥ γ₀(1+s)` to the right of the center `s·(p-1)/(2p)` is `≤ 2C' e^{-c₀ D}/(1 - e^{-c₀})` (`c₀ = min(c²γ₀, c)`).
* `fpDist_high_le`: the probability that the height overshoot of the endpoint satisfies `e₂ - s > Y` is at most `Σ_{k ≤ s} P(ℋ₂ > Y + k)`
  (induction on the budget, without going through the renewal measure). `HT_toReal_le`: from the tail of `ℋ` (the case `n = 1` of `hold_tail_bound`),
  `P(ℋ₂ > y) ≤ 3C e^{-c(y - ν)}`.
* `slope_gap`: condition (b) gives `(p-1)/(2p) < log p / log q²` (the center of the endpoint column lies within the top side of the triangle).

Auxiliary declarations are placed in the namespace `GGMCollatz.Family.WE`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

namespace WE

variable (F : Family)

/-! ### Small real-analysis tools -/

/-- `exp(-a m) ≤ η` (for large `m`, `a, η > 0`). -/
theorem exp_neg_mul_le_eventually {a : ℝ} (ha : 0 < a) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → Real.exp (-a * m) ≤ η := by
  refine ⟨⌈Real.log η⁻¹ / a⌉₊, fun m hm => ?_⟩
  have hx : Real.log η⁻¹ / a ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
  have hρm : Real.log η⁻¹ ≤ (m : ℝ) * a := by
    have h := mul_le_mul_of_nonneg_right hx ha.le
    rwa [div_mul_cancel₀ _ ha.ne'] at h
  have hfin : -a * (m : ℝ) ≤ Real.log η := by rw [Real.log_inv] at hρm; nlinarith [hρm]
  calc Real.exp (-a * (m : ℝ)) ≤ Real.exp (Real.log η) := Real.exp_le_exp.mpr hfin
    _ = η := Real.exp_log hη

/-- `exp(-b m) ≤ η m^{-A}` (for large `m`, `b, η > 0`). -/
theorem exp_neg_mul_le_rpow_eventually (A : ℝ) {b : ℝ} (hb : 0 < b) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → Real.exp (-b * m) ≤ η * (m : ℝ) ^ (-A) := by
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero A b hb).comp
    tendsto_natCast_atTop_atTop
  have hev := hlim.eventually (gt_mem_nhds hη)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨M, hM⟩ := hev
  refine ⟨max M 1, fun m hm => ?_⟩
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have h := (hM m (le_trans (le_max_left _ _) hm)).le
  simp only [Function.comp] at h
  have hA : (m : ℝ) ^ A * (m : ℝ) ^ (-A) = 1 := by
    rw [← Real.rpow_add hmpos, add_neg_cancel, Real.rpow_zero]
  have hApos : 0 < (m : ℝ) ^ (-A) := Real.rpow_pos_of_pos hmpos _
  calc Real.exp (-b * m) = ((m : ℝ) ^ A * Real.exp (-b * m)) * (m : ℝ) ^ (-A) := by
        rw [mul_comm ((m : ℝ) ^ A), mul_assoc, hA, mul_one]
    _ ≤ η * (m : ℝ) ^ (-A) := mul_le_mul_of_nonneg_right h hApos.le

/-- `(1-x)^{-A} ≤ e^{2Ax}` (`A ≥ 0`, `0 ≤ x ≤ 1/2`; `one_sub_rpow_neg_le_exp` of tao-collatz). -/
theorem one_sub_rpow_neg_le_exp {A x : ℝ} (hA : 0 ≤ A) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    (1 - x) ^ (-A) ≤ Real.exp (2 * A * x) := by
  have h1x : (0 : ℝ) < 1 - x := by linarith
  rw [Real.rpow_def_of_pos h1x]
  apply Real.exp_le_exp.mpr
  have hlog : -Real.log (1 - x) ≤ 2 * x := by
    have hy : Real.log (1 / (1 - x)) ≤ 1 / (1 - x) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div one_ne_zero (by linarith), Real.log_one, zero_sub] at hy
    have hle : 1 / (1 - x) - 1 ≤ 2 * x := by
      rw [div_sub_one (by linarith)]
      rw [div_le_iff₀ h1x]; nlinarith
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hlog hA]

/-- Summability of geometric tail sums. -/
theorem geom_tail_summable {c : ℝ} (hc : 0 < c) (y : ℝ) :
    Summable (fun j : ℕ => if y ≤ (j : ℝ) then Real.exp (-c * ((j : ℝ) - y)) else 0) := by
  have hr1 : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  refine Summable.of_nonneg_of_le (fun j => by split_ifs <;> positivity) (fun j => ?_)
    ((summable_geometric_of_lt_one (Real.exp_pos (-c)).le hr1).mul_left (Real.exp (c * y)))
  split_ifs
  · refine le_of_eq ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  · positivity

/-- **Geometric tail sum**: `Σ_{j ≥ y} e^{-c(j - y)} ≤ 1/(1 - e^{-c})` (`j ∈ ℕ`, `y ∈ ℝ`). -/
theorem geom_tail_le {c : ℝ} (hc : 0 < c) (y : ℝ) :
    ∑' j : ℕ, (if y ≤ (j : ℝ) then Real.exp (-c * ((j : ℝ) - y)) else 0)
      ≤ 1 / (1 - Real.exp (-c)) := by
  set r := Real.exp (-c) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by rw [hrdef, Real.exp_lt_one_iff]; linarith
  set n₀ : ℕ := ⌈y⌉₊ with hn₀
  set g : ℕ → ℝ := fun j => if n₀ ≤ j then r ^ (j - n₀) else 0 with hgdef
  have hg : HasSum g ((1 - r)⁻¹) := by
    rw [← hasSum_nat_add_iff' n₀]
    have h0 : ∑ i ∈ Finset.range n₀, g i = 0 :=
      Finset.sum_eq_zero (fun i hi => by
        rw [Finset.mem_range] at hi
        simp only [hgdef]
        rw [if_neg (by omega)])
    rw [h0, sub_zero]
    have : (fun n => g (n + n₀)) = fun n => r ^ n := by
      funext n
      simp only [hgdef]
      rw [if_pos (by omega), Nat.add_sub_cancel]
    rw [this]
    exact hasSum_geometric_of_lt_one hr0 hr1
  have hle : ∀ j : ℕ, (if y ≤ (j : ℝ) then Real.exp (-c * ((j : ℝ) - y)) else 0) ≤ g j := by
    intro j
    split_ifs with h
    · have hn : n₀ ≤ j := Nat.ceil_le.mpr h
      simp only [hgdef]
      rw [if_pos hn, hrdef, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hy0 : y ≤ (n₀ : ℝ) := Nat.le_ceil y
      rw [Nat.cast_sub hn]
      nlinarith
    · simp only [hgdef]
      split_ifs <;> positivity
  calc _ ≤ ∑' j, g j := (geom_tail_summable hc y).tsum_le_tsum hle hg.summable
    _ = (1 - r)⁻¹ := hg.tsum_eq
    _ = 1 / (1 - Real.exp (-c)) := (one_div _).symm

/-! ### Tail of the endpoint column -/

/-- The weight satisfies `G_t(cu) ≤ 2e^{-c₀ u}` (`u ≥ γ₀ t > 0`, `c₀ = min(c²γ₀, c)`). -/
theorem Gweight_le_of_ge {c γ₀ t u : ℝ} (hc : 0 < c) (hγ₀ : 0 < γ₀) (ht : 0 < t)
    (hu : γ₀ * t ≤ u) :
    Sec7.Gweight t (c * u) ≤ 2 * Real.exp (-(min (c ^ 2 * γ₀) c) * u) := by
  have hupos : 0 < u := lt_of_lt_of_le (by positivity) hu
  set c₀ := min (c ^ 2 * γ₀) c with hc₀
  have hc₀1 : c₀ ≤ c ^ 2 * γ₀ := min_le_left _ _
  have hc₀2 : c₀ ≤ c := min_le_right _ _
  unfold Sec7.Gweight
  have h1 : Real.exp (-((c * u) ^ 2) / t) ≤ Real.exp (-c₀ * u) := by
    apply Real.exp_le_exp.mpr
    have hq : γ₀ * u ≤ u ^ 2 / t := by
      rw [le_div_iff₀ ht]
      nlinarith
    have : c₀ * u ≤ (c * u) ^ 2 / t := by
      calc c₀ * u ≤ (c ^ 2 * γ₀) * u := mul_le_mul_of_nonneg_right hc₀1 hupos.le
        _ = c ^ 2 * (γ₀ * u) := by ring
        _ ≤ c ^ 2 * (u ^ 2 / t) := mul_le_mul_of_nonneg_left hq (by positivity)
        _ = (c * u) ^ 2 / t := by ring
    rw [neg_div]
    linarith
  have h2 : Real.exp (-|c * u|) ≤ Real.exp (-c₀ * u) := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_pos (by positivity)]
    nlinarith
  linarith

/-- **Tail of the endpoint column**: if `γ₀(1+s) ≤ y - s·slopeInv`, then
`P(e₁ ≥ y) ≤ 2C' e^{-c₀(y - s·slopeInv)}/(1 - e^{-c₀})` (`c₀ = min(c²γ₀, c)`). -/
theorem colTail {c C' : ℝ} (hc : 0 < c) (hC' : 0 < C')
    (hcol : ∀ s j : ℕ, ∑' l : ℤ, (F.fpDist s (j, l)).toReal
        ≤ C' * (Sec7.Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) * F.slopeInv))
                  / Real.sqrt (1 + (s : ℝ))))
    (s : ℕ) {y γ₀ : ℝ} (hγ₀ : 0 < γ₀) (hy : γ₀ * (1 + (s : ℝ)) ≤ y - s * F.slopeInv) :
    ∑' e : ℕ × ℤ, (F.fpDist s e).toReal * (if y ≤ (e.1 : ℝ) then 1 else 0)
      ≤ 2 * C' * Real.exp (-(min (c ^ 2 * γ₀) c) * (y - s * F.slopeInv))
          / (1 - Real.exp (-(min (c ^ 2 * γ₀) c))) := by
  set c₀ := min (c ^ 2 * γ₀) c with hc₀def
  set x₀ := (s : ℝ) * F.slopeInv with hx₀
  set D := y - x₀ with hDdef
  have hs1 : (0 : ℝ) < 1 + s := by positivity
  have hc₀ : 0 < c₀ := lt_min (by positivity) hc
  set f : ℕ × ℤ → ℝ := fun e => (F.fpDist s e).toReal * (if y ≤ (e.1 : ℝ) then 1 else 0)
    with hfdef
  have hf0 : 0 ≤ f := fun e => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num)
  have hfle : ∀ e, f e ≤ (F.fpDist s e).toReal := fun e =>
    mul_le_of_le_one_right ENNReal.toReal_nonneg (by split_ifs <;> norm_num)
  have hfp : Summable fun e => (F.fpDist s e).toReal :=
    ENNReal.summable_toReal (F.fpDist s).tsum_coe_ne_top
  have hfs : Summable f := Summable.of_nonneg_of_le hf0 hfle hfp
  obtain ⟨hfib, hcolS⟩ := (summable_prod_of_nonneg hf0).mp hfs
  rw [hfs.tsum_prod' hfib]
  set g : ℕ → ℝ := fun j => 2 * C' * Real.exp (-c₀ * D) *
      (if y ≤ (j : ℝ) then Real.exp (-c₀ * ((j : ℝ) - y)) else 0) with hgdef
  have hcolle : ∀ j : ℕ, ∑' l : ℤ, f (j, l) ≤ g j := by
    intro j
    have hfj : (fun l : ℤ => f (j, l))
        = fun l => (F.fpDist s (j, l)).toReal * (if y ≤ (j : ℝ) then 1 else 0) := rfl
    rw [hfj, tsum_mul_right]
    by_cases hj : y ≤ (j : ℝ)
    · rw [if_pos hj, mul_one]
      simp only [hgdef, if_pos hj]
      refine le_trans (hcol s j) ?_
      have hu : γ₀ * (1 + (s : ℝ)) ≤ (j : ℝ) - x₀ := by linarith
      have hG := Gweight_le_of_ge hc hγ₀ hs1 hu
      have hsq : 1 ≤ Real.sqrt (1 + (s : ℝ)) := by
        rw [Real.one_le_sqrt]; linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
      have hGnn : 0 ≤ Sec7.Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - x₀)) :=
        (Sec7.Gweight_pos _ _).le
      have hdiv : Sec7.Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - x₀)) / Real.sqrt (1 + (s : ℝ))
          ≤ Sec7.Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - x₀)) := div_le_self hGnn hsq
      have hsplit : Real.exp (-c₀ * ((j : ℝ) - x₀))
          = Real.exp (-c₀ * D) * Real.exp (-c₀ * ((j : ℝ) - y)) := by
        rw [← Real.exp_add]; congr 1; rw [hDdef]; ring
      calc C' * (Sec7.Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - x₀)) / Real.sqrt (1 + (s : ℝ)))
          ≤ C' * (2 * Real.exp (-c₀ * ((j : ℝ) - x₀))) :=
            mul_le_mul_of_nonneg_left (hdiv.trans hG) hC'.le
        _ = 2 * C' * Real.exp (-c₀ * D) * Real.exp (-c₀ * ((j : ℝ) - y)) := by
            rw [hsplit]; ring
    · rw [if_neg hj, mul_zero]
      simp only [hgdef, if_neg hj, mul_zero, le_refl]
  have hgs : Summable g := (geom_tail_summable hc₀ y).mul_left _
  calc ∑' j : ℕ, ∑' l : ℤ, f (j, l) ≤ ∑' j, g j := hcolS.tsum_le_tsum hcolle hgs
    _ = 2 * C' * Real.exp (-c₀ * D) *
          ∑' j : ℕ, (if y ≤ (j : ℝ) then Real.exp (-c₀ * ((j : ℝ) - y)) else 0) := tsum_mul_left
    _ ≤ 2 * C' * Real.exp (-c₀ * D) * (1 / (1 - Real.exp (-c₀))) :=
        mul_le_mul_of_nonneg_left (geom_tail_le hc₀ y) (by positivity)
    _ = 2 * C' * Real.exp (-c₀ * D) / (1 - Real.exp (-c₀)) := by rw [mul_one_div]

/-! ### Tail of the height overshoot of the endpoint -/

/-- The one-step sum of `ℋ` is `ℋ` itself. -/
theorem holdSum_one : F.holdSum 1 = F.hold := by
  unfold holdSum
  rw [show F.hold.iid 1 = F.hold.bind fun a => (F.hold.iid 0).map (Fin.cons a) from rfl,
    PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure F.hold]
  congr 1
  funext a
  rw [show F.hold.iid 0 = PMF.pure (fun i : Fin 0 => i.elim0) from rfl, PMF.pure_map,
    PMF.pure_map]
  congr 1
  ext <;> simp

/-- `P(ℋ₂ > y)` (in `ℝ≥0∞`). -/
noncomputable def HT (y : ℤ) : ℝ≥0∞ := ∑' d : ℕ × ℤ, F.hold d * (if y < d.2 then 1 else 0)

theorem HT_le_one (y : ℤ) : HT F y ≤ 1 := by
  calc HT F y ≤ ∑' d : ℕ × ℤ, F.hold d * 1 :=
        ENNReal.tsum_le_tsum fun d => mul_le_mul_right (by split_ifs <;> simp) _
    _ = 1 := by rw [tsum_congr fun d => mul_one (F.hold d), F.hold.tsum_coe]

/-- **Height overshoot** (induction on the budget): `P(e₂ > s + Y) ≤ Σ_{k ≤ s} P(ℋ₂ > Y + k)`. -/
theorem fpDist_high_le (Y : ℕ) : ∀ s : ℕ,
    ∑' e : ℕ × ℤ, F.fpDist s e * (if (s : ℤ) + Y < e.2 then 1 else 0)
      ≤ ∑ k ∈ Finset.range (s + 1), HT F ((Y : ℤ) + k) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    rw [fpDist, PMF.tsum_bind_mul]
    set b := ∑ k ∈ Finset.range s, HT F ((Y : ℤ) + k) with hbdef
    have hper : ∀ d : ℕ × ℤ,
        F.hold d * ∑' e, (if _h : d.2 ≤ 0 ∨ (s : ℤ) < d.2 then PMF.pure d
            else (F.fpDist (s - d.2.toNat)).map fun e => (d.1 + e.1, d.2 + e.2)) e
            * (if (s : ℤ) + Y < e.2 then 1 else 0)
          ≤ F.hold d * ((if (s : ℤ) + Y < d.2 then 1 else 0) + b) := by
      intro d
      by_cases h0 : F.hold d = 0
      · rw [h0, zero_mul, zero_mul]
      · have hd2 := F.hold_support_snd_ge d (by rwa [PMF.mem_support_iff])
        refine mul_le_mul_right ?_ _
        by_cases hcond : d.2 ≤ 0 ∨ (s : ℤ) < d.2
        · rw [dif_pos hcond]
          rw [tsum_eq_single d (fun e he => by rw [PMF.pure_apply, if_neg he, zero_mul]),
            PMF.pure_apply, if_pos rfl, one_mul]
          exact le_self_add
        · rw [dif_neg hcond]
          push Not at hcond
          rw [PMF.tsum_map_mul]
          have hIH := IH (s - d.2.toNat) (by omega)
          have hcast : ((s - d.2.toNat : ℕ) : ℤ) = (s : ℤ) - d.2 := by omega
          calc ∑' e, F.fpDist (s - d.2.toNat) e
                * (if (s : ℤ) + Y < (d.1 + e.1, d.2 + e.2).2 then 1 else 0)
              = ∑' e, F.fpDist (s - d.2.toNat) e
                * (if ((s - d.2.toNat : ℕ) : ℤ) + Y < e.2 then 1 else 0) := by
                refine tsum_congr fun e => ?_
                congr 1
                rw [hcast]
                exact if_congr (by constructor <;> intro h <;> dsimp only at h ⊢ <;> omega)
                  rfl rfl
            _ ≤ ∑ k ∈ Finset.range (s - d.2.toNat + 1), HT F ((Y : ℤ) + k) := hIH
            _ ≤ b := Finset.sum_le_sum_of_subset
                (Finset.range_subset_range.mpr (by omega))
            _ ≤ _ := le_add_self
    calc ∑' d, F.hold d * ∑' e, _ ≤ ∑' d, F.hold d * ((if (s : ℤ) + Y < d.2 then 1 else 0) + b) :=
          ENNReal.tsum_le_tsum hper
      _ = HT F ((Y : ℤ) + s) + b := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, F.hold.tsum_coe, one_mul, HT]
          congr 1
          refine tsum_congr fun d => ?_
          congr 2
          exact propext (by constructor <;> intro h <;> omega)
      _ = ∑ k ∈ Finset.range (s + 1), HT F ((Y : ℤ) + k) := by
          rw [Finset.sum_range_succ, add_comm]

/-- `G_2(x) ≤ 3e^{-x}` (`x ≥ 0`). -/
theorem Gweight_two_le {x : ℝ} (hx : 0 ≤ x) : Sec7.Gweight (1 + 1) x ≤ 3 * Real.exp (-x) := by
  unfold Sec7.Gweight
  have he : Real.exp (1 / 2) ≤ 2 := by
    have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h2 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    nlinarith [Real.exp_pos (1 / 2)]
  have h1 : Real.exp (-(x ^ 2) / (1 + 1)) ≤ 2 * Real.exp (-x) := by
    calc Real.exp (-(x ^ 2) / (1 + 1)) ≤ Real.exp (1 / 2 + -x) := by
          apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg (x - 1)]
      _ = Real.exp (1 / 2) * Real.exp (-x) := Real.exp_add _ _
      _ ≤ 2 * Real.exp (-x) := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
  rw [abs_of_nonneg hx]
  linarith

/-- **Height tail of `ℋ`**: with the constants `c, C` of `hold_tail_bound`, if `ν ≤ y` then
`P(ℋ₂ > y) ≤ 3C e^{-c(y - ν)}`. -/
theorem HT_toReal_le {ch Ch : ℝ} (hch : 0 < ch)
    (htail : ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' d : ℕ × ℤ,
          if lam ≤ ‖(((d.1 : ℝ) - F.holdMean1 * n, (d.2 : ℝ) - F.holdMean2 * n) : ℝ × ℝ)‖
          then ((F.holdSum n) d).toReal else 0)
        ≤ Ch * Sec7.Gweight (1 + n) (ch * lam))
    {y : ℤ} (hy : F.holdMean2 ≤ (y : ℝ)) :
    (HT F y).toReal ≤ 3 * Ch * Real.exp (-ch * ((y : ℝ) - F.holdMean2)) := by
  set lam := (y : ℝ) - F.holdMean2 with hlam
  have hlam0 : 0 ≤ lam := by linarith
  have h1 := htail 1 lam hlam0
  rw [holdSum_one F] at h1
  simp only [Nat.cast_one, mul_one] at h1
  have hHT : (HT F y).toReal = ∑' d : ℕ × ℤ, (F.hold d).toReal * (if y < d.2 then 1 else 0) := by
    unfold HT
    rw [ENNReal.tsum_toReal_eq (fun d => ENNReal.mul_ne_top (F.hold.apply_ne_top d)
      (by split_ifs <;> simp))]
    refine tsum_congr fun d => ?_
    rw [ENNReal.toReal_mul]
    split_ifs <;> simp
  have hpt : ∀ d : ℕ × ℤ, (F.hold d).toReal * (if y < d.2 then 1 else 0)
      ≤ if lam ≤ ‖(((d.1 : ℝ) - F.holdMean1, (d.2 : ℝ) - F.holdMean2) : ℝ × ℝ)‖
        then (F.hold d).toReal else 0 := by
    intro d
    by_cases hd : y < d.2
    · rw [if_pos hd, mul_one, if_pos]
      have hyd : (y : ℝ) < d.2 := by exact_mod_cast hd
      rw [Prod.norm_def]
      refine le_trans ?_ (le_max_right _ _)
      rw [Real.norm_eq_abs]
      exact le_trans (by linarith) (le_abs_self _)
    · rw [if_neg hd, mul_zero]
      split_ifs <;> simp
  have hs1 : Summable fun d : ℕ × ℤ => (F.hold d).toReal * (if y < d.2 then 1 else 0) :=
    Summable.of_nonneg_of_le (fun d => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> simp))
      (fun d => mul_le_of_le_one_right ENNReal.toReal_nonneg (by split_ifs <;> simp))
      F.hold_summable_toReal
  have hs2 : Summable fun d : ℕ × ℤ =>
      if lam ≤ ‖(((d.1 : ℝ) - F.holdMean1, (d.2 : ℝ) - F.holdMean2) : ℝ × ℝ)‖
        then (F.hold d).toReal else 0 :=
    Summable.of_nonneg_of_le (fun d => by split_ifs <;> simp)
      (fun d => by split_ifs <;> simp) F.hold_summable_toReal
  rw [hHT]
  calc _ ≤ _ := hs1.tsum_le_tsum hpt hs2
    _ ≤ Ch * Sec7.Gweight (1 + 1) (ch * lam) := h1
    _ ≤ Ch * (3 * Real.exp (-(ch * lam))) := by
        have hCh : 0 ≤ Ch := by
          have := le_trans (tsum_nonneg (fun d => by split_ifs <;> simp)) h1
          have hG := Sec7.Gweight_pos (1 + 1) (ch * lam)
          by_contra hneg
          push Not at hneg
          nlinarith
        exact mul_le_mul_of_nonneg_left (Gweight_two_le (by positivity)) hCh
    _ = 3 * Ch * Real.exp (-ch * lam) := by ring_nf

/-- **Tail of the height overshoot** (real form): if `ν ≤ Y` then `P(e₂ > s + Y) ≤ 3C e^{-c(Y - ν)}/(1 - e^{-c})`. -/
theorem fpDist_high_toReal_le {ch Ch : ℝ} (hch : 0 < ch)
    (htail : ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' d : ℕ × ℤ,
          if lam ≤ ‖(((d.1 : ℝ) - F.holdMean1 * n, (d.2 : ℝ) - F.holdMean2 * n) : ℝ × ℝ)‖
          then ((F.holdSum n) d).toReal else 0)
        ≤ Ch * Sec7.Gweight (1 + n) (ch * lam))
    (Y : ℕ) (hY : F.holdMean2 ≤ (Y : ℝ)) (s : ℕ) :
    ∑' e : ℕ × ℤ, (F.fpDist s e).toReal * (if (s : ℤ) + Y < e.2 then 1 else 0)
      ≤ 3 * Ch * Real.exp (-ch * ((Y : ℝ) - F.holdMean2)) / (1 - Real.exp (-ch)) := by
  have hr0 : 0 ≤ Real.exp (-ch) := (Real.exp_pos _).le
  have hr1 : Real.exp (-ch) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hconv : ∑' e : ℕ × ℤ, (F.fpDist s e).toReal * (if (s : ℤ) + Y < e.2 then 1 else 0)
      = (∑' e : ℕ × ℤ, F.fpDist s e * (if (s : ℤ) + Y < e.2 then 1 else 0)).toReal := by
    rw [ENNReal.tsum_toReal_eq (fun e => ENNReal.mul_ne_top ((F.fpDist s).apply_ne_top e)
      (by split_ifs <;> simp))]
    refine tsum_congr fun e => ?_
    rw [ENNReal.toReal_mul]
    split_ifs <;> simp
  have hfin : ∀ k ∈ Finset.range (s + 1), HT F ((Y : ℤ) + k) ≠ ⊤ :=
    fun k _ => ne_top_of_le_ne_top ENNReal.one_ne_top (HT_le_one F _)
  rw [hconv]
  calc _ ≤ (∑ k ∈ Finset.range (s + 1), HT F ((Y : ℤ) + k)).toReal :=
        ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr hfin) (fpDist_high_le F Y s)
    _ = ∑ k ∈ Finset.range (s + 1), (HT F ((Y : ℤ) + k)).toReal := ENNReal.toReal_sum hfin
    _ ≤ ∑ k ∈ Finset.range (s + 1),
          3 * Ch * Real.exp (-ch * ((Y : ℝ) - F.holdMean2)) * Real.exp (-ch) ^ k := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hyk : F.holdMean2 ≤ (((Y : ℤ) + k : ℤ) : ℝ) := by
          push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        refine le_trans (HT_toReal_le F hch htail hyk) (le_of_eq ?_)
        have hsplit : Real.exp (-ch * ((((Y : ℤ) + k : ℤ) : ℝ) - F.holdMean2))
            = Real.exp (-ch * ((Y : ℝ) - F.holdMean2)) * Real.exp (-ch) ^ k := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
        rw [hsplit]; ring
    _ = 3 * Ch * Real.exp (-ch * ((Y : ℝ) - F.holdMean2)) *
          ∑ k ∈ Finset.range (s + 1), Real.exp (-ch) ^ k := by rw [Finset.mul_sum]
    _ ≤ 3 * Ch * Real.exp (-ch * ((Y : ℝ) - F.holdMean2)) * (1 - Real.exp (-ch))⁻¹ := by
        have hCh : 0 ≤ Ch := by
          have h1 := htail 0 0 le_rfl
          have := le_trans (tsum_nonneg (fun d => by split_ifs <;> simp)) h1
          have hG := Sec7.Gweight_pos (1 + ((0 : ℕ) : ℝ)) (ch * 0)
          by_contra hneg
          push Not at hneg
          nlinarith
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← tsum_geometric_of_lt_one hr0 hr1]
        exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _
          (fun k _ => pow_nonneg hr0 k)
    _ = 3 * Ch * Real.exp (-ch * ((Y : ℝ) - F.holdMean2)) / (1 - Real.exp (-ch)) := by
        rw [div_eq_mul_inv]

/-! ### Condition (b) and the slope -/

theorem log_p_pos : 0 < Real.log (F.p : ℝ) := by
  apply Real.log_pos
  have : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  linarith

theorem log_q_sq_pos : 0 < Real.log ((F.q : ℝ) ^ 2) := by
  apply Real.log_pos
  have : (2 : ℝ) ≤ F.q := by exact_mod_cast F.two_le_q
  nlinarith

theorem slopeInv_nonneg : 0 ≤ F.slopeInv := by
  unfold slopeInv
  have : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  apply div_nonneg <;> linarith

theorem slopeInv_le_half : F.slopeInv ≤ 1 / 2 := by
  unfold slopeInv
  have : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- **Slope gap** (condition (b)): `(p-1)/(2p) < log p / log q²`. -/
theorem slope_gap : F.slopeInv < Real.log (F.p : ℝ) / Real.log ((F.q : ℝ) ^ 2) := by
  have hp : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hp0 : (0 : ℝ) < F.p := by linarith
  have hq0 : (0 : ℝ) < F.q := by
    have : (2 : ℝ) ≤ F.q := by exact_mod_cast F.two_le_q
    linarith
  have hlp := log_p_pos F
  have hlq := log_q_sq_pos F
  have hsub := F.subcritical
  have hlog : Real.log (F.q : ℝ) < ((F.p : ℝ) / ((F.p : ℝ) - 1)) * Real.log (F.p : ℝ) := by
    rw [← Real.log_rpow hp0]
    exact Real.log_lt_log hq0 hsub
  have hlq2 : Real.log ((F.q : ℝ) ^ 2) = 2 * Real.log (F.q : ℝ) := by
    rw [Real.log_pow]; push_cast; ring
  unfold slopeInv
  rw [div_lt_div_iff₀ (by linarith) hlq, hlq2]
  have hp1 : (0 : ℝ) < (F.p : ℝ) - 1 := by linarith
  have := mul_lt_mul_of_pos_left hlog hp1
  rw [show ((F.p : ℝ) - 1) * ((F.p : ℝ) / ((F.p : ℝ) - 1) * Real.log (F.p : ℝ))
      = (F.p : ℝ) * Real.log (F.p : ℝ) by field_simp] at this
  nlinarith

end WE

end Family

end GGMCollatz
