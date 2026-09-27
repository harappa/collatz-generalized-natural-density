import GGMCollatz.Tao.Sec6.Events

/-!
# Mixing between adjacent levels (assembly of GGM §5 Step 1)

Derived from `TaoCollatz/Sec6/MixingMain.lean` (`osc_mainHigh_bound`), `TaoCollatz/Sec6/MixingError.lean`
(`prob_not_globalGood_le`, `error_l1_high_bound`) and `TaoCollatz/Sec6/MixingFromDecay.lean`
(`osc_syracZ_high_regime`) of gotrevor/tao-collatz (Apache-2.0), commit 15efca2; generalized to the GGM
family (p, q, r). No explicit constants are kept (existence only).

**Adjacent levels suffice**: the telescoping of the oscillation (`FromDecay.lean`) only uses
`Osc_{n-1,n}`, so the high frequencies are just those with `q ∤ ξ`. The step in GGM §5 Step 1 "since
`q ∤ ξ`, `q ∤ ξ' = ξ p^{-M}`" is correct in this case (for general `γn ≤ m < n` one needs the descent of the
`q`-adic valuation of `ξ`; tao-collatz's `head_uniform_highFreq`).

* `prob_not_globalGood_le`: `P(¬globalGood) ≤ N p e^{-K_c log p} + N e^{-t K_w}`.
* `osc_piece_le`: oscillation of one piece `≤ D √(q^N p^{-l})` (the base factor via Lemma 6.9 of the paper).
* `osc_step_bound`: **Proposition 5.1 ⇒** for all `B > 0`, `Osc_{N-1,N}(𝒮_N) ≤ C N^{-B}` (`N ≥ N₀`).
-/

open scoped BigOperators ENNReal

namespace GGMCollatz

namespace Mix

/-- If `(2/c)² ≤ x` then `log x ≤ c x`. -/
theorem log_le_mul_self {c x : ℝ} (hc : 0 < c) (hx : (2 / c) ^ 2 ≤ x) : Real.log x ≤ c * x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hsq : 2 / c ≤ Real.sqrt x := by
    rw [show 2 / c = Real.sqrt ((2 / c) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt hx
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx0.le]; ring
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs0
  have h2 : 2 ≤ c * Real.sqrt x := by
    have := mul_le_mul_of_nonneg_left hsq hc.le
    rwa [mul_div_cancel₀ _ hc.ne'] at this
  have hxx : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx0.le).symm
  rw [hlog]
  calc 2 * Real.log (Real.sqrt x) ≤ 2 * Real.sqrt x := by linarith
    _ ≤ c * Real.sqrt x * Real.sqrt x := by nlinarith
    _ = c * x := by rw [mul_assoc, ← hxx]

/-- If `1/(aε) ≤ L` then `e^{-aL} ≤ ε`. -/
theorem exp_neg_le_of_ge {a ε L : ℝ} (ha : 0 < a) (hε : 0 < ε) (hL : 1 / (a * ε) ≤ L) :
    Real.exp (-(a * L)) ≤ ε := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have haL : 1 / ε ≤ a * L := by
    rw [div_le_iff₀ (by positivity)] at hL
    rw [div_le_iff₀ hε]; nlinarith
  have hexp : 1 + a * L ≤ Real.exp (a * L) := by linarith [Real.add_one_le_exp (a * L)]
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hε]
  have : 1 / ε < 1 + a * L := by linarith
  rw [one_div] at this
  linarith

end Mix

namespace Family

variable (F : Family)

/-! ### Constants: `θ = log_p q < s < μ = p/(p-1)` -/

theorem log_p_pos_mix : 0 < Real.log (F.p : ℝ) := Real.log_pos (by exact_mod_cast F.one_lt_p)

theorem pCast_pos : (0 : ℝ) < (F.p : ℝ) := by exact_mod_cast F.p_pos

theorem qCast_pos : (0 : ℝ) < (F.q : ℝ) := by exact_mod_cast F.q_pos

/-- `θ = log_p q`. -/
noncomputable def thetaMix : ℝ := Real.log F.q / Real.log F.p

/-- `μ = p/(p-1)` (the mean of `G(μ)`). -/
noncomputable def muMix : ℝ := (F.p : ℝ) / ((F.p : ℝ) - 1)

theorem one_lt_thetaMix : 1 < F.thetaMix := by
  unfold thetaMix
  rw [one_lt_div F.log_p_pos_mix]
  exact Real.log_lt_log F.pCast_pos (by exact_mod_cast F.p_lt_q)

/-- Condition (b) `q < p^{p/(p-1)}` is `θ < μ`. -/
theorem thetaMix_lt_muMix : F.thetaMix < F.muMix := by
  have h := F.subcritical
  have hq : Real.log F.q < Real.log ((F.p : ℝ) ^ ((F.p : ℝ) / ((F.p : ℝ) - 1))) :=
    Real.log_lt_log F.qCast_pos h
  rw [Real.log_rpow F.pCast_pos] at hq
  unfold thetaMix muMix
  rw [div_lt_iff₀ F.log_p_pos_mix]
  linarith

/-- The slope of the window `s = (θ + μ)/2`. -/
noncomputable def sMix : ℝ := (F.thetaMix + F.muMix) / 2

theorem thetaMix_lt_sMix : F.thetaMix < F.sMix := by
  unfold sMix; linarith [F.thetaMix_lt_muMix]

theorem sMix_lt_muMix : F.sMix < F.muMix := by
  unfold sMix; linarith [F.thetaMix_lt_muMix]

theorem sMix_pos : 0 < F.sMix := by linarith [F.one_lt_thetaMix, F.thetaMix_lt_sMix]

theorem p_rpow_eq_exp_mix (x : ℝ) : (F.p : ℝ) ^ x = Real.exp (x * Real.log F.p) := by
  rw [Real.rpow_def_of_pos F.pCast_pos, mul_comm]

theorem q_pow_eq_exp_mix (N : ℕ) : (F.q : ℝ) ^ N = Real.exp (N * F.thetaMix * Real.log F.p) := by
  have h : (N : ℝ) * F.thetaMix * Real.log F.p = N * Real.log F.q := by
    unfold thetaMix; field_simp [F.log_p_pos_mix.ne']
  rw [h, Real.exp_nat_mul, Real.exp_log F.qCast_pos]

theorem q_lt_p_rpow_sMix : (F.q : ℝ) < (F.p : ℝ) ^ F.sMix := by
  rw [F.p_rpow_eq_exp_mix]
  have h : Real.log F.q < F.sMix * Real.log F.p := by
    have := F.thetaMix_lt_sMix
    unfold thetaMix at this
    rwa [div_lt_iff₀ F.log_p_pos_mix] at this
  calc (F.q : ℝ) = Real.exp (Real.log F.q) := (Real.exp_log F.qCast_pos).symm
    _ < _ := Real.exp_lt_exp.mpr h

/-! ### The probability of the error -/

open Classical in
/-- **The probability of the exceptional event** (counterpart of `P(Ē_n)` in GGM §5 Step 1). -/
theorem prob_not_globalGood_le (N : ℕ) (s t Kc Kw : ℝ) (ht : 0 ≤ t)
    (hmgf : ∑' a, geomP F.p a * ENNReal.ofReal (Real.exp (t * (s - a))) ≤ 1) (hKc : 0 ≤ Kc) :
    ∑' v : Fin N → ℕ × ℕ, (if globalGood N s Kc Kw v then 0
        else (((stepLaw F.p).iid N) v).toReal)
      ≤ N * ((F.p : ℝ) * Real.exp (-(Kc * Real.log F.p))) + N * Real.exp (-(t * Kw)) := by
  classical
  set P := (stepLaw F.p).iid N with hPdef
  -- pointwise union bound (`ℝ≥0∞`)
  have hpt : ∀ v : Fin N → ℕ × ℕ,
      P v * (if globalGood N s Kc Kw v then 0 else 1)
        ≤ ∑ i : Fin N, P v * (if Kc < ((v i).1 : ℝ) then 1 else 0)
          + ∑ r ∈ Finset.Icc 1 N,
              P v * (if (sufSum (fun i => (v i).1) r : ℝ) ≤ s * r - Kw then 1 else 0) := by
    intro v
    by_cases hg : globalGood N s Kc Kw v
    · rw [if_pos hg, mul_zero]; exact bot_le
    · rw [if_neg hg, mul_one]
      unfold globalGood at hg
      rw [not_and_or] at hg
      rcases hg with h1 | h2
      · push Not at h1
        obtain ⟨i, hi⟩ := h1
        calc P v = P v * (if Kc < ((v i).1 : ℝ) then 1 else 0) := by rw [if_pos hi, mul_one]
          _ ≤ ∑ i : Fin N, P v * (if Kc < ((v i).1 : ℝ) then 1 else 0) :=
            Finset.single_le_sum (f := fun i => P v * (if Kc < ((v i).1 : ℝ) then 1 else 0))
              (fun _ _ => bot_le) (Finset.mem_univ i)
          _ ≤ _ := le_self_add
      · push Not at h2
        obtain ⟨r, hr1, hrN, hr⟩ := h2
        calc P v = P v * (if (sufSum (fun i => (v i).1) r : ℝ) ≤ s * r - Kw then 1 else 0) := by
              rw [if_pos hr, mul_one]
          _ ≤ ∑ r ∈ Finset.Icc 1 N,
                P v * (if (sufSum (fun i => (v i).1) r : ℝ) ≤ s * r - Kw then 1 else 0) :=
            Finset.single_le_sum
              (f := fun r => P v * (if (sufSum (fun i => (v i).1) r : ℝ) ≤ s * r - Kw then 1 else 0))
              (fun _ _ => bot_le) (Finset.mem_Icc.mpr ⟨hr1, hrN⟩)
          _ ≤ _ := le_add_self
  set x₁ : ℝ := (F.p : ℝ) * Real.exp (-(Kc * Real.log F.p)) with hx₁
  set x₂ : ℝ := Real.exp (-(t * Kw)) with hx₂
  have hx₁0 : 0 ≤ x₁ := by rw [hx₁]; positivity
  have hx₂0 : 0 ≤ x₂ := by rw [hx₂]; positivity
  have hENN : ∑' v, P v * (if globalGood N s Kc Kw v then 0 else 1)
      ≤ ENNReal.ofReal (N * x₁ + N * x₂) := by
    calc ∑' v, P v * (if globalGood N s Kc Kw v then 0 else 1)
        ≤ ∑' v, (∑ i : Fin N, P v * (if Kc < ((v i).1 : ℝ) then 1 else 0)
          + ∑ r ∈ Finset.Icc 1 N,
              P v * (if (sufSum (fun i => (v i).1) r : ℝ) ≤ s * r - Kw then 1 else 0)) :=
          ENNReal.tsum_le_tsum hpt
      _ = ∑ i : Fin N, ∑' v, P v * (if Kc < ((v i).1 : ℝ) then 1 else 0)
          + ∑ r ∈ Finset.Icc 1 N, ∑' v,
              P v * (if (sufSum (fun i => (v i).1) r : ℝ) ≤ s * r - Kw then 1 else 0) := by
          rw [ENNReal.tsum_add, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
            Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      _ ≤ ∑ _i : Fin N, ENNReal.ofReal x₁ + ∑ _r ∈ Finset.Icc 1 N, ENNReal.ofReal x₂ := by
          gcongr with i _ r hr
          · exact F.coord_upper_tail N i Kc hKc
          · exact F.sufSum_lower_tail s t ht hmgf N r (Finset.mem_Icc.mp hr).2 Kw
      _ = (N : ℝ≥0∞) * ENNReal.ofReal x₁ + (N : ℝ≥0∞) * ENNReal.ofReal x₂ := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, nsmul_eq_mul]
      _ = ENNReal.ofReal (N * x₁ + N * x₂) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_mul (Nat.cast_nonneg N),
            ENNReal.ofReal_natCast]
  have hconv : ∑' v : Fin N → ℕ × ℕ, (if globalGood N s Kc Kw v then 0 else (P v).toReal)
      = (∑' v, P v * (if globalGood N s Kc Kw v then 0 else 1)).toReal := by
    rw [ENNReal.tsum_toReal_eq (fun v => ENNReal.mul_ne_top (P.apply_ne_top v)
      (by split_ifs <;> simp))]
    refine tsum_congr (fun v => ?_)
    split_ifs <;> simp
  rw [hconv]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hENN

/-! ### The oscillation of one piece -/

/-- A high frequency (`q ∤ ξ`) stays high after multiplication by a unit and descent to level `j ≥ 1`. -/
theorem not_dvd_val_unit_castHom {j P : ℕ} (hj : 1 ≤ j) (l : ℕ) (ξ : ZMod (F.q ^ (j + P)))
    (hξ : ¬ F.q ∣ ξ.val) :
    ¬ F.q ∣ ((((F.p : ZMod (F.q ^ j))⁻¹) ^ l
      * ZMod.castHom (pow_dvd_pow F.q (Nat.le_add_right j P)) (ZMod (F.q ^ j)) ξ).val) := by
  intro hdvd
  apply hξ
  have hqj : F.q ∣ F.q ^ j := dvd_pow_self F.q (by omega)
  have hqjP : F.q ∣ F.q ^ (j + P) := dvd_pow_self F.q (by omega)
  -- `q ∣ z.val ↔ z ↦ 0 (mod q)`
  have key : ∀ (M : ℕ) [NeZero M] (h : F.q ∣ M) (z : ZMod M),
      F.q ∣ z.val ↔ ZMod.castHom h (ZMod F.q) z = 0 := by
    intro M _ h z
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  rw [key _ hqj, map_mul, map_pow] at hdvd
  rw [key _ hqjP]
  have hcomp : ZMod.castHom hqj (ZMod F.q)
      (ZMod.castHom (pow_dvd_pow F.q (Nat.le_add_right j P)) (ZMod (F.q ^ j)) ξ)
      = ZMod.castHom hqjP (ZMod F.q) ξ := by
    exact congrArg (fun f : ZMod (F.q ^ (j + P)) →+* ZMod F.q => f ξ)
      (ZMod.castHom_comp hqj (pow_dvd_pow F.q (Nat.le_add_right j P)))
  rw [hcomp] at hdvd
  have hu0 : IsUnit ((F.p : ZMod (F.q ^ j))⁻¹) :=
    IsUnit.of_mul_eq_one _ (F.inv_mul_p_zmod j)
  have hu : IsUnit (ZMod.castHom hqj (ZMod F.q) ((F.p : ZMod (F.q ^ j))⁻¹)) :=
    hu0.map _
  exact (hu.pow l).mul_right_eq_zero.mp hdvd

open Classical in
/-- **The oscillation of one piece** (GGM §5 Step 1): under a uniform decay `D` of the head (on the high
frequencies `q ∤ ξ`) and the budget, `Osc_{N-1}(g_{k,l}) ≤ D √(q^N p^{-l})`. -/
theorem osc_piece_le (N k l : ℕ) (hkN : k < N) (T s Kw : ℝ) (hs0 : 0 ≤ s)
    (hρ : (F.q : ℝ) < (F.p : ℝ) ^ s)
    (hbudget : 2 * (F.rBound : ℝ) * (F.p : ℝ) ^ ((l : ℝ) + Kw)
      < (1 - (F.q : ℝ) / (F.p : ℝ) ^ s) * (F.q : ℝ) ^ N)
    (D : ℝ) (hD : 0 ≤ D)
    (hunif : ∀ ξ : ZMod (F.q ^ (N - 1 - k + (k + 1))), ¬ F.q ∣ ξ.val →
      ‖((stepLaw F.p).iid (N - 1 - k)).cexpect (fun vh => ZMod.stdAddChar
          (-(((F.q : ZMod (F.q ^ (N - 1 - k + (k + 1)))) ^ (k + 1)
            * F.roff (N - 1 - k + (k + 1)) vh
            * ((F.p : ZMod (F.q ^ (N - 1 - k + (k + 1))))⁻¹) ^ l) * ξ)))‖ ≤ D)
    (hmn : N - 1 ≤ N - 1 - k + (k + 1)) :
    F.osc (N - 1) (N - 1 - k + (k + 1)) hmn
        (F.condDensW (N - 1 - k) (k + 1) l (ggmW T s Kw k l))
      ≤ D * Real.sqrt ((F.q : ℝ) ^ N * ((F.p : ℝ)⁻¹) ^ l) := by
  have hcut := cutEq hkN
  refine le_trans (F.condDensW_osc_le (N - 1 - k) (k + 1) l (N - 1) (ggmW T s Kw k l) hmn D hD
    (fun ξ hξ => hunif ξ ?_)) ?_
  · rw [highFreq, Finset.mem_filter] at hξ
    have h1 : N - 1 - k + (k + 1) - (N - 1) = 1 := by omega
    rw [h1, pow_one] at hξ
    exact hξ.2
  · refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hD
    have hqN : (F.q : ℝ) ^ (N - 1 - k + (k + 1)) = (F.q : ℝ) ^ N := by rw [hcut]
    rw [hqN]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine F.tailDensW_renyi_le (N - 1 - k) (k + 1) l (ggmW T s Kw k l) _ (fun Y => ?_)
    refine F.tailDensW_le_single_mass (N - 1 - k) (k + 1) l (ggmW T s Kw k l) ?_ Y
    intro vt hpos _ hW
    rw [hcut]
    exact F.two_abs_fint_lt vt (fun i => (hpos i).2.2) s Kw l hs0 hρ hW.2 hbudget

end Family

end GGMCollatz
