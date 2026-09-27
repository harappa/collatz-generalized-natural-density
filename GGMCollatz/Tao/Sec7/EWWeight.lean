import GGMCollatz.Tao.Sec7.WhiteExit

/-!
# Degradation of the weight ((7.42), (7.48) of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/BlackEdge.lean`
(`one_sub_rpow_neg_le_exp`, `edgeWeight_summand_le`, `fpDist_edgeWeight_split`, `fpDist_edgeWeight_le_at`);
generalized to the GGM family (p, q, r). Modified: the MGF route of tao-collatz is not used; the proof was rebuilt by truncation:

with `K = ⌊θm/2⌋` (`θ = min(1/2, log(1 + δ/2)/(2A))`), if `e₁ ≤ K` and `d₁ ≤ K` then the depth weight is
`(m - e₁ - d₁)^{-A} ≤ ((1-θ)m)^{-A} ≤ e^{2Aθ} m^{-A} ≤ (1 + δ/2) m^{-A}`; otherwise it is `≤ 1 ≤ 1_{e₁ > K} + 1_{d₁ > K}`.
The tails are `P(𝒥 > K) = ρ^K` (geometric) and `P(e₁ > K)` (the column form of Lemma 7.7, `WE.colTail`; with `s ≤ m / log² m`
the endpoint column center is `s(p-1)/(2p) ≤ θm/4`); both are exponentially small in `m`, hence `≤ (δ/4) m^{-A}`.

Auxiliary declarations are placed in the namespace `GGMCollatz.Family.EW`. Used by `fpDist_edgeWeight_le` in `Case2.lean`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

namespace EW

variable (F : Family)

/-- **Pointwise weight bound**: if `2K ≤ θm`, `θ ≤ 1/2`, `m ≥ 2`, then
`max(m - e₁ - d₁, 1)^{-A} ≤ e^{2Aθ} m^{-A} + 1_{K < e₁} + 1_{K < d₁}`. -/
theorem weight_le {A θ : ℝ} (hA : 0 ≤ A) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) {m K : ℕ}
    (hm : 2 ≤ m) (hK : (2 * K : ℝ) ≤ θ * m) (e d : ℕ × ℤ) :
    ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)
      ≤ Real.exp (2 * A * θ) * (m : ℝ) ^ (-A)
        + (if K < e.1 then 1 else 0) + (if K < d.1 then 1 else 0) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hE0 : 0 ≤ Real.exp (2 * A * θ) * (m : ℝ) ^ (-A) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hmpos.le _)
  by_cases h : e.1 ≤ K ∧ d.1 ≤ K
  · rw [if_neg (by omega), if_neg (by omega), add_zero, add_zero]
    have hJ : ((e.1 + d.1 : ℕ) : ℝ) ≤ θ * m := by
      have : e.1 + d.1 ≤ 2 * K := by omega
      have : ((e.1 + d.1 : ℕ) : ℝ) ≤ ((2 * K : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this ⊢
      linarith
    have hθm : θ * (m : ℝ) ≤ (m : ℝ) / 2 := by nlinarith
    have hlt : e.1 + d.1 < m := by
      have : ((e.1 + d.1 : ℕ) : ℝ) < (m : ℝ) := by linarith
      exact_mod_cast this
    have hmax : max (m - e.1 - d.1) 1 = m - e.1 - d.1 := max_eq_left (by omega)
    rw [hmax]
    have hcast : ((m - e.1 - d.1 : ℕ) : ℝ) = (m : ℝ) - ((e.1 + d.1 : ℕ) : ℝ) := by
      have : m - e.1 - d.1 + (e.1 + d.1) = m := by omega
      have h' : ((m - e.1 - d.1 : ℕ) : ℝ) + ((e.1 + d.1 : ℕ) : ℝ) = (m : ℝ) := by
        exact_mod_cast this
      linarith
    have h1θ : 0 < 1 - θ := by linarith
    have hlow : (m : ℝ) * (1 - θ) ≤ ((m - e.1 - d.1 : ℕ) : ℝ) := by rw [hcast]; nlinarith
    have hpos : 0 < (m : ℝ) * (1 - θ) := by positivity
    calc ((m - e.1 - d.1 : ℕ) : ℝ) ^ (-A) ≤ ((m : ℝ) * (1 - θ)) ^ (-A) :=
          Real.rpow_le_rpow_of_nonpos hpos hlow (by linarith)
      _ = (m : ℝ) ^ (-A) * (1 - θ) ^ (-A) := Real.mul_rpow hmpos.le h1θ.le
      _ ≤ (m : ℝ) ^ (-A) * Real.exp (2 * A * θ) :=
          mul_le_mul_of_nonneg_left (WE.one_sub_rpow_neg_le_exp hA hθ0 hθ)
            (Real.rpow_nonneg hmpos.le _)
      _ = Real.exp (2 * A * θ) * (m : ℝ) ^ (-A) := mul_comm _ _
  · have hw1 : ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast Nat.le_max_right (m - e.1 - d.1) 1) (by linarith)
    have hind : (1 : ℝ) ≤ (if K < e.1 then 1 else 0) + (if K < d.1 then 1 else 0) := by
      by_cases h1 : K < e.1
      · rw [if_pos h1]; split_ifs <;> norm_num
      · rw [if_neg h1, if_pos (by omega)]; norm_num
    linarith

/-- **Tail of `𝒥`**: `P(𝒥 > K) = ρ^K`. -/
theorem hold_fst_tail (K : ℕ) :
    ∑' d : ℕ × ℤ, (F.hold d).toReal * (if K < d.1 then 1 else 0) = F.holdRatio ^ K := by
  rw [F.hold_tsum_fst (fun k => if K < k then (1 : ℝ) else 0) (fun k => by split_ifs <;> norm_num)]
  rw [← F.holdGeom_tail K]
  refine tsum_congr fun k => ?_
  split_ifs <;> simp

/-- `ρ^K ≤ ρ₁⁻¹ e^{-b m}` (`K ≥ θm/2 - 1`, `ρ₁ = max(ρ, 1/2)`, `b = (θ/2) log(1/ρ₁)`). -/
theorem holdRatio_pow_le {θ : ℝ} (_hθ0 : 0 ≤ θ) {m K : ℕ}
    (hK : θ * m / 2 < (K : ℝ) + 1) :
    F.holdRatio ^ K ≤ (max F.holdRatio (1 / 2))⁻¹ *
      Real.exp (-(θ / 2 * -Real.log (max F.holdRatio (1 / 2))) * m) := by
  set r₁ := max F.holdRatio (1 / 2) with hr₁
  have hρ0 := F.holdRatio_nonneg
  have hr₁pos : 0 < r₁ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hr₁lt : r₁ < 1 := max_lt F.holdRatio_lt_one (by norm_num)
  have hlog : Real.log r₁ < 0 := Real.log_neg hr₁pos hr₁lt
  have h1 : F.holdRatio ^ K ≤ r₁ ^ K := pow_le_pow_left₀ hρ0 (le_max_left _ _) K
  have h2 : r₁ ^ K = Real.exp (K * Real.log r₁) := by
    rw [Real.exp_nat_mul, Real.exp_log hr₁pos]
  have h3 : (K : ℝ) * Real.log r₁ ≤ -Real.log r₁ + (-(θ / 2 * -Real.log r₁) * m) := by
    have hK' : θ * m / 2 - 1 ≤ (K : ℝ) := by linarith
    have := mul_le_mul_of_nonpos_right hK' hlog.le
    nlinarith
  calc F.holdRatio ^ K ≤ r₁ ^ K := h1
    _ = Real.exp (K * Real.log r₁) := h2
    _ ≤ Real.exp (-Real.log r₁ + (-(θ / 2 * -Real.log r₁) * m)) := Real.exp_le_exp.mpr h3
    _ = r₁⁻¹ * Real.exp (-(θ / 2 * -Real.log r₁) * m) := by
        rw [Real.exp_add, Real.exp_neg, Real.exp_log hr₁pos]

/-- **Degradation of the weight** (`fpDist_edgeWeight_le` of tao-collatz, (7.48)): for `A, δ > 0` there is a threshold such that,
if `m` is large and `s ≤ m / log² m`, then `Σ_e P(e) Σ_d ℋ(d) max(m - e₁ - d₁, 1)^{-A} ≤ (1+δ) m^{-A}`. -/
theorem edgeWeight_bound (A : ℝ) (hA : 0 < A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Cthr : ℕ, ∀ m : ℕ, Cthr ≤ m → ∀ s : ℕ,
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      ∑' e : ℕ × ℤ, (F.fpDist s e).toReal *
        (∑' d : ℕ × ℤ, (F.hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A))
        ≤ (1 + δ) * (m : ℝ) ^ (-A) := by
  obtain ⟨c, hc, C', hC', hcol⟩ := F.fpDist_col_le
  -- `θ`
  have hL : 0 < Real.log (1 + δ / 2) := Real.log_pos (by linarith)
  set θ : ℝ := min (1 / 2) (Real.log (1 + δ / 2) / (2 * A)) with hθdef
  have hθpos : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ2 : θ ≤ 1 / 2 := min_le_left _ _
  have hθexp : Real.exp (2 * A * θ) ≤ 1 + δ / 2 := by
    have h : 2 * A * θ ≤ Real.log (1 + δ / 2) := by
      have h' : θ ≤ Real.log (1 + δ / 2) / (2 * A) := min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at h'
      linarith
    calc Real.exp (2 * A * θ) ≤ Real.exp (Real.log (1 + δ / 2)) := Real.exp_le_exp.mpr h
      _ = 1 + δ / 2 := Real.exp_log (by linarith)
  -- constants for the column tail
  have hγ₀ : 0 < θ / 8 := by positivity
  set c₀ := min (c ^ 2 * (θ / 8)) c with hc₀def
  have hc₀ : 0 < c₀ := lt_min (by positivity) hc
  have hd₀ : 0 < 1 - Real.exp (-c₀) := by
    have : Real.exp (-c₀) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  obtain ⟨M₃, hM₃⟩ := WE.exp_neg_mul_le_rpow_eventually A (b := c₀ * (θ / 4)) (by positivity)
    (η := (δ / 4) * (1 - Real.exp (-c₀)) / (2 * C')) (by positivity)
  -- constants for the tail of `𝒥`
  set r₁ := max F.holdRatio (1 / 2) with hr₁
  have hr₁pos : 0 < r₁ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hr₁lt : r₁ < 1 := max_lt F.holdRatio_lt_one (by norm_num)
  have hlogr : 0 < -Real.log r₁ := by linarith [Real.log_neg hr₁pos hr₁lt]
  obtain ⟨M₄, hM₄⟩ := WE.exp_neg_mul_le_rpow_eventually A (b := θ / 2 * -Real.log r₁)
    (by positivity) (η := (δ / 4) * r₁) (by positivity)
  -- `log m ≥ max 1 (2/θ)`
  set L₀ : ℝ := max 1 (2 / θ) with hL₀
  refine ⟨M₃ + M₄ + ⌈Real.exp L₀⌉₊ + 2, ?_⟩
  intro m hm s hs
  have hm2 : 2 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlogm : L₀ ≤ Real.log m := by
    have h1 : Real.exp L₀ ≤ (m : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast (show ⌈Real.exp L₀⌉₊ ≤ m by omega))
    calc L₀ = Real.log (Real.exp L₀) := (Real.log_exp _).symm
      _ ≤ Real.log m := Real.log_le_log (Real.exp_pos _) h1
  have hlog1 : 1 ≤ Real.log m := le_trans (le_max_left _ _) hlogm
  have hlogθ : 2 / θ ≤ Real.log m := le_trans (le_max_right _ _) hlogm
  have hlogsq : Real.log m ≤ Real.log m ^ 2 := by nlinarith
  have hlsq_pos : 0 < Real.log m ^ 2 := by positivity
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hsm : (s : ℝ) ≤ m := by
    calc (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 := hs
      _ ≤ (m : ℝ) / 1 := div_le_div_of_nonneg_left hmpos.le one_pos (by linarith)
      _ = m := div_one _
  have hsθ : (s : ℝ) ≤ θ * m / 2 := by
    calc (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 := hs
      _ ≤ (m : ℝ) / (2 / θ) := div_le_div_of_nonneg_left hmpos.le (by positivity) (by linarith)
      _ = θ * m / 2 := by field_simp
  have hx₀ : (s : ℝ) * F.slopeInv ≤ θ * m / 4 := by
    have := WE.slopeInv_le_half F
    have := WE.slopeInv_nonneg F
    nlinarith
  -- `K`
  set K : ℕ := ⌊θ * m / 2⌋₊ with hKdef
  have hK2 : (2 * K : ℝ) ≤ θ * m := by
    have := Nat.floor_le (show 0 ≤ θ * m / 2 by positivity)
    rw [← hKdef] at this
    linarith
  have hK1 : θ * m / 2 < (K : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (θ * m / 2)
    rwa [← hKdef] at this
  -- pointwise
  set E₀ := Real.exp (2 * A * θ) * (m : ℝ) ^ (-A) with hE₀
  set H := ∑' d : ℕ × ℤ, (F.hold d).toReal * (if K < d.1 then (1 : ℝ) else 0) with hHdef
  have hmA0 : 0 ≤ (m : ℝ) ^ (-A) := Real.rpow_nonneg hmpos.le _
  have hE00 : 0 ≤ E₀ := mul_nonneg (Real.exp_pos _).le hmA0
  have hholdS := F.hold_summable_toReal
  have hind01 : ∀ (P : Prop) [Decidable P], 0 ≤ (if P then (1 : ℝ) else 0)
      ∧ (if P then (1 : ℝ) else 0) ≤ 1 := fun P _ => by
    constructor <;> split_ifs <;> norm_num
  have hsHd : Summable fun d : ℕ × ℤ => (F.hold d).toReal * (if K < d.1 then (1 : ℝ) else 0) :=
    Summable.of_nonneg_of_le (fun d => mul_nonneg ENNReal.toReal_nonneg (hind01 _).1)
      (fun d => mul_le_of_le_one_right ENNReal.toReal_nonneg (hind01 _).2) hholdS
  have hwS : ∀ e : ℕ × ℤ, Summable fun d : ℕ × ℤ =>
      (F.hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) := fun e =>
    Summable.of_nonneg_of_le
      (fun d => mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (fun d => mul_le_of_le_one_right ENNReal.toReal_nonneg
        (Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast Nat.le_max_right (m - e.1 - d.1) 1) (by linarith)))
      hholdS
  have hEW : ∀ e : ℕ × ℤ,
      ∑' d : ℕ × ℤ, (F.hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)
        ≤ E₀ + (if K < e.1 then (1 : ℝ) else 0) + H := by
    intro e
    set a := E₀ + (if K < e.1 then (1 : ℝ) else 0) with ha
    have hS1 : Summable fun d : ℕ × ℤ => (F.hold d).toReal * a := hholdS.mul_right a
    calc ∑' d : ℕ × ℤ, (F.hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)
        ≤ ∑' d : ℕ × ℤ, ((F.hold d).toReal * a
            + (F.hold d).toReal * (if K < d.1 then (1 : ℝ) else 0)) := by
          refine (hwS e).tsum_le_tsum (fun d => ?_) (hS1.add hsHd)
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left
            (EW.weight_le hA.le hθpos.le hθ2 hm2 hK2 e d) ENNReal.toReal_nonneg
      _ = a + H := by
          rw [hS1.tsum_add hsHd, tsum_mul_right, F.hold_tsum_toReal, one_mul]
  -- the outer sum
  have hfp : Summable fun e => (F.fpDist s e).toReal :=
    ENNReal.summable_toReal (F.fpDist s).tsum_coe_ne_top
  have hfp1 : ∑' e, (F.fpDist s e).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun e => (F.fpDist s).apply_ne_top e), (F.fpDist s).tsum_coe,
      ENNReal.toReal_one]
  have hEWle1 : ∀ e : ℕ × ℤ,
      ∑' d : ℕ × ℤ, (F.hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) ≤ 1 := by
    intro e
    calc _ ≤ ∑' d : ℕ × ℤ, (F.hold d).toReal :=
          (hwS e).tsum_le_tsum (fun d => mul_le_of_le_one_right ENNReal.toReal_nonneg
            (Real.rpow_le_one_of_one_le_of_nonpos
              (by exact_mod_cast Nat.le_max_right (m - e.1 - d.1) 1) (by linarith))) hholdS
      _ = 1 := F.hold_tsum_toReal
  have hLS : Summable fun e => (F.fpDist s e).toReal *
      ∑' d : ℕ × ℤ, (F.hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) :=
    Summable.of_nonneg_of_le
      (fun e => mul_nonneg ENNReal.toReal_nonneg
        (tsum_nonneg fun d => mul_nonneg ENNReal.toReal_nonneg
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
      (fun e => mul_le_of_le_one_right ENNReal.toReal_nonneg (hEWle1 e)) hfp
  have hIS : Summable fun e => (F.fpDist s e).toReal * (if K < e.1 then (1 : ℝ) else 0) :=
    Summable.of_nonneg_of_le (fun e => mul_nonneg ENNReal.toReal_nonneg (hind01 _).1)
      (fun e => mul_le_of_le_one_right ENNReal.toReal_nonneg (hind01 _).2) hfp
  have hRS : Summable fun e => ((F.fpDist s e).toReal * (E₀ + H)
      + (F.fpDist s e).toReal * (if K < e.1 then (1 : ℝ) else 0)) :=
    (hfp.mul_right _).add hIS
  -- the tail of the endpoint column
  have hPfp : ∑' e, (F.fpDist s e).toReal * (if K < e.1 then (1 : ℝ) else 0)
      ≤ δ / 4 * (m : ℝ) ^ (-A) := by
    have hconv : ∑' e, (F.fpDist s e).toReal * (if K < e.1 then (1 : ℝ) else 0)
        = ∑' e : ℕ × ℤ, (F.fpDist s e).toReal
            * (if (K : ℝ) + 1 ≤ (e.1 : ℝ) then 1 else 0) := by
      refine tsum_congr fun e => ?_
      congr 1
      refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
      · have : K + 1 ≤ e.1 := h
        exact_mod_cast this
      · have : K + 1 ≤ e.1 := by exact_mod_cast h
        exact this
    have hy : θ / 8 * (1 + (s : ℝ)) ≤ ((K : ℝ) + 1) - s * F.slopeInv := by nlinarith
    rw [hconv]
    refine le_trans (WE.colTail F hc hC' hcol s hγ₀ hy) ?_
    rw [← hc₀def]
    have hD : θ * m / 4 ≤ ((K : ℝ) + 1) - s * F.slopeInv := by linarith
    have hexp : Real.exp (-c₀ * (((K : ℝ) + 1) - s * F.slopeInv))
        ≤ Real.exp (-(c₀ * (θ / 4)) * m) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hD hc₀.le
      have e : -(c₀ * (θ / 4)) * (m : ℝ) = -(c₀ * (θ * m / 4)) := by ring
      rw [e]; linarith
    have hη := hM₃ m (by omega)
    rw [div_le_iff₀ hd₀]
    calc 2 * C' * Real.exp (-c₀ * (((K : ℝ) + 1) - s * F.slopeInv))
        ≤ 2 * C' * ((δ / 4) * (1 - Real.exp (-c₀)) / (2 * C') * (m : ℝ) ^ (-A)) :=
          mul_le_mul_of_nonneg_left (hexp.trans hη) (by positivity)
      _ = δ / 4 * (m : ℝ) ^ (-A) * (1 - Real.exp (-c₀)) := by field_simp
  -- the tail of `𝒥`
  have hHb : H ≤ δ / 4 * (m : ℝ) ^ (-A) := by
    rw [hHdef, hold_fst_tail F K]
    refine le_trans (holdRatio_pow_le F hθpos.le hK1) ?_
    rw [← hr₁]
    have hη := hM₄ m (by omega)
    calc r₁⁻¹ * Real.exp (-(θ / 2 * -Real.log r₁) * m)
        ≤ r₁⁻¹ * ((δ / 4) * r₁ * (m : ℝ) ^ (-A)) :=
          mul_le_mul_of_nonneg_left hη (inv_nonneg.mpr hr₁pos.le)
      _ = δ / 4 * (m : ℝ) ^ (-A) := by field_simp
  -- assembly
  calc ∑' e : ℕ × ℤ, (F.fpDist s e).toReal *
        (∑' d : ℕ × ℤ, (F.hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A))
      ≤ ∑' e : ℕ × ℤ, ((F.fpDist s e).toReal * (E₀ + H)
          + (F.fpDist s e).toReal * (if K < e.1 then (1 : ℝ) else 0)) := by
        refine hLS.tsum_le_tsum (fun e => ?_) hRS
        rw [← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        have := hEW e
        linarith
    _ = (E₀ + H) + ∑' e, (F.fpDist s e).toReal * (if K < e.1 then (1 : ℝ) else 0) := by
        rw [(hfp.mul_right _).tsum_add hIS, tsum_mul_right, hfp1, one_mul]
    _ ≤ (1 + δ / 2) * (m : ℝ) ^ (-A) + δ / 4 * (m : ℝ) ^ (-A) + δ / 4 * (m : ℝ) ^ (-A) := by
        have hE : E₀ ≤ (1 + δ / 2) * (m : ℝ) ^ (-A) := mul_le_mul_of_nonneg_right hθexp hmA0
        linarith
    _ = (1 + δ) * (m : ℝ) ^ (-A) := by ring

end EW

end Family

end GGMCollatz
