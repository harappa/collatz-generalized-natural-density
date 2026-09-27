import GGMCollatz.Tao.Sec7.Setup

/-!
# The renewal process `ℋ = (𝒥, 𝒫_{1,𝒥})` of GGM §6 and the renewal value `Q` (counterpart of §7.3 of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/Holding.lean`;
generalized to the GGM family (p, q, r). Modified. GGM §6 Step 1 (`ℋ := (𝒥, 𝒫_{1,𝒥})`, where `𝒥` is the first time at which `𝒫 = 3`).

* `hold`: the law of `ℋ`. Draw `k ~ holdGeom p` (geometric with success probability `P(Pascal = 3) = 2(p-1)²/p³`),
  and add `3` to the sum of `k - 1` independent Pascal variables conditioned to avoid `b = 3`: `(k, 3 + Σ)`. The `hold` of tao-collatz is the case `p = 2`.
* `Q half W κ j l`: the renewal value (the finitization D6 of tao-collatz's (7.34), (7.35)). Outside the strip (`half < j`) it is `1`;
  inside the strip it is `exp(-κ 1_W(j,l)) Σ_d hold(d) Q((j,l)+d)`. tao-collatz wrote it with `κ = ε³`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- **One-step law of the renewal** `ℋ = (𝒥, 𝒫_{1,𝒥})` (GGM §6, `hold` of tao-collatz). -/
noncomputable def hold : PMF (ℕ × ℤ) :=
  (holdGeom F.p).bind fun k =>
    ((pascalNe3P F.p).iid (k - 1)).map fun v => (k, (3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ))

theorem holdGeom_zero : holdGeom F.p 0 = 0 := by
  unfold holdGeom
  rw [geomS_apply (holdGeom_prob F.two_le_p), if_pos rfl]

/-- The first coordinate of an atom of `hold` is positive. -/
theorem hold_support_fst_pos (d : ℕ × ℤ) (hd : d ∈ F.hold.support) : 1 ≤ d.1 := by
  rw [hold, PMF.mem_support_bind_iff] at hd
  obtain ⟨k, hk, hkd⟩ := hd
  rw [PMF.mem_support_map_iff] at hkd
  obtain ⟨v, _, hv⟩ := hkd
  have hk0 : k ≠ 0 := by
    intro h
    rw [PMF.mem_support_iff] at hk
    apply hk
    rw [h]
    exact F.holdGeom_zero
  rw [← hv]
  exact Nat.one_le_iff_ne_zero.mpr hk0

/-- Points whose first coordinate is `0` have mass `0`. -/
theorem hold_zero_of_fst_zero {d : ℕ × ℤ} (h0 : d.1 = 0) : F.hold d = 0 := by
  rw [PMF.apply_eq_zero_iff]
  intro hd
  exact absurd (F.hold_support_fst_pos d hd) (by omega)

/-- The first marginal of `hold` is `holdGeom p`. -/
theorem hold_map_fst : F.hold.map Prod.fst = holdGeom F.p := by
  rw [hold, PMF.map_bind]
  have h : ∀ k : ℕ,
      ((((pascalNe3P F.p).iid (k - 1)).map
          fun v => (k, (3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ))).map Prod.fst) = PMF.pure k := by
    intro k
    rw [PMF.map_comp]
    exact PMF.map_const _ _
  simp only [h]
  exact PMF.bind_pure _

/-- The mass of the slice with fixed first coordinate is the mass of `holdGeom`. -/
theorem hold_fst_marginal (k : ℕ) : ∑' l : ℤ, F.hold (k, l) = holdGeom F.p k := by
  have h1 : F.hold.map Prod.fst k = ∑' l : ℤ, F.hold (k, l) := by
    rw [PMF.map_apply, ENNReal.tsum_prod']
    rw [tsum_eq_single k (fun k' hk' => by simp [Ne.symm hk'])]
    exact tsum_congr fun l => by simp
  rw [← h1, F.hold_map_fst]

/-- The `hold`-expectation of a function of the first coordinate alone is its `holdGeom`-expectation. -/
theorem hold_tsum_fst (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    ∑' d : ℕ × ℤ, (F.hold d).toReal * f d.1 = ∑' k : ℕ, (holdGeom F.p k).toReal * f k := by
  have hEN : ∑' d : ℕ × ℤ, F.hold d * ENNReal.ofReal (f d.1)
      = ∑' k : ℕ, holdGeom F.p k * ENNReal.ofReal (f k) := by
    rw [ENNReal.tsum_prod']
    refine tsum_congr fun k => ?_
    have : ∀ l : ℤ, F.hold (k, l) * ENNReal.ofReal (f (k, l).1)
        = F.hold (k, l) * ENNReal.ofReal (f k) := fun l => rfl
    rw [tsum_congr this, ENNReal.tsum_mul_right, F.hold_fst_marginal]
  calc ∑' d : ℕ × ℤ, (F.hold d).toReal * f d.1
      = ∑' d : ℕ × ℤ, (F.hold d * ENNReal.ofReal (f d.1)).toReal :=
        tsum_congr fun d => by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf _)]
    _ = (∑' d : ℕ × ℤ, F.hold d * ENNReal.ofReal (f d.1)).toReal :=
        (ENNReal.tsum_toReal_eq fun d =>
          ENNReal.mul_ne_top (F.hold.apply_ne_top d) ENNReal.ofReal_ne_top).symm
    _ = (∑' k : ℕ, holdGeom F.p k * ENNReal.ofReal (f k)).toReal := by rw [hEN]
    _ = ∑' k : ℕ, (holdGeom F.p k * ENNReal.ofReal (f k)).toReal :=
        ENNReal.tsum_toReal_eq fun k =>
          ENNReal.mul_ne_top ((holdGeom F.p).apply_ne_top k) ENNReal.ofReal_ne_top
    _ = ∑' k : ℕ, (holdGeom F.p k).toReal * f k :=
        tsum_congr fun k => by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf _)]

/-- Atoms of `hold` with fixed first coordinate: the product of the `holdGeom` mass and the law of the sum of increments. -/
theorem hold_apply_pin (k₀ : ℕ) (y : ℤ) :
    F.hold (k₀, y) = holdGeom F.p k₀ *
      (((pascalNe3P F.p).iid (k₀ - 1)).map fun v => ((3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ))) y := by
  classical
  rw [hold, PMF.bind_apply]
  rw [tsum_eq_single k₀ (fun k hk => by
    have hz : (((pascalNe3P F.p).iid (k - 1)).map
        fun v => ((k : ℕ), ((3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ)))) (k₀, y) = 0 := by
      rw [PMF.map_apply]
      refine ENNReal.tsum_eq_zero.mpr fun v => ?_
      rw [if_neg (fun h => hk ((congrArg Prod.fst h).symm : k = k₀))]
    rw [hz, mul_zero])]
  congr 1
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun v => ?_
  congr 1
  rw [Prod.ext_iff]
  simp

/-- The real masses of `hold` sum to `1`. -/
theorem hold_tsum_toReal : ∑' d : ℕ × ℤ, (F.hold d).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun d => F.hold.apply_ne_top d), F.hold.tsum_coe,
    ENNReal.toReal_one]

/-- The real masses of `hold` are summable. -/
theorem hold_summable_toReal : Summable fun d : ℕ × ℤ => (F.hold d).toReal :=
  ENNReal.summable_toReal F.hold.tsum_coe_ne_top

/-! ### The renewal value `Q` (finitization D6) -/

/-- **The renewal value** `Q` ((7.34), (7.35) of tao-collatz, D6): `1` outside the strip; inside the strip,
a self-recursion averaged over `hold`. Well-founded recursion on `half + 1 - j` (the first coordinate of `hold` is `≥ 1`). -/
noncomputable def Q (half : ℕ) (W : Set (ℕ × ℤ)) (κ : ℝ) : ℕ → ℤ → ℝ
  | j, l =>
    if half < j then 1
    else Real.exp (-κ * Set.indicator W 1 (j, l)) *
      ∑' d : ℕ × ℤ,
        if hd : d.1 = 0 then 0
        else (F.hold d).toReal * Q half W κ (j + d.1) (l + d.2)
  termination_by j _ => half + 1 - j
  decreasing_by omega

/-- Boundary ((7.34) of tao-collatz): `Q = 1` outside the strip. -/
theorem Q_boundary (half : ℕ) (W : Set (ℕ × ℤ)) (κ : ℝ) (j : ℕ) (l : ℤ) (hj : half < j) :
    F.Q half W κ j l = 1 := by
  rw [Q]; simp [hj]

/-- Recursion ((7.35) of tao-collatz). -/
theorem Q_rec (half : ℕ) (W : Set (ℕ × ℤ)) (κ : ℝ) (j : ℕ) (l : ℤ) (hj : j ≤ half) :
    F.Q half W κ j l = Real.exp (-κ * Set.indicator W 1 (j, l)) *
      ∑' d : ℕ × ℤ, (F.hold d).toReal * F.Q half W κ (j + d.1) (l + d.2) := by
  rw [Q]
  rw [if_neg (by omega : ¬ half < j)]
  congr 1
  apply tsum_congr
  intro d
  by_cases h0 : d.1 = 0
  · rw [dif_pos h0, F.hold_zero_of_fst_zero h0, ENNReal.toReal_zero, zero_mul]
  · rw [dif_neg h0]

/-- `Q ≥ 0`. -/
theorem Q_nonneg (half : ℕ) (W : Set (ℕ × ℤ)) (κ : ℝ) : ∀ j l, 0 ≤ F.Q half W κ j l := by
  have key : ∀ n j l, half + 1 - j = n → 0 ≤ F.Q half W κ j l := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro j l hn
      rcases Nat.lt_or_ge half j with hj | hj
      · rw [F.Q_boundary _ _ _ _ _ hj]; exact zero_le_one
      · rw [F.Q_rec _ _ _ _ _ hj]
        refine mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun d => ?_)
        rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
        · rw [F.hold_zero_of_fst_zero h0, ENNReal.toReal_zero, zero_mul]
        · exact mul_nonneg ENNReal.toReal_nonneg
            (IH (half + 1 - (j + d.1)) (by omega) _ _ rfl)
  exact fun j l => key _ j l rfl

/-- `Q ≤ 1` (`κ ≥ 0`). -/
theorem Q_le_one (half : ℕ) (W : Set (ℕ × ℤ)) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∀ j l, F.Q half W κ j l ≤ 1 := by
  have key : ∀ n j l, half + 1 - j = n → F.Q half W κ j l ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro j l hn
      rcases Nat.lt_or_ge half j with hj | hj
      · rw [F.Q_boundary _ _ _ _ _ hj]
      · rw [F.Q_rec _ _ _ _ _ hj]
        have hexp : Real.exp (-κ * Set.indicator W 1 (j, l)) ≤ 1 := by
          rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
          exact mul_nonneg hκ (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
        have hterm : ∀ d : ℕ × ℤ,
            (F.hold d).toReal * F.Q half W κ (j + d.1) (l + d.2) ≤ (F.hold d).toReal := by
          intro d
          rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
          · rw [F.hold_zero_of_fst_zero h0, ENNReal.toReal_zero, zero_mul]
          · calc (F.hold d).toReal * F.Q half W κ (j + d.1) (l + d.2)
                ≤ (F.hold d).toReal * 1 :=
                  mul_le_mul_of_nonneg_left
                    (IH (half + 1 - (j + d.1)) (by omega) _ _ rfl) ENNReal.toReal_nonneg
              _ = (F.hold d).toReal := mul_one _
        have hterm_nonneg : ∀ d : ℕ × ℤ,
            0 ≤ (F.hold d).toReal * F.Q half W κ (j + d.1) (l + d.2) :=
          fun d => mul_nonneg ENNReal.toReal_nonneg (F.Q_nonneg _ _ _ _ _)
        have hsum_f : Summable fun d : ℕ × ℤ =>
            (F.hold d).toReal * F.Q half W κ (j + d.1) (l + d.2) :=
          Summable.of_nonneg_of_le hterm_nonneg hterm F.hold_summable_toReal
        have htsum : ∑' d : ℕ × ℤ, (F.hold d).toReal * F.Q half W κ (j + d.1) (l + d.2) ≤ 1 :=
          le_trans (Summable.tsum_le_tsum hterm hsum_f F.hold_summable_toReal)
            F.hold_tsum_toReal.le
        calc Real.exp (-κ * Set.indicator W 1 (j, l)) *
              ∑' d, (F.hold d).toReal * F.Q half W κ (j + d.1) (l + d.2)
            ≤ 1 * 1 := mul_le_mul hexp htsum (tsum_nonneg hterm_nonneg) zero_le_one
          _ = 1 := mul_one 1
  exact fun j l => key _ j l rfl

end Family

end GGMCollatz
