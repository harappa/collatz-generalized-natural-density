import Mathlib

/-!
# Lemmas for (KRON) (an elementary proof of the block form)

Instead of the Erdős–Turán and Koksma inequalities, we use Dirichlet's approximation theorem (`Real.exists_rat_abs_sub_le_and_den_le`)
and the Riemann-sum bounds for monotone functions (`AntitoneOn.integral_le_sum`, `AntitoneOn.sum_le_integral`).

* `extF f`: extends `f`, nonincreasing on `[0,1]` with values in `[0,1]`, to all of `ℝ` by `1` for `t < 0` and `0` for `t > 1`.
* `shift_integral`: `|∫_s^{s+1} F - ∫_0^1 F| ≤ 2|s|`.
* `riemann_lo`, `riemann_hi`: Riemann sums over the lattice `φ + i/h`.
* `pt_bound`: upper and lower bounds for the value at a point displaced by less than `1/h` from a lattice point (the two end
  points may wrap around, so `1` is added).
* `sum_perm`: `k ↦ (m + kA) mod h` is a bijection of `range h` (`A` and `h` coprime).
* `block_bound`: if `λ = A/h + η` and `h²|η| < 1`, then the sum over `h` consecutive points differs from `h ∫ F` by at most `5`.
* `chain_bound`: chaining the blocks, `|Σ_{k < mh + r} - (mh + r)∫F| ≤ 5m + r`.
* `kron_main`: take the Dirichlet approximation with `Q = ⌈ℓ^{1-1/μ}⌉`; from the irrationality measure `h^{μ-1} ≥ c(Q+1)`,
  and the error is `5ℓ/h + h ≤ (5c^{-1/(μ-1)} + 2) ℓ^{1-1/μ}` (the main body of `kron_statement`).
* `var_bound`, `wblock`, `wchain`, `kronW_main`: split into blocks of length `ℓ` and freeze the weight inside each block at its
  value at the left end. The cost of freezing is `ℓ V_B`; the main term is `w(n_B) C ℓ^{1-1/μ}` with `w(n_B) ≤ W_B/ℓ + V_B`;
  the leftover block costs `ℓ V` (`w ≤ V` since `V` includes the jump `w(a) = |w(a) - w(a-1)|` at the left end).
  In total `2ℓV + C(Wℓ^{-1/μ} + Vℓ^{1-1/μ})` (the main body of `kronW_statement`; the constant is the `C` of the block form).
-/

namespace GGMCollatz

namespace ND

namespace KronAux

open intervalIntegral

/-- Extension outside `[0,1]`: `1` for `t < 0` and `0` for `t > 1`. -/
noncomputable def extF (f : ℝ → ℝ) (t : ℝ) : ℝ := if t < 0 then 1 else if 1 < t then 0 else f t

section Ext

variable {f : ℝ → ℝ} (hf : AntitoneOn f (Set.Icc 0 1))
  (hf01 : ∀ θ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f θ ∧ f θ ≤ 1)
include hf01

omit hf01 in
theorem extF_eq {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : extF f t = f t := by
  unfold extF
  rw [if_neg (not_lt.2 ht.1), if_neg (not_lt.2 ht.2)]

theorem extF_mem (t : ℝ) : 0 ≤ extF f t ∧ extF f t ≤ 1 := by
  unfold extF
  split_ifs with h1 h2
  · exact ⟨zero_le_one, le_rfl⟩
  · exact ⟨le_rfl, zero_le_one⟩
  · exact hf01 t ⟨not_lt.1 h1, not_lt.1 h2⟩

include hf in
theorem extF_antitone : Antitone (extF f) := by
  intro s t hst
  have hmem := extF_mem hf01
  by_cases ht0 : t < 0
  · have hs0 : s < 0 := lt_of_le_of_lt hst ht0
    simp [extF, ht0, hs0]
  by_cases ht1 : 1 < t
  · have : extF f t = 0 := by simp [extF, ht0, ht1]
    rw [this]; exact (hmem s).1
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨not_lt.1 ht0, not_lt.1 ht1⟩
  rw [extF_eq ht]
  by_cases hs0 : s < 0
  · have : extF f s = 1 := by simp [extF, hs0]
    rw [this]; exact (hf01 t ht).2
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := ⟨not_lt.1 hs0, le_trans hst ht.2⟩
  rw [extF_eq hs]
  exact hf hs ht hst

omit hf01 in
theorem extF_neg {t : ℝ} (ht : t < 0) : extF f t = 1 := by simp [extF, ht]

omit hf01 in
theorem extF_big {t : ℝ} (ht : 1 < t) : extF f t = 0 := by
  have : ¬ t < 0 := by linarith
  simp [extF, this, ht]

omit hf01 in
theorem extF_integral : ∫ θ in (0 : ℝ)..1, extF f θ = ∫ θ in (0 : ℝ)..1, f θ := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  exact extF_eq ht

end Ext

section Riemann

variable {F : ℝ → ℝ} (hF : Antitone F) (h01 : ∀ t, 0 ≤ F t ∧ F t ≤ 1)
include hF h01

omit hF in
theorem integral_mem : 0 ≤ ∫ t in (0 : ℝ)..1, F t ∧ ∫ t in (0 : ℝ)..1, F t ≤ 1 := by
  constructor
  · exact intervalIntegral.integral_nonneg zero_le_one (fun t _ => (h01 t).1)
  · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := 1) (f := F)
      (fun x _ => by rw [Real.norm_eq_abs, abs_of_nonneg (h01 x).1]; exact (h01 x).2)
    rw [Real.norm_eq_abs] at this
    simpa using (le_abs_self _).trans this

theorem shift_integral (s : ℝ) :
    |(∫ t in s..s + 1, F t) - ∫ t in (0 : ℝ)..1, F t| ≤ 2 * |s| := by
  have hi : ∀ a b : ℝ, IntervalIntegrable F MeasureTheory.volume a b :=
    fun a b => hF.intervalIntegrable
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hi s 0) (hi 0 1)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hi s 1) (hi 1 (s + 1))
  have hb : ∀ a b : ℝ, |∫ t in a..b, F t| ≤ |b - a| := by
    intro a b
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 1) (f := F)
      (fun x _ => by rw [Real.norm_eq_abs, abs_of_nonneg (h01 x).1]; exact (h01 x).2)
    simpa [Real.norm_eq_abs] using this
  have b1 := hb s 0
  have b2 := hb 1 (s + 1)
  have hd : (∫ t in s..s + 1, F t) - ∫ t in (0 : ℝ)..1, F t
      = (∫ t in s..0, F t) + ∫ t in (1 : ℝ)..s + 1, F t := by linarith
  rw [hd]
  have : |0 - s| = |s| := by rw [zero_sub, abs_neg]
  have : |s + 1 - 1| = |s| := by rw [add_sub_cancel_right]
  calc _ ≤ |∫ t in s..0, F t| + |∫ t in (1 : ℝ)..s + 1, F t| := abs_add_le _ _
    _ ≤ |s| + |s| := by linarith
    _ = 2 * |s| := by ring

/-- Lower bound for the Riemann sum over the lattice `φ + (i+1)/h`. -/
theorem riemann_lo {h : ℕ} (hh : 0 < h) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : (h : ℝ) * φ < 1) :
    (h : ℝ) * (∫ t in (0 : ℝ)..1, F t) - 4 ≤ ∑ i ∈ Finset.range h, F (φ + ((i : ℝ) + 1) / h) := by
  have hpos : (0 : ℝ) < h := Nat.cast_pos.2 hh
  have hG : Antitone (fun t => F (t / h)) := fun a b hab => hF (div_le_div_of_nonneg_right hab hpos.le)
  have key := (hG.antitoneOn (Set.Icc ((h : ℝ) * φ + 1) ((h : ℝ) * φ + 1 + h))).integral_le_sum
  rw [intervalIntegral.integral_comp_div (fun t => F t) hpos.ne'] at key
  have e1 : ((h : ℝ) * φ + 1) / h = φ + 1 / h := by field_simp
  have e2 : ((h : ℝ) * φ + 1 + h) / h = (φ + 1 / h) + 1 := by field_simp
  rw [e1, e2, smul_eq_mul] at key
  have hsum : ∀ i ∈ Finset.range h, F (((h : ℝ) * φ + 1 + i) / h) = F (φ + ((i : ℝ) + 1) / h) := by
    intro i _
    congr 1
    field_simp
    ring
  rw [Finset.sum_congr rfl hsum] at key
  have hs := shift_integral hF h01 (φ + 1 / h)
  have hs0 : 0 ≤ φ + 1 / h := by positivity
  rw [abs_of_nonneg hs0] at hs
  have hhs : (h : ℝ) * (φ + 1 / h) = h * φ + 1 := by field_simp
  have hlow : (∫ t in (0 : ℝ)..1, F t) - 2 * (φ + 1 / h) ≤ ∫ t in (φ + 1 / h)..(φ + 1 / h) + 1, F t := by
    linarith [neg_abs_le ((∫ t in (φ + 1 / h)..(φ + 1 / h) + 1, F t) - ∫ t in (0 : ℝ)..1, F t)]
  have := mul_le_mul_of_nonneg_left hlow hpos.le
  nlinarith

/-- Upper bound for the Riemann sum over the lattice `φ + (i-1)/h`. -/
theorem riemann_hi {h : ℕ} (hh : 0 < h) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : (h : ℝ) * φ < 1) :
    ∑ i ∈ Finset.range h, F (φ + ((i : ℝ) - 1) / h) ≤ (h : ℝ) * (∫ t in (0 : ℝ)..1, F t) + 4 := by
  have hpos : (0 : ℝ) < h := Nat.cast_pos.2 hh
  have hG : Antitone (fun t => F (t / h)) := fun a b hab => hF (div_le_div_of_nonneg_right hab hpos.le)
  have key := (hG.antitoneOn (Set.Icc ((h : ℝ) * φ - 2) ((h : ℝ) * φ - 2 + h))).sum_le_integral
  rw [intervalIntegral.integral_comp_div (fun t => F t) hpos.ne'] at key
  have e1 : ((h : ℝ) * φ - 2) / h = φ - 2 / h := by field_simp
  have e2 : ((h : ℝ) * φ - 2 + h) / h = (φ - 2 / h) + 1 := by field_simp
  rw [e1, e2, smul_eq_mul] at key
  have hsum : ∀ i ∈ Finset.range h,
      F (((h : ℝ) * φ - 2 + ((i + 1 : ℕ) : ℝ)) / h) = F (φ + ((i : ℝ) - 1) / h) := by
    intro i _
    congr 1
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl hsum] at key
  have hs := shift_integral hF h01 (φ - 2 / h)
  have hs0 : |φ - 2 / h| ≤ 2 / h := by
    rw [abs_le]
    have : φ < 1 / h := by rw [lt_div_iff₀ hpos]; linarith
    have e3 : 2 / (h : ℝ) = 2 * (1 / h) := by ring
    have : 0 < 1 / (h : ℝ) := by positivity
    constructor
    · linarith
    · have : 0 < 2 / (h : ℝ) := by positivity
      linarith
  have hup : (∫ t in (φ - 2 / h)..(φ - 2 / h) + 1, F t) ≤ (∫ t in (0 : ℝ)..1, F t) + 2 * (2 / h) := by
    linarith [le_abs_self ((∫ t in (φ - 2 / h)..(φ - 2 / h) + 1, F t) - ∫ t in (0 : ℝ)..1, F t)]
  have := mul_le_mul_of_nonneg_left hup hpos.le
  have hh2 : (h : ℝ) * (2 * (2 / h)) = 4 := by field_simp; ring
  nlinarith

end Riemann

section Point

variable {F : ℝ → ℝ} (hF : Antitone F) (h01 : ∀ t, 0 ≤ F t ∧ F t ≤ 1)
  (hneg : ∀ t, t < 0 → F t = 1) (hbig : ∀ t, 1 < t → F t = 0)
include hF h01 hneg hbig

/-- Upper and lower bounds for the value at a point `x` displaced by less than `1/h` from the lattice point `φ + i/h`
(`h x ∈ (hφ + i - 1, hφ + i + 1)`). The two end points (`i = 0` and `i = h - 1`) may wrap around under `Int.fract`, so `1` is added. -/
theorem pt_bound {h : ℕ} (hh : 0 < h) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : (h : ℝ) * φ < 1)
    {i : ℕ} (hi : i < h) {x : ℝ}
    (hxl : (h : ℝ) * φ + i - 1 < h * x) (hxu : (h : ℝ) * x < h * φ + i + 1) :
    F (φ + ((i : ℝ) + 1) / h) - (if i = 0 then 1 else 0) ≤ F (Int.fract x) ∧
      F (Int.fract x) ≤ F (φ + ((i : ℝ) - 1) / h) + (if i = h - 1 then 1 else 0) := by
  have hpos : (0 : ℝ) < h := Nat.cast_pos.2 hh
  have hFx := h01 (Int.fract x)
  have e1 : φ + ((i : ℝ) + 1) / h = (h * φ + i + 1) / h := by field_simp; ring
  have e2 : φ + ((i : ℝ) - 1) / h = (h * φ + i - 1) / h := by field_simp; ring
  rcases lt_or_ge x 0 with hx0 | hx0
  · -- `x < 0`: `i = 0`
    have hhx : (h : ℝ) * x < 0 := mul_neg_of_pos_of_neg hpos hx0
    have hi1 : (i : ℝ) < 1 := by nlinarith
    have hi0 : i = 0 := by
      have : i < 1 := by exact_mod_cast hi1
      omega
    subst hi0
    have hlt : φ + (((0 : ℕ) : ℝ) - 1) / h < 0 := by
      rw [e2, div_neg_iff]; right; exact ⟨by simp; linarith, hpos⟩
    rw [hneg _ hlt]
    have := (h01 (φ + (((0 : ℕ) : ℝ) + 1) / h)).2
    constructor
    · simp only [if_true]; linarith
    · split_ifs <;> linarith
  rcases lt_or_ge x 1 with hx1 | hx1
  · -- `0 ≤ x < 1`
    rw [Int.fract_eq_self.2 ⟨hx0, hx1⟩]
    have hle1 : x ≤ φ + ((i : ℝ) + 1) / h := by
      rw [e1, le_div_iff₀ hpos]; linarith
    have hle2 : φ + ((i : ℝ) - 1) / h ≤ x := by
      rw [e2, div_le_iff₀ hpos]; linarith
    have a1 := hF hle1
    have a2 := hF hle2
    constructor
    · split_ifs <;> linarith
    · split_ifs <;> linarith
  · -- `x ≥ 1`: `i = h - 1`
    have hhx : (h : ℝ) ≤ h * x := by nlinarith
    have hih : i + 1 = h := by
      have : (h : ℝ) < i + 2 := by linarith
      have : h < i + 2 := by exact_mod_cast this
      omega
    have hic : (i : ℝ) + 1 = h := by exact_mod_cast hih
    have hφpos : 0 < φ := by
      have : (0 : ℝ) < h * φ := by nlinarith
      exact pos_of_mul_pos_right this hpos.le
    have hz : F (φ + ((i : ℝ) + 1) / h) = 0 := by
      apply hbig
      rw [hic, div_self hpos.ne']; linarith
    have hi' : i = h - 1 := by omega
    have := (h01 (φ + ((i : ℝ) - 1) / h)).1
    constructor
    · rw [hz]; split_ifs <;> linarith
    · rw [if_pos hi']; linarith

end Point

/-- If `A` and `h` are coprime, then `k ↦ (m + kA) mod h` is a bijection of `range h`. -/
theorem sum_perm {h : ℕ} (hh : 0 < h) {A : ℤ} (hcop : IsCoprime A (h : ℤ)) (m : ℤ) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.range h, g ((m + (k : ℤ) * A) % (h : ℤ)).toNat = ∑ i ∈ Finset.range h, g i := by
  set σ : ℕ → ℕ := fun k => ((m + (k : ℤ) * A) % (h : ℤ)).toNat with hσ
  have hhz : (0 : ℤ) < h := by exact_mod_cast hh
  have hmaps : ∀ k ∈ Finset.range h, σ k ∈ Finset.range h := by
    intro k _
    have h1 := Int.emod_lt_of_pos (m + (k : ℤ) * A) hhz
    have h2 := Int.emod_nonneg (m + (k : ℤ) * A) hhz.ne'
    rw [Finset.mem_range, hσ]
    simp only
    omega
  have hinj : ∀ k₁ ∈ Finset.range h, ∀ k₂ ∈ Finset.range h, σ k₁ = σ k₂ → k₁ = k₂ := by
    intro k₁ hk₁ k₂ hk₂ heq
    rw [Finset.mem_range] at hk₁ hk₂
    have n1 := Int.emod_nonneg (m + (k₁ : ℤ) * A) hhz.ne'
    have n2 := Int.emod_nonneg (m + (k₂ : ℤ) * A) hhz.ne'
    have heq' : (m + (k₁ : ℤ) * A) % h = (m + (k₂ : ℤ) * A) % h := by
      simp only [hσ] at heq
      omega
    have hdvd : (h : ℤ) ∣ ((k₁ : ℤ) - k₂) * A := by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at heq'
      have := Int.dvd_of_emod_eq_zero heq'
      have e : m + (k₁ : ℤ) * A - (m + (k₂ : ℤ) * A) = ((k₁ : ℤ) - k₂) * A := by ring
      rwa [e] at this
    have hd : (h : ℤ) ∣ (k₁ : ℤ) - k₂ := hcop.symm.dvd_of_dvd_mul_right hdvd
    have habs : |(k₁ : ℤ) - k₂| < h := abs_lt.2 ⟨by omega, by omega⟩
    have := Int.eq_zero_of_abs_lt_dvd hd habs
    omega
  have himg : (Finset.range h).image σ = Finset.range h := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      exact hmaps k hk
    · rw [Finset.card_image_of_injOn (fun a ha b hb hab => hinj a ha b hb hab)]
  calc ∑ k ∈ Finset.range h, g (σ k) = ∑ i ∈ (Finset.range h).image σ, g i :=
        (Finset.sum_image hinj).symm
    _ = ∑ i ∈ Finset.range h, g i := by rw [himg]

section Block

variable {F : ℝ → ℝ} (hF : Antitone F) (h01 : ∀ t, 0 ≤ F t ∧ F t ≤ 1)
  (hneg : ∀ t, t < 0 → F t = 1) (hbig : ∀ t, 1 < t → F t = 0)
include hF h01 hneg hbig

/-- **One block**: if `λ = A/h + η` (`A` and `h` coprime, `h²|η| < 1`), then the sum over the `h` consecutive points
`{θ + kλ}` (`k < h`) differs from `h ∫₀¹ F` by at most `5`. -/
theorem block_bound {h : ℕ} (hh : 0 < h) {A : ℤ} (hcop : IsCoprime A (h : ℤ)) {η : ℝ}
    (hη : (h : ℝ) * h * |η| < 1) (θ : ℝ) :
    |∑ k ∈ Finset.range h, F (Int.fract (θ + k * ((A : ℝ) / h + η)))
        - h * ∫ t in (0 : ℝ)..1, F t| ≤ 5 := by
  have hpos : (0 : ℝ) < h := Nat.cast_pos.2 hh
  have hhz : (0 : ℤ) < h := by exact_mod_cast hh
  set m : ℤ := ⌊(h : ℝ) * θ⌋ with hm
  set φ : ℝ := θ - m / h with hφ
  have hhφ : (h : ℝ) * φ = h * θ - m := by rw [hφ]; field_simp
  have hφ0 : 0 ≤ φ := by
    have : (m : ℝ) ≤ h * θ := Int.floor_le _
    have : 0 ≤ (h : ℝ) * φ := by linarith
    exact nonneg_of_mul_nonneg_right (by linarith) hpos
  have hφ1 : (h : ℝ) * φ < 1 := by
    have : (h : ℝ) * θ < m + 1 := Int.lt_floor_add_one _
    linarith
  set lo : ℕ → ℝ := fun j => F (φ + ((j : ℝ) + 1) / h) - (if j = 0 then 1 else 0) with hlo
  set hi : ℕ → ℝ := fun j => F (φ + ((j : ℝ) - 1) / h) + (if j = h - 1 then 1 else 0) with hhi
  set σ : ℕ → ℕ := fun k => ((m + (k : ℤ) * A) % (h : ℤ)).toNat with hσ
  have hk : ∀ k ∈ Finset.range h, lo (σ k) ≤ F (Int.fract (θ + k * ((A : ℝ) / h + η))) ∧
      F (Int.fract (θ + k * ((A : ℝ) / h + η))) ≤ hi (σ k) := by
    intro k hkr
    rw [Finset.mem_range] at hkr
    have n1 := Int.emod_nonneg (m + (k : ℤ) * A) hhz.ne'
    have n2 := Int.emod_lt_of_pos (m + (k : ℤ) * A) hhz
    have hσlt : σ k < h := by simp only [hσ]; omega
    have hσc : ((σ k : ℕ) : ℤ) = (m + (k : ℤ) * A) % (h : ℤ) := by
      simp only [hσ]; exact Int.toNat_of_nonneg n1
    have hσr : ((σ k : ℕ) : ℝ) = (((m + (k : ℤ) * A) % (h : ℤ) : ℤ) : ℝ) := by
      rw [← hσc]; rfl
    set N : ℤ := (m + (k : ℤ) * A) / h with hN
    have hdec : (h : ℤ) * N + (m + (k : ℤ) * A) % (h : ℤ) = m + (k : ℤ) * A := Int.mul_ediv_add_emod _ _
    have hdecR : (h : ℝ) * N + (σ k : ℝ) = m + k * A := by
      rw [hσr]; exact_mod_cast hdec
    have harg : θ + k * ((A : ℝ) / h + η) = (φ + (σ k : ℝ) / h + k * η) + N := by
      have : (σ k : ℝ) = m + k * A - h * N := by linarith
      rw [this, hφ]
      field_simp
      ring
    rw [harg, Int.fract_add_intCast]
    have hkη : |(h : ℝ) * (k * η)| < 1 := by
      rw [abs_mul, abs_mul, abs_of_pos hpos, abs_of_nonneg (Nat.cast_nonneg k)]
      have : (k : ℝ) ≤ h := by exact_mod_cast hkr.le
      calc (h : ℝ) * (k * |η|) ≤ h * (h * |η|) := by gcongr
        _ = h * h * |η| := by ring
        _ < 1 := hη
    have hx : (h : ℝ) * (φ + (σ k : ℝ) / h + k * η) = h * φ + σ k + h * (k * η) := by
      field_simp
    obtain ⟨a1, a2⟩ := abs_lt.1 hkη
    exact pt_bound hF h01 hneg hbig hh hφ0 hφ1 hσlt (by rw [hx]; linarith) (by rw [hx]; linarith)
  have hsum_lo := Finset.sum_le_sum (fun k hk' => (hk k hk').1)
  have hsum_hi := Finset.sum_le_sum (fun k hk' => (hk k hk').2)
  rw [sum_perm hh hcop m lo] at hsum_lo
  rw [sum_perm hh hcop m hi] at hsum_hi
  have hl : ∑ i ∈ Finset.range h, lo i
      = ∑ i ∈ Finset.range h, F (φ + ((i : ℝ) + 1) / h) - 1 := by
    simp only [hlo, Finset.sum_sub_distrib]
    congr 1
    simp [Finset.mem_range, hh]
  have hu : ∑ i ∈ Finset.range h, hi i
      = ∑ i ∈ Finset.range h, F (φ + ((i : ℝ) - 1) / h) + 1 := by
    simp only [hhi, Finset.sum_add_distrib]
    congr 1
    simp [Finset.mem_range, hh]
  have r1 := riemann_lo hF h01 hh hφ0 hφ1
  have r2 := riemann_hi hF h01 hh hφ0 hφ1
  rw [abs_le]
  constructor <;> linarith

end Block

section Chain

variable {F : ℝ → ℝ} (h01 : ∀ t, 0 ≤ F t ∧ F t ≤ 1)
include h01

/-- The leftover block: `|Σ_{k < r} F({θ + kλ}) - r ∫₀¹ F| ≤ r` (trivial bound). -/
theorem rem_bound (lam θ : ℝ) (r : ℕ) :
    |∑ k ∈ Finset.range r, F (Int.fract (θ + k * lam)) - r * ∫ t in (0 : ℝ)..1, F t| ≤ r := by
  have hI := integral_mem h01
  have s0 : 0 ≤ ∑ k ∈ Finset.range r, F (Int.fract (θ + k * lam)) :=
    Finset.sum_nonneg (fun k _ => (h01 _).1)
  have s1 : ∑ k ∈ Finset.range r, F (Int.fract (θ + k * lam)) ≤ r := by
    calc ∑ k ∈ Finset.range r, F (Int.fract (θ + k * lam)) ≤ ∑ k ∈ Finset.range r, (1 : ℝ) :=
          Finset.sum_le_sum (fun k _ => (h01 _).2)
      _ = r := by simp
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  rw [abs_le]
  constructor <;> nlinarith

/-- **Chaining the blocks**: if the error of one block is at most `5`, then the error for `mh + r` points is at most `5m + r`. -/
theorem chain_bound {lam : ℝ} {h : ℕ}
    (hblock : ∀ θ : ℝ, |∑ k ∈ Finset.range h, F (Int.fract (θ + k * lam))
        - h * ∫ t in (0 : ℝ)..1, F t| ≤ 5) (m r : ℕ) (θ : ℝ) :
    |∑ k ∈ Finset.range (m * h + r), F (Int.fract (θ + k * lam))
        - ((m * h + r : ℕ) : ℝ) * ∫ t in (0 : ℝ)..1, F t| ≤ 5 * m + r := by
  induction m generalizing θ with
  | zero => simpa using rem_bound h01 lam θ r
  | succ m ih =>
    have e : (m + 1) * h + r = h + (m * h + r) := by ring
    rw [e, Finset.sum_range_add]
    have hshift : ∑ k ∈ Finset.range (m * h + r), F (Int.fract (θ + ((h + k : ℕ) : ℝ) * lam))
        = ∑ k ∈ Finset.range (m * h + r), F (Int.fract ((θ + h * lam) + k * lam)) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      congr 2
      push_cast
      ring
    rw [hshift]
    have h1 := hblock θ
    have h2 := ih (θ + h * lam)
    have ecast : ((h + (m * h + r) : ℕ) : ℝ) = h + ((m * h + r : ℕ) : ℝ) := by push_cast; ring
    rw [ecast]
    push_cast at h2 ⊢
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith

end Chain

/-- A sum over an integer interval as a sum over `range`. -/
theorem sum_Ico_int {M : Type*} [AddCommMonoid M] (a : ℤ) (L : ℕ) (g : ℤ → M) :
    ∑ n ∈ Finset.Ico a (a + L), g n = ∑ j ∈ Finset.range L, g (a + j) := by
  rw [Int.Ico_eq_finset_map, Finset.sum_map]
  simp

/-- **Main body of the (KRON) block form** (the unfolded form of `kron_statement`, with the irrationality-measure hypothesis also unfolded).
The constant is `C = 5 c^{-1/(μ-1)} + 2`. -/
theorem kron_main {lam c μ : ℝ} (hc : 0 < c) (hμ : 2 ≤ μ)
    (hirr : ∀ h : ℕ, 1 ≤ h → ∀ m : ℤ, c * (h : ℝ) ^ (-(μ - 1)) ≤ |(h : ℝ) * lam - m|) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ, AntitoneOn f (Set.Icc 0 1) →
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f θ ∧ f θ ≤ 1) →
      ∀ (u : ℝ) (a : ℤ) (ℓ : ℕ), 1 ≤ ℓ →
        |∑ n ∈ Finset.Ico a (a + ℓ), f (Int.fract ((n : ℝ) * lam + u))
            - (ℓ : ℝ) * ∫ θ in (0 : ℝ)..1, f θ| ≤ C * (ℓ : ℝ) ^ (1 - 1 / μ) := by
  have hμ1 : 0 < μ - 1 := by linarith
  have hμ0 : 0 < μ := by linarith
  set K : ℝ := c ^ (-(1 / (μ - 1))) with hK
  have hKpos : 0 < K := Real.rpow_pos_of_pos hc _
  refine ⟨5 * K + 2, by positivity, ?_⟩
  intro f hf hf01 u a ℓ hℓ
  set F := extF f with hFdef
  have hF : Antitone F := extF_antitone hf hf01
  have h01 : ∀ t, 0 ≤ F t ∧ F t ≤ 1 := extF_mem hf01
  have hneg : ∀ t, t < 0 → F t = 1 := fun t ht => extF_neg ht
  have hbig : ∀ t, 1 < t → F t = 0 := fun t ht => extF_big ht
  -- the sum as a sum of `F` over `range`
  set θ : ℝ := (a : ℝ) * lam + u with hθ
  have hsum : ∑ n ∈ Finset.Ico a (a + ℓ), f (Int.fract ((n : ℝ) * lam + u))
      = ∑ k ∈ Finset.range ℓ, F (Int.fract (θ + k * lam)) := by
    rw [sum_Ico_int]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have e : ((a + (k : ℤ) : ℤ) : ℝ) * lam + u = θ + k * lam := by rw [hθ]; push_cast; ring
    rw [e, hFdef, extF_eq ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩]
  rw [hsum, ← extF_integral (f := f)]
  -- Dirichlet approximation
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  set e : ℝ := 1 - 1 / μ with he
  have he0 : 0 ≤ e := by
    rw [he, sub_nonneg, div_le_one hμ0]; linarith
  have hℓe : 1 ≤ (ℓ : ℝ) ^ e := Real.one_le_rpow hℓr he0
  set Q : ℕ := ⌈(ℓ : ℝ) ^ e⌉₊ with hQ
  have hQpos : 0 < Q := Nat.ceil_pos.2 (by linarith)
  have hQge : (ℓ : ℝ) ^ e ≤ Q := Nat.le_ceil _
  have hQlt : (Q : ℝ) < (ℓ : ℝ) ^ e + 1 := Nat.ceil_lt_add_one (by linarith)
  obtain ⟨q, hq1, hq2⟩ := Real.exists_rat_abs_sub_le_and_den_le lam hQpos
  set h : ℕ := q.den with hhdef
  have hh : 0 < h := q.den_pos
  have hpos : (0 : ℝ) < h := Nat.cast_pos.2 hh
  have hhQ : (h : ℝ) ≤ Q := by exact_mod_cast hq2
  have hcop : IsCoprime q.num (h : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using q.reduced
  set η : ℝ := lam - q with hη
  have hq : (q : ℝ) = (q.num : ℝ) / h := by rw [Rat.cast_def]
  have hlam : lam = (q.num : ℝ) / h + η := by rw [hη, hq]; ring
  have hQ1 : (0 : ℝ) < Q + 1 := by positivity
  have hηb : |η| ≤ 1 / ((Q + 1) * h) := hq1
  have hhη : (h : ℝ) * |η| ≤ 1 / (Q + 1) := by
    rw [le_div_iff₀ hQ1]
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < (Q + 1) * h)).1 hηb
    linarith
  have hη2 : (h : ℝ) * h * |η| < 1 := by
    have : (h : ℝ) * (h * |η|) ≤ h * (1 / (Q + 1)) := by gcongr
    have : (h : ℝ) * (1 / (Q + 1)) < 1 := by
      rw [mul_one_div, div_lt_one hQ1]; linarith
    nlinarith
  -- one block, and chaining the blocks
  have hblock : ∀ θ' : ℝ, |∑ k ∈ Finset.range h, F (Int.fract (θ' + k * lam))
      - h * ∫ t in (0 : ℝ)..1, F t| ≤ 5 := by
    intro θ'
    rw [hlam]
    exact block_bound hF h01 hneg hbig hh hcop hη2 θ'
  have hdm := Nat.div_add_mod' ℓ h
  have hchain := chain_bound h01 hblock (ℓ / h) (ℓ % h) θ
  rw [hdm] at hchain
  refine hchain.trans ?_
  -- irrationality measure: `c (Q+1) ≤ h^{μ-1}`
  have hirr' := hirr h hh q.num
  have hdiff : |(h : ℝ) * lam - q.num| = h * |η| := by
    rw [hlam, mul_add, mul_div_cancel₀ _ hpos.ne', add_sub_cancel_left, abs_mul, abs_of_pos hpos]
  rw [hdiff] at hirr'
  have hhpow : 0 < (h : ℝ) ^ (μ - 1) := Real.rpow_pos_of_pos hpos _
  have hcQ : c * (Q + 1) ≤ (h : ℝ) ^ (μ - 1) := by
    rw [Real.rpow_neg hpos.le] at hirr'
    have := hirr'.trans hhη
    rw [mul_inv_le_iff₀ hhpow] at this
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hQ1] at this
    linarith
  have hcl : c * (ℓ : ℝ) ^ e ≤ (h : ℝ) ^ (μ - 1) := by nlinarith
  -- `ℓ^{1/μ} ≤ K h`
  have hℓ0 : (0 : ℝ) ≤ ℓ := by linarith
  have hsplit : (ℓ : ℝ) ^ e = ((ℓ : ℝ) ^ (1 / μ)) ^ (μ - 1) := by
    rw [← Real.rpow_mul hℓ0, he]; congr 1; field_simp
  have hKh : ((K * h : ℝ)) ^ (μ - 1) = (h : ℝ) ^ (μ - 1) / c := by
    rw [Real.mul_rpow hKpos.le hpos.le, hK, ← Real.rpow_mul hc.le]
    have : -(1 / (μ - 1)) * (μ - 1) = -1 := by field_simp
    rw [this, Real.rpow_neg_one]; field_simp
  have hroot : (ℓ : ℝ) ^ (1 / μ) ≤ K * h := by
    rw [← Real.rpow_le_rpow_iff (Real.rpow_nonneg hℓ0 _) (by positivity) hμ1, ← hsplit, hKh,
      le_div_iff₀ hc]
    linarith
  have hℓsplit : (ℓ : ℝ) = (ℓ : ℝ) ^ e * (ℓ : ℝ) ^ (1 / μ) := by
    rw [← Real.rpow_add (by linarith), he]; simp
  have hdiv : (ℓ : ℝ) / h ≤ K * (ℓ : ℝ) ^ e := by
    rw [div_le_iff₀ hpos]
    calc (ℓ : ℝ) = (ℓ : ℝ) ^ e * (ℓ : ℝ) ^ (1 / μ) := hℓsplit
      _ ≤ (ℓ : ℝ) ^ e * (K * h) := by gcongr
      _ = K * (ℓ : ℝ) ^ e * h := by ring
  have hm : ((ℓ / h : ℕ) : ℝ) ≤ (ℓ : ℝ) / h := Nat.cast_div_le
  have hr : ((ℓ % h : ℕ) : ℝ) ≤ Q := by
    have : ℓ % h < h := Nat.mod_lt _ hh
    have : ((ℓ % h : ℕ) : ℝ) < h := by exact_mod_cast this
    linarith
  nlinarith

section Weighted

/-- Variation within a block: `|v(b+k) - v(b)| ≤ Σ_{i<k} |v(b+i+1) - v(b+i)|`. -/
theorem var_bound (v : ℕ → ℝ) (b : ℕ) :
    ∀ k : ℕ, |v (b + k) - v b| ≤ ∑ i ∈ Finset.range k, |v (b + i + 1) - v (b + i)| := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    calc |v (b + (k + 1)) - v b| = |(v (b + k + 1) - v (b + k)) + (v (b + k) - v b)| := by
          rw [← add_assoc]; ring_nf
      _ ≤ |v (b + k + 1) - v (b + k)| + |v (b + k) - v b| := abs_add_le _ _
      _ ≤ _ := by linarith

/-- **Freezing the weight at the left end of the block** (one block). -/
theorem wblock (v G : ℕ → ℝ) (hv : ∀ j, 0 ≤ v j) (hG : ∀ j, |G j| ≤ 1) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {Kb : ℝ} (hKb : 0 ≤ Kb) (b : ℕ) (hblk : |∑ k ∈ Finset.range ℓ, G (b + k)| ≤ Kb) :
    |∑ k ∈ Finset.range ℓ, v (b + k) * G (b + k)| ≤
      ℓ * ∑ k ∈ Finset.range ℓ, |v (b + k + 1) - v (b + k)|
        + Kb * ((∑ k ∈ Finset.range ℓ, v (b + k)) / ℓ
          + ∑ k ∈ Finset.range ℓ, |v (b + k + 1) - v (b + k)|) := by
  set DB := ∑ k ∈ Finset.range ℓ, |v (b + k + 1) - v (b + k)| with hDB
  set WB := ∑ k ∈ Finset.range ℓ, v (b + k) with hWB
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hvar : ∀ k ∈ Finset.range ℓ, |v (b + k) - v b| ≤ DB := by
    intro k hk
    refine (var_bound v b k).trans ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_subset_range.2 (Finset.mem_range.1 hk).le
    · intro i _ _; exact abs_nonneg _
  have hsplit : ∑ k ∈ Finset.range ℓ, v (b + k) * G (b + k)
      = v b * ∑ k ∈ Finset.range ℓ, G (b + k)
        + ∑ k ∈ Finset.range ℓ, (v (b + k) - v b) * G (b + k) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have t1 : |v b * ∑ k ∈ Finset.range ℓ, G (b + k)| ≤ v b * Kb := by
    rw [abs_mul, abs_of_nonneg (hv b)]
    exact mul_le_mul_of_nonneg_left hblk (hv b)
  have t2 : |∑ k ∈ Finset.range ℓ, (v (b + k) - v b) * G (b + k)| ≤ ℓ * DB := by
    calc _ ≤ ∑ k ∈ Finset.range ℓ, |(v (b + k) - v b) * G (b + k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range ℓ, DB := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          rw [abs_mul]
          have := hvar k hk
          have := hG (b + k)
          have := abs_nonneg (G (b + k))
          have := abs_nonneg (v (b + k) - v b)
          nlinarith
      _ = ℓ * DB := by simp
  have hvb : (ℓ : ℝ) * v b ≤ WB + ℓ * DB := by
    calc (ℓ : ℝ) * v b = ∑ k ∈ Finset.range ℓ, v b := by simp
      _ ≤ ∑ k ∈ Finset.range ℓ, (v (b + k) + DB) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          have := hvar k hk
          have := neg_abs_le (v (b + k) - v b)
          linarith
      _ = WB + ℓ * DB := by rw [Finset.sum_add_distrib, hWB]; simp
  have hvb' : v b ≤ WB / ℓ + DB := by
    rw [div_add' _ _ _ hℓr.ne', le_div_iff₀ hℓr]; linarith
  rw [hsplit]
  calc _ ≤ |v b * ∑ k ∈ Finset.range ℓ, G (b + k)|
        + |∑ k ∈ Finset.range ℓ, (v (b + k) - v b) * G (b + k)| := abs_add_le _ _
    _ ≤ v b * Kb + ℓ * DB := add_le_add t1 t2
    _ ≤ (WB / ℓ + DB) * Kb + ℓ * DB := by gcongr
    _ = _ := by ring

/-- **Chaining the blocks** (weighted): for `m` blocks, the right-hand side is the sum of the right-hand sides of the blocks. -/
theorem wchain (v G : ℕ → ℝ) (hv : ∀ j, 0 ≤ v j) (hG : ∀ j, |G j| ≤ 1) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {Kb : ℝ} (hKb : 0 ≤ Kb) (hblk : ∀ b : ℕ, |∑ k ∈ Finset.range ℓ, G (b + k)| ≤ Kb) (m : ℕ) :
    |∑ j ∈ Finset.range (m * ℓ), v j * G j| ≤
      ℓ * ∑ j ∈ Finset.range (m * ℓ), |v (j + 1) - v j|
        + Kb * ((∑ j ∈ Finset.range (m * ℓ), v j) / ℓ
          + ∑ j ∈ Finset.range (m * ℓ), |v (j + 1) - v j|) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : (m + 1) * ℓ = m * ℓ + ℓ := by ring
    rw [e, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]
    have hb := wblock v G hv hG hℓ hKb (m * ℓ) (hblk (m * ℓ))
    calc _ ≤ |∑ j ∈ Finset.range (m * ℓ), v j * G j|
          + |∑ k ∈ Finset.range ℓ, v (m * ℓ + k) * G (m * ℓ + k)| := abs_add_le _ _
      _ ≤ _ := add_le_add ih hb
      _ = _ := by rw [add_div]; ring

end Weighted

/-- **Main body of the (KRON) weighted form** (the unfolded form of `kron_statement ⟹ kronW_statement`). The constant is the `C` of the block form. -/
theorem kronW_main {lam μ : ℝ}
    (hk : ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ, AntitoneOn f (Set.Icc 0 1) →
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f θ ∧ f θ ≤ 1) →
      ∀ (u : ℝ) (a : ℤ) (ℓ : ℕ), 1 ≤ ℓ →
        |∑ n ∈ Finset.Ico a (a + ℓ), f (Int.fract ((n : ℝ) * lam + u))
            - (ℓ : ℝ) * ∫ θ in (0 : ℝ)..1, f θ| ≤ C * (ℓ : ℝ) ^ (1 - 1 / μ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ, AntitoneOn f (Set.Icc 0 1) →
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f θ ∧ f θ ≤ 1) →
      ∀ (u : ℝ) (a : ℤ) (L : ℕ) (w : ℤ → ℝ), (∀ n, 0 ≤ w n) →
      (∀ n, n ∉ Finset.Ico a (a + L) → w n = 0) → ∀ ℓ : ℕ, 1 ≤ ℓ →
        |∑ n ∈ Finset.Ico a (a + L), w n * f (Int.fract ((n : ℝ) * lam + u))
            - (∑ n ∈ Finset.Ico a (a + L), w n) * ∫ θ in (0 : ℝ)..1, f θ|
          ≤ 3 * ℓ * (∑ n ∈ Finset.Ico (a - 1) (a + L), |w (n + 1) - w n|)
            + C * ((∑ n ∈ Finset.Ico a (a + L), w n) * (ℓ : ℝ) ^ (-(1 / μ))
              + (∑ n ∈ Finset.Ico (a - 1) (a + L), |w (n + 1) - w n|) * (ℓ : ℝ) ^ (1 - 1 / μ)) := by
  obtain ⟨C₀, hC₀, hk⟩ := hk
  refine ⟨C₀, hC₀, ?_⟩
  intro f hf hf01 u a L w hw hsupp ℓ hℓ
  set I : ℝ := ∫ θ in (0 : ℝ)..1, f θ with hIdef
  have hI : 0 ≤ I ∧ I ≤ 1 := by
    rw [hIdef, ← extF_integral (f := f)]
    exact integral_mem (extF_mem hf01)
  set v : ℕ → ℝ := fun j => w (a + (j : ℤ)) with hvdef
  set G : ℕ → ℝ := fun j => f (Int.fract (((a + (j : ℤ) : ℤ) : ℝ) * lam + u)) - I with hGdef
  have hv : ∀ j, 0 ≤ v j := fun j => hw _
  have hG : ∀ j, |G j| ≤ 1 := by
    intro j
    have := hf01 (Int.fract (((a + (j : ℤ) : ℤ) : ℝ) * lam + u))
      ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    simp only [hGdef]
    rw [abs_le]; constructor <;> linarith
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  set Kb : ℝ := C₀ * (ℓ : ℝ) ^ (1 - 1 / μ) with hKbdef
  have hKb : 0 ≤ Kb := by positivity
  have hblk : ∀ b : ℕ, |∑ k ∈ Finset.range ℓ, G (b + k)| ≤ Kb := by
    intro b
    have h1 := hk f hf hf01 u (a + b) ℓ hℓ
    rw [sum_Ico_int] at h1
    have e : ∑ k ∈ Finset.range ℓ, G (b + k)
        = ∑ j ∈ Finset.range ℓ, f (Int.fract ((((a + b) + (j : ℤ) : ℤ) : ℝ) * lam + u))
          - ℓ * I := by
      simp only [hGdef, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      congr 1
      refine Finset.sum_congr rfl (fun k _ => ?_)
      congr 3
      push_cast
      ring
    rw [e]
    exact h1
  -- the left-hand side as a sum over `range`
  have hLHS : ∑ n ∈ Finset.Ico a (a + L), w n * f (Int.fract ((n : ℝ) * lam + u))
      - (∑ n ∈ Finset.Ico a (a + L), w n) * I = ∑ j ∈ Finset.range L, v j * G j := by
    rw [sum_Ico_int, sum_Ico_int, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [hvdef, hGdef]
    ring
  have hW : ∑ n ∈ Finset.Ico a (a + L), w n = ∑ j ∈ Finset.range L, v j := sum_Ico_int _ _ _
  -- the variation `V = w(a) + Σ_{j<L} |v(j+1) - v(j)|`
  set D : ℝ := ∑ j ∈ Finset.range L, |v (j + 1) - v j| with hDdef
  have hV : ∑ n ∈ Finset.Ico (a - 1) (a + L), |w (n + 1) - w n| = w a + D := by
    have e : a + (L : ℤ) = (a - 1) + ((L + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e, sum_Ico_int, Finset.sum_range_succ']
    have hw0 : w (a - 1) = 0 := hsupp _ (by simp)
    rw [add_comm]
    congr 1
    · simp [hw0, abs_of_nonneg (hw a)]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hvdef]
      have e1 : a - 1 + ((i + 1 : ℕ) : ℤ) + 1 = a + ((i + 1 : ℕ) : ℤ) := by push_cast; ring
      have e2 : a - 1 + ((i + 1 : ℕ) : ℤ) = a + (i : ℤ) := by push_cast; ring
      rw [e1, e2]
  set V : ℝ := ∑ n ∈ Finset.Ico (a - 1) (a + L), |w (n + 1) - w n| with hVdef
  have hD0 : 0 ≤ D := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hDV : D ≤ V := by rw [hV]; linarith [hw a]
  have hV0 : 0 ≤ V := by linarith
  have hvV : ∀ j, j ≤ L → v j ≤ V := by
    intro j hj
    have h1 := var_bound v 0 j
    simp only [zero_add] at h1
    have h2 : ∑ i ∈ Finset.range j, |v (i + 1) - v i| ≤ D := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hj)
      intro i _ _; exact abs_nonneg _
    have h3 : v 0 = w a := by simp [hvdef]
    have := le_abs_self (v j - v 0)
    rw [hV]; linarith
  -- blocks and the leftover
  set m : ℕ := L / ℓ with hm
  set r : ℕ := L % ℓ with hr
  have hmr : m * ℓ + r = L := Nat.div_add_mod' L ℓ
  have hrl : r < ℓ := Nat.mod_lt _ hℓ
  have hsplit : ∑ j ∈ Finset.range L, v j * G j
      = ∑ j ∈ Finset.range (m * ℓ), v j * G j
        + ∑ k ∈ Finset.range r, v (m * ℓ + k) * G (m * ℓ + k) := by
    rw [← Finset.sum_range_add, hmr]
  have wc := wchain v G hv hG hℓ hKb hblk m
  have hrem : |∑ k ∈ Finset.range r, v (m * ℓ + k) * G (m * ℓ + k)| ≤ ℓ * V := by
    calc _ ≤ ∑ k ∈ Finset.range r, |v (m * ℓ + k) * G (m * ℓ + k)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range r, V := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          rw [Finset.mem_range] at hk
          rw [abs_mul, abs_of_nonneg (hv _)]
          have a1 := hvV (m * ℓ + k) (by omega)
          have a2 := hG (m * ℓ + k)
          have a3 := abs_nonneg (G (m * ℓ + k))
          have a4 := hv (m * ℓ + k)
          nlinarith
      _ = r * V := by simp
      _ ≤ ℓ * V := by
          have : (r : ℝ) ≤ ℓ := by exact_mod_cast hrl.le
          exact mul_le_mul_of_nonneg_right this hV0
  have hmL : m * ℓ ≤ L := by omega
  have hD' : ∑ j ∈ Finset.range (m * ℓ), |v (j + 1) - v j| ≤ V := by
    refine le_trans ?_ hDV
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hmL)
    intro i _ _; exact abs_nonneg _
  have hW' : ∑ j ∈ Finset.range (m * ℓ), v j ≤ ∑ j ∈ Finset.range L, v j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hmL)
    intro i _ _; exact hv i
  have hD'0 : 0 ≤ ∑ j ∈ Finset.range (m * ℓ), |v (j + 1) - v j| :=
    Finset.sum_nonneg (fun j _ => abs_nonneg _)
  -- rewriting the power `ℓ^{1-1/μ} = ℓ · ℓ^{-1/μ}`
  have hpow : (ℓ : ℝ) ^ (1 - 1 / μ) = ℓ * (ℓ : ℝ) ^ (-(1 / μ)) := by
    rw [sub_eq_add_neg, Real.rpow_add hℓr, Real.rpow_one]
  rw [hLHS, hsplit]
  set W : ℝ := ∑ n ∈ Finset.Ico a (a + L), w n with hWdef
  have hWW : ∑ j ∈ Finset.range (m * ℓ), v j ≤ W := by rw [hW]; exact hW'
  have hKW : Kb * (W / ℓ) = C₀ * (W * (ℓ : ℝ) ^ (-(1 / μ))) := by
    rw [hKbdef, hpow]; field_simp
  have hmono : Kb * ((∑ j ∈ Finset.range (m * ℓ), v j) / ℓ
      + ∑ j ∈ Finset.range (m * ℓ), |v (j + 1) - v j|) ≤ Kb * (W / ℓ + V) := by
    gcongr
  have hℓD : (ℓ : ℝ) * ∑ j ∈ Finset.range (m * ℓ), |v (j + 1) - v j| ≤ ℓ * V :=
    mul_le_mul_of_nonneg_left hD' hℓr.le
  have hlast : Kb * (W / ℓ + V) = C₀ * (W * (ℓ : ℝ) ^ (-(1 / μ)) + V * (ℓ : ℝ) ^ (1 - 1 / μ)) := by
    rw [mul_add, hKW, hKbdef]; ring
  have hℓV : 0 ≤ (ℓ : ℝ) * V := mul_nonneg hℓr.le hV0
  calc _ ≤ |∑ j ∈ Finset.range (m * ℓ), v j * G j|
        + |∑ k ∈ Finset.range r, v (m * ℓ + k) * G (m * ℓ + k)| := abs_add_le _ _
    _ ≤ (ℓ * V + Kb * (W / ℓ + V)) + ℓ * V := by linarith
    _ ≤ 3 * ℓ * V + C₀ * (W * (ℓ : ℝ) ^ (-(1 / μ)) + V * (ℓ : ℝ) ^ (1 - 1 / μ)) := by
        rw [hlast]; linarith

end KronAux

end ND

end GGMCollatz
