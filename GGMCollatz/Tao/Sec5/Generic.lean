import GGMCollatz.Tao.Sec5.Defs

/-!
# General lemmas used in the first-passage construction (PMF events, total variation, harmonic sums)

Derived from `TaoCollatz/Sec5/Stabilization.lean` (`expect_map_indicator`, `dTV_passLoc_event_witness`)
and `TaoCollatz/Sec5/FirstPassage.lean` (`harmonic_ap_integral_bound`) of gotrevor/tao-collatz
(Apache-2.0), commit 15efca2; generalized to the form used in the proofs for the GGM family (p, q, r).
The lemmas in this file do not depend on `p`, `q`, `r`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

/-- The probability of an event under a pushforward is the probability of the preimage (tao-collatz's
`expect_map_indicator`). -/
theorem expect_map_indicator {α β : Type*} (μ : PMF α) (φ : α → β) (E : Set β) :
    expect (μ.map φ) (Set.indicator E 1) = expect μ (Set.indicator {a | φ a ∈ E} 1) := by
  classical
  unfold expect
  rw [← PMF.toReal_tsum_mul_ofReal (μ.map φ) (Set.indicator E 1)
        (fun b => Set.indicator_nonneg (fun _ _ => zero_le_one) b),
      PMF.tsum_map_mul μ φ (fun b => ENNReal.ofReal (Set.indicator E 1 b)),
      PMF.toReal_tsum_mul_ofReal μ (fun a => Set.indicator E 1 (φ a))
        (fun a => Set.indicator_nonneg (fun _ _ => zero_le_one) (φ a))]
  rfl

/-- Expectation of a nonnegative observable under a pushforward. -/
theorem expect_map_of_nonneg {α β : Type*} (μ : PMF α) (φ : α → β) (f : β → ℝ)
    (hf : ∀ b, 0 ≤ f b) : expect (μ.map φ) f = expect μ (fun a => f (φ a)) := by
  unfold expect
  rw [← PMF.toReal_tsum_mul_ofReal (μ.map φ) f hf,
      PMF.tsum_map_mul μ φ (fun b => ENNReal.ofReal (f b)),
      PMF.toReal_tsum_mul_ofReal μ (fun a => f (φ a)) (fun a => hf (φ a))]

/-- The real-valued probabilities sum to 1. -/
theorem tsum_toReal_eq_one {α : Type*} (μ : PMF α) : ∑' a, (μ a).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun a => μ.apply_ne_top a), μ.tsum_coe]; simp

/-- The real-valued probabilities are summable. -/
theorem summable_toReal {α : Type*} (μ : PMF α) : Summable fun a => (μ a).toReal :=
  ENNReal.summable_toReal (by rw [μ.tsum_coe]; exact ENNReal.one_ne_top)

/-- The expectation of a bounded observable is summable. -/
theorem summable_mul_of_bounded {α : Type*} (μ : PMF α) (f : α → ℝ) (B : ℝ)
    (hf : ∀ a, |f a| ≤ B) : Summable fun a => (μ a).toReal * f a := by
  refine Summable.of_norm_bounded (g := fun a => (μ a).toReal * B) ((summable_toReal μ).mul_right B) ?_
  intro a
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hf a) ENNReal.toReal_nonneg

/-- Monotonicity of expectation (bounded observables). -/
theorem expect_mono {α : Type*} (μ : PMF α) {f g : α → ℝ} (B : ℝ) (hf : ∀ a, |f a| ≤ B)
    (hg : ∀ a, |g a| ≤ B) (hfg : ∀ a, f a ≤ g a) : expect μ f ≤ expect μ g := by
  unfold expect
  exact (summable_mul_of_bounded μ f B hf).tsum_le_tsum
    (fun a => mul_le_mul_of_nonneg_left (hfg a) ENNReal.toReal_nonneg)
    (summable_mul_of_bounded μ g B hg)

/-- The indicator function of an event takes values in `[0, 1]`. -/
theorem abs_indicator_le_one {α : Type*} (E : Set α) (a : α) : |Set.indicator E (1 : α → ℝ) a| ≤ 1 := by
  by_cases h : a ∈ E
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- The probability of an event is nonnegative. -/
theorem expect_indicator_nonneg {α : Type*} (μ : PMF α) (E : Set α) :
    0 ≤ expect μ (Set.indicator E 1) := by
  unfold expect
  exact tsum_nonneg fun a => mul_nonneg ENNReal.toReal_nonneg
    (Set.indicator_nonneg (fun _ _ => zero_le_one) a)

/-- The probability of an event is at most 1. -/
theorem expect_indicator_le_one {α : Type*} (μ : PMF α) (E : Set α) :
    expect μ (Set.indicator E 1) ≤ 1 := by
  have h := expect_mono μ (f := Set.indicator E 1) (g := fun _ => 1) 1
    (abs_indicator_le_one E) (fun _ => by simp) (fun a => by
      by_cases h : a ∈ E
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h])
  refine h.trans (le_of_eq ?_)
  unfold expect
  simp only [mul_one]
  exact tsum_toReal_eq_one μ

/-- Monotonicity of the probability of events. -/
theorem expect_indicator_mono {α : Type*} (μ : PMF α) {E E' : Set α} (h : E ⊆ E') :
    expect μ (Set.indicator E 1) ≤ expect μ (Set.indicator E' 1) :=
  expect_mono μ 1 (abs_indicator_le_one E) (abs_indicator_le_one E')
    (fun a => Set.indicator_le_indicator_of_subset h (fun _ => zero_le_one) a)

/-- The total variation (full `ℓ¹`) is at most 2. -/
theorem dTV_le_two {α : Type*} (μ ν : PMF α) : dTV μ ν ≤ 2 := by
  unfold dTV
  have hμ := summable_toReal μ
  have hν := summable_toReal ν
  have hle : ∀ a, |(μ a).toReal - (ν a).toReal| ≤ (μ a).toReal + (ν a).toReal := by
    intro a
    rw [abs_le]
    constructor <;> linarith [(ENNReal.toReal_nonneg : 0 ≤ (μ a).toReal),
      (ENNReal.toReal_nonneg : 0 ≤ (ν a).toReal)]
  calc ∑' a, |(μ a).toReal - (ν a).toReal| ≤ ∑' a, ((μ a).toReal + (ν a).toReal) :=
        ((hμ.sub hν).abs).tsum_le_tsum hle (hμ.add hν)
    _ = 2 := by rw [hμ.tsum_add hν, tsum_toReal_eq_one, tsum_toReal_eq_one]; norm_num

/-- **Bounding the total variation by events**: if the difference of probabilities is at most `δ` for
every event, then the total variation (`ℓ¹`) is at most `2δ` (general form of tao-collatz's
`dTV_passLoc_event_witness`; equality at the Hahn set `{μ ≥ ν}`). -/
theorem dTV_le_of_forall_event {α : Type*} (μ ν : PMF α) (δ : ℝ)
    (h : ∀ E : Set α, |expect μ (Set.indicator E 1) - expect ν (Set.indicator E 1)| ≤ δ) :
    dTV μ ν ≤ 2 * δ := by
  classical
  have hg := summable_toReal μ
  have hh := summable_toReal ν
  have hf : Summable (fun v => (μ v).toReal - (ν v).toReal) := hg.sub hh
  have hsf : ∑' v, ((μ v).toReal - (ν v).toReal) = 0 := by
    rw [hg.tsum_sub hh, tsum_toReal_eq_one, tsum_toReal_eq_one]; ring
  set E : Set α := {v | (ν v).toReal ≤ (μ v).toReal} with hEdef
  have hEexp : ∀ ρ : PMF α,
      ∑' v, Set.indicator E (fun w => (ρ w).toReal) v = expect ρ (Set.indicator E 1) := by
    intro ρ
    unfold expect
    refine tsum_congr fun v => ?_
    by_cases hv : v ∈ E
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]; simp
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]; simp
  have key : ∀ v, |(μ v).toReal - (ν v).toReal|
      = 2 * (Set.indicator E (fun w => (μ w).toReal) v
             - Set.indicator E (fun w => (ν w).toReal) v)
        - ((μ v).toReal - (ν v).toReal) := by
    intro v
    by_cases hv : v ∈ E
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv,
          abs_of_nonneg (by have : (ν v).toReal ≤ (μ v).toReal := hv; linarith)]; ring
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]
      have hle : (μ v).toReal ≤ (ν v).toReal := le_of_lt (not_le.mp hv)
      rw [abs_of_nonpos (by linarith)]; ring
  have hIndG : Summable (Set.indicator E (fun w => (μ w).toReal)) := hg.indicator E
  have hIndH : Summable (Set.indicator E (fun w => (ν w).toReal)) := hh.indicator E
  have hFsum : Summable (fun v => 2 * (Set.indicator E (fun w => (μ w).toReal) v
                  - Set.indicator E (fun w => (ν w).toReal) v)) :=
    Summable.mul_left 2 (hIndG.sub hIndH)
  calc dTV μ ν
      = ∑' v, |(μ v).toReal - (ν v).toReal| := rfl
    _ = ∑' v, (2 * (Set.indicator E (fun w => (μ w).toReal) v
                    - Set.indicator E (fun w => (ν w).toReal) v)
               - ((μ v).toReal - (ν v).toReal)) := tsum_congr key
    _ = (∑' v, 2 * (Set.indicator E (fun w => (μ w).toReal) v
                    - Set.indicator E (fun w => (ν w).toReal) v))
        - ∑' v, ((μ v).toReal - (ν v).toReal) := hFsum.tsum_sub hf
    _ = 2 * (expect μ (Set.indicator E 1) - expect ν (Set.indicator E 1)) := by
          rw [tsum_mul_left, hIndG.tsum_sub hIndH, hsf, hEexp μ, hEexp ν]; ring
    _ ≤ 2 * δ := by
          have := h E
          have h2 := le_abs_self (expect μ (Set.indicator E 1) - expect ν (Set.indicator E 1))
          linarith

/-! ### Linearity of expectation (bounded observables) -/

theorem expect_add {α : Type*} (μ : PMF α) {f g : α → ℝ} (B : ℝ) (hf : ∀ a, |f a| ≤ B)
    (hg : ∀ a, |g a| ≤ B) : expect μ (fun a => f a + g a) = expect μ f + expect μ g := by
  unfold expect
  simp_rw [mul_add]
  exact (summable_mul_of_bounded μ f B hf).tsum_add (summable_mul_of_bounded μ g B hg)

theorem expect_sub {α : Type*} (μ : PMF α) {f g : α → ℝ} (B : ℝ) (hf : ∀ a, |f a| ≤ B)
    (hg : ∀ a, |g a| ≤ B) : expect μ (fun a => f a - g a) = expect μ f - expect μ g := by
  unfold expect
  simp_rw [mul_sub]
  exact (summable_mul_of_bounded μ f B hf).tsum_sub (summable_mul_of_bounded μ g B hg)

theorem expect_const_mul {α : Type*} (μ : PMF α) (c : ℝ) (f : α → ℝ) :
    expect μ (fun a => c * f a) = c * expect μ f := by
  unfold expect
  simp_rw [mul_left_comm _ c]
  exact tsum_mul_left

theorem expect_finset_sum {α ι : Type*} (μ : PMF α) (s : Finset ι) (f : ι → α → ℝ) (B : ℝ)
    (hf : ∀ i ∈ s, ∀ a, |f i a| ≤ B) :
    expect μ (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expect μ (f i) := by
  unfold expect
  simp_rw [Finset.mul_sum]
  exact Summable.tsum_finsetSum fun i hi => summable_mul_of_bounded μ (f i) B (hf i hi)

/-- A bound on the difference of expectations from pointwise bounds on the support. -/
theorem abs_expect_sub_le_of_support {α : Type*} (μ : PMF α) {f g h : α → ℝ} (B : ℝ)
    (hf : ∀ a, |f a| ≤ B) (hg : ∀ a, |g a| ≤ B) (hh : ∀ a, |h a| ≤ B)
    (hle : ∀ a ∈ μ.support, |f a - g a| ≤ h a) :
    |expect μ f - expect μ g| ≤ expect μ h := by
  rw [← expect_sub μ B hf hg]
  unfold expect
  have hs : Summable fun a => (μ a).toReal * (f a - g a) :=
    summable_mul_of_bounded μ (fun a => f a - g a) (B + B)
      (fun a => (abs_sub _ _).trans (add_le_add (hf a) (hg a)))
  calc |∑' a, (μ a).toReal * (f a - g a)| ≤ ∑' a, |(μ a).toReal * (f a - g a)| := by
        have := norm_tsum_le_tsum_norm (f := fun a => (μ a).toReal * (f a - g a))
          (by simpa only [Real.norm_eq_abs] using hs.abs)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' a, (μ a).toReal * h a := by
        refine hs.abs.tsum_le_tsum (fun a => ?_) (summable_mul_of_bounded μ h B hh)
        rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        by_cases ha : a ∈ μ.support
        · exact mul_le_mul_of_nonneg_left (hle a ha) ENNReal.toReal_nonneg
        · rw [PMF.mem_support_iff, not_not] at ha
          simp [ha]

/-- Comparison of expectations from pointwise comparison on the support. -/
theorem expect_le_of_support {α : Type*} (μ : PMF α) {f g : α → ℝ} (B : ℝ)
    (hf : ∀ a, |f a| ≤ B) (hg : ∀ a, |g a| ≤ B) (hle : ∀ a ∈ μ.support, f a ≤ g a) :
    expect μ f ≤ expect μ g := by
  unfold expect
  refine (summable_mul_of_bounded μ f B hf).tsum_le_tsum (fun a => ?_)
    (summable_mul_of_bounded μ g B hg)
  by_cases ha : a ∈ μ.support
  · exact mul_le_mul_of_nonneg_left (hle a ha) ENNReal.toReal_nonneg
  · rw [PMF.mem_support_iff, not_not] at ha
    simp [ha]

/-- The difference of probabilities of an event is bounded by the total variation (pushforward form). -/
theorem expect_indicator_le_add_dTV {α : Type*} (μ ν : PMF α) (E : Set α) :
    expect μ (Set.indicator E 1) ≤ expect ν (Set.indicator E 1) + μ.dTV ν := by
  have := abs_expect_indicator_sub_le_dTV μ ν E
  rw [dTV_eq_pmf_dTV] at this
  have := le_abs_self (expect μ (Set.indicator E 1) - expect ν (Set.indicator E 1))
  linarith

/-! ### Harmonic sums (replacement for tao-collatz's `harmonic_ap_integral_bound`) -/

/-- `Q/M ≤ log(M/(M-Q))` (`0 < Q < M`). -/
theorem div_le_log_div_sub {M Q : ℝ} (hQ : 0 < Q) (hMQ : Q < M) :
    Q / M ≤ Real.log (M / (M - Q)) := by
  have hM : 0 < M := by linarith
  have h1 : 0 < (M - Q) / M := div_pos (by linarith) hM
  have h2 := Real.log_le_sub_one_of_pos h1
  have h3 : M / (M - Q) = ((M - Q) / M)⁻¹ := by rw [inv_div]
  rw [h3, Real.log_inv]
  have h4 : (M - Q) / M - 1 = -(Q / M) := by field_simp; ring
  linarith

/-- **Upper bound on the harmonic sum over an arithmetic progression**: if a finite set of naturals that
are congruent modulo `Q` lies in `[a, b]` (`0 < a ≤ b`), then `Σ 1/N ≤ 1/a + log(b/a)/Q`. -/
theorem sum_inv_le_of_modEq {Q : ℕ} (hQ : 0 < Q) {a : ℝ} (ha : 0 < a) (S : Finset ℕ) :
    ∀ b : ℝ, a ≤ b → (∀ N ∈ S, a ≤ (N : ℝ) ∧ (N : ℝ) ≤ b) →
      (∀ N ∈ S, ∀ N' ∈ S, N % Q = N' % Q) →
      ∑ N ∈ S, (N : ℝ)⁻¹ ≤ a⁻¹ + Real.log (b / a) / Q := by
  classical
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  induction S using Finset.induction_on_max with
  | empty =>
    intro b hab _ _
    rw [Finset.sum_empty]
    have : 0 ≤ Real.log (b / a) := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
    have : 0 ≤ Real.log (b / a) / Q := div_nonneg this hQR.le
    have : 0 < a⁻¹ := inv_pos.mpr ha
    linarith
  | insert M S hlt ih =>
    intro b hab hmem hcong
    have hM := hmem M (Finset.mem_insert_self M S)
    rw [Finset.sum_insert (fun h => lt_irrefl M (hlt M h))]
    have hlog0 : 0 ≤ Real.log (b / a) := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
    by_cases hS : S = ∅
    · subst hS
      rw [Finset.sum_empty, add_zero]
      have : (M : ℝ)⁻¹ ≤ a⁻¹ := inv_anti₀ ha hM.1
      have : 0 ≤ Real.log (b / a) / Q := div_nonneg hlog0 hQR.le
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
      have haMQ : a ≤ (M : ℝ) - Q := le_trans (hmem N₁ (Finset.mem_insert_of_mem hN₁)).1 (hle N₁ hN₁)
      have ih' := ih (M - Q) haMQ
        (fun N hN => ⟨(hmem N (Finset.mem_insert_of_mem hN)).1, hle N hN⟩)
        (fun N hN N' hN' => hcong N (Finset.mem_insert_of_mem hN) N' (Finset.mem_insert_of_mem hN'))
      have hQM : (Q : ℝ) < M := by linarith
      have hMpos : (0 : ℝ) < M := by linarith
      have hMQpos : (0 : ℝ) < M - Q := by linarith
      have hkey : (M : ℝ)⁻¹ ≤ Real.log (M / (M - Q)) / Q := by
        have := div_le_log_div_sub hQR hQM
        rw [le_div_iff₀ hQR]
        calc (M : ℝ)⁻¹ * Q = Q / M := by field_simp
          _ ≤ _ := this
      have hsplit : Real.log (M / (M - Q)) + Real.log ((M - Q) / a) = Real.log (M / a) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1; field_simp
      have hMb : Real.log (M / a) ≤ Real.log (b / a) :=
        Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hM.2 ha.le)
      calc (M : ℝ)⁻¹ + ∑ x ∈ S, (x : ℝ)⁻¹
          ≤ Real.log (M / (M - Q)) / Q + (a⁻¹ + Real.log ((M - Q) / a) / Q) := add_le_add hkey ih'
        _ = a⁻¹ + Real.log (M / a) / Q := by rw [← hsplit]; ring
        _ ≤ a⁻¹ + Real.log (b / a) / Q := by
            have := div_le_div_of_nonneg_right hMb hQR.le
            linarith

/-- **Lower bound on the harmonic sum over consecutive integers**: if `1 ≤ A` then
`Σ_{N=A}^{B} 1/N ≥ log((B+1)/A)`. -/
theorem log_le_sum_Icc_inv {A : ℕ} (hA : 1 ≤ A) : ∀ B : ℕ,
    Real.log (((B : ℝ) + 1) / A) ≤ ∑ N ∈ Finset.Icc A B, (N : ℝ)⁻¹ := by
  intro B
  induction B with
  | zero =>
    have : Finset.Icc A 0 = ∅ := Finset.Icc_eq_empty (by omega)
    rw [this, Finset.sum_empty]
    apply Real.log_nonpos (by positivity)
    rw [div_le_one (by exact_mod_cast (show 0 < A by omega))]
    push_cast; exact_mod_cast hA
  | succ B ih =>
    by_cases hAB : A ≤ B + 1
    · rw [Finset.sum_Icc_succ_top hAB]
      have hB1 : (0 : ℝ) < (B : ℝ) + 1 := by positivity
      have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
      have hstep : Real.log (((B + 1 : ℕ) : ℝ) + 1) - Real.log ((B : ℝ) + 1) ≤ ((B + 1 : ℕ) : ℝ)⁻¹ := by
        push_cast
        rw [← Real.log_div (by positivity) hB1.ne']
        have := Real.log_le_sub_one_of_pos (show 0 < ((B : ℝ) + 1 + 1) / ((B : ℝ) + 1) by positivity)
        have h2 : ((B : ℝ) + 1 + 1) / ((B : ℝ) + 1) - 1 = ((B : ℝ) + 1)⁻¹ := by field_simp; ring
        linarith
      have e1 : Real.log ((((B + 1 : ℕ) : ℝ) + 1) / A)
          = Real.log (((B + 1 : ℕ) : ℝ) + 1) - Real.log A := Real.log_div (by positivity) hApos.ne'
      have e2 : Real.log (((B : ℝ) + 1) / A) = Real.log ((B : ℝ) + 1) - Real.log A :=
        Real.log_div hB1.ne' hApos.ne'
      rw [e1]; rw [e2] at ih
      linarith
    · have : Finset.Icc A (B + 1) = ∅ := Finset.Icc_eq_empty (by omega)
      rw [this, Finset.sum_empty]
      apply Real.log_nonpos (by positivity)
      rw [div_le_one (by exact_mod_cast (show 0 < A by omega))]
      have : ((B + 1 : ℕ) : ℝ) + 1 ≤ A := by exact_mod_cast (show B + 1 + 1 ≤ A by omega)
      exact this

/-- The number of integers in an interval: if `0 ≤ A ≤ B < n₀ + 1` then
`B - A - 1 ≤ #{n ≤ n₀ | A ≤ n ≤ B} ≤ B - A + 1`. -/
theorem card_filter_range_bounds {A B : ℝ} {n₀ : ℕ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (hB : B < n₀ + 1) [DecidablePred fun n : ℕ => A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B] :
    B - A - 1 ≤ (((Finset.range (n₀ + 1)).filter fun n : ℕ => A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B).card : ℝ) ∧
      (((Finset.range (n₀ + 1)).filter fun n : ℕ => A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B).card : ℝ)
        ≤ B - A + 1 := by
  have hB0 : 0 ≤ B := le_trans hA hAB
  have heq : ((Finset.range (n₀ + 1)).filter fun n : ℕ => A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B)
      = Finset.Icc ⌈A⌉₊ ⌊B⌋₊ := by
    ext n
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hB0]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have : (n : ℝ) < n₀ + 1 := lt_of_le_of_lt h.2 hB
      exact_mod_cast this
  rw [heq, Nat.card_Icc]
  have h1 : (⌈A⌉₊ : ℝ) < A + 1 := Nat.ceil_lt_add_one hA
  have h2 : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
  have h3 : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le hB0
  have h4 : B < (⌊B⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one B
  have hle : ⌈A⌉₊ ≤ ⌊B⌋₊ + 1 := by
    have : (⌈A⌉₊ : ℝ) < (⌊B⌋₊ : ℝ) + 2 := by linarith
    have : ⌈A⌉₊ < ⌊B⌋₊ + 2 := by exact_mod_cast this
    omega
  rw [Nat.cast_sub hle]
  push_cast
  constructor <;> linarith

/-! ### Asymptotic auxiliaries (`x → ∞`) -/

open Filter in
theorem eventually_log_ge (C : ℝ) : ∀ᶠ x : ℝ in atTop, C ≤ Real.log x :=
  Real.tendsto_log_atTop.eventually_ge_atTop C

open Filter in
/-- `log^{-a} x → 0`. -/
theorem eventually_log_rpow_neg_le {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ (-a) ≤ ε :=
  ((tendsto_rpow_neg_atTop ha).comp Real.tendsto_log_atTop).eventually (ge_mem_nhds hε)

open Filter in
/-- If `a < b` then `C log^a x ≤ log^b x` (for `x` large). -/
theorem eventually_mul_log_rpow_le {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * Real.log x ^ a ≤ Real.log x ^ b := by
  have h1 := ((tendsto_rpow_atTop (sub_pos.mpr hab)).comp Real.tendsto_log_atTop).eventually_ge_atTop C
  filter_upwards [h1, eventually_log_ge 1] with x hx hL
  have hLpos : 0 < Real.log x := by linarith
  have hsplit : Real.log x ^ b = Real.log x ^ (b - a) * Real.log x ^ a := by
    rw [← Real.rpow_add hLpos]; ring_nf
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hLpos.le _)

open Filter in
/-- If `a < b`, `0 < b`, `ε > 0` then `A + B log^a x ≤ ε log^b x` (for `x` large). -/
theorem eventually_add_mul_rpow_le {a b : ℝ} (hab : a < b) (hb : 0 < b) (A B : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ x : ℝ in atTop, A + B * Real.log x ^ a ≤ ε * Real.log x ^ b := by
  filter_upwards [eventually_mul_log_rpow_le hab (2 * B / ε),
    eventually_mul_log_rpow_le hb (2 * A / ε), eventually_log_ge 1] with x h1 h2 hL
  have hLpos : 0 < Real.log x := by linarith
  rw [Real.rpow_zero, mul_one] at h2
  have e1 : B * Real.log x ^ a = (ε / 2) * (2 * B / ε * Real.log x ^ a) := by field_simp
  have e2 : A = (ε / 2) * (2 * A / ε) := by field_simp
  have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ ε / 2)
  have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ ε / 2)
  rw [e1]
  nth_rewrite 1 [e2]
  linarith

open Filter in
/-- `C x^{-c} ≤ log^{-A} x` (`c > 0`, for `x` large). -/
theorem eventually_mul_rpow_neg_le_log {c : ℝ} (hc : 0 < c) (A C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * x ^ (-c) ≤ Real.log x ^ (-A) := by
  have ho := (isLittleO_log_rpow_rpow_atTop A hc).bound (c := 1 / (|C| + 1)) (by positivity)
  filter_upwards [ho, eventually_log_ge 1, eventually_gt_atTop 0] with x hx hL hx0
  have hLpos : 0 < Real.log x := by linarith
  have hLA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hLpos A
  have hxc : 0 < x ^ c := Real.rpow_pos_of_pos hx0 c
  rw [Real.norm_of_nonneg hLA.le, Real.norm_of_nonneg hxc.le] at hx
  rw [Real.rpow_neg hLpos.le, Real.rpow_neg hx0.le]
  have key : (|C| + 1) * Real.log x ^ A ≤ x ^ c := by
    have := mul_le_mul_of_nonneg_left hx (by positivity : (0:ℝ) ≤ |C| + 1)
    rwa [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
  have h2 : (|C| + 1) * (x ^ c)⁻¹ ≤ (Real.log x ^ A)⁻¹ := by
    rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ hxc hLA]; linarith
  have hC : C ≤ |C| + 1 := by have := le_abs_self C; linarith
  calc C * (x ^ c)⁻¹ ≤ (|C| + 1) * (x ^ c)⁻¹ := mul_le_mul_of_nonneg_right hC (by positivity)
    _ ≤ _ := h2

end Family

end GGMCollatz
