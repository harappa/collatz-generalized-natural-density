import GGMCollatz.Assembly.Uniform

/-!
# The assembly of (A), part 6: the logarithmic-density corollary (the corollary in the accompanying paper)

* `logDensity_Np`: from the uniform bound `P(N₀, y) ≤ K N₀^{-c'}` for window probabilities, the
  logarithmic sum over `ℕ_p`: `∑_{N ≤ x, p ∤ N, S_min(N) > N₀} 1/N ≤ K₂ N₀^{-c'} log x` (`x ≥ 3`).
  Cover `[2, x]` by the windows `[y_i, y_i^α]` (`y_i = 2^{α^i}`, `i < I`, where `I` is the least with
  `x < 2^{α^I}`); bound the mass of the bad points of each window by `P(N₀, y_i)` × the mass of the
  window, and the mass of the window by `1 + log(y_i^α)` (upper bound for the harmonic sum).
* `logDensity_C`: transfer to general `N` via `N = p^k N'` (`p ∤ N'`) and
  `C_min(N) > N₀ ⇒ S_min(N') > N₀` (`∑_k p^{-k} ≤ p/(p-1)`).

**Deviation from the accompanying paper**: the paper estimates the sum of the total masses of the
windows as `π α ln x + O(log log x)`. Here we bound the mass of each window by `1 + α^{i+1} log 2`, and
obtain `O(log x)` from the number of windows `I ≤ 1 + log x/((α-1) log 2)` and a geometric sum.
-/

namespace GGMCollatz

namespace Asm

/-- Covering by windows: if `2 ≤ N ≤ x < 2^{α^I}` and `p ∤ N`, then for some `i < I`,
`N ∈ ℕ_p ∩ [2^{α^i}, (2^{α^i})^α]`. -/
theorem window_cover (F : Family) {α : ℝ} (hα : 1 < α) {x : ℝ} {I : ℕ} (hI : x < (2 : ℝ) ^ (α ^ I))
    {N : ℕ} (hN2 : 2 ≤ N) (hNx : (N : ℝ) ≤ x) (hNp : N % F.p ≠ 0) :
    ∃ i ∈ Finset.range I, N ∈ F.logWindow ((2 : ℝ) ^ (α ^ i)) (((2 : ℝ) ^ (α ^ i)) ^ α) := by
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hmono : ∀ i j : ℕ, i ≤ j → (2 : ℝ) ^ (α ^ i) ≤ (2 : ℝ) ^ (α ^ j) := fun i j hij =>
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (pow_le_pow_right₀ hα.le hij)
  have hex : ∃ j : ℕ, (N : ℝ) < (2 : ℝ) ^ (α ^ (j + 1)) :=
    ⟨I, lt_of_le_of_lt hNx (lt_of_lt_of_le hI (hmono _ _ (by omega)))⟩
  obtain ⟨i, hi, hmin⟩ : ∃ i, (N : ℝ) < (2 : ℝ) ^ (α ^ (i + 1)) ∧
      ∀ j < i, ¬ (N : ℝ) < (2 : ℝ) ^ (α ^ (j + 1)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hI0 : 1 ≤ I := by
    by_contra h0
    have : I = 0 := by omega
    rw [this, pow_zero, Real.rpow_one] at hI
    linarith
  refine ⟨i, ?_, ?_⟩
  · rw [Finset.mem_range]
    by_contra hiI
    have := hmin (I - 1) (by omega)
    rw [show I - 1 + 1 = I by omega] at this
    exact this (lt_of_le_of_lt hNx hI)
  · have hup : ((2 : ℝ) ^ (α ^ i)) ^ α = (2 : ℝ) ^ (α ^ (i + 1)) := by
      rw [← Real.rpow_mul (by norm_num), pow_succ]
    rw [mem_logWindow, hup]
    refine ⟨hNp, ?_, hi.le⟩
    rcases i with _ | k
    · rw [pow_zero, Real.rpow_one]; exact hN2'
    · have := hmin k (by omega)
      push Not at this
      exact this

/-- Upper bound for the total mass of a window: `∑_{ℕ_p ∩ [y, Y]} 1/N ≤ 1 + log Y` (`Y ≥ 1`). -/
theorem mass_le (F : Family) {y Y : ℝ} (hY : 1 ≤ Y) :
    ∑ N ∈ F.logWindow y Y, (N : ℝ)⁻¹ ≤ 1 + Real.log Y := by
  set n := ⌊Y⌋₊ with hn
  have hsub : F.logWindow y Y ⊆ Finset.Icc 1 n := by
    intro N hN
    have h := mem_logWindow.mp hN
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr (ne_zero_of_mem_logWindow hN), Nat.le_floor h.2.2⟩
  have h1 : ∑ N ∈ F.logWindow y Y, (N : ℝ)⁻¹ ≤ ∑ N ∈ Finset.Icc 1 n, (N : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun N _ _ => by positivity)
  have h2 : ∑ N ∈ Finset.Icc 1 n, (N : ℝ)⁻¹ = (harmonic n : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  have h3 := harmonic_le_one_add_log n
  have h4 : Real.log n ≤ Real.log Y := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg hY
    · exact Real.log_le_log (by exact_mod_cast hpos) (Nat.floor_le (by linarith))
  linarith

/-- The number of windows and the geometric sum: if `2^{α^{I-1}} ≤ x` and `x ≥ 3`, then
`∑_{i<I}(1 + α^{i+1} log 2) ≤ K₃ log x`. -/
lemma window_sum_le {α x : ℝ} (hα : 1 < α) (hx : 3 ≤ x) {I : ℕ} (hI0 : 1 ≤ I)
    (hIx : (2 : ℝ) ^ (α ^ (I - 1)) ≤ x) :
    ∑ i ∈ Finset.range I, (1 + α ^ (i + 1) * Real.log 2) ≤
      (1 / ((α - 1) * Real.log 2) + 1 / Real.log 3 + α ^ 2 / (α - 1)) * Real.log x := by
  have hα0 : 0 < α := by linarith
  have hα1 : 0 < α - 1 := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl3x : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  obtain ⟨m, rfl⟩ : ∃ m, I = m + 1 := ⟨I - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega] at hIx
  -- `α^m log 2 ≤ log x`
  have hm : α ^ m * Real.log 2 ≤ Real.log x := by
    have := Real.log_le_log (by positivity) hIx
    rwa [Real.log_rpow (by norm_num)] at this
  -- `m ≤ α^m/(α-1)` (Bernoulli)
  have hbern : 1 + (m : ℝ) * (α - 1) ≤ α ^ m := by
    have := one_add_mul_le_pow (a := α - 1) (by linarith) m
    rwa [show 1 + (α - 1) = α by ring] at this
  have hsum1 : ∑ i ∈ Finset.range (m + 1), (1 : ℝ) = m + 1 := by simp
  have hgeom : ∑ i ∈ Finset.range (m + 1), α ^ (i + 1) ≤ α ^ 2 * α ^ m / (α - 1) := by
    have e : ∑ i ∈ Finset.range (m + 1), α ^ (i + 1) = α * ∑ i ∈ Finset.range (m + 1), α ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, geom_sum_eq hα.ne', le_div_iff₀ hα1, pow_succ]
    have : α * ((α ^ m * α - 1) / (α - 1)) * (α - 1) = α * (α ^ m * α - 1) := by
      field_simp
    rw [this]
    have : 0 ≤ α ^ m := by positivity
    nlinarith
  rw [Finset.sum_add_distrib, hsum1, ← Finset.sum_mul]
  have hA : ((m : ℝ) + 1) ≤ Real.log x / ((α - 1) * Real.log 2) + Real.log x / Real.log 3 := by
    have h1 : (m : ℝ) ≤ Real.log x / ((α - 1) * Real.log 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h2 : (1 : ℝ) ≤ Real.log x / Real.log 3 := by rw [le_div_iff₀ hl3]; linarith
    linarith
  have hB : (∑ i ∈ Finset.range (m + 1), α ^ (i + 1)) * Real.log 2 ≤
      α ^ 2 / (α - 1) * Real.log x := by
    calc _ ≤ α ^ 2 * α ^ m / (α - 1) * Real.log 2 := by gcongr
      _ = α ^ 2 / (α - 1) * (α ^ m * Real.log 2) := by ring
      _ ≤ α ^ 2 / (α - 1) * Real.log x := by gcongr
  have e : (1 / ((α - 1) * Real.log 2) + 1 / Real.log 3 + α ^ 2 / (α - 1)) * Real.log x =
      Real.log x / ((α - 1) * Real.log 2) + Real.log x / Real.log 3 + α ^ 2 / (α - 1) * Real.log x := by
    ring
  rw [e]
  linarith

/-- **Corollary (on `ℕ_p`)**: from the uniform bound for window probabilities, a bound for the
logarithmic sum over `ℕ_p`. -/
theorem logDensity_Np (F : Family) {α : ℝ} (hα : 1 < α) {K c' : ℝ} (hK : 0 ≤ K)
    (hU : ∀ N₀ : ℕ, 1 ≤ N₀ → ∀ y : ℝ, 0 < y → F.windowProb α N₀ y ≤ K * (N₀ : ℝ) ^ (-c'))
    {N₀ : ℕ} (hN₀ : 1 ≤ N₀) {x : ℝ} (hx : 3 ≤ x) :
    ∑ N ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun N => N % F.p ≠ 0 ∧ N₀ < F.Smin N), (N : ℝ)⁻¹ ≤
      K * (1 / ((α - 1) * Real.log 2) + 1 / Real.log 3 + α ^ 2 / (α - 1)) *
        (N₀ : ℝ) ^ (-c') * Real.log x := by
  have hα0 : 0 < α := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hx0 : 0 < x := by linarith
  -- `I`: the least with `x < 2^{α^I}`
  have hex : ∃ j : ℕ, x < (2 : ℝ) ^ (α ^ j) := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (Real.log x / Real.log 2) hα
    refine ⟨j, ?_⟩
    rw [← Real.log_lt_log_iff hx0 (by positivity), Real.log_rpow (by norm_num)]
    rw [div_lt_iff₀ hl2] at hj
    linarith
  obtain ⟨I, hI, hImin⟩ : ∃ I, x < (2 : ℝ) ^ (α ^ I) ∧ ∀ j < I, ¬ x < (2 : ℝ) ^ (α ^ j) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hI0 : 1 ≤ I := by
    by_contra h0
    have : I = 0 := by omega
    rw [this, pow_zero, Real.rpow_one] at hI
    linarith
  have hIx : (2 : ℝ) ^ (α ^ (I - 1)) ≤ x := by
    have := hImin (I - 1) (by omega)
    push Not at this; exact this
  set y : ℕ → ℝ := fun i => (2 : ℝ) ^ (α ^ i) with hydef
  have hypos : ∀ i, 0 < y i := fun i => by positivity
  set B := (Finset.Icc 1 ⌊x⌋₊).filter (fun N => N % F.p ≠ 0 ∧ N₀ < F.Smin N) with hB
  set W : ℕ → Finset ℕ := fun i => F.logWindow (y i) ((y i) ^ α) with hW
  have hNpow : 0 ≤ (N₀ : ℝ) ^ (-c') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- Each point lies in some window
  have hpt : ∀ N ∈ B, (N : ℝ)⁻¹ ≤
      ∑ i ∈ Finset.range I, (if N ∈ W i then (N : ℝ)⁻¹ else 0) := by
    intro N hN
    rw [hB, Finset.mem_filter, Finset.mem_Icc] at hN
    obtain ⟨⟨hN1, hNx⟩, hNp, hbad⟩ := hN
    have hN2 : 2 ≤ N := by
      by_contra h
      have : N = 1 := by omega
      rw [this] at hbad
      exact not_lt_Smin_one F hN₀ hbad
    have hNx' : (N : ℝ) ≤ x := le_trans (Nat.cast_le.mpr hNx) (Nat.floor_le hx0.le)
    obtain ⟨i, hi, hNi⟩ := window_cover F hα hI hN2 hNx' hNp
    have := Finset.single_le_sum (f := fun j => if N ∈ W j then (N : ℝ)⁻¹ else 0)
      (fun j _ => by split_ifs <;> positivity) hi
    have hNi' : N ∈ W i := hNi
    simp only [if_pos hNi'] at this
    exact this
  have hwin : ∀ i ∈ Finset.range I,
      ∑ N ∈ B, (if N ∈ W i then (N : ℝ)⁻¹ else 0) ≤
        K * (N₀ : ℝ) ^ (-c') * (1 + α ^ (i + 1) * Real.log 2) := by
    intro i _
    have hsub : B.filter (fun N => N ∈ W i) ⊆ (W i).filter (fun N => N₀ < F.Smin N) := by
      intro N hN
      rw [Finset.mem_filter] at hN ⊢
      rw [hB, Finset.mem_filter] at hN
      exact ⟨hN.2, hN.1.2.2⟩
    have h1 : ∑ N ∈ B, (if N ∈ W i then (N : ℝ)⁻¹ else 0) ≤
        ∑ N ∈ (W i).filter (fun N => N₀ < F.Smin N), (N : ℝ)⁻¹ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun N _ _ => by positivity)
    have h2 := bad_mass_eq F α hN₀ (y i)
    have h3 := hU N₀ hN₀ (y i) (hypos i)
    have hyα : 1 ≤ (y i) ^ α := Real.one_le_rpow (by
      simp only [hydef]; exact Real.one_le_rpow (by norm_num) (by positivity)) hα0.le
    have h4 := mass_le F (y := y i) hyα
    have hlog : Real.log ((y i) ^ α) = α ^ (i + 1) * Real.log 2 := by
      simp only [hydef]
      rw [Real.log_rpow (by positivity), Real.log_rpow (by norm_num), pow_succ]; ring
    rw [hlog] at h4
    have hm0 : 0 ≤ ∑ N ∈ W i, (N : ℝ)⁻¹ := Finset.sum_nonneg fun N _ => by positivity
    have hP0 := windowProb_nonneg F α N₀ (y i)
    calc _ ≤ _ := h1
      _ = F.windowProb α N₀ (y i) * ∑ N ∈ W i, (N : ℝ)⁻¹ := h2
      _ ≤ K * (N₀ : ℝ) ^ (-c') * ∑ N ∈ W i, (N : ℝ)⁻¹ := mul_le_mul_of_nonneg_right h3 hm0
      _ ≤ K * (N₀ : ℝ) ^ (-c') * (1 + α ^ (i + 1) * Real.log 2) :=
          mul_le_mul_of_nonneg_left h4 (mul_nonneg hK hNpow)
  have hcnt := window_sum_le hα hx hI0 hIx
  calc ∑ N ∈ B, (N : ℝ)⁻¹
      ≤ ∑ N ∈ B, ∑ i ∈ Finset.range I, (if N ∈ W i then (N : ℝ)⁻¹ else 0) :=
        Finset.sum_le_sum hpt
    _ = ∑ i ∈ Finset.range I, ∑ N ∈ B, (if N ∈ W i then (N : ℝ)⁻¹ else 0) := Finset.sum_comm
    _ ≤ ∑ i ∈ Finset.range I, K * (N₀ : ℝ) ^ (-c') * (1 + α ^ (i + 1) * Real.log 2) :=
        Finset.sum_le_sum hwin
    _ = K * (N₀ : ℝ) ^ (-c') * ∑ i ∈ Finset.range I, (1 + α ^ (i + 1) * Real.log 2) := by
        rw [Finset.mul_sum]
    _ ≤ K * (N₀ : ℝ) ^ (-c') *
          ((1 / ((α - 1) * Real.log 2) + 1 / Real.log 3 + α ^ 2 / (α - 1)) * Real.log x) :=
        mul_le_mul_of_nonneg_left hcnt (mul_nonneg hK hNpow)
    _ = _ := by ring

/-- Sum of powers of `p`: `∑_{k < n} p^{-k} ≤ p/(p-1)`. -/
lemma sum_inv_pow_le {p : ℝ} (hp : 1 < p) (n : ℕ) :
    ∑ k ∈ Finset.range n, (p ^ k)⁻¹ ≤ p / (p - 1) := by
  have hp0 : 0 < p := by linarith
  have hr0 : 0 ≤ p⁻¹ := by positivity
  have hr1 : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hr0 hr1
  rw [pow_zero, ← Finset.range_eq_Ico] at this
  have e : 1 / (1 - p⁻¹) = p / (p - 1) := by
    field_simp
  simp_rw [← inv_pow]
  linarith

/-- **Corollary (general `N`)**: via `N = p^k N'` and `C_min(N) > N₀ ⇒ S_min(N') > N₀`. -/
theorem logDensity_C (F : Family) {N₀ : ℕ} (X : ℕ) :
    ∑ N ∈ (Finset.Icc 1 X).filter (fun N => N₀ < F.Cmin N), (N : ℝ)⁻¹ ≤
      (F.p : ℝ) / ((F.p : ℝ) - 1) *
        ∑ N ∈ (Finset.Icc 1 X).filter (fun N => N % F.p ≠ 0 ∧ N₀ < F.Smin N), (N : ℝ)⁻¹ := by
  have hp1 : 1 < F.p := F.one_lt_p
  have hp1' : (1 : ℝ) < F.p := by exact_mod_cast hp1
  set S := (Finset.Icc 1 X).filter (fun N => N₀ < F.Cmin N) with hS
  set T := (Finset.Icc 1 X).filter (fun N => N % F.p ≠ 0 ∧ N₀ < F.Smin N) with hT
  let g : ℕ → ℕ × ℕ := fun N => (padicValNat F.p N, N / F.p ^ padicValNat F.p N)
  have hginj : Set.InjOn g S := by
    intro N _ M _ h
    simp only [g, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [← pow_val_mul_div F N, ← pow_val_mul_div F M, h2, h1]
  have hsub : S.image g ⊆ Finset.range (X + 1) ×ˢ T := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨N, hN, rfl⟩ := hq
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hN
    obtain ⟨⟨hN1, hNX⟩, hbad⟩ := hN
    have hN0 : N ≠ 0 := by omega
    have hpk : F.p ^ padicValNat F.p N ≤ N := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    have hkp : padicValNat F.p N < F.p ^ padicValNat F.p N := Nat.lt_pow_self hp1
    have hN' : N / F.p ^ padicValNat F.p N ≠ 0 := by
      intro h0
      have := pow_val_mul_div F N
      rw [h0, mul_zero] at this
      exact hN0 this.symm
    simp only [g]
    rw [Finset.mem_product, Finset.mem_range, hT, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨by omega, ⟨⟨Nat.one_le_iff_ne_zero.mpr hN', le_trans (Nat.div_le_self _ _) hNX⟩,
      div_pow_val_mod_ne_zero F hN0, lt_Smin_of_lt_Cmin F hN0 hbad⟩⟩
  have hfg : ∀ N ∈ S, (N : ℝ)⁻¹ =
      (((F.p : ℝ) ^ (g N).1)⁻¹ * ((g N).2 : ℝ)⁻¹) := by
    intro N _
    rw [← mul_inv]
    congr 1
    have := pow_val_mul_div F N
    have h : ((F.p ^ padicValNat F.p N * (N / F.p ^ padicValNat F.p N) : ℕ) : ℝ) = (N : ℝ) := by
      rw [this]
    push_cast at h
    exact h.symm
  calc ∑ N ∈ S, (N : ℝ)⁻¹
      = ∑ N ∈ S, (((F.p : ℝ) ^ (g N).1)⁻¹ * ((g N).2 : ℝ)⁻¹) := Finset.sum_congr rfl hfg
    _ = ∑ q ∈ S.image g, (((F.p : ℝ) ^ q.1)⁻¹ * (q.2 : ℝ)⁻¹) := by
        rw [Finset.sum_image hginj]
    _ ≤ ∑ q ∈ Finset.range (X + 1) ×ˢ T, (((F.p : ℝ) ^ q.1)⁻¹ * (q.2 : ℝ)⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
    _ = (∑ k ∈ Finset.range (X + 1), ((F.p : ℝ) ^ k)⁻¹) * ∑ N ∈ T, (N : ℝ)⁻¹ := by
        rw [Finset.sum_product, Finset.sum_mul_sum]
    _ ≤ (F.p : ℝ) / ((F.p : ℝ) - 1) * ∑ N ∈ T, (N : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right (sum_inv_pow_le hp1' _)
          (Finset.sum_nonneg fun N _ => by positivity)

end Asm

end GGMCollatz
