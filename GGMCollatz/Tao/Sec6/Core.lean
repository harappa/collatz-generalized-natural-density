import GGMCollatz.Tao.Fourier.Char
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev

/-!
# The bridge between oscillation and Fourier analysis (Cauchy–Schwarz and Plancherel in GGM §5 Step 1)

Derived from `TaoCollatz/Sec6/MixingCore.lean` (first half, from `densC` to `osc_sum_le`) of
gotrevor/tao-collatz (Apache-2.0), commit 15efca2; generalized to the GGM family (p, q, r): the modulus
`3ⁿ` is replaced by `qⁿ` (`F.q`), and `syracZ` by `F.syracZ` (`GGMCollatz/Tao/Syracuse/SyracRV.lean`).

* `osc_eq_sum_norm_devC`: `Osc = ∑ ‖devC‖`.
* `osc_le_sqrt_highfreq`: `Osc_{m,n}(c) ≤ √(∑_{q^{n-m} ∤ ξ} ‖𝓕c(ξ)‖²)` (Cauchy–Schwarz and Parseval).
* `osc_syracZ_levels_triangle`: triangle inequality across scales (from the compatibility of projections, GGM (4.4)).
* `osc_le_two_mul_l1`, `osc_add_le`, `osc_sum_le`: `L¹` contraction and subadditivity.
-/

open scoped BigOperators

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- The real density `c` lifted to the complex numbers (for the discrete Fourier transform). -/
noncomputable def densC (n : ℕ) (c : ZMod (F.q ^ n) → ℝ) : ZMod (F.q ^ n) → ℂ :=
  fun Y => ((c Y : ℝ) : ℂ)

/-- High frequencies at scale `(n, m)`: `q^{n-m} ∤ ξ.val`. -/
noncomputable def highFreq (m n : ℕ) : Finset (ZMod (F.q ^ n)) :=
  Finset.univ.filter (fun ξ : ZMod (F.q ^ n) => ¬ (F.q ^ (n - m) ∣ ξ.val))

/-- Low frequencies at scale `(n, m)`: `q^{n-m} ∣ ξ.val`. -/
noncomputable def lowFreq (m n : ℕ) : Finset (ZMod (F.q ^ n)) :=
  Finset.univ.filter (fun ξ : ZMod (F.q ^ n) => (F.q ^ (n - m) ∣ ξ.val))

/-- The residue class modulo `q^m` (a fibre of `castHom`). -/
noncomputable def fiber (m n : ℕ) (hmn : m ≤ n) (Y : ZMod (F.q ^ n)) : Finset (ZMod (F.q ^ n)) :=
  Finset.univ.filter (fun Y' : ZMod (F.q ^ n) =>
    ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y'
      = ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y)

/-- The complex average over a residue class modulo `q^m`. -/
noncomputable def condAvgC (m n : ℕ) (hmn : m ≤ n) (c : ZMod (F.q ^ n) → ℝ) (Y : ZMod (F.q ^ n)) :
    ℂ :=
  (F.q : ℂ) ^ ((m : ℤ) - (n : ℤ)) * ∑ Y' ∈ F.fiber m n hmn Y, F.densC n c Y'

/-- The deviation from the average. -/
noncomputable def devC (m n : ℕ) (hmn : m ≤ n) (c : ZMod (F.q ^ n) → ℝ) (Y : ZMod (F.q ^ n)) : ℂ :=
  F.densC n c Y - F.condAvgC m n hmn c Y

theorem q_real_ne_zero : (F.q : ℝ) ≠ 0 := by exact_mod_cast F.q_pos.ne'

theorem q_complex_ne_zero : (F.q : ℂ) ≠ 0 := by exact_mod_cast F.q_pos.ne'

/-- The oscillation is the `L¹` norm of the deviation. -/
theorem osc_eq_sum_norm_devC (m n : ℕ) (hmn : m ≤ n) (c : ZMod (F.q ^ n) → ℝ) :
    F.osc m n hmn c = ∑ Y, ‖F.devC m n hmn c Y‖ := by
  rw [osc]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  simp only [devC, condAvgC, densC]
  have hcast : ((c Y : ℝ) : ℂ)
        - (F.q : ℂ) ^ ((m : ℤ) - (n : ℤ))
            * ∑ Y' ∈ F.fiber m n hmn Y, ((c Y' : ℝ) : ℂ)
      = ((c Y
          - (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ))
              * ∑ Y' ∈ F.fiber m n hmn Y, c Y' : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, fiber]

/-- The fibre as a set of translates `{Y + t q^m : t < q^{n-m}}`, and injectivity. -/
theorem fiber_eq_image (m n : ℕ) (hmn : m ≤ n) (Y : ZMod (F.q ^ n)) :
    Set.InjOn (fun t : ℕ => Y + (t : ZMod (F.q ^ n)) * (F.q : ZMod (F.q ^ n)) ^ m)
        (Finset.range (F.q ^ (n - m))) ∧
      F.fiber m n hmn Y = (Finset.range (F.q ^ (n - m))).image
        (fun t : ℕ => Y + (t : ZMod (F.q ^ n)) * (F.q : ZMod (F.q ^ n)) ^ m) := by
  classical
  have h3m : (F.q : ZMod (F.q ^ n)) ^ m = ((F.q ^ m : ℕ) : ZMod (F.q ^ n)) := by push_cast; ring
  have hcast3m : ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m))
      ((F.q : ZMod (F.q ^ n)) ^ m) = 0 := by
    rw [h3m, map_natCast]; exact ZMod.natCast_self _
  set g : ℕ → ZMod (F.q ^ n) := fun t => Y + (t : ZMod (F.q ^ n)) * (F.q : ZMod (F.q ^ n)) ^ m
    with hg
  have hginj : Set.InjOn g (Finset.range (F.q ^ (n - m))) := by
    intro t ht t' ht' heq
    simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
    simp only [hg] at heq
    have h2 : (t : ZMod (F.q ^ n)) * (F.q : ZMod (F.q ^ n)) ^ m
        = (t' : ZMod (F.q ^ n)) * (F.q : ZMod (F.q ^ n)) ^ m := add_left_cancel heq
    rw [show (t : ZMod (F.q ^ n)) * (F.q : ZMod (F.q ^ n)) ^ m
          = ((t * F.q ^ m : ℕ) : ZMod (F.q ^ n)) from by push_cast; ring,
      show (t' : ZMod (F.q ^ n)) * (F.q : ZMod (F.q ^ n)) ^ m
          = ((t' * F.q ^ m : ℕ) : ZMod (F.q ^ n)) from by push_cast; ring,
      ZMod.natCast_eq_natCast_iff,
      show F.q ^ n = F.q ^ (n - m) * F.q ^ m from by rw [← pow_add, Nat.sub_add_cancel hmn]] at h2
    have h3 : t ≡ t' [MOD F.q ^ (n - m)] :=
      Nat.ModEq.mul_right_cancel' (pow_pos F.q_pos m).ne' h2
    rwa [Nat.ModEq, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at h3
  refine ⟨hginj, ?_⟩
  ext Y'
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · intro hY'
    rw [fiber, Finset.mem_filter] at hY'
    have hz : ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) (Y' - Y) = 0 := by
      rw [map_sub, hY'.2, sub_self]
    have hval0 : (((Y' - Y).val : ℕ) : ZMod (F.q ^ m)) = 0 := by
      rw [ZMod.castHom_apply] at hz
      rw [ZMod.natCast_val]
      exact hz
    have hdvd : (F.q ^ m : ℕ) ∣ (Y' - Y).val := (ZMod.natCast_eq_zero_iff _ _).mp hval0
    refine ⟨(Y' - Y).val / F.q ^ m, ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul (pow_pos F.q_pos m)]
      calc (Y' - Y).val < F.q ^ n := ZMod.val_lt _
        _ = F.q ^ (n - m) * F.q ^ m := by rw [← pow_add, Nat.sub_add_cancel hmn]
    · simp only [hg]
      have hmul : (((Y' - Y).val / F.q ^ m : ℕ) : ZMod (F.q ^ n)) * (F.q : ZMod (F.q ^ n)) ^ m
          = Y' - Y := by
        rw [h3m, ← Nat.cast_mul, Nat.div_mul_cancel hdvd, ZMod.natCast_zmod_val]
      rw [hmul]; abel
  · rintro ⟨t, _, rfl⟩
    rw [fiber, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [hg, map_add, map_mul, map_pow, map_natCast]
    rw [show ((F.q : ZMod (F.q ^ m))) ^ m = ((F.q ^ m : ℕ) : ZMod (F.q ^ m)) by push_cast; ring,
      ZMod.natCast_self, mul_zero, add_zero]

/-- A fibre has exactly `q^{n-m}` points. -/
theorem fiber_card (m n : ℕ) (hmn : m ≤ n) (Y : ZMod (F.q ^ n)) :
    (F.fiber m n hmn Y).card = F.q ^ (n - m) := by
  obtain ⟨hinj, heq⟩ := F.fiber_eq_image m n hmn Y
  rw [heq, Finset.card_image_of_injOn hinj, Finset.card_range]

/-- The fibre form of the compatibility of projections (GGM (4.4)): `∑_{fiber} P(𝒮_n = Y') = P(𝒮_m = π Y)`. -/
theorem fiber_syracZ_sum (m n : ℕ) (hmn : m ≤ n) (Y : ZMod (F.q ^ n)) :
    ∑ Y' ∈ F.fiber m n hmn Y, ((F.syracZ n) Y').toReal =
      ((F.syracZ m) (ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y)).toReal := by
  classical
  let π : ZMod (F.q ^ n) → ZMod (F.q ^ m) :=
    ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m))
  have hmap := congrArg
    (fun p : PMF (ZMod (F.q ^ m)) => (p (π Y)).toReal)
    (F.syracZ_map_cast hmn)
  rw [PMF.map_apply,
    tsum_eq_sum (s := Finset.univ) (fun a ha => absurd (Finset.mem_univ a) ha),
    ENNReal.toReal_sum (fun a _ => by
      split
      · exact (F.syracZ n).apply_ne_top a
      · exact ENNReal.zero_ne_top)] at hmap
  simp only [fiber, Finset.sum_filter, apply_ite ENNReal.toReal,
    ENNReal.toReal_zero, eq_comm, π] at hmap ⊢
  exact hmap.trans (by congr!)

/-- The law at level `m` lifted uniformly to level `n`. -/
noncomputable def syracLift (m n : ℕ) (hmn : m ≤ n) (Y : ZMod (F.q ^ n)) : ℝ :=
  (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
    ((F.syracZ m) (ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y)).toReal

/-- The oscillation of `𝒮_n` is the `L¹` distance to the uniform lift of `𝒮_m`. -/
theorem osc_syracZ_eq_l1_lift (m n : ℕ) (hmn : m ≤ n) :
    F.osc m n hmn (fun Y => ((F.syracZ n) Y).toReal) =
      ∑ Y, |((F.syracZ n) Y).toReal - F.syracLift m n hmn Y| := by
  classical
  rw [osc]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  change |((F.syracZ n) Y).toReal - (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
      ∑ Y' ∈ F.fiber m n hmn Y, ((F.syracZ n) Y').toReal| = _
  rw [fiber_syracZ_sum]
  rfl

/-- The size of each fibre of the projection. -/
theorem castFiber_card (m n : ℕ) (hmn : m ≤ n) (Z : ZMod (F.q ^ m)) :
    (Finset.univ.filter (fun Y : ZMod (F.q ^ n) =>
      ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y = Z)).card = F.q ^ (n - m) := by
  classical
  obtain ⟨Y, rfl⟩ := ZMod.castHom_surjective (pow_dvd_pow F.q hmn) Z
  simpa only [fiber] using F.fiber_card m n hmn Y

/-- The sum of a function pulled back along the projection counts each value `q^{n-m}` times. -/
theorem sum_comp_castHom (m n : ℕ) (hmn : m ≤ n) (f : ZMod (F.q ^ m) → ℝ) :
    ∑ Y : ZMod (F.q ^ n),
        f (ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y) =
      ((F.q ^ (n - m) : ℕ) : ℝ) * ∑ Z, f Z := by
  classical
  let π : ZMod (F.q ^ n) → ZMod (F.q ^ m) :=
    ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m))
  calc
    ∑ Y, f (π Y) = ∑ Z, ∑ Y ∈ Finset.univ with π Y = Z, f (π Y) := by
      simpa using
        (Finset.sum_fiberwise (Finset.univ : Finset (ZMod (F.q ^ n))) π (fun Y => f (π Y))).symm
    _ = ∑ Z, ((F.q ^ (n - m) : ℕ) : ℝ) * f Z := by
      refine Finset.sum_congr rfl (fun Z _ => ?_)
      simp only [Finset.sum_filter]
      calc
        ∑ Y, (if π Y = Z then f (π Y) else 0) =
            ∑ Y, (if π Y = Z then f Z else 0) := by
          refine Finset.sum_congr rfl (fun Y _ => ?_)
          split_ifs with h
          · rw [h]
          · rfl
        _ = ((F.q ^ (n - m) : ℕ) : ℝ) * f Z := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          congr 1
          norm_cast
          simpa only [π] using F.castFiber_card m n hmn Z
    _ = ((F.q ^ (n - m) : ℕ) : ℝ) * ∑ Z, f Z := by
      rw [Finset.mul_sum]

/-- Uniform lifts compose through an intermediate scale. -/
theorem syracLift_tower (m k n : ℕ) (hmk : m ≤ k) (hkn : k ≤ n) (Y : ZMod (F.q ^ n)) :
    F.syracLift m n (hmk.trans hkn) Y =
      (F.q : ℝ) ^ ((k : ℤ) - (n : ℤ)) *
        F.syracLift m k hmk
          (ZMod.castHom (pow_dvd_pow F.q hkn) (ZMod (F.q ^ k)) Y) := by
  have hcast :
      ZMod.castHom (pow_dvd_pow F.q hmk) (ZMod (F.q ^ m))
          (ZMod.castHom (pow_dvd_pow F.q hkn) (ZMod (F.q ^ k)) Y) =
        ZMod.castHom (pow_dvd_pow F.q (hmk.trans hkn)) (ZMod (F.q ^ m)) Y := by
    exact congrArg (fun f : ZMod (F.q ^ n) →+* ZMod (F.q ^ m) => f Y)
      (ZMod.castHom_comp (pow_dvd_pow F.q hmk) (pow_dvd_pow F.q hkn))
  rw [syracLift, syracLift, hcast]
  rw [← mul_assoc, ← zpow_add₀ F.q_real_ne_zero]
  congr 2
  ring

/-- The `L¹` distance between two lifts is unchanged by lifting to a finer level. -/
theorem sum_abs_syracLift_sub_lift (m k n : ℕ) (hmk : m ≤ k) (hkn : k ≤ n) :
    ∑ Y : ZMod (F.q ^ n),
        |F.syracLift k n hkn Y - F.syracLift m n (hmk.trans hkn) Y| =
      F.osc m k hmk (fun Z => ((F.syracZ k) Z).toReal) := by
  classical
  rw [osc_syracZ_eq_l1_lift]
  let π : ZMod (F.q ^ n) → ZMod (F.q ^ k) :=
    ZMod.castHom (pow_dvd_pow F.q hkn) (ZMod (F.q ^ k))
  have hq0 : (0 : ℝ) ≤ (F.q : ℝ) := Nat.cast_nonneg _
  have hlift (Y : ZMod (F.q ^ n)) :
      |F.syracLift k n hkn Y - F.syracLift m n (hmk.trans hkn) Y| =
        (F.q : ℝ) ^ ((k : ℤ) - (n : ℤ)) *
          |((F.syracZ k) (π Y)).toReal - F.syracLift m k hmk (π Y)| := by
    rw [F.syracLift_tower m k n hmk hkn]
    change |(F.q : ℝ) ^ ((k : ℤ) - (n : ℤ)) * ((F.syracZ k) (π Y)).toReal -
      (F.q : ℝ) ^ ((k : ℤ) - (n : ℤ)) * F.syracLift m k hmk (π Y)| = _
    rw [← mul_sub, abs_mul, abs_of_nonneg (zpow_nonneg hq0 _)]
  simp_rw [hlift]
  rw [← Finset.mul_sum]
  have hsum :
      ∑ i : ZMod (F.q ^ n), |((F.syracZ k) (π i)).toReal - F.syracLift m k hmk (π i)| =
        ((F.q ^ (n - k) : ℕ) : ℝ) *
          ∑ Z, |((F.syracZ k) Z).toReal - F.syracLift m k hmk Z| := by
    simpa only [π] using F.sum_comp_castHom k n hkn
      (fun Z => |((F.syracZ k) Z).toReal - F.syracLift m k hmk Z|)
  rw [hsum]
  rw [← mul_assoc]
  have hpow : ((F.q ^ (n - k) : ℕ) : ℝ) = (F.q : ℝ) ^ ((n : ℤ) - (k : ℤ)) := by
    rw [← Nat.cast_sub hkn, zpow_natCast]
    norm_cast
  rw [hpow, ← zpow_add₀ F.q_real_ne_zero]
  norm_num

/-- Triangle inequality across the scales of the projections. -/
theorem osc_syracZ_levels_triangle (m k n : ℕ) (hmk : m ≤ k) (hkn : k ≤ n) :
    F.osc m n (hmk.trans hkn) (fun Y => ((F.syracZ n) Y).toReal) ≤
      F.osc k n hkn (fun Y => ((F.syracZ n) Y).toReal) +
        F.osc m k hmk (fun Z => ((F.syracZ k) Z).toReal) := by
  rw [osc_syracZ_eq_l1_lift, osc_syracZ_eq_l1_lift]
  calc
    ∑ Y, |((F.syracZ n) Y).toReal - F.syracLift m n (hmk.trans hkn) Y| ≤
        ∑ Y, (|((F.syracZ n) Y).toReal - F.syracLift k n hkn Y| +
          |F.syracLift k n hkn Y - F.syracLift m n (hmk.trans hkn) Y|) := by
      exact Finset.sum_le_sum (fun Y _ => abs_sub_le _ _ _)
    _ = (∑ Y, |((F.syracZ n) Y).toReal - F.syracLift k n hkn Y|) +
        ∑ Y, |F.syracLift k n hkn Y - F.syracLift m n (hmk.trans hkn) Y| :=
      Finset.sum_add_distrib
    _ = (∑ Y, |((F.syracZ n) Y).toReal - F.syracLift k n hkn Y|) +
        F.osc m k hmk (fun Z => ((F.syracZ k) Z).toReal) := by
      rw [sum_abs_syracLift_sub_lift]

/-- **`L¹` contraction of the oscillation**: `Osc(c) ≤ 2 ∑_Y |c Y|`. -/
theorem osc_le_two_mul_l1 (m n : ℕ) (hmn : m ≤ n) (c : ZMod (F.q ^ n) → ℝ) :
    F.osc m n hmn c ≤ 2 * ∑ Y, |c Y| := by
  classical
  rw [osc_eq_sum_norm_devC]
  have hq0 : (0 : ℝ) ≤ (F.q : ℝ) := Nat.cast_nonneg _
  have hnorm3 : ‖(F.q : ℂ) ^ ((m : ℤ) - (n : ℤ))‖ = (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) := by
    rw [norm_zpow, Complex.norm_natCast]
  have hdens : ∀ Y, ‖F.densC n c Y‖ = |c Y| := fun Y => by
    rw [densC, Complex.norm_real, Real.norm_eq_abs]
  have hcount : ∑ Y, ∑ Y' ∈ F.fiber m n hmn Y, |c Y'|
      = ((F.q ^ (n - m) : ℕ) : ℝ) * ∑ Y', |c Y'| := by
    have h1 : ∀ Y, ∑ Y' ∈ F.fiber m n hmn Y, |c Y'|
        = ∑ Y', (if ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y'
              = ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y then |c Y'| else 0) := by
      intro Y; rw [fiber, Finset.sum_filter]
    simp_rw [h1]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Y' _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const]
    have hfeq : (Finset.univ.filter (fun Y => ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y'
          = ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y)) = F.fiber m n hmn Y' := by
      rw [fiber]; ext Y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm]
    rw [hfeq, fiber_card, nsmul_eq_mul]
  have hpow : ((F.q ^ (n - m) : ℕ) : ℝ) = (F.q : ℝ) ^ ((n : ℤ) - (m : ℤ)) := by
    rw [← Nat.cast_sub hmn, zpow_natCast]; push_cast; ring
  have hcond : ∑ Y, ‖F.condAvgC m n hmn c Y‖ ≤ ∑ Y, |c Y| := by
    have hpt : ∀ Y, ‖F.condAvgC m n hmn c Y‖
        ≤ (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) * ∑ Y' ∈ F.fiber m n hmn Y, |c Y'| := by
      intro Y
      rw [condAvgC, norm_mul, hnorm3]
      refine mul_le_mul_of_nonneg_left ?_ (zpow_nonneg hq0 _)
      calc ‖∑ Y' ∈ F.fiber m n hmn Y, F.densC n c Y'‖
          ≤ ∑ Y' ∈ F.fiber m n hmn Y, ‖F.densC n c Y'‖ := norm_sum_le _ _
        _ = ∑ Y' ∈ F.fiber m n hmn Y, |c Y'| := Finset.sum_congr rfl (fun Y' _ => hdens Y')
    calc ∑ Y, ‖F.condAvgC m n hmn c Y‖
        ≤ ∑ Y, (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) * ∑ Y' ∈ F.fiber m n hmn Y, |c Y'| :=
          Finset.sum_le_sum (fun Y _ => hpt Y)
      _ = (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) * ∑ Y, ∑ Y' ∈ F.fiber m n hmn Y, |c Y'| := by
          rw [Finset.mul_sum]
      _ = (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) * (((F.q ^ (n - m) : ℕ) : ℝ) * ∑ Y', |c Y'|) := by
          rw [hcount]
      _ = ∑ Y', |c Y'| := by
          rw [hpow, ← mul_assoc, ← zpow_add₀ F.q_real_ne_zero]
          norm_num
  calc ∑ Y, ‖F.devC m n hmn c Y‖
      ≤ ∑ Y, (‖F.densC n c Y‖ + ‖F.condAvgC m n hmn c Y‖) := by
        refine Finset.sum_le_sum (fun Y _ => ?_); rw [devC]; exact norm_sub_le _ _
    _ = (∑ Y, ‖F.densC n c Y‖) + ∑ Y, ‖F.condAvgC m n hmn c Y‖ := Finset.sum_add_distrib
    _ ≤ (∑ Y, |c Y|) + ∑ Y, |c Y| :=
        add_le_add (le_of_eq (Finset.sum_congr rfl (fun Y _ => hdens Y))) hcond
    _ = 2 * ∑ Y, |c Y| := by ring

/-- The real density of `𝒮_n` sums to 1. -/
theorem sum_syracZ_toReal_eq_one (n : ℕ) :
    ∑ Y : ZMod (F.q ^ n), ((F.syracZ n) Y).toReal = 1 := by
  have h : ∑' Y : ZMod (F.q ^ n), ((F.syracZ n) Y).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun Y => (F.syracZ n).apply_ne_top Y),
      (F.syracZ n).tsum_coe, ENNReal.toReal_one]
  rw [tsum_eq_sum (s := (Finset.univ : Finset (ZMod (F.q ^ n))))
    (fun Y hY => absurd (Finset.mem_univ Y) hY)] at h
  exact h

/-- The oscillation of a probability density is at most 2. -/
theorem osc_syracZ_le_two (m n : ℕ) (hmn : m ≤ n) :
    F.osc m n hmn (fun Y => ((F.syracZ n) Y).toReal) ≤ 2 := by
  calc
    F.osc m n hmn (fun Y => ((F.syracZ n) Y).toReal)
        ≤ 2 * ∑ Y, |((F.syracZ n) Y).toReal| := F.osc_le_two_mul_l1 m n hmn _
    _ = 2 * ∑ Y, ((F.syracZ n) Y).toReal := by
      congr 1
      exact Finset.sum_congr rfl (fun Y _ => abs_of_nonneg ENNReal.toReal_nonneg)
    _ = 2 := by rw [sum_syracZ_toReal_eq_one, mul_one]

/-- Fourier inversion: `densC Y = N⁻¹ ∑_ξ 𝓕(densC)(ξ) e(ξY)`. -/
theorem densC_inversion (n : ℕ) (c : ZMod (F.q ^ n) → ℝ) (Y : ZMod (F.q ^ n)) :
    F.densC n c Y = ((F.q : ℂ) ^ n)⁻¹ *
      ∑ ξ, ZMod.dft (F.densC n c) ξ * ZMod.stdAddChar (ξ * Y) := by
  have hNcast : ((F.q ^ n : ℕ) : ℂ) = (F.q : ℂ) ^ n := by push_cast; ring
  have hself : F.densC n c Y = ZMod.dft.symm (ZMod.dft (F.densC n c)) Y := by
    rw [LinearEquiv.symm_apply_apply]
  rw [hself, ZMod.invDFT_apply, smul_eq_mul, hNcast]
  congr 1
  exact Finset.sum_congr rfl (fun ξ _ => by rw [smul_eq_mul, mul_comm])

/-- Geometric series over a root of unity. -/
theorem geom_sum_root_of_pow_eq_one {K : ℕ} (r : ℂ) (hr : r ^ K = 1) :
    ∑ j ∈ Finset.range K, r ^ j = if r = 1 then (K : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp
  · rw [geom_sum_eq h, hr, sub_self, zero_div]

/-- Reindexing a character sum over a fibre. -/
theorem fiber_char_reindex (m n : ℕ) (hmn : m ≤ n) (ξ Y : ZMod (F.q ^ n)) :
    ∑ Y' ∈ F.fiber m n hmn Y, ZMod.stdAddChar (ξ * Y')
      = ∑ t ∈ Finset.range (F.q ^ (n - m)),
          ZMod.stdAddChar (ξ * (Y + (t : ZMod (F.q ^ n)) * (F.q : ZMod (F.q ^ n)) ^ m)) := by
  obtain ⟨hinj, heq⟩ := F.fiber_eq_image m n hmn Y
  rw [heq, Finset.sum_image hinj]

/-- **Character sum over a residue class**: 0 unless the frequency is low; for a low frequency, `q^{n-m}` times the value at the base point. -/
theorem coset_char_sum (m n : ℕ) (hmn : m ≤ n) (ξ Y : ZMod (F.q ^ n)) :
    ∑ Y' ∈ F.fiber m n hmn Y, ZMod.stdAddChar (ξ * Y')
      = (if ξ ∈ F.lowFreq m n then ((F.q : ℂ) ^ (n - m)) else 0) * ZMod.stdAddChar (ξ * Y) := by
  classical
  set r : ℂ := ZMod.stdAddChar (ξ * (F.q : ZMod (F.q ^ n)) ^ m) with hr_def
  have hpow_zero : (F.q : ZMod (F.q ^ n)) ^ n = 0 := by
    rw [show (F.q : ZMod (F.q ^ n)) ^ n = ((F.q ^ n : ℕ) : ZMod (F.q ^ n)) from by push_cast; ring,
      ZMod.natCast_self]
  have hrK : r ^ (F.q ^ (n - m)) = 1 := by
    rw [hr_def, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
    rw [show ((F.q ^ (n - m) : ℕ) : ZMod (F.q ^ n)) * (ξ * (F.q : ZMod (F.q ^ n)) ^ m) = 0 from ?_,
      AddChar.map_zero_eq_one]
    rw [show ((F.q ^ (n - m) : ℕ) : ZMod (F.q ^ n)) = (F.q : ZMod (F.q ^ n)) ^ (n - m) from by
        push_cast; ring,
      show (F.q : ZMod (F.q ^ n)) ^ (n - m) * (ξ * (F.q : ZMod (F.q ^ n)) ^ m)
        = ξ * ((F.q : ZMod (F.q ^ n)) ^ (n - m) * (F.q : ZMod (F.q ^ n)) ^ m) from by ring,
      ← pow_add, Nat.sub_add_cancel hmn, hpow_zero, mul_zero]
  have hlow_iff : (ξ ∈ F.lowFreq m n) ↔ r = 1 := by
    have hchar : (r = 1) ↔ (ξ * (F.q : ZMod (F.q ^ n)) ^ m = 0) := by
      rw [hr_def]
      constructor
      · intro h
        exact ZMod.injective_stdAddChar (h.trans (AddChar.map_zero_eq_one _).symm)
      · intro h; rw [h, AddChar.map_zero_eq_one]
    have hdvd : ∀ v : ℕ, (F.q ^ n ∣ v * F.q ^ m ↔ F.q ^ (n - m) ∣ v) := by
      intro v
      rw [show F.q ^ n = F.q ^ (n - m) * F.q ^ m from by rw [← pow_add, Nat.sub_add_cancel hmn]]
      exact Nat.mul_dvd_mul_iff_right (pow_pos F.q_pos m)
    rw [lowFreq, Finset.mem_filter, hchar]
    simp only [Finset.mem_univ, true_and]
    rw [show ξ * (F.q : ZMod (F.q ^ n)) ^ m = ((ξ.val * F.q ^ m : ℕ) : ZMod (F.q ^ n)) from by
        push_cast [ZMod.natCast_zmod_val]; ring,
      ZMod.natCast_eq_zero_iff]
    exact (hdvd ξ.val).symm
  rw [F.fiber_char_reindex m n hmn ξ Y]
  have hsplit : ∀ t : ℕ,
      ZMod.stdAddChar (ξ * (Y + (t : ZMod (F.q ^ n)) * (F.q : ZMod (F.q ^ n)) ^ m))
        = ZMod.stdAddChar (ξ * Y) * r ^ t := by
    intro t
    rw [hr_def, mul_add, AddChar.map_add_eq_mul, ← AddChar.map_nsmul_eq_pow]
    congr 2
    rw [nsmul_eq_mul]; ring
  rw [Finset.sum_congr rfl (fun t _ => hsplit t), ← Finset.mul_sum,
    geom_sum_root_of_pow_eq_one r hrK]
  by_cases h : ξ ∈ F.lowFreq m n
  · rw [if_pos h, if_pos (hlow_iff.mp h)]
    push_cast
    ring
  · rw [if_neg h, if_neg (fun hr1 => h (hlow_iff.mpr hr1)), mul_zero, zero_mul]

/-- **The class average is the projection onto the low frequencies**. -/
theorem condAvgC_eq_lowSum (m n : ℕ) (hmn : m ≤ n) (c : ZMod (F.q ^ n) → ℝ) (Y : ZMod (F.q ^ n)) :
    F.condAvgC m n hmn c Y
      = ((F.q : ℂ) ^ n)⁻¹ * ∑ ξ ∈ F.lowFreq m n,
          ZMod.dft (F.densC n c) ξ * ZMod.stdAddChar (ξ * Y) := by
  classical
  have h3 : (F.q : ℂ) ≠ 0 := F.q_complex_ne_zero
  have hcancel : (F.q : ℂ) ^ ((m : ℤ) - (n : ℤ)) * (F.q : ℂ) ^ (n - m) = 1 := by
    rw [← zpow_natCast (F.q : ℂ) (n - m), ← zpow_add₀ h3, Nat.cast_sub hmn,
      show (m : ℤ) - (n : ℤ) + ((n : ℤ) - (m : ℤ)) = 0 from by ring, zpow_zero]
  have hfib : ∑ Y' ∈ F.fiber m n hmn Y, F.densC n c Y'
      = ((F.q : ℂ) ^ n)⁻¹ * ∑ ξ, ZMod.dft (F.densC n c) ξ
          * ∑ Y' ∈ F.fiber m n hmn Y, ZMod.stdAddChar (ξ * Y') := by
    calc ∑ Y' ∈ F.fiber m n hmn Y, F.densC n c Y'
        = ∑ Y' ∈ F.fiber m n hmn Y, ((F.q : ℂ) ^ n)⁻¹
            * ∑ ξ, ZMod.dft (F.densC n c) ξ * ZMod.stdAddChar (ξ * Y') :=
          Finset.sum_congr rfl (fun Y' _ => F.densC_inversion n c Y')
      _ = ((F.q : ℂ) ^ n)⁻¹ * ∑ Y' ∈ F.fiber m n hmn Y,
            ∑ ξ, ZMod.dft (F.densC n c) ξ * ZMod.stdAddChar (ξ * Y') := by rw [Finset.mul_sum]
      _ = ((F.q : ℂ) ^ n)⁻¹ * ∑ ξ,
            ∑ Y' ∈ F.fiber m n hmn Y, ZMod.dft (F.densC n c) ξ * ZMod.stdAddChar (ξ * Y') := by
          rw [Finset.sum_comm]
      _ = ((F.q : ℂ) ^ n)⁻¹ * ∑ ξ, ZMod.dft (F.densC n c) ξ
            * ∑ Y' ∈ F.fiber m n hmn Y, ZMod.stdAddChar (ξ * Y') := by
          refine congrArg _ (Finset.sum_congr rfl (fun ξ _ => ?_))
          rw [Finset.mul_sum]
  have hcoset : ∀ ξ : ZMod (F.q ^ n),
      ZMod.dft (F.densC n c) ξ * ∑ Y' ∈ F.fiber m n hmn Y, ZMod.stdAddChar (ξ * Y')
        = if ξ ∈ F.lowFreq m n then
            (F.q : ℂ) ^ (n - m) * (ZMod.dft (F.densC n c) ξ * ZMod.stdAddChar (ξ * Y)) else 0 := by
    intro ξ
    rw [F.coset_char_sum m n hmn ξ Y]
    split_ifs with h <;> ring
  rw [condAvgC, hfib, Finset.sum_congr rfl (fun ξ (_ : ξ ∈ Finset.univ) => hcoset ξ),
    Finset.sum_ite_mem_eq, ← Finset.mul_sum]
  rw [show (F.q : ℂ) ^ ((m : ℤ) - (n : ℤ)) * (((F.q : ℂ) ^ n)⁻¹
        * ((F.q : ℂ) ^ (n - m) * ∑ ξ ∈ F.lowFreq m n,
            ZMod.dft (F.densC n c) ξ * ZMod.stdAddChar (ξ * Y)))
      = ((F.q : ℂ) ^ ((m : ℤ) - (n : ℤ)) * (F.q : ℂ) ^ (n - m)) * (((F.q : ℂ) ^ n)⁻¹
        * ∑ ξ ∈ F.lowFreq m n, ZMod.dft (F.densC n c) ξ * ZMod.stdAddChar (ξ * Y)) from by ring,
    hcancel, one_mul]

/-- **The deviation is the inverse Fourier transform of the high frequencies**. -/
theorem devC_eq_highfreq_invDFT (m n : ℕ) (hmn : m ≤ n) (c : ZMod (F.q ^ n) → ℝ)
    (Y : ZMod (F.q ^ n)) :
    F.devC m n hmn c Y
      = ((F.q : ℂ) ^ n)⁻¹ * ∑ ξ ∈ F.highFreq m n,
          ZMod.dft (F.densC n c) ξ * ZMod.stdAddChar (ξ * Y) := by
  have hsplit : ∑ ξ ∈ F.highFreq m n, ZMod.dft (F.densC n c) ξ * ZMod.stdAddChar (ξ * Y)
      = (∑ ξ, ZMod.dft (F.densC n c) ξ * ZMod.stdAddChar (ξ * Y))
        - ∑ ξ ∈ F.lowFreq m n, ZMod.dft (F.densC n c) ξ * ZMod.stdAddChar (ξ * Y) := by
    rw [highFreq, lowFreq, eq_sub_iff_add_eq, add_comm, Finset.sum_filter_add_sum_filter_not]
  rw [devC, F.densC_inversion n c Y, F.condAvgC_eq_lowSum m n hmn c Y, ← mul_sub, ← hsplit]

/-- **Parseval for the `L²` norm of the deviation**: `∑_Y ‖devC Y‖² = N⁻¹ ∑_{high} ‖𝓕c(ξ)‖²`. -/
theorem sum_norm_sq_devC_eq (m n : ℕ) (hmn : m ≤ n) (c : ZMod (F.q ^ n) → ℝ) :
    ∑ Y, ‖F.devC m n hmn c Y‖ ^ 2
      = ((F.q : ℝ) ^ n)⁻¹ * ∑ ξ ∈ F.highFreq m n, ‖ZMod.dft (F.densC n c) ξ‖ ^ 2 := by
  classical
  set g : ZMod (F.q ^ n) → ℂ :=
    fun ξ => if ξ ∈ F.highFreq m n then ZMod.dft (F.densC n c) ξ else 0 with hg
  have hNcast : ((F.q ^ n : ℕ) : ℂ) = (F.q : ℂ) ^ n := by push_cast; ring
  have hRcast : ((F.q ^ n : ℕ) : ℝ) = (F.q : ℝ) ^ n := by push_cast; ring
  have hN : (F.q : ℝ) ^ n ≠ 0 := pow_ne_zero _ F.q_real_ne_zero
  have hsum : ∀ Y : ZMod (F.q ^ n), (∑ ξ, ZMod.stdAddChar (ξ * Y) • g ξ)
      = ∑ ξ ∈ F.highFreq m n, ZMod.dft (F.densC n c) ξ * ZMod.stdAddChar (ξ * Y) := by
    intro Y
    simp only [hg, smul_eq_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_mem_eq]
    exact Finset.sum_congr rfl (fun ξ _ => mul_comm _ _)
  have hdev : ∀ Y : ZMod (F.q ^ n), F.devC m n hmn c Y = ZMod.dft.symm g Y := by
    intro Y
    rw [F.devC_eq_highfreq_invDFT m n hmn c Y, ZMod.invDFT_apply, smul_eq_mul, hNcast, hsum Y]
  have hgpt : ∀ ξ, ‖g ξ‖ ^ 2
      = if ξ ∈ F.highFreq m n then ‖ZMod.dft (F.densC n c) ξ‖ ^ 2 else 0 := by
    intro ξ; simp only [hg]; split_ifs <;> simp
  have hgsum : ∑ ξ, ‖g ξ‖ ^ 2 = ∑ ξ ∈ F.highFreq m n, ‖ZMod.dft (F.densC n c) ξ‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun ξ _ => hgpt ξ), Finset.sum_ite_mem_eq]
  have hpars := dft_parseval (ZMod.dft.symm g)
  rw [LinearEquiv.apply_symm_apply, hgsum, hRcast] at hpars
  have hLHS : ∑ Y, ‖F.devC m n hmn c Y‖ ^ 2 = ∑ Y, ‖ZMod.dft.symm g Y‖ ^ 2 :=
    Finset.sum_congr rfl (fun Y _ => by rw [hdev Y])
  rw [hLHS, hpars, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- **The Cauchy–Schwarz and Parseval bridge**: `Osc_{m,n}(c) ≤ √(∑_{high} ‖𝓕c‖²)`. -/
theorem osc_le_sqrt_highfreq (m n : ℕ) (hmn : m ≤ n) (c : ZMod (F.q ^ n) → ℝ) :
    F.osc m n hmn c
      ≤ Real.sqrt (∑ ξ ∈ F.highFreq m n, ‖ZMod.dft (F.densC n c) ξ‖ ^ 2) := by
  rw [osc_eq_sum_norm_devC]
  set D := ∑ Y, ‖F.devC m n hmn c Y‖ with hD
  set H := ∑ ξ ∈ F.highFreq m n, ‖ZMod.dft (F.densC n c) ξ‖ ^ 2 with hH
  have hN : (F.q : ℝ) ^ n ≠ 0 := pow_ne_zero _ F.q_real_ne_zero
  have hcard : ((Finset.univ : Finset (ZMod (F.q ^ n))).card : ℝ) = (F.q : ℝ) ^ n := by
    rw [Finset.card_univ, ZMod.card]; push_cast; ring
  have hcs : D ^ 2 ≤ (F.q : ℝ) ^ n * ∑ Y, ‖F.devC m n hmn c Y‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (ZMod (F.q ^ n))))
      (f := fun Y => ‖F.devC m n hmn c Y‖)
    rwa [hcard] at this
  have key : D ^ 2 ≤ H := by
    calc D ^ 2 ≤ (F.q : ℝ) ^ n * ∑ Y, ‖F.devC m n hmn c Y‖ ^ 2 := hcs
      _ = (F.q : ℝ) ^ n * (((F.q : ℝ) ^ n)⁻¹ * H) := by rw [sum_norm_sq_devC_eq]
      _ = H := by field_simp
  have hnn : 0 ≤ D := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc D = Real.sqrt (D ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt H := Real.sqrt_le_sqrt key

/-- **Subadditivity of the oscillation**. -/
theorem osc_add_le (m n : ℕ) (hmn : m ≤ n) (c₁ c₂ : ZMod (F.q ^ n) → ℝ) :
    F.osc m n hmn (fun Y => c₁ Y + c₂ Y) ≤ F.osc m n hmn c₁ + F.osc m n hmn c₂ := by
  unfold osc
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun Y _ => ?_)
  rw [show (c₁ Y + c₂ Y) - (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
        ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (F.q ^ n) =>
          ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y'
            = ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y), (c₁ Y' + c₂ Y')
      = (c₁ Y - (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
          ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (F.q ^ n) =>
            ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y'
              = ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y), c₁ Y')
        + (c₂ Y - (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
          ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (F.q ^ n) =>
            ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y'
              = ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y), c₂ Y')
      from by rw [Finset.sum_add_distrib]; ring]
  exact abs_add_le _ _

/-- The oscillation is nonnegative. -/
theorem osc_nonneg (m n : ℕ) (hmn : m ≤ n) (c : ZMod (F.q ^ n) → ℝ) : 0 ≤ F.osc m n hmn c :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- **Subadditivity of the oscillation over finite sums**. -/
theorem osc_sum_le {ι : Type*} (m n : ℕ) (hmn : m ≤ n) (s : Finset ι)
    (c : ι → ZMod (F.q ^ n) → ℝ) :
    F.osc m n hmn (fun Y => ∑ i ∈ s, c i Y) ≤ ∑ i ∈ s, F.osc m n hmn (c i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [osc]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc F.osc m n hmn (fun Y => ∑ i ∈ insert a s, c i Y)
        = F.osc m n hmn (fun Y => c a Y + ∑ i ∈ s, c i Y) := by
          refine congrArg _ (funext (fun Y => ?_)); rw [Finset.sum_insert ha]
      _ ≤ F.osc m n hmn (c a) + F.osc m n hmn (fun Y => ∑ i ∈ s, c i Y) := F.osc_add_le _ _ _ _ _
      _ ≤ F.osc m n hmn (c a) + ∑ i ∈ s, F.osc m n hmn (c i) := by linarith [ih]

end Family

end GGMCollatz
