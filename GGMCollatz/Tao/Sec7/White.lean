import GGMCollatz.Tao.Sec7.Setup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# GGM §6 Step 1: cancellation at white points (counterpart of Lemma 7.2 of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/White.lean`;
generalized to the GGM family (p, q, r). Modified. This is the elementary bound used in the second half of GGM §6 Step 1,
`|f(q^{2j-2}p^{-l}, 3)| ≤ 1 - (1 - |cos πθ|)/(p-1)`: at white points (`|θ| > ε`), `|cos(πθ)| ≤ 1 - 2ε²` (using `|θ| ≤ 1/2`).
tao-collatz used the form `≤ exp(-ε³)` with `ε = 10⁻¹⁰⁰⁰`. Here `ε` is general, and the conversion to `exp(-ε³)`
(which uses `ε ≤ 1/p`) is done in `Reduction.lean`.
-/

open scoped Real

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- `|cos(πθ(j,l))|`. -/
noncomputable def cosπθ (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) : ℝ :=
  Real.cos (Real.pi * (F.θq n c j l : ℝ))

/-- The trivial bound `|cos(πθ)| ≤ 1`. -/
theorem cosπθ_abs_le_one (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) : |F.cosπθ n c j l| ≤ 1 :=
  abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-- **Cancellation at white points**: if `0 ≤ ε` and `(j,l)` is white (`|θ| > ε`), then `|cos(πθ)| ≤ 1 - 2ε²`. -/
theorem white_cos_bound (n : ℕ) (c : ℤ) {ε : ℝ} (hε : 0 ≤ ε) (j : ℕ) (l : ℤ)
    (hw : F.white n c ε j l) :
    |F.cosπθ n c j l| ≤ 1 - 2 * ε ^ 2 := by
  set t : ℝ := ((F.θq n c j l : ℚ) : ℝ) with ht
  have ht2 : |t| ≤ 1 / 2 := by
    rw [ht, ← Rat.cast_abs]
    calc ((|F.θq n c j l| : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) :=
          Rat.cast_le.mpr (F.θq_abs_le_half n c j l)
      _ = 1 / 2 := by norm_num
  have hεt : ε < |t| := lt_of_not_ge fun h => hw h
  have hπ := Real.pi_gt_three
  have habs : |Real.pi * t| ≤ Real.pi := by
    rw [abs_mul, abs_of_nonneg Real.pi_pos.le]
    nlinarith [abs_nonneg t]
  have hnn : 0 ≤ Real.cos (Real.pi * t) := by
    refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
    · nlinarith [abs_le.mp ht2]
    · nlinarith [abs_le.mp ht2]
  have hquad : Real.cos (Real.pi * t) ≤ 1 - 2 * t ^ 2 := by
    have hb := Real.cos_le_one_sub_mul_cos_sq habs
    have hπt : 2 / Real.pi ^ 2 * (Real.pi * t) ^ 2 = 2 * t ^ 2 := by
      field_simp
    rw [hπt] at hb
    exact hb
  have hsq : ε ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs t]
    nlinarith [hεt]
  calc |F.cosπθ n c j l| = Real.cos (Real.pi * t) := by
        rw [cosπθ, ht, abs_of_nonneg hnn]
    _ ≤ 1 - 2 * t ^ 2 := hquad
    _ ≤ 1 - 2 * ε ^ 2 := by linarith

end Family

end GGMCollatz
