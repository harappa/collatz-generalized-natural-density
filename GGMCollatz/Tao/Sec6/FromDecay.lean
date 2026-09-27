import GGMCollatz.Tao.Sec6.Assemble
import Mathlib.Analysis.PSeries

/-!
# GGM §5: Proposition 5.1 ⇒ Proposition 4.1 (fine-scale mixing)

Derived from `TaoCollatz/Sec6/MixingRegime.lean` (`osc_syracZ_le_sum_steps`,
`osc_syracZ_regime_telescope_at`) and `TaoCollatz/Sec6/MixingFromDecay.lean` (`fine_scale_mixing`) of
gotrevor/tao-collatz (Apache-2.0), commit 15efca2; generalized to the GGM family (p, q, r).

The reduction at the start of GGM §5 Step 1 ("it suffices to treat `γn ≤ m < n`; the general case follows
from the compatibility of projections, a telescoping sum and the triangle inequality") is carried out as a
telescoping sum of the adjacent-level estimate `osc_step_bound` (`Assemble.lean`):
`Osc_{m,n} ≤ ∑_{m ≤ k < n} Osc_{k,k+1}` (`osc_syracZ_le_sum_steps`), each term `≤ C k^{-(A+2)}`, and
`∑_k k^{-2} < ∞`. Small `m` is absorbed by the trivial upper bound `Osc ≤ 2`.

* `prop41_of_prop51`: **`F.prop51_statement → F.prop41_statement`**.
-/

open scoped BigOperators

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- The oscillation relative to the projection to the same level is 0. -/
theorem osc_syracZ_self (n : ℕ) :
    F.osc n n le_rfl (fun Y => ((F.syracZ n) Y).toReal) = 0 := by
  rw [osc_syracZ_eq_l1_lift]
  simp [syracLift]

/-- The triangle inequality from the compatibility of projections, telescoped along adjacent levels. -/
theorem osc_syracZ_le_sum_steps (m n : ℕ) (hmn : m ≤ n) :
    F.osc m n hmn (fun Y => ((F.syracZ n) Y).toReal) ≤
      ∑ k ∈ Finset.Ico m n,
        F.osc k (k + 1) (Nat.le_succ k) (fun Y => ((F.syracZ (k + 1)) Y).toReal) := by
  induction n, hmn using Nat.le_induction with
  | base => simp [osc_syracZ_self]
  | succ n hmn ih =>
      calc
        F.osc m (n + 1) (hmn.trans (Nat.le_succ n))
            (fun Y => ((F.syracZ (n + 1)) Y).toReal) ≤
            F.osc n (n + 1) (Nat.le_succ n) (fun Y => ((F.syracZ (n + 1)) Y).toReal) +
              F.osc m n hmn (fun Y => ((F.syracZ n) Y).toReal) :=
          F.osc_syracZ_levels_triangle m n (n + 1) hmn (Nat.le_succ n)
        _ ≤ F.osc n (n + 1) (Nat.le_succ n) (fun Y => ((F.syracZ (n + 1)) Y).toReal) +
              ∑ k ∈ Finset.Ico m n,
                F.osc k (k + 1) (Nat.le_succ k) (fun Y => ((F.syracZ (k + 1)) Y).toReal) := by
          gcongr
        _ = ∑ k ∈ Finset.Ico m (n + 1),
              F.osc k (k + 1) (Nat.le_succ k) (fun Y => ((F.syracZ (k + 1)) Y).toReal) := by
          rw [Finset.sum_Ico_succ_top hmn]
          ac_rfl

/-- The mass `ζ(2)`. -/
noncomputable def sZeta2 : ℝ := ∑' k : ℕ, (k : ℝ) ^ (-(2 : ℝ))

theorem sZeta2_nonneg : 0 ≤ sZeta2 :=
  tsum_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- **Reduction across scales**: from the adjacent-level estimate `Osc_{k,k+1} ≤ C k^{-(A+2)}` (`k ≥ M`),
for all `1 ≤ m ≤ n`, `Osc_{m,n} ≤ (2 M^A + C ζ(2)) m^{-A}`. -/
theorem osc_syracZ_telescope (A : ℝ) (hA : 0 < A) (C : ℝ) (hC : 0 < C) (M : ℕ)
    (hstep : ∀ k : ℕ, M ≤ k →
      F.osc k (k + 1) (Nat.le_succ k) (fun Y => ((F.syracZ (k + 1)) Y).toReal)
        ≤ C * (k : ℝ) ^ (-(A + 2))) :
    ∀ n m : ℕ, ∀ hmn : m ≤ n, 1 ≤ m →
      F.osc m n hmn (fun Y => ((F.syracZ n) Y).toReal)
        ≤ (2 * ((max 1 M : ℕ) : ℝ) ^ A + C * sZeta2) * (m : ℝ) ^ (-A) := by
  set N : ℕ := max 1 M with hNdef
  set S : ℝ := ∑' k : ℕ, (k : ℝ) ^ (-(2 : ℝ)) with hSdef
  have hsummable : Summable (fun k : ℕ => (k : ℝ) ^ (-(2 : ℝ))) := by
    rw [Real.summable_nat_rpow]
    norm_num
  have hS0 : 0 ≤ S := tsum_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  intro n m hmn hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmneg : 0 ≤ (m : ℝ) ^ (-A) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hNA : 0 ≤ (N : ℝ) ^ A := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hCS : 0 ≤ C * S := mul_nonneg hC.le hS0
  unfold sZeta2
  rw [← hSdef]
  by_cases hmN : m < N
  · have hmN' : (m : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt hmN)
    have hpow : (m : ℝ) ^ A ≤ (N : ℝ) ^ A :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hmN' hA.le
    calc
      F.osc m n hmn (fun Y => ((F.syracZ n) Y).toReal) ≤ 2 := F.osc_syracZ_le_two m n hmn
      _ = 2 * (m : ℝ) ^ A * (m : ℝ) ^ (-A) := by
        rw [mul_assoc, ← Real.rpow_add hmpos]
        norm_num
      _ ≤ (2 * (N : ℝ) ^ A + C * S) * (m : ℝ) ^ (-A) := by
        have h1 : 2 * (m : ℝ) ^ A * (m : ℝ) ^ (-A) ≤ 2 * (N : ℝ) ^ A * (m : ℝ) ^ (-A) :=
          mul_le_mul_of_nonneg_right (by linarith) hmneg
        have h2 : 0 ≤ C * S * (m : ℝ) ^ (-A) := mul_nonneg hCS hmneg
        calc 2 * (m : ℝ) ^ A * (m : ℝ) ^ (-A) ≤ 2 * (N : ℝ) ^ A * (m : ℝ) ^ (-A) := h1
          _ ≤ 2 * (N : ℝ) ^ A * (m : ℝ) ^ (-A) + C * S * (m : ℝ) ^ (-A) := by linarith
          _ = (2 * (N : ℝ) ^ A + C * S) * (m : ℝ) ^ (-A) := by ring
  · have hNm : N ≤ m := by omega
    have hMm : M ≤ m := le_trans (le_max_right 1 M) hNm
    calc
      F.osc m n hmn (fun Y => ((F.syracZ n) Y).toReal) ≤
          ∑ k ∈ Finset.Ico m n,
            F.osc k (k + 1) (Nat.le_succ k) (fun Y => ((F.syracZ (k + 1)) Y).toReal) :=
        F.osc_syracZ_le_sum_steps m n hmn
      _ ≤ ∑ k ∈ Finset.Ico m n, C * (k : ℝ) ^ (-(A + 2)) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hmk := (Finset.mem_Ico.mp hk).1
        exact hstep k (hMm.trans hmk)
      _ ≤ C * (m : ℝ) ^ (-A) * ∑ k ∈ Finset.Ico m n, (k : ℝ) ^ (-(2 : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hmk : m ≤ k := (Finset.mem_Ico.mp hk).1
        have hkpos : (0 : ℝ) < k := hmpos.trans_le (by exact_mod_cast hmk)
        have hrpow : (k : ℝ) ^ (-A) ≤ (m : ℝ) ^ (-A) :=
          Real.rpow_le_rpow_of_nonpos hmpos (by exact_mod_cast hmk) (neg_nonpos.mpr hA.le)
        rw [show -(A + 2) = -A + -(2 : ℝ) by ring, Real.rpow_add hkpos]
        have hk2 : 0 ≤ (k : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        calc
          C * ((k : ℝ) ^ (-A) * (k : ℝ) ^ (-(2 : ℝ))) =
              C * (k : ℝ) ^ (-A) * (k : ℝ) ^ (-(2 : ℝ)) := by ring
          _ ≤ C * (m : ℝ) ^ (-A) * (k : ℝ) ^ (-(2 : ℝ)) := by gcongr
      _ ≤ C * (m : ℝ) ^ (-A) * S := by
        gcongr
        exact hsummable.sum_le_tsum (Finset.Ico m n)
          (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ (2 * (N : ℝ) ^ A + C * S) * (m : ℝ) ^ (-A) := by
        have h2 : 0 ≤ 2 * (N : ℝ) ^ A * (m : ℝ) ^ (-A) := by positivity
        have : C * (m : ℝ) ^ (-A) * S = C * S * (m : ℝ) ^ (-A) := by ring
        rw [this]
        have : (2 * (N : ℝ) ^ A + C * S) * (m : ℝ) ^ (-A)
            = 2 * (N : ℝ) ^ A * (m : ℝ) ^ (-A) + C * S * (m : ℝ) ^ (-A) := by ring
        rw [this]
        linarith

/-- **GGM §5: Proposition 5.1 ⇒ Proposition 4.1** (counterpart of Tao §6). From polynomial decay of the
characteristic function, fine-scale mixing `Osc_{m,n}(𝒮_n) ≤ C m^{-A}` (for all `A`). -/
theorem prop41_of_prop51 (F : GGMCollatz.Family) (h : F.prop51_statement) :
    F.prop41_statement := by
  intro A hA
  obtain ⟨C, hC, N₀, hstep⟩ := F.osc_step_bound h (A + 2) (by linarith)
  set M : ℕ := max N₀ 1 with hMdef
  have hstepM : ∀ k : ℕ, M ≤ k →
      F.osc k (k + 1) (Nat.le_succ k) (fun Y => ((F.syracZ (k + 1)) Y).toReal)
        ≤ C * (k : ℝ) ^ (-(A + 2)) := by
    intro k hk
    have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
    have hN : N₀ ≤ k + 1 := le_trans (le_max_left _ _) (le_trans hk (Nat.le_succ k))
    have h1 := hstep (k + 1) hN
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hmono : ((k + 1 : ℕ) : ℝ) ^ (-(A + 2)) ≤ (k : ℝ) ^ (-(A + 2)) :=
      Real.rpow_le_rpow_of_nonpos hkpos (by push_cast; linarith) (by linarith)
    calc F.osc k (k + 1) (Nat.le_succ k) (fun Y => ((F.syracZ (k + 1)) Y).toReal)
        ≤ C * ((k + 1 : ℕ) : ℝ) ^ (-(A + 2)) := h1
      _ ≤ C * (k : ℝ) ^ (-(A + 2)) := mul_le_mul_of_nonneg_left hmono hC.le
  refine ⟨2 * ((max 1 M : ℕ) : ℝ) ^ A + C * sZeta2, ?_,
    F.osc_syracZ_telescope A hA C hC M hstepM⟩
  have h1 : (0 : ℝ) < ((max 1 M : ℕ) : ℝ) := by
    have : 1 ≤ max 1 M := le_max_left _ _
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one this
  have := mul_nonneg hC.le sZeta2_nonneg
  have := Real.rpow_pos_of_pos h1 A
  linarith

end Family

end GGMCollatz
