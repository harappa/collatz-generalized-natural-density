import GGMCollatz.NatDen.UProf.Statements

/-!
# Auxiliary for (URD): the box of valid tuples and the model mass

Tools for handling the recounting via preimages with finite sums.

* `sOf v = Σ a_i` (the valuation sum `|a|`), `fOf F v = fint(a, r ∘ dig)` (`p^{|a|} F_k(a, R)`, in ℤ).
* `box F k T`: the set of all tuples of length `k` with valuations in `[1, T]` and digits in `(0, p)` (a finite set). Elements of the box are
  valid (`validVec`), and their model mass is `p^{-|a|}` (`stepLaw_iid_toReal_of_valid`).
* `sum_box_inv_le`: `Σ_{v ∈ box} p^{-|a|} ≤ 1` (the total model mass).
* `jpG_eq_count`: if `s ≤ T`, then `p^s jpG(k, X, s, G) = #{v ∈ box | |a| = s, F_k(v) = X, G(a)}` (identity (K) of the accompanying paper).
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace URDAux

variable (F : Family)

/-- The valuation sum `|a| = Σ a_i`. -/
def sOf {k : ℕ} (v : Fin k → ℕ × ℕ) : ℕ := ∑ i, (v i).1

/-- `fint(a, r ∘ dig)` (GGM's `F_k(a, R)` multiplied by `p^{|a|}`, in ℤ). -/
def fOf {k : ℕ} (v : Fin k → ℕ × ℕ) : ℤ :=
  F.fint (fun i => (v i).1) (fun i => F.r (v i).2)

/-- The box of valid tuples: valuations `∈ [1, T]`, digits `∈ (0, p)`. -/
def box (k T : ℕ) : Finset (Fin k → ℕ × ℕ) :=
  Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 T ×ˢ Finset.Ioo 0 F.p)

theorem mem_box {k T : ℕ} {v : Fin k → ℕ × ℕ} :
    v ∈ box F k T ↔ ∀ i, (1 ≤ (v i).1 ∧ (v i).1 ≤ T) ∧ (0 < (v i).2 ∧ (v i).2 < F.p) := by
  unfold box
  rw [Fintype.mem_piFinset]
  refine forall_congr' fun i => ?_
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Ioo]

/-- Elements of the box are valid. -/
theorem valid_of_mem_box {k T : ℕ} {v : Fin k → ℕ × ℕ} (hv : v ∈ box F k T) : F.validVec v := by
  intro i
  obtain ⟨⟨h1, -⟩, h2, h3⟩ := (mem_box F).mp hv i
  exact ⟨h1, h2, h3⟩

/-- A valid tuple with `|a| ≤ T` lies in the box. -/
theorem mem_box_of_valid {k T : ℕ} {v : Fin k → ℕ × ℕ} (hv : F.validVec v) (hs : sOf v ≤ T) :
    v ∈ box F k T := by
  rw [mem_box]
  intro i
  obtain ⟨h1, h2, h3⟩ := hv i
  refine ⟨⟨h1, le_trans ?_ hs⟩, h2, h3⟩
  unfold sOf
  exact Finset.single_le_sum (f := fun j => (v j).1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- The model mass of an element of the box is `p^{-|a|}`. -/
theorem iid_toReal_of_mem_box {k T : ℕ} {v : Fin k → ℕ × ℕ} (hv : v ∈ box F k T) :
    ((PMF.iid (stepLaw F.p) k) v).toReal = ((F.p : ℝ) ^ sOf v)⁻¹ := by
  rw [F.stepLaw_iid_toReal_of_valid (valid_of_mem_box F hv), pre_eq_fin_sum]
  rfl

/-- The sum of the masses over a finite set is at most 1. -/
theorem sum_toReal_le_one {α : Type*} (μ : PMF α) (S : Finset α) :
    ∑ a ∈ S, (μ a).toReal ≤ 1 := by
  have h1 : ∑ a ∈ S, μ a ≤ 1 := by
    calc ∑ a ∈ S, μ a ≤ ∑' a, μ a := ENNReal.sum_le_tsum S
      _ = 1 := PMF.tsum_coe μ
  have hne : ∀ a ∈ S, μ a ≠ ⊤ := fun a _ => PMF.apply_ne_top μ a
  rw [← ENNReal.toReal_sum hne]
  have := ENNReal.toReal_mono ENNReal.one_ne_top h1
  simpa using this

/-- **Total model mass**: `Σ_{v ∈ box} p^{-|a|} ≤ 1`. -/
theorem sum_box_inv_le (k T : ℕ) : ∑ v ∈ box F k T, ((F.p : ℝ) ^ sOf v)⁻¹ ≤ 1 := by
  rw [← Finset.sum_congr rfl (fun v hv => iid_toReal_of_mem_box F hv)]
  exact sum_toReal_le_one _ _

/-- **Counting form of identity (K)**: if `s ≤ T`, then `p^s jpG(k, X, s, G)` is the number of tuples in the box satisfying the condition. -/
theorem jpG_eq_count {k T s : ℕ} (hs : s ≤ T) (X : ZMod (F.q ^ k))
    (G : (Fin k → ℕ) → Prop) [DecidablePred G] :
    (F.p : ℝ) ^ s * jpG F k X s G
      = ∑ v ∈ box F k T,
          if (sOf v = s ∧ F.offsetFwd v = X ∧ G (fun i => (v i).1)) then (1 : ℝ) else 0 := by
  classical
  unfold jpG
  rw [tsum_eq_sum (s := box F k T)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [iid_toReal_of_mem_box F hv]
    by_cases hc : sOf v = s ∧ F.offsetFwd v = X ∧ G (fun i => (v i).1)
    · have hc' : ∑ i, (v i).1 = s ∧ F.offsetFwd v = X ∧ G (fun i => (v i).1) := hc
      rw [if_pos hc', if_pos hc, mul_one, hc.1]
      exact mul_inv_cancel₀ (pow_ne_zero _ F.p_real_pos.ne')
    · have hc' : ¬ (∑ i, (v i).1 = s ∧ F.offsetFwd v = X ∧ G (fun i => (v i).1)) := hc
      rw [if_neg hc', if_neg hc, mul_zero, mul_zero]
  · intro v hv
    by_cases h0 : (PMF.iid (stepLaw F.p) k) v = 0
    · rw [h0, ENNReal.toReal_zero, zero_mul]
    · have hval := F.validVec_of_ne_zero h0
      rw [if_neg, mul_zero]
      rintro ⟨hsum, -, -⟩
      exact hv (mem_box_of_valid F hval (by unfold sOf; omega))

end URDAux

end ND

end GGMCollatz
