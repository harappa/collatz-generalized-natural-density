import GGMCollatz.NatDen.Statements

/-!
# The top conversion (Lemma 8.2 of the paper)

The probabilistic part of the assembly of (B).

* `stepHyp_of_prop35_alpha`: from the form of GGM Prop. 3.5, the one-step recursion `Asm.StepHyp` for **any** window width
  `α > 1` with `α² < 1 + c` (`oneStep_of_prop35'` of `Assembly/Step.lean` fixes `α = 1 + min(c,1)/3`, but
  (B) needs `α` at most the `α₀` of (D.1) and (D.2'), so the same proof is rewritten for general `α`).
* `card_filter_eq_mul_expect_unifWin`: the number of points of an event in the uniform window is `#W × probability`.
* `unif_bad_le`: if `N₀ ≤ x`, then in the uniform window `[x^α, x^{α²}]` the probability of `S_min > N₀` is at most
  `P(T_x = ∞) + TV[Pass_x(uniform), Pass_x(logarithmic)] + P(N₀, x^α)` (the inequality of the top conversion).
* `count_top`: the number of bad points in `ℕ_p ∩ [1, x^{α²}]` is at most `x^α + x^{α²}(…)` (split into the points `N < y`
  and the points of the window).
-/

namespace GGMCollatz

namespace ND

open Asm

variable (F : Family)

/-- From the form of GGM Prop. 3.5, the one-step recursion for any `α > 1` with `α² < 1 + c` (generalization of `oneStep_of_prop35'`). -/
theorem stepHyp_of_prop35_alpha (h : F.prop35_statement) :
    ∃ c : ℝ, 0 < c ∧ ∀ α : ℝ, 1 < α → α ^ 2 < 1 + c →
      ∃ Cs : ℝ, 0 ≤ Cs ∧ Asm.StepHyp F α c Cs 2 := by
  obtain ⟨c, hc, hP⟩ := h
  refine ⟨c, hc, ?_⟩
  intro α hα1 hα2c
  have hα2 : 1 < α ^ 2 := by nlinarith
  have hαc : α < 1 + c := by nlinarith
  obtain ⟨K₁, hK₁, h₁⟩ := hP α α hα1 hαc hα1 hαc
  obtain ⟨K₂, hK₂, h₂⟩ := hP α (α ^ 2) hα1 hαc hα2 hα2c
  refine ⟨K₁ + K₂, by linarith, ?_⟩
  intro x hx N₀ hN₀ hN₀x
  have hx0 : 0 ≤ x := by linarith
  have hxn : N₀ ≤ ⌊x⌋₊ := Nat.le_floor hN₀x
  obtain ⟨-, hB1⟩ := h₁ x hx
  obtain ⟨hA2, -⟩ := h₂ x hx
  have e3 : α * α = α ^ 2 := by ring
  have e4 : α ^ 2 * α = α * α ^ 2 := by ring
  set μ := F.logUnif (x ^ (α ^ 2)) (x ^ (α * α ^ 2)) with hμdef
  set ν := F.logUnif (x ^ α) (x ^ (α ^ 2)) with hνdef
  have hμ : F.logUnif (x ^ (α * α)) (x ^ (α ^ 2 * α)) = μ := by rw [e3, e4]
  have hν : F.logUnif (x ^ α) (x ^ (α * α)) = ν := by rw [e3]
  rw [hμ, hν] at hB1
  have hwμ : F.windowProb α N₀ (x ^ (α ^ 2)) =
      Family.expect μ ({N | N₀ < F.Smin N}.indicator 1) := by
    unfold Family.windowProb
    rw [← Real.rpow_mul hx0, mul_comm]
  have hwν : F.windowProb α N₀ (x ^ α) =
      Family.expect ν ({N | N₀ < F.Smin N}.indicator 1) := by
    unfold Family.windowProb
    rw [← Real.rpow_mul hx0, e3]
  rw [hwμ, hwν]
  have d1 := expect_bad_eq F μ hN₀ hxn
  have d2 := expect_bad_eq F ν hN₀ hxn
  have t := abs_expect_indicator_sub_le_dTV (ν.map (F.passLoc ⌊x⌋₊)) (μ.map (F.passLoc ⌊x⌋₊))
    {m | N₀ < F.Smin m}
  have t' := (abs_sub_le_iff.mp t).2
  have nn := expect_indicator_nonneg ν {N | ¬ F.passes ⌊x⌋₊ N}
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlx : Real.log x ≤ x := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < x); linarith
  have hr : x ^ (-c) ≤ (Real.log x) ^ (-c) := Real.rpow_le_rpow_of_nonpos hlog hlx (by linarith)
  have hr' : K₂ * x ^ (-c) ≤ K₂ * (Real.log x) ^ (-c) := mul_le_mul_of_nonneg_left hr hK₂.le
  have hA2' : Family.expect μ ({N | ¬ F.passes ⌊x⌋₊ N}.indicator 1) ≤ K₂ * x ^ (-c) := hA2
  nlinarith

/-- The number of points of an event in the uniform window is `#W × probability`. -/
theorem card_filter_eq_mul_expect_unifWin (lo hi : ℝ) (P : ℕ → Prop) [DecidablePred P] :
    (((F.logWindow lo hi).filter P).card : ℝ) =
      ((F.logWindow lo hi).card : ℝ) * Family.expect (unifWin F lo hi) ({N | P N}.indicator 1) := by
  classical
  by_cases hW : (F.logWindow lo hi).Nonempty
  · rw [expect_indicator]
    have hU : unifWin F lo hi = PMF.uniformOfFinset _ hW := by
      unfold unifWin; rw [dif_pos hW]
    rw [hU, PMF.toOuterMeasure_uniformOfFinset_apply, ENNReal.toReal_div, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast]
    have hc : ((F.logWindow lo hi).card : ℝ) ≠ 0 := by exact_mod_cast hW.card_pos.ne'
    rw [mul_div_cancel₀ _ hc]
    norm_cast
    congr 1
    ext N
    simp
  · have h0 : F.logWindow lo hi = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    simp [h0]

/-- The inequality of the top conversion: if `N₀ ≤ x`, then in the uniform window `[x^α, x^{α²}]` the probability of `S_min > N₀`
is at most `P(T_x = ∞) + TV[Pass_x(uniform), Pass_x(logarithmic)] + P(N₀, x^α)`. -/
theorem unif_bad_le (α x : ℝ) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (hxN : (N₀ : ℝ) ≤ x) :
    Family.expect (unifWin F (x ^ α) ((x ^ α) ^ α)) ({N | N₀ < F.Smin N}.indicator 1) ≤
      Family.expect (unifWin F (x ^ α) ((x ^ α) ^ α)) ({N | ¬ F.passes ⌊x⌋₊ N}.indicator 1) +
      Family.dTV ((unifWin F (x ^ α) ((x ^ α) ^ α)).map (F.passLoc ⌊x⌋₊))
          ((F.logUnif (x ^ α) ((x ^ α) ^ α)).map (F.passLoc ⌊x⌋₊)) +
      F.windowProb α N₀ (x ^ α) := by
  have hxn : N₀ ≤ ⌊x⌋₊ := Nat.le_floor hxN
  set μ := unifWin F (x ^ α) ((x ^ α) ^ α) with hμ
  set ν := F.logUnif (x ^ α) ((x ^ α) ^ α) with hν
  have d1 := expect_bad_eq F μ hN₀ hxn
  have d2 := expect_bad_eq F ν hN₀ hxn
  have t := abs_expect_indicator_sub_le_dTV (μ.map (F.passLoc ⌊x⌋₊)) (ν.map (F.passLoc ⌊x⌋₊))
    {m | N₀ < F.Smin m}
  have t' := (abs_sub_le_iff.mp t).1
  have nn := expect_indicator_nonneg ν {N | ¬ F.passes ⌊x⌋₊ N}
  have hw : F.windowProb α N₀ (x ^ α) = Family.expect ν ({N | N₀ < F.Smin N}.indicator 1) := rfl
  rw [hw]
  linarith

open Classical in
/-- **Counting form of the top conversion (Lemma 8.2 (ii) of the paper)**: if `1 ≤ N₀ ≤ x` and `x ≥ 0`, then
`#{N ∈ ℕ_p ∩ [1, x^{α²}] | S_min(N) > N₀} ≤ x^α + x^{α²} (P(T_x = ∞) + TV + P(N₀, x^α))`
(the probabilities are over the uniform window `[x^α, x^{α²}]`). -/
theorem count_top (α x : ℝ) (hx : 0 ≤ x) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (hxN : (N₀ : ℝ) ≤ x) :
    (((Finset.Icc 1 ⌊(x ^ α) ^ α⌋₊).filter (fun N => N % F.p ≠ 0 ∧ N₀ < F.Smin N)).card : ℝ) ≤
      x ^ α + (x ^ α) ^ α *
        (Family.expect (unifWin F (x ^ α) ((x ^ α) ^ α)) ({N | ¬ F.passes ⌊x⌋₊ N}.indicator 1) +
          Family.dTV ((unifWin F (x ^ α) ((x ^ α) ^ α)).map (F.passLoc ⌊x⌋₊))
            ((F.logUnif (x ^ α) ((x ^ α) ^ α)).map (F.passLoc ⌊x⌋₊)) +
          F.windowProb α N₀ (x ^ α)) := by
  set y := x ^ α with hy
  set X := y ^ α with hX
  have hy0 : 0 ≤ y := Real.rpow_nonneg hx α
  have hX0 : 0 ≤ X := Real.rpow_nonneg hy0 α
  set W := F.logWindow y X with hW
  set S := (Finset.Icc 1 ⌊X⌋₊).filter (fun N => N % F.p ≠ 0 ∧ N₀ < F.Smin N) with hS
  have hsub : S ⊆ Finset.Icc 1 ⌊y⌋₊ ∪ W.filter (fun N => N₀ < F.Smin N) := by
    intro N hN
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hN
    obtain ⟨⟨hN1, hNX⟩, hNp, hbad⟩ := hN
    rw [Finset.mem_union]
    by_cases hNy : (N : ℝ) < y
    · left
      rw [Finset.mem_Icc]
      exact ⟨hN1, Nat.le_floor hNy.le⟩
    · right
      push Not at hNy
      rw [Finset.mem_filter]
      refine ⟨mem_logWindow.mpr ⟨hNp, hNy, ?_⟩, hbad⟩
      exact le_trans (Nat.cast_le.mpr hNX) (Nat.floor_le hX0)
  have hWsub : W ⊆ Finset.Icc 1 ⌊X⌋₊ := by
    intro N hN
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr (ne_zero_of_mem_logWindow hN),
      Nat.le_floor (mem_logWindow.mp hN).2.2⟩
  have hWcard : (W.card : ℝ) ≤ X := by
    have h1 : W.card ≤ ⌊X⌋₊ := by
      have := Finset.card_le_card hWsub
      rwa [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact le_trans (Nat.cast_le.mpr h1) (Nat.floor_le hX0)
  have hycard : ((Finset.Icc 1 ⌊y⌋₊).card : ℝ) ≤ y := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
    exact Nat.floor_le hy0
  have hE := unif_bad_le F α x hN₀ hxN
  rw [← hy, ← hX] at hE
  have hE0 := expect_indicator_nonneg (unifWin F y X) {N | N₀ < F.Smin N}
  have hcnt := card_filter_eq_mul_expect_unifWin F y X (fun N => N₀ < F.Smin N)
  rw [← hW] at hcnt
  have h1 : (S.card : ℝ) ≤ ((Finset.Icc 1 ⌊y⌋₊).card : ℝ) +
      ((W.filter (fun N => N₀ < F.Smin N)).card : ℝ) := by
    have := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    exact_mod_cast this
  have h2 : ((W.filter (fun N => N₀ < F.Smin N)).card : ℝ) ≤
      X * Family.expect (unifWin F y X) ({N | N₀ < F.Smin N}.indicator 1) := by
    rw [hcnt]
    exact mul_le_mul_of_nonneg_right hWcard hE0
  have h3 : X * Family.expect (unifWin F y X) ({N | N₀ < F.Smin N}.indicator 1) ≤
      X * (Family.expect (unifWin F y X) ({N | ¬ F.passes ⌊x⌋₊ N}.indicator 1) +
          Family.dTV ((unifWin F y X).map (F.passLoc ⌊x⌋₊))
            ((F.logUnif y X).map (F.passLoc ⌊x⌋₊)) +
          F.windowProb α N₀ y) :=
    mul_le_mul_of_nonneg_left hE hX0
  linarith

end ND

end GGMCollatz
