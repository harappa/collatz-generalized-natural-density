import GGMCollatz.Statement

/-!
# Specification tests for the definitions (worked example `(3, 4, [2, 1])`)

Checks with `decide` (`decide +kernel` for `S`) that the top-level definitions take the intended values (early
detection of vacuous or wrong statements). `native_decide` is not used. `C(1) = 4·1 + 2 = 6`, `C(6) = 2`, `C~(1) = 6/3 = 2`, `S(1) = 6/3 = 2`, `S(2) = (8 + 1)/9 = 1`,
`C(2) = 4·2 + 1 = 9`, `C(7) = 30`, `S(7) = 30/3 = 10`.
-/

namespace GGMCollatz

open Family

example : example34.C 1 = 6 := by decide
example : example34.C 6 = 2 := by decide
example : example34.C 2 = 9 := by decide
example : example34.C 7 = 30 := by decide
example : example34.Ct 1 = 2 := by decide
example : example34.Ct 3 = 1 := by decide
/-! The three examples for `S` used to be checked with `native_decide` (which adds the axiom `Lean.ofReduceBool`,
trusting the compiled evaluator). After a referee pointed this out, they were replaced by `decide +kernel`, which checks
them by kernel reduction (no additional axioms). Plain `decide` does not work: the `padicValNat` inside `S` is defined in
Mathlib via `Nat.maxPowDvdDiv.go` (well-founded recursion, `termination_by n / p`), and definitions by well-founded
recursion are not unfolded by the elaborator's reduction (they are treated as irreducible), so the `Decidable` instance
gets stuck before reducing to `isTrue`/`isFalse` (raising `set_option maxRecDepth` does not help). The kernel can unfold
`WellFounded.fix`, so `decide +kernel` closes these goals immediately for small values. -/
example : example34.S 1 = 2 := by decide +kernel
example : example34.S 2 = 1 := by decide +kernel
example : example34.S 7 = 10 := by decide +kernel

/-! ### Values of `C_min`, and non-vacuity of the left-hand side of (A) (proofs taken from an independent review
of the statements)

Every orbit of the worked example `(3, 4, [2, 1])` enters the cycle with minimum 1 or the cycle with minimum 7;
7 is a periodic point of period 16. -/

theorem per7 : Function.IsPeriodicPt example34.C 16 7 := by
  unfold Function.IsPeriodicPt Function.IsFixedPt; decide

theorem orb7 (k : ℕ) : 7 ≤ example34.C^[k] 7 := by
  rw [← per7.iterate_mod_apply k]
  have hk : k % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have h : ∀ j < 16, 7 ≤ example34.C^[j] 7 := by decide
  exact h _ hk

theorem cmin7 : example34.Cmin 7 = 7 := by
  unfold Family.Cmin
  apply le_antisymm
  · exact Nat.sInf_le ⟨0, rfl⟩
  · apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨k, rfl⟩
    exact orb7 k

theorem cmin5 : example34.Cmin 5 = 5 := by
  unfold Family.Cmin
  apply le_antisymm
  · exact Nat.sInf_le ⟨0, rfl⟩
  · apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨k, rfl⟩
    show 5 ≤ example34.C^[k] 5
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
      rw [Function.iterate_add_apply, show example34.C^[2] 5 = 7 by decide]
      have := orb7 m
      omega

theorem cmin4 : example34.Cmin 4 ≤ 1 := Nat.sInf_le ⟨6, by decide⟩

/-- The left-hand side of (A) is positive for `N₀ = 6`, `x = 7` (`mainA_statement` is not a statement about an
empty sum). -/
example : 0 < ∑ N ∈ (Finset.Icc 1 ⌊(7:ℝ)⌋₊).filter (fun N => 6 < example34.Cmin N), (1 / (N : ℝ)) := by
  apply Finset.sum_pos'
  · intro i hi; positivity
  · refine ⟨7, ?_, by norm_num⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have : ⌊(7:ℝ)⌋₊ = 7 := by norm_num
    refine ⟨⟨by norm_num, by omega⟩, by rw [cmin7]; norm_num⟩

end GGMCollatz
