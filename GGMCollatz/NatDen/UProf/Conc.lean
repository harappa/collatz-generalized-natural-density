import GGMCollatz.NatDen.UProf.Statements
import GGMCollatz.NatDen.UProf.Conc.Event

/-!
# (UC) Concentration on the uniform window and the event identity

On the uniform window, the probability that the valuation sequence is a good tuple (`goodVec`, `n₀` entries) is
`1 - O(L^{-4})` (GGM Prop. 3.1 applied to the uniform window: equidistribution of the residues of the window mod `p^k`).
For `N` giving a good tuple, the passage time lies in `[2m₀, n₀]`, and the event identity
(`event_identity` in `Tao/Sec5/Drift.lean`) gives `1_{Pass ∈ E} = Σ_n 1_{S^{n-m₀}(N) ∈ E'(E)}`.
The cost of weakening the good-tuple condition from `n₀` entries to `k = n - m₀` entries is `P(bad)` per row.

Auxiliaries (namespace `GGMCollatz.ND.ConcAux`):

* `Conc/Window.lean`: the number of points of the uniform window and equidistribution mod `p^k` (`unif_equidist`).
* `Conc/Good.lean`: the law of the valuations on the uniform window (`unif_valuation_law`) and `P(bad) ≤ 2 L^{-4}` (`unif_bad_le`).
* `Conc/Event.lean`: the event identity on good tuples (`event_sum`).

Assembly: `α₀ = √θ₀` (upper end of the window `x^{α²} ≤ x^{θ₀}`). For each `N ∈ W`,
`|1_{Pass ∈ E}(N) - Σ_n 1[...]| ≤ (#rows + 1) · 1[bad](N)` (0 for a good tuple); since `#rows + 1 ≤ n₀ + 2 ≤ L`,
the error is `L · 2L^{-4} = 2 L^{-3}` (`c = 3`, `K = 2`).
-/

namespace GGMCollatz

namespace ND

variable (F : Family)

open Family

/-- The sum of the row counts equals the sum `Σ_{N ∈ W} g(N)` of the row indicators over the window (interchanging the order of summation). -/
theorem ConcAux.sum_urow (α x : ℝ) (E : Set ℕ) :
    ∑ n ∈ rows F α x, (urow F α x E n : ℝ)
      = ∑ N ∈ F.logWindow (x ^ α) ((x ^ α) ^ α), ConcAux.rowSum F α x E N := by
  classical
  unfold urow ConcAux.rowSum
  simp only [Finset.card_filter]
  push_cast
  rw [Finset.sum_comm]

/-- The number of rows is at most `n₀ + 1`. -/
theorem ConcAux.card_rows_le (α x : ℝ) : ((rows F α x).card : ℝ) ≤ F.nZero x + 1 := by
  unfold rows
  rw [Nat.card_Icc]
  have : F.nZero x + 1 - 2 * F.mZero α x ≤ F.nZero x + 1 := Nat.sub_le _ _
  exact_mod_cast this

/-- **(UC)**. -/
theorem uconc : uconc_statement F := by
  classical
  refine ⟨Real.sqrt F.thetaMax, Real.lt_sqrt_of_sq_lt (by rw [one_pow]; exact F.one_lt_thetaMax), ?_⟩
  intro α hα hαθ
  have hθ : α ^ 2 ≤ F.thetaMax := (Real.le_sqrt' (by linarith)).mp hαθ
  refine ⟨3, 2, by norm_num, by norm_num, ?_⟩
  filter_upwards [ConcAux.event_sum F hα hθ, ConcAux.unif_bad_le F hα,
    ConcAux.eventually_card_ge F hα, eventually_log_ge 3, Filter.eventually_ge_atTop 1] with
    x hev hbad hZ hL3 hx1
  set W := F.logWindow (x ^ α) ((x ^ α) ^ α) with hW
  have hZpos : 0 < wCard F α x := by unfold wCard; linarith
  refine ⟨hZpos, fun E => ?_⟩
  have hZ' : (0 : ℝ) < W.card := hZpos
  have hWne : W.Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast hZ'
  set L := Real.log x with hLdef
  have hLpos : 0 < L := by linarith
  -- the expectation as a finite sum
  rw [ConcAux.expect_unifWin F hWne] at hbad ⊢
  have hwc : wCard F α x = (W.card : ℝ) := rfl
  rw [ConcAux.sum_urow F α x E, hwc]
  set f : ℕ → ℝ := Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ E} 1 with hf
  set b : ℕ → ℝ := Set.indicator {N | ¬ F.goodVec x (F.valVec N (F.nZero x))} 1 with hb
  set R : ℝ := ((rows F α x).card : ℝ) with hR
  -- pointwise bound: the difference is 0 for a good tuple, and at most `R + 1` otherwise
  have hpt : ∀ N ∈ W, |f N - ConcAux.rowSum F α x E N| ≤ (R + 1) * b N := by
    intro N hN
    by_cases hg : F.goodVec x (F.valVec N (F.nZero x))
    · rw [hev E N hN hg, sub_self, abs_zero, hb,
        Set.indicator_of_notMem (show N ∉ {N | ¬ F.goodVec x (F.valVec N (F.nZero x))} from
          fun h => h hg)]
      simp
    · rw [hb, Set.indicator_of_mem (show N ∈ {N | ¬ F.goodVec x (F.valVec N (F.nZero x))} from hg),
        Pi.one_apply, mul_one]
      have h1 : 0 ≤ f N := Set.indicator_nonneg (fun _ _ => zero_le_one) N
      have h2 : f N ≤ 1 := (le_abs_self _).trans (abs_indicator_le_one _ N)
      have h3 := ConcAux.rowSum_nonneg F α x E N
      have h4 := ConcAux.rowSum_le F α x E N
      rw [abs_le]; constructor <;> linarith
  -- `R + 1 ≤ n₀ + 2 ≤ L`
  have hRle : R + 1 ≤ L := by
    have h1 := ConcAux.card_rows_le F α x
    have h2 := F.nZero_le hx1
    rw [← hLdef] at h2
    linarith
  have hb0 : 0 ≤ (∑ N ∈ W, b N) / W.card :=
    div_nonneg (Finset.sum_nonneg fun N _ => Set.indicator_nonneg (fun _ _ => zero_le_one) N)
      hZ'.le
  calc |(∑ N ∈ W, f N) / W.card - (∑ N ∈ W, ConcAux.rowSum F α x E N) / W.card|
      = |∑ N ∈ W, (f N - ConcAux.rowSum F α x E N)| / W.card := by
        rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hZ']
    _ ≤ (∑ N ∈ W, |f N - ConcAux.rowSum F α x E N|) / W.card :=
        div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hZ'.le
    _ ≤ (∑ N ∈ W, (R + 1) * b N) / W.card :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum hpt) hZ'.le
    _ = (R + 1) * ((∑ N ∈ W, b N) / W.card) := by rw [← Finset.mul_sum, mul_div_assoc]
    _ ≤ L * (2 * L ^ (-4 : ℝ)) := mul_le_mul hRle hbad hb0 hLpos.le
    _ = 2 * L ^ (-3 : ℝ) := by
        have : L ^ (-3 : ℝ) = L ^ (-4 : ℝ) * L := by
          rw [← Real.rpow_add_one hLpos.ne']; norm_num
        rw [this]; ring

end ND

end GGMCollatz
