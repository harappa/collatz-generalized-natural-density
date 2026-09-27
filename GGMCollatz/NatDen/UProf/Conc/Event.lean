import GGMCollatz.NatDen.UProf.Conc.Good

/-!
# Auxiliary for (UC): the event identity on good tuples

Source: the check of the range of the window points (`x < N ≤ x^{θ₀}`) is adapted from `mem_Iy_of_not_edge` in
`Tao/Sec5/Drift.lean` (derived from `TaoCollatz/Sec5/ApproxFormula.lean` of gotrevor/tao-collatz (Apache-2.0),
commit 15efca2), changed to the uniform window `[x^α, (x^α)^α]`.

For a point `N` of the window `W = ℕ_p ∩ [x^α, (x^α)^α]` (`α² ≤ θ₀`) whose valuation sequence `a^{(n₀)}(N)` is a good tuple:

* the passage time `T_x(N)` lies in `[2m₀, n₀]` (`passTime_est`: `d T ≥ log(N/x) - O(log^{0.6} x)
  ≥ (α-1) log x - O(log^{0.6} x) ≥ 2 d m₀`, `m₀ = ⌊(α-1) log x/(4d)⌋`);
* for each row `n ∈ [2m₀, n₀]`, `a^{(n-m₀)}(N)` is also a good tuple (`goodVec_prefix`), and the event identity
  (`event_identity`, `β = α`) gives `S^{n-m₀}(N) ∈ E'(E) ⟺ T_x(N) = n ∧ Pass_x(N) ∈ E`.

Hence `Σ_{n ∈ [2m₀, n₀]} 1[a^{(n-m₀)}(N) ∈ A^{(n-m₀)}, S^{n-m₀}(N) ∈ E'(E)] = 1[Pass_x(N) ∈ E]` (`event_sum`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace ConcAux

variable (F : Family)

open Family

open Classical in
/-- The sum of the row indicators `g(N) = Σ_{n ∈ [2m₀, n₀]} 1[a^{(n-m₀)}(N) ∈ A^{(n-m₀)}, S^{n-m₀}(N) ∈ E'(E)]`. -/
noncomputable def rowSum (α x : ℝ) (E : Set ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ rows F α x, if (F.goodVec x (F.valVec N (n - F.mZero α x)) ∧
      F.S^[n - F.mZero α x] N ∈ F.Eprime α x E) then (1 : ℝ) else 0

theorem rowSum_nonneg (α x : ℝ) (E : Set ℕ) (N : ℕ) : 0 ≤ rowSum F α x E N := by
  unfold rowSum
  exact Finset.sum_nonneg fun n _ => by split_ifs <;> norm_num

theorem rowSum_le (α x : ℝ) (E : Set ℕ) (N : ℕ) :
    rowSum F α x E N ≤ ((rows F α x).card : ℝ) := by
  unfold rowSum
  calc _ ≤ ∑ _n ∈ rows F α x, (1 : ℝ) := Finset.sum_le_sum fun n _ => by split_ifs <;> norm_num
    _ = ((rows F α x).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The event identity on good tuples**: if `x` is large, `N ∈ W` and `a^{(n₀)}(N)` is a good tuple, then
`g(N) = 1[Pass_x(N) ∈ E]` (for every `E`). -/
theorem event_sum {α : ℝ} (hα : 1 < α) (hθ : α ^ 2 ≤ F.thetaMax) : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ E : Set ℕ, ∀ N ∈ F.logWindow (x ^ α) ((x ^ α) ^ α),
      F.goodVec x (F.valVec N (F.nZero x)) →
        rowSum F α x E N = Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ E} 1 N := by
  classical
  have hd := F.drift_pos
  have hp := F.log_p_pos
  filter_upwards [F.passTime_est, F.event_identity α hα,
    eventually_add_mul_rpow_le (show (0.6:ℝ) < 1 by norm_num) one_pos (F.drift + 2)
      (2 * Real.log F.p) (show 0 < (α - 1) / 2 by linarith),
    Filter.eventually_gt_atTop 1] with x hPT hEI hK hx1
  intro E N hNW hgood
  rw [Real.rpow_one] at hK
  obtain ⟨hNp, hyN, hNY⟩ := (F.mem_logWindow_iff).mp hNW
  have hx0 : 0 < x := by linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx1.le
  have hxy : x < x ^ α := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ < x ^ α := Real.rpow_lt_rpow_of_exponent_lt hx1 hα
  have hxN : x < N := lt_of_lt_of_le hxy hyN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNθ : (N : ℝ) ≤ x ^ F.thetaMax := by
    calc (N : ℝ) ≤ (x ^ α) ^ α := hNY
      _ = x ^ (α ^ 2) := by rw [← Real.rpow_mul hx0.le]; ring_nf
      _ ≤ x ^ F.thetaMax := Real.rpow_le_rpow_of_exponent_le hx1.le hθ
  obtain ⟨_, _, hTle, hTest⟩ := hPT N hNp hxN hNθ hgood
  set T := F.passTime ⌊x⌋₊ N with hT
  set m₀ := F.mZero α x with hm₀
  -- `T ≥ 2 m₀`
  have hT2 : 2 * m₀ ≤ T := by
    have hlogN : α * Real.log x ≤ Real.log N := by
      rw [← Real.log_rpow hx0]; exact Real.log_le_log (by positivity) hyN
    rw [Real.log_div hN0.ne' hx0.ne'] at hTest
    have h1 := (abs_le.mp hTest).1
    have hm : (m₀ : ℝ) ≤ (α - 1) * Real.log x / (4 * F.drift) := by
      rw [hm₀]; unfold mZero
      exact Nat.floor_le (div_nonneg (mul_nonneg (by linarith) hL0) (by positivity))
    have h2 : F.drift * (2 * (m₀ : ℝ)) ≤ (α - 1) * Real.log x / 2 := by
      have := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 2 * F.drift)
      calc F.drift * (2 * (m₀ : ℝ)) = 2 * F.drift * m₀ := by ring
        _ ≤ 2 * F.drift * ((α - 1) * Real.log x / (4 * F.drift)) := this
        _ = (α - 1) * Real.log x / 2 := by field_simp; ring
    have h3 : F.drift * (2 * (m₀ : ℝ)) ≤ F.drift * T := by nlinarith
    have : (2 * (m₀ : ℝ)) ≤ T := le_of_mul_le_mul_left h3 hd
    exact_mod_cast this
  -- each row
  have hrow : ∀ n ∈ rows F α x,
      (if (F.goodVec x (F.valVec N (n - m₀)) ∧ F.S^[n - m₀] N ∈ F.Eprime α x E) then (1 : ℝ)
        else 0) = if (n = T ∧ F.passLoc ⌊x⌋₊ N ∈ E) then 1 else 0 := by
    intro n hn
    rw [rows, Finset.mem_Icc] at hn
    have hgood' : F.goodVec x (F.valVec N (n - m₀)) := F.goodVec_prefix hgood (by omega)
    have hiff := hEI N hNp hxN hNθ hgood n hn.1 hn.2 E
    by_cases h : F.S^[n - m₀] N ∈ F.Eprime α x E
    · rw [if_pos ⟨hgood', h⟩, if_pos ⟨(hiff.mp h).1.symm, (hiff.mp h).2⟩]
    · rw [if_neg (fun hh => h hh.2), if_neg (fun hh => h (hiff.mpr ⟨hh.1.symm, hh.2⟩))]
  unfold rowSum
  rw [Finset.sum_congr rfl hrow]
  have hTmem : T ∈ rows F α x := by rw [rows, Finset.mem_Icc]; exact ⟨hT2, hTle⟩
  by_cases hP : F.passLoc ⌊x⌋₊ N ∈ E
  · rw [Set.indicator_of_mem (show N ∈ {N | F.passLoc ⌊x⌋₊ N ∈ E} from hP)]
    simp [hP, hTmem]
  · rw [Set.indicator_of_notMem (show N ∉ {N | F.passLoc ⌊x⌋₊ N ∈ E} from hP)]
    simp [hP]

end ConcAux

end ND

end GGMCollatz
