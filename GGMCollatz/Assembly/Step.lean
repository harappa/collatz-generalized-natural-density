import GGMCollatz.Statement
import GGMCollatz.Assembly.Prob
import GGMCollatz.Assembly.Orbit

/-!
# The assembly of (A), part 3: the one-step recursion (Lemma 5.3 of the paper)

`oneStep_of_prop35'`: `oneStep_statement` from the form `prop35_statement` of GGM's Proposition 3.5.

The window width is `α := 1 + min(c, 1)/3` (`α < 1 + c` and `α² < 1 + c`). For either window `μ`,
`E_μ[1_{S_min > N₀}] = E_μ[1_{T_x = ∞}] + E_{Pass_x(μ)}[1_A]` (`A = {m | S_min(m) > N₀}`, `1 ∉ A`).
For `[x^{α²}, x^{α³}]` we apply the first half of Proposition 3.5 (`β = α²`) to the first term, and compare
the second term with the same term for `[x^α, x^{α²}]` via the total variation from the second half
(`β = α`) (the difference of probabilities of an event is at most `dTV`). The errors are combined using
`x^{-c} ≤ (log x)^{-c}`, with `C_s = K₁ + K₂`, `X_s = 2`. The set `A = {m ≤ x | …}` of the accompanying
paper is replaced by `{m | S_min(m) > N₀}`, dropping `m ≤ x` (since the values of `Pass_x` are `≤ x` or
equal to 1, the probability is the same, and `m ≤ x` is not used).
-/

namespace GGMCollatz

namespace Asm

/-- Decomposition by first passage: if `1 ≤ N₀ ≤ x_n`, then for every distribution `μ`,
`E_μ[1_{S_min > N₀}] = E_μ[1_{T = ∞}] + E_{μ∘Pass^{-1}}[1_{S_min > N₀}]`. -/
theorem expect_bad_eq (F : Family) (μ : PMF ℕ) {xn N₀ : ℕ} (hN₀ : 1 ≤ N₀) (hx : N₀ ≤ xn) :
    Family.expect μ ({N | N₀ < F.Smin N}.indicator 1) =
      Family.expect μ ({N | ¬ F.passes xn N}.indicator 1) +
      Family.expect (μ.map (F.passLoc xn)) ({m | N₀ < F.Smin m}.indicator 1) := by
  have h := bad_eq_union F (N₀ := N₀) hx
  conv_lhs => rw [h]
  rw [expect_indicator_union μ (disjoint_passes F hN₀), expect_map_indicator]

/-- **Lemma 5.3 of the paper**: the one-step recursion from the form of Proposition 3.5. -/
theorem oneStep_of_prop35' (F : Family) (h : F.prop35_statement) : F.oneStep_statement := by
  obtain ⟨c, hc, hP⟩ := h
  set m := min c 1 with hmdef
  have hm : 0 < m := lt_min hc one_pos
  have hm1 : m ≤ 1 := min_le_right _ _
  have hmc : m ≤ c := min_le_left _ _
  set α : ℝ := 1 + m / 3 with hαdef
  have hα1 : 1 < α := by rw [hαdef]; linarith
  have hαc : α < 1 + c := by rw [hαdef]; linarith
  have hα2c : α ^ 2 < 1 + c := by
    rw [hαdef]; nlinarith
  have hα2 : 1 < α ^ 2 := by nlinarith
  obtain ⟨K₁, hK₁, h₁⟩ := hP α α hα1 hαc hα1 hαc
  obtain ⟨K₂, hK₂, h₂⟩ := hP α (α ^ 2) hα1 hαc hα2 hα2c
  refine ⟨α, hα1, c, hc, K₁ + K₂, 2, ?_⟩
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

end Asm

end GGMCollatz
