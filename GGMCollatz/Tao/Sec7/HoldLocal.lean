import GGMCollatz.Tao.Sec7.HLFpLoc

/-!
# Local limit of the `ℋ` walk (Lemma 2.2 of tao-collatz applied to `Hold`) and the first-passage location (Lemma 7.7)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, from the statements in `TaoCollatz/Prob/LocalBound.lean` (`Gweight`,
`iidSum`), `TaoCollatz/Sec7/HoldLocal.lean` and `TaoCollatz/Sec7/FpLocation.lean`;
generalized to the GGM family (p, q, r). Modified. GGM §7 Step 1 (counterparts of Lemma 2.2 and Lemma 7.7).

The mean of `ℋ = (𝒥, 𝒫_{1,𝒥})` is `(λ, ν)` with `λ = p³/(2(p-1)²)`, `ν = 2μλ = p⁴/(p-1)³`
(`(4, 16)` for `p = 2` in tao-collatz). The first-passage location is `j ≈ s/(2μ) = s(p-1)/(2p)`
(`s/4` in tao-collatz).

* `Gweight t x = e^{-x²/t} + e^{-|x|}`, `iidSum p n` (the law of an i.i.d. sum), `holdSum n`.
* `hold_local_bound` (Lemma 2.2(i)), `hold_tail_bound` (Lemma 2.2(ii)): proved (`HLLocal.lean`;
  the exponential moment, the mean and the quadratic MGF bound are in `HLBase`, `HLMoment`, `HLQuad`; the circle method is in `HLCircle`).
* `fpDist_location_bound` (**Lemma 7.7**), `fpDist_col_le` (column sums): proved (`HLFpLoc.lean`;
  the first-passage decomposition is in `HLFpConv`, the Gaussian bound for the renewal measure and the one-step bound are in `HLRenew`, `HLRenewF`,
  the analytic lemmas are in `HLAnal`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- **The `ℋ` version of Lemma 2.2(i)** (`hold_local_bound` of tao-collatz):
`P(ℋ_{[1,n]} = (j,l)) ≤ C/(1+n) G_{1+n}(c ‖(j - λn, l - νn)‖)`. Proved in `HL.hold_local_boundHL`. -/
theorem hold_local_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (j : ℕ) (l : ℤ),
      ((F.holdSum n) (j, l)).toReal
        ≤ C / (1 + n) * Sec7.Gweight (1 + n)
            (c * ‖(((j : ℝ) - F.holdMean1 * n, (l : ℝ) - F.holdMean2 * n) : ℝ × ℝ)‖) := by
  exact HL.hold_local_boundHL F

/-- **The `ℋ` version of Lemma 2.2(ii)** (`hold_tail_bound` of tao-collatz):
`P(‖ℋ_{[1,n]} - (λn, νn)‖ ≥ λ') ≤ C G_{1+n}(c λ')`. Proved in `HL.hold_tail_boundHL`. -/
theorem hold_tail_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' d : ℕ × ℤ,
          if lam ≤ ‖(((d.1 : ℝ) - F.holdMean1 * n, (d.2 : ℝ) - F.holdMean2 * n) : ℝ × ℝ)‖
          then ((F.holdSum n) d).toReal else 0)
        ≤ C * Sec7.Gweight (1 + n) (c * lam) := by
  exact HL.hold_tail_boundHL F

/-- **Lemma 7.7** (distribution of the first-passage location, `fpDist_location_bound` of tao-collatz):
`P(endpoint = (j,l)) ≤ C e^{-c(l-s)}/√(1+s) · G_{1+s}(c(j - s(p-1)/(2p)))`. Proved in `HL.fpDist_location_boundHL`. -/
theorem fpDist_location_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ (s : ℕ) (j : ℕ) (l : ℤ),
      (F.fpDist s (j, l)).toReal
        ≤ C * (Real.exp (-c * ((l : ℝ) - s)) / Real.sqrt (1 + s))
            * Sec7.Gweight (1 + s) (c * ((j : ℝ) - s * F.slopeInv)) := by
  exact HL.fpDist_location_boundHL F

/-- **Column form of Lemma 7.7** (`fpDist_col_le` of tao-collatz): the marginal law of the endpoint column `j` is
`≤ C' G_{1+s}(c(j - s(p-1)/(2p)))/√(1+s)`. Proved in `HL.fpDist_col_leHL`. -/
theorem fpDist_col_le :
    ∃ c : ℝ, 0 < c ∧ ∃ C' : ℝ, 0 < C' ∧ ∀ (s j : ℕ),
      ∑' l : ℤ, (F.fpDist s (j, l)).toReal
        ≤ C' * (Sec7.Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) * F.slopeInv))
                  / Real.sqrt (1 + (s : ℝ))) := by
  exact HL.fpDist_col_leHL F

end Family

end GGMCollatz
