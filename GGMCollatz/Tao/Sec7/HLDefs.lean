import GGMCollatz.Tao.Sec7.Unroll

/-!
# Definitions for the local limit of the `ℋ` walk (definitions moved upstream from `HoldLocal.lean`)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, files `TaoCollatz/Prob/LocalBound.lean` (`Gweight`,
`iidSum`) and `TaoCollatz/Sec7/Unroll.lean` (`holdSum`); generalized to the GGM family (p, q, r). Modified.
Names and statements are as they were in `HoldLocal.lean` (moved upstream so that the `HL*.lean` files can use them).
-/

open scoped ENNReal

namespace GGMCollatz

namespace Sec7

/-- The Gaussian-plus-exponential weight `G_t(x) = e^{-x²/t} + e^{-|x|}` (`Gweight` of tao-collatz). -/
noncomputable def Gweight (t x : ℝ) : ℝ := Real.exp (-(x ^ 2) / t) + Real.exp (-|x|)

theorem Gweight_pos (t x : ℝ) : 0 < Gweight t x :=
  add_pos (Real.exp_pos _) (Real.exp_pos _)

/-- The law of a sum of i.i.d. variables on a commutative monoid (`iidSum` of tao-collatz). -/
noncomputable def iidSum {M : Type*} [AddCommMonoid M] (p : PMF M) (n : ℕ) : PMF M :=
  (p.iid n).map fun v => ∑ i, v i

end Sec7

namespace Family

variable (F : Family)

/-- First coordinate of the mean of `ℋ`: `λ = p³/(2(p-1)²)` (`E𝒥`). -/
noncomputable def holdMean1 : ℝ := (F.p : ℝ) ^ 3 / (2 * ((F.p : ℝ) - 1) ^ 2)

/-- Second coordinate of the mean of `ℋ`: `ν = 2μλ = p⁴/(p-1)³` (`E𝒫_{1,𝒥}`). -/
noncomputable def holdMean2 : ℝ := (F.p : ℝ) ^ 4 / ((F.p : ℝ) - 1) ^ 3

/-- Column advance per unit height `1/(2μ) = (p-1)/(2p)` (the central slope of the first-passage location). -/
noncomputable def slopeInv : ℝ := ((F.p : ℝ) - 1) / (2 * (F.p : ℝ))

/-- The law of the sum of `n` steps of `ℋ` (`holdSum` of tao-collatz). -/
noncomputable def holdSum (n : ℕ) : PMF (ℕ × ℤ) :=
  (F.hold.iid n).map fun v => (∑ i, (v i).1, ∑ i, (v i).2)

end Family

end GGMCollatz
