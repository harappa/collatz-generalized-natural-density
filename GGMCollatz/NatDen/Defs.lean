import GGMCollatz.StatementB
import GGMCollatz.Main
import GGMCollatz.Tao.Prob.LocalBound
import GGMCollatz.Tao.Prob.LocalInstances

/-!
# Definitions for the formalization of (B)

Definitions used to prove (B) (`Family.mainB_statement`, the power rate in natural density). They correspond to the notation
of the accompanying paper. The namespace is `GGMCollatz.ND` (to avoid clashes with existing names). The statements
(intermediate propositions) are in `NatDen/Statements.lean`.

* `lam F = log q / log p` (the paper's `λ = λ_{p,q}`) and the irrationality-measure predicate `IrrMeasure` (the condition (IRR)).
* `unifWin F lo hi`: the uniform distribution on the window `ℕ_p ∩ [lo, hi]` (the paper's `Ñ_y`; the window is a closed interval,
  with the same support as `logUnif`).
* `nb p n s = P(s_n = s)` (the sum of `n` copies of `G(μ)`, negative binomial), `sig2 p = σ_G² = p/(p-1)²`,
  `gauss p n s`: the Gaussian main term of the local limit theorem.
* `jointSZ F n`: the joint distribution of `(𝒮_n, s_n)`, `jp F n Y s = P(𝒮_n = Y, s_n = s)` (the numerator of the law
  conditioned on the sum).
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

variable (F : Family)

/-- `λ = log q / log p` (the paper's `λ_{p,q}`). -/
noncomputable def lam : ℝ := Real.log F.q / Real.log F.p

/-- **Irrationality measure**: `|hλ - m| ≥ c h^{-(μ-1)}` for all `h ≥ 1` and integers `m` (the condition (IRR),
`‖hλ‖ ≥ c h^{-(μ_irr - 1)}`). -/
def IrrMeasure (lam c μ : ℝ) : Prop :=
  ∀ h : ℕ, 1 ≤ h → ∀ m : ℤ, c * (h : ℝ) ^ (-(μ - 1)) ≤ |(h : ℝ) * lam - m|

/-- **Uniform window** `Ñ`: the uniform distribution on `ℕ_p ∩ [lo, hi]` (`logWindow lo hi`). If the window is empty, `pure 1`. -/
noncomputable def unifWin (lo hi : ℝ) : PMF ℕ := by
  classical
  exact if h : (F.logWindow lo hi).Nonempty then PMF.uniformOfFinset _ h else PMF.pure 1

/-- `P(s_n = s)`: the mass of the law of the sum `s_n` of `n` copies of `G(μ)` (negative binomial, `negBinomial_apply`). -/
noncomputable def nb (p n s : ℕ) : ℝ := (iidSum (geomP p) n s).toReal

/-- `σ_G² = μ(μ-1) = p/(p-1)²` (the variance of `G(μ)`). -/
noncomputable def sig2 (p : ℕ) : ℝ := (p : ℝ) / ((p : ℝ) - 1) ^ 2

/-- The Gaussian main term of the local limit theorem, `(2π σ² n)^{-1/2} exp(-(s - μn)²/(2σ²n))`. -/
noncomputable def gauss (p n : ℕ) (s : ℝ) : ℝ :=
  (2 * Real.pi * sig2 p * n) ^ (-(1 / 2 : ℝ)) *
    Real.exp (-(s - muP p * n) ^ 2 / (2 * sig2 p * n))

/-- The joint distribution of `(𝒮_n, s_n)` (`𝒮_n` is the `offsetIn` of the element `syracZ n`, and `s_n` is the valuation sum). -/
noncomputable def jointSZ (n : ℕ) : PMF (ZMod (F.q ^ n) × ℕ) :=
  ((stepLaw F.p).iid n).map (fun v => (F.offsetIn (F.q ^ n) v, ∑ i, (v i).1))

/-- `P(𝒮_n = Y, s_n = s)`.`P(𝒮_n = Y | s_n = s) = jp F n Y s / nb F.p n s`. -/
noncomputable def jp (n : ℕ) (Y : ZMod (F.q ^ n)) (s : ℕ) : ℝ := (jointSZ F n (Y, s)).toReal

end ND

end GGMCollatz
