import GGMCollatz.NatDen.Statements
import GGMCollatz.NatDen.KronAux

/-!
# (KRON) Equidistribution of the Kronecker orbit `{nλ + u}`

`kron`: from the irrationality measure `IrrMeasure λ c μ`, the block form `kron_statement λ μ` (error `C ℓ^{1-1/μ}` over `ℓ` consecutive points).
`kronW_of_kron`: from the block form, the weighted form `kronW_statement λ μ` (split into blocks and freeze the weight).

The main body of the proof is in `NatDen/KronAux.lean` (depending only on Mathlib). Instead of the Erdős–Turán and Koksma
inequalities used in the paper, we take `λ = A/h + η` by Dirichlet's approximation theorem (`Real.exists_rat_abs_sub_le_and_den_le`)
(`A/h` in lowest terms, `h ≤ Q`, `h²|η| < 1`); `h` consecutive points lie close to a permutation of the lattice `φ + i/h`,
and the Riemann-sum bound for monotone functions makes the error of one block at most `5`. From the irrationality measure,
`h ≥ c^{1/(μ-1)} ℓ^{1/μ}` (`Q = ⌈ℓ^{1-1/μ}⌉`), so the error is `5ℓ/h + h ≤ (5c^{-1/(μ-1)} + 2) ℓ^{1-1/μ}`.
-/

namespace GGMCollatz

namespace ND

/-- **(KRON) block form**: from the irrationality measure. -/
theorem kron {lam c μ : ℝ} (hc : 0 < c) (hμ : 2 ≤ μ) (hirr : IrrMeasure lam c μ) :
    kron_statement lam μ :=
  KronAux.kron_main hc hμ hirr

/-- **(KRON) weighted form**: from the block form (`2 ≤ μ` is not needed at this step, so it is not taken as an argument). -/
theorem kronW_of_kron {lam μ : ℝ} (h : kron_statement lam μ) :
    kronW_statement lam μ :=
  KronAux.kronW_main h

end ND

end GGMCollatz
