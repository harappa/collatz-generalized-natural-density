import GGMCollatz.NatDen.UProf.Defs

/-!
# Decomposition of the profile on the uniform side: statements of the intermediate propositions (skeleton)

`uprof_statement` (`NatDen/Statements.lean`) is split into the following seven statements (the uniform side of the
profile argument). All have the form "`∃ α₀ > 1, ∀ α ∈ (1, α₀]`"; the assembly (`UProf.lean`) takes the smallest `α₀`.

```
uniform window P(Pass ∈ E) ≈ (1/Z) Σ_n urow(n)              (UC)   concentration, event identity (Lemma 7.10 of the paper)
Σ_n urow(n) ≈ Σ_n umain(n)            (error Z·L^{-c})       (URD)  recounting via preimages, identity (K), window replacement
Σ_n umain(n) ≈ kernSum = Σ_{M∈E'(E)} q^{m₁}ω_{m₁}(M) D(M)  (UM)   master formula (Lemma 7.18 of the paper)
kernSum/Z ≈ (μ/d) ψ(E)                                       (UF)   kernel values, number of window points, scale m₁ → m₀
D(M) = (1/d)(Y/M)(1 + O(L^{-c}))                            (DK)   kernel bound (Lemma 7.21 of the paper)
C_k(X) = q^k Σ_{M∈E', M≡X} 1/M ≤ K                          (EP1)  structure of E' (Lemma 7.13 (ii) of the paper)
#{M ∈ E' ∩ (A,B] | M ≡ X} = q^{-k}#(E' ∩ (A,B]) + O(x^{1/2})   (EP2)  flatness on residue classes (Lemma 7.13 (i)(iii) of the paper)
```
Notation: `y = x^α`, `Y = (x^α)^α`, `Z = wCard`, `L = log x`, `k = n - m₀`, `E' = F.Eprime α x Set.univ`.
-/

namespace GGMCollatz

namespace ND

variable (F : Family)

/-- **(UC)** Concentration and the event identity: the first-passage probability of the uniform window is approximated by the sum of the row counts. -/
def uconc_statement : Prop :=
  ∃ α₀ : ℝ, 1 < α₀ ∧ ∀ α : ℝ, 1 < α → α ≤ α₀ → ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
    ∀ᶠ x : ℝ in Filter.atTop, 0 < wCard F α x ∧ ∀ E : Set ℕ,
      |Family.expect (unifWin F (x ^ α) ((x ^ α) ^ α))
          (Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ E} 1)
        - (∑ n ∈ rows F α x, (urow F α x E n : ℝ)) / wCard F α x| ≤ K * Real.log x ^ (-c)

/-- **(URD)** Recounting via preimages (Lemma 7.9 of the paper, identity (K)) and window replacement (using (IRR)). -/
def urd_statement : Prop :=
  ∃ α₀ : ℝ, 1 < α₀ ∧ ∀ α : ℝ, 1 < α → α ≤ α₀ → ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
    ∀ᶠ x : ℝ in Filter.atTop, ∀ E : Set ℕ,
      |∑ n ∈ rows F α x, (urow F α x E n : ℝ) - ∑ n ∈ rows F α x, umain F α x E n|
        ≤ K * wCard F α x * Real.log x ^ (-c)

/-- **(UM)** The master formula (Lemma 7.18 of the paper): remove the restriction to good tuples, discard the non-central `s`,
replace `P(Σa = s, F_k ≡ M)` by `P(s_k = s) q^{-(k - m₁)} ω_{m₁}(M)` via the product formula (Proposition 6.12 (c) of the paper), and put
the non-central `s` back into the kernel. -/
def umaster_statement : Prop :=
  ∃ α₀ : ℝ, 1 < α₀ ∧ ∀ α : ℝ, 1 < α → α ≤ α₀ → ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
    ∀ᶠ x : ℝ in Filter.atTop, ∀ E : Set ℕ,
      |∑ n ∈ rows F α x, umain F α x E n - kernSum F α x E| ≤ K * wCard F α x * Real.log x ^ (-c)

/-- **(UF)** Conclusion: the kernel values `D(M) ≈ (1/d)(Y/M)`, `Z ≈ Y/μ`, and passage from the profile at scale `m₁`
to the profile `ψ` at scale `m₀` (GGM Prop. 4.1). -/
def ufinal_statement : Prop :=
  ∃ α₀ : ℝ, 1 < α₀ ∧ ∀ α : ℝ, 1 < α → α ≤ α₀ → ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
    ∀ᶠ x : ℝ in Filter.atTop, 0 < wCard F α x ∧ ∀ E : Set ℕ,
      |kernSum F α x E / wCard F α x - F.mu / F.drift * F.psi α x E| ≤ K * Real.log x ^ (-c)

/-- **(DK)** The kernel bound (Lemma 7.21 of the paper): uniformly in `M ∈ [Mlo, Mhi]`, `D(M) = (1/d)(Y/M)(1 + O(L^{-c}))`. -/
def dkern_statement : Prop :=
  ∃ α₀ : ℝ, 1 < α₀ ∧ ∀ α : ℝ, 1 < α → α ≤ α₀ → ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
    ∀ᶠ x : ℝ in Filter.atTop, ∀ M : ℝ, F.Mlo α x ≤ M → M ≤ F.Mhi α x →
      |kern F α x M - (x ^ α) ^ α / (F.drift * M)| ≤ K * ((x ^ α) ^ α / M) * Real.log x ^ (-c)

/-- **(EP1)** Boundedness of `C_k` (Lemma 7.13 (ii) of the paper): for `k ≤ n₀` (`q^k ≤ x^{1/5}`),
`C_k(X) = q^k Σ_{M ∈ E', M ≡ X (q^k)} 1/M ≤ K`. -/
def eprimeC_statement : Prop :=
  ∃ α₀ : ℝ, 1 < α₀ ∧ ∀ α : ℝ, 1 < α → α ≤ α₀ → ∃ K : ℝ, 0 < K ∧
    ∀ᶠ x : ℝ in Filter.atTop, ∀ k ≤ F.nZero x, ∀ X : ZMod (F.q ^ k),
      F.cE α x Set.univ k X ≤ K

open Classical in
/-- **(EP2)** Flatness on residue classes (Lemma 7.13 (i)(iii) of the paper): for `k ≤ n₀`, an interval `(A, B]` and `X`,
`|#{M ∈ E' ∩ (A,B] | M ≡ X (q^k)} - q^{-k}#(E' ∩ (A,B])| ≤ x^{1/2}` (the number of prefix classes is `Π_x ≤ x^{1/2}/2`). -/
def eprimeFlat_statement : Prop :=
  ∃ α₀ : ℝ, 1 < α₀ ∧ ∀ α : ℝ, 1 < α → α ≤ α₀ →
    ∀ᶠ x : ℝ in Filter.atTop, ∀ k ≤ F.nZero x, ∀ X : ZMod (F.q ^ k), ∀ A B : ℝ,
      |(((F.Eprime α x Set.univ).filter (fun M : ℕ =>
            A < (M : ℝ) ∧ (M : ℝ) ≤ B ∧ ((M : ℕ) : ZMod (F.q ^ k)) = X)).card : ℝ)
        - (F.q : ℝ) ^ (-(k : ℤ)) *
          (((F.Eprime α x Set.univ).filter (fun M : ℕ => A < (M : ℝ) ∧ (M : ℝ) ≤ B)).card : ℝ)|
        ≤ x ^ (1 / 2 : ℝ)

end ND

end GGMCollatz
