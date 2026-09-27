import GGMCollatz.NatDen.Defs

/-!
# Statements of the intermediate propositions of (B) (skeleton)

The intermediate propositions into which the proof of (B) (`Family.mainB_statement`) is split. **This file is the skeleton;
the proofs are filled in other files.** When changing a statement, check that its users (the assembly up to
`NatDen/Main.lean`) still go through without `sorry`.

Direction of dependencies:

```
(M)  MatveevHyp ──────────────────────────────▶ irr_statement            (a one-line argument)
(KRON) irr ───────────────────────────────────▶ kron_statement ─▶ kronW_statement (Kronecker equidistribution)
(LCLT) ───────────────────────────────────────▶ lclt_statement           (negative binomial LLT)
(SUMCF) lclt + GGM §6 (pair majorant of Sec7)─▶ sumcf_statement          (conditioned characteristic function)
(SUMMIX) sumcf + lclt + GGM §5 (Sec6)─────────▶ summixA / summixB ─▶ summixC (conditioned mixing)
(D1)  GGM Prop. 3.1 (prop33)──────────────────▶ noHit_statement          (no hit in the uniform window)
(UPROF) irr + kronW + lclt + summixC + prop33 + prop41 ─▶ uprof_statement (the uniform side of the profile)
(D2') uprof + logarithmic side (window_formula of Sec5) ─▶ tvPass_statement (the (D.2') comparison)
(TOPCONV) + assembly of (B): noHit + tvPass + window bound of (A) + seed ─▶ mainB_statement (top conversion)
```

Windows: `y = x^α`, the window is `[y, y^α]` (closed intervals for both `unifWin` and `logUnif`). `E'`, `ψ`, `m₀` use the
definitions of the logarithmic side (`Tao/Sec5/Defs.lean`) with `β = α`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

variable (F : Family)

/-! ### (M) Irrationality measure -/

/-- **(IRR)**: the irrationality measure of `λ = log_p q` is finite. -/
def irr_statement : Prop := ∃ c μ : ℝ, 0 < c ∧ 2 ≤ μ ∧ IrrMeasure (lam F) c μ

/-! ### (KRON) Equidistribution of Kronecker orbits -/

/-- Block form of **(KRON)**: for the points `{nλ + u}` over `ℓ` consecutive integers `n`,
and `f` nonincreasing on `[0,1]` with values in `[0,1]`, the difference between the sum of `f` and `ℓ ∫₀¹ f` is at most `C ℓ^{1 - 1/μ}`. -/
def kron_statement (lam μ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ, AntitoneOn f (Set.Icc 0 1) →
    (∀ θ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f θ ∧ f θ ≤ 1) →
    ∀ (u : ℝ) (a : ℤ) (ℓ : ℕ), 1 ≤ ℓ →
      |∑ n ∈ Finset.Ico a (a + ℓ), f (Int.fract ((n : ℝ) * lam + u))
          - (ℓ : ℝ) * ∫ θ in (0 : ℝ)..1, f θ| ≤ C * (ℓ : ℝ) ^ (1 - 1 / μ)

/-- Weighted form of **(KRON)**: if `w ≥ 0` vanishes outside `[a, a+L)`,
`W = Σ w`, `V = Σ_{n ∈ [a-1, a+L)} |w(n+1) - w(n)|` (including the jumps at both ends of the support), then for all `ℓ ≥ 1`,
`|Σ w(n) f({nλ+u}) - W ∫₀¹ f| ≤ 3ℓV + C(W ℓ^{-1/μ} + V ℓ^{1-1/μ})`. -/
def kronW_statement (lam μ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ, AntitoneOn f (Set.Icc 0 1) →
    (∀ θ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f θ ∧ f θ ≤ 1) →
    ∀ (u : ℝ) (a : ℤ) (L : ℕ) (w : ℤ → ℝ), (∀ n, 0 ≤ w n) →
    (∀ n, n ∉ Finset.Ico a (a + L) → w n = 0) → ∀ ℓ : ℕ, 1 ≤ ℓ →
      |∑ n ∈ Finset.Ico a (a + L), w n * f (Int.fract ((n : ℝ) * lam + u))
          - (∑ n ∈ Finset.Ico a (a + L), w n) * ∫ θ in (0 : ℝ)..1, f θ|
        ≤ 3 * ℓ * (∑ n ∈ Finset.Ico (a - 1) (a + L), |w (n + 1) - w n|)
          + C * ((∑ n ∈ Finset.Ico a (a + L), w n) * (ℓ : ℝ) ^ (-(1 / μ))
            + (∑ n ∈ Finset.Ico (a - 1) (a + L), |w (n + 1) - w n|) * (ℓ : ℝ) ^ (1 - 1 / μ))

/-! ### (LCLT) Local limit theorem for the negative binomial -/

/-- **(LCLT)**: for `|s - μn| ≤ n^{3/5}`,
`P(s_n = s) = g(n,s)(1 + O(n^{-1/2} + |s - μn|³/n²))`, where `g` is the Gaussian main term. -/
def lclt_statement (p : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ s : ℕ, |(s : ℝ) - muP p * n| ≤ (n : ℝ) ^ (3 / 5 : ℝ) →
    |nb p n s - gauss p n s| ≤
      C * gauss p n s * ((n : ℝ) ^ (-(1 / 2 : ℝ)) + |(s : ℝ) - muP p * n| ^ 3 / (n : ℝ) ^ 2)

/-! ### (SUMCF) Decay of the characteristic function conditioned on the sum -/

/-- **Proposition 6.7 of the paper**: for `|s - μn| ≤ C√(n log n)` and `q ∤ ξ`,
`‖E[e(-ξ𝒮_n/q^n) 1_{s_n = s}]‖ ≤ K n^{-A} P(s_n = s)` (for every `A`). -/
def sumcf_statement : Prop :=
  ∀ A C : ℝ, 0 < A → 0 < C → ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 ≤ n → ∀ s : ℕ,
    |(s : ℝ) - muP F.p * n| ≤ C * Real.sqrt (n * Real.log n) →
    ∀ ξ : ZMod (F.q ^ n), ¬ (F.q ∣ ξ.val) →
      ‖∑ Y : ZMod (F.q ^ n), (jp F n Y s : ℂ) * eC (-(ξ.val * Y.val : ℚ) / (F.q : ℚ) ^ n)‖
        ≤ K * (n : ℝ) ^ (-A) * nb F.p n s

/-! ### (SUMMIX) Fine-scale mixing conditioned on the sum -/

/-- **Proposition 6.12 (a) of the paper**: for `n^{1/4} ≤ m ≤ n` and `|s - μn| ≤ C√(n log n)`,
`Osc_{m,n}(P(𝒮_n = · , s_n = s)) ≤ K m^{-A} P(s_n = s)`. -/
def summixA_statement : Prop :=
  ∀ A C : ℝ, 0 < A → 0 < C → ∃ K : ℝ, 0 < K ∧ ∀ n m : ℕ, ∀ hmn : m ≤ n, 2 ≤ n →
    (n : ℝ) ^ (1 / 4 : ℝ) ≤ m → ∀ s : ℕ, |(s : ℝ) - muP F.p * n| ≤ C * Real.sqrt (n * Real.log n) →
      F.osc m n hmn (fun Y => jp F n Y s) ≤ K * (m : ℝ) ^ (-A) * nb F.p n s

/-- **Proposition 6.12 (b) of the paper** (stability at coarse scales): for `log⁴ n ≤ m ≤ n^{9/10}` and `|s - μn| ≤ C√(n log n)`,
`Σ_Z |P(𝒮_n ≡ Z (q^m), s_n = s) - P(s_n = s) P(𝒮_m = Z)| ≤ K √(m log n / n) P(s_n = s)`. -/
def summixB_statement : Prop :=
  ∀ C : ℝ, 0 < C → ∃ K : ℝ, 0 < K ∧ ∀ n m : ℕ, ∀ hmn : m ≤ n, 2 ≤ n →
    Real.log n ^ 4 ≤ m → (m : ℝ) ≤ (n : ℝ) ^ (9 / 10 : ℝ) →
    ∀ s : ℕ, |(s : ℝ) - muP F.p * n| ≤ C * Real.sqrt (n * Real.log n) →
      ∑ Z : ZMod (F.q ^ m),
          |(∑ Y ∈ Finset.univ.filter (fun Y : ZMod (F.q ^ n) =>
              ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y = Z), jp F n Y s)
            - nb F.p n s * ((F.syracZ m) Z).toReal|
        ≤ K * Real.sqrt (m * Real.log n / n) * nb F.p n s

/-- **Proposition 6.12 (c) of the paper** (product formula): for `n^{1/4} ≤ m ≤ n^{1/2}` and `|s - μn| ≤ C√(n log n)`,
`Σ_Y |P(𝒮_n = Y, s_n = s) - P(s_n = s) q^{-(n-m)} P(𝒮_m = Y mod q^m)| ≤ K P(s_n = s)(m^{-A} + √(m log n / n))`. -/
def summixC_statement : Prop :=
  ∀ A C : ℝ, 0 < A → 0 < C → ∃ K : ℝ, 0 < K ∧ ∀ n m : ℕ, ∀ hmn : m ≤ n, 2 ≤ n →
    (n : ℝ) ^ (1 / 4 : ℝ) ≤ m → (m : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) →
    ∀ s : ℕ, |(s : ℝ) - muP F.p * n| ≤ C * Real.sqrt (n * Real.log n) →
      ∑ Y : ZMod (F.q ^ n),
          |jp F n Y s - nb F.p n s * (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
            ((F.syracZ m) (ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y)).toReal|
        ≤ K * nb F.p n s * ((m : ℝ) ^ (-A) + Real.sqrt (m * Real.log n / n))

/-! ### First passage from the uniform window (Section 7 of the paper) -/

/-- **(D.1)**: in the uniform window `[x^α, x^{α²}]`, the probability that the orbit never comes to at most `x` is at most `K x^{-c}`. -/
def noHit_statement : Prop :=
  ∃ α₀ : ℝ, 1 < α₀ ∧ ∀ α : ℝ, 1 < α → α ≤ α₀ → ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
    ∀ᶠ x : ℝ in Filter.atTop,
      Family.expect (unifWin F (x ^ α) ((x ^ α) ^ α)) (Set.indicator {N | ¬ F.passes ⌊x⌋₊ N} 1)
        ≤ K * x ^ (-c)

/-- **Profile of the uniform side** (the form (D.3)): the law of the first-passage location from the uniform window
`[x^α, x^{α²}]` is close, uniformly in `E`, to `Φ_x(E) = (μ/d) ψ_α(x, E)` (the same profile as the logarithmic side, `psi` of `Tao/Sec5`). -/
def uprof_statement : Prop :=
  ∃ α₀ : ℝ, 1 < α₀ ∧ ∀ α : ℝ, 1 < α → α ≤ α₀ → ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
    ∀ᶠ x : ℝ in Filter.atTop, ∀ E : Set ℕ,
      |Family.expect (unifWin F (x ^ α) ((x ^ α) ^ α))
          (Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ E} 1) - F.mu / F.drift * F.psi α x E|
        ≤ K * Real.log x ^ (-c)

/-- **(D.2')**: the total variation (the total `ℓ¹`) between the laws of the first-passage location from the uniform and
from the logarithmic distribution on the same window `[x^α, x^{α²}]` is at most `K (log x)^{-c}`. -/
def tvPass_statement : Prop :=
  ∃ α₀ : ℝ, 1 < α₀ ∧ ∀ α : ℝ, 1 < α → α ≤ α₀ → ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
    ∀ᶠ x : ℝ in Filter.atTop,
      Family.dTV ((unifWin F (x ^ α) ((x ^ α) ^ α)).map (F.passLoc ⌊x⌋₊))
          ((F.logUnif (x ^ α) ((x ^ α) ^ α)).map (F.passLoc ⌊x⌋₊))
        ≤ K * Real.log x ^ (-c)

end ND

end GGMCollatz
