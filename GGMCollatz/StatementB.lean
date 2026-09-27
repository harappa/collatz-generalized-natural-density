import GGMCollatz.Statement

/-!
# The statements of (B) and of the family without (d) (frozen)

* `MatveevHyp p q`: the case of two logarithms of **Corollary 2.3** of Matveev (2000, Izv. Math. 64:6,
  1217–1269), checked against the primary source. `α₁ = p`, `α₂ = q` (integers `≥ 2`), the field is `ℚ`
  (`D = 1`; it is real, so `κ = 1`), `A_j = log α_j` (`≥ max(D h(α_j), |ln α_j|, 0.16)`, `h(p) = log p`), and `B` is
  `B* = max(|b₁|, |b₂|)` ((1.4) of the original). The conclusion in the original is
  `ln |Λ| > -C₁(2) D² Ω ln(eD) ln(eB*)` with `C₁(2) = e·30⁵·2^{3.5} ≈ 7.473·10⁸` and `Ω = A₁A₂`.
  **Here the constant is weakened to `10⁹` and the inequality to `≤`** (nothing is stated more strongly than in
  the original). Taking it as an explicit hypothesis is a project decision.
* `Family.mainB_statement`: (B) (a power rate for the natural density).
* `FamilyGen`: the family given only by GGM's Definition 1.2 and (a)(b)(c) (neither (d) nor `q > p` is assumed).
  `mainA_gen_statement`, `mainB_gen_statement`: (A) and (B) for that family.
-/

namespace GGMCollatz

/-- **The case of two logarithms of Matveev (2000) Corollary 2.3** (with the constant rounded up to `10⁹`, on
the safe side). If `b₁ log p + b₂ log q ≠ 0`, then
`|b₁ log p + b₂ log q| ≥ exp(-10⁹ · log p · log q · (1 + log max(|b₁|, |b₂|)))`. -/
def MatveevHyp (p q : ℕ) : Prop :=
  ∀ b₁ b₂ : ℤ, (b₁ : ℝ) * Real.log p + (b₂ : ℝ) * Real.log q ≠ 0 →
    Real.exp (-(10 ^ 9 : ℝ) * Real.log p * Real.log q *
        (1 + Real.log ((max |b₁| |b₂| : ℤ) : ℝ)))
      ≤ |(b₁ : ℝ) * Real.log p + (b₂ : ℝ) * Real.log q|

namespace Family

variable (F : Family)

open Classical in
/-- **The top-level statement of (B)** (Theorem 8.4 of the paper): there are `K, c > 0` such that for all `N₀ ≥ 1` and
`X ≥ 1`, `#{N ≤ X | C_min(N) > N₀} ≤ K X N₀^{-c}`. -/
def mainB_statement : Prop :=
  ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ N₀ : ℕ, 1 ≤ N₀ → ∀ X : ℝ, 1 ≤ X →
    (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => N₀ < F.Cmin N)).card : ℝ) ≤ K * X * (N₀ : ℝ) ^ (-c)

end Family

/-- The family given only by GGM's Definition 1.2 and (a)(b)(c) (neither (d) nor `q > p` is assumed). -/
structure FamilyGen where
  p : ℕ
  q : ℕ
  r : ℕ → ℤ
  two_le_p : 2 ≤ p
  two_le_q : 2 ≤ q
  /-- (a) -/
  coprime : Nat.Coprime p q
  /-- (b) -/
  subcritical : (q : ℝ) < (p : ℝ) ^ ((p : ℝ) / ((p : ℝ) - 1))
  /-- (c) -/
  divisible : ∀ j : ℕ, 0 < j → j < p → (p : ℤ) ∣ (q : ℤ) * j + r j
  /-- `qj + r(j) ≥ 1` from Definition 1.2. -/
  positive : ∀ j : ℕ, 0 < j → j < p → 1 ≤ (q : ℤ) * j + r j

namespace FamilyGen

variable (G : FamilyGen)

/-- The GGM map `C` (the same formula as `Family.C`). -/
def C (N : ℕ) : ℕ :=
  if N % G.p = 0 then N / G.p else ((G.q : ℤ) * N + G.r (N % G.p)).toNat

/-- `C_min(N)`. -/
noncomputable def Cmin (N : ℕ) : ℕ := sInf (Set.range fun k => G.C^[k] N)

/-- The statement of (A) (for the whole family). -/
def mainA_gen_statement : Prop :=
  ∃ K c' : ℝ, 0 < K ∧ 0 < c' ∧ ∀ N₀ : ℕ, 1 ≤ N₀ → ∀ x : ℝ, 3 ≤ x →
    ∑ N ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun N => N₀ < G.Cmin N), (1 / (N : ℝ))
      ≤ K * (N₀ : ℝ) ^ (-c') * Real.log x

open Classical in
/-- The statement of (B) (for the whole family). -/
def mainB_gen_statement : Prop :=
  ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ N₀ : ℕ, 1 ≤ N₀ → ∀ X : ℝ, 1 ≤ X →
    (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => N₀ < G.Cmin N)).card : ℝ) ≤ K * X * (N₀ : ℝ) ^ (-c)

end FamilyGen

end GGMCollatz
