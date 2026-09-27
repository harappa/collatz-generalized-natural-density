import GGMCollatz.Basic

/-!
# The statements of the main results (frozen)

The claims of the accompanying paper, written as Lean statements. **This is the surface to be checked**; the
proofs are supplied in other modules. Any change to these statements is recorded in the project's decision log.

* `seed_statement`: Theorem 4.1 of the paper. An upper bound for the number of elements of a shell whose orbit under the
  reduced map stays `≥ p^L`.
* `prop35_statement`: the form of GGM's Proposition 3.5 (the counterpart of Tao's Proposition 1.11) used here.
  Windows are closed intervals (tao-collatz convention) and the total variation is the full `L¹` distance.
  **It is proved, not assumed.**
* `oneStep_statement`: Lemma 5.3 of the paper (the one-step recursion).
* `mainA_statement`: Theorem 5.7 (ii) of the paper. **The top-level statement of (A)**: a power rate for the
  logarithmic density, uniform in `x`.
-/

namespace GGMCollatz

namespace Family

variable (F : Family)

open Classical in
/-- Theorem 4.1 of the paper: there are `c > 0`, `C > 0` and `L₀` such that for all `L₀ ≤ L ≤ M`, the number of `n` in
the shell `[p^M, p^{M+1})` whose orbit under the reduced map stays `≥ p^L` forever is at most
`C p^M (M+1)(L+1) e^{-cL}`. -/
def seed_statement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℕ, ∀ L M : ℕ, L₀ ≤ L → L ≤ M →
    (((Finset.Ico (F.p ^ M) (F.p ^ (M + 1))).filter
        (fun n => ∀ k, F.p ^ L ≤ F.Ct^[k] n)).card : ℝ)
      ≤ C * (F.p : ℝ) ^ M * ((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(c * L))

open Classical in
/-- The form of GGM's Proposition 3.5: there is `c > 0` such that for all `α, β ∈ (1, 1 + c)` there is a
constant `K` with the following property for every `x ≥ 2`. Under the logarithmic distribution on the window
`[x^β, x^{αβ}]`, the probability that the orbit never reaches a value `≤ x` is at most `K x^{-c}`, and the total
variation between the laws of the first passage location for this window and for the adjacent window
`[x^{αβ}, x^{α²β}]` is at most `K (log x)^{-c}`. -/
def prop35_statement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ α β : ℝ, 1 < α → α < 1 + c → 1 < β → β < 1 + c →
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x →
      expect (F.logUnif (x ^ β) (x ^ (α * β)))
          (Set.indicator {N | ¬ F.passes ⌊x⌋₊ N} 1) ≤ K * x ^ (-c) ∧
      dTV ((F.logUnif (x ^ β) (x ^ (α * β))).map (F.passLoc ⌊x⌋₊))
            ((F.logUnif (x ^ (α * β)) (x ^ (α ^ 2 * β))).map (F.passLoc ⌊x⌋₊))
        ≤ K * (Real.log x) ^ (-c)

/-- Lemma 5.3 of the paper (the one-step recursion): there are a window width `α > 1` and `c > 0`, `C_s`, `X_s` such that
`P(N₀, x^{α²}) ≤ P(N₀, x^α) + C_s (log x)^{-c}` whenever `x ≥ X_s` and `1 ≤ N₀ ≤ x`. -/
def oneStep_statement : Prop :=
  ∃ α : ℝ, 1 < α ∧ ∃ c : ℝ, 0 < c ∧ ∃ Cs Xs : ℝ, ∀ x : ℝ, Xs ≤ x → ∀ N₀ : ℕ, 1 ≤ N₀ →
    (N₀ : ℝ) ≤ x →
      F.windowProb α N₀ (x ^ (α ^ 2)) ≤ F.windowProb α N₀ (x ^ α) + Cs * (Real.log x) ^ (-c)

/-- **The top-level statement of (A)** (Theorem 5.7 (ii) of the paper): there are `K, c' > 0` such that for all
`N₀ ≥ 1` and `x ≥ 3`, `∑_{N ≤ x, C_min(N) > N₀} 1/N ≤ K N₀^{-c'} log x`. -/
def mainA_statement : Prop :=
  ∃ K c' : ℝ, 0 < K ∧ 0 < c' ∧ ∀ N₀ : ℕ, 1 ≤ N₀ → ∀ x : ℝ, 3 ≤ x →
    ∑ N ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun N => N₀ < F.Cmin N), (1 / (N : ℝ))
      ≤ K * (N₀ : ℝ) ^ (-c') * Real.log x

end Family

/-- The worked example `(p, q, r) = (3, 4, [2, 1])`. An anchor showing that the statements are not vacuous. -/
def example34 : Family where
  p := 3
  q := 4
  r := fun j => if j = 1 then 2 else 1
  two_le_p := by norm_num
  p_lt_q := by norm_num
  coprime := by norm_num
  subcritical := by
    -- 4 < 3^{3/2}: squaring both sides gives 16 < 27
    push_cast
    rw [show (3 : ℝ) / ((3 : ℝ) - 1) = 3 / 2 by norm_num]
    have hsq : ((3 : ℝ) ^ ((3 : ℝ) / 2)) ^ (2 : ℕ) = 27 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have hpos : 0 < (3 : ℝ) ^ ((3 : ℝ) / 2) := by positivity
    nlinarith [hsq, hpos]
  divisible := by
    intro j hj hjp
    interval_cases j <;> norm_num
  positive := by
    intro j hj hjp
    interval_cases j <;> norm_num
  gcd_one := by
    intro d hd hr
    have h1 := hr 2 (by norm_num) (by norm_num)
    have h1' : (d : ℤ) ∣ 1 := by simpa using h1
    exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1'

end GGMCollatz
