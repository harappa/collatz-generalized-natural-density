import GGMCollatz.Statement
import GGMCollatz.Tao.Syracuse.SyracRV

/-!
# The statements of GGM's Propositions 3.1, 4.1 and 5.1 (frozen)

The intermediate surface used to prove GGM's Proposition 3.5 (`prop35_statement`) in Lean from scratch. These
generalize to the GGM family the tao-collatz statements of Tao's Propositions 1.9, 1.14 and 1.17
(`valuation_dist`, `fine_scale_mixing`, `charFn_decay`). The chain is `prop51 ⇒ prop41` (GGM §5, Sec6 of
tao-collatz), `prop33 ∧ prop41 ⇒ prop35` (GGM §4, Sec5), and `⇒ prop51` (GGM §6, §7, Sec7).
**Any change here is recorded in the project's decision log.**

* `prop33_statement`: the distribution of valuations (GGM Proposition 3.1). If the distribution modulo `p^{n'}`
  of a random number not divisible by `p` is close to uniform and `n' ≥ (μ + c₀)n`, then the valuation vector
  `a^{(n)}` is exponentially close to `G(μ)^n`.
* `prop41_statement`: fine-scale mixing (GGM Proposition 4.1). `Osc_{m,n}(𝒮_n) ≤ C m^{-A}` (for every `A`).
* `prop51_statement`: decay of the characteristic function (GGM Proposition 5.1).
  `|E e(-ξ𝒮_n/q^n)| ≤ C n^{-A}` for `q ∤ ξ` (for every `A`).
-/

namespace GGMCollatz

/-- `e(t) = exp(2πit)`. -/
noncomputable def eC (t : ℚ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))

namespace Family

variable (F : Family)

instance instNeZeroQPow (n : ℕ) : NeZero (F.q ^ n) := F.neZero_q_pow n

instance instNeZeroPPow (n : ℕ) : NeZero (F.p ^ n) :=
  ⟨pow_ne_zero _ (by have := F.two_le_p; omega)⟩

/-- The oscillation `Osc_{m,n}(c)`: the `ℓ¹` norm of the deviation of a function `c` on `ℤ/q^n` from its
averages over the residue classes mod `q^m` (GGM Proposition 4.1). -/
noncomputable def osc (m n : ℕ) (hmn : m ≤ n) (c : ZMod (F.q ^ n) → ℝ) : ℝ :=
  ∑ Y : ZMod (F.q ^ n),
    |c Y - (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
      ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (F.q ^ n) =>
        ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y'
          = ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y), c Y'|

open Classical in
/-- The uniform distribution on the residues mod `p^{n'}` not divisible by `p` (`pure 0` if there are none). -/
noncomputable def unifNpMod (n' : ℕ) : PMF (ZMod (F.p ^ n')) :=
  if h : (Finset.univ.filter fun z : ZMod (F.p ^ n') => z.val % F.p ≠ 0).Nonempty then
    PMF.uniformOfFinset _ h
  else PMF.pure 0

/-- **GGM Proposition 3.1** (distribution of valuations). -/
def prop33_statement : Prop :=
  ∀ c₀ K : ℝ, 0 < c₀ → 0 < K → ∃ c₁ C : ℝ, 0 < c₁ ∧ 0 < C ∧ ∀ (n n' : ℕ) (X : PMF ℕ),
    ((F.p : ℝ) / ((F.p : ℝ) - 1) + c₀) * n ≤ (n' : ℝ) →
    (∀ N ∈ X.support, N % F.p ≠ 0) →
    PMF.dTV (X.map fun N => (N : ZMod (F.p ^ n'))) (F.unifNpMod n') ≤ K * (F.p : ℝ) ^ (-(n' : ℝ)) →
    PMF.dTV (X.map fun N => F.valVec N n) (PMF.iid (geomP F.p) n) ≤ C * (F.p : ℝ) ^ (-c₁ * (n : ℝ))

/-- **GGM Proposition 4.1** (fine-scale mixing). -/
def prop41_statement : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ n m : ℕ, ∀ hmn : m ≤ n, 1 ≤ m →
    F.osc m n hmn (fun Y => ((F.syracZ n) Y).toReal) ≤ C * (m : ℝ) ^ (-A)

/-- **GGM Proposition 5.1** (decay of the characteristic function). -/
def prop51_statement : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ ξ : ZMod (F.q ^ n), ¬ (F.q ∣ ξ.val) →
    ‖(F.syracZ n).cexpect fun Y => eC (-(ξ.val * Y.val : ℚ) / (F.q : ℚ) ^ n)‖ ≤ C * (n : ℝ) ^ (-A)

end Family

end GGMCollatz
