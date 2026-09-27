import GGMCollatz.Inter

/-!
# The first-passage construction of GGM §4: parameters and sets (counterpart of tao-collatz's Sec5)

Derived from the constructions (`nZero`, `mZero`, `goodTuple`, `Iy`, `Eprime`, `mainZ`, `cn`) of
`TaoCollatz/Sec5/FirstPassage.lean`, `TaoCollatz/Sec5/ApproxFormula.lean` and
`TaoCollatz/Sec5/Stabilization.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2;
generalized to the GGM family (p, q, r).
Steps 1-3 of GGM (arXiv:2111.06170) §4 "Proof that Proposition 4.1 ⇒ Proposition 3.5".

This is written in a form that repairs the gaps in the presentation of the GGM original (G1-G7 in the
accompanying paper):

* The interval `I_y` is the **trimmed** interval of Tao (5.9) ((G1); with the extended interval the rows
  are incomplete).
* `E'` includes the range condition `M ∈ [Mlo, Mhi]` of Tao (5.10) ((G4)).
* The width of `A^{(k)}` is `log^{0.6} x` ((G6); `ε = 0.1` in GGM's `log^{0.5+ε}`).
* The fine scale is GGM's `m₀` itself (profile `Ψ = q^{m₀} Σ_{M∈E'} ω_{m₀}(M)/M`, GGM's `Q'`).
* For the upper bound on `C_k` ((G3)), the crude upper bound `q^k/Mlo + 2 log^{0.7} x` from
  `E' ⊂ [Mlo, Mhi]` suffices (Proposition 4.1 applies for arbitrary `A`, so the loss of a power of the
  logarithm is absorbed). The `O(1)` for the profile `Ψ` comes from the normalization obtained by
  applying the approximation formula to `E = ℕ` (the "normalization check" in the accompanying paper).
* The order of `𝒮_n` and `F_n` ((G7)): by `syracZ_eq_rev_fint`, `𝒮_n` is the pushforward of the forward
  `fint`, so the good-tuple condition applies directly to the forward sequence of valuations.

Parameters (`x` a large real, `L = log x`):

* `μ = p/(p-1)`, `d = μ log p - log q > 0` (condition (b)), `θ₀ = 1 + d/(20 log q)` (upper limit of the
  window exponent).
* `n₀ = ⌊L/(5 log q)⌋` (`q^{n₀} ≤ x^{1/5}`), `m₀ = ⌊(β-1)L/(4d)⌋` (`β` is the exponent of the first
  window).
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- `μ = p/(p-1)` (the mean of `G(μ)`). -/
noncomputable def mu : ℝ := (F.p : ℝ) / ((F.p : ℝ) - 1)

/-- The logarithmic contraction per step `d = μ log p - log q` (positive by condition (b)). -/
noncomputable def drift : ℝ := F.mu * Real.log F.p - Real.log F.q

/-- Upper limit of the window exponent `θ₀ = 1 + d/(20 log q)`. -/
noncomputable def thetaMax : ℝ := 1 + F.drift / (20 * Real.log F.q)

/-- `n₀ = ⌊log x/(5 log q)⌋` (counterpart of GGM's `n₀`; `q^{n₀} ≤ x^{1/5}`). -/
noncomputable def nZero (x : ℝ) : ℕ := ⌊Real.log x / (5 * Real.log F.q)⌋₊

/-- `m₀ = ⌊(β-1) log x/(4d)⌋` (counterpart of GGM `eq: definition of m_0`; adapted to the exponent `β`
of the first window so that `I_y ⊂ [2m₀, n₀]`). -/
noncomputable def mZero (β x : ℝ) : ℕ := ⌊(β - 1) * Real.log x / (4 * F.drift)⌋₊

/-- Good tuples `A^{(k)}`: every prefix sum is within less than `log^{0.6} x` of the mean `μ j`
(GGM `a-mu n<log 0.6 x`). -/
def goodVec (x : ℝ) {k : ℕ} (a : Fin k → ℕ) : Prop :=
  ∀ j, j ≤ k → |(pre a j : ℝ) - F.mu * j| < Real.log x ^ (0.6 : ℝ)

/-- Lower end of the range of `E'`: `e^{d m₀} x e^{-log^{0.7} x}` (Tao (5.10)). -/
noncomputable def Mlo (β x : ℝ) : ℝ :=
  Real.exp (F.drift * F.mZero β x + Real.log x - Real.log x ^ (0.7 : ℝ))

/-- Upper end of the range of `E'`: `e^{d m₀} x e^{log^{0.7} x}`. -/
noncomputable def Mhi (β x : ℝ) : ℝ :=
  Real.exp (F.drift * F.mZero β x + Real.log x + Real.log x ^ (0.7 : ℝ))

open Classical in
/-- `E'(E) = {M ∈ ℕ_p ∩ [Mlo, Mhi] | T_x(M) = m₀, Pass_x(M) ∈ E}` (GGM's `E'` with the range condition
added). -/
noncomputable def Eprime (β x : ℝ) (E : Set ℕ) : Finset ℕ :=
  (Finset.range (⌊F.Mhi β x⌋₊ + 1)).filter fun M =>
    M % F.p ≠ 0 ∧ F.Mlo β x ≤ (M : ℝ) ∧ F.passes ⌊x⌋₊ M ∧
      F.passTime ⌊x⌋₊ M = F.mZero β x ∧ F.passLoc ⌊x⌋₊ M ∈ E

open Classical in
/-- The trimmed interval `I_y = [log(y/x)/d + log^{0.8} x, log(y^α/x)/d - log^{0.8} x] ∩ [0, n₀]`
(Tao (5.9)). -/
noncomputable def Iy (x y α : ℝ) : Finset ℕ :=
  (Finset.range (F.nZero x + 1)).filter fun n =>
    Real.log (y / x) / F.drift + Real.log x ^ (0.8 : ℝ) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ Real.log (y ^ α / x) / F.drift - Real.log x ^ (0.8 : ℝ)

/-- Logarithmic mass of the window `Z = Σ_{N ∈ ℕ_p ∩ [lo, hi]} 1/N`. -/
noncomputable def windowMass (lo hi : ℝ) : ℝ := ∑ N ∈ F.logWindow lo hi, (N : ℝ)⁻¹

/-- `C^E_k(Y) = q^k Σ_{M ∈ E'(E), M ≡ Y (q^k)} 1/M` (`C_n` of GGM Step 2). -/
noncomputable def cE (β x : ℝ) (E : Set ℕ) (k : ℕ) (Y : ZMod (F.q ^ k)) : ℝ :=
  (F.q : ℝ) ^ k *
    ∑ M ∈ (F.Eprime β x E).filter (fun M : ℕ => ((M : ℕ) : ZMod (F.q ^ k)) = Y), (M : ℝ)⁻¹

/-- The profile `Ψ(E) = q^{m₀} Σ_{M ∈ E'(E)} P(𝒮_{m₀} = M mod q^{m₀}) / M` (GGM's `Q'`, the `Z` of
Tao (5.21)). Independent of the window `y`. -/
noncomputable def psi (β x : ℝ) (E : Set ℕ) : ℝ :=
  (F.q : ℝ) ^ F.mZero β x * ∑ M ∈ F.Eprime β x E,
    ((F.syracZ (F.mZero β x)) (M : ZMod (F.q ^ F.mZero β x))).toReal * (M : ℝ)⁻¹

/-- The term of row `n`: `P(a^{(n-m₀)}(N) ∈ A^{(n-m₀)}, S^{n-m₀}(N) ∈ E'(E))` (each row of GGM's
`eq: formula for pass depending on Aff_a,r`, each term of Tao's `steppedMid`). -/
noncomputable def rowTerm (β x : ℝ) (E : Set ℕ) (y α : ℝ) (n : ℕ) : ℝ :=
  expect (F.logUnif y (y ^ α))
    (Set.indicator {N | F.goodVec x (F.valVec N (n - F.mZero β x)) ∧
      F.S^[n - F.mZero β x] N ∈ F.Eprime β x E} 1)

/-- The forward offset `F_n(a, R) mod q^n = fint(a, r ∘ j) · p^{-|a|}` (`v i = (a_i, j_i)`).
By `syracZ_eq_rev_fint`, `𝒮_n` is its pushforward. -/
noncomputable def offsetFwd {n : ℕ} (v : Fin n → ℕ × ℕ) : ZMod (F.q ^ n) :=
  ((F.fint (fun i => (v i).1) (fun i => F.r (v i).2) : ℤ) : ZMod (F.q ^ n)) *
    ((F.p : ZMod (F.q ^ n))⁻¹) ^ pre (fun i => (v i).1) n

/-- The edge of the window `[y, y^α]`: `log N < log y + 2d log^{0.8} x` or
`log N > α log y - 2d log^{0.8} x`. -/
def edge (x y α : ℝ) (N : ℕ) : Prop :=
  Real.log N < Real.log y + 2 * F.drift * Real.log x ^ (0.8 : ℝ) ∨
    α * Real.log y - 2 * F.drift * Real.log x ^ (0.8 : ℝ) < Real.log N

/-! ### Basic properties of the constants -/

theorem p_real_two_le : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p

theorem one_lt_p_real : (1 : ℝ) < F.p := by have := F.p_real_two_le; linarith

theorem p_real_pos : (0 : ℝ) < F.p := by have := F.p_real_two_le; linarith

theorem q_real_pos : (0 : ℝ) < F.q := by exact_mod_cast F.q_pos

theorem p_real_lt_q_real : (F.p : ℝ) < F.q := by exact_mod_cast F.p_lt_q

theorem log_p_pos : 0 < Real.log F.p := Real.log_pos F.one_lt_p_real

theorem log_q_pos : 0 < Real.log F.q :=
  Real.log_pos (lt_trans F.one_lt_p_real F.p_real_lt_q_real)

theorem log_p_lt_log_q : Real.log F.p < Real.log F.q :=
  Real.log_lt_log F.p_real_pos F.p_real_lt_q_real

theorem one_lt_mu : 1 < F.mu := by
  unfold mu
  have h := F.p_real_two_le
  rw [lt_div_iff₀ (by linarith)]; linarith

theorem mu_pos : 0 < F.mu := lt_trans one_pos F.one_lt_mu

theorem mu_le_two : F.mu ≤ 2 := by
  unfold mu
  have h := F.p_real_two_le
  rw [div_le_iff₀ (by linarith)]; linarith

/-- `d > 0` (condition (b): `q < p^{p/(p-1)}`). -/
theorem drift_pos : 0 < F.drift := by
  unfold drift
  have h := F.subcritical
  have hlog : Real.log F.q < Real.log ((F.p : ℝ) ^ ((F.p : ℝ) / ((F.p : ℝ) - 1))) :=
    Real.log_lt_log F.q_real_pos h
  rw [Real.log_rpow F.p_real_pos] at hlog
  unfold mu
  linarith

theorem one_lt_thetaMax : 1 < F.thetaMax := by
  unfold thetaMax
  have := F.drift_pos
  have := F.log_q_pos
  have : 0 < F.drift / (20 * Real.log F.q) := by positivity
  linarith

/-- `d < μ log p`. -/
theorem drift_lt : F.drift < F.mu * Real.log F.p := by
  unfold drift; linarith [F.log_q_pos]

end Family

end GGMCollatz
