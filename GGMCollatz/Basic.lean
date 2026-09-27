import Mathlib

/-!
# The GGM family of generalized Collatz maps (definitions)

Definition 1.2 and conditions (a)(b)(c)(d) of Gonçalves–Greenfeld–Madrid, *Generalized Collatz maps with almost
bounded orbits* (Indiana Univ. Math. J. 74 (2025), arXiv:2111.06170), together with `q > p` (for `q < p` the
orbits are trivially bounded, GGM §2.2).

* `C`: `C(N) = N/p` if `p ∣ N`, and `C(N) = qN + r(N mod p)` otherwise.
* `Cmin`: the minimum of the `C`-orbit.
* `Ct`: the reduced map, `N/p` or `(qN + r(j))/p` (the map in the seed theorem).
* `S`: the Syracuse-type map `(qN + r(j))/p^{ν_p(qN + r(j))}` (used on `p ∤ N`).
* `Smin`: the minimum of the `S`-orbit.

The definitions are placed here only; the statements are frozen in `GGMCollatz.Statement`.
-/

namespace GGMCollatz

/-- The data of a GGM family. `r j` is used only for `0 < j < p`. -/
structure Family where
  p : ℕ
  q : ℕ
  r : ℕ → ℤ
  two_le_p : 2 ≤ p
  p_lt_q : p < q
  /-- (a) `gcd(p, q) = 1`. -/
  coprime : Nat.Coprime p q
  /-- (b) `q < p^{p/(p-1)}`. -/
  subcritical : (q : ℝ) < (p : ℝ) ^ ((p : ℝ) / ((p : ℝ) - 1))
  /-- (c) `qj + r(j) ≡ 0 (mod p)`. -/
  divisible : ∀ j : ℕ, 0 < j → j < p → (p : ℤ) ∣ (q : ℤ) * j + r j
  /-- `qj + r(j) ≥ 1` from Definition 1.2 (so that `C(ℕ) ⊂ ℕ`). -/
  positive : ∀ j : ℕ, 0 < j → j < p → 1 ≤ (q : ℤ) * j + r j
  /-- (d) `gcd(q, r(1), …, r(p-1)) = 1` (the setting after the reduction of GGM §2.2). -/
  gcd_one : ∀ d : ℕ, d ∣ q → (∀ j : ℕ, 0 < j → j < p → (d : ℤ) ∣ r j) → d = 1

namespace Family

variable (F : Family)

/-- The GGM map `C`. -/
def C (N : ℕ) : ℕ :=
  if N % F.p = 0 then N / F.p else ((F.q : ℤ) * N + F.r (N % F.p)).toNat

/-- `C_min(N)`: the minimum of the `C`-orbit of `N`. -/
noncomputable def Cmin (N : ℕ) : ℕ := sInf (Set.range fun k => F.C^[k] N)

/-- The reduced map `C~` (after a multiplication step, divide by `p` exactly once). -/
def Ct (N : ℕ) : ℕ :=
  if N % F.p = 0 then N / F.p else (((F.q : ℤ) * N + F.r (N % F.p)) / F.p).toNat

/-- The Syracuse-type map `S`: remove from `qN + r(j)` the largest power of `p` dividing it. -/
def S (N : ℕ) : ℕ :=
  let v := ((F.q : ℤ) * N + F.r (N % F.p)).toNat
  v / F.p ^ padicValNat F.p v

/-- `S_min(N)`: the minimum of the `S`-orbit of `N`. -/
noncomputable def Smin (N : ℕ) : ℕ := sInf (Set.range fun k => F.S^[k] N)

/-- The `S`-orbit of `N` reaches a value `≤ x`. -/
def passes (x N : ℕ) : Prop := ∃ n, F.S^[n] N ≤ x

/-- The first passage time `T_x(N)` (0 if the orbit never reaches a value `≤ x`). -/
noncomputable def passTime (x N : ℕ) : ℕ := sInf {n | F.S^[n] N ≤ x}

open Classical in
/-- The first passage location `Pass_x(N)` (1 if the orbit never reaches a value `≤ x`, following GGM's
convention). -/
noncomputable def passLoc (x N : ℕ) : ℕ := if F.passes x N then F.S^[F.passTime x N] N else 1

/-- The window `ℕ_p ∩ [lo, hi]` (numbers not divisible by `p`; the closed interval follows the tao-collatz
convention). -/
noncomputable def logWindow (lo hi : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil hi + 1)).filter fun N => N % F.p ≠ 0 ∧ lo ≤ (N : ℝ) ∧ (N : ℝ) ≤ hi

/-- The logarithmic distribution on the window (mass `∝ 1/N`); `pure 1` if the window is empty. -/
noncomputable def logUnif (lo hi : ℝ) : PMF ℕ := by
  classical
  exact if h : (F.logWindow lo hi).Nonempty then
    PMF.ofFinset
      (fun N => if N ∈ F.logWindow lo hi then
          (N : ENNReal)⁻¹ / ∑ M ∈ F.logWindow lo hi, (M : ENNReal)⁻¹ else 0)
      (F.logWindow lo hi)
      (by
        -- The denominator `D = ∑_{M∈W} M⁻¹` is positive (the window is nonempty) and finite (`M ≠ 0` since `p ∤ M`).
        have hnetop : (∑ M ∈ F.logWindow lo hi, (M : ENNReal)⁻¹) ≠ ⊤ := by
          rw [ENNReal.sum_ne_top]
          intro M hM
          rw [ENNReal.inv_ne_top]
          simp only [logWindow, Finset.mem_filter] at hM
          have hM0 : M ≠ 0 := by
            intro h0
            exact hM.2.1 (by simp [h0])
          simpa using hM0
        have hne0 : (∑ M ∈ F.logWindow lo hi, (M : ENNReal)⁻¹) ≠ 0 := by
          obtain ⟨M₀, hM₀⟩ := h
          intro hsum0
          rw [Finset.sum_eq_zero_iff] at hsum0
          have h0 := hsum0 M₀ hM₀
          rw [ENNReal.inv_eq_zero] at h0
          exact ENNReal.natCast_ne_top M₀ h0
        rw [Finset.sum_congr rfl (fun N hN => if_pos hN)]
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, ENNReal.mul_inv_cancel hne0 hnetop])
      (by intro a ha; rw [if_neg ha])
  else PMF.pure 1

/-- The expectation of a real-valued observable (tao-collatz convention). -/
noncomputable def expect {α : Type*} (μ : PMF α) (f : α → ℝ) : ℝ := ∑' a, (μ a).toReal * f a

/-- Total variation as the full `L¹` distance `∑ |p - q|` (twice GGM's `sup_E`). -/
noncomputable def dTV {α : Type*} (μ ν : PMF α) : ℝ := ∑' a, |(μ a).toReal - (ν a).toReal|

/-- The window probability `P(N₀, y)`: the probability that `S_min > N₀` under the logarithmic distribution on
the window `[y, y^α]`. -/
noncomputable def windowProb (α : ℝ) (N₀ : ℕ) (y : ℝ) : ℝ :=
  expect (F.logUnif y (y ^ α)) (Set.indicator {N | N₀ < F.Smin N} 1)

end Family

end GGMCollatz
