/- Portions Copyright (c) 2026 Idris Ali Shaik (FirstPassageLinearTransport, Apache License 2.0).
   Modified: generalized to the maps of Goncalves, Greenfeld and Madrid. See NOTICE. -/
import GGMCollatz.Statement
import GGMCollatz.Seed.Chain

/-!
# The seed theorem (Theorem 4.1 of the accompanying paper)

`GGMCollatz.Family.seed : F.seed_statement`. The ingredients are the four files in `GGMCollatz/Seed/`
(derived from Idris Ali Shaik's `FirstPassageLinearTransport` (Apache-2.0), rewritten and generalized to
the GGM family):

* `Seed/Step.lean`: one step of the reduced map, the increase in a multiplication step, injectivity of
  the letters, the average over a shell.
* `Seed/Potential.lean`: the average of the θ-th power, and the density `≤ K p^m ξ^m` of the bad set `bad m`.
* `Seed/Fiber.lean`: the number of elements of a fibre at a fixed time (backward sandwiching).
* `Seed/Chain.lean`: the chain (first bad point) and the counting bound `≤ K(1+4R)/(1-ξ) (M+1)^6 p^M ξ^L`.

Here we take the rate `c := min(-log ξ / 7, log p / 4)`. If `M + 1 ≥ e^{cL}` we use the trivial upper bound
`#I_M = (p-1)p^M`; if `M + 1 < e^{cL}` we absorb the polynomial factor `(M+1)^5` of the counting bound
into `e^{5cL}`, obtaining the form `C p^M (M+1)(L+1) e^{-cL}`. The constants `C`, `L₀ = 2R + 1` depend on
`ξ`, `K` from `bad_density` (ineffective). The only hypotheses are (a)(b)(c), `p < q`, `qj + r(j) ≥ 1`;
the sign of `r(j)` and (d) are not used.
-/

namespace GGMCollatz

namespace Family

open Finset

open Classical in
/-- **The seed theorem (Theorem 4.1 of the paper).** -/
theorem seed (F : Family) : F.seed_statement := by
  obtain ⟨ξ, hξ0, hξ1, K, hK, hbad⟩ := F.bad_density
  have hp2 : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hp : (0 : ℝ) < F.p := by linarith
  have hlogp : 0 < Real.log F.p := Real.log_pos (by linarith)
  have hlogξ : Real.log ξ < 0 := Real.log_neg hξ0 hξ1
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (-Real.log ξ / 7) (Real.log F.p / 4) := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hcdef]; apply lt_min
    · have : 0 < -Real.log ξ := by linarith
      positivity
    · positivity
  have hc7 : 7 * c ≤ -Real.log ξ := by
    have := min_le_left (-Real.log ξ / 7) (Real.log F.p / 4)
    rw [← hcdef] at this; linarith
  have hc4 : 4 * c ≤ Real.log F.p := by
    have := min_le_right (-Real.log ξ / 7) (Real.log F.p / 4)
    rw [← hcdef] at this; linarith
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = K * (1 + 4 * (F.Rb : ℝ)) / (1 - ξ) := ⟨_, rfl⟩
  have hA : 0 ≤ A := by
    rw [hAdef]; apply div_nonneg _ (by linarith); positivity
  unfold seed_statement
  refine ⟨c, hc0, (F.p : ℝ) - 1 + A, by linarith, 2 * F.Rb + 1, ?_⟩
  intro L M hL hLM
  have hpM : (0 : ℝ) ≤ (F.p : ℝ) ^ M := by positivity
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have hM0 : (0 : ℝ) ≤ M := by positivity
  -- The trivial upper bound `#I_M = (p-1) p^M`
  have htriv : (((Ico (F.p ^ M) (F.p ^ (M + 1))).filter
      (fun n => ∀ k, F.p ^ L ≤ F.Ct^[k] n)).card : ℝ) ≤ ((F.p : ℝ) - 1) * (F.p : ℝ) ^ M := by
    have h1 := card_filter_le (Ico (F.p ^ M) (F.p ^ (M + 1))) (fun n => ∀ k, F.p ^ L ≤ F.Ct^[k] n)
    rw [Nat.card_Ico] at h1
    have h2 : F.p ^ M ≤ F.p ^ (M + 1) := Nat.pow_le_pow_right F.p_pos (by omega)
    have h3 : (((F.p ^ (M + 1) - F.p ^ M : ℕ)) : ℝ) = ((F.p : ℝ) - 1) * (F.p : ℝ) ^ M := by
      rw [Nat.cast_sub h2]; push_cast; ring
    rw [← h3]; exact_mod_cast h1
  have hexp : Real.exp (-(c * L)) = (Real.exp (c * L))⁻¹ := Real.exp_neg _
  have hexpos : 0 < Real.exp (c * L) := Real.exp_pos _
  by_cases hcase : Real.exp (c * L) ≤ (M : ℝ) + 1
  · -- The trivial case
    have hX : 1 ≤ ((M : ℝ) + 1) * Real.exp (-(c * L)) := by
      rw [hexp, ← div_eq_mul_inv, one_le_div hexpos]; exact hcase
    have hY : 1 ≤ (L : ℝ) + 1 := by linarith
    have hB : 0 ≤ ((F.p : ℝ) - 1 + A) * (F.p : ℝ) ^ M := mul_nonneg (by linarith) hpM
    calc _ ≤ ((F.p : ℝ) - 1) * (F.p : ℝ) ^ M := htriv
      _ ≤ ((F.p : ℝ) - 1 + A) * (F.p : ℝ) ^ M := mul_le_mul_of_nonneg_right (by linarith) hpM
      _ ≤ ((F.p : ℝ) - 1 + A) * (F.p : ℝ) ^ M * (((M : ℝ) + 1) * Real.exp (-(c * L))) :=
          le_mul_of_one_le_right hB hX
      _ ≤ ((F.p : ℝ) - 1 + A) * (F.p : ℝ) ^ M * (((M : ℝ) + 1) * Real.exp (-(c * L)))
            * ((L : ℝ) + 1) := le_mul_of_one_le_right (by positivity) hY
      _ = _ := by ring
  · -- The main case: `M + 1 < e^{cL}`
    rw [not_le] at hcase
    -- `R ≤ p^L`, `R^2 ≤ p^L` (`L ≥ 2R + 1`)
    have hRL : F.Rb ≤ L := by omega
    have h2RL : 2 * F.Rb ≤ L := by omega
    have h2p : 2 ^ L ≤ F.p ^ L := Nat.pow_le_pow_left F.two_le_p L
    have hL3n : F.Rb ≤ F.p ^ L := by
      have := (Nat.lt_two_pow_self (n := F.Rb)).le
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hRL
      omega
    have hR2n : F.Rb ^ 2 ≤ F.p ^ L := by
      have h1 : F.Rb ^ 2 ≤ (2 ^ F.Rb) ^ 2 :=
        Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := F.Rb)).le 2
      have h2 : (2 ^ F.Rb) ^ 2 = 2 ^ (2 * F.Rb) := by rw [← pow_mul, mul_comm]
      have h3 := Nat.pow_le_pow_right (by norm_num : 0 < 2) h2RL
      omega
    have hL3 : (F.Rb : ℝ) ≤ (F.p : ℝ) ^ L := by exact_mod_cast hL3n
    have hR2 : (F.Rb : ℝ) ^ 2 ≤ (F.p : ℝ) ^ L := by exact_mod_cast hR2n
    -- `M^4 ≤ p^L`
    have hpL : Real.exp (L * Real.log F.p) = (F.p : ℝ) ^ L := by
      rw [Real.exp_nat_mul, Real.exp_log hp]
    have hM4 : (M : ℝ) ^ 4 ≤ (F.p : ℝ) ^ L := by
      have h1 : (M : ℝ) ^ 4 ≤ Real.exp (c * L) ^ 4 :=
        pow_le_pow_left₀ hM0 (by linarith) 4
      have h2 : Real.exp (c * L) ^ 4 = Real.exp ((4 : ℕ) * (c * L)) := (Real.exp_nat_mul _ 4).symm
      have h3 : Real.exp ((4 : ℕ) * (c * L)) ≤ Real.exp (L * Real.log F.p) := by
        apply Real.exp_le_exp.2
        push_cast
        have := mul_le_mul_of_nonneg_right hc4 hL0
        linarith
      rw [← hpL]; linarith
    have hMR : (M : ℝ) ^ 2 * F.Rb ≤ (F.p : ℝ) ^ L := by
      nlinarith [sq_nonneg ((M : ℝ) ^ 2 - F.Rb)]
    have hL2 : 4 * (M : ℝ) ^ 2 * F.Rb ≤ (F.p : ℝ) ^ (L + 2) := by
      have : (4 : ℝ) ≤ (F.p : ℝ) ^ 2 := by nlinarith
      rw [pow_add]
      have hpL0 : (0 : ℝ) ≤ (F.p : ℝ) ^ L := by positivity
      nlinarith
    have hcount := F.count_le hξ0 hξ1 hK hbad hL3 hL2
      (L := L) (M := M)
    rw [← hAdef] at hcount
    -- `(M+1)^6 ξ^L ≤ (M+1)(L+1) e^{-cL}`
    have hξL : ξ ^ L ≤ Real.exp (-(7 * c) * L) := by
      have e1 : ξ ^ L = Real.exp (L * Real.log ξ) := by
        rw [Real.exp_nat_mul, Real.exp_log hξ0]
      rw [e1]
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left hc7 hL0
      nlinarith
    have hM5 : ((M : ℝ) + 1) ^ 5 ≤ Real.exp (5 * (c * L)) := by
      have h1 : ((M : ℝ) + 1) ^ 5 ≤ Real.exp (c * L) ^ 5 :=
        pow_le_pow_left₀ (by positivity) hcase.le 5
      have h2 : Real.exp (c * L) ^ 5 = Real.exp ((5 : ℕ) * (c * L)) := (Real.exp_nat_mul _ 5).symm
      rw [h2] at h1; push_cast at h1; exact h1
    have hpoly : ((M : ℝ) + 1) ^ 6 * ξ ^ L ≤ ((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(c * L)) := by
      have hM1 : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
      calc ((M : ℝ) + 1) ^ 6 * ξ ^ L = ((M : ℝ) + 1) * (((M : ℝ) + 1) ^ 5 * ξ ^ L) := by ring
        _ ≤ ((M : ℝ) + 1) * (Real.exp (5 * (c * L)) * Real.exp (-(7 * c) * L)) := by
            apply mul_le_mul_of_nonneg_left _ hM1
            exact mul_le_mul hM5 hξL (by positivity) (by positivity)
        _ = ((M : ℝ) + 1) * Real.exp (-(c * L) - c * L) := by
            rw [← Real.exp_add]; ring_nf
        _ ≤ ((M : ℝ) + 1) * Real.exp (-(c * L)) := by
            apply mul_le_mul_of_nonneg_left _ hM1
            apply Real.exp_le_exp.2
            have := mul_nonneg hc0.le hL0
            linarith
        _ ≤ ((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(c * L)) := by
            have : 0 ≤ ((M : ℝ) + 1) * Real.exp (-(c * L)) := by positivity
            nlinarith
    calc _ ≤ A * ((M : ℝ) + 1) ^ 6 * (F.p : ℝ) ^ M * ξ ^ L := hcount
      _ = A * (F.p : ℝ) ^ M * (((M : ℝ) + 1) ^ 6 * ξ ^ L) := by ring
      _ ≤ A * (F.p : ℝ) ^ M * (((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(c * L))) :=
          mul_le_mul_of_nonneg_left hpoly (mul_nonneg hA hpM)
      _ ≤ ((F.p : ℝ) - 1 + A) * (F.p : ℝ) ^ M * (((M : ℝ) + 1) * ((L : ℝ) + 1)
            * Real.exp (-(c * L))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (by linarith) hpM
      _ = _ := by ring

end Family

end GGMCollatz
