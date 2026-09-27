import GGMCollatz.NatDen.Statements
import GGMCollatz.Tao.Sec6.Core

/-!
# Proposition 6.12 (c) of the paper: assembling the product formula from (a) and (b)

Split `Σ_Y |P(𝒮_n = Y, s_n = s) - P(s_n = s) q^{-(n-m)} ω_m(Y mod q^m)|` by the triangle inequality into the deviation
of `Y` from the average over its class (the oscillation of (a)) and the deviation of the class sums from
`P(s_n = s) ω_m` ((b), each class counted `q^{n-m}` times). The `n` for which the hypothesis `log⁴ n ≤ m` of (b) fails
are bounded (`n < 2^{160}`, from `log n ≤ 32 n^{1/32}`), so they are absorbed by the trivial upper bound `2 P(s_n = s)`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace SumMixCAux

variable (F : Family)

/-- The sum over a finite first component is the marginal distribution of the second component. -/
theorem sum_fst_toReal {A B : Type*} [Fintype A] (μ : PMF (A × B)) (b : B) :
    ∑ a : A, (μ (a, b)).toReal = ((μ.map Prod.snd) b).toReal := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod', tsum_fintype]
  rw [ENNReal.toReal_sum (fun a _ => ?_)]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    rw [tsum_eq_single b]
    · simp
    · intro b' hb'
      rw [if_neg (fun h => hb' h.symm)]
  · exact ENNReal.ne_top_of_tsum_ne_top (by
      rw [← ENNReal.tsum_prod']
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (by
        calc ∑' x : A × B, (if b = x.2 then μ x else 0) ≤ ∑' x, μ x :=
              ENNReal.tsum_le_tsum (fun x => by split_ifs <;> simp)
          _ = 1 := PMF.tsum_coe μ)) a

/-- The sum of `jp` over `Y` is `nb` (the marginal of the second component of `jointSZ` is the sum of `G(μ)^n`). -/
theorem sum_jp (n s : ℕ) : ∑ Y : ZMod (F.q ^ n), jp F n Y s = nb F.p n s := by
  unfold jp
  rw [sum_fst_toReal]
  unfold nb jointSZ iidSum
  congr 2
  rw [PMF.map_comp, ← iid_stepLaw_map_fst, PMF.map_comp]
  rfl

theorem jp_nonneg (n : ℕ) (Y : ZMod (F.q ^ n)) (s : ℕ) : 0 ≤ jp F n Y s := ENNReal.toReal_nonneg

theorem nb_nonneg (p n s : ℕ) : 0 ≤ nb p n s := ENNReal.toReal_nonneg

/-- `ω_m` sums to 1. -/
theorem sum_syracZ (m : ℕ) : ∑ Z : ZMod (F.q ^ m), ((F.syracZ m) Z).toReal = 1 :=
  F.sum_syracZ_toReal_eq_one m

/-- If `n ≥ 2^{160}`, then `log⁴ n ≤ n^{1/4}`. -/
theorem log_pow_four_le {x : ℝ} (hx : (2 : ℝ) ^ (160 : ℕ) ≤ x) : Real.log x ^ 4 ≤ x ^ (1 / 4 : ℝ) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have h1 : Real.log x ≤ x ^ (1 / 32 : ℝ) / (1 / 32) := Real.log_le_rpow_div hx0.le (by norm_num)
  -- `32 ≤ x^{1/32}`
  have h32 : (32 : ℝ) ≤ x ^ (1 / 32 : ℝ) := by
    have e : ((2 : ℝ) ^ (160 : ℕ)) ^ (1 / 32 : ℝ) = 32 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc (32 : ℝ) = ((2 : ℝ) ^ (160 : ℕ)) ^ (1 / 32 : ℝ) := e.symm
      _ ≤ x ^ (1 / 32 : ℝ) := Real.rpow_le_rpow (by positivity) hx (by norm_num)
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (le_trans (by norm_num) hx)
  have h2 : Real.log x ≤ x ^ (1 / 16 : ℝ) := by
    have e : x ^ (1 / 16 : ℝ) = x ^ (1 / 32 : ℝ) * x ^ (1 / 32 : ℝ) := by
      rw [← Real.rpow_add hx0]; norm_num
    rw [e]
    have hpos : 0 ≤ x ^ (1 / 32 : ℝ) := Real.rpow_nonneg hx0.le _
    nlinarith
  have e4 : (x ^ (1 / 16 : ℝ)) ^ 4 = x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  rw [← e4]
  exact pow_le_pow_left₀ hlog0 h2 4

/-- **Proposition 6.12 (c) of the paper**: from (a) and (b). -/
theorem summixC_of_AB' (hA : summixA_statement F) (hB : summixB_statement F) :
    summixC_statement F := by
  classical
  intro A C hA0 hC0
  obtain ⟨KA, hKA, hAb⟩ := hA A C hA0 hC0
  obtain ⟨KB, hKB, hBb⟩ := hB C hC0
  set N₁ : ℝ := (2 : ℝ) ^ (160 : ℕ) with hN₁
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set K₀ : ℝ := 2 * Real.sqrt (N₁ / Real.log 2) with hK₀
  refine ⟨KA + KB + K₀ + 1, by positivity, ?_⟩
  intro n m hmn hn hm1 hm2 s hs
  set c : ZMod (F.q ^ n) → ℝ := fun Y => jp F n Y s with hcdef
  set π : ZMod (F.q ^ n) → ZMod (F.q ^ m) :=
    fun Y => ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y with hπ
  set nbv := nb F.p n s with hnbv
  have hnb0 : 0 ≤ nbv := nb_nonneg _ _ _
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hm0 : (1 : ℝ) ≤ m := by
    have : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow (by linarith) (by norm_num)
    linarith
  have hmpos : (0 : ℝ) < m := by linarith
  set T : ℝ := Real.sqrt (m * Real.log n / n) with hT
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hmA : 0 ≤ (m : ℝ) ^ (-A) := Real.rpow_nonneg hmpos.le _
  -- the trivial upper bound
  have htriv : ∑ Y : ZMod (F.q ^ n),
      |c Y - nbv * (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) * ((F.syracZ m) (π Y)).toReal| ≤ 2 * nbv := by
    have hq : (0 : ℝ) < F.q := by exact_mod_cast F.q_pos
    calc _ ≤ ∑ Y : ZMod (F.q ^ n),
          (c Y + nbv * (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) * ((F.syracZ m) (π Y)).toReal) := by
          refine Finset.sum_le_sum (fun Y _ => ?_)
          have h1 : 0 ≤ c Y := jp_nonneg F n Y s
          have h2 : 0 ≤ nbv * (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) * ((F.syracZ m) (π Y)).toReal := by
            positivity
          rw [abs_le]; constructor <;> linarith
      _ = nbv + nbv * (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
            ∑ Y : ZMod (F.q ^ n), ((F.syracZ m) (π Y)).toReal := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          exact sum_jp F n s
      _ = 2 * nbv := by
          rw [hπ, F.sum_comp_castHom m n hmn (fun Z => ((F.syracZ m) Z).toReal), sum_syracZ]
          have hpow : (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) * ((F.q ^ (n - m) : ℕ) : ℝ) = 1 := by
            push_cast
            rw [← zpow_natCast, ← zpow_add₀ hq.ne']
            have : ((m : ℤ) - (n : ℤ)) + ((n - m : ℕ) : ℤ) = 0 := by
              rw [Nat.cast_sub hmn]; ring
            rw [this, zpow_zero]
          calc nbv + nbv * (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) * (((F.q ^ (n - m) : ℕ) : ℝ) * 1)
              = nbv + nbv * ((F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) * ((F.q ^ (n - m) : ℕ) : ℝ)) := by
                ring
            _ = 2 * nbv := by rw [hpow]; ring
  by_cases hlog4 : Real.log n ^ 4 ≤ m
  · -- main case: split into (a) and (b) by the triangle inequality
    have hm9 : (m : ℝ) ≤ (n : ℝ) ^ (9 / 10 : ℝ) :=
      le_trans hm2 (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
    have hA' := hAb n m hmn hn hm1 s hs
    have hB' := hBb n m hmn hn hlog4 hm9 s hs
    set g : ZMod (F.q ^ m) → ℝ := fun Z =>
      |(∑ Y ∈ Finset.univ.filter (fun Y : ZMod (F.q ^ n) => π Y = Z), c Y)
        - nbv * ((F.syracZ m) Z).toReal| with hg
    have hsplit : ∀ Y : ZMod (F.q ^ n),
        |c Y - nbv * (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) * ((F.syracZ m) (π Y)).toReal|
          ≤ |c Y - (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
              ∑ Y' ∈ Finset.univ.filter (fun Y' => π Y' = π Y), c Y'|
            + (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) * g (π Y) := by
      intro Y
      have hq0 : 0 ≤ (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) := by positivity
      rw [hg]
      simp only
      rw [← abs_of_nonneg hq0, ← abs_mul, abs_of_nonneg hq0]
      calc _ = |(c Y - (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
              ∑ Y' ∈ Finset.univ.filter (fun Y' => π Y' = π Y), c Y')
            + (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
              ((∑ Y' ∈ Finset.univ.filter (fun Y' => π Y' = π Y), c Y')
                - nbv * ((F.syracZ m) (π Y)).toReal)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have hsum1 : ∑ Y : ZMod (F.q ^ n), |c Y - (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
        ∑ Y' ∈ Finset.univ.filter (fun Y' => π Y' = π Y), c Y'| = F.osc m n hmn c := rfl
    have hsum2 : ∑ Y : ZMod (F.q ^ n), (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) * g (π Y) = ∑ Z, g Z := by
      rw [← Finset.mul_sum, hπ, F.sum_comp_castHom m n hmn g]
      have hq : (0 : ℝ) < F.q := by exact_mod_cast F.q_pos
      have hpow : (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) * ((F.q ^ (n - m) : ℕ) : ℝ) = 1 := by
        push_cast
        rw [← zpow_natCast, ← zpow_add₀ hq.ne']
        have : ((m : ℤ) - (n : ℤ)) + ((n - m : ℕ) : ℤ) = 0 := by
          rw [Nat.cast_sub hmn]; ring
        rw [this, zpow_zero]
      rw [← mul_assoc, hpow, one_mul]
    have hB'' : ∑ Z, g Z ≤ KB * T * nbv := hB'
    calc _ ≤ ∑ Y : ZMod (F.q ^ n), (|c Y - (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
              ∑ Y' ∈ Finset.univ.filter (fun Y' => π Y' = π Y), c Y'|
            + (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) * g (π Y)) := Finset.sum_le_sum (fun Y _ => hsplit Y)
      _ = F.osc m n hmn c + ∑ Z, g Z := by rw [Finset.sum_add_distrib, hsum1, hsum2]
      _ ≤ KA * (m : ℝ) ^ (-A) * nbv + KB * T * nbv := add_le_add hA' hB''
      _ ≤ (KA + KB + K₀ + 1) * nbv * ((m : ℝ) ^ (-A) + T) := by
          have : 0 ≤ K₀ + 1 := by positivity
          nlinarith [mul_nonneg hmA hnb0, mul_nonneg hT0 hnb0, mul_nonneg (mul_nonneg hmA hnb0) this,
            mul_nonneg (mul_nonneg hT0 hnb0) this, mul_nonneg (mul_nonneg hT0 hnb0) hKA.le,
            mul_nonneg (mul_nonneg hmA hnb0) hKB.le]
  · -- `n < 2^{160}`: the trivial upper bound
    have hnN : (n : ℝ) < N₁ := by
      by_contra hge
      push Not at hge
      apply hlog4
      exact le_trans (log_pow_four_le hge) hm1
    have hTlow : Real.sqrt (Real.log 2 / N₁) ≤ T := by
      apply Real.sqrt_le_sqrt
      have hlog2n : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
      rw [div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith
    have hK₀T : 2 ≤ K₀ * T := by
      have hsq : Real.sqrt (N₁ / Real.log 2) * Real.sqrt (Real.log 2 / N₁) = 1 := by
        rw [← Real.sqrt_mul (by positivity)]
        rw [show N₁ / Real.log 2 * (Real.log 2 / N₁) = 1 by field_simp]
        exact Real.sqrt_one
      have h0 : 0 ≤ Real.sqrt (N₁ / Real.log 2) := Real.sqrt_nonneg _
      calc (2 : ℝ) = 2 * (Real.sqrt (N₁ / Real.log 2) * Real.sqrt (Real.log 2 / N₁)) := by
            rw [hsq]; ring
        _ ≤ 2 * (Real.sqrt (N₁ / Real.log 2) * T) := by gcongr
        _ = K₀ * T := by rw [hK₀]; ring
    calc _ ≤ 2 * nbv := htriv
      _ ≤ K₀ * T * nbv := by nlinarith
      _ ≤ (KA + KB + K₀ + 1) * nbv * ((m : ℝ) ^ (-A) + T) := by
          nlinarith [mul_nonneg hmA hnb0, mul_nonneg hT0 hnb0,
            mul_nonneg (mul_nonneg hmA hnb0) (show 0 ≤ KA + KB + K₀ + 1 by positivity),
            mul_nonneg (mul_nonneg hT0 hnb0) (show 0 ≤ KA + KB + 1 by positivity)]

end SumMixCAux

end ND

end GGMCollatz
