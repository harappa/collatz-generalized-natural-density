import GGMCollatz.NatDen.Statements

/-!
# (M) The irrationality measure of `λ = log_p q` from Matveev's lower bound for two logarithms (a one-line argument)

From `MatveevHyp p q` (`StatementB.lean`, the hypothesis of the natural-density theorem) to `irr_statement`: `|hλ - m| ≥ c h^{-(μ-1)}`,
`μ = 1 + K`, `K = 10⁹ log p log q`, `c = min(1/2, e^{-K(1 + log(λ+1))}/log p)`.

Argument: if `|hλ - m| ≥ 1/2` it is trivial. Otherwise `|m| ≤ (λ+1)h`, and `Λ := h log q - m log p = log p · (hλ - m)`
is not `0` (`q^h = p^m` cannot happen since `gcd(p, q) = 1` and `p, q ≥ 2`), so `MatveevHyp` with
`b₁ = -m`, `b₂ = h` gives `log p · |hλ - m| ≥ exp(-K(1 + log max(|m|, h))) ≥ e^{-K(1 + log(λ+1))} h^{-K}`.
-/

namespace GGMCollatz

namespace ND

namespace IrrAux

variable (F : Family)

/-- `p^m ≠ q^h` (`h ≥ 1`): the real equality `h log q = m log p` does not hold. -/
theorem log_ne_of_coprime {h : ℕ} (hh : 1 ≤ h) (m : ℤ) :
    (h : ℝ) * Real.log F.q ≠ (m : ℝ) * Real.log F.p := by
  intro heq
  have hp : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hq : (2 : ℝ) ≤ F.q := by exact_mod_cast F.two_le_q
  have hp0 : (0 : ℝ) < F.p := by linarith
  have hq0 : (0 : ℝ) < F.q := by linarith
  rcases le_or_gt m 0 with hm | hm
  · -- `m ≤ 0`: `m log p ≤ 0 < h log q`
    have h1 : 0 < (h : ℝ) * Real.log F.q := by
      have : (1 : ℝ) ≤ h := by exact_mod_cast hh
      have hlq : 0 < Real.log F.q := Real.log_pos (by linarith)
      positivity
    have h2 : (m : ℝ) * Real.log F.p ≤ 0 := by
      have hlp : 0 < Real.log F.p := Real.log_pos (by linarith)
      have : (m : ℝ) ≤ 0 := by exact_mod_cast hm
      nlinarith
    linarith
  · -- `m ≥ 1`: `q^h = p^m` in the natural numbers
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = (k : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg hm.le).symm⟩
    have hk : 1 ≤ k := by exact_mod_cast hm
    have e1 : Real.log ((F.q : ℝ) ^ h) = Real.log ((F.p : ℝ) ^ k) := by
      rw [Real.log_pow, Real.log_pow]; push_cast at heq ⊢; linarith
    have e2 : ((F.q : ℝ) ^ h) = ((F.p : ℝ) ^ k) :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) e1
    have e3 : F.q ^ h = F.p ^ k := by exact_mod_cast e2
    have hcop : Nat.Coprime (F.p ^ k) (F.q ^ h) := Nat.Coprime.pow k h F.coprime
    rw [← e3] at hcop
    have h1 : F.q ^ h = 1 := (Nat.coprime_self _).mp hcop
    have h2 : 2 ≤ F.q ^ h := by
      calc 2 ≤ F.q := F.two_le_q
        _ = F.q ^ 1 := (pow_one _).symm
        _ ≤ F.q ^ h := Nat.pow_le_pow_right (by have := F.two_le_q; omega) hh
    omega

end IrrAux

variable (F : Family)

/-- **(M) ⇒ (IRR)**. -/
theorem irr_of_matveev (hM : MatveevHyp F.p F.q) : irr_statement F := by
  have hp : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hq : (2 : ℝ) ≤ F.q := by exact_mod_cast F.two_le_q
  have hlp : 0 < Real.log F.p := Real.log_pos (by linarith)
  have hlq : 0 < Real.log F.q := Real.log_pos (by linarith)
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlp2 : Real.log 2 ≤ Real.log F.p := Real.log_le_log (by norm_num) hp
  have hlq2 : Real.log 2 ≤ Real.log F.q := Real.log_le_log (by norm_num) hq
  set K : ℝ := (10 : ℝ) ^ 9 * Real.log F.p * Real.log F.q with hKdef
  have hK1 : 1 ≤ K := by
    have h1 : (1 / 4 : ℝ) ≤ Real.log F.p * Real.log F.q := by nlinarith
    rw [hKdef, mul_assoc]; nlinarith
  have hK0 : 0 ≤ K := by linarith
  set lam' : ℝ := lam F with hlamdef
  have hlam : 0 < lam' := div_pos hlq hlp
  set c₀ : ℝ := Real.exp (-K * (1 + Real.log (lam' + 1))) / Real.log F.p with hc₀
  have hc₀pos : 0 < c₀ := div_pos (Real.exp_pos _) hlp
  refine ⟨min (1 / 2) c₀, 1 + K, lt_min (by norm_num) hc₀pos, by linarith, ?_⟩
  intro h hh m
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := by linarith
  have hexpo : -(1 + K - 1) = -K := by ring
  rw [hexpo]
  have hpow_le : (h : ℝ) ^ (-K) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hhR (by linarith)
  have hpow0 : 0 ≤ (h : ℝ) ^ (-K) := Real.rpow_nonneg hh0.le _
  by_cases hbig : (1 / 2 : ℝ) ≤ |(h : ℝ) * lam' - m|
  · calc min (1 / 2) c₀ * (h : ℝ) ^ (-K) ≤ 1 / 2 * 1 :=
          mul_le_mul (min_le_left _ _) hpow_le hpow0 (by norm_num)
      _ ≤ _ := by linarith
  · push Not at hbig
    -- `Λ = h log q - m log p = log p · (hλ - m)`
    have hΛ : ((-m : ℤ) : ℝ) * Real.log F.p + ((h : ℤ) : ℝ) * Real.log F.q
        = Real.log F.p * ((h : ℝ) * lam' - m) := by
      rw [hlamdef]; unfold lam; push_cast; field_simp; ring
    have hne : ((-m : ℤ) : ℝ) * Real.log F.p + ((h : ℤ) : ℝ) * Real.log F.q ≠ 0 := by
      rw [hΛ]
      intro h0
      rcases mul_eq_zero.mp h0 with h1 | h1
      · linarith
      · apply IrrAux.log_ne_of_coprime F hh m
        have : (h : ℝ) * lam' = m := by linarith
        rw [hlamdef] at this; unfold lam at this
        field_simp at this
        linarith
    have hmat := hM (-m) (h : ℤ) hne
    rw [hΛ, abs_mul, abs_of_pos hlp] at hmat
    -- `max(|m|, h) ≤ (λ+1) h`
    have hm_le : |(m : ℝ)| ≤ (lam' + 1) * h := by
      have h1 : |(m : ℝ)| ≤ |(h : ℝ) * lam'| + |(h : ℝ) * lam' - m| := by
        have := abs_sub_abs_le_abs_sub ((h : ℝ) * lam') ((h : ℝ) * lam' - m)
        have e : (h : ℝ) * lam' - ((h : ℝ) * lam' - m) = m := by ring
        rw [e] at this
        linarith [abs_sub_abs_le_abs_sub ((m : ℝ)) ((h : ℝ) * lam'),
          abs_sub_comm ((m : ℝ)) ((h : ℝ) * lam')]
      rw [abs_of_pos (by positivity : (0 : ℝ) < (h : ℝ) * lam')] at h1
      nlinarith
    set B : ℤ := max |(-m)| |(h : ℤ)| with hBdef
    have hB1 : (h : ℝ) ≤ (B : ℝ) := by
      have : |(h : ℤ)| ≤ B := le_max_right _ _
      have h2 : ((|(h : ℤ)| : ℤ) : ℝ) = (h : ℝ) := by
        rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ h)]; push_cast; ring
      have h3 : ((|(h : ℤ)| : ℤ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast this
      linarith
    have hBle : (B : ℝ) ≤ (lam' + 1) * h := by
      rw [hBdef]
      push_cast
      rw [abs_neg]
      apply max_le hm_le
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ h)]
      nlinarith
    have hBpos : (0 : ℝ) < (B : ℝ) := lt_of_lt_of_le hh0 hB1
    have hlogB : Real.log (B : ℝ) ≤ Real.log (lam' + 1) + Real.log h := by
      rw [← Real.log_mul (by positivity) hh0.ne']
      exact Real.log_le_log hBpos hBle
    -- rewriting the lower bound
    have hexp : Real.exp (-K * (1 + Real.log (lam' + 1))) * (h : ℝ) ^ (-K)
        ≤ Real.exp (-(10 ^ 9 : ℝ) * Real.log F.p * Real.log F.q * (1 + Real.log (B : ℝ))) := by
      rw [Real.rpow_def_of_pos hh0, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : -(10 ^ 9 : ℝ) * Real.log F.p * Real.log F.q = -K := by rw [hKdef]; ring
      rw [this]
      nlinarith
    have hfin : c₀ * (h : ℝ) ^ (-K) ≤ |(h : ℝ) * lam' - m| := by
      rw [hc₀, div_mul_eq_mul_div, div_le_iff₀ hlp]
      linarith
    calc min (1 / 2) c₀ * (h : ℝ) ^ (-K) ≤ c₀ * (h : ℝ) ^ (-K) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hpow0
      _ ≤ _ := hfin

end ND

end GGMCollatz
