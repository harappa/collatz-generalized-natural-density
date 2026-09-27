import GGMCollatz.StatementB

/-!
# Matveev (2000) Corollary 2.3 and the hypothesis `MatveevHyp`

From **transcriptions** of Corollary 2.3 of the original (Izv. Math. 64:6, p. 1219, checked on an image of the
primary source) in our case (`n = 2`, `K = ℚ`, `D = 1`, `κ = 1`, `A₁ = ln p`, `A₂ = ln q`), namely `Cor23B13`
(with `B` as in (1.3) of the original) and `Cor23Bstar` (with `B*` as in (1.4)), we show that the frozen hypothesis
`MatveevHyp` follows for `p, q ≥ 2`. The constant of the original is
`C₁(2) = min{e·30⁵·2^{3.5}, 2^{32}} ≈ 7.473·10⁸ ≤ 10⁹`.
**`MatveevHyp` is applied only to the `p, q` of a family (`≥ 2`)**: if `p` or `q` is 0 or 1, the statement is false
because `Real.log 1 = 0` (`not_hyp_1_2`). This is not because the original is false, but because our formulation
drops the lower bound 0.16 on `A_j`.
(Proofs taken from an independent review of the statements.)
-/

namespace GGMCollatz

namespace Matveev

open Real


/-- Degenerate case: for `p = 1` (`Real.log 1 = 0`) the statement is false. -/
theorem not_hyp_1_2 : ¬ GGMCollatz.MatveevHyp 1 2 := by
  intro h
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h' := h 0 1 (by simp only [Int.cast_zero, zero_mul, Int.cast_one, one_mul, zero_add, Nat.cast_ofNat]; exact hl2.ne')
  simp at h'
  rw [abs_of_pos hl2] at h'
  have := Real.log_two_lt_d9
  linarith

/-- The constant of the original, `C₁(2, κ = 1) = min{(1/κ)(e n/2)^κ 30^{n+3} n^{3.5}, 2^{6n+20}}`. -/
noncomputable def C1 : ℝ :=
  min ((1 / 1) * ((1 / 2) * Real.exp 1 * 2) ^ (1 : ℕ) * 30 ^ (2 + 3) * (2 : ℝ) ^ (3.5 : ℝ))
      (2 ^ (6 * 2 + 20))

lemma C1_le : C1 ≤ 10 ^ 9 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hsq : ((2 : ℝ) ^ (3.5 : ℝ)) ^ (2 : ℕ) = 128 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hpos : 0 < (2 : ℝ) ^ (3.5 : ℝ) := by positivity
  have h12 : (2 : ℝ) ^ (3.5 : ℝ) ≤ 12 := by nlinarith
  unfold C1
  refine le_trans (min_le_left _ _) ?_
  have hep : 0 < Real.exp 1 := Real.exp_pos 1
  norm_num
  nlinarith

lemma C1_nonneg : 0 ≤ C1 := by unfold C1; positivity

/-- Corollary 2.3 of the original (n = 2, K = ℚ, D = 1, κ = 1, A₁ = ln p, A₂ = ln q), in the form with `B*`. -/
def Cor23Bstar (p q : ℕ) : Prop :=
  ∀ b₁ b₂ : ℤ, (b₁ : ℝ) * Real.log p + (b₂ : ℝ) * Real.log q ≠ 0 →
    Real.log |(b₁ : ℝ) * Real.log p + (b₂ : ℝ) * Real.log q| >
      -C1 * (1 : ℝ) ^ 2 * (Real.log p * Real.log q) * Real.log (Real.exp 1 * 1) *
        Real.log (Real.exp 1 * ((max |b₁| |b₂| : ℤ) : ℝ))

/-- Corollary 2.3 of the original, in the form with `B` from (1.3) (`B = max{1, max_j |b_j| A_j / A_n}`, `n = 2`). -/
def Cor23B13 (p q : ℕ) : Prop :=
  ∀ b₁ b₂ : ℤ, (b₁ : ℝ) * Real.log p + (b₂ : ℝ) * Real.log q ≠ 0 →
    Real.log |(b₁ : ℝ) * Real.log p + (b₂ : ℝ) * Real.log q| >
      -C1 * (1 : ℝ) ^ 2 * (Real.log p * Real.log q) * Real.log (Real.exp 1 * 1) *
        Real.log (Real.exp 1 * max 1 (max (|(b₁ : ℝ)| * Real.log p / Real.log q)
                                             (|(b₂ : ℝ)| * Real.log q / Real.log q)))

lemma M_ge_one (p q : ℕ) (b₁ b₂ : ℤ)
    (hΛ : (b₁ : ℝ) * Real.log p + (b₂ : ℝ) * Real.log q ≠ 0) :
    (1 : ℝ) ≤ ((max |b₁| |b₂| : ℤ) : ℝ) := by
  have : b₁ ≠ 0 ∨ b₂ ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hΛ; simp [hc.1, hc.2]
  have h1 : (1 : ℤ) ≤ max |b₁| |b₂| := by
    rcases this with h | h
    · exact le_trans (Int.one_le_abs h) (le_max_left _ _)
    · exact le_trans (Int.one_le_abs h) (le_max_right _ _)
  exact_mod_cast h1

/-- The essential line: from `log |Λ| > -C₁ Ω ln(e B*)` to the Lean statement. -/
lemma hyp_of_bound (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (b₁ b₂ : ℤ)
    (hΛ : (b₁ : ℝ) * Real.log p + (b₂ : ℝ) * Real.log q ≠ 0)
    (hb : Real.log |(b₁ : ℝ) * Real.log p + (b₂ : ℝ) * Real.log q| >
      -C1 * (Real.log p * Real.log q) * (1 + Real.log ((max |b₁| |b₂| : ℤ) : ℝ))) :
    Real.exp (-(10 ^ 9 : ℝ) * Real.log p * Real.log q *
        (1 + Real.log ((max |b₁| |b₂| : ℤ) : ℝ)))
      ≤ |(b₁ : ℝ) * Real.log p + (b₂ : ℝ) * Real.log q| := by
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have hM := M_ge_one p q b₁ b₂ hΛ
  have hlM : 0 ≤ Real.log ((max |b₁| |b₂| : ℤ) : ℝ) := Real.log_nonneg hM
  have hΩ : 0 ≤ Real.log p * Real.log q * (1 + Real.log ((max |b₁| |b₂| : ℤ) : ℝ)) := by
    positivity
  have hapos : 0 < |(b₁ : ℝ) * Real.log p + (b₂ : ℝ) * Real.log q| := abs_pos.mpr hΛ
  rw [← Real.exp_log hapos]
  apply Real.exp_le_exp.mpr
  have hC := C1_le
  nlinarith

theorem hyp_of_Bstar (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (h : Cor23Bstar p q) :
    GGMCollatz.MatveevHyp p q := by
  intro b₁ b₂ hΛ
  apply hyp_of_bound p q hp hq b₁ b₂ hΛ
  have h0 := h b₁ b₂ hΛ
  have hM := M_ge_one p q b₁ b₂ hΛ
  have hMpos : (0 : ℝ) < ((max |b₁| |b₂| : ℤ) : ℝ) := by linarith
  rw [Real.log_mul (Real.exp_pos 1).ne' hMpos.ne', Real.log_exp] at h0
  simpa using h0

/-- Also from the form with `B` from (1.3) (`B ≤ B*` when ordered as `p ≤ q`; otherwise swap the indices). -/
theorem hyp_of_B13 (h : ∀ p q : ℕ, 2 ≤ p → 2 ≤ q → Cor23B13 p q)
    (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) : GGMCollatz.MatveevHyp p q := by
  -- Lemma: choose the order and convert Cor23B13 to the form with B*
  have key : ∀ p q : ℕ, 2 ≤ p → 2 ≤ q → p ≤ q → Cor23Bstar p q := by
    intro p q hp hq hpq b₁ b₂ hΛ
    have h0 := h p q hp hq b₁ b₂ hΛ
    have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
    have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
    have hA : Real.log p ≤ Real.log q :=
      Real.log_le_log (by positivity) (by exact_mod_cast hpq)
    have hM := M_ge_one p q b₁ b₂ hΛ
    set M : ℝ := ((max |b₁| |b₂| : ℤ) : ℝ) with hMdef
    have hMr : M = max |(b₁ : ℝ)| |(b₂ : ℝ)| := by simp [hMdef]
    have hB1 : |(b₁ : ℝ)| * Real.log p / Real.log q ≤ M := by
      rw [div_le_iff₀ hlq, hMr]
      have : |(b₁ : ℝ)| ≤ max |(b₁ : ℝ)| |(b₂ : ℝ)| := le_max_left _ _
      have h0' : 0 ≤ |(b₁ : ℝ)| := abs_nonneg _
      nlinarith
    have hB2 : |(b₂ : ℝ)| * Real.log q / Real.log q ≤ M := by
      rw [mul_div_assoc, div_self hlq.ne', mul_one, hMr]; exact le_max_right _ _
    have hBle : max 1 (max (|(b₁ : ℝ)| * Real.log p / Real.log q)
        (|(b₂ : ℝ)| * Real.log q / Real.log q)) ≤ M :=
      max_le hM (max_le hB1 hB2)
    have hBpos : 0 < max 1 (max (|(b₁ : ℝ)| * Real.log p / Real.log q)
        (|(b₂ : ℝ)| * Real.log q / Real.log q)) :=
      lt_of_lt_of_le one_pos (le_max_left _ _)
    have hlog : Real.log (Real.exp 1 * max 1 (max (|(b₁ : ℝ)| * Real.log p / Real.log q)
        (|(b₂ : ℝ)| * Real.log q / Real.log q))) ≤ Real.log (Real.exp 1 * M) :=
      Real.log_le_log (by positivity) (by nlinarith [Real.exp_pos 1])
    have hΩ : 0 ≤ C1 * (1 : ℝ) ^ 2 * (Real.log p * Real.log q) * Real.log (Real.exp 1 * 1) := by
      rw [mul_one, Real.log_exp]; have := C1_nonneg; positivity
    show _ > _
    calc -C1 * (1 : ℝ) ^ 2 * (Real.log p * Real.log q) * Real.log (Real.exp 1 * 1) *
            Real.log (Real.exp 1 * M)
        ≤ -C1 * (1 : ℝ) ^ 2 * (Real.log p * Real.log q) * Real.log (Real.exp 1 * 1) *
            Real.log (Real.exp 1 * max 1 (max (|(b₁ : ℝ)| * Real.log p / Real.log q)
              (|(b₂ : ℝ)| * Real.log q / Real.log q))) := by nlinarith
      _ < _ := h0
  rcases le_total p q with hpq | hqp
  · exact hyp_of_Bstar p q hp hq (key p q hp hq hpq)
  · -- Swap the indices: Λ(p, q; b₁, b₂) = Λ(q, p; b₂, b₁)
    have hs := hyp_of_Bstar q p hq hp (key q p hq hp hqp)
    intro b₁ b₂ hΛ
    have hΛ' : (b₂ : ℝ) * Real.log q + (b₁ : ℝ) * Real.log p ≠ 0 := by
      rwa [add_comm]
    have := hs b₂ b₁ hΛ'
    rw [add_comm ((b₂ : ℝ) * Real.log q), max_comm |b₂| |b₁|] at this
    have heq : -(10 ^ 9 : ℝ) * Real.log q * Real.log p * (1 + Real.log ((max |b₁| |b₂| : ℤ) : ℝ))
        = -(10 ^ 9 : ℝ) * Real.log p * Real.log q * (1 + Real.log ((max |b₁| |b₂| : ℤ) : ℝ)) := by ring
    rw [heq] at this
    exact this

#print axioms not_hyp_1_2

end Matveev

end GGMCollatz
