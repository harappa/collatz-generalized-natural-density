import GGMCollatz.NatDen.Statements

/-!
# The lower bound on `P(s_n = s)` from the local limit theorem (fourth step of the proof of Proposition 6.7 of the paper)

From (LCLT) (`lclt_statement`): if `|s - μn| ≤ C √(n log n)` and `n` is large, then
`P(s_n = s) ≥ c₀ n^{-1/2 - C²/(2σ²)}` (`σ² = sig2 p`).

The proof is written in terms of `t = n^{1/10}` (`n = t^{10}`, `n^{3/5} = t^6`, `n^{-1/2} = t^{-5}`, `log n ≤ 10 t`):
`|s - μn|² ≤ C² n log n ≤ 10 C² t^{11} ≤ t^{12}` (`t ≥ 10 C²`), so `|s - μn| ≤ n^{3/5}` and (LCLT) applies;
the error term is `n^{-1/2} + |s - μn|³/n² ≤ (1 + 10C²)/t³`, so `nb ≥ gauss/2` for `t ≥ 2 C_L (1 + 10C²)`.
The Gaussian main term is bounded below by `exp(-(s-μn)²/(2σ²n)) ≥ n^{-C²/(2σ²)}`.
-/

namespace GGMCollatz

namespace ND

namespace SumCFAux

/-- `x^{k/10} = (x^{1/10})^k`. -/
theorem rpow_tenth (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    x ^ ((k : ℝ) / 10) = (x ^ (1 / 10 : ℝ)) ^ k := by
  rw [← Real.rpow_mul_natCast hx]
  congr 1
  ring

/-- `σ² = p/(p-1)² > 0`. -/
theorem sig2_pos {p : ℕ} (hp : 2 ≤ p) : 0 < sig2 p := by
  unfold sig2
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  positivity

/-- **Lower bound on `P(s_n = s)`** (from (LCLT)): if `|s - μn| ≤ C √(n log n)` and `n ≥ n₀`, then
`c₀ n^{-(1/2 + C²/(2σ²))} ≤ P(s_n = s)`. -/
theorem nb_lower {p : ℕ} (hp : 2 ≤ p) (hL : lclt_statement p) (C : ℝ) (hC : 0 < C) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ s : ℕ,
      |(s : ℝ) - muP p * n| ≤ C * Real.sqrt (n * Real.log n) →
      c₀ * (n : ℝ) ^ (-(1 / 2 + C ^ 2 / (2 * sig2 p))) ≤ nb p n s := by
  obtain ⟨CL, hCL, hlclt⟩ := hL
  have hσ := sig2_pos hp
  set M : ℝ := max 1 (max (10 * C ^ 2) (2 * CL * (1 + 10 * C ^ 2))) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM2 : 10 * C ^ 2 ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hM3 : 2 * CL * (1 + 10 * C ^ 2) ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hπσ : 0 < 2 * Real.pi * sig2 p := by positivity
  refine ⟨⌈M ^ 10⌉₊ + 1, by omega, (2 * Real.pi * sig2 p) ^ (-(1 / 2 : ℝ)) / 2,
    by positivity, ?_⟩
  intro n hn s hs
  have hn1 : 1 ≤ n := by omega
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnR : (0 : ℝ) < n := by linarith
  have hnM : M ^ 10 ≤ (n : ℝ) := by
    have h1 : M ^ 10 ≤ (⌈M ^ 10⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈M ^ 10⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈M ^ 10⌉₊ ≤ n)
    linarith
  -- `t = n^{1/10}`
  set t : ℝ := (n : ℝ) ^ (1 / 10 : ℝ) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hnR.le _
  have htk : ∀ k : ℕ, (n : ℝ) ^ ((k : ℝ) / 10) = t ^ k := fun k => rpow_tenth _ hnR.le k
  have htn : t ^ 10 = (n : ℝ) := by
    rw [← htk 10]
    norm_num
  have htM : M ≤ t := by
    by_contra hlt
    have : t ^ 10 < M ^ 10 := pow_lt_pow_left₀ (not_le.mp hlt) ht0 (by norm_num)
    linarith
  have ht1 : 1 ≤ t := le_trans hM1 htM
  have htpos : 0 < t := by linarith
  have hlog : Real.log n ≤ 10 * t := by
    have h := Real.log_le_rpow_div hnR.le (by norm_num : (0 : ℝ) < 1 / 10)
    rw [← ht] at h
    calc Real.log n ≤ t / (1 / 10) := h
      _ = 10 * t := by ring
  -- `d = |s - μn|`
  set d : ℝ := |(s : ℝ) - muP p * n| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hnR1
  have hX0 : 0 ≤ (n : ℝ) * Real.log n := mul_nonneg hnR.le hlog0
  have hd2 : d ^ 2 ≤ C ^ 2 * ((n : ℝ) * Real.log n) := by
    have h := pow_le_pow_left₀ hd0 hs 2
    rw [mul_pow, Real.sq_sqrt hX0] at h
    exact h
  have hd2' : d ^ 2 ≤ 10 * C ^ 2 * t ^ 11 := by
    calc d ^ 2 ≤ C ^ 2 * ((n : ℝ) * Real.log n) := hd2
      _ ≤ C ^ 2 * ((n : ℝ) * (10 * t)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog hnR.le) (sq_nonneg C)
      _ = 10 * C ^ 2 * t ^ 11 := by rw [← htn]; ring
  have hd2'' : d ^ 2 ≤ (t ^ 6) ^ 2 := by
    calc d ^ 2 ≤ 10 * C ^ 2 * t ^ 11 := hd2'
      _ ≤ t * t ^ 11 := mul_le_mul_of_nonneg_right (hM2.trans htM) (pow_nonneg ht0 11)
      _ = (t ^ 6) ^ 2 := by ring
  have hdt6 : d ≤ t ^ 6 :=
    (pow_le_pow_iff_left₀ hd0 (pow_nonneg ht0 6) (by norm_num : (2 : ℕ) ≠ 0)).mp hd2''
  have hrange : d ≤ (n : ℝ) ^ (3 / 5 : ℝ) := by
    have h6 : (n : ℝ) ^ (3 / 5 : ℝ) = t ^ 6 := by
      rw [← htk 6]
      norm_num
    rw [h6]
    exact hdt6
  have hl := hlclt n hn1 s hrange
  rw [← hd] at hl
  -- the error term
  have hnhalf : (n : ℝ) ^ (-(1 / 2 : ℝ)) = (t ^ 5)⁻¹ := by
    rw [Real.rpow_neg hnR.le, ← htk 5]
    norm_num
  have hn2 : (n : ℝ) ^ 2 = t ^ 20 := by
    rw [← htn]
    ring
  have hd3 : d ^ 3 ≤ 10 * C ^ 2 * t ^ 17 := by
    calc d ^ 3 = d * d ^ 2 := by ring
      _ ≤ t ^ 6 * (10 * C ^ 2 * t ^ 11) := mul_le_mul hdt6 hd2' (sq_nonneg d) (pow_nonneg ht0 6)
      _ = 10 * C ^ 2 * t ^ 17 := by ring
  have ht3 : 0 < t ^ 3 := by positivity
  have ht35 : t ^ 3 ≤ t ^ 5 := pow_le_pow_right₀ ht1 (by norm_num)
  have hE : (n : ℝ) ^ (-(1 / 2 : ℝ)) + d ^ 3 / (n : ℝ) ^ 2 ≤ (1 + 10 * C ^ 2) / t ^ 3 := by
    rw [hnhalf, hn2]
    have h1 : (t ^ 5)⁻¹ ≤ (t ^ 3)⁻¹ := inv_anti₀ ht3 ht35
    have h2 : d ^ 3 / t ^ 20 ≤ 10 * C ^ 2 / t ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) ht3]
      calc d ^ 3 * t ^ 3 ≤ 10 * C ^ 2 * t ^ 17 * t ^ 3 :=
            mul_le_mul_of_nonneg_right hd3 ht3.le
        _ = 10 * C ^ 2 * t ^ 20 := by ring
    calc (t ^ 5)⁻¹ + d ^ 3 / t ^ 20 ≤ (t ^ 3)⁻¹ + 10 * C ^ 2 / t ^ 3 := add_le_add h1 h2
      _ = (1 + 10 * C ^ 2) / t ^ 3 := by field_simp
  have hE' : CL * ((n : ℝ) ^ (-(1 / 2 : ℝ)) + d ^ 3 / (n : ℝ) ^ 2) ≤ 1 / 2 := by
    have h1 : (1 + 10 * C ^ 2) / t ^ 3 ≤ (1 + 10 * C ^ 2) / t := by
      apply div_le_div_of_nonneg_left (by positivity) htpos
      calc t = t ^ 1 := (pow_one t).symm
        _ ≤ t ^ 3 := pow_le_pow_right₀ ht1 (by norm_num)
    have h2 : CL * ((1 + 10 * C ^ 2) / t) ≤ 1 / 2 := by
      rw [mul_div_assoc', div_le_iff₀ htpos]
      linarith
    calc CL * ((n : ℝ) ^ (-(1 / 2 : ℝ)) + d ^ 3 / (n : ℝ) ^ 2)
        ≤ CL * ((1 + 10 * C ^ 2) / t) := mul_le_mul_of_nonneg_left (hE.trans h1) hCL.le
      _ ≤ 1 / 2 := h2
  -- the Gaussian main term
  have hg0 : 0 ≤ gauss p n s := by
    unfold gauss
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
  have hnb : gauss p n s / 2 ≤ nb p n s := by
    have hmul : CL * gauss p n s * ((n : ℝ) ^ (-(1 / 2 : ℝ)) + d ^ 3 / (n : ℝ) ^ 2)
        ≤ gauss p n s / 2 := by
      calc CL * gauss p n s * ((n : ℝ) ^ (-(1 / 2 : ℝ)) + d ^ 3 / (n : ℝ) ^ 2)
          = gauss p n s * (CL * ((n : ℝ) ^ (-(1 / 2 : ℝ)) + d ^ 3 / (n : ℝ) ^ 2)) := by ring
        _ ≤ gauss p n s * (1 / 2) := mul_le_mul_of_nonneg_left hE' hg0
        _ = gauss p n s / 2 := by ring
    have h := neg_abs_le (nb p n s - gauss p n s)
    linarith
  set β : ℝ := C ^ 2 / (2 * sig2 p) with hβ
  have hexp : (n : ℝ) ^ (-β) ≤
      Real.exp (-((s : ℝ) - muP p * n) ^ 2 / (2 * sig2 p * n)) := by
    rw [Real.rpow_def_of_pos hnR]
    apply Real.exp_le_exp.mpr
    have hsq : ((s : ℝ) - muP p * n) ^ 2 = d ^ 2 := (sq_abs _).symm
    rw [neg_div, hsq, mul_neg, neg_le_neg_iff, div_le_iff₀ (by positivity)]
    calc d ^ 2 ≤ C ^ 2 * ((n : ℝ) * Real.log n) := hd2
      _ = Real.log n * β * (2 * sig2 p * n) := by
          rw [hβ]
          field_simp
  have hgauss : (2 * Real.pi * sig2 p) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 + β))
      ≤ gauss p n s := by
    unfold gauss
    rw [Real.mul_rpow hπσ.le hnR.le, neg_add, Real.rpow_add hnR]
    set a := (2 * Real.pi * sig2 p) ^ (-(1 / 2 : ℝ)) with ha
    set b := (n : ℝ) ^ (-(1 / 2 : ℝ)) with hb
    have ha0 : 0 ≤ a := Real.rpow_nonneg hπσ.le _
    have hb0 : 0 ≤ b := Real.rpow_nonneg hnR.le _
    calc a * (b * (n : ℝ) ^ (-β))
        ≤ a * (b * Real.exp (-((s : ℝ) - muP p * n) ^ 2 / (2 * sig2 p * n))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hb0) ha0
      _ = a * b * Real.exp (-((s : ℝ) - muP p * n) ^ 2 / (2 * sig2 p * n)) := by ring
  calc (2 * Real.pi * sig2 p) ^ (-(1 / 2 : ℝ)) / 2 * (n : ℝ) ^ (-(1 / 2 + β))
      = (2 * Real.pi * sig2 p) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 + β)) / 2 := by ring
    _ ≤ gauss p n s / 2 := by linarith
    _ ≤ nb p n s := hnb

end SumCFAux

end ND

end GGMCollatz
