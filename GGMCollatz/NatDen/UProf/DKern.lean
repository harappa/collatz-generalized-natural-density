import GGMCollatz.NatDen.UProf.Statements
import GGMCollatz.NatDen.UProf.DKern.Params

/-!
# (DK) The kernel estimate (Lemma 7.21 of the paper)

`D(M) = Σ_n Σ_{s ∈ Σ(n,M)} p^{s - kλ} P(s_k = s)`. (a) hockey stick
`Σ_{j ≥ 0} p^{-j} P(s_k = s - j) = (s/k) P(s_k = s)`, (b) the inner sum of each row, (c) Chernoff outside the central window
`J_* = {|k - k_*| ≤ √k_* log log x}` (`k_* = log(Y/M)/d`), (d) the Gauss envelope ((LCLT)),
(e) weighted equidistribution of the Kronecker orbit `{kλ + u}` ((KRON-W), `f(θ) = p^{-θ}`, `∫ f = 1/(μ log p)`).

The pieces are in `NatDen/UProf/DKern/` (auxiliary lemmas in the namespace `GGMCollatz.ND.DKernAux`):

* `Hockey.lean`: `Hs_eq_mul_nb` for (a) (`Σ_{s ≤ S} p^{-(S-s)} P(s_k = s) = (S/k) P(s_k = S)`),
  `row_bound` for (b) (row sum `= (Y/M) Phi(k) + O(y/M)`; the truncation at the lower end uses `p^s/q^k ≤ y/M` for each term and `Σ_s P ≤ 1`).
* `Gauss.lean`: the Riemann sum of the Gaussian `gau_sum` ((E3)) and the variation of the truncated weight `wt_var` ((E2)).
* `Env.lean`: the comparison `env_rel` of `Hs` with the Gaussian via (LCLT) ((E1)), and the tail `Hs_tail`.
* `Kron.lean`: `kron_apply`, applying (KRON-W) to `f(θ) = p^{-θ}` (`∫₀¹ p^{-θ} = (1 - 1/p)/log p`).
* `Asym.lean`: the central window `[⌊c - t^{11}⌋, ⌈c + t^{11}⌉)` at `t = L^{1/20}` and the size of the Gaussian constants.
* `PiecesA.lean`, `PiecesB.lean`, `PiecesC.lean`: `W_piece` (Gaussian mass), `T_piece` (tail outside the window),
  `E_piece` (comparison with the envelope), `K_piece` (Kronecker).
* `Core.lean`: `Σ_k Phi(k) = 1/((μ-λ) log p) + O(L^{-1/(10μ_irr)})` (`mainSum`, in a family-independent form).
* `Params.lean`: the parameters of the family `F` (`α₀ = 1 + d/(30 log q)`, `m₀`, `n₀`, `M ∈ [Mlo, Mhi]`)
  satisfy the hypotheses of `mainSum`.

Differences from the accompanying paper: the radius `√k_* log log x` of the central window is replaced by `L^{11/20}`
(so that all errors are powers of `L`). The rate is `c = 1/(10μ_irr)` (smaller than the paper's `c_D < 1/(2(μ_irr+1))`,
but the statement only needs some positive `c`). The Gauss envelope is not the paper's `w̃(k)` (with prefactor and
denominator `k`) but the true Gaussian with `k` replaced by `k_*`; the cost of this replacement is put into the relative
error of (E1). The hypothesis (IRR) acts only through (KRON-W), so `dkern` does not take it as an argument.
-/

namespace GGMCollatz

namespace ND

variable (F : Family)

namespace DKernAux

/-- Shift of the row index: if `m ≤ A` and `m ≤ B`, then `Σ_{n ∈ [A, B]} f(n - m) = Σ_{k ∈ [A-m, B-m]} f(k)`. -/
theorem sum_Icc_sub (f : ℕ → ℝ) {m A B : ℕ} (hmA : m ≤ A) (hmB : m ≤ B) :
    ∑ n ∈ Finset.Icc A B, f (n - m) = ∑ k ∈ Finset.Icc (A - m) (B - m), f k := by
  apply Finset.sum_nbij' (fun n => n - m) (fun k => k + m)
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    omega
  · intro k _
    simp
  · intro n _
    rfl

end DKernAux

/-- **(DK)**. (IRR) acts only through (KRON-W) `hkw`, so it is not taken as an argument (removed after
a referee pointed out that it was unused). -/
theorem dkern {μ : ℝ} (hμ : 2 ≤ μ)
    (hkw : kronW_statement (lam F) μ) (hL : lclt_statement F.p) : dkern_statement F := by
  classical
  have hp := F.two_le_p
  have hq1 : 1 ≤ F.q := by have := F.p_lt_q; omega
  have hd := F.drift_pos
  have hlq := F.log_q_pos
  have hlp := F.log_p_pos
  have hα₀ : 1 < 1 + F.drift / (30 * Real.log F.q) := by
    have : 0 < F.drift / (30 * Real.log F.q) := by positivity
    linarith
  refine ⟨1 + F.drift / (30 * Real.log F.q), hα₀, fun α hα hαα₀ => ?_⟩
  obtain ⟨K, hK, hmain⟩ := DKernAux.mainSum hp (DKernAux.lam_pos F) (DKernAux.lam_lt_mu F) hμ hkw
    hL (c₁ := (α - 1) / F.drift) (div_pos (by linarith) hd)
  have hc0 : 0 < 1 / (10 * μ) := by positivity
  have hc1 : 1 / (10 * μ) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  refine ⟨1 / (10 * μ), K + 1, hc0, by linarith, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually hmain, DKernAux.params F hα hαα₀,
    Family.eventually_log_ge 1] with x hx hpar hL1
  intro M hM1 hM2
  obtain ⟨hy0, hyY, hm1, h2m, hK2, hsmall, hMp⟩ := hpar
  obtain ⟨hu, hcc, hk1, hk2⟩ := hMp M hM1 hM2
  have hMpos : 0 < M := lt_of_lt_of_le (Real.exp_pos _) hM1
  set L := Real.log x with hLdef
  set y := x ^ α with hydef
  set Y := (x ^ α) ^ α with hYdef
  set m₀ := F.mZero α x with hm₀
  set n₀ := F.nZero x with hn₀
  set u := Real.log (Y / M) / Real.log F.p with hudef
  have hY0 : 0 < Y := lt_of_lt_of_le hy0 hyY
  -- row sums
  set rowI : ℕ → ℝ := fun k => ∑' s : ℕ, if inWin F y Y k s M then
      (F.p : ℝ) ^ s / (F.q : ℝ) ^ k * nb F.p k s else 0 with hrowI
  have hkern : kern F α x M = ∑ k ∈ Finset.Icc m₀ (n₀ - m₀), rowI k := by
    have h := DKernAux.sum_Icc_sub rowI (m := m₀) (A := 2 * m₀) (B := n₀) (by omega) (by omega)
    rw [show 2 * m₀ - m₀ = m₀ by omega] at h
    unfold kern rows
    exact h
  have hrow : ∀ k ∈ Finset.Icc m₀ (n₀ - m₀),
      |rowI k - Y / M * DKernAux.Phi F.p (lam F) u k| ≤ y / M := by
    intro k _
    have hpos : 0 ≤ (k : ℝ) * (Real.log F.q / Real.log F.p) + Real.log (Y / M) / Real.log F.p := by
      have := DKernAux.lam_pos F
      unfold lam at this
      positivity
    have := DKernAux.row_bound hp hq1 hMpos hy0 hyY hpos
    convert this using 5 <;> first | rfl | exact if_congr Iff.rfl rfl rfl
  have hsum := hx u m₀ (n₀ - m₀) hu hm1 hcc hK2 hk1 hk2
  -- assembly
  have hdl := DKernAux.dl_mul_log F
  have hYd : Y / (F.drift * M) = Y / M * (1 / ((muP F.p - lam F) * Real.log F.p)) := by
    rw [hdl]; field_simp
  have hcard : ((Finset.Icc m₀ (n₀ - m₀)).card : ℝ) ≤ ((n₀ - m₀ : ℕ) : ℝ) + 1 := by
    rw [Nat.card_Icc]
    have : n₀ - m₀ + 1 - m₀ ≤ n₀ - m₀ + 1 := Nat.sub_le _ _
    exact_mod_cast this
  have hLc : L ^ (-(1 : ℝ)) ≤ L ^ (-(1 / (10 * μ))) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hYM : 0 < Y / M := div_pos hY0 hMpos
  have hsplit : kern F α x M - Y / (F.drift * M)
      = ∑ k ∈ Finset.Icc m₀ (n₀ - m₀), (rowI k - Y / M * DKernAux.Phi F.p (lam F) u k)
        + Y / M * (∑ k ∈ Finset.Icc m₀ (n₀ - m₀), DKernAux.Phi F.p (lam F) u k
          - 1 / ((muP F.p - lam F) * Real.log F.p)) := by
    rw [hkern, hYd, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have h1 : |∑ k ∈ Finset.Icc m₀ (n₀ - m₀), (rowI k - Y / M * DKernAux.Phi F.p (lam F) u k)|
      ≤ Y / M * L ^ (-(1 / (10 * μ))) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum hrow) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hyM : y / M = Y / M * (y / Y) := by field_simp
    calc ((Finset.Icc m₀ (n₀ - m₀)).card : ℝ) * (y / M)
        ≤ (((n₀ - m₀ : ℕ) : ℝ) + 1) * (y / M) :=
          mul_le_mul_of_nonneg_right hcard (div_nonneg hy0.le hMpos.le)
      _ = Y / M * ((((n₀ - m₀ : ℕ) : ℝ) + 1) * (y / Y)) := by rw [hyM]; ring
      _ ≤ Y / M * L ^ (-(1 : ℝ)) := mul_le_mul_of_nonneg_left hsmall hYM.le
      _ ≤ Y / M * L ^ (-(1 / (10 * μ))) := mul_le_mul_of_nonneg_left hLc hYM.le
  have h2 : |Y / M * (∑ k ∈ Finset.Icc m₀ (n₀ - m₀), DKernAux.Phi F.p (lam F) u k
      - 1 / ((muP F.p - lam F) * Real.log F.p))| ≤ Y / M * (K * L ^ (-(1 / (10 * μ)))) := by
    rw [abs_mul, abs_of_pos hYM]
    exact mul_le_mul_of_nonneg_left hsum hYM.le
  rw [hsplit]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ Y / M * L ^ (-(1 / (10 * μ))) + Y / M * (K * L ^ (-(1 / (10 * μ)))) := add_le_add h1 h2
    _ = (K + 1) * (Y / M) * L ^ (-(1 / (10 * μ))) := by ring

end ND

end GGMCollatz
