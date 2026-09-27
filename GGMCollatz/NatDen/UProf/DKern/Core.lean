import GGMCollatz.NatDen.UProf.DKern.PiecesC

/-!
# The main body of (DK): `Σ_k p^{-θ(k)} Hs(k, ⌊kλ+u⌋) = 1/((μ-λ) log p) + O(L^{-1/(10μ_irr)})`

A form independent of the family `F` (only `p`, `λ` and the hypotheses (KRON-W), (LCLT)). `L` is a large real
(`log x` on the using side), `c = u/(μ-λ)` is the expected passage time `k_*`, and the row range `[k₁, k₂]` contains
the central window `[c - L^{11/20}, c + L^{11/20}]`.

Proof (steps (c)(d)(e) of the kernel estimate): outside the window `J = [⌊c - R⌋, ⌈c + R⌉)` (`R = L^{11/20}`),
`Hs_tail` gives size `e^{-cL^{1/10}}`; inside, `env_rel` replaces `Hs` by the Gaussian `g` (relative error `O(L^{-7/20})`);
(KRON-W) (`ℓ = ⌊L^{1/10}⌋`, `kron_apply`, `wt_var`) handles `Σ_J p^{-θ} g`, and `gau_sum` handles `Σ_J g`.
Instead of the paper's radius `√k_* log log x` we use `L^{11/20}` (so that all errors are powers of `L`).
-/

namespace GGMCollatz

namespace ND

namespace DKernAux

/-- **The main body of (DK)**. -/
theorem mainSum {p : ℕ} (hp : 2 ≤ p) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < muP p) {μi : ℝ}
    (hμi : 2 ≤ μi) (hkw : kronW_statement lam μi) (hL : lclt_statement p) {c₁ : ℝ} (hc₁ : 0 < c₁) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ L : ℝ in Filter.atTop, ∀ (u : ℝ) (k₁ k₂ : ℕ), 0 < u → 1 ≤ k₁ →
      c₁ * L ≤ u / (muP p - lam) → (k₂ : ℝ) ≤ L →
      (k₁ : ℝ) ≤ u / (muP p - lam) - L ^ (11 / 20 : ℝ) →
      u / (muP p - lam) + L ^ (11 / 20 : ℝ) ≤ k₂ →
      |∑ k ∈ Finset.Icc k₁ k₂, Phi p lam u k - 1 / ((muP p - lam) * Real.log p)|
        ≤ K * L ^ (-(1 / (10 * μi))) := by
  obtain ⟨KW, hKW, hW⟩ := W_piece hp hlam hc₁
  obtain ⟨KE, hKE, hE⟩ := E_piece hp hlam0 hlam hL hc₁
  obtain ⟨KK, hKK, hK⟩ := K_piece hp hlam0 hlam hμi hkw hc₁
  have hT := T_piece hp hlam0 hlam hc₁
  have hμ := muP_pos hp
  have hdl : 0 < muP p - lam := by linarith
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have hμlp : 0 < muP p * Real.log p := by positivity
  set WM := muP p / (muP p - lam) + KW with hWM
  have hWM0 : 0 < WM := by positivity
  refine ⟨2 + KE * WM + KK + KW / (muP p * Real.log p), by positivity, ?_⟩
  have htend : Filter.Tendsto (fun L : ℝ => L ^ (1 / 20 : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hev := hW.and (hE.and (hK.and (hT.and (Filter.eventually_ge_atTop (1 : ℝ)))))
  filter_upwards [htend.eventually hev, Filter.eventually_ge_atTop 0] with L hLt hL0
  obtain ⟨hWt, hEt, hKt, hTt, ht1⟩ := hLt
  intro u k₁ k₂ hu hk₁ hc1 hk₂ hk1 hk2
  rw [rpow_rate hL0]
  rw [rpow1120 hL0] at hk1 hk2
  rw [← rpow20 hL0] at hc1 hk₂
  set t := L ^ (1 / 20 : ℝ) with ht
  have ht0 : 0 < t := by linarith
  set c := u / (muP p - lam) with hc
  have hk₁r : (1 : ℝ) ≤ k₁ := by exact_mod_cast hk₁
  have hwin : 0 ≤ c - t ^ 11 := by linarith
  have ht11 : 0 ≤ t ^ 11 := by positivity
  have hc0 : 0 < c := by linarith
  have hc2 : c ≤ t ^ 20 := by linarith
  have hu' : u = (muP p - lam) * c := by rw [hc]; field_simp
  -- the window lies in the row range
  have hJsub : Finset.Ico (ja c t) (jb c t) ⊆ Finset.Icc k₁ k₂ := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_Icc]
    have h1 : k₁ ≤ ja c t := Nat.le_floor hk1
    have h2 : jb c t ≤ k₂ := Nat.ceil_le.mpr hk2
    omega
  rw [← Finset.sum_sdiff hJsub]
  -- outside the window
  set T := ∑ k ∈ Finset.Icc k₁ k₂ \ Finset.Ico (ja c t) (jb c t), Phi p lam u k with hTdef
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun k _ => Phi_nonneg _ _ _ _
  have hT1 : T ≤ 2 * (1 / t ^ 2) := by
    have hpt : ∀ k ∈ Finset.Icc k₁ k₂ \ Finset.Ico (ja c t) (jb c t),
        Phi p lam u k ≤ 1 / t ^ 22 := by
      intro k hk
      rw [Finset.mem_sdiff, Finset.mem_Icc] at hk
      have hkk : (k : ℝ) ≤ t ^ 20 := le_trans (by exact_mod_cast hk.1.2) hk₂
      exact hTt u c rfl hc1 hc2 k (le_trans hk₁ hk.1.1) hk.2 hkk
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.Icc k₁ k₂ \ Finset.Ico (ja c t) (jb c t)).card : ℝ) ≤ t ^ 20 + 1 := by
      have h1 : (Finset.Icc k₁ k₂ \ Finset.Ico (ja c t) (jb c t)).card ≤ (Finset.Icc k₁ k₂).card :=
        Finset.card_le_card Finset.sdiff_subset
      have h2 : (Finset.Icc k₁ k₂).card ≤ k₂ + 1 := by rw [Nat.card_Icc]; omega
      have h3 : ((Finset.Icc k₁ k₂ \ Finset.Ico (ja c t) (jb c t)).card : ℝ) ≤ (k₂ : ℝ) + 1 := by
        exact_mod_cast le_trans h1 h2
      linarith
    have ht20 : 1 ≤ t ^ 20 := one_le_pow₀ ht1
    calc ((Finset.Icc k₁ k₂ \ Finset.Ico (ja c t) (jb c t)).card : ℝ) * (1 / t ^ 22)
        ≤ (t ^ 20 + 1) * (1 / t ^ 22) := by gcongr
      _ ≤ (2 * t ^ 20) * (1 / t ^ 22) := by gcongr; linarith
      _ = 2 * (1 / t ^ 2) := by field_simp
  -- inside the window: comparison with the envelope
  set SJ := ∑ k ∈ Finset.Ico (ja c t) (jb c t), Phi p lam u k with hSJ
  set SG := ∑ k ∈ Finset.Ico (ja c t) (jb c t),
    Real.exp (-(th lam u k) * Real.log p) * gg p lam c k with hSG
  have hEnv : |SJ - SG| ≤ KE / t ^ 7 * Wt p lam c t := by
    rw [hSJ, hSG, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    unfold Wt
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hpos : 0 ≤ (k : ℝ) * lam + u := by rw [hu']; positivity
    have hθ0 := th_nonneg hpos
    have he1 : Real.exp (-(th lam u k) * Real.log p) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have he0 : 0 ≤ Real.exp (-(th lam u k) * Real.log p) := (Real.exp_pos _).le
    unfold Phi
    rw [← mul_sub, abs_mul, abs_of_nonneg he0]
    have hb := hEt u c rfl hc1 hc2 k hk
    calc Real.exp (-(th lam u k) * Real.log p) * |Hs p k (fl lam u k) - gg p lam c k|
        ≤ 1 * |Hs p k (fl lam u k) - gg p lam c k| :=
          mul_le_mul_of_nonneg_right he1 (abs_nonneg _)
      _ ≤ KE / t ^ 7 * gg p lam c k := by rw [one_mul]; exact hb
  have hKr := hKt u c rfl hc1 hc2
  have hWr := hWt c hc1 hc2
  have hWle : Wt p lam c t ≤ WM := by
    have : KW / t ^ 8 ≤ KW := div_le_self hKW.le (one_le_pow₀ ht1)
    rw [hWM]; linarith [(abs_le.mp hWr).2]
  have hW0 : 0 ≤ Wt p lam c t := by
    unfold Wt; exact Finset.sum_nonneg fun k _ => gau_nonneg (gA_pos hp hc0).le _ _ _
  -- comparison of the rates
  have hμi0 : 0 < μi := by linarith
  have h2μ : 2 / μi ≤ 1 := by rw [div_le_one hμi0]; exact hμi
  have hr2 : 1 / t ^ 2 ≤ t ^ (-(2 / μi)) := inv_pow_le_rate ht1 2 (by push_cast; linarith)
  have hr7 : 1 / t ^ 7 ≤ t ^ (-(2 / μi)) := inv_pow_le_rate ht1 7 (by push_cast; linarith)
  have hr8 : 1 / t ^ 8 ≤ t ^ (-(2 / μi)) := inv_pow_le_rate ht1 8 (by push_cast; linarith)
  have hrate0 : 0 ≤ t ^ (-(2 / μi)) := Real.rpow_nonneg ht0.le _
  -- assembly
  have hsplit : T + SJ - 1 / ((muP p - lam) * Real.log p)
      = T + (SJ - SG) + (SG - Wt p lam c t / (muP p * Real.log p))
        + (Wt p lam c t - muP p / (muP p - lam)) / (muP p * Real.log p) := by
    field_simp
    ring
  rw [hsplit]
  have hA1 : |T| ≤ 2 * t ^ (-(2 / μi)) := by
    rw [abs_of_nonneg hT0]; linarith
  have hA2 : |SJ - SG| ≤ KE * WM * t ^ (-(2 / μi)) := by
    refine le_trans hEnv ?_
    calc KE / t ^ 7 * Wt p lam c t = KE * Wt p lam c t * (1 / t ^ 7) := by ring
      _ ≤ KE * WM * t ^ (-(2 / μi)) := by gcongr
  have hA4 : |(Wt p lam c t - muP p / (muP p - lam)) / (muP p * Real.log p)|
      ≤ KW / (muP p * Real.log p) * t ^ (-(2 / μi)) := by
    rw [abs_div, abs_of_pos hμlp, div_le_iff₀ hμlp]
    calc |Wt p lam c t - muP p / (muP p - lam)| ≤ KW / t ^ 8 := hWr
      _ = KW * (1 / t ^ 8) := by ring
      _ ≤ KW * t ^ (-(2 / μi)) := by gcongr
      _ = KW / (muP p * Real.log p) * t ^ (-(2 / μi)) * (muP p * Real.log p) := by
          field_simp
  calc |T + (SJ - SG) + (SG - Wt p lam c t / (muP p * Real.log p))
        + (Wt p lam c t - muP p / (muP p - lam)) / (muP p * Real.log p)|
      ≤ |T| + |SJ - SG| + |SG - Wt p lam c t / (muP p * Real.log p)|
        + |(Wt p lam c t - muP p / (muP p - lam)) / (muP p * Real.log p)| := by
        have h1 := abs_add_le (T + (SJ - SG) + (SG - Wt p lam c t / (muP p * Real.log p)))
          ((Wt p lam c t - muP p / (muP p - lam)) / (muP p * Real.log p))
        have h2 := abs_add_le (T + (SJ - SG)) (SG - Wt p lam c t / (muP p * Real.log p))
        have h3 := abs_add_le T (SJ - SG)
        linarith
    _ ≤ 2 * t ^ (-(2 / μi)) + KE * WM * t ^ (-(2 / μi)) + KK * t ^ (-(2 / μi))
        + KW / (muP p * Real.log p) * t ^ (-(2 / μi)) := by
        linarith
    _ = (2 + KE * WM + KK + KW / (muP p * Real.log p)) * t ^ (-(2 / μi)) := by ring

end DKernAux

end ND

end GGMCollatz
