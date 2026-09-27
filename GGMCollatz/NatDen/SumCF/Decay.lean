import GGMCollatz.Tao.Sec7.Decay
import GGMCollatz.NatDen.SumCF.Pairing

/-!
# Decay of the pair majorant, and decay of the characteristic function multiplied by a function of the sum (second step of the proof of Proposition 6.7 of the paper)

Adapted and modified from the proof of `prop51` in `GGMCollatz/Tao/Sec7/Decay.lean`, which is derived from
`TaoCollatz/Sec7/Decay.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2.

**Changes**: the second half of the proof of `prop51` (the bound on the pair majorant `E_b ∏_j ‖f(…)‖`) is extracted
as a separate lemma `pairing_decay` (for small `n` it uses that the majorant is `≤ 1`). Combined with
`cexpect_pairing_h` (`Pairing.lean`), this gives the decay `cexpect_h_decay` of the characteristic function multiplied
by a function `h` of the valuation sum (`‖h‖ ≤ 1`).

```
‖E[χ(𝒮_n) h(s_n)]‖ ≤ E_{b ~ Pascal^{n/2}} ∏_j ‖f(…)‖          (cexpect_pairing_h)
                   ≤ C n^{-A}                                  (pairing_decay, as in prop51)
```
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace SumCFAux

variable (F : Family)

/-- **Decay of the pair majorant** (the second half of the proof of `prop51`): for `q ∤ ξ`,
`E_{b ~ Pascal^{⌊n/2⌋}} ∏_{k<n/2} ‖f(q^{2k} p^{-b_{[1,k+1]}}, b_k)‖ ≤ C n^{-A}` (for every `A`). -/
theorem pairing_decay : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    ∀ ξ : ZMod (F.q ^ n), ¬ (F.q ∣ ξ.val) →
      ((PMF.iid (pascalP F.p) (n / 2)).expect fun b =>
          ∏ j : Fin (n / 2), ‖F.fCond n ξ.val (F.xArg n (j : ℕ) (pre b ((j : ℕ) + 1))) (b j)‖)
        ≤ C * (n : ℝ) ^ (-A) := by
  classical
  intro A hA
  obtain ⟨ε₀, hε₀, hren⟩ := F.renewal_white
  obtain ⟨ε₁, hε₁, hblk⟩ := F.black_structure
  have hp : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hp0 : (0 : ℝ) < F.p := by linarith
  set ε : ℝ := min (min ε₀ ε₁) (1 / (F.p : ℝ)) with hεdef
  have hε : 0 < ε := lt_min (lt_min hε₀ hε₁) (by positivity)
  have hεε₀ : ε ≤ ε₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hεε₁ : ε ≤ ε₁ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hεp : ε ≤ 1 / (F.p : ℝ) := min_le_right _ _
  obtain ⟨C, hC, hCb⟩ := hren ε hε hεε₀ A hA
  set B : ℕ := F.edgeB with hBdef
  set N0 : ℕ := 4 * B + 4 with hN0
  refine ⟨max ((N0 : ℝ) ^ A) (C * 4 ^ A), lt_max_of_lt_right (by positivity), ?_⟩
  intro n hn ξ hξ
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hE1 : ((PMF.iid (pascalP F.p) (n / 2)).expect fun b =>
      ∏ j : Fin (n / 2), ‖F.fCond n ξ.val (F.xArg n (j : ℕ) (pre b ((j : ℕ) + 1))) (b j)‖) ≤ 1 :=
    Sec7.expect_le_one _ _
      (fun b => Finset.prod_nonneg fun j _ => norm_nonneg _)
      (fun b => Finset.prod_le_one (fun j _ => norm_nonneg _)
        (fun j _ => F.fCond_norm_le_one _ _ _ _))
  rcases lt_or_ge n N0 with hsmall | hbig
  · calc ((PMF.iid (pascalP F.p) (n / 2)).expect fun b =>
          ∏ j : Fin (n / 2), ‖F.fCond n ξ.val (F.xArg n (j : ℕ) (pre b ((j : ℕ) + 1))) (b j)‖)
        ≤ 1 := hE1
      _ ≤ (N0 : ℝ) ^ A * (n : ℝ) ^ (-A) := by
          have h1 : (n : ℝ) ≤ (N0 : ℝ) := by exact_mod_cast hsmall.le
          have h2 : (1 : ℝ) = (n : ℝ) ^ A * (n : ℝ) ^ (-A) := by
            rw [← Real.rpow_add hnR, add_neg_cancel, Real.rpow_zero]
          rw [h2]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow hnR.le h1 hA.le) (Real.rpow_nonneg hnR.le _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hnR.le _)
  · set half : ℕ := n / 2 - B with hhalf
    have hhalf1 : 1 ≤ half := by omega
    have hhalfn : half ≤ n / 2 := Nat.sub_le _ _
    have hhalfR : (0 : ℝ) < (half : ℝ) := by exact_mod_cast hhalf1
    have hn4 : (n : ℝ) ≤ 4 * (half : ℝ) := by
      have : n ≤ 4 * half := by omega
      exact_mod_cast this
    have hc := F.phaseC_not_dvd hξ
    obtain ⟨T, hT⟩ := hblk ε hε hεε₁ n (F.phaseC ξ.val) hc
    set κ : ℝ := ε ^ 3 with hκ
    have hκ0 : 0 ≤ κ := by positivity
    -- the bound for each `b`
    have hpt : ∀ b : Fin (n / 2) → ℕ,
        ∏ j : Fin (n / 2), ‖F.fCond n ξ.val (F.xArg n (j : ℕ) (pre b ((j : ℕ) + 1))) (b j)‖
          ≤ Real.exp (-κ * ((Finset.univ.filter fun j : Fin (n / 2) =>
              (j : ℕ) < half ∧ b j = 3 ∧
                ((j : ℕ), ((pre b ((j : ℕ) + 1) : ℕ) : ℤ)) ∉ T.blk).card : ℝ)) := by
      intro b
      refine le_trans (F.prod_fCond_le_damping n ξ.val half hε.le hεp b) ?_
      apply Real.exp_le_exp.mpr
      have hsub : (Finset.univ.filter fun j : Fin (n / 2) =>
            (j : ℕ) < half ∧ b j = 3 ∧ ((j : ℕ), ((pre b ((j : ℕ) + 1) : ℕ) : ℤ)) ∉ T.blk)
          ⊆ (Finset.univ.filter fun j : Fin (n / 2) =>
            (j : ℕ) < half ∧ b j = 3 ∧
              F.white n (F.phaseC ξ.val) ε (j : ℕ) ((pre b ((j : ℕ) + 1) : ℕ) : ℤ)) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        refine ⟨hj.1, hj.2.1, fun hb => hj.2.2 ?_⟩
        exact hT _ (by simp only; omega) hb
      have hc := Finset.card_le_card hsub
      have hcR : ((Finset.univ.filter fun j : Fin (n / 2) =>
            (j : ℕ) < half ∧ b j = 3 ∧
              ((j : ℕ), ((pre b ((j : ℕ) + 1) : ℕ) : ℤ)) ∉ T.blk).card : ℝ)
          ≤ ((Finset.univ.filter fun j : Fin (n / 2) =>
            (j : ℕ) < half ∧ b j = 3 ∧
              F.white n (F.phaseC ξ.val) ε (j : ℕ) ((pre b ((j : ℕ) + 1) : ℕ) : ℤ)).card : ℝ) := by
        exact_mod_cast hc
      nlinarith
    calc ((PMF.iid (pascalP F.p) (n / 2)).expect fun b =>
          ∏ j : Fin (n / 2), ‖F.fCond n ξ.val (F.xArg n (j : ℕ) (pre b ((j : ℕ) + 1))) (b j)‖)
        ≤ (PMF.iid (pascalP F.p) (n / 2)).expect fun b =>
            Real.exp (-κ * ((Finset.univ.filter fun j : Fin (n / 2) =>
              (j : ℕ) < half ∧ b j = 3 ∧
                ((j : ℕ), ((pre b ((j : ℕ) + 1) : ℕ) : ℤ)) ∉ T.blk).card : ℝ)) :=
          Sec7.expect_mono_le _ _ _
            (fun b => Finset.prod_nonneg fun j _ => norm_nonneg _) hpt
            (fun b => by
              rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
              positivity)
      _ = (PMF.iid (pascalP F.p) half).expect fun b =>
            Real.exp (-κ * ((Finset.univ.filter fun i : Fin half =>
              b i = 3 ∧ ((i : ℕ), ((pre b ((i : ℕ) + 1) : ℕ) : ℤ)) ∉ T.blk).card : ℝ)) :=
          F.expect_damping_castLE hhalfn κ T.blk
      _ ≤ C * (half : ℝ) ^ (-A) := hCb half T hhalf1
      _ ≤ C * 4 ^ A * (n : ℝ) ^ (-A) := by
          have h1 : (4 * (half : ℝ)) ^ (-A) ≤ (n : ℝ) ^ (-A) :=
            Real.rpow_le_rpow_of_nonpos hnR hn4 (by linarith)
          have h2 : (4 * (half : ℝ)) ^ (-A) = (4 : ℝ) ^ (-A) * (half : ℝ) ^ (-A) :=
            Real.mul_rpow (by norm_num) hhalfR.le
          have h3 : (half : ℝ) ^ (-A) = (4 : ℝ) ^ A * ((4 : ℝ) ^ (-A) * (half : ℝ) ^ (-A)) := by
            rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 4), add_neg_cancel,
              Real.rpow_zero, one_mul]
          rw [h3, ← h2, ← mul_assoc]
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hnR.le _)

/-- **Decay of the characteristic function multiplied by a function of the valuation sum**: for `‖h‖ ≤ 1` and
`q ∤ ξ`, `‖E[e(-ξ𝒮_n/q^n) h(s_n)]‖ ≤ C n^{-A}` (for every `A`; `C` does not depend on `h`, `ξ`, `n`). -/
theorem cexpect_h_decay : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    ∀ ξ : ZMod (F.q ^ n), ¬ (F.q ∣ ξ.val) → ∀ h : ℕ → ℂ, (∀ t, ‖h t‖ ≤ 1) →
      ‖(PMF.iid (stepLaw F.p) n).cexpect fun v =>
          F.chiC n ξ.val (F.offsetIn (F.q ^ n) v) * h (∑ i, (v i).1)‖
        ≤ C * (n : ℝ) ^ (-A) := by
  intro A hA
  obtain ⟨C, hC, hCb⟩ := pairing_decay F A hA
  exact ⟨C, hC, fun n hn ξ hξ h hh =>
    (cexpect_pairing_h F n ξ.val h hh).trans (hCb n hn ξ hξ)⟩

end SumCFAux

end ND

end GGMCollatz
