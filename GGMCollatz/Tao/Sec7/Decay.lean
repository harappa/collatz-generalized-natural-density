import GGMCollatz.Tao.Sec7.Reduction
import GGMCollatz.Tao.Sec7.Triangles
import GGMCollatz.Tao.Sec7.Bridge

/-!
# GGM Proposition 5.1: decay of the characteristic function of the Syracuse random variable (counterpart of Propositions 1.17 and 7.1 of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, files `TaoCollatz/Sec7/Decay.lean` and
`Sec7/Reduction.lean` (`key_fourier_decay`); generalized to the GGM family (p, q, r). Modified.
GGM §6 (Theorem 1.9 ⇒ Proposition 5.1).

Assembly (`n ≥ 4B + 4`, `half = ⌊n/2⌋ - B`, `ε = min(ε₀, ε₁, 1/p)`):
```
‖E χ(𝒮_n)‖ ≤ E_{𝒫} ∏_{k<n/2} ‖f(q^{2k}p^{-𝒫_{[1,k+1]}}, 𝒫_k)‖          (cexpect_pairing)
           ≤ E_{𝒫} exp(-ε³ #{k < half : 𝒫_k = 3, (k, 𝒫_{[1,k+1]}) white})   (prod_fCond_le_damping)
           ≤ E_{𝒫} exp(-ε³ #{k < half : 𝒫_k = 3, (k, 𝒫_{[1,k+1]}) ∉ ⋃T})   (black_structure)
           = E_{𝒫 ~ Pascal^{half}} exp(-ε³ #{…})                            (marginal of the first half components)
           ≤ C half^{-A} ≤ C 4^A n^{-A}                                      (renewal_white)
```
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

variable (F : Family)

open Classical in
/-- Marginalization to the first `half` components: the expected number of white points, over `b ~ Pascal^{n/2}`, which depends only
on the first `half` components equals the corresponding expectation over `Pascal^{half}`. -/
theorem expect_damping_castLE {m half : ℕ} (hh : half ≤ m) (κ : ℝ)
    (Bl : Set (ℕ × ℤ)) :
    (PMF.iid (pascalP F.p) m).expect (fun b =>
        Real.exp (-κ * ((Finset.univ.filter fun j : Fin m =>
          (j : ℕ) < half ∧ b j = 3 ∧ ((j : ℕ), ((pre b ((j : ℕ) + 1) : ℕ) : ℤ)) ∉ Bl).card : ℝ)))
      = (PMF.iid (pascalP F.p) half).expect (fun b =>
        Real.exp (-κ * ((Finset.univ.filter fun i : Fin half =>
          b i = 3 ∧ ((i : ℕ), ((pre b ((i : ℕ) + 1) : ℕ) : ℤ)) ∉ Bl).card : ℝ))) := by
  have hcard : ∀ b : Fin m → ℕ,
      (Finset.univ.filter fun j : Fin m =>
          (j : ℕ) < half ∧ b j = 3 ∧ ((j : ℕ), ((pre b ((j : ℕ) + 1) : ℕ) : ℤ)) ∉ Bl).card
        = (Finset.univ.filter fun i : Fin half =>
          (b ∘ Fin.castLE hh) i = 3 ∧
            ((i : ℕ), ((pre (b ∘ Fin.castLE hh) ((i : ℕ) + 1) : ℕ) : ℤ)) ∉ Bl).card := by
    intro b
    symm
    apply Finset.card_bij (fun i _ => Fin.castLE hh i)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hi ⊢
      rw [pre_castLE hh b (by omega)] at hi
      exact ⟨by simp, hi.1, by simpa using hi.2⟩
    · intro i _ j _ h
      exact Fin.castLE_injective hh h
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      refine ⟨⟨j, hj.1⟩, ?_, by ext; simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
      rw [pre_castLE hh b (by simp; omega)]
      have hjj : Fin.castLE hh ⟨(j : ℕ), hj.1⟩ = j := by ext; simp
      rw [hjj]
      exact ⟨hj.2.1, hj.2.2⟩
  have hg0 : ∀ b : Fin half → ℕ, 0 ≤ Real.exp (-κ * ((Finset.univ.filter fun i : Fin half =>
      b i = 3 ∧ ((i : ℕ), ((pre b ((i : ℕ) + 1) : ℕ) : ℤ)) ∉ Bl).card : ℝ)) :=
    fun b => (Real.exp_pos _).le
  rw [← iid_map_castLE (pascalP F.p) half m hh, Sec7.expect_map _ _ _ hg0]
  exact congrArg _ (funext fun b => by rw [hcard b])

/-- **GGM Proposition 5.1** (decay of the characteristic function): if `q ∤ ξ` then `‖E e(-ξ𝒮_n/q^n)‖ ≤ C n^{-A}` (for every `A`). -/
theorem prop51 : F.prop51_statement := by
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
  have hchi : (fun Y : ZMod (F.q ^ n) => eC (-(ξ.val * Y.val : ℚ) / (F.q : ℚ) ^ n))
      = F.chiC n ξ.val := rfl
  rw [hchi]
  have hE1 : ‖(F.syracZ n).cexpect (F.chiC n ξ.val)‖ ≤ 1 :=
    Sec7.cexpect_norm_le _ _ (fun y => (F.chiC_norm _ _ _).le)
  rcases lt_or_ge n N0 with hsmall | hbig
  · calc ‖(F.syracZ n).cexpect (F.chiC n ξ.val)‖ ≤ 1 := hE1
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
    -- bound at each `b`
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
    calc ‖(F.syracZ n).cexpect (F.chiC n ξ.val)‖
        ≤ (PMF.iid (pascalP F.p) (n / 2)).expect fun b =>
            ∏ j : Fin (n / 2),
              ‖F.fCond n ξ.val (F.xArg n (j : ℕ) (pre b ((j : ℕ) + 1))) (b j)‖ :=
          F.cexpect_pairing n ξ.val
      _ ≤ (PMF.iid (pascalP F.p) (n / 2)).expect fun b =>
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

end Family

end GGMCollatz
