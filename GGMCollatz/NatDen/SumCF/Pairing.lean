import GGMCollatz.Tao.Sec7.Reduction

/-!
# The pairing bound with a function of the valuation sum inserted (first step of the proof of Proposition 6.7 of the paper)

Adapted and modified from the theorems of the same names in `GGMCollatz/Tao/Sec7/Reduction.lean`, which is derived
from `TaoCollatz/Sec7/Reduction.lean` (`cexpect_pairing_gen`, `cexpect_pairing`) of gotrevor/tao-collatz (Apache-2.0),
commit 15efca2.

**Changes**: the integrand is multiplied by a function `h(Σ_i a_i)` of the valuation sum (`‖h‖ ≤ 1`).
When a pair `(x₀, x₁)` is peeled off, the argument of `h` is shifted by the pair sum `b = a₀ + a₁`, so the induction
hypothesis is applied to `h(b + ·)`. The right-hand side (the majorant) is unchanged: since `‖h‖ ≤ 1`, the factor
`H` of the accompanying paper is bounded by `1`.

* `cexpect_pairing_gen_h`: `‖E[χ(x_{k,L} · offset(v)) h(Σ a)]‖ ≤ E_{b ~ Pascal^{m/2}} ∏_j ‖f(…)‖`.
* `cexpect_pairing_h`: the case `k = L = 0`, `m = n` (`x_{0,0} = 1`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace SumCFAux

variable (F : Family)

/-- The integrand `χ(x · offset(v)) g(Σ a)` lies in the unit disc (`‖g‖ ≤ 1`). -/
theorem norm_chiC_mul_le (n ξ k L : ℕ) (g : ℕ → ℂ) (hg : ∀ t, ‖g t‖ ≤ 1) {m : ℕ}
    (v : Fin m → ℕ × ℕ) :
    ‖F.chiC n ξ (F.xArg n k L * F.offsetIn (F.q ^ n) v) * g (∑ i, (v i).1)‖ ≤ 1 := by
  rw [norm_mul, F.chiC_norm, one_mul]
  exact hg _

/-- The valuation sum after peeling off two coordinates. -/
theorem sum_fst_cons_cons {m : ℕ} (x₀ x₁ : ℕ × ℕ) (w : Fin m → ℕ × ℕ) :
    ∑ i, ((Fin.cons x₀ (Fin.cons x₁ w : Fin (m + 1) → ℕ × ℕ) : Fin (m + 2) → ℕ × ℕ) i).1
      = (x₀.1 + x₁.1) + ∑ i, (w i).1 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

open Classical in
/-- **The pairing bound with a function of the sum** (generalization of `cexpect_pairing_gen`): if `‖h‖ ≤ 1`, then
`‖E[χ(x_{k,L} · offset(v)) h(Σ_i a_i)]‖ ≤ E_{b ~ Pascal^{⌊m/2⌋}} ∏_j ‖f(x_{k+j, L+b_{[1,j+1]}}, b_j)‖`. -/
theorem cexpect_pairing_gen_h (n ξ : ℕ) :
    ∀ m k L : ℕ, ∀ h : ℕ → ℂ, (∀ t, ‖h t‖ ≤ 1) →
      ‖(PMF.iid (stepLaw F.p) m).cexpect fun v =>
          F.chiC n ξ (F.xArg n k L * F.offsetIn (F.q ^ n) v) * h (∑ i, (v i).1)‖
        ≤ (PMF.iid (pascalP F.p) (m / 2)).expect fun b =>
            ∏ j : Fin (m / 2),
              ‖F.fCond n ξ (F.xArg n (k + (j : ℕ)) (L + pre b ((j : ℕ) + 1))) (b j)‖ := by
  have hp := F.two_le_p
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro k L h hh
    rcases Nat.lt_or_ge m 2 with hm | hm
    · have hdiv : m / 2 = 0 := by omega
      refine le_trans (Sec7.cexpect_norm_le _ _ (fun v => norm_chiC_mul_le F n ξ k L h hh v))
        (le_of_eq ?_)
      rw [hdiv, PMF.expect_iid_zero]
      exact (Finset.prod_of_isEmpty _).symm
    · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
      rw [show (m + 2) / 2 = m / 2 + 1 from Nat.add_div_right m (by norm_num)]
      set T : ℕ → ℂ := fun b => (PMF.iid (stepLaw F.p) m).cexpect fun w =>
        F.chiC n ξ (F.xArg n (k + 1) (L + b) * F.offsetIn (F.q ^ n) w) * h (b + ∑ i, (w i).1)
        with hT
      have hTle : ∀ b, ‖T b‖ ≤ 1 := fun b =>
        Sec7.cexpect_norm_le _ _
          (fun w => norm_chiC_mul_le F n ξ (k + 1) (L + b) (fun t => h (b + t)) (fun t => hh _) w)
      set H : ℕ → ℕ → ℕ → ℕ → ℂ := fun b a d d' =>
        F.chiC n ξ (F.xArg n k (L + b) * ((F.p : ZMod (F.q ^ n)) ^ a * (F.r d : ZMod (F.q ^ n))
          + (F.q : ZMod (F.q ^ n)) * (F.r d' : ZMod (F.q ^ n)))) with hH
      have hHT : ∀ b a d d', ‖H b a d d' * T b‖ ≤ 1 := by
        intro b a d d'
        rw [norm_mul, hH]
        calc ‖F.chiC n ξ _‖ * ‖T b‖ ≤ 1 * 1 :=
              mul_le_mul (F.chiC_norm _ _ _).le (hTle b) (norm_nonneg _) zero_le_one
          _ = 1 := mul_one 1
      have hpeel : ((PMF.iid (stepLaw F.p) (m + 2)).cexpect fun v =>
            F.chiC n ξ (F.xArg n k L * F.offsetIn (F.q ^ n) v) * h (∑ i, (v i).1))
          = ∑' b : ℕ, ((pascalP F.p b).toReal : ℂ)
              * ((((b : ℂ) - 1) * ((F.p : ℂ) - 1) ^ 2)⁻¹
                * ∑ a ∈ Finset.Icc 1 (b - 1), ∑ d ∈ Finset.Ioo 0 F.p, ∑ d' ∈ Finset.Ioo 0 F.p,
                    H b a d d' * T b) := by
        rw [Sec7.cexpect_iid_succ _ _ _ (fun v => norm_chiC_mul_le F n ξ k L h hh v)]
        have hinner : ∀ x₀ : ℕ × ℕ, ((PMF.iid (stepLaw F.p) (m + 1)).cexpect fun w =>
            F.chiC n ξ (F.xArg n k L * F.offsetIn (F.q ^ n)
              (Fin.cons x₀ w : Fin (m + 2) → ℕ × ℕ))
              * h (∑ i, ((Fin.cons x₀ w : Fin (m + 2) → ℕ × ℕ) i).1))
            = ∑' x₁ : ℕ × ℕ, ((stepLaw F.p x₁).toReal : ℂ)
                * (H (x₀.1 + x₁.1) x₁.1 x₀.2 x₁.2 * T (x₀.1 + x₁.1)) := by
          intro x₀
          rw [Sec7.cexpect_iid_succ _ _ _
            (fun w => norm_chiC_mul_le F n ξ k L h hh (Fin.cons x₀ w : Fin (m + 2) → ℕ × ℕ))]
          refine tsum_congr fun x₁ => ?_
          congr 1
          calc ((PMF.iid (stepLaw F.p) m).cexpect fun w =>
                F.chiC n ξ (F.xArg n k L * F.offsetIn (F.q ^ n)
                  (Fin.cons x₀ (Fin.cons x₁ w : Fin (m + 1) → ℕ × ℕ) : Fin (m + 2) → ℕ × ℕ))
                * h (∑ i, ((Fin.cons x₀ (Fin.cons x₁ w : Fin (m + 1) → ℕ × ℕ)
                    : Fin (m + 2) → ℕ × ℕ) i).1))
              = (PMF.iid (stepLaw F.p) m).cexpect fun w => H (x₀.1 + x₁.1) x₁.1 x₀.2 x₁.2
                  * (F.chiC n ξ (F.xArg n (k + 1) (L + (x₀.1 + x₁.1))
                    * F.offsetIn (F.q ^ n) w) * h ((x₀.1 + x₁.1) + ∑ i, (w i).1)) := by
                congr 1
                funext w
                rw [F.xArg_offset_peel2 n k L x₀ x₁ w, F.chiC_add, sum_fst_cons_cons]
                ring
            _ = H (x₀.1 + x₁.1) x₁.1 x₀.2 x₁.2 * T (x₀.1 + x₁.1) := by
                rw [Sec7.cexpect_const_mul, hT]
        rw [tsum_congr fun x₀ => by rw [hinner x₀]]
        exact Pair.tsum_step_pair hp (fun b a d d' => H b a d d' * T b) hHT
      rw [hpeel]
      have hsum_fCond : ∀ b : ℕ,
          (((b : ℂ) - 1) * ((F.p : ℂ) - 1) ^ 2)⁻¹
              * ∑ a ∈ Finset.Icc 1 (b - 1), ∑ d ∈ Finset.Ioo 0 F.p, ∑ d' ∈ Finset.Ioo 0 F.p,
                  H b a d d' * T b
            = F.fCond n ξ (F.xArg n k (L + b)) b * T b := by
        intro b
        simp only [← Finset.sum_mul]
        rw [Family.fCond, hH]
        ring
      have hIH : ∀ b, ‖T b‖ ≤ (PMF.iid (pascalP F.p) (m / 2)).expect fun c =>
          ∏ j : Fin (m / 2),
            ‖F.fCond n ξ (F.xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
              (c j)‖ :=
        fun b => IH m (by omega) (k + 1) (L + b) (fun t => h (b + t)) (fun t => hh _)
      have hE0 : ∀ b, (0:ℝ) ≤ (PMF.iid (pascalP F.p) (m / 2)).expect fun c =>
          ∏ j : Fin (m / 2),
            ‖F.fCond n ξ (F.xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
              (c j)‖ :=
        fun b => Sec7.expect_nonneg _ _ fun c => Finset.prod_nonneg fun j _ => norm_nonneg _
      have hE1 : ∀ b, ((PMF.iid (pascalP F.p) (m / 2)).expect fun c =>
          ∏ j : Fin (m / 2),
            ‖F.fCond n ξ (F.xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
              (c j)‖) ≤ 1 :=
        fun b => Sec7.expect_le_one _ _
          (fun c => Finset.prod_nonneg fun j _ => norm_nonneg _)
          (fun c => Finset.prod_le_one (fun j _ => norm_nonneg _)
            (fun j _ => F.fCond_norm_le_one _ _ _ _))
      have hΦnorm : ∀ b : ℕ, ‖((pascalP F.p b).toReal : ℂ)
            * ((((b : ℂ) - 1) * ((F.p : ℂ) - 1) ^ 2)⁻¹
              * ∑ a ∈ Finset.Icc 1 (b - 1), ∑ d ∈ Finset.Ioo 0 F.p, ∑ d' ∈ Finset.Ioo 0 F.p,
                  H b a d d' * T b)‖
          = (pascalP F.p b).toReal * (‖F.fCond n ξ (F.xArg n k (L + b)) b‖ * ‖T b‖) := by
        intro b
        rw [hsum_fCond b, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ENNReal.toReal_nonneg]
      have hmass : Summable fun b => (pascalP F.p b).toReal :=
        ENNReal.summable_toReal (pascalP F.p).tsum_coe_ne_top
      have hΦbound : ∀ b : ℕ,
          (pascalP F.p b).toReal * (‖F.fCond n ξ (F.xArg n k (L + b)) b‖ * ‖T b‖)
            ≤ (pascalP F.p b).toReal := fun b => by
        calc (pascalP F.p b).toReal * (‖F.fCond n ξ (F.xArg n k (L + b)) b‖ * ‖T b‖)
            ≤ (pascalP F.p b).toReal * (1 * 1) := by
              refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
              exact mul_le_mul (F.fCond_norm_le_one _ _ _ _) (hTle b) (norm_nonneg _)
                zero_le_one
          _ = (pascalP F.p b).toReal := by ring
      have hΦS : Summable fun b : ℕ => ‖((pascalP F.p b).toReal : ℂ)
          * ((((b : ℂ) - 1) * ((F.p : ℂ) - 1) ^ 2)⁻¹
            * ∑ a ∈ Finset.Icc 1 (b - 1), ∑ d ∈ Finset.Ioo 0 F.p, ∑ d' ∈ Finset.Ioo 0 F.p,
                H b a d d' * T b)‖ :=
        Summable.of_nonneg_of_le (fun b => norm_nonneg _)
          (fun b => (hΦnorm b).le.trans (hΦbound b)) hmass
      have hRHSb : ∀ b : ℕ, (0:ℝ) ≤ (pascalP F.p b).toReal
          * (‖F.fCond n ξ (F.xArg n k (L + b)) b‖
            * (PMF.iid (pascalP F.p) (m / 2)).expect fun c =>
              ∏ j : Fin (m / 2),
                ‖F.fCond n ξ (F.xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
                  (c j)‖) :=
        fun b => mul_nonneg ENNReal.toReal_nonneg
          (mul_nonneg (norm_nonneg _) (hE0 b))
      have hRHSS : Summable fun b : ℕ => (pascalP F.p b).toReal
          * (‖F.fCond n ξ (F.xArg n k (L + b)) b‖
            * (PMF.iid (pascalP F.p) (m / 2)).expect fun c =>
              ∏ j : Fin (m / 2),
                ‖F.fCond n ξ (F.xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
                  (c j)‖) := by
        refine Summable.of_nonneg_of_le hRHSb (fun b => ?_) hmass
        calc (pascalP F.p b).toReal * (‖F.fCond n ξ (F.xArg n k (L + b)) b‖ * _)
            ≤ (pascalP F.p b).toReal * (1 * 1) := by
              refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
              exact mul_le_mul (F.fCond_norm_le_one _ _ _ _) (hE1 b) (hE0 b) zero_le_one
          _ = (pascalP F.p b).toReal := by ring
      have hprodcons : ∀ (b : ℕ) (c : Fin (m / 2) → ℕ),
          (∏ j : Fin (m / 2 + 1),
            ‖F.fCond n ξ (F.xArg n (k + (j : ℕ))
                (L + pre (Fin.cons b c : Fin (m / 2 + 1) → ℕ) ((j : ℕ) + 1)))
              ((Fin.cons b c : Fin (m / 2 + 1) → ℕ) j)‖)
            = ‖F.fCond n ξ (F.xArg n k (L + b)) b‖
              * ∏ j : Fin (m / 2),
                ‖F.fCond n ξ (F.xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
                  (c j)‖ := by
        intro b c
        rw [Fin.prod_univ_succ]
        simp only [Fin.val_zero, Fin.cons_zero, Fin.val_succ, Fin.cons_succ, Pair.pre_cons,
          pre_zero, add_zero]
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [show k + ((j : ℕ) + 1) = (k + 1) + (j : ℕ) from by ring,
          show L + (b + pre c ((j : ℕ) + 1)) = (L + b) + pre c ((j : ℕ) + 1) from by ring]
      have htarget : ((PMF.iid (pascalP F.p) (m / 2 + 1)).expect fun b =>
            ∏ j : Fin (m / 2 + 1),
              ‖F.fCond n ξ (F.xArg n (k + (j : ℕ)) (L + pre b ((j : ℕ) + 1))) (b j)‖)
          = ∑' b : ℕ, (pascalP F.p b).toReal
              * (‖F.fCond n ξ (F.xArg n k (L + b)) b‖
                * (PMF.iid (pascalP F.p) (m / 2)).expect fun c =>
                  ∏ j : Fin (m / 2),
                    ‖F.fCond n ξ (F.xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
                      (c j)‖) := by
        rw [PMF.expect_iid_succ _ _ _
          (fun v => Finset.prod_nonneg fun j _ => norm_nonneg _)
          (fun v => Finset.prod_le_one (fun j _ => norm_nonneg _)
            (fun j _ => F.fCond_norm_le_one _ _ _ _))]
        refine tsum_congr fun b => ?_
        congr 1
        rw [show (fun c : Fin (m / 2) → ℕ =>
            ∏ j : Fin (m / 2 + 1),
              ‖F.fCond n ξ (F.xArg n (k + (j : ℕ))
                  (L + pre (Fin.cons b c : Fin (m / 2 + 1) → ℕ) ((j : ℕ) + 1)))
                ((Fin.cons b c : Fin (m / 2 + 1) → ℕ) j)‖)
          = fun c : Fin (m / 2) → ℕ => ‖F.fCond n ξ (F.xArg n k (L + b)) b‖
              * ∏ j : Fin (m / 2),
                ‖F.fCond n ξ (F.xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
                  (c j)‖ from funext fun c => hprodcons b c, Sec7.expect_const_mul]
      calc ‖∑' b : ℕ, ((pascalP F.p b).toReal : ℂ)
            * ((((b : ℂ) - 1) * ((F.p : ℂ) - 1) ^ 2)⁻¹
              * ∑ a ∈ Finset.Icc 1 (b - 1), ∑ d ∈ Finset.Ioo 0 F.p, ∑ d' ∈ Finset.Ioo 0 F.p,
                  H b a d d' * T b)‖
          ≤ ∑' b : ℕ, ‖((pascalP F.p b).toReal : ℂ)
              * ((((b : ℂ) - 1) * ((F.p : ℂ) - 1) ^ 2)⁻¹
                * ∑ a ∈ Finset.Icc 1 (b - 1), ∑ d ∈ Finset.Ioo 0 F.p, ∑ d' ∈ Finset.Ioo 0 F.p,
                    H b a d d' * T b)‖ :=
            norm_tsum_le_tsum_norm hΦS
        _ ≤ ∑' b : ℕ, (pascalP F.p b).toReal
              * (‖F.fCond n ξ (F.xArg n k (L + b)) b‖
                * (PMF.iid (pascalP F.p) (m / 2)).expect fun c =>
                  ∏ j : Fin (m / 2),
                    ‖F.fCond n ξ (F.xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
                      (c j)‖) := by
            refine hΦS.tsum_le_tsum (fun b => ?_) hRHSS
            rw [hΦnorm b]
            refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
            exact mul_le_mul_of_nonneg_left (hIH b) (norm_nonneg _)
        _ = _ := htarget.symm

open Classical in
/-- **The pairing bound with a function of the sum** (generalization of `cexpect_pairing`): if `‖h‖ ≤ 1`, then
`‖E[χ(𝒮_n) h(s_n)]‖ ≤ E_{𝒫 ~ Pascal(μ)^{⌊n/2⌋}} ∏_k ‖f(q^{2k} p^{-𝒫_{[1,k+1]}}, 𝒫_k)‖`
(`𝒮_n = offset(v)`, `s_n = Σ_i a_i`). -/
theorem cexpect_pairing_h (n ξ : ℕ) (h : ℕ → ℂ) (hh : ∀ t, ‖h t‖ ≤ 1) :
    ‖(PMF.iid (stepLaw F.p) n).cexpect fun v =>
        F.chiC n ξ (F.offsetIn (F.q ^ n) v) * h (∑ i, (v i).1)‖
      ≤ (PMF.iid (pascalP F.p) (n / 2)).expect fun b =>
          ∏ j : Fin (n / 2), ‖F.fCond n ξ (F.xArg n (j : ℕ) (pre b ((j : ℕ) + 1))) (b j)‖ := by
  have hgen := cexpect_pairing_gen_h F n ξ n 0 0 h hh
  have hx : F.xArg n 0 0 = 1 := by
    unfold Family.xArg
    simp
  simp only [hx, one_mul, zero_add] at hgen
  exact hgen

end SumCFAux

end ND

end GGMCollatz
