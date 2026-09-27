import GGMCollatz.NatDen.Defs
import GGMCollatz.NatDen.SumCF.Decay

/-!
# The sum of the joint distribution, and the expectation over i.i.d. copies of the one-step law (third step of the proof of Proposition 6.7 of the paper)

The left-hand side `Σ_Y P(𝒮_n = Y, s_n = s) e(-ξY/q^n)` of the statement `sumcf_statement` is rewritten as the
expectation `E[χ(offset(v)) 1_{s_n = s}]` over the vector `v` of i.i.d. copies of the one-step law (the definition of
`jointSZ` and `PMF.map`). Also `E[1_{s_n = s}] = P(s_n = s) = nb p n s` (the valuation components are `G(μ)ⁿ`,
`iid_stepLaw_map_fst`).

* `sum_jp_chi_eq`: `Σ_Y jp(n, Y, s) e(-ξY/q^n) = E[χ(𝒮_n) 1_{s_n = s}]`.
* `expect_ind_sum_eq_nb`: `E[1_{s_n = s}] = nb p n s`.
* `norm_sum_jp_chi_le`: `‖Σ_Y jp(n, Y, s) e(-ξY/q^n)‖ ≤ nb p n s` (used to absorb small `n`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace SumCFAux

variable (F : Family)

/-- The indicator function (`ℂ`-valued) of the event `{s_n = s}`. -/
noncomputable def indC (s t : ℕ) : ℂ := if t = s then 1 else 0

theorem norm_indC_le (s t : ℕ) : ‖indC s t‖ ≤ 1 := by
  unfold indC
  split_ifs <;> simp

/-- `‖E f‖ ≤ E ‖f‖` (for observables with values in the unit disc). -/
theorem norm_cexpect_le_expect_norm {α : Type*} (p : PMF α) (f : α → ℂ) (hf : ∀ a, ‖f a‖ ≤ 1) :
    ‖p.cexpect f‖ ≤ p.expect fun a => ‖f a‖ := by
  have hsumP : Summable fun a => (p a).toReal :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have hn : ∀ a, ‖((p a).toReal : ℂ) * f a‖ = (p a).toReal * ‖f a‖ := fun a => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have hb : ∀ a, ‖((p a).toReal : ℂ) * f a‖ ≤ (p a).toReal := fun a => by
    rw [hn a]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (hf a)
  have hsn : Summable fun a => ‖((p a).toReal : ℂ) * f a‖ :=
    Summable.of_nonneg_of_le (fun a => norm_nonneg _) hb hsumP
  calc ‖p.cexpect f‖ ≤ ∑' a, ‖((p a).toReal : ℂ) * f a‖ := norm_tsum_le_tsum_norm hsn
    _ = p.expect fun a => ‖f a‖ := tsum_congr hn

/-- **Rewriting the left-hand side**: `Σ_Y P(𝒮_n = Y, s_n = s) e(-ξY/q^n) = E[χ(𝒮_n) 1_{s_n = s}]`. -/
theorem sum_jp_chi_eq (n s : ℕ) (ξ : ZMod (F.q ^ n)) :
    ∑ Y : ZMod (F.q ^ n), (jp F n Y s : ℂ) * eC (-(ξ.val * Y.val : ℚ) / (F.q : ℚ) ^ n)
      = (PMF.iid (stepLaw F.p) n).cexpect fun v =>
          F.chiC n ξ.val (F.offsetIn (F.q ^ n) v) * indC s (∑ i, (v i).1) := by
  have := F.neZero_q_pow n
  set G : ZMod (F.q ^ n) × ℕ → ℂ := fun x => F.chiC n ξ.val x.1 * indC s x.2 with hG
  have hGn : ∀ x, ‖G x‖ ≤ 1 := fun x => by
    rw [hG, norm_mul, F.chiC_norm, one_mul]
    exact norm_indC_le _ _
  have hmap := Sec7.cexpect_map ((stepLaw F.p).iid n)
    (fun v => (F.offsetIn (F.q ^ n) v, ∑ i, (v i).1)) G hGn
  rw [show (PMF.iid (stepLaw F.p) n).cexpect (fun v =>
      F.chiC n ξ.val (F.offsetIn (F.q ^ n) v) * indC s (∑ i, (v i).1))
      = ((stepLaw F.p).iid n).cexpect (fun v => G (F.offsetIn (F.q ^ n) v, ∑ i, (v i).1))
      from rfl, ← hmap]
  show _ = ∑' x, ((jointSZ F n x).toReal : ℂ) * G x
  rw [tsum_eq_sum (s := Finset.univ ×ˢ {s}) (fun x hx => by
    have hx2 : x.2 ≠ s := by
      intro h
      exact hx (Finset.mem_product.mpr ⟨Finset.mem_univ _, by simp [h]⟩)
    rw [hG]
    simp only [indC, if_neg hx2, mul_zero]), Finset.sum_product]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [Finset.sum_singleton]
  simp only [hG, indC, if_true, mul_one]
  rfl

/-- `P(s_n = s)`: the law of the valuation sum is `iidSum (G(μ)) n`. -/
theorem map_sum_fst_eq_iidSum (n : ℕ) :
    ((stepLaw F.p).iid n).map (fun v => ∑ i, (v i).1) = iidSum (geomP F.p) n := by
  rw [iidSum, ← iid_stepLaw_map_fst, PMF.map_comp]
  rfl

/-- `E[1_{s_n = s}] = nb p n s`. -/
theorem expect_ind_sum_eq_nb (n s : ℕ) :
    ((stepLaw F.p).iid n).expect (fun v => ‖indC s (∑ i, (v i).1)‖) = nb F.p n s := by
  have hg0 : ∀ t : ℕ, (0 : ℝ) ≤ ‖indC s t‖ := fun t => norm_nonneg _
  have hmap := Sec7.expect_map ((stepLaw F.p).iid n) (fun v => ∑ i, (v i).1)
    (fun t => ‖indC s t‖) hg0
  rw [← hmap, map_sum_fst_eq_iidSum]
  show ∑' t, ((iidSum (geomP F.p) n) t).toReal * ‖indC s t‖ = nb F.p n s
  rw [tsum_eq_single s (fun t ht => by simp [indC, ht])]
  simp [indC, nb]

/-- **The trivial bound**: `‖Σ_Y P(𝒮_n = Y, s_n = s) e(-ξY/q^n)‖ ≤ P(s_n = s)`. -/
theorem norm_sum_jp_chi_le (n s : ℕ) (ξ : ZMod (F.q ^ n)) :
    ‖∑ Y : ZMod (F.q ^ n), (jp F n Y s : ℂ) * eC (-(ξ.val * Y.val : ℚ) / (F.q : ℚ) ^ n)‖
      ≤ nb F.p n s := by
  rw [sum_jp_chi_eq, ← expect_ind_sum_eq_nb]
  refine (norm_cexpect_le_expect_norm _ _ (fun v => ?_)).trans (le_of_eq ?_)
  · rw [norm_mul, F.chiC_norm, one_mul]
    exact norm_indC_le _ _
  · show ((stepLaw F.p).iid n).expect _ = _
    congr 1
    funext v
    rw [norm_mul, F.chiC_norm, one_mul]

end SumCFAux

end ND

end GGMCollatz
