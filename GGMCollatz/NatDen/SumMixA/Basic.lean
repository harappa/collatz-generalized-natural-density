import GGMCollatz.NatDen.Statements
import GGMCollatz.Tao.Sec6.FromDecay
import GGMCollatz.Tao.Sec5.Tail

/-!
# Auxiliary (1) for Proposition 6.12 (a) of the paper: the conditioned density in reversed form, the negative binomial, the convolution of projections

Notation:

* `jpR F n σ`: `Y ↦ P(roff_n = Y, s_n = σ)` (the reversed form `roff`, `Tao/Sec6/Factor.lean`). It equals `jp F n Y σ`
  (`jp_eq_jpR`; an i.i.d. law is invariant under reversing the order).
* `nb_dev_tail`: `P(s_n = s) ≤ C (e^{-c(s - μn)²/(n+1)} + e^{-c|s - μn|})` (Chernoff, `geom_dev_tail`).
* `proj_jp_eq`: **the convolution (T4)**. `𝒮_{k+d} mod q^k` is determined by the first `k` entries alone, and the sum of the
  remaining `d` valuations is independent, so `Σ_{Y ↦ Z} P(𝒮_{k+d} = Y, s_{k+d} = s) = Σ_{σ ≤ s} P(s_d = s - σ) P(𝒮_k = Z, s_k = σ)`.

The proof of `roff_eq_offsetIn_rev` extracts the identity inside `syracZ_eq_rev_fint` of `Tao/Syracuse/SyracRV.lean`
(derived from `TaoCollatz/Syracuse/SyracRV.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2).
-/

open scoped BigOperators ENNReal

namespace GGMCollatz

namespace ND

namespace SumMixAAux

open Family

variable (F : Family)

/-! ### General lemmas -/

/-- The real value of the mass of a push-forward. -/
theorem map_apply_toReal {α β : Type*} [DecidableEq β] (μ : PMF α) (f : α → β) (b : β) :
    ((μ.map f) b).toReal = ∑' a, (μ a).toReal * (if f a = b then (1 : ℝ) else 0) := by
  rw [PMF.map_apply, ENNReal.tsum_toReal_eq (fun a => by
    split_ifs
    · exact μ.apply_ne_top a
    · exact ENNReal.zero_ne_top)]
  refine tsum_congr fun a => ?_
  by_cases h : f a = b
  · rw [if_pos h.symm, if_pos h, mul_one]
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero, ENNReal.toReal_zero]

/-- The total mass of a restricted push-forward is the probability of the event. -/
theorem sum_restrictedDensity {α β : Type*} [Fintype β] [DecidableEq β] (P : PMF α) (X : α → β)
    (E : α → Prop) [DecidablePred E] :
    ∑ Y, Mix.restrictedDensity P X E Y = ∑' a, (P a).toReal * (if E a then (1 : ℝ) else 0) := by
  have hPsum : Summable fun a => (P a).toReal := ENNReal.summable_toReal P.tsum_coe_ne_top
  have hs : ∀ Y, Summable fun a => (P a).toReal * (if X a = Y ∧ E a then (1 : ℝ) else 0) :=
    fun Y => Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num))
      (fun a => by split <;> simp [ENNReal.toReal_nonneg]) hPsum
  unfold Mix.restrictedDensity
  rw [← Summable.tsum_finsetSum (fun Y _ => hs Y)]
  refine tsum_congr fun a => ?_
  rw [← Finset.mul_sum]
  congr 1
  by_cases hE : E a
  · rw [if_pos hE, Finset.sum_eq_single (X a)]
    · rw [if_pos ⟨rfl, hE⟩]
    · intro Y _ hY; rw [if_neg (fun h => hY h.1.symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hE]; exact Finset.sum_eq_zero (fun Y _ => if_neg (fun h => hE h.2))

/-- **Splitting an i.i.d. vector into front and back**: `μ^{⊗(k+d)} = μ^{⊗k} ⊗ μ^{⊗d}` (`Fin.append`). -/
theorem iid_add_eq_bind {α : Type*} (μ : PMF α) (k d : ℕ) :
    μ.iid (k + d) = (μ.iid k).bind (fun vh => (μ.iid d).map (fun vt => Fin.append vh vt)) := by
  classical
  ext v
  rw [PMF.bind_apply, tsum_eq_single (fun i => v (Fin.castAdd d i))]
  · rw [PMF.map_apply, tsum_eq_single (fun i => v (Fin.natAdd k i))]
    · rw [if_pos Fin.append_castAdd_natAdd.symm, PMF.iid_apply_eq_prod, PMF.iid_apply_eq_prod,
        PMF.iid_apply_eq_prod, Fin.prod_univ_add]
    · intro vt hvt
      rw [if_neg]
      intro h
      apply hvt
      funext i
      rw [h, Fin.append_right]
  · intro vh hvh
    rw [PMF.map_apply, ENNReal.tsum_eq_zero.mpr, mul_zero]
    intro vt
    rw [if_neg]
    intro h
    apply hvh
    funext i
    rw [h, Fin.append_left]

/-! ### The reversed form -/

/-- `roff` is the reversed `offsetIn` (the identity of `syracZ_eq_rev_fint`). -/
theorem roff_eq_offsetIn_rev (n : ℕ) (b : Fin n → ℕ × ℕ) :
    F.roff n b = F.offsetIn (F.q ^ n) (b ∘ Fin.rev) := by
  have hunit := F.p_mul_inv_zmod n
  unfold roff
  set a : Fin n → ℕ := fun i => (b i).1 with ha
  rw [F.fint_eq_sum_range, Int.cast_sum, Finset.sum_mul, ← Finset.sum_range_reflect]
  unfold offsetIn
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hj' : n - 1 - (n - 1 - j) = j := by omega
  rw [hj']
  have hsplit : pre (a ∘ Fin.rev) (j + 1) + pre a (n - 1 - j) = pre a n := by
    have := pre_comp_rev a (m := j + 1) (by omega)
    rwa [show n - (j + 1) = n - 1 - j from by omega] at this
  have hvget : vget (fun i => F.r (b i).2) 0 (n - 1 - j)
      = F.r (vget (fun i => ((b ∘ Fin.rev) i).2) 0 j) := by
    rw [vget_of_lt _ _ (by omega), vget_of_lt _ _ hj]
    simp only [Function.comp_apply]
    congr 3
    apply Fin.ext
    rw [Fin.val_rev]
    simp only
    omega
  rw [hvget]
  have hpre_eq : pre (fun i => ((b ∘ Fin.rev) i).1) (j + 1) = pre (a ∘ Fin.rev) (j + 1) := rfl
  rw [hpre_eq]
  set P := pre a (n - 1 - j)
  set Q := pre (a ∘ Fin.rev) (j + 1)
  push_cast
  rw [← hsplit, pow_add]
  have h2 : (F.p : ZMod (F.q ^ n)) ^ P * ((F.p : ZMod (F.q ^ n))⁻¹) ^ P = 1 := by
    rw [← mul_pow, hunit, one_pow]
  linear_combination ((F.q : ZMod (F.q ^ n)) ^ j * ((F.p : ZMod (F.q ^ n))⁻¹) ^ Q
    * (F.r (vget (fun i => ((b ∘ Fin.rev) i).2) 0 j) : ZMod (F.q ^ n))) * h2

/-- The reversed form of `jointSZ`. -/
theorem jointSZ_eq_roff (n : ℕ) :
    jointSZ F n = ((stepLaw F.p).iid n).map (fun v => (F.roff n v, pre (fun i => (v i).1) n)) := by
  unfold jointSZ
  conv_lhs => rw [← iid_map_rev (stepLaw F.p) n]
  rw [PMF.map_comp]
  congr 1
  funext v
  simp only [Function.comp_apply]
  rw [roff_eq_offsetIn_rev, pre_eq_fin_sum]
  congr 1
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun i => by rw [Fin.revPerm_apply])

/-- The conditioned density in reversed form `Y ↦ P(roff_n = Y, s_n = σ)`. -/
noncomputable def jpR (n σ : ℕ) : ZMod (F.q ^ n) → ℝ :=
  Mix.restrictedDensity ((stepLaw F.p).iid n) (F.roff n) (fun v => pre (fun i => (v i).1) n = σ)

theorem jp_eq_jpR (n : ℕ) (Y : ZMod (F.q ^ n)) (s : ℕ) : jp F n Y s = jpR F n s Y := by
  unfold jp jpR Mix.restrictedDensity
  rw [jointSZ_eq_roff, map_apply_toReal]
  refine tsum_congr fun v => ?_
  congr 1
  by_cases h : F.roff n v = Y ∧ pre (fun i => (v i).1) n = s
  · rw [if_pos (Prod.mk_inj.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (Prod.mk_inj.mp h')), if_neg h]

theorem jpR_nonneg (n σ : ℕ) (Y : ZMod (F.q ^ n)) : 0 ≤ jpR F n σ Y :=
  Mix.restrictedDensity_nonneg _ _ _ Y

theorem jp_nonneg (n : ℕ) (Y : ZMod (F.q ^ n)) (s : ℕ) : 0 ≤ jp F n Y s :=
  ENNReal.toReal_nonneg

/-! ### The negative binomial -/

/-- The law of `s_n` is the push-forward of the i.i.d. one-step law under the sum of the valuations. -/
theorem iidSum_geomP_eq_map (n : ℕ) :
    iidSum (geomP F.p) n = ((stepLaw F.p).iid n).map (fun v => ∑ i, (v i).1) := by
  unfold iidSum
  rw [← iid_stepLaw_map_fst, PMF.map_comp]
  rfl

/-- `P(s_n = s)` written in terms of the i.i.d. one-step law. -/
theorem nb_eq_tsum (n s : ℕ) :
    nb F.p n s = ∑' v : Fin n → ℕ × ℕ,
      (((stepLaw F.p).iid n) v).toReal * (if pre (fun i => (v i).1) n = s then (1 : ℝ) else 0) := by
  unfold nb
  rw [iidSum_geomP_eq_map, map_apply_toReal]
  simp_rw [pre_eq_fin_sum]

theorem sum_jpR (n σ : ℕ) : ∑ Y, jpR F n σ Y = nb F.p n σ := by
  unfold jpR
  rw [sum_restrictedDensity, nb_eq_tsum]

theorem sum_jp (n σ : ℕ) : ∑ Y, jp F n Y σ = nb F.p n σ := by
  simp_rw [jp_eq_jpR]; exact sum_jpR F n σ

theorem nb_nonneg (n s : ℕ) : 0 ≤ nb F.p n s := ENNReal.toReal_nonneg

/-- The sum of the masses of finitely many values is at most 1. -/
theorem sum_nb_le_one (n : ℕ) (S : Finset ℕ) : ∑ s ∈ S, nb F.p n s ≤ 1 := by
  unfold nb
  rw [← ENNReal.toReal_sum (fun s _ => PMF.apply_ne_top _ s)]
  have h : ∑ s ∈ S, iidSum (geomP F.p) n s ≤ 1 := by
    calc ∑ s ∈ S, iidSum (geomP F.p) n s ≤ ∑' s, iidSum (geomP F.p) n s := ENNReal.sum_le_tsum S
      _ = 1 := PMF.tsum_coe _
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact h)

theorem nb_le_one (n s : ℕ) : nb F.p n s ≤ 1 := by
  have := sum_nb_le_one F n {s}
  simpa using this

/-- **The Chernoff tail** (`geom_dev_tail`, GGM `ineq:chernofftail`). -/
theorem nb_dev_tail : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n s : ℕ,
    nb F.p n s ≤ C * (Real.exp (-(c * ((s : ℝ) - muP F.p * n) ^ 2 / (n + 1)))
      + Real.exp (-(c * |(s : ℝ) - muP F.p * n|))) := by
  obtain ⟨c, C, hc, hC, h⟩ := F.geom_dev_tail
  refine ⟨c, C, hc, hC, fun n s => ?_⟩
  have hnb : nb F.p n s = expect (PMF.iid (geomP F.p) n) (Set.indicator {a | pre a n = s} 1) := by
    unfold nb iidSum expect
    rw [map_apply_toReal]
    refine tsum_congr fun a => ?_
    congr 1
    by_cases ha : pre a n = s
    · rw [Set.indicator_of_mem (show a ∈ {a : Fin n → ℕ | pre a n = s} from ha), Pi.one_apply,
        if_pos (by rw [← pre_eq_fin_sum]; exact ha)]
    · rw [Set.indicator_of_notMem (show a ∉ {a : Fin n → ℕ | pre a n = s} from ha),
        if_neg (by rw [← pre_eq_fin_sum]; exact ha)]
  set t : ℝ := |(s : ℝ) - muP F.p * n| with ht
  have hsub : {a : Fin n → ℕ | pre a n = s} ⊆ {a | t ≤ |(pre a n : ℝ) - F.mu * n|} := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [ha]
    exact le_rfl
  rw [hnb]
  refine (expect_indicator_mono _ hsub).trans ((h n t (abs_nonneg _) n le_rfl).trans (le_of_eq ?_))
  rw [ht, sq_abs]

/-! ### The convolution (T4) -/

/-- An identity of PMFs for the projection and the push-forward of the sum. -/
theorem jointSZ_map_proj (k d : ℕ) :
    (jointSZ F (k + d)).map (fun p => (ZMod.castHom (pow_dvd_pow F.q (Nat.le_add_right k d))
        (ZMod (F.q ^ k)) p.1, p.2))
      = (jointSZ F k).bind (fun p => (iidSum (geomP F.p) d).map (fun t => (p.1, p.2 + t))) := by
  unfold jointSZ
  rw [PMF.map_comp, iid_add_eq_bind, PMF.map_bind, PMF.bind_map, iidSum_geomP_eq_map]
  congr 1
  funext vh
  simp only [Function.comp_apply]
  rw [PMF.map_comp, PMF.map_comp]
  congr 1
  funext vt
  simp only [Function.comp_apply]
  rw [F.castHom_offsetIn (Nat.le_add_right k d), F.offsetIn_truncate (Nat.le_add_right k d)]
  have hcut : (Fin.append vh vt) ∘ Fin.castLE (Nat.le_add_right k d) = vh := by
    funext i
    simp only [Function.comp_apply]
    rw [show Fin.castLE (Nat.le_add_right k d) i = Fin.castAdd d i from Fin.ext rfl,
      Fin.append_left]
  rw [hcut, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- **The convolution (T4)** (projection and the condition on the sum). -/
theorem proj_jp_eq (k d s : ℕ) (Z : ZMod (F.q ^ k)) :
    ∑ Y ∈ Finset.univ.filter (fun Y : ZMod (F.q ^ (k + d)) =>
        ZMod.castHom (pow_dvd_pow F.q (Nat.le_add_right k d)) (ZMod (F.q ^ k)) Y = Z),
        jp F (k + d) Y s
      = ∑ σ ∈ Finset.range (s + 1), nb F.p d (s - σ) * jp F k Z σ := by
  classical
  set π := ZMod.castHom (pow_dvd_pow F.q (Nat.le_add_right k d)) (ZMod (F.q ^ k)) with hπ
  have hL : ((jointSZ F (k + d)).map (fun p => (π p.1, p.2))) (Z, s)
      = ∑ Y ∈ Finset.univ.filter (fun Y : ZMod (F.q ^ (k + d)) => π Y = Z),
          jointSZ F (k + d) (Y, s) := by
    rw [PMF.map_apply, ENNReal.tsum_prod', tsum_fintype, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun Y _ => ?_)
    rw [tsum_eq_single s]
    · by_cases hY : π Y = Z
      · rw [if_pos (by rw [hY]), if_pos hY]
      · rw [if_neg (fun h => hY (Prod.mk_inj.mp h).1.symm), if_neg hY]
    · intro t ht
      rw [if_neg (fun h => ht (Prod.mk_inj.mp h).2.symm)]
  have hR : ((jointSZ F k).bind (fun p => (iidSum (geomP F.p) d).map (fun t => (p.1, p.2 + t))))
        (Z, s)
      = ∑ σ ∈ Finset.range (s + 1), iidSum (geomP F.p) d (s - σ) * jointSZ F k (Z, σ) := by
    rw [PMF.bind_apply, ENNReal.tsum_prod', tsum_eq_single Z]
    · rw [tsum_eq_sum (s := Finset.range (s + 1))]
      · refine Finset.sum_congr rfl (fun σ hσ => ?_)
        rw [Finset.mem_range] at hσ
        rw [PMF.map_apply, tsum_eq_single (s - σ), if_pos (by
          rw [Prod.mk_inj]; exact ⟨rfl, by omega⟩), mul_comm]
        intro t ht
        rw [if_neg (fun h => ht (by have := (Prod.mk_inj.mp h).2; omega))]
      · intro σ hσ
        rw [Finset.mem_range] at hσ
        rw [PMF.map_apply, ENNReal.tsum_eq_zero.mpr, mul_zero]
        intro t
        rw [if_neg (fun h => hσ (by have := (Prod.mk_inj.mp h).2; omega))]
    · intro Z' hZ'
      rw [ENNReal.tsum_eq_zero.mpr]
      intro σ
      rw [PMF.map_apply, ENNReal.tsum_eq_zero.mpr, mul_zero]
      intro t
      rw [if_neg (fun h => hZ' (Prod.mk_inj.mp h).1.symm)]
  have hE := congrArg (fun μ : PMF (ZMod (F.q ^ k) × ℕ) => (μ (Z, s)).toReal)
    (jointSZ_map_proj F k d)
  rw [hL, hR, ENNReal.toReal_sum (fun Y _ => PMF.apply_ne_top _ _),
    ENNReal.toReal_sum (fun σ _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (PMF.apply_ne_top _ _))] at hE
  unfold jp nb
  rw [hE]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [ENNReal.toReal_mul]

end SumMixAAux

end ND

end GGMCollatz
