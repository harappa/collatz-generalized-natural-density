import GGMCollatz.Tao.Sec7.WhiteExit

/-!
# GGM §7: the walk after the passage and the main iteration (7.53) (first half of Case 3 of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/Case3.lean` (`pathSum`,
`Q_le_walk_damped`, `Q_le_damped_iter`); generalized to the GGM family (p, q, r). Modified.

* `pathSum v p`: the sum of the first `p` steps of the walk.
* `Q_le_walk_damped`, `Q_le_damped_iter`: the main iteration (7.53) (the first passage, then `P` steps keeping
  the decay from the white points in the strip).
-/

open scoped ENNReal

namespace GGMCollatz

/-- The sum of the first `p` steps of the walk `v` (the total sum if `p ≥ T`; `pathSum` of tao-collatz). -/
def pathSum {T : ℕ} (v : Fin T → ℕ × ℤ) (p : ℕ) : ℕ × ℤ :=
  ((List.ofFn v).take p).sum

@[simp] theorem pathSum_zero {T : ℕ} (v : Fin T → ℕ × ℤ) : pathSum v 0 = 0 := rfl

/-- Peeling off the head: `pathSum (cons d w) (p+1) = d + pathSum w p`. -/
theorem pathSum_cons {T : ℕ} (d : ℕ × ℤ) (w : Fin T → ℕ × ℤ) (p : ℕ) :
    pathSum (Fin.cons d w) (p + 1) = d + pathSum w p := by
  rw [pathSum, pathSum, List.ofFn_succ]
  simp [Fin.cons_succ]

namespace Family

variable (F : Family)

/-- **Iteration over `P` steps keeping the decay from the white points in the strip** (`Q_le_walk_damped` of tao-collatz). -/
theorem Q_le_walk_damped (half : ℕ) (W : Set (ℕ × ℤ)) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∀ (P : ℕ) (j : ℕ) (l : ℤ),
      ENNReal.ofReal (F.Q half W κ j l)
        ≤ ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
            ENNReal.ofReal (
              Real.exp (-κ * ∑ p ∈ Finset.range P,
                Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                  (j + (pathSum v p).1, l + (pathSum v p).2)) *
              F.Q half W κ (j + (pathSum v P).1) (l + (pathSum v P).2)) := by
  intro P
  induction P with
  | zero =>
    intro j l
    rw [PMF.tsum_iid_zero_mul F.hold
      (fun v : Fin 0 → ℕ × ℤ => ENNReal.ofReal (
        Real.exp (-κ * ∑ p ∈ Finset.range 0,
          Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
            (j + (pathSum v p).1, l + (pathSum v p).2)) *
        F.Q half W κ (j + (pathSum v 0).1) (l + (pathSum v 0).2)))]
    simp
  | succ P IH =>
    intro j l
    rw [PMF.tsum_iid_succ_mul F.hold P]
    rcases Nat.lt_or_ge half j with hout | hin
    · rw [F.Q_boundary _ _ _ _ _ hout, ENNReal.ofReal_one]
      have hone : ∀ (d : ℕ × ℤ) (w : Fin P → ℕ × ℤ),
          ENNReal.ofReal (
            Real.exp (-κ * ∑ p ∈ Finset.range (P + 1),
              Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                (j + (pathSum (Fin.cons d w) p).1,
                  l + (pathSum (Fin.cons d w) p).2)) *
            F.Q half W κ (j + (pathSum (Fin.cons d w) (P + 1)).1)
              (l + (pathSum (Fin.cons d w) (P + 1)).2)) = 1 := by
        intro d w
        have hind : ∀ p : ℕ,
            Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) (1 : ℕ × ℤ → ℝ)
              (j + (pathSum (Fin.cons d w) p).1,
                l + (pathSum (Fin.cons d w) p).2) = 0 := by
          intro p
          refine Set.indicator_of_notMem (fun hmem => ?_) 1
          have := hmem.2
          simp only [Set.mem_ofPred_eq] at this
          omega
        have hQ : F.Q half W κ (j + (pathSum (Fin.cons d w) (P + 1)).1)
            (l + (pathSum (Fin.cons d w) (P + 1)).2) = 1 :=
          F.Q_boundary _ _ _ _ _ (by omega)
        rw [hQ, mul_one, Finset.sum_congr rfl (fun p _ => hind p)]
        simp
      refine le_of_eq ?_
      have hin1 : (∑' w : Fin P → ℕ × ℤ, F.hold.iid P w * 1) = 1 := by
        rw [tsum_congr fun w : Fin P → ℕ × ℤ => mul_one (F.hold.iid P w),
          (F.hold.iid P).tsum_coe]
      have h1 : (1 : ℝ≥0∞) = ∑' d : ℕ × ℤ, F.hold d * ∑' w : Fin P → ℕ × ℤ,
          F.hold.iid P w * 1 :=
        (F.hold.tsum_coe.symm).trans
          (tsum_congr fun d => by rw [hin1, mul_one])
      refine h1.trans (tsum_congr fun d => ?_)
      refine congrArg (F.hold d * ·) (tsum_congr fun w => ?_)
      rw [hone d w]
    · rw [F.Q_rec _ _ _ _ _ hin]
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      have hlift : ENNReal.ofReal
            (∑' d : ℕ × ℤ, (F.hold d).toReal * F.Q half W κ (j + d.1) (l + d.2))
          = ∑' d : ℕ × ℤ, F.hold d * ENNReal.ofReal (F.Q half W κ (j + d.1) (l + d.2)) := by
        rw [← PMF.toReal_tsum_mul_ofReal F.hold _ (fun d => F.Q_nonneg _ _ _ _ _),
          ENNReal.ofReal_toReal]
        exact ne_top_of_le_ne_top (by simp)
          (PMF.tsum_mul_ofReal_le_one F.hold _ (fun d => F.Q_le_one _ _ _ hκ _ _))
      rw [hlift, ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun d => ?_
      rw [← mul_assoc, mul_comm (ENNReal.ofReal (Real.exp _)) (F.hold d), mul_assoc]
      refine mul_le_mul_right ?_ (F.hold d)
      have hIH := IH (j + d.1) (l + d.2)
      calc ENNReal.ofReal (Real.exp (-κ * Set.indicator W 1 (j, l)))
            * ENNReal.ofReal (F.Q half W κ (j + d.1) (l + d.2))
          ≤ ENNReal.ofReal (Real.exp (-κ * Set.indicator W 1 (j, l)))
            * ∑' w : Fin P → ℕ × ℤ, F.hold.iid P w *
              ENNReal.ofReal (
                Real.exp (-κ * ∑ p ∈ Finset.range P,
                  Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                    (j + d.1 + (pathSum w p).1, l + d.2 + (pathSum w p).2)) *
                F.Q half W κ (j + d.1 + (pathSum w P).1) (l + d.2 + (pathSum w P).2)) :=
            mul_le_mul_right hIH _
        _ = _ := by
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun w => ?_
            rw [← mul_assoc, mul_comm (ENNReal.ofReal (Real.exp _)) (F.hold.iid P w),
              mul_assoc]
            refine congrArg _ ?_
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc,
              ← Real.exp_add]
            have hend : pathSum (Fin.cons d w) (P + 1) = d + pathSum w P :=
              pathSum_cons d w P
            have hexp : -κ * Set.indicator W 1 (j, l)
                  + -κ * ∑ p ∈ Finset.range P,
                    Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                      (j + d.1 + (pathSum w p).1, l + d.2 + (pathSum w p).2)
                = -κ * ∑ p ∈ Finset.range (P + 1),
                    Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                      (j + (pathSum (Fin.cons d w) p).1,
                        l + (pathSum (Fin.cons d w) p).2) := by
              rw [Finset.sum_range_succ']
              have h0 : Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) (1 : ℕ × ℤ → ℝ)
                  (j + (pathSum (Fin.cons d w) 0).1, l + (pathSum (Fin.cons d w) 0).2)
                  = Set.indicator W 1 (j, l) := by
                rw [pathSum_zero]
                simp only [Prod.fst_zero, Prod.snd_zero, add_zero]
                by_cases hW : (j, l) ∈ W
                · have hmem : (j, l) ∈ W ∩ {q : ℕ × ℤ | q.1 ≤ half} :=
                    ⟨hW, by simpa using hin⟩
                  rw [Set.indicator_of_mem hW, Set.indicator_of_mem hmem]
                · rw [Set.indicator_of_notMem hW,
                    Set.indicator_of_notMem (fun hmem => hW hmem.1)]
              have hstep : ∀ p ∈ Finset.range P,
                  Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) (1 : ℕ × ℤ → ℝ)
                    (j + (pathSum (Fin.cons d w) (p + 1)).1,
                      l + (pathSum (Fin.cons d w) (p + 1)).2)
                  = Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                    (j + d.1 + (pathSum w p).1, l + d.2 + (pathSum w p).2) := by
                intro p _
                rw [pathSum_cons]
                congr 2
                · show j + (d.1 + (pathSum w p).1) = j + d.1 + (pathSum w p).1
                  omega
                · show l + (d.2 + (pathSum w p).2) = l + d.2 + (pathSum w p).2
                  ring
              rw [Finset.sum_congr rfl hstep, h0]
              ring
            rw [hexp, hend]
            congr 3
            · show j + d.1 + (pathSum w P).1 = j + (d.1 + (pathSum w P).1)
              omega
            · show l + d.2 + (pathSum w P).2 = l + (d.2 + (pathSum w P).2)
              ring

/-- **The main iteration (7.53)** (`Q_le_damped_iter` of tao-collatz): `P` steps after the first passage (budget `s`). -/
theorem Q_le_damped_iter (half : ℕ) (W : Set (ℕ × ℤ)) (κ : ℝ) (hκ : 0 ≤ κ)
    (s P : ℕ) (j : ℕ) (l : ℤ) :
    ENNReal.ofReal (F.Q half W κ j l)
      ≤ ∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
          ENNReal.ofReal (
            Real.exp (-κ * ∑ p ∈ Finset.range P,
              Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                (j + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) *
            F.Q half W κ (j + e.1 + (pathSum v P).1) (l + e.2 + (pathSum v P).2)) := by
  refine le_trans (F.Q_le_fpDist_expect half W κ hκ s j l) ?_
  refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
  exact F.Q_le_walk_damped half W κ hκ P (j + e.1) (l + e.2)

end Family

end GGMCollatz
