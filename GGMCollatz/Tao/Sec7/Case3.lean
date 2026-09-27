import GGMCollatz.Tao.Sec7.ColTail
import GGMCollatz.Tao.Sec7.FewWhite

/-!
# GGM §7: Case 3 of Proposition 7.8 (deep triangles, (7.53)–(7.67) of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/Case3.lean`
(the assembly of `damping_column_mass_le_at`, `damped_iter_expectation_le_at`, `Q_black_edge_case3_at`);
generalized to the GGM family (p, q, r). Modified. The threshold for bad columns is `colFrac · m` instead of `0.9m` (`ColTail.lean`).

* `damping_column_mass_le` (the column split (7.54)): from `col_tail_mass_le` (`ColTail.lean`) and
  `damping_expectation_le` (`FewWhite.lean`, with `δ = (1 - colFrac)^A / 2`).
* `damped_iter_expectation_le`: peel off the endpoint value with `Q_le_Qm`, then the above.
* `Q_black_edge_case3`: from `Q_le_damped_iter` (`Walk.lean`) and the above.
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- **The column split (7.54)** (`damping_column_mass_le` of tao-collatz): the mean of the product of the decay and the
endpoint depth weight `max(half - j_end, 1)^{-A}` is `≤ m^{-A}`. -/
theorem damping_column_mass_le :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ A : ℝ, 0 < A →
      ∃ Cthr P : ℕ, ∀ (half : ℕ) (T : F.TriFam half (F.sep ε)) (m : ℕ), Cthr ≤ m → m ≤ half →
        ∀ l : ℤ, 1 ≤ half - m → ∀ t ∈ T.T, (half - m - 1, l) ∈ F.triangle t.1 t.2.1 t.2.2 →
        ∀ s : ℕ, (s : ℤ) = t.2.1 - l → (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
        (s : ℝ) * Real.log F.p ≤ ((m : ℝ) + 2) * Real.log ((F.q : ℝ) ^ 2) →
        (∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
          ENNReal.ofReal (
            Real.exp (-(ε ^ 3) * ∑ p ∈ Finset.range P,
              Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) *
            ((max (half - (half - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A)))
          ≤ ENNReal.ofReal ((m : ℝ) ^ (-A)) := by
  obtain ⟨ε₀, hε₀, hdampAll⟩ := F.damping_expectation_le
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεle A hA
  set c₀ : ℝ := 1 - F.colFrac with hc₀
  have hc₀pos : 0 < c₀ := by have := F.colFrac_lt_one; rw [hc₀]; linarith
  have hc₀le : c₀ ≤ 1 := by have := F.colFrac_pos; rw [hc₀]; linarith
  obtain ⟨P, C1, hdamp⟩ := hdampAll ε hε hεle (c₀ ^ A / 2) (by positivity)
  obtain ⟨C2, htail⟩ := F.col_tail_mass_le A hA P
  refine ⟨max (max C1 C2) 1, P, ?_⟩
  intro half T m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hmC1 : C1 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hmC2 : C2 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hm0R : (0 : ℝ) ≤ (m : ℝ) ^ (-A) := Real.rpow_nonneg hmR.le _
  set Wc : ℝ := c₀ ^ (-A) * (m : ℝ) ^ (-A) with hWcdef
  have hWc0 : 0 ≤ Wc := by positivity
  have hconst : Wc * (c₀ ^ A / 2) = (m : ℝ) ^ (-A) / 2 := by
    rw [hWcdef]
    have h1 : c₀ ^ (-A) * c₀ ^ A = 1 := by
      rw [← Real.rpow_add hc₀pos, neg_add_cancel, Real.rpow_zero]
    calc c₀ ^ (-A) * (m : ℝ) ^ (-A) * (c₀ ^ A / 2)
        = (c₀ ^ (-A) * c₀ ^ A) * (m : ℝ) ^ (-A) / 2 := by ring
      _ = (m : ℝ) ^ (-A) / 2 := by rw [h1, one_mul]
  -- pointwise split
  have hpoint : ∀ (e : ℕ × ℤ) (v : Fin P → ℕ × ℤ),
      ENNReal.ofReal (Real.exp (-(ε ^ 3) * ∑ p ∈ Finset.range P,
          Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
            (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) *
        ((max (half - (half - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A))
      ≤ ENNReal.ofReal (if F.colFrac * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
            then (1 : ℝ) else 0)
        + ENNReal.ofReal Wc *
          ENNReal.ofReal (Real.exp (-(ε ^ 3) * ∑ p ∈ Finset.range P,
            Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
              (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))) := by
    intro e v
    set EXPV : ℝ := Real.exp (-(ε ^ 3) * ∑ p ∈ Finset.range P,
        Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
          (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) with hEXVdef
    have hEXPV0 : (0 : ℝ) ≤ EXPV := (Real.exp_pos _).le
    have hEXPV1 : EXPV ≤ 1 := by
      rw [hEXVdef, Real.exp_le_one_iff]
      have hsum0 : (0 : ℝ) ≤ ∑ p ∈ Finset.range P,
          Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
            (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) :=
        Finset.sum_nonneg fun p _ => Set.indicator_nonneg (fun _ _ => by norm_num) _
      have hε30 : (0 : ℝ) ≤ ε ^ 3 := by positivity
      nlinarith [hsum0, hε30]
    set WT : ℝ := ((max (half - (half - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A)
      with hWTdef
    have hWT0 : (0 : ℝ) ≤ WT := by rw [hWTdef]; exact Real.rpow_nonneg (by positivity) _
    have hind0 : (0 : ℝ) ≤ (if F.colFrac * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
        then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    rw [← ENNReal.ofReal_mul hWc0, ← ENNReal.ofReal_add hind0 (mul_nonneg hWc0 hEXPV0)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hcol : F.colFrac * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
    · rw [if_pos hcol]
      have hWT1 : WT ≤ 1 := by
        rw [hWTdef]
        refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
        have : (1 : ℕ) ≤ max (half - (half - m + e.1 + (pathSum v P).1)) 1 := le_max_right _ _
        exact_mod_cast this
      have hmul : EXPV * WT ≤ 1 := by
        have := mul_le_mul hEXPV1 hWT1 hWT0 (by norm_num : (0 : ℝ) ≤ 1)
        linarith
      nlinarith [hmul, mul_nonneg hWc0 hEXPV0]
    · rw [if_neg hcol]
      have hlt : ((e.1 + (pathSum v P).1 : ℕ) : ℝ) < F.colFrac * (m : ℝ) := not_le.mp hcol
      have hcm : F.colFrac * (m : ℝ) ≤ (m : ℝ) := by
        have := F.colFrac_lt_one
        nlinarith
      have hadvm : e.1 + (pathSum v P).1 < m := by
        have : ((e.1 + (pathSum v P).1 : ℕ) : ℝ) < (m : ℝ) := lt_of_lt_of_le hlt hcm
        exact_mod_cast this
      have hdcol_eq : half - (half - m + e.1 + (pathSum v P).1)
          = m - (e.1 + (pathSum v P).1) := by omega
      have hcast : ((half - (half - m + e.1 + (pathSum v P).1) : ℕ) : ℝ)
          = (m : ℝ) - ((e.1 + (pathSum v P).1 : ℕ) : ℝ) := by
        rw [hdcol_eq, Nat.cast_sub (le_of_lt hadvm)]
      have hmaxge : c₀ * (m : ℝ)
          ≤ ((max (half - (half - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) := by
        have hbase : c₀ * (m : ℝ)
            ≤ ((half - (half - m + e.1 + (pathSum v P).1) : ℕ) : ℝ) := by
          rw [hcast, hc₀]; linarith
        have hle : ((half - (half - m + e.1 + (pathSum v P).1) : ℕ) : ℝ)
            ≤ ((max (half - (half - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_max_left _ _
        linarith
      have hcm_pos : (0 : ℝ) < c₀ * (m : ℝ) := by positivity
      have hconstEq : (c₀ * (m : ℝ)) ^ (-A) = Wc := by
        rw [Real.mul_rpow hc₀pos.le hmR.le]
      have hWTbound : WT ≤ Wc := by
        rw [hWTdef, ← hconstEq]
        exact Real.rpow_le_rpow_of_nonpos hcm_pos hmaxge (by linarith)
      calc EXPV * WT ≤ EXPV * Wc := mul_le_mul_of_nonneg_left hWTbound hEXPV0
        _ = 0 + Wc * EXPV := by ring
  refine le_trans (ENNReal.tsum_le_tsum fun e => mul_le_mul_right
    (ENNReal.tsum_le_tsum fun v => mul_le_mul_right (hpoint e v) _) _) ?_
  have heq :
      (∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
        (ENNReal.ofReal (if F.colFrac * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
              then (1 : ℝ) else 0)
          + ENNReal.ofReal Wc *
            ENNReal.ofReal (Real.exp (-(ε ^ 3) * ∑ p ∈ Finset.range P,
              Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)))))
      = (∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
          ENNReal.ofReal (if F.colFrac * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        + ENNReal.ofReal Wc *
          ∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
            ENNReal.ofReal (Real.exp (-(ε ^ 3) * ∑ p ∈ Finset.range P,
              Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))) := by
    have inner : ∀ e : ℕ × ℤ,
        (∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
          (ENNReal.ofReal (if F.colFrac * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
                then (1 : ℝ) else 0)
            + ENNReal.ofReal Wc *
              ENNReal.ofReal (Real.exp (-(ε ^ 3) * ∑ p ∈ Finset.range P,
                Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                  (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)))))
        = (∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
            ENNReal.ofReal (if F.colFrac * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
              then (1 : ℝ) else 0))
          + ENNReal.ofReal Wc *
            ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
              ENNReal.ofReal (Real.exp (-(ε ^ 3) * ∑ p ∈ Finset.range P,
                Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                  (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))) := by
      intro e
      rw [tsum_congr fun v => mul_add (F.hold.iid P v) _ _, ENNReal.tsum_add]
      congr 1
      rw [tsum_congr fun v => mul_left_comm (F.hold.iid P v) (ENNReal.ofReal Wc) _,
        ENNReal.tsum_mul_left]
    rw [tsum_congr fun e => by rw [inner e, mul_add (F.fpDist s e)], ENNReal.tsum_add]
    congr 1
    rw [tsum_congr fun e => mul_left_comm (F.fpDist s e) (ENNReal.ofReal Wc) _,
      ENNReal.tsum_mul_left]
  rw [heq]
  have hb1 := htail m hmC2 s hs2
  have hb2 := hdamp half T m hmC1 hmn l hpos t ht hmem s hs hs1 hs2
  calc _ ≤ ENNReal.ofReal ((m : ℝ) ^ (-A) / 2) + ENNReal.ofReal Wc * ENNReal.ofReal (c₀ ^ A / 2) :=
        add_le_add hb1 (mul_le_mul_right hb2 _)
    _ = ENNReal.ofReal ((m : ℝ) ^ (-A) / 2) + ENNReal.ofReal ((m : ℝ) ^ (-A) / 2) := by
        rw [← ENNReal.ofReal_mul hWc0, hconst]
    _ = ENNReal.ofReal ((m : ℝ) ^ (-A)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **The bound (7.54)–(7.67)** (`damped_iter_expectation_le` of tao-collatz). -/
theorem damped_iter_expectation_le :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ A : ℝ, 0 < A →
      ∃ Cthr P : ℕ, ∀ (half : ℕ) (T : F.TriFam half (F.sep ε)) (m : ℕ), Cthr ≤ m → m ≤ half →
        ∀ l : ℤ, 1 ≤ half - m → ∀ t ∈ T.T, (half - m - 1, l) ∈ F.triangle t.1 t.2.1 t.2.2 →
        ∀ s : ℕ, (s : ℤ) = t.2.1 - l → (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
        (s : ℝ) * Real.log F.p ≤ ((m : ℝ) + 2) * Real.log ((F.q : ℝ) ^ 2) →
        (∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
          ENNReal.ofReal (
            Real.exp (-(ε ^ 3) * ∑ p ∈ Finset.range P,
              Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) *
            F.Q half T.W (ε ^ 3)
              (half - m + e.1 + (pathSum v P).1) (l + e.2 + (pathSum v P).2)))
          ≤ ENNReal.ofReal ((m : ℝ) ^ (-A) * F.Qm half T.W (ε ^ 3) A (m - 1)) := by
  obtain ⟨ε₀, hε₀, hmassAll⟩ := F.damping_column_mass_le
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεle A hA
  obtain ⟨Cthr, P, hmass⟩ := hmassAll ε hε hεle A hA
  refine ⟨max Cthr 1, P, ?_⟩
  intro half T m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hmC : Cthr ≤ m := le_trans (le_max_left _ _) hm
  have hκ0 : (0 : ℝ) ≤ ε ^ 3 := by positivity
  set QM : ℝ := F.Qm half T.W (ε ^ 3) A (m - 1) with hQMdef
  have hQM0 : (0 : ℝ) ≤ QM := F.Qm_nonneg _ _ _ _ _
  set D : (ℕ × ℤ) → (Fin P → ℕ × ℤ) → ℝ := fun e v =>
    Real.exp (-(ε ^ 3) * ∑ p ∈ Finset.range P,
      Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
        (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) with hDdef
  set WTf : (ℕ × ℤ) → (Fin P → ℕ × ℤ) → ℝ := fun e v =>
    ((max (half - (half - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A) with hWTfdef
  have step1 :
      (∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
          ENNReal.ofReal (D e v *
            F.Q half T.W (ε ^ 3)
              (half - m + e.1 + (pathSum v P).1) (l + e.2 + (pathSum v P).2)))
        ≤ ∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
            (ENNReal.ofReal QM * ENNReal.ofReal (D e v * WTf e v)) := by
    refine ENNReal.tsum_le_tsum fun e => ?_
    by_cases he0 : F.fpDist s e = 0
    · simp [he0]
    refine mul_le_mul_right ?_ _
    refine ENNReal.tsum_le_tsum fun v => mul_le_mul_right ?_ _
    rw [← ENNReal.ofReal_mul hQM0]
    refine ENNReal.ofReal_le_ofReal ?_
    have he1 : 1 ≤ e.1 := F.fpDist_support_fst_pos s e (by rwa [PMF.mem_support_iff])
    have h1 : 1 ≤ half - m + e.1 + (pathSum v P).1 := by omega
    have h2 : half - (m - 1) ≤ half - m + e.1 + (pathSum v P).1 := by omega
    have hQle := F.Q_le_Qm half T.W hκ0 A hA.le (m - 1)
      (l := l + e.2 + (pathSum v P).2) h1 h2
    have hD0 : 0 ≤ D e v := (Real.exp_pos _).le
    calc D e v * F.Q half T.W (ε ^ 3)
          (half - m + e.1 + (pathSum v P).1) (l + e.2 + (pathSum v P).2)
        ≤ D e v * (WTf e v * QM) := mul_le_mul_of_nonneg_left hQle hD0
      _ = QM * (D e v * WTf e v) := by ring
  have outer_eq :
      (∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
        (ENNReal.ofReal QM * ENNReal.ofReal (D e v * WTf e v)))
        = ENNReal.ofReal QM *
          ∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
            ENNReal.ofReal (D e v * WTf e v) := by
    have inner_eq : ∀ e : ℕ × ℤ,
        (∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
          (ENNReal.ofReal QM * ENNReal.ofReal (D e v * WTf e v)))
          = ENNReal.ofReal QM * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
              ENNReal.ofReal (D e v * WTf e v) := by
      intro e
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr fun v => by rw [mul_left_comm]
    simp only [inner_eq]
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun e => by rw [mul_left_comm]
  refine le_trans step1 ?_
  rw [outer_eq]
  calc ENNReal.ofReal QM *
        ∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
          ENNReal.ofReal (D e v * WTf e v)
      ≤ ENNReal.ofReal QM * ENNReal.ofReal ((m : ℝ) ^ (-A)) :=
        mul_le_mul_right (hmass half T m hmC hmn l hpos t ht hmem s hs hs1 hs2) _
    _ = ENNReal.ofReal ((m : ℝ) ^ (-A) * QM) := by
        rw [← ENNReal.ofReal_mul hQM0]; congr 1; ring

/-- **Case 3** (`Q_black_edge_case3` of tao-collatz): at the starting point of a black edge of a deep triangle, `Q ≤ m^{-A} Q_{m-1}`. -/
theorem Q_black_edge_case3 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ A : ℝ, 0 < A →
      ∃ Cthr : ℕ, ∀ (half : ℕ) (T : F.TriFam half (F.sep ε)) (m : ℕ), Cthr ≤ m → m ≤ half →
        ∀ l : ℤ, 1 ≤ half - m → ∀ t ∈ T.T, (half - m - 1, l) ∈ F.triangle t.1 t.2.1 t.2.2 →
        ∀ s : ℕ, (s : ℤ) = t.2.1 - l → (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
        (s : ℝ) * Real.log F.p ≤ ((m : ℝ) + 2) * Real.log ((F.q : ℝ) ^ 2) →
        F.Q half T.W (ε ^ 3) (half - m) l
          ≤ (m : ℝ) ^ (-A) * F.Qm half T.W (ε ^ 3) A (m - 1) := by
  obtain ⟨ε₀, hε₀, hD⟩ := F.damped_iter_expectation_le
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεle A hA
  obtain ⟨Cthr, P, hbound⟩ := hD ε hε hεle A hA
  refine ⟨Cthr, ?_⟩
  intro half T m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hκ0 : (0 : ℝ) ≤ ε ^ 3 := by positivity
  have hentry := F.Q_le_damped_iter half T.W (ε ^ 3) hκ0 s P (half - m) l
  have hexp := hbound half T m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hchain : ENNReal.ofReal (F.Q half T.W (ε ^ 3) (half - m) l)
      ≤ ENNReal.ofReal ((m : ℝ) ^ (-A) * F.Qm half T.W (ε ^ 3) A (m - 1)) :=
    le_trans hentry hexp
  have hRHSnn : (0 : ℝ) ≤ (m : ℝ) ^ (-A) * F.Qm half T.W (ε ^ 3) A (m - 1) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _) (F.Qm_nonneg _ _ _ _ _)
  exact (ENNReal.ofReal_le_ofReal_iff hRHSnn).mp hchain

end Family

end GGMCollatz
