import GGMCollatz.Tao.Sec7.BlackEdge
import GGMCollatz.Tao.Sec7.Expect

/-!
# Rewriting into the renewal process of GGM §6, and the bound for the renewal process avoiding triangles (the bridge of §7.3 of tao-collatz, Proposition 7.3)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/Bridge.lean`;
generalized to the GGM family (p, q, r). Modified. The form of (ineq:badset) of GGM §6 Step 1 and of the conclusion of Theorem 1.9.

```
E_{b iid Pascal(μ)} exp(-κ #{j : b_j = 3, (j, b_{[1,j]}) ∈ W})
  = Rcol 0 0                 (column-by-column recursion, D6)
  = Σ_d hold(d) Q(d)         (self-similarity of one renewal step)
  ≪_A half^{-A}              ((7.37) and `hold_weight_expect`)
```

* `Rcol`: the column-by-column recursion. `bridge_vector_gen`: the expectation over an i.i.d. vector equals `Rcol`.
* `hold_tsum_step`: one-column self-similarity of `ℋ` (`(1,3)` with probability `P(Pascal = 3)`; otherwise add a column with `b ≠ 3` and restart).
* `bridge_renewal`: `Rcol = Σ_d hold(d) Q((j,l)+d)`.
* `renewal_white`: **bound for the renewal process avoiding triangles** (Proposition 7.3 of tao-collatz; the conclusion of GGM Theorem 1.9
  specialized to `ℋ`).
-/

open scoped ENNReal

namespace GGMCollatz

/-- Peeling off the head: `pre (cons a w) (m+1) = a + pre w m`. -/
theorem pre_cons {n : ℕ} (a : ℕ) (w : Fin n → ℕ) (m : ℕ) :
    pre (Fin.cons a w : Fin (n + 1) → ℕ) (m + 1) = a + pre w m := by
  rw [pre_cons_head]
  simp

namespace Family

variable (F : Family)

open Classical in
/-- **Column-by-column recursion** (`Rcol` of tao-collatz): from column `j` and forward sum `l`, draw the next column `b ~ Pascal(μ)`;
if the renewal point (`b = 3`) lies in `W`, apply the decay `exp(-κ)`. Outside the strip it is `1`. -/
noncomputable def Rcol (half : ℕ) (W : Set (ℕ × ℤ)) (κ : ℝ) : ℕ → ℤ → ℝ
  | j, l =>
    if half ≤ j then 1
    else ∑' b : ℕ,
      (pascalP F.p b).toReal
        * (if b = 3 ∧ ((j + 1 : ℕ), l + (b : ℤ)) ∈ W then Real.exp (-κ) else 1)
        * Rcol half W κ (j + 1) (l + b)
  termination_by j _ => half - j
  decreasing_by omega

open Classical in
/-- **Bridge, vector side** (`bridge_vector_gen` of tao-collatz). -/
theorem bridge_vector_gen (W : Set (ℕ × ℤ)) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∀ (m half j : ℕ) (l : ℤ), half - j = m →
      (PMF.iid (pascalP F.p) m).expect (fun v =>
          Real.exp (-κ *
            ((Finset.univ.filter fun i : Fin m =>
              v i = 3 ∧ ((j + (i : ℕ) + 1 : ℕ), l + (pre v ((i : ℕ) + 1) : ℤ)) ∈ W).card
              : ℝ)))
        = F.Rcol half W κ j l := by
  intro m
  induction m with
  | zero =>
    intro half j l hm
    rw [PMF.expect_iid_zero, Rcol, if_pos (by omega : half ≤ j)]
    simp
  | succ m IH =>
    intro half j l hm
    rw [PMF.expect_iid_succ (pascalP F.p) m _ (fun v => (Real.exp_pos _).le)
      (fun v => by
        rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
        exact mul_nonneg hκ (Nat.cast_nonneg _))]
    have hinner : ∀ a : ℕ,
        ((PMF.iid (pascalP F.p) m).expect fun w =>
          Real.exp (-κ *
            ((Finset.univ.filter fun i : Fin (m + 1) =>
              (Fin.cons a w : Fin (m + 1) → ℕ) i = 3
                ∧ ((j + (i : ℕ) + 1 : ℕ),
                    l + (pre (Fin.cons a w) ((i : ℕ) + 1) : ℤ)) ∈ W).card : ℝ)))
        = (if a = 3 ∧ ((j + 1 : ℕ), l + (a : ℤ)) ∈ W
            then Real.exp (-κ) else 1)
          * F.Rcol half W κ (j + 1) (l + (a : ℤ)) := by
      intro a
      rw [← IH half (j + 1) (l + (a : ℤ)) (by omega)]
      have hcount : ∀ w : Fin m → ℕ,
          ((Finset.univ.filter fun i : Fin (m + 1) =>
            (Fin.cons a w : Fin (m + 1) → ℕ) i = 3
              ∧ ((j + (i : ℕ) + 1 : ℕ),
                  l + (pre (Fin.cons a w) ((i : ℕ) + 1) : ℤ)) ∈ W).card
          = (if a = 3 ∧ ((j + 1 : ℕ), l + (a : ℤ)) ∈ W then 1 else 0)
            + (Finset.univ.filter fun i : Fin m =>
                w i = 3 ∧ ((j + 1 + (i : ℕ) + 1 : ℕ),
                  (l + (a : ℤ)) + (pre w ((i : ℕ) + 1) : ℤ)) ∈ W).card) := by
        intro w
        rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        have h2 : (j + ((i.succ : Fin (m + 1)) : ℕ) + 1 : ℕ)
            = j + 1 + (i : ℕ) + 1 := by
          rw [Fin.val_succ]; omega
        have h3 : l + (pre (Fin.cons a w) (((i.succ : Fin (m + 1)) : ℕ) + 1) : ℤ)
            = (l + (a : ℤ)) + (pre w ((i : ℕ) + 1) : ℤ) := by
          rw [Fin.val_succ, pre_cons]
          push_cast
          ring
        have hiff : ((Fin.cons a w : Fin (m + 1) → ℕ) i.succ = 3
            ∧ ((j + ((i.succ : Fin (m + 1)) : ℕ) + 1 : ℕ),
                l + (pre (Fin.cons a w) (((i.succ : Fin (m + 1)) : ℕ) + 1) : ℤ)) ∈ W)
            ↔ (w i = 3 ∧ ((j + 1 + (i : ℕ) + 1 : ℕ),
                (l + (a : ℤ)) + (pre w ((i : ℕ) + 1) : ℤ)) ∈ W) := by
          rw [show ((Fin.cons a w : Fin (m + 1) → ℕ) i.succ) = w i
            from Fin.cons_succ (α := fun _ => ℕ) a w i, h2, h3]
        exact if_congr hiff rfl rfl
      unfold PMF.expect
      dsimp only
      rw [← tsum_mul_left]
      refine tsum_congr fun w => ?_
      rw [hcount w]
      push_cast
      rw [mul_add, Real.exp_add]
      have hhead : Real.exp (-κ *
            ((if a = 3 ∧ ((j + 1 : ℕ), l + (a : ℤ)) ∈ W then (1 : ℝ) else 0)))
          = (if a = 3 ∧ ((j + 1 : ℕ), l + (a : ℤ)) ∈ W
              then Real.exp (-κ) else 1) := by
        split_ifs
        · rw [mul_one]
        · rw [mul_zero, Real.exp_zero]
      rw [hhead]
      ring
    rw [tsum_congr fun a => by rw [hinner a]]
    rw [Rcol, if_neg (by omega : ¬ half ≤ j)]
    exact tsum_congr fun a => (mul_assoc _ _ _).symm

/-! ### One-column self-similarity of `ℋ` -/

/-- Expanding the `hold`-expectation along its `bind`/`map` structure. -/
theorem hold_tsum_expand (G : ℕ × ℤ → ℝ≥0∞) :
    ∑' d : ℕ × ℤ, F.hold d * G d
      = ∑' k : ℕ, holdGeom F.p k * ∑' v : Fin (k - 1) → ℕ,
          ((pascalNe3P F.p).iid (k - 1)) v * G (k, (3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ)) := by
  rw [hold, PMF.tsum_bind_mul]
  exact tsum_congr fun k => by rw [PMF.tsum_map_mul]

/-- `P(Pascal = 3) < 1` (from `P(Pascal = 2) > 0`). -/
theorem pascalP_three_lt_one : pascalP F.p 3 < 1 := by
  have h2 := pascalP_two_pos F.two_le_p
  have hsum : pascalP F.p 2 + pascalP F.p 3 ≤ 1 := by
    have h := ENNReal.sum_le_tsum (f := pascalP F.p) ({2, 3} : Finset ℕ)
    rw [Finset.sum_pair (by norm_num), PMF.tsum_coe] at h
    exact h
  have hne : pascalP F.p 3 ≠ ⊤ := PMF.apply_ne_top _ _
  by_contra hge
  push Not at hge
  have h1 : pascalP F.p 3 = 1 := le_antisymm (PMF.coe_le_one _ _) hge
  rw [h1] at hsum
  have : pascalP F.p 2 = 0 := by
    have h' : pascalP F.p 2 + 1 ≤ 0 + 1 := by simpa using hsum
    exact le_antisymm ((ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mp h') zero_le
  exact h2.ne' this

theorem one_sub_pascalP_three_ne_zero : 1 - pascalP F.p 3 ≠ 0 := by
  have := F.pascalP_three_lt_one
  exact (tsub_pos_of_lt this).ne'

/-- **One-column self-similarity of `ℋ`** (`hold_tsum_step` of tao-collatz, (7.29)). -/
theorem hold_tsum_step (g : ℕ × ℤ → ℝ≥0∞) :
    ∑' d : ℕ × ℤ, F.hold d * g d
      = pascalP F.p 3 * g (1, 3)
        + ∑' b : ℕ, (if b = 3 then 0 else pascalP F.p b)
            * ∑' d : ℕ × ℤ, F.hold d * g (d.1 + 1, d.2 + b) := by
  classical
  have hs := holdGeom_prob F.two_le_p
  set s := pascalP F.p 3 with hsdef
  have hgq1 : holdGeom F.p 1 = s := by
    unfold holdGeom
    rw [geomS_apply hs, if_neg (by norm_num)]
    simp
  have hgqs : ∀ k : ℕ, holdGeom F.p (k + 2) = (1 - s) * holdGeom F.p (k + 1) := by
    intro k
    unfold holdGeom
    rw [geomS_apply hs, geomS_apply hs, if_neg (by omega), if_neg (by omega),
      show k + 2 - 1 = (k + 1 - 1) + 1 from by omega, pow_succ]
    ring
  have hpas : ∀ b : ℕ, (if b = 3 then (0 : ℝ≥0∞) else pascalP F.p b)
      = (1 - s) * pascalNe3P F.p b := by
    intro b
    rw [pascalNe3P_apply F.two_le_p]
    by_cases hb3 : b = 3
    · simp [hb3]
    · rw [if_neg hb3, if_neg hb3, ← mul_assoc,
        ENNReal.mul_inv_cancel F.one_sub_pascalP_three_ne_zero
          (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self), one_mul]
  have hL1 : ∑' d : ℕ × ℤ, F.hold d * g d
      = s * g (1, 3)
        + ∑' k : ℕ, holdGeom F.p (k + 2) * ∑' v : Fin (k + 1) → ℕ,
            ((pascalNe3P F.p).iid (k + 1)) v * g (k + 2, (3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ)) := by
    rw [F.hold_tsum_expand g, tsum_eq_zero_add' ENNReal.summable,
      F.holdGeom_zero, zero_mul, zero_add,
      tsum_eq_zero_add' ENNReal.summable]
    congr 1
    · rw [hgq1]
      congr 1
      exact (PMF.tsum_iid_zero_mul (pascalNe3P F.p)
        (fun v => g (1, (3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ)))).trans (by simp)
  have hR : ∀ b : ℕ, ∑' d : ℕ × ℤ, F.hold d * g (d.1 + 1, d.2 + (b : ℤ))
      = ∑' k : ℕ, holdGeom F.p (k + 1) * ∑' w : Fin k → ℕ,
          ((pascalNe3P F.p).iid k) w
            * g (k + 1 + 1, (3 : ℤ) + (∑ i, ((w i : ℕ) : ℤ)) + (b : ℤ)) := by
    intro b
    rw [F.hold_tsum_expand fun d => g (d.1 + 1, d.2 + (b : ℤ)),
      tsum_eq_zero_add' ENNReal.summable, F.holdGeom_zero, zero_mul, zero_add]
    rfl
  have hL2 : ∑' k : ℕ, holdGeom F.p (k + 2) * ∑' v : Fin (k + 1) → ℕ,
        ((pascalNe3P F.p).iid (k + 1)) v * g (k + 2, (3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ))
      = ∑' b : ℕ, (1 - s) * pascalNe3P F.p b
          * ∑' k : ℕ, holdGeom F.p (k + 1) * ∑' w : Fin k → ℕ,
              ((pascalNe3P F.p).iid k) w
                * g (k + 1 + 1, (3 : ℤ) + (∑ i, ((w i : ℕ) : ℤ)) + (b : ℤ)) := by
    have hpeel : ∀ k : ℕ, ∑' v : Fin (k + 1) → ℕ,
          ((pascalNe3P F.p).iid (k + 1)) v * g (k + 2, (3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ))
        = ∑' a : ℕ, pascalNe3P F.p a * ∑' w : Fin k → ℕ,
            ((pascalNe3P F.p).iid k) w
              * g (k + 1 + 1, (3 : ℤ) + (∑ i, ((w i : ℕ) : ℤ)) + (a : ℤ)) := by
      intro k
      rw [PMF.tsum_iid_succ_mul (pascalNe3P F.p) k
        (fun v => g (k + 2, (3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ)))]
      refine tsum_congr fun a => ?_
      congr 1
      refine tsum_congr fun w => ?_
      congr 1
      rw [show ((3 : ℤ) + ∑ i : Fin (k + 1), (((Fin.cons a w : Fin (k + 1) → ℕ) i : ℕ) : ℤ))
          = (3 : ℤ) + (∑ i, ((w i : ℕ) : ℤ)) + (a : ℤ) from by
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        ring]
    calc ∑' k : ℕ, holdGeom F.p (k + 2) * ∑' v : Fin (k + 1) → ℕ,
          ((pascalNe3P F.p).iid (k + 1)) v * g (k + 2, (3 : ℤ) + ∑ i, ((v i : ℕ) : ℤ))
        = ∑' k : ℕ, ∑' a : ℕ, (1 - s) * pascalNe3P F.p a
            * (holdGeom F.p (k + 1) * ∑' w : Fin k → ℕ,
                ((pascalNe3P F.p).iid k) w
                  * g (k + 1 + 1, (3 : ℤ) + (∑ i, ((w i : ℕ) : ℤ)) + (a : ℤ))) := by
          refine tsum_congr fun k => ?_
          rw [hpeel k, hgqs k, ← ENNReal.tsum_mul_left]
          exact tsum_congr fun a => by ring
      _ = ∑' a : ℕ, ∑' k : ℕ, (1 - s) * pascalNe3P F.p a
            * (holdGeom F.p (k + 1) * ∑' w : Fin k → ℕ,
                ((pascalNe3P F.p).iid k) w
                  * g (k + 1 + 1, (3 : ℤ) + (∑ i, ((w i : ℕ) : ℤ)) + (a : ℤ))) :=
          ENNReal.tsum_comm
      _ = ∑' a : ℕ, (1 - s) * pascalNe3P F.p a
            * ∑' k : ℕ, holdGeom F.p (k + 1) * ∑' w : Fin k → ℕ,
                ((pascalNe3P F.p).iid k) w
                  * g (k + 1 + 1, (3 : ℤ) + (∑ i, ((w i : ℕ) : ℤ)) + (a : ℤ)) :=
          tsum_congr fun a => ENNReal.tsum_mul_left
  rw [hL1, hL2]
  congr 1
  exact tsum_congr fun b => by rw [hpas b, hR b]

/-- The real form of `hold_tsum_step` (`[0,1]`-valued observables). -/
theorem hold_tsum_step_real (f : ℕ × ℤ → ℝ) (hf0 : ∀ d, 0 ≤ f d) (hf1 : ∀ d, f d ≤ 1) :
    ∑' d : ℕ × ℤ, (F.hold d).toReal * f d
      = (pascalP F.p 3).toReal * f (1, 3)
        + ∑' b : ℕ, (if b = 3 then 0 else (pascalP F.p b).toReal)
            * ∑' d : ℕ × ℤ, (F.hold d).toReal * f (d.1 + 1, d.2 + b) := by
  classical
  have hstep := F.hold_tsum_step fun d => ENNReal.ofReal (f d)
  have hcv : ∀ G : ℕ × ℤ → ℕ × ℤ,
      (∑' d : ℕ × ℤ, F.hold d * ENNReal.ofReal (f (G d))).toReal
        = ∑' d : ℕ × ℤ, (F.hold d).toReal * f (G d) := by
    intro G
    rw [ENNReal.tsum_toReal_eq
      (fun d => ENNReal.mul_ne_top (F.hold.apply_ne_top d) ENNReal.ofReal_ne_top)]
    exact tsum_congr fun d => by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf0 _)]
  have hcv0 : (∑' d : ℕ × ℤ, F.hold d * ENNReal.ofReal (f d)).toReal
      = ∑' d : ℕ × ℤ, (F.hold d).toReal * f d := hcv id
  have hcvb : ∀ b : ℕ,
      (∑' d : ℕ × ℤ, F.hold d * ENNReal.ofReal (f (d.1 + 1, d.2 + (b : ℤ)))).toReal
        = ∑' d : ℕ × ℤ, (F.hold d).toReal * f (d.1 + 1, d.2 + (b : ℤ)) :=
    fun b => hcv fun d => (d.1 + 1, d.2 + (b : ℤ))
  have hTle : ∀ b : ℕ,
      ∑' d : ℕ × ℤ, F.hold d * ENNReal.ofReal (f (d.1 + 1, d.2 + (b : ℤ))) ≤ 1 := by
    intro b
    calc ∑' d : ℕ × ℤ, F.hold d * ENNReal.ofReal (f (d.1 + 1, d.2 + (b : ℤ)))
        ≤ ∑' d : ℕ × ℤ, F.hold d * 1 :=
          ENNReal.tsum_le_tsum fun d => mul_le_mul_right
            (ENNReal.ofReal_le_one.mpr (hf1 _)) _
      _ = 1 := by rw [tsum_congr fun d => mul_one (F.hold d), F.hold.tsum_coe]
  have hcb : ∀ b : ℕ, (if b = 3 then (0 : ℝ≥0∞) else pascalP F.p b) ≤ pascalP F.p b := by
    intro b; split_ifs <;> simp
  have htail_ne : (∑' b : ℕ, (if b = 3 then (0 : ℝ≥0∞) else pascalP F.p b)
      * ∑' d : ℕ × ℤ, F.hold d * ENNReal.ofReal (f (d.1 + 1, d.2 + (b : ℤ)))) ≠ ∞ := by
    refine ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ∞) ?_
    calc ∑' b : ℕ, (if b = 3 then (0 : ℝ≥0∞) else pascalP F.p b)
          * ∑' d : ℕ × ℤ, F.hold d * ENNReal.ofReal (f (d.1 + 1, d.2 + (b : ℤ)))
        ≤ ∑' b : ℕ, pascalP F.p b * 1 :=
          ENNReal.tsum_le_tsum fun b => mul_le_mul' (hcb b) (hTle b)
      _ = 1 := by rw [tsum_congr fun b => mul_one (pascalP F.p b), (pascalP F.p).tsum_coe]
  have h := congrArg ENNReal.toReal hstep
  rw [hcv0, ENNReal.toReal_add
      (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) ENNReal.ofReal_ne_top) htail_ne,
    ENNReal.toReal_mul, ENNReal.tsum_toReal_eq (fun b => ENNReal.mul_ne_top
      (ne_top_of_le_ne_top (PMF.apply_ne_top _ _) (hcb b))
      (ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ∞) (hTle b)))] at h
  rw [h, ENNReal.toReal_ofReal (hf0 _)]
  congr 1
  refine tsum_congr fun b => ?_
  rw [ENNReal.toReal_mul, hcvb b]
  congr 1
  split_ifs <;> simp

/-- **Bridge, renewal side** (`bridge_renewal` of tao-collatz, (7.27) ≡ (7.28)). -/
theorem bridge_renewal (half : ℕ) (W : Set (ℕ × ℤ)) (κ : ℝ) (hκ : 0 ≤ κ) (j : ℕ) (l : ℤ) :
    F.Rcol half W κ j l
      = ∑' d : ℕ × ℤ, (F.hold d).toReal * F.Q half W κ (j + d.1) (l + d.2) := by
  classical
  have hQ0 := F.Q_nonneg half W κ
  have hQ1 := F.Q_le_one half W κ hκ
  have hSterm : ∀ (j' : ℕ) (l' : ℤ) (d : ℕ × ℤ),
      (F.hold d).toReal * F.Q half W κ (j' + d.1) (l' + d.2) ≤ (F.hold d).toReal := by
    intro j' l' d
    calc (F.hold d).toReal * F.Q half W κ (j' + d.1) (l' + d.2)
        ≤ (F.hold d).toReal * 1 :=
          mul_le_mul_of_nonneg_left (hQ1 _ _) ENNReal.toReal_nonneg
      _ = (F.hold d).toReal := mul_one _
  have hSnn : ∀ (j' : ℕ) (l' : ℤ) (d : ℕ × ℤ),
      0 ≤ (F.hold d).toReal * F.Q half W κ (j' + d.1) (l' + d.2) :=
    fun j' l' d => mul_nonneg ENNReal.toReal_nonneg (hQ0 _ _)
  have hSsum : ∀ (j' : ℕ) (l' : ℤ),
      Summable fun d : ℕ × ℤ => (F.hold d).toReal * F.Q half W κ (j' + d.1) (l' + d.2) :=
    fun j' l' => Summable.of_nonneg_of_le (hSnn j' l') (hSterm j' l') F.hold_summable_toReal
  have hSle : ∀ (j' : ℕ) (l' : ℤ),
      ∑' d : ℕ × ℤ, (F.hold d).toReal * F.Q half W κ (j' + d.1) (l' + d.2) ≤ 1 :=
    fun j' l' => le_trans
      ((hSsum j' l').tsum_le_tsum (hSterm j' l') F.hold_summable_toReal)
      F.hold_tsum_toReal.le
  have hSnn' : ∀ (j' : ℕ) (l' : ℤ),
      0 ≤ ∑' d : ℕ × ℤ, (F.hold d).toReal * F.Q half W κ (j' + d.1) (l' + d.2) :=
    fun j' l' => tsum_nonneg (hSnn j' l')
  have hdamp01 : ∀ (P : Prop) [Decidable P],
      0 ≤ (if P then Real.exp (-κ) else 1)
        ∧ (if P then Real.exp (-κ) else 1) ≤ 1 := by
    intro P _
    constructor
    · split_ifs <;> [exact (Real.exp_pos _).le; exact zero_le_one]
    · split_ifs
      · rw [Real.exp_le_one_iff, neg_nonpos]; exact hκ
      · exact le_refl 1
  have key : ∀ n j l, half - j = n → F.Rcol half W κ j l
      = ∑' d : ℕ × ℤ, (F.hold d).toReal * F.Q half W κ (j + d.1) (l + d.2) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro j l hn
      rcases Nat.lt_or_ge j half with hj | hj
      · rw [Rcol, if_neg (by omega : ¬ half ≤ j)]
        have hIH : ∀ b : ℕ, F.Rcol half W κ (j + 1) (l + (b : ℤ))
            = ∑' d : ℕ × ℤ, (F.hold d).toReal
                * F.Q half W κ (j + 1 + d.1) (l + (b : ℤ) + d.2) :=
          fun b => IH (half - (j + 1)) (by omega) _ _ rfl
        have hfr := F.hold_tsum_step_real
          (fun d => F.Q half W κ (j + d.1) (l + d.2))
          (fun d => hQ0 _ _) (fun d => hQ1 _ _)
        rw [hfr]
        have hterm_eq : ∀ b : ℕ,
            (pascalP F.p b).toReal
              * (if b = 3 ∧ ((j + 1 : ℕ), l + (b : ℤ)) ∈ W
                  then Real.exp (-κ) else 1)
              * F.Rcol half W κ (j + 1) (l + (b : ℤ))
            = (pascalP F.p b).toReal
              * (if b = 3 ∧ ((j + 1 : ℕ), l + (b : ℤ)) ∈ W
                  then Real.exp (-κ) else 1)
              * ∑' d : ℕ × ℤ, (F.hold d).toReal
                  * F.Q half W κ (j + 1 + d.1) (l + (b : ℤ) + d.2) :=
          fun b => by rw [hIH b]
        rw [tsum_congr hterm_eq]
        have hsummable : Summable fun b : ℕ =>
            (pascalP F.p b).toReal
              * (if b = 3 ∧ ((j + 1 : ℕ), l + (b : ℤ)) ∈ W
                  then Real.exp (-κ) else 1)
              * ∑' d : ℕ × ℤ, (F.hold d).toReal
                  * F.Q half W κ (j + 1 + d.1) (l + (b : ℤ) + d.2) := by
          refine Summable.of_nonneg_of_le
            (fun b => mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (hdamp01 _).1)
              (hSnn' _ _))
            (fun b => ?_)
            (ENNReal.summable_toReal (pascalP F.p).tsum_coe_ne_top)
          calc (pascalP F.p b).toReal * _ * _
              ≤ (pascalP F.p b).toReal * 1 * 1 :=
                mul_le_mul (mul_le_mul_of_nonneg_left (hdamp01 _).2
                  ENNReal.toReal_nonneg) (hSle _ _) (hSnn' _ _)
                  (by positivity)
            _ = (pascalP F.p b).toReal := by ring
        rw [hsummable.tsum_eq_add_tsum_ite 3]
        congr 1
        · simp only [Nat.cast_ofNat]
          have hrec := F.Q_rec half W κ (j + 1) (l + 3) (by omega)
          by_cases hW : ((j + 1 : ℕ), l + (3 : ℤ)) ∈ W
          · rw [if_pos ⟨trivial, hW⟩, hrec, Set.indicator_of_mem hW,
              Pi.one_apply, mul_one, mul_assoc]
          · rw [if_neg (fun h => hW h.2), hrec, Set.indicator_of_notMem hW,
              mul_zero, Real.exp_zero, one_mul, mul_assoc, one_mul]
        · refine tsum_congr fun b => ?_
          by_cases hb3 : b = 3
          · rw [if_pos hb3, if_pos hb3, zero_mul]
          · rw [if_neg hb3, if_neg hb3,
              if_neg (fun h => hb3 h.1), mul_one]
            congr 1
            refine tsum_congr fun d => ?_
            congr 2
            · omega
            · ring
      · rw [Rcol, if_pos hj]
        symm
        calc ∑' d : ℕ × ℤ, (F.hold d).toReal * F.Q half W κ (j + d.1) (l + d.2)
            = ∑' d : ℕ × ℤ, (F.hold d).toReal := by
              refine tsum_congr fun d => ?_
              rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
              · rw [F.hold_zero_of_fst_zero h0, ENNReal.toReal_zero, zero_mul]
              · rw [F.Q_boundary _ _ _ _ _ (by omega), mul_one]
          _ = 1 := F.hold_tsum_toReal
  exact key _ j l rfl

open Classical in
/-- **Bound for the renewal process avoiding triangles** (Proposition 7.3 of tao-collatz; the conclusion of GGM Theorem 1.9 specialized to `ℋ`):
if `ε` is small, then for every `A > 0` there is a constant `C` such that for all `half ≥ 1` and every triangle family
`T : F.TriFam half (F.sep ε)`, over `b ~ Pascal(μ)^{half}`,
`E exp(-ε³ #{i < half : b_i = 3, (i, b_{[1,i+1]}) ∉ ⋃T}) ≤ C half^{-A}`. -/
theorem renewal_white :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ A : ℝ, 0 < A →
      ∃ C : ℝ, 0 < C ∧ ∀ (half : ℕ) (T : F.TriFam half (F.sep ε)), 1 ≤ half →
        (PMF.iid (pascalP F.p) half).expect (fun b =>
          Real.exp (-(ε ^ 3) *
            ((Finset.univ.filter fun i : Fin half =>
              b i = 3 ∧ ((i : ℕ), ((pre b ((i : ℕ) + 1) : ℕ) : ℤ)) ∉ T.blk).card : ℝ)))
          ≤ C * (half : ℝ) ^ (-A) := by
  obtain ⟨ε₀, hε₀, hdecay⟩ := F.Q_polynomial_decay
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεle A hA
  obtain ⟨C0, hC00, hC0⟩ := hdecay ε hε hεle A hA
  set κ : ℝ := ε ^ 3 with hκdef
  have hκ : 0 < κ := by positivity
  obtain ⟨C1, hC11, hC1⟩ := F.hold_weight_expect A hA (Real.exp (κ / 2) - 1) (by
    have h2 := Real.add_one_lt_exp (show κ / 2 ≠ 0 by positivity)
    linarith)
  refine ⟨max (((2 * C1 : ℕ) : ℝ) ^ A) (C0 * Real.exp (κ / 2) * 2 ^ A),
    lt_max_of_lt_right (by positivity), ?_⟩
  intro half T hhalf
  have hhalfR : (0 : ℝ) < (half : ℝ) := by exact_mod_cast hhalf
  -- the expectation is `≤ 1`
  have hE1 : (PMF.iid (pascalP F.p) half).expect (fun b =>
      Real.exp (-κ *
        ((Finset.univ.filter fun i : Fin half =>
          b i = 3 ∧ ((i : ℕ), ((pre b ((i : ℕ) + 1) : ℕ) : ℤ)) ∉ T.blk).card : ℝ))) ≤ 1 :=
    Sec7.expect_le_one _ _ (fun b => (Real.exp_pos _).le) (fun b => by
      rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
      positivity)
  rcases lt_or_ge half (2 * C1) with hsmall | hbig
  · calc (PMF.iid (pascalP F.p) half).expect _ ≤ 1 := hE1
      _ ≤ ((2 * C1 : ℕ) : ℝ) ^ A * (half : ℝ) ^ (-A) := by
          have h1 : (half : ℝ) ≤ ((2 * C1 : ℕ) : ℝ) := by exact_mod_cast hsmall.le
          have h2 : (1 : ℝ) = (half : ℝ) ^ A * (half : ℝ) ^ (-A) := by
            rw [← Real.rpow_add hhalfR, add_neg_cancel, Real.rpow_zero]
          rw [h2]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow hhalfR.le h1 hA.le) (Real.rpow_nonneg hhalfR.le _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hhalfR.le _)
  · -- bridge: vector → column recursion → renewal
    have hvec := F.bridge_vector_gen T.W κ hκ.le half half 0 0 (by omega)
    have hcount : ∀ b : Fin half → ℕ,
        (Finset.univ.filter fun i : Fin half =>
            b i = 3 ∧ ((i : ℕ), ((pre b ((i : ℕ) + 1) : ℕ) : ℤ)) ∉ T.blk).card
          = (Finset.univ.filter fun i : Fin half =>
            b i = 3 ∧ ((0 + (i : ℕ) + 1 : ℕ), (0 : ℤ) + (pre b ((i : ℕ) + 1) : ℤ)) ∈ T.W).card := by
      intro b
      refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
      refine and_congr_right fun _ => ?_
      simp only [TriFam.W, Set.mem_ofPred_eq, zero_add]
      constructor
      · intro h; exact ⟨by omega, by simpa using h⟩
      · intro h; simpa using h.2
    have hEeq : (PMF.iid (pascalP F.p) half).expect (fun b =>
        Real.exp (-κ *
          ((Finset.univ.filter fun i : Fin half =>
            b i = 3 ∧ ((i : ℕ), ((pre b ((i : ℕ) + 1) : ℕ) : ℤ)) ∉ T.blk).card : ℝ)))
        = ∑' d : ℕ × ℤ, (F.hold d).toReal * F.Q half T.W κ (0 + d.1) (0 + d.2) := by
      rw [← F.bridge_renewal half T.W κ hκ.le 0 0, ← hvec]
      exact congrArg _ (funext fun b => by rw [hcount b])
    rw [hEeq]
    have hpt : ∀ d : ℕ × ℤ,
        (F.hold d).toReal * F.Q half T.W κ (0 + d.1) (0 + d.2)
          ≤ (F.hold d).toReal * (C0 * ((max (half - d.1) 1 : ℕ) : ℝ) ^ (-A)) := by
      intro d
      rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
      · rw [F.hold_zero_of_fst_zero h0, ENNReal.toReal_zero, zero_mul, zero_mul]
      · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        have h := hC0 half T (0 + d.1) (0 + d.2) (by omega)
        simpa using h
    have hnn : ∀ d : ℕ × ℤ,
        0 ≤ (F.hold d).toReal * F.Q half T.W κ (0 + d.1) (0 + d.2) :=
      fun d => mul_nonneg ENNReal.toReal_nonneg (F.Q_nonneg _ _ _ _ _)
    have hwle : ∀ d : ℕ × ℤ, ((max (half - d.1) 1 : ℕ) : ℝ) ^ (-A) ≤ 1 := fun d =>
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast Nat.le_max_right (half - d.1) 1) (by linarith)
    have hsumw : Summable fun d : ℕ × ℤ =>
        (F.hold d).toReal * ((max (half - d.1) 1 : ℕ) : ℝ) ^ (-A) :=
      Summable.of_nonneg_of_le
        (fun d => mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (fun d => by
          calc (F.hold d).toReal * ((max (half - d.1) 1 : ℕ) : ℝ) ^ (-A)
              ≤ (F.hold d).toReal * 1 :=
                mul_le_mul_of_nonneg_left (hwle d) ENNReal.toReal_nonneg
            _ = (F.hold d).toReal := mul_one _)
        F.hold_summable_toReal
    have hsumCw : Summable fun d : ℕ × ℤ =>
        (F.hold d).toReal * (C0 * ((max (half - d.1) 1 : ℕ) : ℝ) ^ (-A)) :=
      (hsumw.mul_left C0).congr fun d => by ring
    have hsumQ : Summable fun d : ℕ × ℤ =>
        (F.hold d).toReal * F.Q half T.W κ (0 + d.1) (0 + d.2) :=
      Summable.of_nonneg_of_le hnn
        (fun d => by
          calc (F.hold d).toReal * F.Q half T.W κ (0 + d.1) (0 + d.2)
              ≤ (F.hold d).toReal * 1 :=
                mul_le_mul_of_nonneg_left (F.Q_le_one _ _ _ hκ.le _ _) ENNReal.toReal_nonneg
            _ = (F.hold d).toReal := mul_one _)
        F.hold_summable_toReal
    have hC1' : 1 + (Real.exp (κ / 2) - 1) = Real.exp (κ / 2) := by ring
    have htail := hC1 half (by omega)
    rw [hC1'] at htail
    calc ∑' d : ℕ × ℤ, (F.hold d).toReal * F.Q half T.W κ (0 + d.1) (0 + d.2)
        ≤ ∑' d : ℕ × ℤ,
            (F.hold d).toReal * (C0 * ((max (half - d.1) 1 : ℕ) : ℝ) ^ (-A)) :=
          hsumQ.tsum_le_tsum hpt hsumCw
      _ = C0 * ∑' d : ℕ × ℤ,
            (F.hold d).toReal * ((max (half - d.1) 1 : ℕ) : ℝ) ^ (-A) := by
          rw [← tsum_mul_left]
          exact tsum_congr fun d => by ring
      _ ≤ C0 * (Real.exp (κ / 2) * (half : ℝ) ^ (-A)) :=
          mul_le_mul_of_nonneg_left htail hC00.le
      _ ≤ C0 * Real.exp (κ / 2) * 2 ^ A * (half : ℝ) ^ (-A) := by
          have h2A : (1 : ℝ) ≤ 2 ^ A := Real.one_le_rpow (by norm_num) hA.le
          have hpos : 0 ≤ C0 * Real.exp (κ / 2) * (half : ℝ) ^ (-A) := by positivity
          nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hhalfR.le _)

end Family

end GGMCollatz
