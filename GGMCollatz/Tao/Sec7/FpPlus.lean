import GGMCollatz.Tao.Sec7.Walk
import GGMCollatz.Tao.Sec7.FPTail

/-!
# GGM §7: the law `fpDistPlus` of the endpoint `p` steps after the passage, and its tails ((7.61) of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, files `TaoCollatz/Sec7/ManyTriangles.lean`
(`fpDistPlus`, `fpDistPlus_height_tail`, `fpDistPlus_col_tail`) and `TaoCollatz/Sec7/Case3.lean`
(`iid_pathSum_law`, `fpDist_walk_eq_fpDistPlus`); generalized to the GGM family (p, q, r). Modified.

* `fpDistPlus s p`: the law of the first-passage endpoint (`fpDist s`) plus `p` independent steps of `ℋ`.
* `iid_pathSum_law`, `fpDist_walk_eq_fpDistPlus`: the marginal law of the sum of the first `p` steps of the walk (proved).
* `fpDistPlus_height_tail`: height tail `P(q₂ ≥ s + H) ≤ C e^{-cH}` (`H ≥ K(1+p)`). A union bound over the overshoot tail and
  the height tail of the sum of `p` steps (`FPTail.lean`).
* `fpDistPlus_col_tail`: column tail `P(|q₁ - s(p-1)/(2p)| ≥ 2D) ≤ C(e^{-cD²/(1+s)} + e^{-cD})` (`D ≥ K(1+p)`).
  A union bound over the column tail of the first passage and the column tail of the sum of `p` steps (`FPTail.lean`).
(The constants `50` and `10` of tao-collatz depend on the mean `(4, 16)` of `ℋ`; here we use `∃ K`.)
-/

open scoped ENNReal

namespace GGMCollatz

namespace Sec7

theorem iidSum_zero_pure {M : Type*} [AddCommMonoid M] (p : PMF M) :
    iidSum p 0 = PMF.pure 0 := by
  rw [iidSum, show p.iid 0 = PMF.pure (fun i => i.elim0) from rfl, PMF.pure_map]
  simp

theorem iidSum_succ_bind {M : Type*} [AddCommMonoid M] (p : PMF M) (n : ℕ) :
    iidSum p (n + 1) = p.bind fun a => (iidSum p n).map (a + ·) := by
  rw [iidSum, show p.iid (n + 1) = p.bind fun a => (p.iid n).map (Fin.cons a) from rfl,
    PMF.map_bind]
  refine congrArg _ (funext fun a => ?_)
  rw [PMF.map_comp, iidSum, PMF.map_comp]
  have hf : ((fun v : Fin (n + 1) → M => ∑ i, v i) ∘ Fin.cons a)
      = ((a + ·) ∘ fun w : Fin n → M => ∑ i, w i) := by
    funext w
    simp only [Function.comp_apply]
    rw [Fin.sum_cons]
  rw [hf]

end Sec7

namespace Family

variable (F : Family)

/-- **Law of the endpoint `p` steps after the passage** (`fpDistPlus` of tao-collatz). -/
noncomputable def fpDistPlus (s p : ℕ) : PMF (ℕ × ℤ) :=
  (F.fpDist s).bind fun e => (Sec7.iidSum F.hold p).map fun w => e + w

/-- The marginal law of the sum of the first `p` steps of the walk is `iidSum hold p` (`iid_pathSum_law` of tao-collatz). -/
theorem iid_pathSum_law :
    ∀ (T p : ℕ), p ≤ T → ∀ (f : ℕ × ℤ → ℝ≥0∞),
      ∑' v : Fin T → ℕ × ℤ, F.hold.iid T v * f (pathSum v p)
        = ∑' d : ℕ × ℤ, Sec7.iidSum F.hold p d * f d := by
  intro T
  induction T with
  | zero =>
    intro p hp f
    rw [Nat.le_zero.mp hp]
    rw [PMF.tsum_iid_zero_mul F.hold (fun v : Fin 0 → ℕ × ℤ => f (pathSum v 0))]
    rw [Sec7.iidSum_zero_pure]
    rw [tsum_eq_single (0 : ℕ × ℤ) (fun d hd => by
      rw [PMF.pure_apply, if_neg hd, zero_mul])]
    rw [PMF.pure_apply, if_pos rfl, one_mul, pathSum_zero]
  | succ T IH =>
    intro p hp f
    rw [PMF.tsum_iid_succ_mul F.hold T (fun v => f (pathSum v p))]
    rcases Nat.eq_zero_or_pos p with rfl | hppos
    · have hinner : ∀ d : ℕ × ℤ,
          ∑' w : Fin T → ℕ × ℤ, F.hold.iid T w * f (pathSum (Fin.cons d w) 0)
            = f 0 := by
        intro d
        rw [tsum_congr fun w : Fin T → ℕ × ℤ => by rw [pathSum_zero],
          ENNReal.tsum_mul_right, (F.hold.iid T).tsum_coe, one_mul]
      rw [tsum_congr fun d => by rw [hinner d]]
      rw [ENNReal.tsum_mul_right, F.hold.tsum_coe, one_mul, Sec7.iidSum_zero_pure]
      rw [tsum_eq_single (0 : ℕ × ℤ) (fun d hd => by
        rw [PMF.pure_apply, if_neg hd, zero_mul])]
      rw [PMF.pure_apply, if_pos rfl, one_mul]
    · obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hppos
      rw [tsum_congr fun d : ℕ × ℤ => by
        rw [tsum_congr fun w : Fin T → ℕ × ℤ => by
          rw [show 1 + q = q + 1 from by omega, pathSum_cons]]]
      have hIH : ∀ d : ℕ × ℤ,
          ∑' w : Fin T → ℕ × ℤ, F.hold.iid T w * f (d + pathSum w q)
            = ∑' x : ℕ × ℤ, Sec7.iidSum F.hold q x * f (d + x) :=
        fun d => IH q (by omega) (fun x => f (d + x))
      rw [tsum_congr fun d => by rw [hIH d]]
      rw [show 1 + q = q + 1 from by omega, Sec7.iidSum_succ_bind, PMF.tsum_bind_mul]
      exact tsum_congr fun d => by rw [PMF.tsum_map_mul]

/-- **`fpDistPlus` in walk form** (`fpDist_walk_eq_fpDistPlus` of tao-collatz). -/
theorem fpDist_walk_eq_fpDistPlus (s : ℕ) {T p : ℕ} (hp : p ≤ T) (g : ℕ × ℤ → ℝ≥0∞) :
    ∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin T → ℕ × ℤ, F.hold.iid T v * g (e + pathSum v p)
      = ∑' x : ℕ × ℤ, F.fpDistPlus s p x * g x := by
  have hRHS : ∑' x : ℕ × ℤ, F.fpDistPlus s p x * g x
      = ∑' e : ℕ × ℤ, F.fpDist s e * ∑' d : ℕ × ℤ, Sec7.iidSum F.hold p d * g (e + d) := by
    rw [fpDistPlus, PMF.tsum_bind_mul]
    exact tsum_congr fun e => by rw [PMF.tsum_map_mul]
  rw [hRHS]
  refine tsum_congr fun e => ?_
  congr 1
  simpa only [] using F.iid_pathSum_law T p hp (fun d => g (e + d))

/-- Indicator functions take values in `[0, 1]`. -/
theorem FP.indicator_one_mem {α : Type*} (S : Set α) (x : α) :
    0 ≤ S.indicator (1 : α → ℝ) x ∧ S.indicator (1 : α → ℝ) x ≤ 1 := by
  by_cases h : x ∈ S
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- **Height tail** (`fpDistPlus_height_tail` of tao-collatz, (7.61)). -/
theorem fpDistPlus_height_tail :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 0 < K ∧ ∀ (s p : ℕ) (H : ℝ),
      K * (1 + (p : ℝ)) ≤ H →
      ∑' e : ℕ × ℤ, (F.fpDistPlus s p e).toReal
          * Set.indicator {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} 1 e
        ≤ C * Real.exp (-c * H) := by
  obtain ⟨c₁, hc₁, C₁, hC₁, hov⟩ := FP.fpDist_overshoot_tail F
  obtain ⟨c₂, hc₂, C₂, hC₂, K₂, hK₂, hht⟩ := FP.iidSum_height_tail F
  refine ⟨min c₁ c₂ / 2, by positivity, C₁ + C₂, by positivity, 2 * K₂, by positivity, ?_⟩
  intro s p H hH
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hK : K₂ * (1 + p) ≤ H / 2 := by linarith
  have hH0 : 0 ≤ H := by nlinarith
  have hle : ∀ e w : ℕ × ℤ,
      Set.indicator {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} (1 : ℕ × ℤ → ℝ) (e + w)
        ≤ Set.indicator {q : ℕ × ℤ | (s : ℝ) + H / 2 ≤ (q.2 : ℝ)} 1 e
          + Set.indicator {q : ℕ × ℤ | H / 2 ≤ (q.2 : ℝ)} 1 w := by
    intro e w
    by_cases h : e + w ∈ {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)}
    · rw [Set.indicator_of_mem h, Pi.one_apply]
      simp only [Set.mem_ofPred_eq, Prod.snd_add, Int.cast_add] at h
      by_cases h1 : (s : ℝ) + H / 2 ≤ (e.2 : ℝ)
      · rw [Set.indicator_of_mem (show e ∈ {q : ℕ × ℤ | (s : ℝ) + H / 2 ≤ (q.2 : ℝ)} from h1),
          Pi.one_apply]
        linarith [(FP.indicator_one_mem {q : ℕ × ℤ | H / 2 ≤ (q.2 : ℝ)} w).1]
      · have h2 : H / 2 ≤ (w.2 : ℝ) := by push Not at h1; linarith
        rw [Set.indicator_of_mem (show w ∈ {q : ℕ × ℤ | H / 2 ≤ (q.2 : ℝ)} from h2),
          Pi.one_apply]
        linarith [(FP.indicator_one_mem {q : ℕ × ℤ | (s : ℝ) + H / 2 ≤ (q.2 : ℝ)} e).1]
    · rw [Set.indicator_of_notMem h]
      linarith [(FP.indicator_one_mem {q : ℕ × ℤ | (s : ℝ) + H / 2 ≤ (q.2 : ℝ)} e).1,
        (FP.indicator_one_mem {q : ℕ × ℤ | H / 2 ≤ (q.2 : ℝ)} w).1]
  have hconv := _root_.GGMCollatz.FP.tsum_conv_le (F.fpDist s) (Sec7.iidSum F.hold p)
    (Set.indicator {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} 1)
    (Set.indicator {q : ℕ × ℤ | (s : ℝ) + H / 2 ≤ (q.2 : ℝ)} 1)
    (Set.indicator {q : ℕ × ℤ | H / 2 ≤ (q.2 : ℝ)} 1)
    (fun x => (FP.indicator_one_mem _ x).1) (fun x => (FP.indicator_one_mem _ x).1)
    (fun x => (FP.indicator_one_mem _ x).1) (fun x => (FP.indicator_one_mem _ x).2)
    (fun x => (FP.indicator_one_mem _ x).2) hle
  have h1 := hov s (H / 2)
  have h2 := hht p (H / 2) hK
  have hm1 : min c₁ c₂ ≤ c₁ := min_le_left _ _
  have hm2 : min c₁ c₂ ≤ c₂ := min_le_right _ _
  have he1 : Real.exp (-c₁ * (H / 2)) ≤ Real.exp (-(min c₁ c₂ / 2) * H) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have he2 : Real.exp (-c₂ * (H / 2)) ≤ Real.exp (-(min c₁ c₂ / 2) * H) := by
    apply Real.exp_le_exp.mpr; nlinarith
  unfold fpDistPlus
  calc _ ≤ _ := hconv
    _ ≤ C₁ * Real.exp (-c₁ * (H / 2)) + C₂ * Real.exp (-c₂ * (H / 2)) := add_le_add h1 h2
    _ ≤ C₁ * Real.exp (-(min c₁ c₂ / 2) * H) + C₂ * Real.exp (-(min c₁ c₂ / 2) * H) :=
        add_le_add (mul_le_mul_of_nonneg_left he1 hC₁.le) (mul_le_mul_of_nonneg_left he2 hC₂.le)
    _ = (C₁ + C₂) * Real.exp (-(min c₁ c₂ / 2) * H) := by ring

/-- **Column tail** (`fpDistPlus_col_tail` of tao-collatz, (7.61)). -/
theorem fpDistPlus_col_tail :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 0 < K ∧ ∀ (s p : ℕ) (D : ℝ),
      K * (1 + (p : ℝ)) ≤ D →
      ∑' e : ℕ × ℤ, (F.fpDistPlus s p e).toReal
          * Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) * F.slopeInv|} 1 e
        ≤ C * (Real.exp (-c * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-c * D)) := by
  obtain ⟨c₁, hc₁, C₁, hC₁, hcol⟩ := FP.fpDist_col_tail F
  obtain ⟨c₂, hc₂, C₂, hC₂, K₂, hK₂, hct⟩ := FP.iidSum_col_tail F
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, C₁ + C₂, by positivity, K₂, hK₂, ?_⟩
  intro s p D hD
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
  set x₀ : ℝ := (s : ℝ) * F.slopeInv with hx₀
  have hle : ∀ e w : ℕ × ℤ,
      Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - x₀|} (1 : ℕ × ℤ → ℝ) (e + w)
        ≤ Set.indicator {q : ℕ × ℤ | D ≤ |(q.1 : ℝ) - x₀|} 1 e
          + Set.indicator {q : ℕ × ℤ | D ≤ (q.1 : ℝ)} 1 w := by
    intro e w
    by_cases h : e + w ∈ {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - x₀|}
    · rw [Set.indicator_of_mem h, Pi.one_apply]
      simp only [Set.mem_ofPred_eq, Prod.fst_add, Nat.cast_add] at h
      have htri : |(e.1 : ℝ) + (w.1 : ℝ) - x₀| ≤ |(e.1 : ℝ) - x₀| + (w.1 : ℝ) := by
        have h := abs_add_le ((e.1 : ℝ) - x₀) (w.1 : ℝ)
        have hw : |(w.1 : ℝ)| = (w.1 : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
        have heq : (e.1 : ℝ) + (w.1 : ℝ) - x₀ = ((e.1 : ℝ) - x₀) + (w.1 : ℝ) := by ring
        rw [heq]; linarith
      by_cases h1 : D ≤ |(e.1 : ℝ) - x₀|
      · rw [Set.indicator_of_mem (show e ∈ {q : ℕ × ℤ | D ≤ |(q.1 : ℝ) - x₀|} from h1),
          Pi.one_apply]
        linarith [(FP.indicator_one_mem {q : ℕ × ℤ | D ≤ (q.1 : ℝ)} w).1]
      · have h2 : D ≤ (w.1 : ℝ) := by push Not at h1; linarith
        rw [Set.indicator_of_mem (show w ∈ {q : ℕ × ℤ | D ≤ (q.1 : ℝ)} from h2), Pi.one_apply]
        linarith [(FP.indicator_one_mem {q : ℕ × ℤ | D ≤ |(q.1 : ℝ) - x₀|} e).1]
    · rw [Set.indicator_of_notMem h]
      linarith [(FP.indicator_one_mem {q : ℕ × ℤ | D ≤ |(q.1 : ℝ) - x₀|} e).1,
        (FP.indicator_one_mem {q : ℕ × ℤ | D ≤ (q.1 : ℝ)} w).1]
  have hconv := _root_.GGMCollatz.FP.tsum_conv_le (F.fpDist s) (Sec7.iidSum F.hold p)
    (Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - x₀|} 1)
    (Set.indicator {q : ℕ × ℤ | D ≤ |(q.1 : ℝ) - x₀|} 1)
    (Set.indicator {q : ℕ × ℤ | D ≤ (q.1 : ℝ)} 1)
    (fun x => (FP.indicator_one_mem _ x).1) (fun x => (FP.indicator_one_mem _ x).1)
    (fun x => (FP.indicator_one_mem _ x).1) (fun x => (FP.indicator_one_mem _ x).2)
    (fun x => (FP.indicator_one_mem _ x).2) hle
  have h1 := hcol s D hDpos
  have h2 := hct p D hD
  have ht0 : (0 : ℝ) < 1 + s := by positivity
  set m := min c₁ c₂ with hm
  have hm1 : m ≤ c₁ := min_le_left _ _
  have hm2 : m ≤ c₂ := min_le_right _ _
  have he1 : Real.exp (-c₁ * D ^ 2 / (1 + (s : ℝ))) ≤ Real.exp (-m * D ^ 2 / (1 + (s : ℝ))) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ ht0.le
    nlinarith [sq_nonneg D]
  have he2 : Real.exp (-c₁ * D) ≤ Real.exp (-m * D) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have he3 : Real.exp (-c₂ * D) ≤ Real.exp (-m * D) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have hE1 := (Real.exp_pos (-m * D ^ 2 / (1 + (s : ℝ)))).le
  unfold fpDistPlus
  calc _ ≤ _ := hconv
    _ ≤ C₁ * (Real.exp (-c₁ * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-c₁ * D))
          + C₂ * Real.exp (-c₂ * D) := add_le_add h1 h2
    _ ≤ C₁ * (Real.exp (-m * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-m * D))
          + C₂ * (Real.exp (-m * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-m * D)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (add_le_add he1 he2) hC₁.le
        · exact mul_le_mul_of_nonneg_left (by linarith) hC₂.le
    _ = (C₁ + C₂) * (Real.exp (-m * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-m * D)) := by ring

end Family

end GGMCollatz
