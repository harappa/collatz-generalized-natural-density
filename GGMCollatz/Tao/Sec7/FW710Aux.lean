import GGMCollatz.Tao.Sec7.FW710Geo

/-!
# Components for assembling Lemma 7.10: support of `fpDistPlus`, decomposition of sums, probability of a separated set

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/ManyTriangles.lean`
(the ideas of `fpDistPlus_support_snd_gt`, `encounter_separated_sum`); generalized to the GGM family (p, q, r). Modified.

* `fpDistPlus_support_snd_gt`: on the support of `fpDistPlus s p`, `s < x₂`.
* `tsum_mul_indicator_eq`: correspondence between sums of indicator functions in `ℝ≥0∞` and real sums.
* `fpDistPlus_tsum_eq`: `Σ_x fpDistPlus(x) g(x) = Σ_w iidSum(w) Σ_e fpDist(e) g(e + w)`.
* `sparse_shift_le`: for a `d`-separated set `A` and `r`, the probability that `j + x₁ - r ∈ A` is
  `≤ K(1/√(1+s) + 1/d)` (`col_sparse_le` after a translation).
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

namespace FW

namespace T710

variable (F : Family)

/-- On the support of `fpDistPlus s p`, `s < x₂`. -/
theorem fpDistPlus_support_snd_gt (s p : ℕ) (x : ℕ × ℤ) (hx : F.fpDistPlus s p x ≠ 0) :
    (s : ℤ) < x.2 := by
  have hx' : x ∈ (F.fpDistPlus s p).support := hx
  rw [Family.fpDistPlus, PMF.mem_support_bind_iff] at hx'
  obtain ⟨e, he, hxe⟩ := hx'
  rw [PMF.mem_support_map_iff] at hxe
  obtain ⟨w, hw, rfl⟩ := hxe
  have he2 := F.fpDist_support_snd_gt s e he
  have hw2 : 0 ≤ w.2 := by
    rw [Sec7.iidSum, PMF.mem_support_map_iff] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    have hvi := PMF.iid_support_coord F.hold p v hv
    rw [Prod.snd_sum]
    exact Finset.sum_nonneg fun i _ => by
      have := F.hold_support_snd_ge (v i) (hvi i); omega
  show (s : ℤ) < (e + w).2
  rw [Prod.snd_add]; omega

/-- A sum of indicator functions in `ℝ≥0∞` is `ofReal` of the real sum. -/
theorem tsum_mul_indicator_eq {α : Type*} (μ : PMF α) (E : Set α) :
    ∑' x, μ x * E.indicator (1 : α → ℝ≥0∞) x
      = ENNReal.ofReal (∑' x, (μ x).toReal * E.indicator (1 : α → ℝ) x) := by
  have hpt : ∀ x, E.indicator (1 : α → ℝ≥0∞) x = ENNReal.ofReal (E.indicator (1 : α → ℝ) x) := by
    intro x
    by_cases hx : x ∈ E
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hne : ∑' x, μ x * ENNReal.ofReal (E.indicator (1 : α → ℝ) x) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (PMF.tsum_mul_ofReal_le_one μ _ (fun x => by
        by_cases hx : x ∈ E
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx]))
  rw [tsum_congr fun x => by rw [hpt x], ← PMF.toReal_tsum_mul_ofReal μ _ (fun x => by
    by_cases hx : x ∈ E
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]), ENNReal.ofReal_toReal hne]

/-- Decomposition of sums against `fpDistPlus`. -/
theorem fpDistPlus_tsum_eq (s p : ℕ) (g : ℕ × ℤ → ℝ≥0∞) :
    ∑' x, F.fpDistPlus s p x * g x
      = ∑' w, Sec7.iidSum F.hold p w * ∑' e, F.fpDist s e * g (e + w) := by
  rw [Family.fpDistPlus, PMF.tsum_bind_mul]
  have h1 : ∀ e, ∑' x, ((Sec7.iidSum F.hold p).map fun w => e + w) x * g x
      = ∑' w, Sec7.iidSum F.hold p w * g (e + w) := fun e => PMF.tsum_map_mul _ _ _
  rw [tsum_congr fun e => by rw [h1 e]]
  rw [tsum_congr fun e => (ENNReal.tsum_mul_left).symm, ENNReal.tsum_comm]
  refine tsum_congr fun w => ?_
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun e => by ring

/-- **Translated probability of a separated set**: if `A` is `d`-separated, the `fpDistPlus` probability that
`j + x₁ - r ∈ A` (with `r ≤ j + x₁`) is `≤ K(1/√(1+s) + 1/d)`. -/
theorem sparse_shift_le : ∃ K : ℝ, 0 < K ∧ ∀ (s p d : ℕ), 1 ≤ d → ∀ (A : Set ℕ),
    (∀ a ∈ A, ∀ b ∈ A, a < b → a + d ≤ b) → ∀ (j r : ℕ),
    ∑' x, F.fpDistPlus s p x
        * Set.indicator {y : ℕ × ℤ | r ≤ j + y.1 ∧ j + y.1 - r ∈ A} (1 : ℕ × ℤ → ℝ≥0∞) x
      ≤ ENNReal.ofReal (K * (1 / Real.sqrt (1 + s) + 1 / d)) := by
  obtain ⟨K, hK, hcol⟩ := col_sparse_le F
  refine ⟨K, hK, ?_⟩
  intro s p d hd A hA j r
  rw [fpDistPlus_tsum_eq]
  have hinner : ∀ w : ℕ × ℤ,
      ∑' e, F.fpDist s e
          * Set.indicator {y : ℕ × ℤ | r ≤ j + y.1 ∧ j + y.1 - r ∈ A} (1 : ℕ × ℤ → ℝ≥0∞) (e + w)
        ≤ ENNReal.ofReal (K * (1 / Real.sqrt (1 + s) + 1 / d)) := by
    intro w
    obtain ⟨S, hSdef⟩ : ∃ S : Set ℕ, S = {k | r ≤ j + k + w.1 ∧ j + k + w.1 - r ∈ A} := ⟨_, rfl⟩
    have hS : ∀ a ∈ S, ∀ b ∈ S, a < b → a + d ≤ b := by
      intro a ha b hb hab
      rw [hSdef] at ha hb
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hb1, hb2⟩ := hb
      have := hA _ ha2 _ hb2 (by omega)
      omega
    have heq : ∀ e : ℕ × ℤ,
        Set.indicator {y : ℕ × ℤ | r ≤ j + y.1 ∧ j + y.1 - r ∈ A} (1 : ℕ × ℤ → ℝ≥0∞) (e + w)
          = S.indicator 1 e.1 := by
      intro e
      have hiff : e + w ∈ {y : ℕ × ℤ | r ≤ j + y.1 ∧ j + y.1 - r ∈ A} ↔ e.1 ∈ S := by
        rw [hSdef]
        show (r ≤ j + (e.1 + w.1) ∧ j + (e.1 + w.1) - r ∈ A)
          ↔ (r ≤ j + e.1 + w.1 ∧ j + e.1 + w.1 - r ∈ A)
        rw [← Nat.add_assoc]
      by_cases h : e.1 ∈ S
      · rw [Set.indicator_of_mem (hiff.mpr h), Set.indicator_of_mem h, Pi.one_apply, Pi.one_apply]
      · rw [Set.indicator_of_notMem (fun h' => h (hiff.mp h')), Set.indicator_of_notMem h]
    rw [tsum_congr fun e => by rw [heq e]]
    exact hcol s d hd S hS
  calc ∑' w, Sec7.iidSum F.hold p w * ∑' e, F.fpDist s e
          * Set.indicator {y : ℕ × ℤ | r ≤ j + y.1 ∧ j + y.1 - r ∈ A} (1 : ℕ × ℤ → ℝ≥0∞) (e + w)
      ≤ ∑' w, Sec7.iidSum F.hold p w * ENNReal.ofReal (K * (1 / Real.sqrt (1 + s) + 1 / d)) :=
        ENNReal.tsum_le_tsum fun w => by gcongr; exact hinner w
    _ = ENNReal.ofReal (K * (1 / Real.sqrt (1 + s) + 1 / d)) := by
        rw [ENNReal.tsum_mul_right, (Sec7.iidSum F.hold p).tsum_coe, one_mul]

end T710

end FW

end Family

end GGMCollatz
