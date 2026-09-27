import GGMCollatz.NatDen.SumMixA.Head

/-!
# Auxiliary (3) for Proposition 6.12 (a) of the paper: the disjoint decomposition conditioned on the sum, and the error

Adapted from `GGMCollatz/Tao/Sec6/Events.lean` (`castedTerm`, `mainDensity`, `osc_mainDensity_le`,
`sum_abs_syracZ_sub_main_eq`), derived from `TaoCollatz/Sec6/MixingCore.lean` and
`TaoCollatz/Sec6/MixingError.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2, by adding the condition
`s_N = σ` on the sum of all valuations. The events (`pieceEvent`, `mainEvent`, `globalGood`) are those of Sec6, used unchanged.

* `castedTermS`, `mainDensityS`: the push-forwards restricted to a piece / the main event and to `s_N = σ`.
* `osc_mainDensityS_le`: the oscillation of the main density is at most the sum of the oscillations of the pieces.
* `sum_abs_jpR_sub_mainS_le`: the `L¹` norm of the error is at most `P(¬mainEvent)` (the positivity form of (T3)).
-/

open scoped BigOperators ENNReal

namespace GGMCollatz

namespace ND

namespace SumMixAAux

open Family

variable (F : Family)

/-! ### Differences of restricted push-forwards -/

/-- If `E₂ ⊆ E₁`, the difference of the restricted push-forwards is the restriction to `E₁ ∧ ¬E₂`. -/
theorem restrictedDensity_sub {α β : Type*} [Fintype β] [DecidableEq β] (P : PMF α) (X : α → β)
    (E₁ E₂ : α → Prop) [DecidablePred E₁] [DecidablePred E₂] (h : ∀ a, E₂ a → E₁ a) (Y : β) :
    Mix.restrictedDensity P X E₁ Y - Mix.restrictedDensity P X E₂ Y
      = Mix.restrictedDensity P X (fun a => E₁ a ∧ ¬ E₂ a) Y := by
  have hPsum : Summable fun a => (P a).toReal := ENNReal.summable_toReal P.tsum_coe_ne_top
  have hs : ∀ (E : α → Prop) [DecidablePred E],
      Summable fun a => (P a).toReal * (if X a = Y ∧ E a then (1 : ℝ) else 0) := by
    intro E _
    exact Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num))
      (fun a => by split <;> simp [ENNReal.toReal_nonneg]) hPsum
  unfold Mix.restrictedDensity
  rw [← (hs E₁).tsum_sub (hs E₂)]
  refine tsum_congr (fun a => ?_)
  by_cases hX : X a = Y
  · by_cases h2 : E₂ a
    · have h1 := h a h2
      simp [hX, h1, h2]
    · by_cases h1 : E₁ a <;> simp [hX, h1, h2]
  · simp [hX]

/-! ### Transferred pieces -/

/-- The density of a transferred piece conditioned on the sum is the restricted push-forward at level `n`. -/
theorem cast_condDensWS_apply_eq_restricted (j P n l σ : ℕ) (e : j + P = n)
    (W : (Fin P → ℕ × ℕ) → Prop) [DecidablePred W] (Y : ZMod (F.q ^ n)) :
    (e ▸ condDensWS F j P l σ W) Y =
      Mix.restrictedDensity ((stepLaw F.p).iid n) (F.roff n)
        (fun v =>
          (let vt : Fin P → ℕ × ℕ := fun i => v (Fin.cast e (Fin.natAdd j i))
          pre (fun i => (vt i).1) P = l ∧ W vt) ∧ pre (fun i => (v i).1) n = σ) Y := by
  subst n
  rfl

open Classical in
/-- The density of the piece with cut `k`, `M = l` and `s_N = σ`, transferred to level `N`. -/
noncomputable def castedTermS (N : ℕ) (Wf : TailFam) (k l σ : ℕ) : ZMod (F.q ^ N) → ℝ :=
  if h : k < N then (cutEq h) ▸ condDensWS F (N - 1 - k) (k + 1) l σ (Wf k l) else 0

open Classical in
theorem castedTermS_apply_eq (N : ℕ) (Wf : TailFam) (k l σ : ℕ) (Y : ZMod (F.q ^ N)) :
    castedTermS F N Wf k l σ Y =
      Mix.restrictedDensity ((stepLaw F.p).iid N) (F.roff N)
        (fun v => pieceEvent N Wf k l v ∧ pre (fun i => (v i).1) N = σ) Y := by
  by_cases h : k < N
  · unfold castedTermS
    rw [dif_pos h, cast_condDensWS_apply_eq_restricted F (N - 1 - k) (k + 1) N l σ (cutEq h)
      (Wf k l) Y]
    unfold Mix.restrictedDensity
    refine tsum_congr (fun v => ?_)
    congr 1
    refine if_congr ?_ rfl rfl
    simp only [pieceEvent, dif_pos h]
    rfl
  · unfold castedTermS
    rw [dif_neg h]
    simp [Mix.restrictedDensity, pieceEvent, h]

open Classical in
/-- The oscillation of a piece is the oscillation of the conditioned density at the original level. -/
theorem osc_castedTermS (N m k l σ : ℕ) (hmn : m ≤ N) (hkn : k < N) (Wf : TailFam) :
    F.osc m N hmn (castedTermS F N Wf k l σ)
      = F.osc m (N - 1 - k + (k + 1)) (by rw [cutEq hkn]; exact hmn)
          (condDensWS F (N - 1 - k) (k + 1) l σ (Wf k l)) := by
  unfold castedTermS
  rw [dif_pos hkn]
  exact F.osc_cast' (cutEq hkn) _ hmn _

/-- **The main density** (conditioned on the sum). -/
noncomputable def mainDensityS (N : ℕ) (Wf : TailFam) (S : Finset (ℕ × ℕ)) (σ : ℕ) :
    ZMod (F.q ^ N) → ℝ := fun Y => ∑ kl ∈ S, castedTermS F N Wf kl.1 kl.2 σ Y

open Classical in
/-- The oscillation of the main density is at most the sum of the oscillations of the pieces at their original levels. -/
theorem osc_mainDensityS_le (N m σ : ℕ) (hmn : m ≤ N) (Wf : TailFam) (S : Finset (ℕ × ℕ))
    (B : ℕ × ℕ → ℝ)
    (hterm : ∀ kl ∈ S, ∀ hkn : kl.1 < N,
      F.osc m (N - 1 - kl.1 + (kl.1 + 1)) (by rw [cutEq hkn]; exact hmn)
        (condDensWS F (N - 1 - kl.1) (kl.1 + 1) kl.2 σ (Wf kl.1 kl.2)) ≤ B kl)
    (hB : ∀ kl ∈ S, 0 ≤ B kl) :
    F.osc m N hmn (mainDensityS F N Wf S σ) ≤ ∑ kl ∈ S, B kl := by
  unfold mainDensityS
  refine le_trans (F.osc_sum_le m N hmn S (fun kl Y => castedTermS F N Wf kl.1 kl.2 σ Y)) ?_
  refine Finset.sum_le_sum (fun kl hkl => ?_)
  by_cases hkn : kl.1 < N
  · rw [show (fun Y => castedTermS F N Wf kl.1 kl.2 σ Y) = castedTermS F N Wf kl.1 kl.2 σ from rfl,
      osc_castedTermS F N m kl.1 kl.2 σ hmn hkn Wf]
    exact hterm kl hkl hkn
  · have hz : (fun Y => castedTermS F N Wf kl.1 kl.2 σ Y) = fun _ => 0 := by
      funext Y; unfold castedTermS; rw [dif_neg hkn]; rfl
    rw [hz]
    simp only [osc, sub_self, mul_zero, abs_zero, Finset.sum_const_zero]
    exact hB kl hkl

open Classical in
/-- The main density (conditioned on the sum) is the push-forward restricted to the main event and to `s_N = σ`. -/
theorem mainDensityS_eq_restricted (N : ℕ) (T s K : ℝ) (S : Finset (ℕ × ℕ)) (σ : ℕ)
    (Y : ZMod (F.q ^ N)) :
    mainDensityS F N (ggmW T s K) S σ Y =
      Mix.restrictedDensity ((stepLaw F.p).iid N) (F.roff N)
        (fun v => mainEvent N T s K S v ∧ pre (fun i => (v i).1) N = σ) Y := by
  unfold mainDensityS
  simp only [castedTermS_apply_eq]
  have hdisj : ∀ v kl, kl ∈ S → ∀ kl', kl' ∈ S →
      (pieceEvent N (ggmW T s K) kl.1 kl.2 v ∧ pre (fun i => (v i).1) N = σ) →
      (pieceEvent N (ggmW T s K) kl'.1 kl'.2 v ∧ pre (fun i => (v i).1) N = σ) → kl = kl' := by
    intro v kl _ kl' _ hE hE'
    exact pieceEvent_index_unique N kl.1 kl'.1 kl.2 kl'.2 T s K v hE.1 hE'.1
  rw [Mix.sum_restrictedDensity_eq_union ((stepLaw F.p).iid N) (F.roff N) S
    (fun kl v => pieceEvent N (ggmW T s K) kl.1 kl.2 v ∧ pre (fun i => (v i).1) N = σ) hdisj Y]
  unfold Mix.restrictedDensity
  refine tsum_congr (fun v => ?_)
  congr 1
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨hX, kl, hkl, hp, hσ⟩
    exact ⟨hX, ⟨kl, hkl, hp⟩, hσ⟩
  · rintro ⟨hX, ⟨kl, hkl, hp⟩, hσ⟩
    exact ⟨hX, kl, hkl, hp, hσ⟩

open Classical in
/-- **The `L¹` norm of the error**: `Σ |P(𝒮_N = ·, s_N = σ) - main_σ| ≤ P(¬mainEvent)`. -/
theorem sum_abs_jpR_sub_mainS_le (N : ℕ) (T s K : ℝ) (S : Finset (ℕ × ℕ)) (σ : ℕ) :
    ∑ Y, |jpR F N σ Y - mainDensityS F N (ggmW T s K) S σ Y| ≤
      ∑' v : Fin N → ℕ × ℕ, if mainEvent N T s K S v then 0
        else (((stepLaw F.p).iid N) v).toReal := by
  have hpt : ∀ Y, |jpR F N σ Y - mainDensityS F N (ggmW T s K) S σ Y|
      = Mix.restrictedDensity ((stepLaw F.p).iid N) (F.roff N)
          (fun v => pre (fun i => (v i).1) N = σ
            ∧ ¬ (mainEvent N T s K S v ∧ pre (fun i => (v i).1) N = σ)) Y := by
    intro Y
    rw [mainDensityS_eq_restricted]
    unfold jpR
    rw [restrictedDensity_sub _ _ _ _ (fun a h => h.2) Y]
    exact abs_of_nonneg (Mix.restrictedDensity_nonneg _ _ _ Y)
  rw [Finset.sum_congr rfl (fun Y _ => hpt Y), sum_restrictedDensity]
  have hPsum : Summable fun v : Fin N → ℕ × ℕ => (((stepLaw F.p).iid N) v).toReal :=
    ENNReal.summable_toReal ((stepLaw F.p).iid N).tsum_coe_ne_top
  refine Summable.tsum_le_tsum (fun v => ?_) ?_ ?_
  · by_cases hm : mainEvent N T s K S v
    · rw [if_pos hm]
      by_cases hσ : pre (fun i => (v i).1) N = σ
      · rw [if_neg (fun h => h.2 ⟨hm, hσ⟩), mul_zero]
      · rw [if_neg (fun h => hσ h.1), mul_zero]
    · rw [if_neg hm]
      split_ifs <;> simp
  · exact Summable.of_nonneg_of_le
      (fun v => mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num))
      (fun v => by split <;> simp [ENNReal.toReal_nonneg]) hPsum
  · exact Summable.of_nonneg_of_le
      (fun v => by split <;> simp [ENNReal.toReal_nonneg])
      (fun v => by split <;> simp [ENNReal.toReal_nonneg]) hPsum

end SumMixAAux

end ND

end GGMCollatz
