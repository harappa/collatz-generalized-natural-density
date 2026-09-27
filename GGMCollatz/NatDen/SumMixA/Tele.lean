import GGMCollatz.NatDen.SumMixA.Basic

/-!
# Auxiliary (5) for Proposition 6.12 (a) of the paper: telescoping of the oscillation of a general function, and the oscillation of a mixture of projections

The telescoping for (a). The telescoping of `GGMCollatz/Tao/Sec6/Core.lean` and `FromDecay.lean`, derived from
`TaoCollatz/Sec6/MixingCore.lean` (`osc_syracZ_levels_triangle`) of gotrevor/tao-collatz (Apache-2.0), commit 15efca2,
adapted from the law of `𝒮_n` to a general function: instead of the agreement of projections, we use the projection
`projS` (the sum over the classes mod `q^k`).

* `osc_levels_triangle_gen`: `Osc_{m,n}(c) ≤ Osc_{k,n}(c) + Osc_{m,k}(projS_k c)`.
* `osc_le_sum_of_steps`: the sum of the bounds for adjacent levels.
* `osc_proj_jp_le`: `projS_{k+1}(P(𝒮_n = ·, s_n = s))` is a nonnegative mixture of the `P(𝒮_{k+1} = ·, s_{k+1} = σ)`
  (`proj_jp_eq`), so its oscillation is at most the weighted sum of the mixture.
-/

open scoped BigOperators ENNReal

namespace GGMCollatz

namespace ND

namespace SumMixAAux

open Family

variable (F : Family)

/-- Projection: the sum over the classes mod `q^k`. -/
noncomputable def projS (k n : ℕ) (hkn : k ≤ n) (c : ZMod (F.q ^ n) → ℝ) : ZMod (F.q ^ k) → ℝ :=
  fun Z => ∑ Y ∈ Finset.univ.filter (fun Y : ZMod (F.q ^ n) =>
    ZMod.castHom (pow_dvd_pow F.q hkn) (ZMod (F.q ^ k)) Y = Z), c Y

/-- The oscillation can be written in terms of the values of the projection. -/
theorem osc_eq_projS (m n : ℕ) (hmn : m ≤ n) (c : ZMod (F.q ^ n) → ℝ) :
    F.osc m n hmn c = ∑ Y, |c Y - (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
      projS F m n hmn c (ZMod.castHom (pow_dvd_pow F.q hmn) (ZMod (F.q ^ m)) Y)| := rfl

/-- Projection to the same level is the identity. -/
theorem projS_self (n : ℕ) (h : n ≤ n) (c : ZMod (F.q ^ n) → ℝ) : projS F n n h c = c := by
  funext Z
  unfold projS
  rw [Finset.sum_eq_single Z]
  · intro Y hY hYZ
    rw [Finset.mem_filter] at hY
    exact absurd (by rw [← hY.2, ZMod.castHom_apply, ZMod.cast_id', id]) hYZ
  · intro hZ
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [ZMod.castHom_apply, ZMod.cast_id', id]⟩) hZ

/-- The oscillation at the same level is 0. -/
theorem osc_self (n : ℕ) (c : ZMod (F.q ^ n) → ℝ) : F.osc n n le_rfl c = 0 := by
  rw [osc_eq_projS, projS_self]
  refine Finset.sum_eq_zero (fun Y _ => ?_)
  rw [ZMod.castHom_apply, ZMod.cast_id', id, sub_self, zpow_zero, one_mul, sub_self, abs_zero]

/-- Projections compose through an intermediate level. -/
theorem projS_tower (m k n : ℕ) (hmk : m ≤ k) (hkn : k ≤ n) (c : ZMod (F.q ^ n) → ℝ) :
    projS F m n (hmk.trans hkn) c = projS F m k hmk (projS F k n hkn c) := by
  funext W
  set πk := ZMod.castHom (pow_dvd_pow F.q hkn) (ZMod (F.q ^ k)) with hπk
  set πmk := ZMod.castHom (pow_dvd_pow F.q hmk) (ZMod (F.q ^ m)) with hπmk
  have hcomp : ∀ Y : ZMod (F.q ^ n),
      ZMod.castHom (pow_dvd_pow F.q (hmk.trans hkn)) (ZMod (F.q ^ m)) Y = πmk (πk Y) := by
    intro Y
    exact (congrArg (fun f : ZMod (F.q ^ n) →+* ZMod (F.q ^ m) => f Y)
      (ZMod.castHom_comp (pow_dvd_pow F.q hmk) (pow_dvd_pow F.q hkn))).symm
  unfold projS
  simp only [Finset.sum_filter]
  simp_rw [hcomp]
  have h1 : ∀ Z : ZMod (F.q ^ k),
      (if πmk Z = W then ∑ Y : ZMod (F.q ^ n), (if πk Y = Z then c Y else 0) else 0)
        = ∑ Y : ZMod (F.q ^ n), (if πmk Z = W then (if πk Y = Z then c Y else 0) else 0) := by
    intro Z
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun Z _ => h1 Z), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  rw [Finset.sum_eq_single (πk Y)]
  · by_cases h : πmk (πk Y) = W
    · rw [if_pos h, if_pos h, if_pos rfl]
    · rw [if_neg h, if_neg h]
  · intro Z _ hZ
    rw [if_neg (Ne.symm hZ)]
    split_ifs <;> rfl
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Triangle inequality across scales** (general function). -/
theorem osc_levels_triangle_gen (m k n : ℕ) (hmk : m ≤ k) (hkn : k ≤ n)
    (c : ZMod (F.q ^ n) → ℝ) :
    F.osc m n (hmk.trans hkn) c ≤ F.osc k n hkn c + F.osc m k hmk (projS F k n hkn c) := by
  set πk := ZMod.castHom (pow_dvd_pow F.q hkn) (ZMod (F.q ^ k)) with hπk
  set πmk := ZMod.castHom (pow_dvd_pow F.q hmk) (ZMod (F.q ^ m)) with hπmk
  have hcomp : ∀ Y : ZMod (F.q ^ n),
      ZMod.castHom (pow_dvd_pow F.q (hmk.trans hkn)) (ZMod (F.q ^ m)) Y = πmk (πk Y) := by
    intro Y
    exact (congrArg (fun f : ZMod (F.q ^ n) →+* ZMod (F.q ^ m) => f Y)
      (ZMod.castHom_comp (pow_dvd_pow F.q hmk) (pow_dvd_pow F.q hkn))).symm
  set Pk := projS F k n hkn c with hPk
  have hq0 : (0 : ℝ) < (F.q : ℝ) := by exact_mod_cast F.q_pos
  -- the second term is the oscillation at level `k`
  set g : ZMod (F.q ^ k) → ℝ := fun Z => (F.q : ℝ) ^ ((k : ℤ) - (n : ℤ)) *
    |Pk Z - (F.q : ℝ) ^ ((m : ℤ) - (k : ℤ)) * projS F m k hmk Pk (πmk Z)| with hg
  have hpt : ∀ Y : ZMod (F.q ^ n),
      |(F.q : ℝ) ^ ((k : ℤ) - (n : ℤ)) * Pk (πk Y)
        - (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) * projS F m n (hmk.trans hkn) c
            (ZMod.castHom (pow_dvd_pow F.q (hmk.trans hkn)) (ZMod (F.q ^ m)) Y)| = g (πk Y) := by
    intro Y
    rw [hcomp, projS_tower F m k n hmk hkn c, hg]
    simp only
    rw [← hPk]
    have hsplit : (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ))
        = (F.q : ℝ) ^ ((k : ℤ) - (n : ℤ)) * (F.q : ℝ) ^ ((m : ℤ) - (k : ℤ)) := by
      rw [← zpow_add₀ hq0.ne']; congr 1; ring
    rw [hsplit, mul_assoc, ← mul_sub, abs_mul, abs_of_nonneg (zpow_nonneg hq0.le _)]
  have hsecond : ∑ Y : ZMod (F.q ^ n),
      |(F.q : ℝ) ^ ((k : ℤ) - (n : ℤ)) * Pk (πk Y)
        - (F.q : ℝ) ^ ((m : ℤ) - (n : ℤ)) * projS F m n (hmk.trans hkn) c
            (ZMod.castHom (pow_dvd_pow F.q (hmk.trans hkn)) (ZMod (F.q ^ m)) Y)|
      = F.osc m k hmk Pk := by
    rw [Finset.sum_congr rfl (fun Y _ => hpt Y), F.sum_comp_castHom k n hkn g, osc_eq_projS, hg]
    simp only
    rw [← Finset.mul_sum, ← mul_assoc]
    have hpow : ((F.q ^ (n - k) : ℕ) : ℝ) * (F.q : ℝ) ^ ((k : ℤ) - (n : ℤ)) = 1 := by
      rw [show ((F.q ^ (n - k) : ℕ) : ℝ) = (F.q : ℝ) ^ ((n : ℤ) - (k : ℤ)) by
        rw [← Nat.cast_sub hkn, zpow_natCast]; push_cast; ring, ← zpow_add₀ hq0.ne']
      simp
    rw [hpow, one_mul]
  rw [osc_eq_projS, osc_eq_projS F k n hkn, ← hsecond, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun Y _ => ?_)
  exact abs_sub_le _ _ _

/-- **Telescoping**: the sum of the bounds `b k` for adjacent levels. -/
theorem osc_le_sum_of_steps (b : ℕ → ℝ) :
    ∀ (d m : ℕ) (c : ZMod (F.q ^ (m + d)) → ℝ),
      (∀ k (hk : k + 1 ≤ m + d), m ≤ k →
        F.osc k (k + 1) (Nat.le_succ k) (projS F (k + 1) (m + d) hk c) ≤ b k) →
      F.osc m (m + d) (Nat.le_add_right m d) c ≤ ∑ k ∈ Finset.Ico m (m + d), b k := by
  intro d
  induction d with
  | zero =>
    intro m c _
    rw [show F.osc m (m + 0) (Nat.le_add_right m 0) c = 0 from osc_self F m c]
    simp
  | succ d ih =>
    intro m c h
    have htri := osc_levels_triangle_gen F m (m + d) (m + (d + 1)) (Nat.le_add_right m d)
      (by omega) c
    have htop : F.osc (m + d) (m + (d + 1)) (by omega) c ≤ b (m + d) := by
      have h0 := h (m + d) (le_refl _) (Nat.le_add_right m d)
      have hself : projS F (m + d + 1) (m + (d + 1)) (le_refl _) c = c :=
        projS_self F (m + (d + 1)) _ c
      rw [hself] at h0
      exact h0
    have hrest := ih m (projS F (m + d) (m + (d + 1)) (by omega) c) (fun k hk hmk => by
      have := h k (by omega) hmk
      rw [projS_tower F (k + 1) (m + d) (m + (d + 1)) hk (by omega) c] at this
      exact this)
    have hsum : ∑ k ∈ Finset.Ico m (m + (d + 1)), b k
        = ∑ k ∈ Finset.Ico m (m + d), b k + b (m + d) :=
      Finset.sum_Ico_succ_top (Nat.le_add_right m d) b
    rw [hsum]
    calc F.osc m (m + (d + 1)) (Nat.le_add_right m (d + 1)) c
        ≤ F.osc (m + d) (m + (d + 1)) (by omega) c
          + F.osc m (m + d) (Nat.le_add_right m d) (projS F (m + d) (m + (d + 1)) (by omega) c) :=
          htri
      _ ≤ b (m + d) + ∑ k ∈ Finset.Ico m (m + d), b k := add_le_add htop hrest
      _ = ∑ k ∈ Finset.Ico m (m + d), b k + b (m + d) := add_comm _ _

/-- The oscillation commutes with multiplication by a nonnegative constant. -/
theorem osc_const_mul (m n : ℕ) (hmn : m ≤ n) (a : ℝ) (ha : 0 ≤ a) (c : ZMod (F.q ^ n) → ℝ) :
    F.osc m n hmn (fun Y => a * c Y) = a * F.osc m n hmn c := by
  unfold osc
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  rw [← Finset.mul_sum, ← abs_of_nonneg ha, ← abs_mul, abs_of_nonneg ha]
  congr 1
  ring

/-- **The oscillation of a mixture of projections**. -/
theorem osc_proj_jp_le (k d s : ℕ) :
    F.osc k (k + 1) (Nat.le_succ k)
        (projS F (k + 1) (k + 1 + d) (Nat.le_add_right _ _) (fun Y => jp F (k + 1 + d) Y s))
      ≤ ∑ σ ∈ Finset.range (s + 1),
          nb F.p d (s - σ) * F.osc k (k + 1) (Nat.le_succ k) (fun Y => jp F (k + 1) Y σ) := by
  have hfun : projS F (k + 1) (k + 1 + d) (Nat.le_add_right _ _) (fun Y => jp F (k + 1 + d) Y s)
      = fun Z => ∑ σ ∈ Finset.range (s + 1), nb F.p d (s - σ) * jp F (k + 1) Z σ := by
    funext Z
    exact proj_jp_eq F (k + 1) d s Z
  rw [hfun]
  refine le_trans (F.osc_sum_le k (k + 1) (Nat.le_succ k) (Finset.range (s + 1))
    (fun σ Z => nb F.p d (s - σ) * jp F (k + 1) Z σ)) (le_of_eq ?_)
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  exact osc_const_mul F k (k + 1) _ _ (nb_nonneg F d (s - σ)) _

end SumMixAAux

end ND

end GGMCollatz
