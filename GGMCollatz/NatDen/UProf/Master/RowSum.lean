import GGMCollatz.NatDen.UProf.Master.Rows

/-!
# Ingredients of (UM): assembling the bound for each row `n` and sum `s`, and summing over `s` and `n`

* `row_bound`: fix `k` and `s`; bound `Σ_{M ∈ E'} (U₁ + U₂)` by the cost of the good tuples `Y K₁ P(Σa = s, not good)`, plus,
  for central `s`, the (EP2) flattening and the product-formula error `ε β (p^s q^{-k} ν̄ + p^s x^{1/2} 1[ν̄ ≥ 1])`,
  and, for non-central `s`, `2 Y K₁ P(s_k = s)`.
* `sum_cenN_le`: the sum over `n` and `s` of `p^s q^{-k} ν̄` for central `s` is, after re-summing over `M`,
  `(p/(p-1)) N_R Y K₁` (`kernC_le` and the case `k = 0` of (EP1)).
* `sum_half_le`: the sum of `p^s` over the `s` with `ν̄ ≥ 1` is `(p/(p-1)) Y q^{n₀}/Mlo`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace MasterAux

variable (F : Family)

open Classical in
/-- **The bound for each row `k` and sum `s`**. -/
theorem row_bound {α x y Y K₁ ε β : ℝ} {k s : ℕ} (hx : 0 ≤ x) (hY : 0 < Y) (hk : k ≤ F.nZero x)
    (hmk : m1 x ≤ k)
    (hK₁ : ∀ j ≤ F.nZero x, ∀ X : ZMod (F.q ^ j), F.cE α x Set.univ j X ≤ K₁)
    (hflatk : ∀ X : ZMod (F.q ^ k), ∀ A B : ℝ,
      |(((F.Eprime α x Set.univ).filter (fun M : ℕ =>
            A < (M : ℝ) ∧ (M : ℝ) ≤ B ∧ ((M : ℕ) : ZMod (F.q ^ k)) = X)).card : ℝ)
        - (F.q : ℝ) ^ (-(k : ℤ)) *
          (((F.Eprime α x Set.univ).filter (fun M : ℕ => A < (M : ℝ) ∧ (M : ℝ) ≤ B)).card : ℝ)|
        ≤ x ^ (1 / 2 : ℝ))
    (hmixk : |(s : ℝ) - F.mu * k| ≤ rad k →
        ∑ X : ZMod (F.q ^ k), |jp F k X s - nb F.p k s * (F.q : ℝ) ^ ((m1 x : ℤ) - (k : ℤ)) *
            ((F.syracZ (m1 x)) (ZMod.castHom (pow_dvd_pow F.q hmk) (ZMod (F.q ^ m1 x)) X)).toReal|
          ≤ ε * nb F.p k s)
    (hlock : nb F.p k s ≤ β) (hε : 0 ≤ ε) (G : (Fin k → ℕ) → Prop) :
    ∑ M ∈ F.Eprime α x Set.univ,
        ((if inWin F y Y k s M then (F.p : ℝ) ^ s *
            (jp F k (M : ZMod (F.q ^ k)) s - jpG F k (M : ZMod (F.q ^ k)) s G) else 0)
          + (if inWin F y Y k s M then (F.p : ℝ) ^ s *
            |jp F k (M : ZMod (F.q ^ k)) s - nb F.p k s * (F.q : ℝ) ^ ((m1 x : ℤ) - (k : ℤ)) *
              ((F.syracZ (m1 x)) (M : ZMod (F.q ^ m1 x))).toReal| else 0))
      ≤ Y * K₁ * pG F k s (fun a => ¬ G a)
        + (if |(s : ℝ) - F.mu * k| ≤ rad k then
            ε * β * ((F.p : ℝ) ^ s / (F.q : ℝ) ^ k *
                (((F.Eprime α x Set.univ).filter (fun M : ℕ => inWin F y Y k s M)).card : ℝ)
              + (if 0 < ((F.Eprime α x Set.univ).filter (fun M : ℕ => inWin F y Y k s M)).card
                  then (F.p : ℝ) ^ s * x ^ (1 / 2 : ℝ) else 0))
          else 2 * Y * K₁ * nb F.p k s) := by
  have hm1n : m1 x ≤ F.nZero x := le_trans hmk hk
  have hps : 0 ≤ (F.p : ℝ) ^ s := (pow_pos F.p_real_pos s).le
  rw [Finset.sum_add_distrib]
  refine add_le_add (sum_bad_le F hY.le (hK₁ k hk) G) ?_
  -- the weights of the product formula
  set e : ZMod (F.q ^ k) → ℝ := fun X => |jp F k X s - nb F.p k s *
      (F.q : ℝ) ^ ((m1 x : ℤ) - (k : ℤ)) *
      ((F.syracZ (m1 x)) (ZMod.castHom (pow_dvd_pow F.q hmk) (ZMod (F.q ^ m1 x)) X)).toReal|
    with he
  have hcast : ∀ M : ℕ, ZMod.castHom (pow_dvd_pow F.q hmk) (ZMod (F.q ^ m1 x))
      ((M : ℕ) : ZMod (F.q ^ k)) = ((M : ℕ) : ZMod (F.q ^ m1 x)) := fun M => map_natCast _ M
  by_cases hc : |(s : ℝ) - F.mu * k| ≤ rad k
  · rw [if_pos hc]
    have hrw : ∀ M : ℕ, (if inWin F y Y k s M then (F.p : ℝ) ^ s *
          |jp F k (M : ZMod (F.q ^ k)) s - nb F.p k s * (F.q : ℝ) ^ ((m1 x : ℤ) - (k : ℤ)) *
            ((F.syracZ (m1 x)) (M : ZMod (F.q ^ m1 x))).toReal| else 0)
        = (if inWin F y Y k s M then (F.p : ℝ) ^ s * e (M : ZMod (F.q ^ k)) else 0) := by
      intro M
      simp only [he, hcast]
    rw [Finset.sum_congr rfl (fun M _ => hrw M)]
    have hfib := ep2_fiber F (y := y) (Y := Y) (s := s) hflatk e (fun X => abs_nonneg _)
    have hsum : ∑ X, e X ≤ ε * β :=
      (hmixk hc).trans (mul_le_mul_of_nonneg_left hlock hε)
    set N := ((F.Eprime α x Set.univ).filter (fun M : ℕ => inWin F y Y k s M)).card
    have hco : 0 ≤ (F.p : ℝ) ^ s / (F.q : ℝ) ^ k * (N : ℝ)
        + (if 0 < N then (F.p : ℝ) ^ s * x ^ (1 / 2 : ℝ) else 0) := by
      have h1 : 0 ≤ (F.p : ℝ) ^ s / (F.q : ℝ) ^ k * (N : ℝ) :=
        mul_nonneg (div_nonneg hps (pow_pos F.q_real_pos k).le) (Nat.cast_nonneg _)
      have h2 : 0 ≤ (if 0 < N then (F.p : ℝ) ^ s * x ^ (1 / 2 : ℝ) else 0) := by
        split_ifs
        · exact mul_nonneg hps (Real.rpow_nonneg hx _)
        · exact le_refl 0
      linarith
    calc _ ≤ _ := hfib
      _ ≤ ((F.p : ℝ) ^ s / (F.q : ℝ) ^ k * (N : ℝ)
            + (if 0 < N then (F.p : ℝ) ^ s * x ^ (1 / 2 : ℝ) else 0)) * (ε * β) :=
          mul_le_mul_of_nonneg_left hsum hco
      _ = _ := by ring
  · rw [if_neg hc]
    have hle : ∀ M ∈ F.Eprime α x Set.univ, (if inWin F y Y k s M then (F.p : ℝ) ^ s *
          |jp F k (M : ZMod (F.q ^ k)) s - nb F.p k s * (F.q : ℝ) ^ ((m1 x : ℤ) - (k : ℤ)) *
            ((F.syracZ (m1 x)) (M : ZMod (F.q ^ m1 x))).toReal| else 0)
        ≤ (if inWin F y Y k s M then (F.p : ℝ) ^ s * jp F k (M : ZMod (F.q ^ k)) s else 0)
          + (if inWin F y Y k s M then (F.p : ℝ) ^ s *
              (nb F.p k s * (F.q : ℝ) ^ ((m1 x : ℤ) - (k : ℤ)) *
                ((F.syracZ (m1 x)) (M : ZMod (F.q ^ m1 x))).toReal) else 0) := by
      intro M _
      by_cases hw : inWin F y Y k s M
      · simp only [if_pos hw]
        rw [← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ hps
        have hb := jp_nonneg F k (M : ZMod (F.q ^ k)) s
        have hc0 : 0 ≤ nb F.p k s * (F.q : ℝ) ^ ((m1 x : ℤ) - (k : ℤ)) *
            ((F.syracZ (m1 x)) (M : ZMod (F.q ^ m1 x))).toReal :=
          mul_nonneg (mul_nonneg (nb_nonneg _ _ _) (zpow_nonneg F.q_real_pos.le _))
            ENNReal.toReal_nonneg
        rw [abs_le]; constructor <;> linarith
      · simp [if_neg hw]
    calc _ ≤ _ := Finset.sum_le_sum hle
      _ = _ := Finset.sum_add_distrib
      _ ≤ Y * K₁ * nb F.p k s + Y * K₁ * nb F.p k s :=
          add_le_add (sum_jp_le F hY.le (hK₁ k hk)) (sum_c_le F hY.le (hK₁ (m1 x) hm1n))
      _ = 2 * Y * K₁ * nb F.p k s := by ring

open Classical in
/-- **The sum of `p^s q^{-k} ν̄` over central `s`** (re-summing over `M`). -/
theorem sum_cenN_le {α x y Y K₁ R : ℝ} (hY : 0 < Y) (hR0 : 0 ≤ R)
    (hK0 : ∀ X : ZMod (F.q ^ 0), F.cE α x Set.univ 0 X ≤ K₁)
    (hR : ∀ n ∈ rows F α x, rad (n - F.mZero α x) ≤ R) (S : Finset ℕ) :
    ∑ n ∈ rows F α x, ∑ s ∈ S,
        (if |(s : ℝ) - F.mu * ((n - F.mZero α x : ℕ) : ℝ)| ≤ rad (n - F.mZero α x) then
          (F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - F.mZero α x) *
            (((F.Eprime α x Set.univ).filter
              (fun M : ℕ => inWin F y Y (n - F.mZero α x) s M)).card : ℝ)
        else 0)
      ≤ (F.p : ℝ) / ((F.p : ℝ) - 1) * NR F R * (Y * K₁) := by
  set m₀ := F.mZero α x
  set E0 := F.Eprime α x Set.univ
  have hp1 : 0 < (F.p : ℝ) / ((F.p : ℝ) - 1) :=
    div_pos F.p_real_pos (by linarith [F.one_lt_p_real])
  have hNR : 0 ≤ NR F R := by
    unfold NR
    have hd := F.drift_pos
    have hed : 1 < Real.exp F.drift := by have := Real.add_one_lt_exp hd.ne'; linarith
    have h1 : 0 ≤ 2 * R * Real.log F.p / F.drift :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hR0) F.log_p_pos.le) hd.le
    have h2 : 0 ≤ Real.exp F.drift / (Real.exp F.drift - 1) :=
      div_nonneg (Real.exp_pos _).le (by linarith)
    linarith
  -- turn the count into a sum over `M`
  have h1 : ∀ n ∈ rows F α x, ∀ s ∈ S,
      (if |(s : ℝ) - F.mu * ((n - m₀ : ℕ) : ℝ)| ≤ rad (n - m₀) then
          (F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - m₀) *
            ((E0.filter (fun M : ℕ => inWin F y Y (n - m₀) s M)).card : ℝ)
        else 0)
      ≤ ∑ M ∈ E0, (if inWin F y Y (n - m₀) s M ∧ |(s : ℝ) - F.mu * ((n - m₀ : ℕ) : ℝ)| ≤ R
          then (F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - m₀) else 0) := by
    intro n hn s _
    by_cases hc : |(s : ℝ) - F.mu * ((n - m₀ : ℕ) : ℝ)| ≤ rad (n - m₀)
    · rw [if_pos hc, Finset.natCast_card_filter, Finset.mul_sum]
      refine le_of_eq (Finset.sum_congr rfl fun M _ => ?_)
      by_cases hw : inWin F y Y (n - m₀) s M
      · rw [if_pos hw, if_pos ⟨hw, hc.trans (hR n hn)⟩, mul_one]
      · rw [if_neg hw, if_neg (fun h => hw h.1), mul_zero]
    · rw [if_neg hc]
      exact Finset.sum_nonneg fun M _ => by
        split_ifs
        · exact div_nonneg (pow_pos F.p_real_pos _).le (pow_pos F.q_real_pos _).le
        · exact le_refl 0
  calc _ ≤ ∑ n ∈ rows F α x, ∑ s ∈ S, ∑ M ∈ E0,
        (if inWin F y Y (n - m₀) s M ∧ |(s : ℝ) - F.mu * ((n - m₀ : ℕ) : ℝ)| ≤ R
          then (F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - m₀) else 0) :=
        Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun s hs => h1 n hn s hs
    _ = ∑ M ∈ E0, ∑ n ∈ rows F α x, ∑ s ∈ S,
        (if inWin F y Y (n - m₀) s M ∧ |(s : ℝ) - F.mu * ((n - m₀ : ℕ) : ℝ)| ≤ R
          then (F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - m₀) else 0) := by
        rw [Finset.sum_congr rfl fun n _ => Finset.sum_comm, Finset.sum_comm]
    _ ≤ ∑ M ∈ E0, (F.p : ℝ) / ((F.p : ℝ) - 1) * (Y / (M : ℝ)) * NR F R :=
        Finset.sum_le_sum fun M hM => kernC_le F hY (pos_of_mem_Eprime F hM) hR0 S
    _ = (F.p : ℝ) / ((F.p : ℝ) - 1) * NR F R * Y *
          ∑ M ∈ E0, (F.q : ℝ) ^ 0 / (M : ℝ) * (fun _ : ZMod (F.q ^ 0) => (1 : ℝ)) (M : ZMod (F.q ^ 0)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun M _ => ?_
        simp only [pow_zero]
        ring
    _ ≤ (F.p : ℝ) / ((F.p : ℝ) - 1) * NR F R * Y * (K₁ * ∑ _X : ZMod (F.q ^ 0), (1 : ℝ)) :=
        mul_le_mul_of_nonneg_left (ep1_avg F hK0 _ (fun _ => zero_le_one))
          (mul_nonneg (mul_nonneg hp1.le hNR) hY.le)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, pow_zero]
        ring

open Classical in
/-- **The `x^{1/2}` part of (EP2)** (the (P) of the accompanying paper): the sum of `p^s` over the `s` with `ν̄ ≥ 1`. -/
theorem sum_half_le {α x y Y : ℝ} {k : ℕ} (hY : 0 ≤ Y) (hk : k ≤ F.nZero x)
    (hMlo : 0 < F.Mlo α x) (S : Finset ℕ) :
    ∑ s ∈ S, (if 0 < ((F.Eprime α x Set.univ).filter (fun M : ℕ => inWin F y Y k s M)).card
        then (F.p : ℝ) ^ s else 0)
      ≤ (F.p : ℝ) / ((F.p : ℝ) - 1) * (Y * (F.q : ℝ) ^ F.nZero x / F.Mlo α x) := by
  rw [← Finset.sum_filter]
  have hq1 : (1 : ℝ) ≤ F.q := by exact_mod_cast F.q_pos
  refine geom_sum_le F.one_lt_p_real (by positivity) _ fun s hs => ?_
  obtain ⟨M, hM⟩ := Finset.card_pos.mp (Finset.mem_filter.mp hs).2
  obtain ⟨hME, hw⟩ := Finset.mem_filter.mp hM
  have hM0 := pos_of_mem_Eprime F hME
  have hMlo' := Mlo_le_of_mem_Eprime F hME
  calc (F.p : ℝ) ^ s ≤ Y * (F.q : ℝ) ^ k / M := pow_le_of_inWin F hw hM0
    _ ≤ Y * (F.q : ℝ) ^ F.nZero x / F.Mlo α x :=
        div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq1 hk) hY) hMlo hMlo'

end MasterAux

end ND

end GGMCollatz
