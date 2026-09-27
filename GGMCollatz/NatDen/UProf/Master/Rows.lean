import GGMCollatz.NatDen.UProf.Master.Count

/-!
# Ingredients of (UM): the bound for each row `n` and sum `s` (the individual terms of steps 2–4 of the master formula)

With `k = n - m₀` and `s` fixed, we bound the sum over `M ∈ E'` (all of it). Write `a = P(Σa = s, F_k ≡ M, good tuple)`,
`b = P(Σa = s, F_k ≡ M)`, `c = P(s_k = s) q^{m₁ - k} ω_{m₁}(M)`.

* `term_le`: pointwise, `|p^s a - q^{m₁} ω (p^s/q^k) nb| ≤ p^s (b - a) + p^s |b - c|` (inside the window).
* `sum_bad_le`: `Σ_M 1[window] p^s (b - a) ≤ Y K₁ P(Σa = s, not good)` (the average of (EP1); the central part of step 2 of the paper,
  done directly without dividing by `P(s_k = s)`).
* `sum_jp_le`, `sum_c_le`: for non-central `s`, the sums of `b` and of `c` are at most `Y K₁ P(s_k = s)` (the second half of step 2 and step 4 of the paper).
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace MasterAux

variable (F : Family)

/-- The elements of `E'` are positive. -/
theorem pos_of_mem_Eprime {α x : ℝ} {E : Set ℕ} {M : ℕ} (hM : M ∈ F.Eprime α x E) :
    (0 : ℝ) < M := by
  simp only [Family.Eprime, Finset.mem_filter] at hM
  have h := hM.2.1
  have : M ≠ 0 := fun h0 => h (by simp [h0])
  exact_mod_cast Nat.pos_of_ne_zero this

/-- The elements of `E'` are at least `Mlo`. -/
theorem Mlo_le_of_mem_Eprime {α x : ℝ} {E : Set ℕ} {M : ℕ} (hM : M ∈ F.Eprime α x E) :
    F.Mlo α x ≤ (M : ℝ) := by
  simp only [Family.Eprime, Finset.mem_filter] at hM
  exact hM.2.2.1

/-- `jpG(True) ≥ jpG(G)`. -/
theorem jpG_le_true (k : ℕ) (X : ZMod (F.q ^ k)) (s : ℕ) (G : (Fin k → ℕ) → Prop) :
    jpG F k X s G ≤ jp F k X s := by
  rw [jp_eq_jpG_true]
  have h := jpG_true_sub F k X s G
  have h0 := jpG_nonneg F k X s (fun a => ¬ G a)
  linarith

/-- `q^{m₁} ω (p^s/q^k) nb = p^s (nb q^{m₁ - k} ω)`. -/
theorem kern_term_eq (k m s : ℕ) (w : ℝ) :
    (F.q : ℝ) ^ m * w * ((F.p : ℝ) ^ s / (F.q : ℝ) ^ k * nb F.p k s)
      = (F.p : ℝ) ^ s * (nb F.p k s * (F.q : ℝ) ^ ((m : ℤ) - (k : ℤ)) * w) := by
  have hq : (F.q : ℝ) ≠ 0 := F.q_real_pos.ne'
  rw [zpow_sub₀ hq, zpow_natCast, zpow_natCast]
  field_simp

open Classical in
/-- **Pointwise bound** (triangle inequality). -/
theorem term_le {y Y : ℝ} {k m s : ℕ} {M : ℝ} {a b w : ℝ} (hab : a ≤ b) :
    |(if inWin F y Y k s M then (F.p : ℝ) ^ s * a else 0)
        - (F.q : ℝ) ^ m * w *
          (if inWin F y Y k s M then (F.p : ℝ) ^ s / (F.q : ℝ) ^ k * nb F.p k s else 0)|
      ≤ (if inWin F y Y k s M then (F.p : ℝ) ^ s * (b - a) else 0)
        + (if inWin F y Y k s M then (F.p : ℝ) ^ s *
            |b - nb F.p k s * (F.q : ℝ) ^ ((m : ℤ) - (k : ℤ)) * w| else 0) := by
  have hps : 0 ≤ (F.p : ℝ) ^ s := (pow_pos F.p_real_pos s).le
  by_cases hw : inWin F y Y k s M
  · simp only [if_pos hw]
    rw [kern_term_eq, ← mul_sub, abs_mul, abs_of_nonneg hps, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hps
    set c := nb F.p k s * (F.q : ℝ) ^ ((m : ℤ) - (k : ℤ)) * w
    calc |a - c| ≤ |a - b| + |b - c| := abs_sub_le a b c
      _ = (b - a) + |b - c| := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  · simp [if_neg hw]

open Classical in
/-- **Removing the weight `p^s` by (EP1)**: if `g ≥ 0` then `Σ_M 1[window] p^s g(M mod q^k) ≤ Y K₁ Σ_X g(X)`. -/
theorem sum_win_le {α x y Y K₁ : ℝ} {k s : ℕ} (hY : 0 ≤ Y)
    (hK : ∀ X : ZMod (F.q ^ k), F.cE α x Set.univ k X ≤ K₁)
    (g : ZMod (F.q ^ k) → ℝ) (hg : ∀ X, 0 ≤ g X) :
    ∑ M ∈ F.Eprime α x Set.univ,
        (if inWin F y Y k s M then (F.p : ℝ) ^ s * g (M : ZMod (F.q ^ k)) else 0)
      ≤ Y * K₁ * ∑ X, g X := by
  have hq : 0 < (F.q : ℝ) ^ k := pow_pos F.q_real_pos k
  calc _ ≤ ∑ M ∈ F.Eprime α x Set.univ, Y * ((F.q : ℝ) ^ k / (M : ℝ) * g (M : ZMod (F.q ^ k))) := by
        refine Finset.sum_le_sum fun M hM => ?_
        have hM0 := pos_of_mem_Eprime F hM
        by_cases hw : inWin F y Y k s M
        · rw [if_pos hw]
          have h1 := pow_le_of_inWin F hw hM0
          calc (F.p : ℝ) ^ s * g (M : ZMod (F.q ^ k))
              ≤ Y * (F.q : ℝ) ^ k / M * g (M : ZMod (F.q ^ k)) :=
                mul_le_mul_of_nonneg_right h1 (hg _)
            _ = _ := by ring
        · rw [if_neg hw]
          exact mul_nonneg hY (mul_nonneg (div_nonneg hq.le hM0.le) (hg _))
    _ = Y * ∑ M ∈ F.Eprime α x Set.univ, (F.q : ℝ) ^ k / (M : ℝ) * g (M : ZMod (F.q ^ k)) := by
        rw [Finset.mul_sum]
    _ ≤ Y * (K₁ * ∑ X, g X) := mul_le_mul_of_nonneg_left (ep1_avg F hK g hg) hY
    _ = _ := by ring

open Classical in
/-- **The cost of removing the good-tuple restriction**. -/
theorem sum_bad_le {α x y Y K₁ : ℝ} {k s : ℕ} (hY : 0 ≤ Y)
    (hK : ∀ X : ZMod (F.q ^ k), F.cE α x Set.univ k X ≤ K₁) (G : (Fin k → ℕ) → Prop) :
    ∑ M ∈ F.Eprime α x Set.univ,
        (if inWin F y Y k s M then (F.p : ℝ) ^ s *
          (jp F k (M : ZMod (F.q ^ k)) s - jpG F k (M : ZMod (F.q ^ k)) s G) else 0)
      ≤ Y * K₁ * pG F k s (fun a => ¬ G a) := by
  have hrw : ∀ X : ZMod (F.q ^ k), jp F k X s - jpG F k X s G = jpG F k X s (fun a => ¬ G a) :=
    fun X => by rw [jp_eq_jpG_true, jpG_true_sub]
  simp only [hrw]
  rw [← sum_jpG]
  exact sum_win_le F hY hK _ (fun X => jpG_nonneg F k X s _)

open Classical in
/-- The sum of `b` over non-central `s`. -/
theorem sum_jp_le {α x y Y K₁ : ℝ} {k s : ℕ} (hY : 0 ≤ Y)
    (hK : ∀ X : ZMod (F.q ^ k), F.cE α x Set.univ k X ≤ K₁) :
    ∑ M ∈ F.Eprime α x Set.univ,
        (if inWin F y Y k s M then (F.p : ℝ) ^ s * jp F k (M : ZMod (F.q ^ k)) s else 0)
      ≤ Y * K₁ * nb F.p k s := by
  rw [← sum_jp]
  exact sum_win_le F hY hK _ (fun X => jp_nonneg F k X s)

open Classical in
/-- The sum of `c` over non-central `s` (the cost of returning to the kernel; (EP1) with `k = m₁`). -/
theorem sum_c_le {α x y Y K₁ : ℝ} {k m s : ℕ} (hY : 0 ≤ Y)
    (hK : ∀ X : ZMod (F.q ^ m), F.cE α x Set.univ m X ≤ K₁) :
    ∑ M ∈ F.Eprime α x Set.univ,
        (if inWin F y Y k s M then (F.p : ℝ) ^ s *
          (nb F.p k s * (F.q : ℝ) ^ ((m : ℤ) - (k : ℤ)) *
            ((F.syracZ m) (M : ZMod (F.q ^ m))).toReal) else 0)
      ≤ Y * K₁ * nb F.p k s := by
  have hq : 0 < (F.q : ℝ) ^ k := pow_pos F.q_real_pos k
  have hqne : (F.q : ℝ) ≠ 0 := F.q_real_pos.ne'
  have hnb := nb_nonneg F.p k s
  have hzq : (F.q : ℝ) ^ k * (F.q : ℝ) ^ ((m : ℤ) - (k : ℤ)) = (F.q : ℝ) ^ m := by
    rw [zpow_sub₀ hqne, zpow_natCast, zpow_natCast]; field_simp
  have hzq0 : 0 ≤ (F.q : ℝ) ^ ((m : ℤ) - (k : ℤ)) := zpow_nonneg F.q_real_pos.le _
  calc _ ≤ ∑ M ∈ F.Eprime α x Set.univ, Y * nb F.p k s *
          ((F.q : ℝ) ^ m / (M : ℝ) * ((F.syracZ m) (M : ZMod (F.q ^ m))).toReal) := by
        refine Finset.sum_le_sum fun M hM => ?_
        have hM0 := pos_of_mem_Eprime F hM
        have hω : 0 ≤ ((F.syracZ m) (M : ZMod (F.q ^ m))).toReal := ENNReal.toReal_nonneg
        by_cases hw : inWin F y Y k s M
        · rw [if_pos hw]
          have h1 := pow_le_of_inWin F hw hM0
          calc (F.p : ℝ) ^ s * (nb F.p k s * (F.q : ℝ) ^ ((m : ℤ) - (k : ℤ)) *
                ((F.syracZ m) (M : ZMod (F.q ^ m))).toReal)
              ≤ Y * (F.q : ℝ) ^ k / M * (nb F.p k s * (F.q : ℝ) ^ ((m : ℤ) - (k : ℤ)) *
                ((F.syracZ m) (M : ZMod (F.q ^ m))).toReal) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = Y * nb F.p k s * (((F.q : ℝ) ^ k * (F.q : ℝ) ^ ((m : ℤ) - (k : ℤ))) / M *
                ((F.syracZ m) (M : ZMod (F.q ^ m))).toReal) := by ring
            _ = _ := by rw [hzq]
        · rw [if_neg hw]
          exact mul_nonneg (mul_nonneg hY hnb) (mul_nonneg (div_nonneg (by positivity) hM0.le) hω)
    _ = Y * nb F.p k s * ∑ M ∈ F.Eprime α x Set.univ,
          (F.q : ℝ) ^ m / (M : ℝ) * ((F.syracZ m) (M : ZMod (F.q ^ m))).toReal := by
        rw [Finset.mul_sum]
    _ ≤ Y * nb F.p k s * (K₁ * ∑ X, ((F.syracZ m) X).toReal) :=
        mul_le_mul_of_nonneg_left (ep1_avg F hK _ (fun X => ENNReal.toReal_nonneg))
          (mul_nonneg hY hnb)
    _ = Y * K₁ * nb F.p k s := by rw [F.sum_syracZ_toReal_eq_one]; ring

end MasterAux

end ND

end GGMCollatz
