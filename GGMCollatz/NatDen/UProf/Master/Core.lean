import GGMCollatz.NatDen.UProf.Master.RowSum

/-!
# The deterministic core of (UM) (steps 2–4 of the master formula, the bound at fixed `x`)

Fix `x`, take (EP1), (EP2), the good-tuple tail, the product formula, the tail outside the centre and the local bound as hypotheses,
and show `|Σ_n umain(n) - kernSum| ≤ Y · (sum of four errors)`. The four errors are

1. the cost of removing the good-tuple restriction, `K₁ (n₀+1) δ` (the averaged form of (EP1); the weight is bounded by `p^s ≤ Y q^k/M`),
2. the cost of discarding non-central `s` and returning to the kernel, `2 K₁ (n₀+1) τ` ((EP1), twice: with `k` and with `k = m₁`),
3. the main part of the product-formula error, `ε β (p/(p-1)) N_R K₁` (the flatness (EP2), the kernel `kernC_le` restricted to the centre, (EP1) with `k = 0`),
4. the `x^{1/2}` part of (EP2) (the (P) of the accompanying paper), `ε β x^{1/2} (n₀+1) (p/(p-1)) q^{n₀}/Mlo`.

By the upper end of the window `p^s M/q^k ≤ Y` (`M ≥ 1`), the sum over `s` is a finite sum over `s < ⌈Y q^{n₀}⌉`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace MasterAux

variable (F : Family)

/-- For `s ≥ ⌈Y q^{n₀}⌉` the window is not entered (`M ≥ 1`, `k ≤ n₀`, `p^s > s`). -/
theorem not_inWin_of_ge {y Y : ℝ} {k n₀ s : ℕ} {M : ℝ} (hY : 0 ≤ Y) (hM : 1 ≤ M)
    (hk : k ≤ n₀) (hs : ⌈Y * (F.q : ℝ) ^ n₀⌉₊ ≤ s) : ¬ inWin F y Y k s M := by
  intro h
  have hq : 0 < (F.q : ℝ) ^ k := pow_pos F.q_real_pos k
  have hq1 : (1 : ℝ) ≤ F.q := by exact_mod_cast F.q_pos
  have h1 : Y * (F.q : ℝ) ^ n₀ ≤ s := Nat.ceil_le.mp hs
  have h2 : (s : ℝ) < (F.p : ℝ) ^ s := by
    have := Nat.lt_pow_self (n := s) (show 1 < F.p by have := F.two_le_p; omega)
    exact_mod_cast this
  have h3 : Y * (F.q : ℝ) ^ k ≤ Y * (F.q : ℝ) ^ n₀ :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq1 hk) hY
  have h5 := h.2
  rw [div_le_iff₀ hq] at h5
  have h6 : (F.p : ℝ) ^ s ≤ (F.p : ℝ) ^ s * M :=
    le_mul_of_one_le_right (pow_pos F.p_real_pos s).le hM
  linarith

open Classical in
/-- The sum over `s` with the window indicator is a finite sum. -/
theorem tsum_win_eq {y Y : ℝ} {k n₀ : ℕ} {M : ℝ} (hY : 0 ≤ Y) (hM : 1 ≤ M) (hk : k ≤ n₀)
    (f : ℕ → ℝ) :
    ∑' s : ℕ, (if inWin F y Y k s M then f s else 0)
      = ∑ s ∈ Finset.range ⌈Y * (F.q : ℝ) ^ n₀⌉₊, (if inWin F y Y k s M then f s else 0) := by
  apply tsum_eq_sum
  intro s hs
  rw [Finset.mem_range, not_lt] at hs
  rw [if_neg (not_inWin_of_ge F hY hM hk hs)]

/-- The elements of `E'` are at least 1. -/
theorem one_le_of_mem_Eprime {α x : ℝ} {E : Set ℕ} {M : ℕ} (hM : M ∈ F.Eprime α x E) :
    (1 : ℝ) ≤ M := by
  have h := pos_of_mem_Eprime F hM
  have : 0 < M := by exact_mod_cast h
  exact_mod_cast this

/-- The range of rows. -/
theorem mem_rows {α x : ℝ} {n : ℕ} (hn : n ∈ rows F α x) :
    F.mZero α x ≤ n - F.mZero α x ∧ n - F.mZero α x ≤ F.nZero x := by
  simp only [rows, Finset.mem_Icc] at hn
  omega

open Classical in
/-- The sum of the main terms written as a finite sum. -/
theorem sum_umain_eq {α x : ℝ} (E : Set ℕ) (hY : 0 ≤ (x ^ α) ^ α) :
    ∑ n ∈ rows F α x, umain F α x E n
      = ∑ M ∈ F.Eprime α x E, ∑ n ∈ rows F α x,
          ∑ s ∈ Finset.range ⌈(x ^ α) ^ α * (F.q : ℝ) ^ F.nZero x⌉₊,
            (if inWin F (x ^ α) ((x ^ α) ^ α) (n - F.mZero α x) s M then
              (F.p : ℝ) ^ s * jpG F (n - F.mZero α x) (M : ZMod (F.q ^ (n - F.mZero α x))) s
                (fun a => F.goodVec x a) else 0) := by
  unfold umain
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun M hM => Finset.sum_congr rfl fun n hn => ?_
  exact tsum_win_eq F hY (one_le_of_mem_Eprime F hM) (mem_rows F hn).2 _

open Classical in
/-- The kernel-weighted sum written as a finite sum. -/
theorem kernSum_eq {α x : ℝ} (E : Set ℕ) (hY : 0 ≤ (x ^ α) ^ α) :
    kernSum F α x E
      = ∑ M ∈ F.Eprime α x E, ∑ n ∈ rows F α x,
          ∑ s ∈ Finset.range ⌈(x ^ α) ^ α * (F.q : ℝ) ^ F.nZero x⌉₊,
            (F.q : ℝ) ^ m1 x * ((F.syracZ (m1 x)) (M : ZMod (F.q ^ m1 x))).toReal *
              (if inWin F (x ^ α) ((x ^ α) ^ α) (n - F.mZero α x) s M then
                (F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - F.mZero α x) * nb F.p (n - F.mZero α x) s
              else 0) := by
  unfold kernSum kern
  refine Finset.sum_congr rfl fun M hM => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [tsum_win_eq F hY (one_le_of_mem_Eprime F hM) (mem_rows F hn).2, Finset.mul_sum]

open Classical in
/-- The error term `U₁ + U₂` (the right-hand side of `term_le`). -/
noncomputable def tU (α x : ℝ) (M n s : ℕ) : ℝ :=
  (if inWin F (x ^ α) ((x ^ α) ^ α) (n - F.mZero α x) s M then (F.p : ℝ) ^ s *
      (jp F (n - F.mZero α x) (M : ZMod (F.q ^ (n - F.mZero α x))) s
        - jpG F (n - F.mZero α x) (M : ZMod (F.q ^ (n - F.mZero α x))) s
            (fun a => F.goodVec x a)) else 0)
    + (if inWin F (x ^ α) ((x ^ α) ^ α) (n - F.mZero α x) s M then (F.p : ℝ) ^ s *
      |jp F (n - F.mZero α x) (M : ZMod (F.q ^ (n - F.mZero α x))) s
        - nb F.p (n - F.mZero α x) s * (F.q : ℝ) ^ ((m1 x : ℤ) - ((n - F.mZero α x : ℕ) : ℤ)) *
          ((F.syracZ (m1 x)) (M : ZMod (F.q ^ m1 x))).toReal| else 0)

theorem tU_nonneg (α x : ℝ) (M n s : ℕ) : 0 ≤ tU F α x M n s := by
  unfold tU
  have hps : 0 ≤ (F.p : ℝ) ^ s := (pow_pos F.p_real_pos s).le
  have h1 := jpG_le_true F (n - F.mZero α x) (M : ZMod (F.q ^ (n - F.mZero α x))) s
    (fun a => F.goodVec x a)
  apply add_nonneg
  · split_ifs
    · exact mul_nonneg hps (by linarith)
    · exact le_refl 0
  · split_ifs
    · exact mul_nonneg hps (abs_nonneg _)
    · exact le_refl 0

open Classical in
/-- **The sum over `s` and `n`** (the four parts of the error). -/
theorem sum_rows_le {α x : ℝ} {K₁ ε β τ δ R : ℝ}
    (hx : 0 ≤ x) (hY : 0 < (x ^ α) ^ α) (hMlo : 0 < F.Mlo α x)
    (hK₁ : ∀ j ≤ F.nZero x, ∀ X : ZMod (F.q ^ j), F.cE α x Set.univ j X ≤ K₁)
    (hgood : ∀ k ≤ F.nZero x,
      Family.expect ((geomP F.p).iid k) (Set.indicator {a | ¬ F.goodVec x a} 1) ≤ δ)
    (htail : ∀ k, F.mZero α x ≤ k → k ≤ F.nZero x → ∀ S : Finset ℕ,
        ∑ s ∈ S.filter (fun s : ℕ => ¬ |(s : ℝ) - F.mu * k| ≤ rad k), nb F.p k s ≤ τ)
    (hR : ∀ k, k ≤ F.nZero x → rad k ≤ R)
    (hK₁0 : 0 ≤ K₁) (hε : 0 ≤ ε) (hβ : 0 ≤ β) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (hR0 : 0 ≤ R)
    (S : Finset ℕ) :
    ∑ n ∈ rows F α x, ∑ s ∈ S,
        ((x ^ α) ^ α * K₁ * pG F (n - F.mZero α x) s (fun a => ¬ F.goodVec x a)
          + (if |(s : ℝ) - F.mu * ((n - F.mZero α x : ℕ) : ℝ)| ≤ rad (n - F.mZero α x) then
              ε * β * ((F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - F.mZero α x) *
                  (((F.Eprime α x Set.univ).filter (fun M : ℕ =>
                    inWin F (x ^ α) ((x ^ α) ^ α) (n - F.mZero α x) s M)).card : ℝ)
                + (if 0 < ((F.Eprime α x Set.univ).filter (fun M : ℕ =>
                      inWin F (x ^ α) ((x ^ α) ^ α) (n - F.mZero α x) s M)).card
                    then (F.p : ℝ) ^ s * x ^ (1 / 2 : ℝ) else 0))
            else 2 * (x ^ α) ^ α * K₁ * nb F.p (n - F.mZero α x) s))
      ≤ (x ^ α) ^ α * (K₁ * ((F.nZero x : ℝ) + 1) * δ + 2 * K₁ * ((F.nZero x : ℝ) + 1) * τ
          + ε * β * ((F.p : ℝ) / ((F.p : ℝ) - 1)) * NR F R * K₁
          + ε * β * x ^ (1 / 2 : ℝ) * ((F.nZero x : ℝ) + 1) * ((F.p : ℝ) / ((F.p : ℝ) - 1))
              * (F.q : ℝ) ^ F.nZero x / F.Mlo α x) := by
  set Y := (x ^ α) ^ α with hYdef
  set m₀ := F.mZero α x with hm₀
  set n₀ := F.nZero x with hn₀
  set E0 := F.Eprime α x Set.univ with hE0
  have hp1 : 0 < (F.p : ℝ) / ((F.p : ℝ) - 1) :=
    div_pos F.p_real_pos (by linarith [F.one_lt_p_real])
  have hxh : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx _
  set H := (F.p : ℝ) / ((F.p : ℝ) - 1) * (Y * (F.q : ℝ) ^ n₀ / F.Mlo α x) with hH
  have hH0 : 0 ≤ H := mul_nonneg hp1.le (div_nonneg (mul_nonneg hY.le (by positivity)) hMlo.le)
  -- the `ν̄` part for central `s` (a sum also over `n`)
  set cen : ℕ → ℕ → Prop := fun n s =>
    |(s : ℝ) - F.mu * ((n - m₀ : ℕ) : ℝ)| ≤ rad (n - m₀) with hcen
  set Nc : ℕ → ℕ → ℕ := fun n s =>
    (E0.filter (fun M : ℕ => inWin F (x ^ α) Y (n - m₀) s M)).card with hNc
  -- the bound for each row
  have hrow : ∀ n ∈ rows F α x, ∑ s ∈ S,
      (Y * K₁ * pG F (n - m₀) s (fun a => ¬ F.goodVec x a)
        + (if cen n s then
            ε * β * ((F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - m₀) * (Nc n s : ℝ)
              + (if 0 < Nc n s then (F.p : ℝ) ^ s * x ^ (1 / 2 : ℝ) else 0))
          else 2 * Y * K₁ * nb F.p (n - m₀) s))
      ≤ Y * K₁ * δ + 2 * Y * K₁ * τ + ε * β * x ^ (1 / 2 : ℝ) * H
        + ε * β * ∑ s ∈ S, (if cen n s then
            (F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - m₀) * (Nc n s : ℝ) else 0) := by
    intro n hn
    obtain ⟨hk0, hk1⟩ := mem_rows F hn
    have hsplit : ∀ s, (if cen n s then
            ε * β * ((F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - m₀) * (Nc n s : ℝ)
              + (if 0 < Nc n s then (F.p : ℝ) ^ s * x ^ (1 / 2 : ℝ) else 0))
          else 2 * Y * K₁ * nb F.p (n - m₀) s)
        ≤ ε * β * (if cen n s then (F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - m₀) * (Nc n s : ℝ) else 0)
          + ε * β * x ^ (1 / 2 : ℝ) * (if 0 < Nc n s then (F.p : ℝ) ^ s else 0)
          + 2 * Y * K₁ * (if cen n s then 0 else nb F.p (n - m₀) s) := by
      intro s
      have hps : 0 ≤ (F.p : ℝ) ^ s := (pow_pos F.p_real_pos s).le
      have hεβ : 0 ≤ ε * β := mul_nonneg hε hβ
      by_cases hc : cen n s
      · simp only [if_pos hc, mul_zero, add_zero]
        split_ifs
        · ring_nf; exact le_refl _
        · have : 0 ≤ ε * β * x ^ (1 / 2 : ℝ) * 0 := by simp
          nlinarith
      · simp only [if_neg hc, mul_zero, zero_add]
        have : 0 ≤ ε * β * x ^ (1 / 2 : ℝ) * (if 0 < Nc n s then (F.p : ℝ) ^ s else 0) := by
          apply mul_nonneg (mul_nonneg hεβ hxh)
          split_ifs
          · exact hps
          · exact le_refl 0
        linarith
    calc _ ≤ ∑ s ∈ S, (Y * K₁ * pG F (n - m₀) s (fun a => ¬ F.goodVec x a)
            + (ε * β * (if cen n s then (F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - m₀) * (Nc n s : ℝ) else 0)
              + ε * β * x ^ (1 / 2 : ℝ) * (if 0 < Nc n s then (F.p : ℝ) ^ s else 0)
              + 2 * Y * K₁ * (if cen n s then 0 else nb F.p (n - m₀) s))) :=
          Finset.sum_le_sum fun s _ => add_le_add (le_refl _) (hsplit s)
      _ = Y * K₁ * ∑ s ∈ S, pG F (n - m₀) s (fun a => ¬ F.goodVec x a)
          + ε * β * ∑ s ∈ S, (if cen n s then
              (F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - m₀) * (Nc n s : ℝ) else 0)
          + ε * β * x ^ (1 / 2 : ℝ) * ∑ s ∈ S, (if 0 < Nc n s then (F.p : ℝ) ^ s else 0)
          + 2 * Y * K₁ * ∑ s ∈ S, (if cen n s then 0 else nb F.p (n - m₀) s) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
          ring
      _ ≤ Y * K₁ * δ
          + ε * β * ∑ s ∈ S, (if cen n s then
              (F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - m₀) * (Nc n s : ℝ) else 0)
          + ε * β * x ^ (1 / 2 : ℝ) * H
          + 2 * Y * K₁ * τ := by
          have h1 : ∑ s ∈ S, pG F (n - m₀) s (fun a => ¬ F.goodVec x a) ≤ δ :=
            (sum_pG_le F _ _ S).trans (hgood _ hk1)
          have h2 : ∑ s ∈ S, (if 0 < Nc n s then (F.p : ℝ) ^ s else 0) ≤ H :=
            sum_half_le F hY.le hk1 hMlo S
          have h3 : ∑ s ∈ S, (if cen n s then 0 else nb F.p (n - m₀) s) ≤ τ := by
            refine le_trans (le_of_eq ?_) (htail _ hk0 hk1 S)
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun s _ => ?_
            by_cases hc : cen n s
            · rw [if_pos hc, if_neg (not_not.mpr hc)]
            · rw [if_neg hc, if_pos hc]
          have hεβ : 0 ≤ ε * β := mul_nonneg hε hβ
          have hYK : 0 ≤ Y * K₁ := mul_nonneg hY.le hK₁0
          have e1 := mul_le_mul_of_nonneg_left h1 hYK
          have e2 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hεβ hxh)
          have e3 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * Y * K₁)
          linarith
      _ = _ := by ring
  have hcard : ((rows F α x).card : ℝ) ≤ (n₀ : ℝ) + 1 := by
    have : (rows F α x).card ≤ n₀ + 1 := by
      unfold rows; rw [Nat.card_Icc]; omega
    exact_mod_cast this
  have hconst : 0 ≤ Y * K₁ * δ + 2 * Y * K₁ * τ + ε * β * x ^ (1 / 2 : ℝ) * H := by
    have hεβ : 0 ≤ ε * β := mul_nonneg hε hβ
    positivity
  have hcN := sum_cenN_le F (y := x ^ α) (Y := Y) hY hR0 (hK₁ 0 (Nat.zero_le _))
    (fun n hn => hR _ (mem_rows F hn).2) S
  calc _ ≤ ∑ n ∈ rows F α x, (Y * K₁ * δ + 2 * Y * K₁ * τ + ε * β * x ^ (1 / 2 : ℝ) * H
          + ε * β * ∑ s ∈ S, (if cen n s then
              (F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - m₀) * (Nc n s : ℝ) else 0)) :=
        Finset.sum_le_sum hrow
    _ = ((rows F α x).card : ℝ) * (Y * K₁ * δ + 2 * Y * K₁ * τ + ε * β * x ^ (1 / 2 : ℝ) * H)
          + ε * β * ∑ n ∈ rows F α x, ∑ s ∈ S, (if cen n s then
              (F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - m₀) * (Nc n s : ℝ) else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    _ ≤ ((n₀ : ℝ) + 1) * (Y * K₁ * δ + 2 * Y * K₁ * τ + ε * β * x ^ (1 / 2 : ℝ) * H)
          + ε * β * ((F.p : ℝ) / ((F.p : ℝ) - 1) * NR F R * (Y * K₁)) :=
        add_le_add (mul_le_mul_of_nonneg_right hcard hconst)
          (mul_le_mul_of_nonneg_left hcN (mul_nonneg hε hβ))
    _ = _ := by rw [hH]; ring

open Classical in
/-- **The deterministic core of (UM)**. -/
theorem core {α x : ℝ} (E : Set ℕ) {K₁ ε β τ δ R : ℝ}
    (hx : 0 ≤ x) (hY : 0 < (x ^ α) ^ α) (hMlo : 0 < F.Mlo α x)
    (hK₁ : ∀ j ≤ F.nZero x, ∀ X : ZMod (F.q ^ j), F.cE α x Set.univ j X ≤ K₁)
    (hflat : ∀ k ≤ F.nZero x, ∀ X : ZMod (F.q ^ k), ∀ A B : ℝ,
      |(((F.Eprime α x Set.univ).filter (fun M : ℕ =>
            A < (M : ℝ) ∧ (M : ℝ) ≤ B ∧ ((M : ℕ) : ZMod (F.q ^ k)) = X)).card : ℝ)
        - (F.q : ℝ) ^ (-(k : ℤ)) *
          (((F.Eprime α x Set.univ).filter (fun M : ℕ => A < (M : ℝ) ∧ (M : ℝ) ≤ B)).card : ℝ)|
        ≤ x ^ (1 / 2 : ℝ))
    (hgood : ∀ k ≤ F.nZero x,
      Family.expect ((geomP F.p).iid k) (Set.indicator {a | ¬ F.goodVec x a} 1) ≤ δ)
    (hm1 : m1 x ≤ F.mZero α x)
    (hmix : ∀ k (hk : m1 x ≤ k), F.mZero α x ≤ k → k ≤ F.nZero x → ∀ s : ℕ,
        |(s : ℝ) - F.mu * k| ≤ rad k →
        ∑ X : ZMod (F.q ^ k), |jp F k X s - nb F.p k s * (F.q : ℝ) ^ ((m1 x : ℤ) - (k : ℤ)) *
            ((F.syracZ (m1 x)) (ZMod.castHom (pow_dvd_pow F.q hk) (ZMod (F.q ^ m1 x)) X)).toReal|
          ≤ ε * nb F.p k s)
    (htail : ∀ k, F.mZero α x ≤ k → k ≤ F.nZero x → ∀ S : Finset ℕ,
        ∑ s ∈ S.filter (fun s : ℕ => ¬ |(s : ℝ) - F.mu * k| ≤ rad k), nb F.p k s ≤ τ)
    (hloc : ∀ k, F.mZero α x ≤ k → k ≤ F.nZero x → ∀ s, nb F.p k s ≤ β)
    (hR : ∀ k, k ≤ F.nZero x → rad k ≤ R)
    (hK₁0 : 0 ≤ K₁) (hε : 0 ≤ ε) (hβ : 0 ≤ β) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (hR0 : 0 ≤ R) :
    |∑ n ∈ rows F α x, umain F α x E n - kernSum F α x E|
      ≤ (x ^ α) ^ α * (K₁ * ((F.nZero x : ℝ) + 1) * δ + 2 * K₁ * ((F.nZero x : ℝ) + 1) * τ
          + ε * β * ((F.p : ℝ) / ((F.p : ℝ) - 1)) * NR F R * K₁
          + ε * β * x ^ (1 / 2 : ℝ) * ((F.nZero x : ℝ) + 1) * ((F.p : ℝ) / ((F.p : ℝ) - 1))
              * (F.q : ℝ) ^ F.nZero x / F.Mlo α x) := by
  have hEE : F.Eprime α x E ⊆ F.Eprime α x Set.univ := F.Eprime_mono α x (Set.subset_univ E)
  set SR := Finset.range ⌈(x ^ α) ^ α * (F.q : ℝ) ^ F.nZero x⌉₊ with hSR
  rw [sum_umain_eq F E hY.le, kernSum_eq F E hY.le, ← Finset.sum_sub_distrib]
  -- pointwise triangle inequality
  have hD : ∀ M ∈ F.Eprime α x E,
      |∑ n ∈ rows F α x, ∑ s ∈ SR,
          (if inWin F (x ^ α) ((x ^ α) ^ α) (n - F.mZero α x) s M then
            (F.p : ℝ) ^ s * jpG F (n - F.mZero α x) (M : ZMod (F.q ^ (n - F.mZero α x))) s
              (fun a => F.goodVec x a) else 0)
        - ∑ n ∈ rows F α x, ∑ s ∈ SR,
          (F.q : ℝ) ^ m1 x * ((F.syracZ (m1 x)) (M : ZMod (F.q ^ m1 x))).toReal *
            (if inWin F (x ^ α) ((x ^ α) ^ α) (n - F.mZero α x) s M then
              (F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - F.mZero α x) * nb F.p (n - F.mZero α x) s
            else 0)|
        ≤ ∑ n ∈ rows F α x, ∑ s ∈ SR, tU F α x M n s := by
    intro M _
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    exact term_le F (jpG_le_true F _ _ _ _)
  calc _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ M ∈ F.Eprime α x E, ∑ n ∈ rows F α x, ∑ s ∈ SR, tU F α x M n s :=
        Finset.sum_le_sum hD
    _ ≤ ∑ M ∈ F.Eprime α x Set.univ, ∑ n ∈ rows F α x, ∑ s ∈ SR, tU F α x M n s :=
        Finset.sum_le_sum_of_subset_of_nonneg hEE (fun M _ _ =>
          Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun s _ => tU_nonneg F α x M n s)
    _ = ∑ n ∈ rows F α x, ∑ s ∈ SR, ∑ M ∈ F.Eprime α x Set.univ, tU F α x M n s := by
        rw [Finset.sum_comm, Finset.sum_congr rfl fun n _ => Finset.sum_comm]
    _ ≤ ∑ n ∈ rows F α x, ∑ s ∈ SR,
        ((x ^ α) ^ α * K₁ * pG F (n - F.mZero α x) s (fun a => ¬ F.goodVec x a)
          + (if |(s : ℝ) - F.mu * ((n - F.mZero α x : ℕ) : ℝ)| ≤ rad (n - F.mZero α x) then
              ε * β * ((F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - F.mZero α x) *
                  (((F.Eprime α x Set.univ).filter (fun M : ℕ =>
                    inWin F (x ^ α) ((x ^ α) ^ α) (n - F.mZero α x) s M)).card : ℝ)
                + (if 0 < ((F.Eprime α x Set.univ).filter (fun M : ℕ =>
                      inWin F (x ^ α) ((x ^ α) ^ α) (n - F.mZero α x) s M)).card
                    then (F.p : ℝ) ^ s * x ^ (1 / 2 : ℝ) else 0))
            else 2 * (x ^ α) ^ α * K₁ * nb F.p (n - F.mZero α x) s)) := by
        refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun s _ => ?_
        obtain ⟨hk0, hk1⟩ := mem_rows F hn
        have hmk : m1 x ≤ n - F.mZero α x := le_trans hm1 hk0
        exact row_bound F hx hY hk1 hmk hK₁ (hflat _ hk1) (hmix _ hmk hk0 hk1 s)
          (hloc _ hk0 hk1 s) hε (fun a => F.goodVec x a)
    _ ≤ _ := sum_rows_le F hx hY hMlo hK₁ hgood htail hR hK₁0 hε hβ hτ hδ hR0 SR

end MasterAux

end ND

end GGMCollatz
