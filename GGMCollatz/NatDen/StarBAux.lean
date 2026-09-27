import GGMCollatz.NatDen.TopConv

/-!
# Auxiliary results for the assembly of (B)

* `count_seed`: from the seed (Theorem 4.1 of the paper), `#{N ∈ ℕ_p ∩ [1, X] | S_min(N) > N₀} ≤ C_B X (ℓ_max+1)² (L+1) e^{-c_B L}`
  (`ℓ_max = ⌊log_p ⌊X⌋⌋`, `L = ⌊log_p N₀⌋`). The shell-by-shell bound. The accompanying paper sums the shells as a
  geometric series into `X`; here each shell is bounded by `p^M ≤ X` and the factor of the number of shells is kept
  (`(ℓ_max+1)²`, the same form as `bad_mass_le` in (A)).
* `count_C_le`: using `N = p^k N'` (`p ∤ N'`) and `C_min(N) > N₀ ⇒ S_min(N') > N₀`, the count for general `N` is
  bounded by `∑_k #{N' ∈ ℕ_p ∩ [1, X/p^k] | …}`.
* Arithmetic: `exp_neg_mul_exp_le` (`e^{-a e^t} ≤ a^{-1} e^{-t}`), `exp_neg_le_rate`, `arith_small`.
-/

namespace GGMCollatz

namespace ND

open Asm

variable (F : Family)

open Classical in
/-- From the seed: the number of bad points in `ℕ_p ∩ [1, X]`. -/
theorem count_seed {cB CB : ℝ} (hCB : 0 ≤ CB) {L₀ : ℕ}
    (hseed : ∀ L M : ℕ, L₀ ≤ L → L ≤ M →
      (((Finset.Ico (F.p ^ M) (F.p ^ (M + 1))).filter
          (fun n => ∀ k, F.p ^ L ≤ F.Ct^[k] n)).card : ℝ)
        ≤ CB * (F.p : ℝ) ^ M * ((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(cB * L)))
    {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (hL : L₀ ≤ Nat.log F.p N₀) {X : ℝ} (hX : 0 ≤ X) :
    (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => N % F.p ≠ 0 ∧ N₀ < F.Smin N)).card : ℝ) ≤
      CB * X * ((Nat.log F.p ⌊X⌋₊ : ℝ) + 1) ^ 2 * ((Nat.log F.p N₀ : ℝ) + 1) *
        Real.exp (-(cB * Nat.log F.p N₀)) := by
  set L := Nat.log F.p N₀ with hLdef
  set lm := Nat.log F.p ⌊X⌋₊ with hlm
  set S := (Finset.Icc 1 ⌊X⌋₊).filter (fun N => N % F.p ≠ 0 ∧ N₀ < F.Smin N) with hS
  set E : ℝ := CB * ((L : ℝ) + 1) * Real.exp (-(cB * L)) with hE
  have hE0 : 0 ≤ E := by positivity
  have hp1 : 1 < F.p := F.one_lt_p
  have hpL : F.p ^ L ≤ N₀ := Nat.pow_log_le_self F.p (by omega)
  have hRHS : 0 ≤ CB * X * ((lm : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) * Real.exp (-(cB * L)) := by
    positivity
  rcases Nat.eq_zero_or_pos ⌊X⌋₊ with hX0 | hXpos
  · have hS0 : S = ∅ := by
      rw [hS, hX0]
      rfl
    rw [hS0, Finset.card_empty, Nat.cast_zero]
    exact hRHS
  have hmaps : ∀ N ∈ S, Nat.log F.p N ∈ Finset.range (lm + 1) := by
    intro N hN
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hN
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right hN.1.2)
  have hplm : (F.p : ℝ) ^ lm ≤ X := by
    have h1 : F.p ^ lm ≤ ⌊X⌋₊ := Nat.pow_log_le_self F.p hXpos.ne'
    have h2 : ((F.p ^ lm : ℕ) : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact le_trans h2 (Nat.floor_le hX)
  have hfib : ∀ ℓ ∈ Finset.range (lm + 1),
      ((S.filter (fun N => Nat.log F.p N = ℓ)).card : ℝ) ≤ X * ((lm : ℝ) + 1) * E := by
    intro ℓ hℓ
    have hℓlm : ℓ ≤ lm := Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)
    have hℓ' : (ℓ : ℝ) ≤ lm := by exact_mod_cast hℓlm
    set T := (Finset.Ico (F.p ^ ℓ) (F.p ^ (ℓ + 1))).filter (fun n => ∀ k, F.p ^ L ≤ F.Ct^[k] n)
    have hsubT : S.filter (fun N => Nat.log F.p N = ℓ) ⊆ T := by
      intro N hN
      rw [Finset.mem_filter, hS, Finset.mem_filter, Finset.mem_Icc] at hN
      obtain ⟨⟨⟨hN1, _⟩, hNp, hbad⟩, hlog⟩ := hN
      have hN0 : N ≠ 0 := by omega
      rw [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨hlog ▸ Nat.pow_log_le_self F.p hN0, hlog ▸ Nat.lt_pow_succ_log_self hp1 N⟩, ?_⟩
      exact Ct_iterate_ge_of_lt_Smin F hNp hpL hbad
    have h1 : ((S.filter (fun N => Nat.log F.p N = ℓ)).card : ℝ) ≤ (T.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubT
    have hpℓ : (F.p : ℝ) ^ ℓ ≤ X := by
      have : (F.p : ℝ) ^ ℓ ≤ (F.p : ℝ) ^ lm :=
        pow_le_pow_right₀ (by exact_mod_cast hp1.le) hℓlm
      linarith
    have h2 : (T.card : ℝ) ≤ X * ((lm : ℝ) + 1) * E := by
      by_cases hLℓ : L ≤ ℓ
      · have hs := hseed L ℓ hL hLℓ
        have hpℓ0 : (0 : ℝ) ≤ (F.p : ℝ) ^ ℓ := by positivity
        calc (T.card : ℝ) ≤ _ := hs
          _ = (F.p : ℝ) ^ ℓ * ((ℓ : ℝ) + 1) * E := by rw [hE]; ring
          _ ≤ X * ((lm : ℝ) + 1) * E := by
              apply mul_le_mul_of_nonneg_right _ hE0
              exact mul_le_mul hpℓ (by linarith) (by positivity) hX
      · have hT : T = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro n hn hk
          rw [Finset.mem_Ico] at hn
          have h0 := hk 0
          simp only [Function.iterate_zero, id] at h0
          have : F.p ^ (ℓ + 1) ≤ F.p ^ L := Nat.pow_le_pow_right F.p_pos (by omega)
          omega
        rw [hT, Finset.card_empty, Nat.cast_zero]
        positivity
    linarith
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  push_cast
  calc ∑ ℓ ∈ Finset.range (lm + 1), ((S.filter (fun N => Nat.log F.p N = ℓ)).card : ℝ)
      ≤ ∑ ℓ ∈ Finset.range (lm + 1), X * ((lm : ℝ) + 1) * E := Finset.sum_le_sum hfib
    _ = ((lm : ℝ) + 1) * (X * ((lm : ℝ) + 1) * E) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ = CB * X * ((lm : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) * Real.exp (-(cB * L)) := by rw [hE]; ring

open Classical in
/-- Extension to general `N`: `N = p^k N'`, `C_min(N) > N₀ ⇒ S_min(N') > N₀`. -/
theorem count_C_le (N₀ : ℕ) {X : ℝ} (hX : 0 ≤ X) :
    (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => N₀ < F.Cmin N)).card : ℝ) ≤
      ∑ k ∈ Finset.range (⌊X⌋₊ + 1),
        (((Finset.Icc 1 ⌊X / (F.p : ℝ) ^ k⌋₊).filter
          (fun N => N % F.p ≠ 0 ∧ N₀ < F.Smin N)).card : ℝ) := by
  have hp1 : 1 < F.p := F.one_lt_p
  set S := (Finset.Icc 1 ⌊X⌋₊).filter (fun N => N₀ < F.Cmin N) with hS
  set T : ℕ → Finset ℕ := fun k => (Finset.Icc 1 ⌊X / (F.p : ℝ) ^ k⌋₊).filter
    (fun N => N % F.p ≠ 0 ∧ N₀ < F.Smin N) with hT
  have hsub : S ⊆ (Finset.range (⌊X⌋₊ + 1)).biUnion
      (fun k => (T k).image (fun N' => F.p ^ k * N')) := by
    intro N hN
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hN
    obtain ⟨⟨hN1, hNX⟩, hbad⟩ := hN
    have hN0 : N ≠ 0 := by omega
    set k := padicValNat F.p N with hk
    set N' := N / F.p ^ k with hN'
    have hmul : F.p ^ k * N' = N := pow_val_mul_div F N
    have hpk : F.p ^ k ≤ N := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    have hkp : k < F.p ^ k := Nat.lt_pow_self hp1
    have hN'0 : N' ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hmul
      exact hN0 hmul.symm
    rw [Finset.mem_biUnion]
    refine ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Finset.mem_image]
    refine ⟨N', ?_, hmul⟩
    rw [hT]
    simp only
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr hN'0, ?_⟩, div_pow_val_mod_ne_zero F hN0,
      lt_Smin_of_lt_Cmin F hN0 hbad⟩
    apply Nat.le_floor
    have hpk0 : (0 : ℝ) < (F.p : ℝ) ^ k := by have := F.p_pos; positivity
    rw [le_div_iff₀ hpk0]
    have h1 : ((F.p ^ k * N' : ℕ) : ℝ) = (N : ℝ) := by rw [hmul]
    push_cast at h1
    have h2 : (N : ℝ) ≤ X := le_trans (Nat.cast_le.mpr hNX) (Nat.floor_le hX)
    linarith
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le (s := Finset.range (⌊X⌋₊ + 1))
    (t := fun k => (T k).image (fun N' => F.p ^ k * N'))
  have h3 : ∑ k ∈ Finset.range (⌊X⌋₊ + 1), ((T k).image (fun N' => F.p ^ k * N')).card ≤
      ∑ k ∈ Finset.range (⌊X⌋₊ + 1), (T k).card :=
    Finset.sum_le_sum fun k _ => Finset.card_image_le
  have h4 : S.card ≤ ∑ k ∈ Finset.range (⌊X⌋₊ + 1), (T k).card := le_trans h1 (le_trans h2 h3)
  calc (S.card : ℝ) ≤ ((∑ k ∈ Finset.range (⌊X⌋₊ + 1), (T k).card : ℕ) : ℝ) := Nat.cast_le.mpr h4
    _ = ∑ k ∈ Finset.range (⌊X⌋₊ + 1), ((T k).card : ℝ) := Nat.cast_sum _ _

/-- `e^{-a e^t} ≤ a^{-1} e^{-t}` (`a > 0`). -/
lemma exp_neg_mul_exp_le {a : ℝ} (ha : 0 < a) (t : ℝ) :
    Real.exp (-(a * Real.exp t)) ≤ (1 / a) * Real.exp (-t) := by
  have h1 := Real.add_one_le_exp (a * Real.exp t)
  have hpos : 0 < a * Real.exp t := mul_pos ha (Real.exp_pos t)
  rw [Real.exp_neg, Real.exp_neg, one_div, ← mul_inv]
  apply inv_anti₀ hpos
  linarith

/-- `e^{-c_B L/4} ≤ (L+1) e^{-c₁ L}` (`c₁ ≤ c_B/4`). -/
lemma exp_neg_le_rate {cB c₁ L : ℝ} (hL : 0 ≤ L) (hc : c₁ ≤ cB / 4) :
    Real.exp (-(cB * L / 4)) ≤ (L + 1) * Real.exp (-(c₁ * L)) := by
  have h0 : c₁ * L ≤ cB / 4 * L := mul_le_mul_of_nonneg_right hc hL
  have h1 : Real.exp (-(cB * L / 4)) ≤ Real.exp (-(c₁ * L)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(c₁ * L)) ≤ (L + 1) * Real.exp (-(c₁ * L)) := by
    have := (Real.exp_pos (-(c₁ * L))).le
    nlinarith
  linarith

/-- Arithmetic for small `X`: if `ℓ_max ≤ α² v / log p` and `v = e^{c_B L/4}`, then
`C_B X (ℓ_max+1)² (L+1) e^{-c_B L} ≤ C_B (α²/log p + 1)² X (L+1) e^{-c₁ L}` (`c₁ ≤ c_B/2`). -/
lemma arith_small {α lp CB cB c₁ L X lm : ℝ} (hlp : 0 < lp) (hCB : 0 ≤ CB)
    (hX : 0 ≤ X) (hL : 0 ≤ L) (hcB : 0 ≤ cB) (hc₁ : c₁ ≤ cB / 2) (hlm0 : 0 ≤ lm)
    (hlm : lm ≤ α ^ 2 * Real.exp (cB * L / 4) / lp) :
    CB * X * (lm + 1) ^ 2 * (L + 1) * Real.exp (-(cB * L)) ≤
      CB * (α ^ 2 / lp + 1) ^ 2 * X * ((L + 1) * Real.exp (-(c₁ * L))) := by
  obtain ⟨v, hv⟩ : ∃ v, v = Real.exp (cB * L / 4) := ⟨_, rfl⟩
  rw [← hv] at hlm
  have hv1 : 1 ≤ v := by rw [hv]; exact Real.one_le_exp (by positivity)
  have h1 : lm + 1 ≤ (α ^ 2 / lp + 1) * v := by
    have e : α ^ 2 * v / lp = α ^ 2 / lp * v := by ring
    rw [e] at hlm
    rw [add_mul, one_mul]; linarith
  have hsq : (lm + 1) ^ 2 ≤ (α ^ 2 / lp + 1) ^ 2 * v ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) h1 2
  have hve : v ^ 2 * Real.exp (-(cB * L)) ≤ Real.exp (-(c₁ * L)) := by
    rw [hv, sq, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hc₁ hL
    have e : cB * L / 4 + cB * L / 4 + -(cB * L) = -(cB / 2 * L) := by ring
    rw [e]; linarith
  have hK : 0 ≤ CB * X * (L + 1) := by positivity
  have hE : 0 ≤ Real.exp (-(cB * L)) := (Real.exp_pos _).le
  have hA : 0 ≤ CB * X * (L + 1) * (α ^ 2 / lp + 1) ^ 2 := by positivity
  calc _ = CB * X * (L + 1) * ((lm + 1) ^ 2 * Real.exp (-(cB * L))) := by ring
    _ ≤ CB * X * (L + 1) * ((α ^ 2 / lp + 1) ^ 2 * v ^ 2 * Real.exp (-(cB * L))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hE) hK
    _ = CB * X * (L + 1) * (α ^ 2 / lp + 1) ^ 2 * (v ^ 2 * Real.exp (-(cB * L))) := by ring
    _ ≤ CB * X * (L + 1) * (α ^ 2 / lp + 1) ^ 2 * Real.exp (-(c₁ * L)) :=
        mul_le_mul_of_nonneg_left hve hA
    _ = _ := by ring

/-- Thresholds (the same argument as `Asm.uniform_large`): if `L = ⌊log_p N₀⌋ ≥ 1`, `L ≥ 64 log p / c_B²` and
`L ≥ 4 X_s / c_B`, then with `v = e^{c_B L/4}` we have `X_s ≤ e^v` and `N₀ ≤ e^v`. -/
lemma exp_thresholds {p : ℕ} (hp1 : 1 < p) {cB Xs : ℝ} (hcB : 0 < cB) (N₀ : ℕ)
    (hL1 : (1 : ℝ) ≤ Nat.log p N₀) (hLc : 64 * Real.log p / cB ^ 2 ≤ Nat.log p N₀)
    (hLX : 4 * Xs / cB ≤ Nat.log p N₀) :
    Xs ≤ Real.exp (Real.exp (cB * Nat.log p N₀ / 4)) ∧
      (N₀ : ℝ) ≤ Real.exp (Real.exp (cB * Nat.log p N₀ / 4)) := by
  set L := Nat.log p N₀ with hLdef
  have hp2 : (1 : ℝ) < p := by exact_mod_cast hp1
  have hlp : 0 < Real.log p := Real.log_pos hp2
  obtain ⟨v, hvdef⟩ : ∃ v, v = Real.exp (cB * L / 4) := ⟨_, rfl⟩
  rw [← hvdef]
  have hL0 : (0 : ℝ) ≤ L := by linarith
  constructor
  · have h1 : Xs ≤ cB * L / 4 := by
      rw [div_le_iff₀ hcB] at hLX; linarith
    have h2 := Real.add_one_le_exp (cB * L / 4)
    have h3 := Real.add_one_le_exp v
    rw [← hvdef] at h2
    linarith
  · have hN0lt : (N₀ : ℝ) < (p : ℝ) ^ (L + 1) := by
      rw [hLdef]; exact_mod_cast Nat.lt_pow_succ_log_self hp1 N₀
    have hq : (cB * L / 4) ^ 2 / 2 ≤ v := by
      have := Real.pow_div_factorial_le_exp (x := cB * L / 4) (by positivity) 2
      rw [hvdef]; simpa using this
    have hq2 : ((L : ℝ) + 1) * Real.log p ≤ (cB * L / 4) ^ 2 / 2 := by
      have h1 : 64 * Real.log p ≤ cB ^ 2 * L := by
        rw [div_le_iff₀ (by positivity)] at hLc; linarith
      have h2 : 1 * Real.log p ≤ (L : ℝ) * Real.log p := mul_le_mul_of_nonneg_right hL1 hlp.le
      have h3 : (2 * (L : ℝ)) * (64 * Real.log p) ≤ (2 * (L : ℝ)) * (cB ^ 2 * L) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have e : (cB * L / 4) ^ 2 / 2 = cB ^ 2 * L * L / 32 := by ring
      rw [e]; nlinarith
    have h2 : (p : ℝ) ^ (L + 1) = Real.exp (((L : ℝ) + 1) * Real.log p) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]; push_cast; ring_nf
    rw [h2] at hN0lt
    exact le_trans hN0lt.le (Real.exp_le_exp.mpr (le_trans hq2 (le_trans hq (by
      have := Real.add_one_le_exp v; linarith))))

/-- The trivial case `L = ⌊log_p N₀⌋ ≤ M`: the count is `≤ X ≤ (p^{M+1})^c X N₀^{-c}`. -/
lemma small_L_bound {p : ℕ} (hp1 : 1 < p) {c K : ℝ} (hc : 0 < c) {M N₀ : ℕ} (hN₀ : 1 ≤ N₀)
    (hsmall : Nat.log p N₀ < M + 1) (hK : ((p : ℝ) ^ (M + 1)) ^ c ≤ K) {X cnt : ℝ} (hX : 0 ≤ X)
    (hcnt : cnt ≤ X) : cnt ≤ K * X * (N₀ : ℝ) ^ (-c) := by
  have hN0pos : (0 : ℝ) < N₀ := by exact_mod_cast (by omega : 0 < N₀)
  have hN0lt : (N₀ : ℝ) ≤ (p : ℝ) ^ (M + 1) := by
    have h1 : N₀ < p ^ (Nat.log p N₀ + 1) := Nat.lt_pow_succ_log_self hp1 N₀
    have h2 : p ^ (Nat.log p N₀ + 1) ≤ p ^ (M + 1) := Nat.pow_le_pow_right (by omega) hsmall
    exact_mod_cast (le_trans h1.le h2)
  have h1 : (N₀ : ℝ) ^ c ≤ ((p : ℝ) ^ (M + 1)) ^ c := Real.rpow_le_rpow hN0pos.le hN0lt hc.le
  have h2 : (N₀ : ℝ) ^ c * (N₀ : ℝ) ^ (-c) = 1 := by
    rw [← Real.rpow_add hN0pos, add_neg_cancel, Real.rpow_zero]
  have hNpow : 0 < (N₀ : ℝ) ^ (-c) := Real.rpow_pos_of_pos hN0pos _
  have h3 : 1 ≤ K * (N₀ : ℝ) ^ (-c) := by
    calc (1 : ℝ) = (N₀ : ℝ) ^ c * (N₀ : ℝ) ^ (-c) := h2.symm
      _ ≤ ((p : ℝ) ^ (M + 1)) ^ c * (N₀ : ℝ) ^ (-c) := mul_le_mul_of_nonneg_right h1 hNpow.le
      _ ≤ K * (N₀ : ℝ) ^ (-c) := mul_le_mul_of_nonneg_right hK hNpow.le
  calc cnt ≤ X := hcnt
    _ = X * 1 := (mul_one X).symm
    _ ≤ X * (K * (N₀ : ℝ) ^ (-c)) := mul_le_mul_of_nonneg_left h3 hX
    _ = K * X * (N₀ : ℝ) ^ (-c) := by ring

/-- Combining the rates: `A (L+1)e^{-c₁L} + K_A N₀^{-c'} ≤ (A (1+2/c₁)e^{c₁/2} + K_A) N₀^{-c}`
(`c ≤ c₁/(2 log p)`, `c ≤ c'`). -/
lemma combine_rate {p : ℕ} (hp1 : 1 < p) {A KA c₁ c c' : ℝ} (hA : 0 ≤ A) (hKA : 0 ≤ KA)
    (hc₁ : 0 < c₁) (hcc₁ : c ≤ c₁ / (2 * Real.log p)) (hcc' : c ≤ c') {N₀ : ℕ} (hN₀ : 1 ≤ N₀) :
    A * (((Nat.log p N₀ : ℝ) + 1) * Real.exp (-(c₁ * Nat.log p N₀))) + KA * (N₀ : ℝ) ^ (-c') ≤
      (A * ((1 + 2 / c₁) * Real.exp (c₁ / 2)) + KA) * (N₀ : ℝ) ^ (-c) := by
  have hrate := rate_to_N0 p hp1 c₁ hc₁ N₀ hN₀
  have hN1 : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
  have hmono1 : (N₀ : ℝ) ^ (-(c₁ / (2 * Real.log p))) ≤ (N₀ : ℝ) ^ (-c) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hmono2 : (N₀ : ℝ) ^ (-c') ≤ (N₀ : ℝ) ^ (-c) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hC0 : 0 ≤ (1 + 2 / c₁) * Real.exp (c₁ / 2) := by positivity
  have e1 : A * (((Nat.log p N₀ : ℝ) + 1) * Real.exp (-(c₁ * Nat.log p N₀))) ≤
      A * ((1 + 2 / c₁) * Real.exp (c₁ / 2) * (N₀ : ℝ) ^ (-c)) :=
    mul_le_mul_of_nonneg_left (le_trans hrate (mul_le_mul_of_nonneg_left hmono1 hC0)) hA
  have e2 : KA * (N₀ : ℝ) ^ (-c') ≤ KA * (N₀ : ℝ) ^ (-c) :=
    mul_le_mul_of_nonneg_left hmono2 hKA
  calc _ ≤ A * ((1 + 2 / c₁) * Real.exp (c₁ / 2) * (N₀ : ℝ) ^ (-c)) + KA * (N₀ : ℝ) ^ (-c) :=
        add_le_add e1 e2
    _ = _ := by ring

end ND

end GGMCollatz
