/- Portions Copyright (c) 2026 Idris Ali Shaik (FirstPassageLinearTransport, Apache License 2.0).
   Modified: generalized to the maps of Goncalves, Greenfeld and Madrid. See NOTICE. -/
import GGMCollatz.Seed.Step

/-!
# Seed (Theorem 4.1 of the paper), part 3: fibres at a fixed time (transport)

Items 3 and 4 of the seed argument in the accompanying paper. The counterparts of `Pullback` and
`Transport` (Lemmas 4.1, 4.2, Proposition 4.3) of Idris Ali Shaik's `FirstPassageLinearTransport`
(Apache-2.0), rewritten and generalized to the GGM family (base `p`, arbitrary sign of `r`).

* `mulCount t n`: the number `s_t(n)` of multiplication steps among the first `t` steps.
* `backward_bounds`: if the orbit stays `≥ Y` for `t` steps, then
  `p^t y (1-a)^t ≤ q^{s} n ≤ p^t y (1+a)^t` (`y = C~^t(n)`, `R = a p Y`). A form of the backward
  product `n = (p^t y / q^s) ∏(1 - u_j)`, `|u_j| ≤ a` of the accompanying paper without expanding the
  product.
* `card_fiber_le`: the number of `n` in the shell `I_M` with `C~^t(n) = y` and staying `≥ Y` for `t`
  steps is at most `(t+1)(1 + 4 t a p^{M+1})` (the corollary in the accompanying paper; instead of the
  argument making `s` common, we sum over `s`).
-/

namespace GGMCollatz

namespace Family

variable (F : Family)

open Finset

/-- The number `s_t(n)` of multiplication steps among the first `t` steps. -/
def mulCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | t + 1, n => (if n % F.p = 0 then 0 else 1) + mulCount t (F.Ct n)

lemma mulCount_succ (t n : ℕ) :
    F.mulCount (t + 1) n = (if n % F.p = 0 then 0 else 1) + F.mulCount t (F.Ct n) := rfl

lemma mulCount_le : ∀ t n, F.mulCount t n ≤ t := by
  intro t
  induction t with
  | zero => intro n; simp [mulCount]
  | succ t ih =>
    intro n
    rw [mulCount_succ]
    have := ih (F.Ct n)
    split_ifs <;> omega

/-- Backward sandwiching ((ii) and item 3 of the seed argument in the accompanying paper). -/
lemma backward_bounds {Y : ℕ} (hRY : (F.Rb : ℝ) ≤ ((F.q : ℝ) - F.p) * Y)
    {a : ℝ} (ha : (F.Rb : ℝ) = a * F.p * Y) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ t n, (∀ k < t, Y ≤ F.Ct^[k] n) →
      (F.p : ℝ) ^ t * (F.Ct^[t] n : ℝ) * (1 - a) ^ t ≤ (F.q : ℝ) ^ (F.mulCount t n) * n ∧
      (F.q : ℝ) ^ (F.mulCount t n) * n ≤ (F.p : ℝ) ^ t * (F.Ct^[t] n : ℝ) * (1 + a) ^ t := by
  have hp : (0 : ℝ) < F.p := by exact_mod_cast F.p_pos
  have hq : (0 : ℝ) < F.q := by exact_mod_cast F.q_pos
  intro t
  induction t with
  | zero => intro n _; simp [mulCount]
  | succ t ih =>
    intro n hk
    have hk' : ∀ k < t, Y ≤ F.Ct^[k] (F.Ct n) := by
      intro k hk2
      have := hk (k + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    obtain ⟨ih1, ih2⟩ := ih (F.Ct n) hk'
    rw [Function.iterate_succ_apply, mulCount_succ]
    have hnY : Y ≤ n := by simpa using hk 0 (by omega)
    have hnYr : (Y : ℝ) ≤ n := by exact_mod_cast hnY
    have hy0 : (0 : ℝ) ≤ (F.Ct^[t] (F.Ct n) : ℝ) := by positivity
    have hqs : (0 : ℝ) ≤ (F.q : ℝ) ^ F.mulCount t (F.Ct n) := by positivity
    have hpt : (0 : ℝ) ≤ (F.p : ℝ) ^ t := by positivity
    have h1a : 0 ≤ 1 - a := by linarith
    have hA1 : 0 ≤ (1 - a) ^ t := pow_nonneg h1a t
    have hA2 : 0 ≤ (1 + a) ^ t := pow_nonneg (by linarith) t
    by_cases h : n % F.p = 0
    · simp only [h, if_true, zero_add]
      have e : (F.p : ℝ) * (F.Ct n : ℝ) = n := F.p_mul_Ct_real_of_mod_eq_zero h
      rw [← e]
      constructor
      · have step : (F.p : ℝ) * (1 - a) * ((F.p : ℝ) ^ t * (F.Ct^[t] (F.Ct n) : ℝ) * (1 - a) ^ t)
            ≤ (F.p : ℝ) * (1 - a) * ((F.q : ℝ) ^ F.mulCount t (F.Ct n) * (F.Ct n : ℝ)) :=
          mul_le_mul_of_nonneg_left ih1 (mul_nonneg hp.le h1a)
        have step2 : (F.p : ℝ) * (1 - a) * ((F.q : ℝ) ^ F.mulCount t (F.Ct n) * (F.Ct n : ℝ))
            ≤ (F.p : ℝ) * ((F.q : ℝ) ^ F.mulCount t (F.Ct n) * (F.Ct n : ℝ)) := by
          have : 0 ≤ (F.q : ℝ) ^ F.mulCount t (F.Ct n) * (F.Ct n : ℝ) := by positivity
          have := mul_nonneg (mul_nonneg hp.le ha0) this
          linarith
        calc (F.p : ℝ) ^ (t + 1) * (F.Ct^[t] (F.Ct n) : ℝ) * (1 - a) ^ (t + 1)
            = (F.p : ℝ) * (1 - a) * ((F.p : ℝ) ^ t * (F.Ct^[t] (F.Ct n) : ℝ) * (1 - a) ^ t) := by
              ring
          _ ≤ (F.p : ℝ) * ((F.q : ℝ) ^ F.mulCount t (F.Ct n) * (F.Ct n : ℝ)) := step.trans step2
          _ = (F.q : ℝ) ^ F.mulCount t (F.Ct n) * ((F.p : ℝ) * (F.Ct n : ℝ)) := by ring
      · have step : (F.p : ℝ) * ((F.q : ℝ) ^ F.mulCount t (F.Ct n) * (F.Ct n : ℝ))
            ≤ (F.p : ℝ) * ((F.p : ℝ) ^ t * (F.Ct^[t] (F.Ct n) : ℝ) * (1 + a) ^ t) :=
          mul_le_mul_of_nonneg_left ih2 hp.le
        have step2 : (F.p : ℝ) * ((F.p : ℝ) ^ t * (F.Ct^[t] (F.Ct n) : ℝ) * (1 + a) ^ t)
            ≤ (F.p : ℝ) * (1 + a) * ((F.p : ℝ) ^ t * (F.Ct^[t] (F.Ct n) : ℝ) * (1 + a) ^ t) := by
          have : 0 ≤ (F.p : ℝ) ^ t * (F.Ct^[t] (F.Ct n) : ℝ) * (1 + a) ^ t := by positivity
          have := mul_nonneg (mul_nonneg hp.le ha0) this
          linarith
        calc (F.q : ℝ) ^ F.mulCount t (F.Ct n) * ((F.p : ℝ) * (F.Ct n : ℝ))
            = (F.p : ℝ) * ((F.q : ℝ) ^ F.mulCount t (F.Ct n) * (F.Ct n : ℝ)) := by ring
          _ ≤ (F.p : ℝ) * (1 + a) * ((F.p : ℝ) ^ t * (F.Ct^[t] (F.Ct n) : ℝ) * (1 + a) ^ t) :=
              step.trans step2
          _ = (F.p : ℝ) ^ (t + 1) * (F.Ct^[t] (F.Ct n) : ℝ) * (1 + a) ^ (t + 1) := by ring
    · simp only [h, if_false]
      have e : (F.p : ℝ) * (F.Ct n : ℝ) = (F.q : ℝ) * n + F.r (n % F.p) :=
        F.p_mul_Ct_real_of_mod_ne_zero h
      have hr := F.abs_r_le_real (F.mod_lt_p n)
      -- `n ≤ C~(n)`
      have hgrow : n ≤ F.Ct n := by
        apply F.le_Ct_of_mod_ne_zero h
        have : ((F.q : ℝ) - F.p) * Y ≤ ((F.q : ℝ) - F.p) * n := by
          apply mul_le_mul_of_nonneg_left hnYr
          have : (F.p : ℝ) < F.q := by exact_mod_cast F.p_lt_q
          linarith
        linarith
      have hn' : (Y : ℝ) ≤ (F.Ct n : ℝ) := by exact_mod_cast le_trans hnY hgrow
      -- `|r| ≤ a p C~(n)`
      have hrb : |(F.r (n % F.p) : ℝ)| ≤ a * F.p * (F.Ct n : ℝ) := by
        have : a * F.p * (Y : ℝ) ≤ a * F.p * (F.Ct n : ℝ) :=
          mul_le_mul_of_nonneg_left hn' (mul_nonneg ha0 hp.le)
        linarith
      have hr1 := neg_abs_le (F.r (n % F.p) : ℝ)
      have hr2 := le_abs_self (F.r (n % F.p) : ℝ)
      have hqn : (F.q : ℝ) * n = (F.p : ℝ) * (F.Ct n : ℝ) - F.r (n % F.p) := by linarith
      have hpow : (F.q : ℝ) ^ (1 + F.mulCount t (F.Ct n)) * n
          = (F.q : ℝ) ^ F.mulCount t (F.Ct n) * ((F.p : ℝ) * (F.Ct n : ℝ) - F.r (n % F.p)) := by
        rw [← hqn, pow_add, pow_one]; ring
      rw [hpow]
      constructor
      · have hlow : (F.p : ℝ) * (1 - a) * (F.Ct n : ℝ) ≤ (F.p : ℝ) * (F.Ct n : ℝ) - F.r (n % F.p) := by
          nlinarith
        have step := mul_le_mul_of_nonneg_left ih1 (mul_nonneg hp.le h1a)
        calc (F.p : ℝ) ^ (t + 1) * (F.Ct^[t] (F.Ct n) : ℝ) * (1 - a) ^ (t + 1)
            = (F.p : ℝ) * (1 - a) * ((F.p : ℝ) ^ t * (F.Ct^[t] (F.Ct n) : ℝ) * (1 - a) ^ t) := by
              ring
          _ ≤ (F.p : ℝ) * (1 - a) * ((F.q : ℝ) ^ F.mulCount t (F.Ct n) * (F.Ct n : ℝ)) := step
          _ = (F.q : ℝ) ^ F.mulCount t (F.Ct n) * ((F.p : ℝ) * (1 - a) * (F.Ct n : ℝ)) := by ring
          _ ≤ (F.q : ℝ) ^ F.mulCount t (F.Ct n) * ((F.p : ℝ) * (F.Ct n : ℝ) - F.r (n % F.p)) :=
              mul_le_mul_of_nonneg_left hlow hqs
      · have hup : (F.p : ℝ) * (F.Ct n : ℝ) - F.r (n % F.p) ≤ (F.p : ℝ) * (1 + a) * (F.Ct n : ℝ) := by
          nlinarith
        have step := mul_le_mul_of_nonneg_left ih2 (mul_nonneg hp.le (by linarith : (0 : ℝ) ≤ 1 + a))
        calc (F.q : ℝ) ^ F.mulCount t (F.Ct n) * ((F.p : ℝ) * (F.Ct n : ℝ) - F.r (n % F.p))
            ≤ (F.q : ℝ) ^ F.mulCount t (F.Ct n) * ((F.p : ℝ) * (1 + a) * (F.Ct n : ℝ)) :=
              mul_le_mul_of_nonneg_left hup hqs
          _ = (F.p : ℝ) * (1 + a) * ((F.q : ℝ) ^ F.mulCount t (F.Ct n) * (F.Ct n : ℝ)) := by ring
          _ ≤ (F.p : ℝ) * (1 + a) * ((F.p : ℝ) ^ t * (F.Ct^[t] (F.Ct n) : ℝ) * (1 + a) ^ t) := step
          _ = (F.p : ℝ) ^ (t + 1) * (F.Ct^[t] (F.Ct n) : ℝ) * (1 + a) ^ (t + 1) := by ring

/-- A finite set of natural numbers contained in the real interval `[lo, hi]` has at most
`hi - lo + 1` elements. -/
lemma card_le_of_forall_mem_real (S : Finset ℕ) (hS : S.Nonempty) (lo hi : ℝ)
    (h : ∀ n ∈ S, lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi) : (S.card : ℝ) ≤ hi - lo + 1 := by
  set n₀ := S.min' hS with hn₀
  have hn₀S : n₀ ∈ S := S.min'_mem hS
  have hlohi : 0 ≤ hi - lo := by
    have := h n₀ hn₀S; linarith
  have hsub : S ⊆ Icc n₀ (n₀ + ⌊hi - lo⌋₊) := by
    intro n hn
    have h1 : n₀ ≤ n := S.min'_le n hn
    rw [mem_Icc]
    refine ⟨h1, ?_⟩
    have h2 : ((n - n₀ : ℕ) : ℝ) ≤ hi - lo := by
      rw [Nat.cast_sub h1]
      have := h n hn; have := h n₀ hn₀S; linarith
    have := Nat.le_floor h2
    omega
  have hc := card_le_card hsub
  rw [Nat.card_Icc] at hc
  have hc' : (S.card : ℝ) ≤ ((⌊hi - lo⌋₊ : ℕ) : ℝ) + 1 := by
    have : S.card ≤ ⌊hi - lo⌋₊ + 1 := by omega
    exact_mod_cast this
  have := Nat.floor_le hlohi
  linarith

/-- `(1 + a)^t ≤ 1 + 2ta` (`0 ≤ ta ≤ 1`). -/
lemma one_add_pow_le {a : ℝ} (ha0 : 0 ≤ a) (t : ℕ) (hta : (t : ℝ) * a ≤ 1) :
    (1 + a) ^ t ≤ 1 + 2 * t * a := by
  have h1 : (1 + a) ^ t ≤ Real.exp a ^ t := by
    apply pow_le_pow_left₀ (by linarith)
    have := Real.add_one_le_exp a; linarith
  rw [← Real.exp_nat_mul] at h1
  have habs : |(t : ℝ) * a| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; exact hta
  have h2 := Real.abs_exp_sub_one_le habs
  have h3 := le_abs_self (Real.exp ((t : ℝ) * a) - 1)
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t : ℝ) * a)] at h2
  linarith

/-- The number of elements of a fibre at a fixed time (the corollary and item 4 of the seed argument in
the accompanying paper). -/
theorem card_fiber_le {Y : ℕ} (hRY : (F.Rb : ℝ) ≤ ((F.q : ℝ) - F.p) * Y)
    {a : ℝ} (ha : (F.Rb : ℝ) = a * F.p * Y) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (M t y : ℕ)
    (hta : (t : ℝ) * a ≤ 1 / 4) :
    (((Ico (F.p ^ M) (F.p ^ (M + 1))).filter
        (fun n => F.Ct^[t] n = y ∧ ∀ k < t, Y ≤ F.Ct^[k] n)).card : ℝ)
      ≤ ((t : ℝ) + 1) * (1 + 4 * t * a * (F.p : ℝ) ^ (M + 1)) := by
  classical
  have hp : (0 : ℝ) < F.p := by exact_mod_cast F.p_pos
  have hq : (0 : ℝ) < F.q := by exact_mod_cast F.q_pos
  set S := (Ico (F.p ^ M) (F.p ^ (M + 1))).filter
    (fun n => F.Ct^[t] n = y ∧ ∀ k < t, Y ≤ F.Ct^[k] n) with hS
  have hmaps : ∀ n ∈ S, F.mulCount t n ∈ range (t + 1) := by
    intro n _; rw [mem_range]; have := F.mulCount_le t n; omega
  rw [card_eq_sum_card_fiberwise hmaps]
  push_cast
  have hta0 : 0 ≤ (t : ℝ) * a := by positivity
  have hbound : ∀ s ∈ range (t + 1),
      (((S.filter (fun n => F.mulCount t n = s)).card : ℕ) : ℝ)
        ≤ 1 + 4 * t * a * (F.p : ℝ) ^ (M + 1) := by
    intro s _
    set T := S.filter (fun n => F.mulCount t n = s) with hT
    rcases T.eq_empty_or_nonempty with hTe | hTn
    · rw [hTe, card_empty, Nat.cast_zero]; positivity
    set B := (F.p : ℝ) ^ t * y / (F.q : ℝ) ^ s with hB
    have hqs : (0 : ℝ) < (F.q : ℝ) ^ s := by positivity
    have hB0 : 0 ≤ B := by positivity
    have hmem : ∀ n ∈ T, B * (1 - a) ^ t ≤ (n : ℝ) ∧ (n : ℝ) ≤ B * (1 + a) ^ t := by
      intro n hn
      simp only [hT, hS, mem_filter, mem_Ico] at hn
      obtain ⟨⟨_, hy, hk⟩, hs⟩ := hn
      obtain ⟨b1, b2⟩ := F.backward_bounds hRY ha ha0 ha1 t n hk
      rw [hy, hs] at b1 b2
      constructor
      · rw [hB, div_mul_eq_mul_div, div_le_iff₀ hqs]; linarith
      · rw [hB, div_mul_eq_mul_div, le_div_iff₀ hqs]; linarith
    have hcard := card_le_of_forall_mem_real T hTn _ _ hmem
    -- `(1-a)^t ≥ 1 - ta ≥ 3/4`, `(1+a)^t ≤ 1 + 2ta`
    have hlow : 1 - (t : ℝ) * a ≤ (1 - a) ^ t := by
      have := one_add_mul_le_pow (a := -a) (by linarith) t
      simpa [sub_eq_add_neg, mul_neg] using this
    have hup := one_add_pow_le ha0 t (by linarith)
    -- `B ≤ (4/3) p^{M+1}`
    obtain ⟨n₀, hn₀⟩ := hTn
    have hn₀' := (hmem n₀ hn₀).1
    have hn₀lt : (n₀ : ℝ) < (F.p : ℝ) ^ (M + 1) := by
      have : n₀ ∈ S := (mem_filter.1 hn₀).1
      have := (mem_Ico.1 (mem_filter.1 this).1).2
      exact_mod_cast this
    have hB43 : B * (3 / 4) ≤ (F.p : ℝ) ^ (M + 1) := by
      have : B * (3 / 4) ≤ B * (1 - a) ^ t := mul_le_mul_of_nonneg_left (by linarith) hB0
      linarith
    have hdiff : B * (1 + a) ^ t - B * (1 - a) ^ t ≤ B * (3 * ((t : ℝ) * a)) := by
      have : (1 + a) ^ t - (1 - a) ^ t ≤ 3 * ((t : ℝ) * a) := by linarith
      nlinarith
    have hfin : B * (3 * ((t : ℝ) * a)) ≤ 4 * t * a * (F.p : ℝ) ^ (M + 1) := by
      have := mul_le_mul_of_nonneg_right hB43 (by positivity : (0 : ℝ) ≤ 4 * ((t : ℝ) * a))
      nlinarith
    linarith
  calc ∑ s ∈ range (t + 1), (((S.filter (fun n => F.mulCount t n = s)).card : ℕ) : ℝ)
      ≤ ∑ _s ∈ range (t + 1), (1 + 4 * t * a * (F.p : ℝ) ^ (M + 1)) := sum_le_sum hbound
    _ = ((t : ℝ) + 1) * (1 + 4 * t * a * (F.p : ℝ) ^ (M + 1)) := by
        rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

end Family

end GGMCollatz
