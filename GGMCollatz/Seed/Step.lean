/- Portions Copyright (c) 2026 Idris Ali Shaik (FirstPassageLinearTransport, Apache License 2.0).
   Modified: generalized to the maps of Goncalves, Greenfeld and Madrid. See NOTICE. -/
import GGMCollatz.Basic

/-!
# Seed (Theorem 4.1 of the paper), part 1: one step of the reduced map, and letters

The construction follows the `Parity` and `Basic` modules of Idris Ali Shaik's
`FirstPassageLinearTransport` (Apache-2.0), rewritten and generalized to the GGM family
(base `p`, general `q`, `r`, arbitrary sign of `r`).

* `Rb`: `R := ∑_{j<p} |r j|` (an upper bound used in place of `max_j |r(j)|` in the accompanying paper).
* `p_mul_Ct_of_mod_ne_zero`: the multiplication step `p · C~(N) = qN + r(N mod p)`.
* `le_Ct_of_mod_ne_zero`: if `(q-p)N ≥ R` then a multiplication step increases (item 3 of the seed
  argument in the accompanying paper).
* `modEq_of_chars`: if the first `m` letters agree, then the numbers are congruent modulo `p^m` (the
  injectivity direction in the accompanying paper).
* `sum_prod_chars_le`: the sum over the shell `I_m` of the product of letters is at most `p-1` times the
  sum over uniform letter sequences.
-/

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- `R := ∑_{j<p} |r j|`. Used as an upper bound for `|r j|` with `0 < j < p`. -/
def Rb : ℕ := ∑ j ∈ Finset.range F.p, (F.r j).natAbs

lemma natAbs_r_le {j : ℕ} (hj : j < F.p) : (F.r j).natAbs ≤ F.Rb :=
  Finset.single_le_sum (f := fun j => (F.r j).natAbs) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 hj)

lemma abs_r_le {j : ℕ} (hj : j < F.p) : |F.r j| ≤ (F.Rb : ℤ) := by
  have := F.natAbs_r_le hj
  rw [Int.abs_eq_natAbs]
  exact_mod_cast this

lemma abs_r_le_real {j : ℕ} (hj : j < F.p) : |(F.r j : ℝ)| ≤ (F.Rb : ℝ) := by
  have := F.abs_r_le hj
  have h : ((|F.r j| : ℤ) : ℝ) ≤ ((F.Rb : ℤ) : ℝ) := by exact_mod_cast this
  simpa using h

lemma p_pos : 0 < F.p := by have := F.two_le_p; omega

lemma one_lt_p : 1 < F.p := by have := F.two_le_p; omega

lemma q_pos : 0 < F.q := lt_trans F.p_pos F.p_lt_q

lemma mod_lt_p (N : ℕ) : N % F.p < F.p := Nat.mod_lt _ F.p_pos

lemma Ct_of_mod_eq_zero {N : ℕ} (h : N % F.p = 0) : F.Ct N = N / F.p := by
  simp [Ct, h]

lemma p_mul_Ct_of_mod_eq_zero {N : ℕ} (h : N % F.p = 0) : F.p * F.Ct N = N := by
  rw [F.Ct_of_mod_eq_zero h]
  exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h)

lemma dvd_q_mul_add_r {N : ℕ} (h : N % F.p ≠ 0) :
    (F.p : ℤ) ∣ (F.q : ℤ) * N + F.r (N % F.p) := by
  have hj0 : 0 < N % F.p := Nat.pos_of_ne_zero h
  have hd := F.divisible (N % F.p) hj0 (F.mod_lt_p N)
  have hN : (N : ℤ) = F.p * ((N / F.p : ℕ) : ℤ) + ((N % F.p : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod N F.p).symm
  have : (F.q : ℤ) * N + F.r (N % F.p)
      = F.p * (F.q * ((N / F.p : ℕ) : ℤ)) + ((F.q : ℤ) * ((N % F.p : ℕ) : ℤ) + F.r (N % F.p)) := by
    rw [hN]; ring
  rw [this]
  exact dvd_add (dvd_mul_right _ _) hd

lemma one_le_q_mul_add_r {N : ℕ} (h : N % F.p ≠ 0) :
    1 ≤ (F.q : ℤ) * N + F.r (N % F.p) := by
  have hj0 : 0 < N % F.p := Nat.pos_of_ne_zero h
  have hpos := F.positive (N % F.p) hj0 (F.mod_lt_p N)
  have hle : ((N % F.p : ℕ) : ℤ) ≤ N := by exact_mod_cast Nat.mod_le N F.p
  have hq : (0 : ℤ) ≤ F.q := by positivity
  nlinarith

/-- Multiplication step: `p · C~(N) = qN + r(N mod p)` (in the integers). -/
lemma p_mul_Ct_of_mod_ne_zero {N : ℕ} (h : N % F.p ≠ 0) :
    (F.p : ℤ) * (F.Ct N : ℤ) = (F.q : ℤ) * N + F.r (N % F.p) := by
  have hd := F.dvd_q_mul_add_r h
  have hpos := F.one_le_q_mul_add_r h
  have hCt : F.Ct N = (((F.q : ℤ) * N + F.r (N % F.p)) / F.p).toNat := by simp [Ct, h]
  have hnn : 0 ≤ ((F.q : ℤ) * N + F.r (N % F.p)) / F.p :=
    Int.ediv_nonneg (by omega) (by positivity)
  rw [hCt, Int.toNat_of_nonneg hnn]
  exact Int.mul_ediv_cancel' hd

lemma p_mul_Ct_real_of_mod_ne_zero {N : ℕ} (h : N % F.p ≠ 0) :
    (F.p : ℝ) * (F.Ct N : ℝ) = (F.q : ℝ) * N + F.r (N % F.p) := by
  have := F.p_mul_Ct_of_mod_ne_zero h
  exact_mod_cast this

lemma p_mul_Ct_real_of_mod_eq_zero {N : ℕ} (h : N % F.p = 0) :
    (F.p : ℝ) * (F.Ct N : ℝ) = N := by
  have := F.p_mul_Ct_of_mod_eq_zero h
  exact_mod_cast this

/-- Increase in a multiplication step (item 3 of the seed argument in the accompanying paper):
if `(q - p)N ≥ R` then `N ≤ C~(N)`. -/
lemma le_Ct_of_mod_ne_zero {N : ℕ} (h : N % F.p ≠ 0)
    (hN : (F.Rb : ℝ) ≤ ((F.q : ℝ) - F.p) * N) : N ≤ F.Ct N := by
  have h1 := F.p_mul_Ct_real_of_mod_ne_zero h
  have h2 := F.abs_r_le_real (F.mod_lt_p N)
  have h3 : -(F.Rb : ℝ) ≤ F.r (N % F.p) := by
    have := neg_abs_le (F.r (N % F.p) : ℝ); linarith
  have hp : (0 : ℝ) < F.p := by exact_mod_cast F.p_pos
  have : (F.p : ℝ) * N ≤ (F.p : ℝ) * (F.Ct N : ℝ) := by nlinarith
  have : (N : ℝ) ≤ F.Ct N := le_of_mul_le_mul_left this hp
  exact_mod_cast this

/-! ## Injectivity of the letters -/

/-- If the first `m` letters agree, then the numbers are congruent modulo `p^m`. -/
lemma modEq_of_chars : ∀ (m n n' : ℕ),
    (∀ k < m, F.Ct^[k] n % F.p = F.Ct^[k] n' % F.p) → n ≡ n' [MOD F.p ^ m] := by
  intro m
  induction m with
  | zero => intro n n' _; simp [Nat.ModEq, Nat.mod_one]
  | succ m ih =>
    intro n n' h
    have h0 : n % F.p = n' % F.p := by simpa using h 0 (Nat.succ_pos m)
    have hrest : ∀ k < m, F.Ct^[k] (F.Ct n) % F.p = F.Ct^[k] (F.Ct n') % F.p := by
      intro k hk
      have := h (k + 1) (by omega)
      simpa [Function.iterate_succ_apply] using this
    have hIH := ih (F.Ct n) (F.Ct n') hrest
    rw [Nat.modEq_iff_dvd] at hIH ⊢
    by_cases hz : n % F.p = 0
    · have hz' : n' % F.p = 0 := by rw [← h0]; exact hz
      have e1 : (n : ℤ) = F.p * (F.Ct n : ℤ) := by exact_mod_cast (F.p_mul_Ct_of_mod_eq_zero hz).symm
      have e2 : (n' : ℤ) = F.p * (F.Ct n' : ℤ) := by
        exact_mod_cast (F.p_mul_Ct_of_mod_eq_zero hz').symm
      rw [e1, e2, ← mul_sub]
      push_cast
      rw [pow_succ, mul_comm ((F.p : ℤ) ^ m)]
      exact mul_dvd_mul_left _ hIH
    · have hz' : n' % F.p ≠ 0 := by rw [← h0]; exact hz
      have e1 := F.p_mul_Ct_of_mod_ne_zero hz
      have e2 := F.p_mul_Ct_of_mod_ne_zero hz'
      rw [← h0] at e2
      have hq : (F.q : ℤ) * ((n' : ℤ) - n) = F.p * ((F.Ct n' : ℤ) - F.Ct n) := by
        rw [mul_sub, mul_sub, e1, e2]; ring
      have hdvd : ((F.p ^ (m + 1) : ℕ) : ℤ) ∣ (F.q : ℤ) * ((n' : ℤ) - n) := by
        rw [hq]
        push_cast
        rw [pow_succ, mul_comm ((F.p : ℤ) ^ m)]
        exact mul_dvd_mul_left _ (by exact_mod_cast hIH)
      have hcop : IsCoprime ((F.p ^ (m + 1) : ℕ) : ℤ) (F.q : ℤ) := by
        rw [Nat.isCoprime_iff_coprime]
        exact Nat.Coprime.pow_left _ F.coprime
      exact hcop.dvd_of_dvd_mul_left hdvd

/-- The sequence of the first `m` letters. -/
def charVec (m n : ℕ) : Fin m → Fin F.p := fun k => ⟨F.Ct^[k] n % F.p, F.mod_lt_p _⟩

/-- In the shell `I_m = [p^m, p^{m+1})`, at most `p - 1` numbers have a given letter sequence. -/
lemma card_fiber_charVec_le (m : ℕ) (w : Fin m → Fin F.p) :
    ((Finset.Ico (F.p ^ m) (F.p ^ (m + 1))).filter (fun n => F.charVec m n = w)).card
      ≤ F.p - 1 := by
  classical
  set S := (Finset.Ico (F.p ^ m) (F.p ^ (m + 1))).filter (fun n => F.charVec m n = w)
  have hpm : 0 < F.p ^ m := pow_pos F.p_pos m
  have hmaps : ∀ n ∈ S, n / F.p ^ m ∈ Finset.Ico 1 F.p := by
    intro n hn
    simp only [S, Finset.mem_filter, Finset.mem_Ico] at hn
    refine Finset.mem_Ico.2 ⟨?_, ?_⟩
    · exact (Nat.le_div_iff_mul_le hpm).2 (by simpa using hn.1.1)
    · exact (Nat.div_lt_iff_lt_mul hpm).2 (by rw [← pow_succ']; exact hn.1.2)
  have hinj : Set.InjOn (fun n => n / F.p ^ m) (S : Set ℕ) := by
    intro n hn n' hn' hdiv
    simp only [S, Finset.coe_filter, Finset.mem_Ico] at hn hn'
    have hc : ∀ k < m, F.Ct^[k] n % F.p = F.Ct^[k] n' % F.p := by
      intro k hk
      have h1 := congrFun hn.2 ⟨k, hk⟩
      have h2 := congrFun hn'.2 ⟨k, hk⟩
      have := h1.trans h2.symm
      simpa [charVec] using congrArg Fin.val this
    have hmod := F.modEq_of_chars m n n' hc
    have hd : n / F.p ^ m = n' / F.p ^ m := hdiv
    calc n = n % F.p ^ m + F.p ^ m * (n / F.p ^ m) := (Nat.mod_add_div n _).symm
      _ = n' % F.p ^ m + F.p ^ m * (n' / F.p ^ m) := by rw [hmod, hd]
      _ = n' := Nat.mod_add_div n' _
  have := Finset.card_le_card_of_injOn (fun n => n / F.p ^ m) hmaps hinj
  simpa using this

/-- Averaging lemma: the sum over the shell `I_m` of the product of the position-wise weights `f k` of
the letters is at most `p - 1` times the sum over uniform letter sequences (the upper-bound direction of
"each sequence is taken `p - 1` times" in the accompanying paper). -/
lemma sum_prod_chars_le (m : ℕ) (f : ℕ → ℕ → ℝ) (hf : ∀ k j, 0 ≤ f k j) :
    ∑ n ∈ Finset.Ico (F.p ^ m) (F.p ^ (m + 1)), ∏ k ∈ Finset.range m, f k (F.Ct^[k] n % F.p)
      ≤ ((F.p : ℝ) - 1) * ∏ k ∈ Finset.range m, ∑ j ∈ Finset.range F.p, f k j := by
  classical
  set I := Finset.Ico (F.p ^ m) (F.p ^ (m + 1))
  set G : (Fin m → Fin F.p) → ℝ := fun w => ∏ k : Fin m, f k (w k) with hG
  have hG0 : ∀ w, 0 ≤ G w := fun w => Finset.prod_nonneg (fun k _ => hf _ _)
  have hrw : ∀ n, ∏ k ∈ Finset.range m, f k (F.Ct^[k] n % F.p) = G (F.charVec m n) := by
    intro n
    simp only [hG, charVec]
    exact (Fin.prod_univ_eq_prod_range (fun k => f k (F.Ct^[k] n % F.p)) m).symm
  simp_rw [hrw]
  rw [Finset.sum_comp]
  have hp1 : ((F.p - 1 : ℕ) : ℝ) = (F.p : ℝ) - 1 := by
    rw [Nat.cast_sub (by have := F.two_le_p; omega)]; simp
  calc ∑ w ∈ I.image (F.charVec m), (I.filter (fun n => F.charVec m n = w)).card • G w
      ≤ ∑ w ∈ I.image (F.charVec m), ((F.p : ℝ) - 1) * G w := by
        apply Finset.sum_le_sum
        intro w _
        rw [nsmul_eq_mul, ← hp1]
        apply mul_le_mul_of_nonneg_right _ (hG0 w)
        exact_mod_cast F.card_fiber_charVec_le m w
    _ ≤ ∑ w : Fin m → Fin F.p, ((F.p : ℝ) - 1) * G w := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro w _ _
        have : (0 : ℝ) ≤ (F.p : ℝ) - 1 := by
          have := F.two_le_p
          have : (2 : ℝ) ≤ F.p := by exact_mod_cast this
          linarith
        exact mul_nonneg this (hG0 w)
    _ = ((F.p : ℝ) - 1) * ∏ k ∈ Finset.range m, ∑ j ∈ Finset.range F.p, f k j := by
        rw [← Finset.mul_sum]
        congr 1
        simp only [hG]
        rw [← Fintype.prod_sum (fun (k : Fin m) (j : Fin F.p) => f k j)]
        rw [← Fin.prod_univ_eq_prod_range (fun k => ∑ j ∈ Finset.range F.p, f k j) m]
        refine Finset.prod_congr rfl (fun k _ => ?_)
        exact Fin.sum_univ_eq_sum_range (fun j => f k j) F.p

end Family

end GGMCollatz
