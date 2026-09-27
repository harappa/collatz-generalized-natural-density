import GGMCollatz.Tao.Sec6.Factor

/-!
# Joint separation of the offsets (GGM §5 Step 2, Lemma 6.9 of the paper) and a pointwise upper bound for the tail density

Derived from `TaoCollatz/Sec6/MixingCore.lean` (`fnat_lt_of_suffix_window`, `fnat_offset_zmod_inj`,
`tailDensW_le_single_mass`, `geomHalf_iid_pos_coords`, `geomHalf_iid_apply_pos`) of gotrevor/tao-collatz
(Apache-2.0), commit 15efca2; generalized to the GGM family (p, q, r).

GGM §5 Step 1 writes `q^n ∑_N P(𝒮_{k+1} = N ∧ …)²` as **equal** to a sum of squares over the pairs `(a, R)`,
which requires a **joint** separation: at most one pair `(a, R)` per residue. The lemma of Step 2 in the
original only states separation for each fixed `R`. Here this is supplied by Lemma 6.9 of the
accompanying paper:

* `r_modp_inj`: if `r(j) ≡ r(j') (mod p)` then `j = j'` (from (a)(c), `r(j) ≡ -qj`).
* `fint_inj_joint`: **`fint(a, r ∘ d)` is injective in `(a, d)`** (on sequences of positive components with
  equal total valuation).
* `two_abs_fint_lt`: from the suffix window `a_{[1,P-r]} ≤ l - s r + K` and the budget, `2 |fint| < q^N`
  (the size estimate of GGM Step 2; `R = R'` is not used).
* `roff_inj_of_window`: lift the congruence modulo `q^N` to an equality of integers, and conclude
  `vt = vt'` by joint injectivity.
* `tailDensW_le_single_mass`: on the window, `tailDensW Y ≤ p^{-l}` (at most one tail per residue, with mass
  `p^{-l}`).
-/

open scoped BigOperators ENNReal

namespace GGMCollatz

namespace Family

variable (F : Family)

/-! ### Injectivity of `r` modulo `p`, and joint injectivity (Lemma 6.9 of the paper) -/

/-- If `p ∣ r(j) - r(j')` (`0 < j, j' < p`) then `j = j'`. -/
theorem r_modp_inj {j j' : ℕ} (h0 : 0 < j) (hj : j < F.p) (h0' : 0 < j') (hj' : j' < F.p)
    (h : (F.p : ℤ) ∣ F.r j - F.r j') : j = j' := by
  have hc := F.divisible j h0 hj
  have hc' := F.divisible j' h0' hj'
  have h1 : (F.p : ℤ) ∣ (F.q : ℤ) * ((j : ℤ) - j') := by
    have h2 := dvd_sub (dvd_sub hc hc') h
    have heq : (F.q : ℤ) * j + F.r j - ((F.q : ℤ) * j' + F.r j') - (F.r j - F.r j')
        = (F.q : ℤ) * ((j : ℤ) - j') := by ring
    rwa [heq] at h2
  have hcop : IsCoprime (F.p : ℤ) (F.q : ℤ) := Nat.isCoprime_iff_coprime.mpr F.coprime
  have h2 : j' ≡ j [MOD F.p] :=
    Nat.modEq_iff_dvd.mpr (by simpa using hcop.dvd_of_dvd_mul_left h1)
  rw [Nat.ModEq, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at h2
  exact h2.symm

/-- **Lemma 6.9 (i) of the paper**: `fint(a, r ∘ d)` is injective in the pair `(a, d)` of a sequence of
positive components with a given total valuation and a sequence of digits in `{1, …, p-1}`. -/
theorem fint_inj_joint : ∀ (n : ℕ) (a a' d d' : Fin n → ℕ),
    (∀ i, 1 ≤ a i) → (∀ i, 1 ≤ a' i) → (∀ i, 0 < d i ∧ d i < F.p) →
    (∀ i, 0 < d' i ∧ d' i < F.p) → pre a n = pre a' n →
    F.fint a (fun i => F.r (d i)) = F.fint a' (fun i => F.r (d' i)) → a = a' ∧ d = d' := by
  intro n
  induction n with
  | zero =>
    intro a a' d d' _ _ _ _ _ _
    exact ⟨funext (fun i => i.elim0), funext (fun i => i.elim0)⟩
  | succ n ih =>
    intro a a' d d' ha ha' hd hd' hpre hf
    have hp0 : (F.p : ℤ) ≠ 0 := by exact_mod_cast F.p_ne_zero
    -- the leading digit is determined modulo `p`
    have hm := F.fint_modp a ha (fun i => F.r (d i)) (Nat.le_succ n)
    have hm' := F.fint_modp a' ha' (fun i => F.r (d' i)) (Nat.le_succ n)
    rw [hf] at hm
    have hdiff : (F.p : ℤ) ∣ (F.q : ℤ) ^ n * (F.r (d 0) - F.r (d' 0)) := by
      have := dvd_sub hm' hm
      have heq : F.fint a' (fun i => F.r (d' i)) - (F.q : ℤ) ^ n * F.r (d' 0)
          - (F.fint a' (fun i => F.r (d' i)) - (F.q : ℤ) ^ n * F.r (d 0))
          = (F.q : ℤ) ^ n * (F.r (d 0) - F.r (d' 0)) := by ring
      rwa [heq] at this
    have hdiff' : (F.p : ℤ) ∣ F.r (d 0) - F.r (d' 0) := by
      simpa using F.dvd_of_dvd_q_pow_mul (s := 1) (e := n) (by simpa using hdiff)
    have hd0 : d 0 = d' 0 := F.r_modp_inj (hd 0).1 (hd 0).2 (hd' 0).1 (hd' 0).2 hdiff'
    -- subtract the leading term
    rw [F.fint_cons, F.fint_cons] at hf
    have hFF : (F.p : ℤ) ^ (a 0) * F.fint (Fin.tail a) (Fin.tail fun i => F.r (d i))
        = (F.p : ℤ) ^ (a' 0) * F.fint (Fin.tail a') (Fin.tail fun i => F.r (d' i)) := by
      rw [hd0] at hf; linarith
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h00 : a 0 = a' 0 := by
        have e1 : pre a 1 = a 0 := by simp [pre]
        have e2 : pre a' 1 = a' 0 := by simp [pre]
        rw [e1, e2] at hpre; exact hpre
      exact ⟨funext (fun i => by rw [Fin.fin_one_eq_zero i]; exact h00),
        funext (fun i => by rw [Fin.fin_one_eq_zero i]; exact hd0)⟩
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hnd : ∀ (b e : Fin (n' + 1 + 1) → ℕ), (∀ i, 1 ≤ b i) → (∀ i, 0 < e i ∧ e i < F.p) →
          ¬ (F.p : ℤ) ∣ F.fint (Fin.tail b) (Fin.tail fun i => F.r (e i)) := by
        intro b e hb he
        exact F.fint_not_dvd (Fin.tail b) (fun i => hb i.succ) _ (by omega)
          (F.r_not_dvd (he 1).1 (he 1).2)
      obtain ⟨h0eq, hFeq⟩ := pow_mul_eq_pow_mul hp0 (hnd a d ha hd) (hnd a' d' ha' hd') hFF
      have hpretail : pre (Fin.tail a) (n' + 1) = pre (Fin.tail a') (n' + 1) := by
        have ea := pre_cons_head a (n' + 1)
        have ea' := pre_cons_head a' (n' + 1)
        rw [ea, ea', h0eq] at hpre; omega
      have htail := ih (Fin.tail a) (Fin.tail a') (Fin.tail d) (Fin.tail d')
        (fun i => ha i.succ) (fun i => ha' i.succ) (fun i => hd i.succ) (fun i => hd' i.succ)
        hpretail hFeq
      exact ⟨funext (fun i => Fin.cases h0eq (fun k => congrFun htail.1 k) i),
        funext (fun i => Fin.cases hd0 (fun k => congrFun htail.2 k) i)⟩

/-! ### The size estimate (GGM §5 Step 2) -/

/-- Fine size estimate: `|fint a R| ≤ B ∑_{m<n} q^{n-1-m} p^{a_{[1,m]}}` (`|R_m| ≤ B`). -/
theorem abs_fint_le_sum {k n : ℕ} (a : Fin k → ℕ) (R : Fin n → ℤ) {B : ℤ}
    (hB : ∀ m, |R m| ≤ B) :
    |F.fint a R| ≤ B * ∑ m : Fin n, (F.q : ℤ) ^ (n - 1 - (m : ℕ)) * (F.p : ℤ) ^ pre a m := by
  unfold fint
  rw [Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun m _ => ?_))
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have h0 : (0 : ℤ) ≤ (F.q : ℤ) ^ (n - 1 - (m : ℕ)) * (F.p : ℤ) ^ pre a m := by positivity
  calc (F.q : ℤ) ^ (n - 1 - (m : ℕ)) * (F.p : ℤ) ^ pre a m * |R m|
      ≤ (F.q : ℤ) ^ (n - 1 - (m : ℕ)) * (F.p : ℤ) ^ pre a m * B :=
        mul_le_mul_of_nonneg_left (hB m) h0
    _ = B * ((F.q : ℤ) ^ (n - 1 - (m : ℕ)) * (F.p : ℤ) ^ pre a m) := by ring

/-- Geometric series estimate under the suffix window (`ρ = q / p^s`):
`∑_{m<n} q^{n-1-m} p^{a_{[1,m]}} ≤ p^{l+K} ∑_{i<n} ρ^i`. -/
theorem sum_window_geom_le {n : ℕ} (a : Fin n → ℕ) (s K l : ℝ) (hs : 0 ≤ s)
    (hsuf : ∀ r : ℕ, 1 ≤ r → r ≤ n → (pre a (n - r) : ℝ) ≤ l - s * r + K) :
    (∑ m : Fin n, (F.q : ℝ) ^ (n - 1 - (m : ℕ)) * (F.p : ℝ) ^ pre a m)
      ≤ (F.p : ℝ) ^ (l + K) * ∑ i ∈ Finset.range n, ((F.q : ℝ) / (F.p : ℝ) ^ s) ^ i := by
  have hp1 : (1 : ℝ) ≤ (F.p : ℝ) := by exact_mod_cast F.p_pos
  have hp0 : (0 : ℝ) < (F.p : ℝ) := by linarith
  have hps1 : (1 : ℝ) ≤ (F.p : ℝ) ^ s := Real.one_le_rpow hp1 hs
  have hps0 : (0 : ℝ) < (F.p : ℝ) ^ s := by linarith
  have hq0 : (0 : ℝ) ≤ (F.q : ℝ) := Nat.cast_nonneg _
  set ρ : ℝ := (F.q : ℝ) / (F.p : ℝ) ^ s with hρdef
  have hterm : ∀ m : Fin n, (F.q : ℝ) ^ (n - 1 - (m : ℕ)) * (F.p : ℝ) ^ pre a m
      ≤ (F.p : ℝ) ^ (l + K) * ρ ^ (n - 1 - (m : ℕ)) := by
    intro m
    have hmn : (m : ℕ) < n := m.isLt
    have hr := hsuf (n - m) (by omega) (by omega)
    rw [show n - (n - (m : ℕ)) = (m : ℕ) by omega] at hr
    have hexp : ((F.p : ℝ) ^ pre a m)
        ≤ (F.p : ℝ) ^ (l + K) / ((F.p : ℝ) ^ s) ^ (n - (m : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast ((F.p : ℝ) ^ s), ← Real.rpow_mul hp0.le,
        ← Real.rpow_sub hp0]
      apply Real.rpow_le_rpow_of_exponent_le hp1
      push_cast [Nat.cast_sub hmn.le]
      push_cast [Nat.cast_sub hmn.le] at hr
      nlinarith
    have hidx : n - 1 - (m : ℕ) + 1 = n - (m : ℕ) := by omega
    calc (F.q : ℝ) ^ (n - 1 - (m : ℕ)) * (F.p : ℝ) ^ pre a m
        ≤ (F.q : ℝ) ^ (n - 1 - (m : ℕ))
            * ((F.p : ℝ) ^ (l + K) / ((F.p : ℝ) ^ s) ^ (n - (m : ℕ))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (F.p : ℝ) ^ (l + K) * (ρ ^ (n - 1 - (m : ℕ)) / (F.p : ℝ) ^ s) := by
          rw [← hidx, pow_succ, hρdef, div_pow]
          field_simp
      _ ≤ (F.p : ℝ) ^ (l + K) * ρ ^ (n - 1 - (m : ℕ)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hp0.le _)
          exact div_le_self (by positivity) hps1
  calc (∑ m : Fin n, (F.q : ℝ) ^ (n - 1 - (m : ℕ)) * (F.p : ℝ) ^ pre a m)
      ≤ ∑ m : Fin n, (F.p : ℝ) ^ (l + K) * ρ ^ (n - 1 - (m : ℕ)) :=
        Finset.sum_le_sum (fun m _ => hterm m)
    _ = (F.p : ℝ) ^ (l + K) * ∑ m ∈ Finset.range n, ρ ^ (n - 1 - m) := by
        rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun m => ρ ^ (n - 1 - m)) n]
    _ = (F.p : ℝ) ^ (l + K) * ∑ i ∈ Finset.range n, ρ ^ i := by
        rw [Finset.sum_range_reflect (fun i => ρ ^ i) n]

/-- **The size estimate of GGM §5 Step 2**: given the suffix window `a_{[1,P-r]} ≤ l - s r + K`
(`1 ≤ r ≤ P`), `q < p^s`, and the budget `2 B_r p^{l+K} < (1 - ρ) q^N` (`ρ = q/p^s`), we have
`2 |fint(a, r ∘ d)| < q^N`. -/
theorem two_abs_fint_lt {N P : ℕ} (vt : Fin P → ℕ × ℕ) (hd : ∀ i, (vt i).2 < F.p)
    (s K l : ℝ) (hs : 0 ≤ s) (hρ : (F.q : ℝ) < (F.p : ℝ) ^ s)
    (hsuf : ∀ r : ℕ, 1 ≤ r → r ≤ P → (pre (fun i => (vt i).1) (P - r) : ℝ) ≤ l - s * r + K)
    (hbudget : 2 * (F.rBound : ℝ) * (F.p : ℝ) ^ (l + K)
      < (1 - (F.q : ℝ) / (F.p : ℝ) ^ s) * (F.q : ℝ) ^ N) :
    2 * |F.fint (fun i => (vt i).1) (fun i => F.r (vt i).2)| < (F.q : ℤ) ^ N := by
  have hp1 : (1 : ℝ) ≤ (F.p : ℝ) := by exact_mod_cast F.p_pos
  have hps0 : (0 : ℝ) < (F.p : ℝ) ^ s := lt_of_lt_of_le zero_lt_one (Real.one_le_rpow hp1 hs)
  set ρ : ℝ := (F.q : ℝ) / (F.p : ℝ) ^ s with hρdef
  have hρ0 : 0 ≤ ρ := div_nonneg (Nat.cast_nonneg _) hps0.le
  have hρ1 : ρ < 1 := (div_lt_one hps0).mpr hρ
  have hint := F.abs_fint_le_sum (fun i => (vt i).1) (fun i => F.r (vt i).2)
    (B := F.rBound) (fun m => F.abs_r_le_rBound (hd m))
  have hreal : (|F.fint (fun i => (vt i).1) (fun i => F.r (vt i).2)| : ℝ)
      ≤ (F.rBound : ℝ) * ∑ m : Fin P, (F.q : ℝ) ^ (P - 1 - (m : ℕ))
          * (F.p : ℝ) ^ pre (fun i => (vt i).1) m := by
    exact_mod_cast hint
  have hsum := F.sum_window_geom_le (fun i => (vt i).1) s K l hs hsuf
  have hgeo : ∑ i ∈ Finset.range P, ρ ^ i ≤ 1 / (1 - ρ) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := P) hρ0 hρ1
    rw [Finset.range_eq_Ico]
    simpa using h
  have hB0 : (0 : ℝ) ≤ (F.rBound : ℝ) := by exact_mod_cast F.rBound_nonneg
  have hpK : (0 : ℝ) ≤ (F.p : ℝ) ^ (l + K) := Real.rpow_nonneg (by linarith) _
  have h1ρ : (0 : ℝ) < 1 - ρ := by linarith
  have hchain : 2 * (|F.fint (fun i => (vt i).1) (fun i => F.r (vt i).2)| : ℝ)
      < (F.q : ℝ) ^ N := by
    calc 2 * (|F.fint (fun i => (vt i).1) (fun i => F.r (vt i).2)| : ℝ)
        ≤ 2 * ((F.rBound : ℝ) * ((F.p : ℝ) ^ (l + K) * (1 / (1 - ρ)))) := by
          gcongr
          exact le_trans hreal (mul_le_mul_of_nonneg_left
            (le_trans hsum (mul_le_mul_of_nonneg_left hgeo hpK)) hB0)
      _ = (2 * (F.rBound : ℝ) * (F.p : ℝ) ^ (l + K)) / (1 - ρ) := by ring
      _ < (F.q : ℝ) ^ N := by
          rw [div_lt_iff₀ h1ρ]; linarith
  exact_mod_cast hchain

/-! ### From a congruence modulo `q^N` to an equality of integers, and then to an equality of tails -/

/-- Points in the support of the i.i.d. one-step law: valuations are at least 1 and digits lie in `{1, …, p-1}`. -/
theorem stepLaw_iid_support_coords {n : ℕ} {v : Fin n → ℕ × ℕ}
    (h : ((stepLaw F.p).iid n) v ≠ 0) : ∀ i, 1 ≤ (v i).1 ∧ 0 < (v i).2 ∧ (v i).2 < F.p := by
  intro i
  rw [iid_stepLaw_apply] at h
  have hi := Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ i)
  have hg : geomP F.p (v i).1 ≠ 0 := left_ne_zero_of_mul hi
  have hu : unifDigit F.p (v i).2 ≠ 0 := right_ne_zero_of_mul hi
  rw [geomP_apply F.two_le_p] at hg
  rw [unifDigit_apply F.two_le_p] at hu
  refine ⟨?_, ?_⟩
  · by_contra hc
    exact hg (if_pos (by omega))
  · by_contra hc
    exact hu (if_neg hc)

/-- The mass of a point in the support is `p^{-|a|}`. -/
theorem stepLaw_iid_mass_of_support {n : ℕ} (v : Fin n → ℕ × ℕ)
    (hpos : ∀ i, 1 ≤ (v i).1 ∧ 0 < (v i).2 ∧ (v i).2 < F.p) :
    ((stepLaw F.p).iid n) v = ((F.p : ℝ≥0∞)⁻¹) ^ pre (fun i => (v i).1) n := by
  have hne : ((F.p - 1 : ℕ) : ℝ≥0∞) ≠ 0 := natCast_sub_one_ne_zero F.two_le_p
  have hnt : ((F.p - 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [iid_stepLaw_apply, pre_eq_fin_sum, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [geomP_apply F.two_le_p, if_neg (by have := (hpos i).1; omega),
    unifDigit_apply F.two_le_p, if_pos (hpos i).2]
  rw [mul_comm (((F.p - 1 : ℕ) : ℝ≥0∞)), mul_assoc, ENNReal.mul_inv_cancel hne hnt, mul_one]

/-- **Separation modulo `q^N`** (the lemma of GGM §5 Step 2, supplemented by Lemma 6.9 of the paper): if the offsets of two
tails on the window agree modulo `q^N` and their total valuations are equal, then the tails are equal. -/
theorem roff_inj_of_window {N P : ℕ} (vt vt' : Fin P → ℕ × ℕ)
    (hpos : ∀ i, 1 ≤ (vt i).1 ∧ 0 < (vt i).2 ∧ (vt i).2 < F.p)
    (hpos' : ∀ i, 1 ≤ (vt' i).1 ∧ 0 < (vt' i).2 ∧ (vt' i).2 < F.p)
    (hl : pre (fun i => (vt i).1) P = pre (fun i => (vt' i).1) P)
    (hb : 2 * |F.fint (fun i => (vt i).1) (fun i => F.r (vt i).2)| < (F.q : ℤ) ^ N)
    (hb' : 2 * |F.fint (fun i => (vt' i).1) (fun i => F.r (vt' i).2)| < (F.q : ℤ) ^ N)
    (hoff : F.roff N vt = F.roff N vt') : vt = vt' := by
  unfold roff at hoff
  rw [hl] at hoff
  set e := pre (fun i => (vt' i).1) P with he
  have hunit : ((F.p : ZMod (F.q ^ N))⁻¹) ^ e * (F.p : ZMod (F.q ^ N)) ^ e = 1 := by
    rw [← mul_pow, F.inv_mul_p_zmod, one_pow]
  have hcast : ((F.fint (fun i => (vt i).1) (fun i => F.r (vt i).2) : ℤ) : ZMod (F.q ^ N))
      = ((F.fint (fun i => (vt' i).1) (fun i => F.r (vt' i).2) : ℤ) : ZMod (F.q ^ N)) := by
    have h := congrArg (· * (F.p : ZMod (F.q ^ N)) ^ e) hoff
    simp only [mul_assoc, hunit, mul_one] at h
    exact h
  have hdvd : ((F.q ^ N : ℕ) : ℤ) ∣ F.fint (fun i => (vt i).1) (fun i => F.r (vt i).2)
      - F.fint (fun i => (vt' i).1) (fun i => F.r (vt' i).2) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcast.symm
  have habs : |F.fint (fun i => (vt i).1) (fun i => F.r (vt i).2)
      - F.fint (fun i => (vt' i).1) (fun i => F.r (vt' i).2)| < ((F.q ^ N : ℕ) : ℤ) := by
    push_cast
    have := abs_sub (F.fint (fun i => (vt i).1) (fun i => F.r (vt i).2))
      (F.fint (fun i => (vt' i).1) (fun i => F.r (vt' i).2))
    have h1 := abs_nonneg (F.fint (fun i => (vt i).1) (fun i => F.r (vt i).2))
    have h2 := abs_nonneg (F.fint (fun i => (vt' i).1) (fun i => F.r (vt' i).2))
    linarith
  have hint := sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdvd habs)
  obtain ⟨ha, hd⟩ := F.fint_inj_joint P (fun i => (vt i).1) (fun i => (vt' i).1)
    (fun i => (vt i).2) (fun i => (vt' i).2) (fun i => (hpos i).1) (fun i => (hpos' i).1)
    (fun i => (hpos i).2) (fun i => (hpos' i).2) hl hint
  funext i
  exact Prod.ext (congrFun ha i) (congrFun hd i)

/-- **Pointwise upper bound for the tail density** (the base factor in GGM §5 Step 1): if every tail on the
window satisfies `2 |fint| < q^{j+P}`, then `tailDensW Y ≤ p^{-l}`. -/
theorem tailDensW_le_single_mass (j P l : ℕ) (W : (Fin P → ℕ × ℕ) → Prop) [DecidablePred W]
    (hwin : ∀ vt : Fin P → ℕ × ℕ, (∀ i, 1 ≤ (vt i).1 ∧ 0 < (vt i).2 ∧ (vt i).2 < F.p) →
      pre (fun i => (vt i).1) P = l → W vt →
      2 * |F.fint (fun i => (vt i).1) (fun i => F.r (vt i).2)| < (F.q : ℤ) ^ (j + P))
    (Y : ZMod (F.q ^ (j + P))) :
    F.tailDensW j P l W Y ≤ ((F.p : ℝ)⁻¹) ^ l := by
  by_cases hex : ∃ vt₀ : Fin P → ℕ × ℕ, (∀ i, 1 ≤ (vt₀ i).1 ∧ 0 < (vt₀ i).2 ∧ (vt₀ i).2 < F.p)
      ∧ F.roff (j + P) vt₀ = Y ∧ pre (fun i => (vt₀ i).1) P = l ∧ W vt₀
  · obtain ⟨vt₀, hpos₀, hoff₀, hl₀, hW₀⟩ := hex
    have hsingle : ∀ vt : Fin P → ℕ × ℕ, vt ≠ vt₀ →
        (((stepLaw F.p).iid P) vt).toReal
          * (if F.roff (j + P) vt = Y ∧ (pre (fun i => (vt i).1) P = l ∧ W vt)
              then (1 : ℝ) else 0) = 0 := by
      intro vt hne
      by_cases hind : F.roff (j + P) vt = Y ∧ (pre (fun i => (vt i).1) P = l ∧ W vt)
      · by_cases hz : ((stepLaw F.p).iid P) vt = 0
        · rw [hz]; simp
        · have hpos := F.stepLaw_iid_support_coords hz
          exact absurd (F.roff_inj_of_window vt vt₀ hpos hpos₀ (by rw [hind.2.1, hl₀])
            (hwin vt hpos hind.2.1 hind.2.2) (hwin vt₀ hpos₀ hl₀ hW₀)
            (by rw [hind.1, hoff₀])) hne
      · rw [if_neg hind, mul_zero]
    refine le_of_eq ?_
    calc F.tailDensW j P l W Y
        = (((stepLaw F.p).iid P) vt₀).toReal
          * (if F.roff (j + P) vt₀ = Y ∧ (pre (fun i => (vt₀ i).1) P = l ∧ W vt₀)
              then (1 : ℝ) else 0) := by
          simp only [tailDensW]
          exact tsum_eq_single vt₀ hsingle
      _ = (((F.p : ℝ≥0∞)⁻¹) ^ l).toReal := by
          rw [if_pos ⟨hoff₀, hl₀, hW₀⟩, mul_one, F.stepLaw_iid_mass_of_support vt₀ hpos₀, hl₀]
      _ = ((F.p : ℝ)⁻¹) ^ l := by
          rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · have hall : ∀ vt : Fin P → ℕ × ℕ,
        (((stepLaw F.p).iid P) vt).toReal
          * (if F.roff (j + P) vt = Y ∧ (pre (fun i => (vt i).1) P = l ∧ W vt)
              then (1 : ℝ) else 0) = 0 := by
      intro vt
      by_cases hind : F.roff (j + P) vt = Y ∧ (pre (fun i => (vt i).1) P = l ∧ W vt)
      · by_cases hz : ((stepLaw F.p).iid P) vt = 0
        · rw [hz]; simp
        · exact absurd ⟨vt, F.stepLaw_iid_support_coords hz, hind.1, hind.2.1, hind.2.2⟩ hex
      · rw [if_neg hind, mul_zero]
    have hzero : F.tailDensW j P l W Y = 0 := by
      simp only [tailDensW]
      exact (tsum_congr hall).trans tsum_zero
    rw [hzero]
    positivity

end Family

end GGMCollatz
