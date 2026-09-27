import GGMCollatz.Basic

/-!
# Basic properties of the GGM maps `C`, `S` (counterpart of node C1 of tao-collatz)

Derived from `TaoCollatz/Basic/Collatz.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2;
generalized to the GGM family (p, q, r).

* `oddPart`: the part coprime to `p`, `N / p^{ν_p(N)}` (tao-collatz's `oddPart`; for `p = 2` it is the odd part).
  Since `p` need not be prime, `padicValNat` is treated as a multiplicity, and only lemmas that do not use primality are used.
* `lift N = (qN + r(N mod p)).toNat`: the value of the multiplication step of `C`. `S N = oddPart (lift N)` (by definition).
* `syr_*`: positivity of `S`, `p ∤ S N`, `p^{ν} S N = qN + r(N mod p)` (when `p ∤ N`).
* `colMin_eq_syrMin_oddPart`: `C_min(N) = S_min(oddPart N)` (tao-collatz's (1.2)).
  As corollaries, `colMin_eq_syrMin` (`p ∤ N`) and `colMin_pow_mul` (`C_min(p^k N') = S_min(N')`).

Lemma names follow tao-collatz (`col` ↔ `F.C`, `syr` ↔ `F.S`, `colMin` ↔ `F.Cmin`, `syrMin` ↔ `F.Smin`).
-/

namespace GGMCollatz

namespace Family

variable (F : Family)

/-! ### Basic facts about `p`, and `p`-adic valuation lemmas that do not use primality -/

theorem one_lt_p : 1 < F.p := by have := F.two_le_p; omega

theorem p_pos : 0 < F.p := by have := F.two_le_p; omega

theorem p_ne_one : F.p ≠ 1 := by have := F.two_le_p; omega

theorem p_ne_zero : F.p ≠ 0 := by have := F.two_le_p; omega

theorem q_pos : 0 < F.q := by have := F.two_le_p; have := F.p_lt_q; omega

theorem two_le_q : 2 ≤ F.q := by have := F.two_le_p; have := F.p_lt_q; omega

/-- The part coprime to `p` (tao-collatz's `oddPart`): `N / p^{ν_p(N)}`. -/
def oddPart (N : ℕ) : ℕ := N / F.p ^ padicValNat F.p N

/-- `p^{ν_p(N)}` divides `N`. -/
theorem pow_padicValNat_dvd' (N : ℕ) : F.p ^ padicValNat F.p N ∣ N := pow_padicValNat_dvd

/-- Putting back the extracted power of `p` recovers `N`. -/
theorem pow_mul_oddPart (N : ℕ) : F.p ^ padicValNat F.p N * F.oddPart N = N :=
  Nat.mul_div_cancel' (pow_padicValNat_dvd' F N)

/-- If `N ≠ 0` then `p^{ν+1} ∤ N` (`p` need not be prime). -/
theorem pow_succ_padicValNat_not_dvd' {N : ℕ} (hN : N ≠ 0) :
    ¬ F.p ^ (padicValNat F.p N + 1) ∣ N := by
  rw [padicValNat_dvd_iff_le_of_ne_one F.p_ne_one hN]
  omega

/-- `oddPart` is positive (`N > 0`). -/
theorem oddPart_pos {N : ℕ} (hN : 0 < N) : 0 < F.oddPart N := by
  rcases Nat.eq_zero_or_pos (F.oddPart N) with h | h
  · exact absurd (by rw [← F.pow_mul_oddPart N, h, Nat.mul_zero]) hN.ne'
  · exact h

/-- `oddPart` is not divisible by `p` (`N > 0`). -/
theorem oddPart_mod_ne_zero {N : ℕ} (hN : 0 < N) : F.oddPart N % F.p ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
  apply F.pow_succ_padicValNat_not_dvd' hN.ne'
  exact ⟨k, by rw [pow_succ, mul_assoc, ← hk, F.pow_mul_oddPart N]⟩

/-- If `p^k · w = v`, `p ∤ w` and `w > 0`, then `ν_p(v) = k` (`p` need not be prime). -/
theorem padicValNat_eq_of_mul {v k w : ℕ} (h : F.p ^ k * w = v) (hw : w % F.p ≠ 0) :
    padicValNat F.p v = k := by
  have hw0 : w ≠ 0 := by
    intro h0; apply hw; rw [h0, Nat.zero_mod]
  have hv : v ≠ 0 := by
    rw [← h]; exact Nat.mul_ne_zero (pow_ne_zero _ F.p_ne_zero) hw0
  apply le_antisymm
  · by_contra hlt
    have hk : k + 1 ≤ padicValNat F.p v := by omega
    have hd := (padicValNat_dvd_iff_le_of_ne_one F.p_ne_one hv).2 hk
    rw [← h, pow_succ] at hd
    have hd' : F.p ∣ w :=
      (Nat.mul_dvd_mul_iff_left (pow_pos F.p_pos k)).mp hd
    exact hw (Nat.mod_eq_zero_of_dvd hd')
  · exact (padicValNat_dvd_iff_le_of_ne_one F.p_ne_one hv).1 ⟨w, h.symm⟩

/-- If `p ∤ a` then `ν_p(a) = 0`. -/
theorem padicValNat_of_mod_ne_zero {a : ℕ} (h : a % F.p ≠ 0) : padicValNat F.p a = 0 :=
  padicValNat.eq_zero_of_not_dvd (fun hd => h (Nat.mod_eq_zero_of_dvd hd))

/-- If `p ∤ a` then `oddPart a = a`. -/
theorem oddPart_of_mod_ne_zero {a : ℕ} (h : a % F.p ≠ 0) : F.oddPart a = a := by
  unfold oddPart; rw [F.padicValNat_of_mod_ne_zero h, pow_zero, Nat.div_one]

/-- If `p^k · w = v` and `p ∤ w` then `oddPart v = w`. -/
theorem oddPart_eq_of_mul {v k w : ℕ} (h : F.p ^ k * w = v) (hw : w % F.p ≠ 0) :
    F.oddPart v = w := by
  have hval := F.padicValNat_eq_of_mul h hw
  unfold oddPart
  rw [hval, ← h, Nat.mul_div_cancel_left _ (pow_pos F.p_pos k)]

/-- Multiplying by `p` increases the valuation by one (`a > 0`). -/
theorem padicValNat_p_mul {a : ℕ} (ha : 0 < a) :
    padicValNat F.p (F.p * a) = padicValNat F.p a + 1 := by
  apply F.padicValNat_eq_of_mul (w := F.oddPart a) _ (F.oddPart_mod_ne_zero ha)
  rw [pow_succ, mul_comm (F.p ^ padicValNat F.p a) F.p, mul_assoc, F.pow_mul_oddPart]

/-- `oddPart` is invariant under multiplication by `p` (`a > 0`). -/
theorem oddPart_p_mul {a : ℕ} (ha : 0 < a) : F.oddPart (F.p * a) = F.oddPart a := by
  apply F.oddPart_eq_of_mul (k := padicValNat F.p a + 1) _ (F.oddPart_mod_ne_zero ha)
  rw [pow_succ, mul_comm (F.p ^ padicValNat F.p a) F.p, mul_assoc, F.pow_mul_oddPart]

/-- `oddPart (p^k · N') = N'` (`p ∤ N'`). -/
theorem oddPart_pow_mul {N' : ℕ} (hN' : N' % F.p ≠ 0) (k : ℕ) :
    F.oddPart (F.p ^ k * N') = N' :=
  F.oddPart_eq_of_mul rfl hN'

/-! ### The multiplication step `lift N = qN + r(N mod p)` -/

/-- The value `(qN + r(N mod p)).toNat` of the multiplication step of `C`. `S N = oddPart (lift N)`. -/
def lift (N : ℕ) : ℕ := ((F.q : ℤ) * N + F.r (N % F.p)).toNat

/-- `S` is the part of `lift` coprime to `p` (by definition). -/
theorem syr_eq_oddPart_lift (N : ℕ) : F.S N = F.oddPart (F.lift N) := rfl

/-- If `p ∤ N` then `N mod p ∈ (0, p)`. -/
theorem mod_pos_lt {N : ℕ} (hN : N % F.p ≠ 0) : 0 < N % F.p ∧ N % F.p < F.p :=
  ⟨Nat.pos_of_ne_zero hN, Nat.mod_lt _ F.p_pos⟩

/-- If `p ∤ N` then `qN + r(N mod p) ≥ 1` (in ℤ). -/
theorem one_le_lift_int {N : ℕ} (hN : N % F.p ≠ 0) :
    1 ≤ (F.q : ℤ) * N + F.r (N % F.p) := by
  obtain ⟨h0, hlt⟩ := F.mod_pos_lt hN
  have hpos := F.positive (N % F.p) h0 hlt
  have hle : ((N % F.p : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast Nat.mod_le N F.p
  have hq : (0 : ℤ) ≤ F.q := by positivity
  nlinarith

/-- If `p ∤ N` then `lift N = qN + r(N mod p)` (cast back to ℤ). -/
theorem lift_intCast {N : ℕ} (hN : N % F.p ≠ 0) :
    ((F.lift N : ℕ) : ℤ) = (F.q : ℤ) * N + F.r (N % F.p) :=
  Int.toNat_of_nonneg (by have := F.one_le_lift_int hN; omega)

/-- If `p ∤ N` then `lift N > 0`. -/
theorem lift_pos {N : ℕ} (hN : N % F.p ≠ 0) : 0 < F.lift N := by
  have h := F.lift_intCast hN
  have h1 := F.one_le_lift_int hN
  omega

/-- If `p ∤ N` then `p ∣ qN + r(N mod p)` (in ℤ). From condition (c). -/
theorem p_dvd_lift_int {N : ℕ} (hN : N % F.p ≠ 0) :
    (F.p : ℤ) ∣ (F.q : ℤ) * N + F.r (N % F.p) := by
  obtain ⟨h0, hlt⟩ := F.mod_pos_lt hN
  have hc := F.divisible (N % F.p) h0 hlt
  have hN' : (N : ℤ) = (F.p : ℤ) * ((N / F.p : ℕ) : ℤ) + ((N % F.p : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod N F.p).symm
  have : (F.q : ℤ) * N + F.r (N % F.p)
      = (F.p : ℤ) * ((F.q : ℤ) * ((N / F.p : ℕ) : ℤ))
        + ((F.q : ℤ) * ((N % F.p : ℕ) : ℤ) + F.r (N % F.p)) := by
    rw [hN']; ring
  rw [this]
  exact dvd_add (dvd_mul_right _ _) hc

/-- If `p ∤ N` then `p ∣ lift N`. -/
theorem p_dvd_lift {N : ℕ} (hN : N % F.p ≠ 0) : F.p ∣ F.lift N := by
  have h := F.p_dvd_lift_int hN
  rw [← F.lift_intCast hN] at h
  exact Int.natCast_dvd_natCast.mp h

/-- If `p ∤ N` then the valuation of the multiplication step is at least 1. -/
theorem one_le_val_lift {N : ℕ} (hN : N % F.p ≠ 0) : 1 ≤ padicValNat F.p (F.lift N) := by
  rw [← padicValNat_dvd_iff_le_of_ne_one F.p_ne_one (F.lift_pos hN).ne', pow_one]
  exact F.p_dvd_lift hN

/-! ### Basic properties of `S` -/

/-- `p^{ν} · S N = lift N` (unconditionally). tao-collatz's `two_pow_val_mul_syr'`. -/
theorem pow_val_mul_syr (N : ℕ) :
    F.p ^ padicValNat F.p (F.lift N) * F.S N = F.lift N :=
  F.pow_mul_oddPart (F.lift N)

/-- If `p ∤ N` then `p^{ν} · S N = qN + r(N mod p)` (in ℤ). tao-collatz's `two_pow_val_mul_syr`. -/
theorem pow_val_mul_syr_int {N : ℕ} (hN : N % F.p ≠ 0) :
    (F.p : ℤ) ^ padicValNat F.p (F.lift N) * (F.S N : ℤ) = (F.q : ℤ) * N + F.r (N % F.p) := by
  rw [← F.lift_intCast hN]
  exact_mod_cast F.pow_val_mul_syr N

/-- `S` preserves positivity (`p ∤ N`). -/
theorem syr_pos {N : ℕ} (hN : N % F.p ≠ 0) : 0 < F.S N :=
  F.oddPart_pos (F.lift_pos hN)

/-- The values of `S` are not divisible by `p` (`p ∤ N`). tao-collatz's `syr_odd`. -/
theorem syr_mod_ne_zero {N : ℕ} (hN : N % F.p ≠ 0) : F.S N % F.p ≠ 0 :=
  F.oddPart_mod_ne_zero (F.lift_pos hN)

/-- The iterates of `S` are not divisible by `p` (`p ∤ N`). tao-collatz's `syr_iterate_odd`. -/
theorem syr_iterate_mod_ne_zero {N : ℕ} (hN : N % F.p ≠ 0) : ∀ n, F.S^[n] N % F.p ≠ 0 := by
  intro n
  induction n with
  | zero => simpa using hN
  | succ n ih => rw [Function.iterate_succ_apply']; exact F.syr_mod_ne_zero ih

/-- The iterates of `S` are positive (`p ∤ N`). tao-collatz's `syr_iterate_pos`. -/
theorem syr_iterate_pos {N : ℕ} (hN : N % F.p ≠ 0) : ∀ n, 0 < F.S^[n] N := by
  intro n
  have h := F.syr_iterate_mod_ne_zero hN n
  rcases Nat.eq_zero_or_pos (F.S^[n] N) with h0 | h0
  · rw [h0, Nat.zero_mod] at h; exact absurd rfl h
  · exact h0

/-! ### Basic properties of `C`, and `C_min = S_min` -/

/-- If `p ∣ N` then `C N = N / p`. -/
theorem col_of_mod_eq_zero {N : ℕ} (h : N % F.p = 0) : F.C N = N / F.p := by
  unfold C; rw [if_pos h]

/-- If `p ∤ N` then `C N = lift N`. -/
theorem col_of_mod_ne_zero {N : ℕ} (h : N % F.p ≠ 0) : F.C N = F.lift N := by
  unfold C; rw [if_neg h]; rfl

/-- `C` preserves positivity. -/
theorem col_pos {N : ℕ} (hN : 0 < N) : 0 < F.C N := by
  by_cases h : N % F.p = 0
  · rw [F.col_of_mod_eq_zero h]
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
    rw [hk, Nat.mul_div_cancel_left _ F.p_pos]
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk, hk0, mul_zero] at hN; exact absurd hN (lt_irrefl 0)
    · exact hk0
  · rw [F.col_of_mod_ne_zero h]; exact F.lift_pos h

/-- The iterates of `C` are positive. -/
theorem col_iterate_pos {N : ℕ} (hN : 0 < N) : ∀ k, 0 < F.C^[k] N := by
  intro k; induction k with
  | zero => simpa using hN
  | succ k ih => rw [Function.iterate_succ_apply']; exact F.col_pos ih

/-- In `ν_p(a)` steps, `C` divides `a` down to `oddPart a`. -/
theorem col_iterate_oddPart : ∀ a : ℕ, 0 < a → F.C^[padicValNat F.p a] a = F.oddPart a := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha
    by_cases hmod : a % F.p = 0
    · obtain ⟨b, hb⟩ := Nat.dvd_of_mod_eq_zero hmod
      have hb0 : 0 < b := by
        rcases Nat.eq_zero_or_pos b with h0 | h0
        · rw [hb, h0, mul_zero] at ha; exact absurd ha (lt_irrefl 0)
        · exact h0
      have hlt : b < a := by
        rw [hb]; have := F.two_le_p; nlinarith
      have hval : padicValNat F.p a = padicValNat F.p b + 1 := by
        rw [hb]; exact F.padicValNat_p_mul hb0
      have hcol : F.C a = b := by
        rw [F.col_of_mod_eq_zero hmod, hb, Nat.mul_div_cancel_left _ F.p_pos]
      have hop : F.oddPart b = F.oddPart a := by
        rw [hb, F.oddPart_p_mul hb0]
      rw [hval, Function.iterate_succ_apply, hcol, ih b hlt hb0, hop]
    · rw [F.padicValNat_of_mod_ne_zero hmod, Function.iterate_zero_apply,
        F.oddPart_of_mod_ne_zero hmod]

/-- If `p ∤ M` then `C` reaches `S M` in `ν + 1` steps. -/
theorem col_iterate_syr {M : ℕ} (hM : M % F.p ≠ 0) :
    F.C^[padicValNat F.p (F.lift M) + 1] M = F.S M := by
  rw [Function.iterate_succ_apply, F.col_of_mod_ne_zero hM,
    F.col_iterate_oddPart (F.lift M) (F.lift_pos hM)]
  rfl

/-- **Fact A**: every iterate of `S` on `oddPart N` is an iterate of `C` on `N`. -/
theorem col_reaches_syr {N : ℕ} (hN : 0 < N) :
    ∀ j, ∃ k, F.C^[k] N = F.S^[j] (F.oddPart N) := by
  intro j
  induction j with
  | zero => exact ⟨padicValNat F.p N, by rw [F.col_iterate_oddPart N hN, Function.iterate_zero_apply]⟩
  | succ j ih =>
    obtain ⟨k, hk⟩ := ih
    have hM : F.S^[j] (F.oddPart N) % F.p ≠ 0 :=
      F.syr_iterate_mod_ne_zero (F.oddPart_mod_ne_zero hN) j
    refine ⟨padicValNat F.p (F.lift (F.S^[j] (F.oddPart N))) + 1 + k, ?_⟩
    rw [Function.iterate_add_apply, hk, F.col_iterate_syr hM,
      ← Function.iterate_succ_apply' F.S j]

/-- **Invariant B**: the `oddPart` of every iterate of `C` on `N` is an iterate of `S` on `oddPart N`. -/
theorem oddPart_col_iterate {N : ℕ} (hN : 0 < N) :
    ∀ k, ∃ j, F.oddPart (F.C^[k] N) = F.S^[j] (F.oddPart N) := by
  intro k
  induction k with
  | zero => exact ⟨0, by rw [Function.iterate_zero_apply, Function.iterate_zero_apply]⟩
  | succ k ih =>
    obtain ⟨j, hj⟩ := ih
    set x := F.C^[k] N with hx
    have hxpos : 0 < x := F.col_iterate_pos hN k
    rw [Function.iterate_succ_apply']
    by_cases hmod : x % F.p = 0
    · refine ⟨j, ?_⟩
      obtain ⟨b, hb⟩ := Nat.dvd_of_mod_eq_zero hmod
      have hb0 : 0 < b := by
        rcases Nat.eq_zero_or_pos b with h0 | h0
        · rw [hb, h0, mul_zero] at hxpos; exact absurd hxpos (lt_irrefl 0)
        · exact h0
      rw [F.col_of_mod_eq_zero hmod, hb, Nat.mul_div_cancel_left _ F.p_pos,
        ← F.oddPart_p_mul hb0, ← hb, hj]
    · refine ⟨j + 1, ?_⟩
      have hox : F.oddPart x = x := F.oddPart_of_mod_ne_zero hmod
      rw [F.col_of_mod_ne_zero hmod, ← F.syr_eq_oddPart_lift, Function.iterate_succ_apply',
        ← hj, hox]

/-- **tao-collatz's (1.2)**: `C_min(N) = S_min(oddPart N)` (`N > 0`). -/
theorem colMin_eq_syrMin_oddPart {N : ℕ} (hN : 0 < N) :
    F.Cmin N = F.Smin (F.oddPart N) := by
  apply le_antisymm
  · have hne : (Set.range fun j => F.S^[j] (F.oddPart N)).Nonempty := ⟨F.oddPart N, 0, rfl⟩
    obtain ⟨j, hj⟩ := Nat.sInf_mem hne
    obtain ⟨k, hk⟩ := F.col_reaches_syr hN j
    have hmem : F.Smin (F.oddPart N) ∈ Set.range fun k => F.C^[k] N := by
      refine ⟨k, ?_⟩
      show F.C^[k] N = F.Smin (F.oddPart N)
      rw [hk]; exact hj
    exact Nat.sInf_le hmem
  · have hne : (Set.range fun k => F.C^[k] N).Nonempty := ⟨N, 0, rfl⟩
    obtain ⟨k, hk⟩ := Nat.sInf_mem hne
    obtain ⟨j, hj⟩ := F.oddPart_col_iterate hN k
    have h1 : F.S^[j] (F.oddPart N) ≤ F.C^[k] N := by
      rw [← hj]; unfold oddPart; exact Nat.div_le_self _ _
    calc F.Smin (F.oddPart N) ≤ F.S^[j] (F.oddPart N) := Nat.sInf_le ⟨j, rfl⟩
      _ ≤ F.C^[k] N := h1
      _ = F.Cmin N := hk

/-- If `p ∤ N` then `C_min(N) = S_min(N)`. -/
theorem colMin_eq_syrMin {N : ℕ} (hN : N % F.p ≠ 0) : F.Cmin N = F.Smin N := by
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, Nat.zero_mod] at hN; exact absurd rfl hN
    · exact h
  rw [F.colMin_eq_syrMin_oddPart hN0, F.oddPart_of_mod_ne_zero hN]

/-- `C_min(p^k N') = S_min(N')` (`p ∤ N'`). -/
theorem colMin_pow_mul {N' : ℕ} (hN' : N' % F.p ≠ 0) (k : ℕ) :
    F.Cmin (F.p ^ k * N') = F.Smin N' := by
  have hN0 : 0 < N' := by
    rcases Nat.eq_zero_or_pos N' with h | h
    · rw [h, Nat.zero_mod] at hN'; exact absurd rfl hN'
    · exact h
  rw [F.colMin_eq_syrMin_oddPart (Nat.mul_pos (pow_pos F.p_pos k) hN0),
    F.oddPart_pow_mul hN' k]

end Family

end GGMCollatz
