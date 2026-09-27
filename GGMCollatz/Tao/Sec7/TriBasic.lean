import GGMCollatz.Tao.Sec7.Setup

/-!
# Tools for GGM §6 Step 2: exact recurrences for the phase, claims on weakly black points, the lower bound at the edge, upward black columns

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/Triangles.lean`, first half
(`θq_succ_j_exact`, `θq_pred_l_exact`, the claims (i)–(iii) on weakly black points, (7.18), (7.16), the length of upward columns);
generalized to the GGM family (p, q, r). Modified.

Replacements: `9 → q²`, `2 → p`, `ξ` (`3 ∤ ξ`) → the phase multiplier `c` (`q^{2B+2} ∤ c`), the strip `2j + 1 ≤ n` →
`2j + 2B + 2 ≤ n`, the weakly-black threshold `1/100` → `wth = 1/(4p q²(M+1))` (`M = |u| + |v|`, `u q² + v p = 1`).
The identity `θ = θ(j+1) - 4θ(j,l-1) + K` of claim (ii) of tao-collatz is replaced by the Bezout identity `u q² + v p = 1`
(`θ(j,l) = {uθ(j+1,l) + vθ(j,l-1)}` in GGM §6 Step 2). Phases are handled as real values `th`.
Namespace `GGMCollatz.Family.Tri` (to avoid clashes with parallel work).
-/

namespace GGMCollatz

namespace Family

namespace Tri

variable (F : Family)

/-! ### Real-valued phases and recurrences -/

/-- The real value of the phase `θ(j,l)`. -/
noncomputable def th (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) : ℝ := ((F.θq n c j l : ℚ) : ℝ)

theorem black_iff {n : ℕ} {c : ℤ} {ε : ℝ} {j : ℕ} {l : ℤ} :
    F.black n c ε j l ↔ |th F n c j l| ≤ ε := Iff.rfl

theorem th_abs_le_half (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) : |th F n c j l| ≤ 1 / 2 := by
  unfold th
  have h := F.θq_abs_le_half n c j l
  have h' : ((|F.θq n c j l| : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr h
  push_cast at h'
  exact h'

theorem th_succ_j (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) :
    ∃ k : ℤ, th F n c (j + 1) l = (F.q : ℝ) ^ 2 * th F n c j l + k := by
  obtain ⟨k, hk⟩ := F.θq_succ_j n c j l
  exact ⟨k, by unfold th; rw [hk]; push_cast; ring⟩

theorem th_pred_l (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) :
    ∃ k : ℤ, th F n c j (l - 1) = (F.p : ℝ) * th F n c j l + k := by
  obtain ⟨k, hk⟩ := F.θq_pred_l n c j l
  exact ⟨k, by unfold th; rw [hk]; push_cast; ring⟩

theorem int_eq_zero_of_abs_lt_one {k : ℤ} (h : |(k : ℝ)| < 1) : k = 0 := by
  have : |k| < 1 := by exact_mod_cast h
  exact Int.abs_lt_one_iff.mp this

theorem one_le_q_sq : (1 : ℝ) ≤ (F.q : ℝ) ^ 2 := by
  have : (2 : ℝ) ≤ F.q := by exact_mod_cast F.two_le_q
  nlinarith

theorem one_le_p : (1 : ℝ) ≤ (F.p : ℝ) := by
  have : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  linarith

/-- Exact multiplication by `q²` (the exact form of (7.13) of tao-collatz). -/
theorem th_succ_j_exact (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ)
    (h : (F.q : ℝ) ^ 2 * |th F n c j l| < 1 / 2) :
    th F n c (j + 1) l = (F.q : ℝ) ^ 2 * th F n c j l := by
  obtain ⟨k, hk⟩ := th_succ_j F n c j l
  have hq : (0 : ℝ) ≤ (F.q : ℝ) ^ 2 := by positivity
  have hk1 : |(k : ℝ)| < 1 := by
    have e : (k : ℝ) = th F n c (j + 1) l - (F.q : ℝ) ^ 2 * th F n c j l := by linarith
    rw [e]
    calc |th F n c (j + 1) l - (F.q : ℝ) ^ 2 * th F n c j l|
        ≤ |th F n c (j + 1) l| + |(F.q : ℝ) ^ 2 * th F n c j l| := abs_sub _ _
      _ < 1 := by
          rw [abs_mul, abs_of_nonneg hq]
          linarith [th_abs_le_half F n c (j + 1) l]
  rw [hk, int_eq_zero_of_abs_lt_one hk1]
  simp

/-- Exact multiplication by `p` (the exact form of (7.14) of tao-collatz). -/
theorem th_pred_l_exact (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ)
    (h : (F.p : ℝ) * |th F n c j l| < 1 / 2) :
    th F n c j (l - 1) = (F.p : ℝ) * th F n c j l := by
  obtain ⟨k, hk⟩ := th_pred_l F n c j l
  have hp : (0 : ℝ) ≤ (F.p : ℝ) := by positivity
  have hk1 : |(k : ℝ)| < 1 := by
    have e : (k : ℝ) = th F n c j (l - 1) - (F.p : ℝ) * th F n c j l := by linarith
    rw [e]
    calc |th F n c j (l - 1) - (F.p : ℝ) * th F n c j l|
        ≤ |th F n c j (l - 1)| + |(F.p : ℝ) * th F n c j l| := abs_sub _ _
      _ < 1 := by
          rw [abs_mul, abs_of_nonneg hp]
          linarith [th_abs_le_half F n c j (l - 1)]
  rw [hk, int_eq_zero_of_abs_lt_one hk1]
  simp

theorem θq_sfrac_eq (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) :
    sfrac (F.θq n c j l) = F.θq n c j l := by
  unfold Family.θq
  exact sfrac_idem _

/-- `|θ(j+1,l)| ≤ q²|θ(j,l)|` (unconditionally). -/
theorem th_succ_j_abs_le (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) :
    |th F n c (j + 1) l| ≤ (F.q : ℝ) ^ 2 * |th F n c j l| := by
  obtain ⟨k, hk⟩ := F.θq_succ_j n c j l
  have hq : |F.θq n c (j + 1) l| ≤ (F.q : ℚ) ^ 2 * |F.θq n c j l| := by
    calc |F.θq n c (j + 1) l| = |sfrac (F.θq n c (j + 1) l)| := by rw [θq_sfrac_eq]
      _ = |sfrac ((((F.q : ℤ) ^ 2 : ℤ) : ℚ) * F.θq n c j l)| := by rw [hk, sfrac_add_int]
      _ ≤ |(((F.q : ℤ) ^ 2 : ℤ) : ℚ) * F.θq n c j l| := abs_sfrac_le _
      _ = (F.q : ℚ) ^ 2 * |F.θq n c j l| := by
          rw [abs_mul]; push_cast; rw [abs_of_nonneg (by positivity)]
  unfold th
  have := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at this
  exact this

/-- `|θ(j,l-1)| ≤ p|θ(j,l)|` (unconditionally). -/
theorem th_pred_l_abs_le (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) :
    |th F n c j (l - 1)| ≤ (F.p : ℝ) * |th F n c j l| := by
  obtain ⟨k, hk⟩ := F.θq_pred_l n c j l
  have hq : |F.θq n c j (l - 1)| ≤ (F.p : ℚ) * |F.θq n c j l| := by
    calc |F.θq n c j (l - 1)| = |sfrac (F.θq n c j (l - 1))| := by rw [θq_sfrac_eq]
      _ = |sfrac (((F.p : ℤ) : ℚ) * F.θq n c j l)| := by rw [hk, sfrac_add_int]
      _ ≤ |((F.p : ℤ) : ℚ) * F.θq n c j l| := abs_sfrac_le _
      _ = (F.p : ℚ) * |F.θq n c j l| := by
          rw [abs_mul]; push_cast; rw [abs_of_nonneg (by positivity)]
  unfold th
  have := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at this
  exact this

/-! ### (7.18): iteration -/

/-- Iterated (7.13): if `(q²)^a |θ(j,l)| < 1/2` then `θ(j+a,l) = (q²)^a θ(j,l)`. -/
theorem th_iterate_j (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) (a : ℕ)
    (h : ((F.q : ℝ) ^ 2) ^ a * |th F n c j l| < 1 / 2) :
    th F n c (j + a) l = ((F.q : ℝ) ^ 2) ^ a * th F n c j l := by
  induction a with
  | zero => simp
  | succ a IH =>
    have hq1 := one_le_q_sq F
    have hmono : ((F.q : ℝ) ^ 2) ^ a * |th F n c j l|
        ≤ ((F.q : ℝ) ^ 2) ^ (a + 1) * |th F n c j l| :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq1 (by omega)) (abs_nonneg _)
    have hIH := IH (lt_of_le_of_lt hmono h)
    have habs : |th F n c (j + a) l| = ((F.q : ℝ) ^ 2) ^ a * |th F n c j l| := by
      rw [hIH, abs_mul, abs_of_nonneg (by positivity)]
    have hstep := th_succ_j_exact F n c (j + a) l (by
      rw [habs, ← mul_assoc, ← pow_succ']; exact h)
    rw [show j + (a + 1) = (j + a) + 1 by omega, hstep, hIH, pow_succ]
    ring

/-- Iterated (7.14): if `p^b |θ(j,l)| < 1/2` then `θ(j,l-b) = p^b θ(j,l)`. -/
theorem th_iterate_l (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) (b : ℕ)
    (h : (F.p : ℝ) ^ b * |th F n c j l| < 1 / 2) :
    th F n c j (l - b) = (F.p : ℝ) ^ b * th F n c j l := by
  induction b with
  | zero => simp
  | succ b IH =>
    have hp1 := one_le_p F
    have hmono : (F.p : ℝ) ^ b * |th F n c j l| ≤ (F.p : ℝ) ^ (b + 1) * |th F n c j l| :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hp1 (by omega)) (abs_nonneg _)
    have hIH := IH (lt_of_le_of_lt hmono h)
    have habs : |th F n c j (l - b)| = (F.p : ℝ) ^ b * |th F n c j l| := by
      rw [hIH, abs_mul, abs_of_nonneg (by positivity)]
    have hstep := th_pred_l_exact F n c j (l - b) (by
      rw [habs, ← mul_assoc, ← pow_succ']; exact h)
    have hcast : l - ((b + 1 : ℕ) : ℤ) = (l - b) - 1 := by push_cast; ring
    rw [hcast, hstep, hIH, pow_succ]
    ring

/-- **Equality form of (7.18)**: if `(q²)^a p^b |θ(j,l)| < 1/2` then `θ(j+a,l-b) = (q²)^a p^b θ(j,l)`. -/
theorem th_iterate_exact (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) (a b : ℕ)
    (h : ((F.q : ℝ) ^ 2) ^ a * (F.p : ℝ) ^ b * |th F n c j l| < 1 / 2) :
    th F n c (j + a) (l - b) = ((F.q : ℝ) ^ 2) ^ a * (F.p : ℝ) ^ b * th F n c j l := by
  have hpb : (1 : ℝ) ≤ (F.p : ℝ) ^ b := one_le_pow₀ (one_le_p F)
  have hqa : (0 : ℝ) < ((F.q : ℝ) ^ 2) ^ a := by
    have := one_le_q_sq F
    positivity
  have hja : ((F.q : ℝ) ^ 2) ^ a * |th F n c j l| < 1 / 2 := by
    nlinarith [abs_nonneg (th F n c j l)]
  have h1 := th_iterate_j F n c j l a hja
  have habs : |th F n c (j + a) l| = ((F.q : ℝ) ^ 2) ^ a * |th F n c j l| := by
    rw [h1, abs_mul, abs_of_nonneg hqa.le]
  have h2 : (F.p : ℝ) ^ b * |th F n c (j + a) l| < 1 / 2 := by
    rw [habs]
    calc (F.p : ℝ) ^ b * (((F.q : ℝ) ^ 2) ^ a * |th F n c j l|)
        = ((F.q : ℝ) ^ 2) ^ a * (F.p : ℝ) ^ b * |th F n c j l| := by ring
      _ < 1 / 2 := h
  rw [th_iterate_l F n c (j + a) l b h2, h1]
  ring

/-- **Inequality form of (7.18)**: `|θ(j+a,l-b)| ≤ (q²)^a p^b |θ(j,l)|` (unconditionally). -/
theorem th_iterate_abs_le (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) (a b : ℕ) :
    |th F n c (j + a) (l - b)| ≤ ((F.q : ℝ) ^ 2) ^ a * (F.p : ℝ) ^ b * |th F n c j l| := by
  have hj : ∀ a' : ℕ, |th F n c (j + a') l| ≤ ((F.q : ℝ) ^ 2) ^ a' * |th F n c j l| := by
    intro a'
    induction a' with
    | zero => simp
    | succ a' IH =>
      calc |th F n c (j + (a' + 1)) l| = |th F n c ((j + a') + 1) l| := by
            rw [show j + (a' + 1) = (j + a') + 1 by omega]
        _ ≤ (F.q : ℝ) ^ 2 * |th F n c (j + a') l| := th_succ_j_abs_le F n c (j + a') l
        _ ≤ (F.q : ℝ) ^ 2 * (((F.q : ℝ) ^ 2) ^ a' * |th F n c j l|) :=
            mul_le_mul_of_nonneg_left IH (by positivity)
        _ = ((F.q : ℝ) ^ 2) ^ (a' + 1) * |th F n c j l| := by rw [pow_succ]; ring
  induction b with
  | zero => simpa using hj a
  | succ b IH =>
    calc |th F n c (j + a) (l - ((b + 1 : ℕ) : ℤ))| = |th F n c (j + a) ((l - b) - 1)| := by
          rw [show l - ((b + 1 : ℕ) : ℤ) = (l - b) - 1 by push_cast; ring]
      _ ≤ (F.p : ℝ) * |th F n c (j + a) (l - b)| := th_pred_l_abs_le F n c (j + a) (l - b)
      _ ≤ (F.p : ℝ) * (((F.q : ℝ) ^ 2) ^ a * (F.p : ℝ) ^ b * |th F n c j l|) :=
          mul_le_mul_of_nonneg_left IH (by positivity)
      _ = ((F.q : ℝ) ^ 2) ^ a * (F.p : ℝ) ^ (b + 1) * |th F n c j l| := by rw [pow_succ]; ring

/-! ### Bezout coefficients and the weakly-black threshold -/

/-- The Bezout coefficient `u` (`u q² + v p = 1`). -/
noncomputable def bezU : ℤ := Int.gcdA ((F.q : ℤ) ^ 2) (F.p : ℤ)

/-- The Bezout coefficient `v` (`u q² + v p = 1`). -/
noncomputable def bezV : ℤ := Int.gcdB ((F.q : ℤ) ^ 2) (F.p : ℤ)

theorem bez_eq : bezU F * (F.q : ℤ) ^ 2 + bezV F * F.p = 1 := by
  have h := Int.gcd_eq_gcd_ab ((F.q : ℤ) ^ 2) (F.p : ℤ)
  have hg : Int.gcd ((F.q : ℤ) ^ 2) (F.p : ℤ) = 1 := by
    have hc : Nat.Coprime (F.q ^ 2) F.p := Nat.Coprime.pow_left 2 F.coprime.symm
    rw [show ((F.q : ℤ) ^ 2) = ((F.q ^ 2 : ℕ) : ℤ) by push_cast; ring, Int.gcd_natCast_natCast]
    exact hc
  rw [hg] at h
  unfold bezU bezV
  push_cast at h
  linarith

/-- `M = |u| + |v|`. -/
noncomputable def bezM : ℝ := |(bezU F : ℝ)| + |(bezV F : ℝ)|

theorem bezM_nonneg : 0 ≤ bezM F := by unfold bezM; positivity

/-- The weakly-black threshold `w = 1/(4p q²(M+1))` (the `1/100` of tao-collatz). -/
noncomputable def wth : ℝ := 1 / (4 * (F.p : ℝ) * (F.q : ℝ) ^ 2 * (bezM F + 1))

theorem wth_den_pos : 0 < 4 * (F.p : ℝ) * (F.q : ℝ) ^ 2 * (bezM F + 1) := by
  have := bezM_nonneg F
  have hp : (0 : ℝ) < F.p := by have := one_le_p F; linarith
  have hq : (0 : ℝ) < (F.q : ℝ) ^ 2 := by have := one_le_q_sq F; linarith
  positivity

theorem wth_pos : 0 < wth F := by unfold wth; exact div_pos one_pos (wth_den_pos F)

theorem wth_mul : wth F * (4 * (F.p : ℝ) * (F.q : ℝ) ^ 2 * (bezM F + 1)) = 1 := by
  unfold wth; rw [one_div, inv_mul_cancel₀ (wth_den_pos F).ne']

theorem two_le_pR : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p

theorem four_le_q_sq : (4 : ℝ) ≤ (F.q : ℝ) ^ 2 := by
  have : (2 : ℝ) ≤ F.q := by exact_mod_cast F.two_le_q
  nlinarith

/-- `q² w ≤ 1/8`. -/
theorem q2_wth : (F.q : ℝ) ^ 2 * wth F ≤ 1 / 8 := by
  have hm := wth_mul F
  have hw := wth_pos F
  have hM := bezM_nonneg F
  have hp := two_le_pR F
  have hq := four_le_q_sq F
  nlinarith [mul_nonneg hM hw.le, mul_nonneg (mul_nonneg hM hw.le) (by linarith : (0 : ℝ) ≤ F.p),
    mul_pos (mul_pos hw (by linarith : (0 : ℝ) < (F.q : ℝ) ^ 2)) (by linarith : (0 : ℝ) < F.p)]

/-- `p w ≤ 1/16`. -/
theorem p_wth : (F.p : ℝ) * wth F ≤ 1 / 16 := by
  have hm := wth_mul F
  have hw := wth_pos F
  have hM := bezM_nonneg F
  have hp := two_le_pR F
  have hq := four_le_q_sq F
  nlinarith [mul_nonneg hM hw.le, mul_nonneg (mul_nonneg hM hw.le) (by linarith : (0 : ℝ) ≤ (F.q : ℝ) ^ 2),
    mul_pos (mul_pos hw (by linarith : (0 : ℝ) < (F.q : ℝ) ^ 2)) (by linarith : (0 : ℝ) < F.p),
    mul_pos hw (by linarith : (0 : ℝ) < F.p)]

/-- `p q² w ≤ 1/4`. -/
theorem pq2_wth : (F.p : ℝ) * ((F.q : ℝ) ^ 2 * wth F) ≤ 1 / 4 := by
  have hm := wth_mul F
  have hw := wth_pos F
  have hM := bezM_nonneg F
  have hp := two_le_pR F
  have hq := four_le_q_sq F
  have hx : 0 ≤ (F.p : ℝ) * ((F.q : ℝ) ^ 2 * wth F) := by positivity
  nlinarith [mul_nonneg hM hx]

/-- `q² M w ≤ 1/8`. -/
theorem q2M_wth : (F.q : ℝ) ^ 2 * (bezM F * wth F) ≤ 1 / 8 := by
  have hm := wth_mul F
  have hw := wth_pos F
  have hM := bezM_nonneg F
  have hp := two_le_pR F
  have hq := four_le_q_sq F
  have hx : 0 ≤ (F.q : ℝ) ^ 2 * (bezM F * wth F) := by positivity
  have hy : 0 ≤ (F.q : ℝ) ^ 2 * wth F := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ F.p from hp) hx,
    mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ F.p from hp) hy]

/-- `M w ≤ 1/8`. -/
theorem M_wth : bezM F * wth F ≤ 1 / 8 := by
  have h := q2M_wth F
  have hq := one_le_q_sq F
  have hx : 0 ≤ bezM F * wth F := mul_nonneg (bezM_nonneg F) (wth_pos F).le
  nlinarith

/-- `w ≤ 1/8`. -/
theorem wth_le : wth F ≤ 1 / 8 := by
  have h := q2_wth F
  have hq := one_le_q_sq F
  have hw := (wth_pos F).le
  nlinarith

/-! ### Weakly black points (claims (i)–(iii) on p.38 of tao-collatz) -/

/-- Weakly black points: `|θ(j,l)| ≤ w`. -/
def wb (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) : Prop := |th F n c j l| ≤ wth F

section Claims

variable {F} {n : ℕ} {c : ℤ} {ε : ℝ}

theorem wb_of_black (hεw : ε ≤ wth F) {j : ℕ} {l : ℤ} (h : F.black n c ε j l) :
    wb F n c j l := le_trans h hεw

/-- **Claim (i), `j` form**: if `(j,l)` is weakly black and `(j+1,l)` is black, then `(j,l)` is black. -/
theorem black_of_wb_succ_j {j : ℕ} {l : ℤ} (hw : wb F n c j l)
    (hb : F.black n c ε (j + 1) l) : F.black n c ε j l := by
  rw [black_iff] at hb ⊢
  have hq2w := q2_wth F
  have hw' : |th F n c j l| ≤ wth F := hw
  have hq1 := one_le_q_sq F
  have he := th_succ_j_exact F n c j l (by nlinarith [abs_nonneg (th F n c j l)])
  rw [he, abs_mul, abs_of_nonneg (by positivity)] at hb
  nlinarith [abs_nonneg (th F n c j l)]

/-- **Claim (i), `l` form**: if `(j,l)` is weakly black and `(j,l-1)` is black, then `(j,l)` is black. -/
theorem black_of_wb_pred_l {j : ℕ} {l : ℤ} (hw : wb F n c j l)
    (hb : F.black n c ε j (l - 1)) : F.black n c ε j l := by
  rw [black_iff] at hb ⊢
  have hpw := p_wth F
  have hw' : |th F n c j l| ≤ wth F := hw
  have hp1 := one_le_p F
  have he := th_pred_l_exact F n c j l (by nlinarith [abs_nonneg (th F n c j l)])
  rw [he, abs_mul, abs_of_nonneg (by positivity)] at hb
  nlinarith [abs_nonneg (th F n c j l)]

/-- **Claim (ii)**: if `(j+1,l)` and `(j,l-1)` are weakly black, then `(j,l)` is weakly black (Bezout identity). -/
theorem wb_of_succ_j_pred_l {j : ℕ} {l : ℤ} (h1 : wb F n c (j + 1) l)
    (h2 : wb F n c j (l - 1)) : wb F n c j l := by
  have h1' : |th F n c (j + 1) l| ≤ wth F := h1
  have h2' : |th F n c j (l - 1)| ≤ wth F := h2
  obtain ⟨k₁, hk₁⟩ := th_succ_j F n c j l
  obtain ⟨k₂, hk₂⟩ := th_pred_l F n c j l
  have hb : ((bezU F : ℤ) : ℝ) * (F.q : ℝ) ^ 2 + ((bezV F : ℤ) : ℝ) * F.p = 1 := by
    have := bez_eq F
    exact_mod_cast this
  set u : ℝ := ((bezU F : ℤ) : ℝ) with hu
  set v : ℝ := ((bezV F : ℤ) : ℝ) with hv
  set K : ℤ := bezU F * k₁ + bezV F * k₂ with hK
  have hcomb : th F n c j l + (K : ℝ) = u * th F n c (j + 1) l + v * th F n c j (l - 1) := by
    rw [hk₁, hk₂, hK]
    push_cast
    linear_combination (-(th F n c j l)) * hb
  have hsmall : |u * th F n c (j + 1) l + v * th F n c j (l - 1)| ≤ bezM F * wth F := by
    calc |u * th F n c (j + 1) l + v * th F n c j (l - 1)|
        ≤ |u * th F n c (j + 1) l| + |v * th F n c j (l - 1)| := abs_add_le _ _
      _ = |u| * |th F n c (j + 1) l| + |v| * |th F n c j (l - 1)| := by rw [abs_mul, abs_mul]
      _ ≤ |u| * wth F + |v| * wth F := by
          gcongr
      _ = bezM F * wth F := by unfold bezM; rw [← hu, ← hv]; ring
  have hMw := M_wth F
  have hK0 : K = 0 := by
    apply int_eq_zero_of_abs_lt_one
    have e : (K : ℝ) = (th F n c j l + (K : ℝ)) - th F n c j l := by ring
    rw [e]
    calc |(th F n c j l + (K : ℝ)) - th F n c j l|
        ≤ |th F n c j l + (K : ℝ)| + |th F n c j l| := abs_sub _ _
      _ < 1 := by rw [hcomb]; linarith [th_abs_le_half F n c j l]
  have hθ : |th F n c j l| ≤ bezM F * wth F := by
    have : th F n c j l = u * th F n c (j + 1) l + v * th F n c j (l - 1) := by
      rw [← hcomb, hK0]; simp
    rw [this]; exact hsmall
  have hq2M := q2M_wth F
  have hq1 := one_le_q_sq F
  have hex := th_succ_j_exact F n c j l (by nlinarith [abs_nonneg (th F n c j l)])
  rw [hex, abs_mul, abs_of_nonneg (by positivity)] at h1'
  show |th F n c j l| ≤ wth F
  nlinarith [abs_nonneg (th F n c j l)]

/-- **Claim (iii)**: if `(j,l)` and `(j+1,l-1)` are weakly black, then `(j+1,l)` is weakly black. -/
theorem wb_of_pred_j_pred_l {j : ℕ} {l : ℤ} (h1 : wb F n c j l)
    (h2 : wb F n c (j + 1) (l - 1)) : wb F n c (j + 1) l := by
  have h1' : |th F n c j l| ≤ wth F := h1
  have h2' : |th F n c (j + 1) (l - 1)| ≤ wth F := h2
  have hq2w := q2_wth F
  have hpq2w := pq2_wth F
  have hq1 := one_le_q_sq F
  have hp1 := one_le_p F
  have he := th_succ_j_exact F n c j l (by nlinarith [abs_nonneg (th F n c j l)])
  have h9 : |th F n c (j + 1) l| ≤ (F.q : ℝ) ^ 2 * wth F := by
    rw [he, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left h1' (by positivity)
  have he2 := th_pred_l_exact F n c (j + 1) l (by
    have := mul_le_mul_of_nonneg_left h9 (by positivity : (0 : ℝ) ≤ F.p)
    linarith)
  rw [he2, abs_mul, abs_of_nonneg (by positivity)] at h2'
  show |th F n c (j + 1) l| ≤ wth F
  nlinarith [abs_nonneg (th F n c (j + 1) l)]

end Claims

/-! ### The lower bound at the edge (counterpart of (7.16)) and upward black columns -/

/-- **Lower bound at the edge**: if `q^{2B+2} ∤ c` and `2j + 2B + 2 ≤ n`, then `|θ(j,l)| ≥ q^{-(n-2j)}`. -/
theorem th_lower_bound {n : ℕ} {c : ℤ} (hc : ¬ (F.q : ℤ) ^ (2 * F.edgeB + 2) ∣ c)
    {j : ℕ} (l : ℤ) (hj : 2 * j + 2 * F.edgeB + 2 ≤ n) :
    1 / (F.q : ℝ) ^ (n - 2 * j) ≤ |th F n c j l| := by
  have := F.neZero_q_pow n
  have hq0 : 0 < F.q := F.q_pos
  set N := n - 2 * j with hN
  set W := F.phasePt n c j l with hW
  set u : ZMod (F.q ^ n) := (((F.up n) ^ (1 - l) : (ZMod (F.q ^ n))ˣ) : ZMod (F.q ^ n)) with hu
  set Y : ZMod (F.q ^ n) := (c : ZMod (F.q ^ n)) * u with hY
  have hWY : W = ((F.q ^ (2 * j) * Y.val : ℕ) : ZMod (F.q ^ n)) := by
    rw [hW]; unfold phasePt; push_cast; rw [ZMod.natCast_zmod_val, hY, hu]; ring
  have hWval : W.val = (F.q ^ (2 * j) * Y.val) % F.q ^ n := by rw [hWY, ZMod.val_natCast]
  have hdvd : F.q ^ (2 * j) ∣ W.val := by
    rw [hWval, Nat.dvd_mod_iff (pow_dvd_pow _ (by omega))]
    exact dvd_mul_right _ _
  obtain ⟨X, hX⟩ := hdvd
  -- `W ≠ 0`
  have hW0 : W ≠ 0 := by
    intro h0
    have h1 : ((c * (F.q : ℤ) ^ (2 * j) : ℤ) : ZMod (F.q ^ n)) = 0 := by
      have : ((c * (F.q : ℤ) ^ (2 * j) : ℤ) : ZMod (F.q ^ n)) * u = 0 := by
        rw [← h0, hW]; unfold phasePt; push_cast; rw [hu]
      exact (Units.mul_left_eq_zero _).mp this
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (F.q ^ n)).mp h1
    have h3 : (F.q : ℤ) ^ N ∣ c := by
      have hn : ((F.q ^ n : ℕ) : ℤ) = (F.q : ℤ) ^ N * (F.q : ℤ) ^ (2 * j) := by
        push_cast; rw [← pow_add]; congr 1; omega
      rw [hn] at h2
      exact (mul_dvd_mul_iff_right (pow_ne_zero _ (by exact_mod_cast hq0.ne'))).mp h2
    exact hc (dvd_trans (pow_dvd_pow _ (by omega)) h3)
  -- `θ q^n = W.val - r q^n`
  set r : ℤ := round ((W.val : ℚ) / (F.q : ℚ) ^ n) with hr
  have hqnR : (0 : ℝ) < (F.q : ℝ) ^ n := by positivity
  have hth : th F n c j l * (F.q : ℝ) ^ n = (W.val : ℝ) - r * (F.q : ℝ) ^ n := by
    unfold th Family.θq sfrac
    rw [← hW, ← hr]
    push_cast
    field_simp
  have hqn : (F.q : ℝ) ^ n = (F.q : ℝ) ^ (2 * j) * (F.q : ℝ) ^ N := by
    rw [← pow_add]; congr 1; omega
  have hWr : (W.val : ℝ) = (F.q : ℝ) ^ (2 * j) * X := by rw [hX]; push_cast; ring
  set m : ℤ := (X : ℤ) - r * (F.q : ℤ) ^ N with hm
  have hmR : th F n c j l * (F.q : ℝ) ^ N = (m : ℝ) := by
    have hpos : (F.q : ℝ) ^ (2 * j) ≠ 0 := by positivity
    apply mul_left_cancel₀ hpos
    rw [hm]
    push_cast
    calc (F.q : ℝ) ^ (2 * j) * (th F n c j l * (F.q : ℝ) ^ N)
        = th F n c j l * (F.q : ℝ) ^ n := by rw [hqn]; ring
      _ = (W.val : ℝ) - r * (F.q : ℝ) ^ n := hth
      _ = (F.q : ℝ) ^ (2 * j) * ((X : ℝ) - r * (F.q : ℝ) ^ N) := by rw [hWr, hqn]; ring
  -- `m ≠ 0`
  have hm0 : m ≠ 0 := by
    intro hm0
    have hth0 : th F n c j l = 0 := by
      have hqN : (F.q : ℝ) ^ N ≠ 0 := by positivity
      have : th F n c j l * (F.q : ℝ) ^ N = 0 := by rw [hmR, hm0]; simp
      exact (mul_eq_zero.mp this).resolve_right hqN
    have hWeq : (W.val : ℝ) = r * (F.q : ℝ) ^ n := by rw [hth0] at hth; linarith
    have hWeqZ : (W.val : ℤ) = r * ((F.q : ℤ) ^ n) := by exact_mod_cast hWeq
    have hlt : (W.val : ℤ) < (F.q : ℤ) ^ n := by exact_mod_cast ZMod.val_lt W
    have hqnZ : (0 : ℤ) < (F.q : ℤ) ^ n := by positivity
    have hr0 : r = 0 := by
      have hge : (0 : ℤ) ≤ r * (F.q : ℤ) ^ n := by rw [← hWeqZ]; positivity
      rcases lt_trichotomy r 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    rw [hr0, zero_mul] at hWeqZ
    have : W.val = 0 := by exact_mod_cast hWeqZ
    exact hW0 ((ZMod.val_eq_zero W).mp this)
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm0
    exact_mod_cast this
  have hqNpos : (0 : ℝ) < (F.q : ℝ) ^ N := by positivity
  rw [div_le_iff₀ hqNpos]
  calc (1 : ℝ) ≤ |(m : ℝ)| := hm1
    _ = |th F n c j l| * (F.q : ℝ) ^ N := by
        rw [← hmR, abs_mul, abs_of_pos hqNpos]

/-- Basic hypotheses: `q^{2B+2} ∤ c`, `0 < ε ≤ w`. -/
structure Hyp (n : ℕ) (c : ℤ) (ε : ℝ) : Prop where
  hc : ¬ (F.q : ℤ) ^ (2 * F.edgeB + 2) ∣ c
  pos : 0 < ε
  le_w : ε ≤ wth F

section Runs

variable {F} {n : ℕ} {c : ℤ} {ε : ℝ}

theorem Hyp.p_eps (H : Hyp F n c ε) : (F.p : ℝ) * ε < 1 / 2 := by
  have := p_wth F
  have hp : (0 : ℝ) ≤ F.p := by positivity
  have := mul_le_mul_of_nonneg_left H.le_w hp
  linarith

theorem Hyp.q2_eps (H : Hyp F n c ε) : (F.q : ℝ) ^ 2 * ε < 1 / 2 := by
  have := q2_wth F
  have hq : (0 : ℝ) ≤ (F.q : ℝ) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left H.le_w hq
  linarith

/-- Along an upward black column, `θ(j,l) = p^t θ(j,l+t)`. -/
theorem th_up_run (H : Hyp F n c ε) (j : ℕ) (l : ℤ) (t : ℕ)
    (hb : ∀ i : ℕ, 1 ≤ i → i ≤ t → F.black n c ε j (l + i)) :
    th F n c j l = (F.p : ℝ) ^ t * th F n c j (l + t) := by
  induction t with
  | zero => simp
  | succ t IH =>
    have hbt : |th F n c j (l + ((t + 1 : ℕ) : ℤ))| ≤ ε := hb (t + 1) (by omega) le_rfl
    have hsmall : (F.p : ℝ) * |th F n c j (l + ((t + 1 : ℕ) : ℤ))| < 1 / 2 := by
      have := H.p_eps
      have hp : (0 : ℝ) ≤ F.p := by positivity
      have := mul_le_mul_of_nonneg_left hbt hp
      linarith
    have hstep := th_pred_l_exact F n c j (l + ((t + 1 : ℕ) : ℤ)) hsmall
    have hcast : l + ((t + 1 : ℕ) : ℤ) - 1 = l + t := by push_cast; ring
    rw [hcast] at hstep
    rw [IH (fun i h1 h2 => hb i h1 (by omega)), hstep]
    ring

/-- Upward black columns are short: `p^t ≤ ε q^{n-2j}`. -/
theorem black_run_le (H : Hyp F n c ε) {j : ℕ} {l : ℤ} {t : ℕ}
    (h2j : 2 * j + 2 * F.edgeB + 2 ≤ n) (hb : ∀ i : ℕ, i ≤ t → F.black n c ε j (l + i)) :
    (F.p : ℝ) ^ t ≤ ε * (F.q : ℝ) ^ (n - 2 * j) := by
  have hrun := th_up_run H j l t (fun i _ h2 => hb i h2)
  have hlow := th_lower_bound F H.hc (l + t) h2j
  have hb0 : |th F n c j l| ≤ ε := by
    have h0 := hb 0 (by omega)
    rw [Nat.cast_zero, add_zero] at h0
    exact h0
  have habs : |th F n c j l| = (F.p : ℝ) ^ t * |th F n c j (l + t)| := by
    rw [hrun, abs_mul, abs_of_nonneg (by positivity)]
  have hq : (0 : ℝ) < (F.q : ℝ) ^ (n - 2 * j) := by have := F.q_pos; positivity
  have hchain : (F.p : ℝ) ^ t * (1 / (F.q : ℝ) ^ (n - 2 * j)) ≤ ε := by
    calc (F.p : ℝ) ^ t * (1 / (F.q : ℝ) ^ (n - 2 * j))
        ≤ (F.p : ℝ) ^ t * |th F n c j (l + t)| :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
      _ = |th F n c j l| := habs.symm
      _ ≤ ε := hb0
  calc (F.p : ℝ) ^ t = ((F.p : ℝ) ^ t * (1 / (F.q : ℝ) ^ (n - 2 * j))) * (F.q : ℝ) ^ (n - 2 * j) := by
        field_simp
    _ ≤ ε * (F.q : ℝ) ^ (n - 2 * j) := mul_le_mul_of_nonneg_right hchain hq.le

/-- In column `j` there is a white point somewhere at or above `l`. -/
theorem exists_white_above (H : Hyp F n c ε) (j : ℕ) (l : ℤ)
    (h2j : 2 * j + 2 * F.edgeB + 2 ≤ n) :
    ∃ t : ℕ, ¬ F.black n c ε j (l + t) := by
  by_contra hall
  push Not at hall
  have hp : (1 : ℝ) < F.p := by have := two_le_pR F; linarith
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (ε * (F.q : ℝ) ^ (n - 2 * j)) hp
  exact absurd (black_run_le H h2j (fun i _ => hall i)) (not_le.mpr ht)

end Runs

end Tri

end Family

end GGMCollatz
