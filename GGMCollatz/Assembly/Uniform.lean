import GGMCollatz.Seed
import GGMCollatz.Assembly.Window

/-!
# The assembly of (A), part 5: a power rate uniform over windows (Theorem 5.7 (i) of the paper)

`uniform`: from the one-step recursion `StepHyp` (the content of `oneStep_statement`) and the seed theorem,
there are `K, c' > 0` such that for all `N₀ ≥ 1` and `y > 0`, `P(N₀, y) ≤ K N₀^{-c'}`.

Modeled on the assembly of the companion manuscript for the Collatz map (*A power-saving bound, uniform in the endpoint, for Collatz orbits that stay above a fixed barrier*; `window_uniform`, `rate_to_N0`,
`nd_syracuse_uniform_of_fixedBarrier` in `lean-nd/CollatzND/Core/Uniform.lean`; `p_iter_step`, `err_sum` in
`lean/CollatzProof/Core/TaoRec.lean`; `represent` in `lean/CollatzProof/Core/TaoFinal.lean`). Rewritten with
the fixed window width `α = 1.001` generalized to arbitrary `α > 1`, and the base 2 generalized to `p`.

**Choice of parameters** (as in Section 5 of the paper): `v := e^{c_B L/4}`, because the
estimate of the bottom windows (`windowProb_base`) carries the factor from the number of shells squared.
The rate is `c₁ = c_B min(1/2, c^G/4)`, `c' = c₁/(2 log p)`.
Also, the choice of `J` in (ii) of the paper (`v ≤ ln x₁ < αv`) is obtained in the same way by
`represent` (`X₁ = e^v ≤ x₁ < X₁^α`).
-/

namespace GGMCollatz

namespace Asm

/-- The hypothesis of the one-step recursion (window width `α`, exponent `c`, constant `C_s`,
threshold `X_s`). -/
def StepHyp (F : Family) (α c Cs Xs : ℝ) : Prop :=
  ∀ x : ℝ, Xs ≤ x → ∀ N₀ : ℕ, 1 ≤ N₀ → (N₀ : ℝ) ≤ x →
    F.windowProb α N₀ (x ^ (α ^ 2)) ≤ F.windowProb α N₀ (x ^ α) + Cs * (Real.log x) ^ (-c)

/-- From `oneStep_statement`, a `StepHyp` normalized to `C_s ≥ 0`. -/
theorem stepHyp_of_oneStep (F : Family) (h : F.oneStep_statement) :
    ∃ α c Cs Xs : ℝ, 1 < α ∧ 0 < c ∧ 0 ≤ Cs ∧ StepHyp F α c Cs Xs := by
  obtain ⟨α, hα, c, hc, Cs, Xs, hS⟩ := h
  refine ⟨α, c, max Cs 0, max Xs 1, hα, hc, le_max_right _ _, ?_⟩
  intro x hx N₀ hN₀ hN₀x
  have h1 := hS x (le_trans (le_max_left _ _) hx) N₀ hN₀ hN₀x
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hl : 0 ≤ (Real.log x) ^ (-c) := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have : Cs * (Real.log x) ^ (-c) ≤ max Cs 0 * (Real.log x) ^ (-c) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hl
  linarith

/-- Write the window position `x ≥ X₁^α` as `x = x₁^{α^{J+1}}` with `X₁ ≤ x₁ < X₁^α` (`represent` of
`lean/CollatzProof/Core/TaoFinal.lean`, for general `α`). -/
lemma represent {α : ℝ} (hα : 1 < α) (X1 x : ℝ) (hX1 : 1 < X1) (hx : X1 ^ α ≤ x) :
    ∃ J : ℕ, ∃ x1 : ℝ, X1 ≤ x1 ∧ x1 < X1 ^ α ∧ x = x1 ^ (α ^ (J + 1)) := by
  have hα0 : 0 < α := by linarith
  have hlX : 0 < Real.log X1 := Real.log_pos hX1
  have hx1 : 1 < x := lt_of_lt_of_le (Real.one_lt_rpow hX1 hα0) hx
  set r := Real.log x / Real.log X1
  have hr : α ≤ r := by
    rw [le_div_iff₀ hlX]
    have := Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _) hx
    rw [Real.log_rpow (by linarith)] at this
    linarith
  have hex : ∃ n : ℕ, r < α ^ n := pow_unbounded_of_one_lt r hα
  set n := Nat.find hex
  have hn : r < α ^ n := Nat.find_spec hex
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    interval_cases h : n
    · simp at hn; linarith
    · simp at hn; linarith
  have hprev : α ^ (n - 1) ≤ r := by
    have := Nat.find_min hex (show n - 1 < n by omega)
    push Not at this; exact this
  refine ⟨n - 2, x ^ ((α ^ (n - 1))⁻¹), ?_, ?_, ?_⟩
  · have hp : 0 < α ^ (n - 1) := pow_pos hα0 _
    rw [← Real.log_le_log_iff (by linarith) (Real.rpow_pos_of_pos (by linarith) _),
      Real.log_rpow (by linarith)]
    rw [le_div_iff₀ hlX] at hprev
    rw [inv_mul_eq_div, le_div_iff₀ hp]; linarith
  · have hp : 0 < α ^ (n - 1) := pow_pos hα0 _
    rw [← Real.log_lt_log_iff (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_pos_of_pos (by linarith) _), Real.log_rpow (by linarith), Real.log_rpow (by linarith)]
    rw [div_lt_iff₀ hlX] at hn
    have e : α ^ n = α ^ (n - 1) * α := by rw [← pow_succ]; congr 1; omega
    rw [e] at hn
    rw [inv_mul_eq_div, div_lt_iff₀ hp]; nlinarith
  · have e : n - 2 + 1 = n - 1 := by omega
    rw [e, ← Real.rpow_mul (by linarith), inv_mul_cancel₀ (pow_pos hα0 _).ne', Real.rpow_one]

lemma le_rpow_pow {α : ℝ} (hα : 1 < α) (x1 : ℝ) (hx1 : 1 ≤ x1) (j : ℕ) : x1 ≤ x1 ^ (α ^ j) := by
  have h1 : (1 : ℝ) ≤ α ^ j := one_le_pow₀ hα.le
  calc x1 = x1 ^ (1 : ℝ) := (Real.rpow_one x1).symm
    _ ≤ x1 ^ (α ^ j) := Real.rpow_le_rpow_of_exponent_le hx1 h1

/-- Iteration of `StepHyp` (a generalization of `p_iter_step`). -/
theorem iter_step (F : Family) {α c Cs Xs : ℝ} (hα : 1 < α) (hS : StepHyp F α c Cs Xs)
    (N₀ : ℕ) (hN₀ : 1 ≤ N₀) (x1 : ℝ) (hx1 : 1 ≤ x1) (hX : Xs ≤ x1) (hxN : (N₀ : ℝ) ≤ x1) :
    ∀ J : ℕ, F.windowProb α N₀ (x1 ^ (α ^ (J + 1))) ≤ F.windowProb α N₀ (x1 ^ α) +
      ∑ j ∈ Finset.range J, Cs * (Real.log (x1 ^ (α ^ j))) ^ (-c) := by
  have hx0 : 0 ≤ x1 := by linarith
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
    have hz := le_rpow_pow hα x1 hx1 J
    have hstep := hS (x1 ^ (α ^ J)) (le_trans hX hz) N₀ hN₀ (le_trans hxN hz)
    rw [← Real.rpow_mul hx0, ← Real.rpow_mul hx0, ← pow_succ, ← pow_add] at hstep
    rw [Finset.sum_range_succ]
    linarith

/-- Sum of the errors: `∑_{j<J} C_s (log x₁^{α^j})^{-c} ≤ C_s/(1 - α^{-c}) · (log x₁)^{-c}`. -/
theorem err_sum {α : ℝ} (hα : 1 < α) (Cs c x1 : ℝ) (hC : 0 ≤ Cs) (hc : 0 < c) (hx1 : 1 < x1)
    (J : ℕ) :
    ∑ j ∈ Finset.range J, Cs * (Real.log (x1 ^ (α ^ j))) ^ (-c) ≤
      Cs / (1 - α ^ (-c)) * (Real.log x1) ^ (-c) := by
  have hα0 : 0 < α := by linarith
  have hlx : 0 < Real.log x1 := Real.log_pos hx1
  have hr0 : 0 < α ^ (-c) := Real.rpow_pos_of_pos hα0 _
  have hr1 : α ^ (-c) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hα (by linarith)
  have hterm : ∀ j : ℕ, Cs * (Real.log (x1 ^ (α ^ j))) ^ (-c) =
      Cs * (Real.log x1) ^ (-c) * (α ^ (-c)) ^ j := by
    intro j
    rw [Real.log_rpow (by linarith), Real.mul_rpow (pow_pos hα0 j).le hlx.le, mul_comm _ ((Real.log x1) ^ (-c))]
    rw [mul_assoc]
    congr 2
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hα0.le,
      ← Real.rpow_mul hα0.le, mul_comm]
  calc _ = ∑ j ∈ Finset.range J, Cs * (Real.log x1) ^ (-c) * (α ^ (-c)) ^ j :=
        Finset.sum_congr rfl fun j _ => hterm j
    _ = Cs * (Real.log x1) ^ (-c) * ∑ j ∈ Finset.range J, (α ^ (-c)) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ Cs * (Real.log x1) ^ (-c) * (1 / (1 - α ^ (-c))) := by
        have hnn : 0 ≤ Cs * (Real.log x1) ^ (-c) := mul_nonneg hC (Real.rpow_nonneg hlx.le _)
        gcongr
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hr0.le hr1
        rw [pow_zero] at this
        rw [Finset.range_eq_Ico]
        exact this
    _ = Cs / (1 - α ^ (-c)) * (Real.log x1) ^ (-c) := by
        field_simp

open Classical in
/-- Bound the window probability for all `y > 0` ((o)(i)(ii) of the accompanying paper).
`v > 0`, `e^v ≥ X_s, N₀`. -/
theorem window_all (F : Family) {α c Cs Xs : ℝ} (hα : 1 < α) (hc : 0 < c) (hCs : 0 ≤ Cs)
    (hS : StepHyp F α c Cs Xs) {cB CB : ℝ} (hCB : 0 ≤ CB) {L₀ : ℕ}
    (hseed : ∀ L M : ℕ, L₀ ≤ L → L ≤ M →
      (((Finset.Ico (F.p ^ M) (F.p ^ (M + 1))).filter
          (fun n => ∀ k, F.p ^ L ≤ F.Ct^[k] n)).card : ℝ)
        ≤ CB * (F.p : ℝ) ^ M * ((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(cB * L)))
    {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (hL : L₀ ≤ Nat.log F.p N₀)
    (hLw : (yw F α) ^ α ≤ (F.p : ℝ) ^ Nat.log F.p N₀)
    {v : ℝ} (hv : 0 < v) (hXs : Xs ≤ Real.exp v) (hN₀v : (N₀ : ℝ) ≤ Real.exp v)
    (y : ℝ) (hy : 0 < y) :
    F.windowProb α N₀ y ≤ 6 * F.p * CB * (α * (α ^ 2 * v) / Real.log F.p + 1) ^ 2 *
      ((Nat.log F.p N₀ : ℝ) + 1) * Real.exp (-(cB * Nat.log F.p N₀)) +
      Cs / (1 - α ^ (-c)) * v ^ (-c) := by
  have hα0 : 0 < α := by linarith
  have hΛ : 0 ≤ α ^ 2 * v := by positivity
  have hbase := fun y' hy' hy'Λ => windowProb_base F hα hCB hseed hN₀ hL hLw hΛ (y := y') hy' hy'Λ
  have hr1 : α ^ (-c) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hα (by linarith)
  have hKE : 0 ≤ Cs / (1 - α ^ (-c)) * v ^ (-c) :=
    mul_nonneg (div_nonneg hCs (by linarith)) (Real.rpow_nonneg hv.le _)
  set X1 := Real.exp v with hX1def
  have hX1 : 1 < X1 := Real.one_lt_exp_iff.mpr hv
  by_cases hyv : y < X1 ^ α
  · have h1 : Real.log y ≤ α ^ 2 * v := by
      have := Real.log_lt_log hy hyv
      rw [Real.log_rpow (Real.exp_pos v), Real.log_exp] at this
      nlinarith
    linarith [hbase y hy h1]
  · push Not at hyv
    obtain ⟨J, x1, hx1lo, hx1hi, hyx⟩ := represent hα X1 y hX1 hyv
    have hx1 : 1 < x1 := lt_of_lt_of_le hX1 hx1lo
    have hstep := iter_step F hα hS N₀ hN₀ x1 hx1.le (le_trans hXs hx1lo) (le_trans hN₀v hx1lo) J
    have herr := err_sum hα Cs c x1 hCs hc hx1 J
    have hlx1 : v ≤ Real.log x1 := by
      rw [← Real.log_exp v]; exact Real.log_le_log (Real.exp_pos v) hx1lo
    have hlx1' : Real.log x1 < α * v := by
      have := Real.log_lt_log (lt_trans one_pos hx1) hx1hi
      rwa [Real.log_rpow (Real.exp_pos v), Real.log_exp] at this
    have hvpow : (Real.log x1) ^ (-c) ≤ v ^ (-c) :=
      Real.rpow_le_rpow_of_nonpos hv hlx1 (by linarith)
    have hb : F.windowProb α N₀ (x1 ^ α) ≤ 6 * F.p * CB * (α * (α ^ 2 * v) / Real.log F.p + 1) ^ 2 *
        ((Nat.log F.p N₀ : ℝ) + 1) * Real.exp (-(cB * Nat.log F.p N₀)) := by
      apply hbase (x1 ^ α) (Real.rpow_pos_of_pos (by linarith) _)
      rw [Real.log_rpow (by linarith)]
      nlinarith
    have hE : Cs / (1 - α ^ (-c)) * (Real.log x1) ^ (-c) ≤ Cs / (1 - α ^ (-c)) * v ^ (-c) :=
      mul_le_mul_of_nonneg_left hvpow (div_nonneg hCs (by linarith))
    rw [hyx]
    linarith

/-- `(L+1) e^{-c₁ L} ≤ (1 + 2/c₁) e^{c₁/2} N₀^{-c₁/(2 log p)}` (`L = ⌊log_p N₀⌋`; `rate_to_N0` of
`lean-nd`, for base `p`). -/
lemma rate_to_N0 (p : ℕ) (hp : 1 < p) (c1 : ℝ) (hc1 : 0 < c1) (N0 : ℕ) (hN0 : 1 ≤ N0) :
    ((Nat.log p N0 : ℝ) + 1) * Real.exp (-(c1 * Nat.log p N0)) ≤
      (1 + 2 / c1) * Real.exp (c1 / 2) * (N0 : ℝ) ^ (-(c1 / (2 * Real.log p))) := by
  set L := Nat.log p N0 with hLdef
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hN0pos : (0 : ℝ) < N0 := by exact_mod_cast (by omega : 0 < N0)
  have h1 : (L : ℝ) * Real.exp (-(c1 * L / 2)) ≤ 2 / c1 := by
    have := Real.add_one_le_exp (c1 * L / 2)
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
    rw [div_mul_eq_mul_div, le_div_iff₀ hc1]
    nlinarith
  have hsplit : Real.exp (-(c1 * L)) = Real.exp (-(c1 * L / 2)) * Real.exp (-(c1 * L / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have hN0lt : (N0 : ℝ) < (p : ℝ) ^ (L + 1) := by exact_mod_cast Nat.lt_pow_succ_log_self hp N0
  have hlogN0 : Real.log N0 < ((L : ℝ) + 1) * Real.log p := by
    have := Real.log_lt_log hN0pos hN0lt
    rw [Real.log_pow] at this; push_cast at this; linarith
  have h3 : Real.exp (-(c1 * L / 2)) ≤ Real.exp (c1 / 2) * (N0 : ℝ) ^ (-(c1 / (2 * Real.log p))) := by
    rw [Real.rpow_def_of_pos hN0pos, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : Real.log N0 * (c1 / (2 * Real.log p)) ≤
        ((L : ℝ) + 1) * Real.log p * (c1 / (2 * Real.log p)) :=
      mul_le_mul_of_nonneg_right hlogN0.le (by positivity)
    have e1 : ((L : ℝ) + 1) * Real.log p * (c1 / (2 * Real.log p)) = c1 * (L + 1) / 2 := by
      field_simp
    nlinarith
  have hA : 0 ≤ Real.exp (-(c1 * L / 2)) := (Real.exp_pos _).le
  calc ((L : ℝ) + 1) * Real.exp (-(c1 * L))
      = ((L : ℝ) * Real.exp (-(c1 * L / 2)) + Real.exp (-(c1 * L / 2))) *
          Real.exp (-(c1 * L / 2)) := by
        rw [hsplit]; ring
    _ ≤ (2 / c1 + 1) * Real.exp (-(c1 * L / 2)) := by
        have h2 : Real.exp (-(c1 * L / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        apply mul_le_mul_of_nonneg_right _ hA; linarith
    _ ≤ (2 / c1 + 1) * (Real.exp (c1 / 2) * (N0 : ℝ) ^ (-(c1 / (2 * Real.log p)))) := by
        gcongr
    _ = (1 + 2 / c1) * Real.exp (c1 / 2) * (N0 : ℝ) ^ (-(c1 / (2 * Real.log p))) := by ring

/-- Arithmetic 1 (the bottom-window term): with `v = e^{c_B L/4}`,
`6PC(α(α²v)/lp + 1)²(L+1)e^{-c_B L} ≤ 6PC(α³/lp + 1)²(L+1)e^{-c₁L}`. -/
lemma arith_base {α lp P CB cB c₁ L : ℝ} (hα : 0 < α) (hlp : 0 < lp) (hP : 0 ≤ P) (hCB : 0 ≤ CB)
    (hL : 0 ≤ L) (hcB : 0 < cB) (hc₁ : c₁ ≤ cB / 2) :
    6 * P * CB * (α * (α ^ 2 * Real.exp (cB * L / 4)) / lp + 1) ^ 2 * (L + 1) * Real.exp (-(cB * L))
      ≤ 6 * P * CB * (α ^ 3 / lp + 1) ^ 2 * ((L + 1) * Real.exp (-(c₁ * L))) := by
  obtain ⟨v, hv⟩ : ∃ v, v = Real.exp (cB * L / 4) := ⟨_, rfl⟩
  rw [← hv]
  have hv1 : 1 ≤ v := by rw [hv]; exact Real.one_le_exp (by positivity)
  have h1 : α * (α ^ 2 * v) / lp + 1 ≤ (α ^ 3 / lp + 1) * v := by
    have e : α * (α ^ 2 * v) / lp = α ^ 3 / lp * v := by ring
    rw [e, add_mul, one_mul]; linarith
  have h0 : 0 ≤ α * (α ^ 2 * v) / lp + 1 := by positivity
  have hsq : (α * (α ^ 2 * v) / lp + 1) ^ 2 ≤ (α ^ 3 / lp + 1) ^ 2 * v ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ h0 h1 2
  have hve : v ^ 2 * Real.exp (-(cB * L)) ≤ Real.exp (-(c₁ * L)) := by
    rw [hv, sq, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hc₁ hL
    have e : cB * L / 4 + cB * L / 4 + -(cB * L) = -(cB / 2 * L) := by ring
    rw [e]; linarith
  have hK : 0 ≤ 6 * P * CB * (L + 1) := by positivity
  have hE : 0 ≤ Real.exp (-(cB * L)) := (Real.exp_pos _).le
  have hA : 0 ≤ 6 * P * CB * (L + 1) * (α ^ 3 / lp + 1) ^ 2 := by positivity
  calc _ = 6 * P * CB * (L + 1) * ((α * (α ^ 2 * v) / lp + 1) ^ 2 * Real.exp (-(cB * L))) := by ring
    _ ≤ 6 * P * CB * (L + 1) * ((α ^ 3 / lp + 1) ^ 2 * v ^ 2 * Real.exp (-(cB * L))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hE) hK
    _ = 6 * P * CB * (L + 1) * (α ^ 3 / lp + 1) ^ 2 * (v ^ 2 * Real.exp (-(cB * L))) := by ring
    _ ≤ 6 * P * CB * (L + 1) * (α ^ 3 / lp + 1) ^ 2 * Real.exp (-(c₁ * L)) :=
        mul_le_mul_of_nonneg_left hve hA
    _ = _ := by ring

/-- Arithmetic 2 (the error term): `K_E (e^{c_B L/4})^{-c} ≤ K_E (L+1) e^{-c₁ L}` (`c₁ ≤ c_B c/4`). -/
lemma arith_err {c cB c₁ L KE : ℝ} (hKE : 0 ≤ KE) (hL : 0 ≤ L) (hc₁ : c₁ ≤ cB * c / 4) :
    KE * (Real.exp (cB * L / 4)) ^ (-c) ≤ KE * ((L + 1) * Real.exp (-(c₁ * L))) := by
  apply mul_le_mul_of_nonneg_left _ hKE
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have h1 : Real.exp (cB * L / 4 * -c) ≤ Real.exp (-(c₁ * L)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hc₁ hL
    have e : cB * L / 4 * -c = -(cB * c / 4 * L) := by ring
    rw [e]; linarith
  have h2 : Real.exp (-(c₁ * L)) ≤ (L + 1) * Real.exp (-(c₁ * L)) := by
    have := (Real.exp_pos (-(c₁ * L))).le
    nlinarith
  linarith

open Classical in
/-- The case of large `L` ((iii) of the accompanying paper). -/
theorem uniform_large (F : Family) {α c Cs Xs : ℝ} (hα : 1 < α) (hc : 0 < c) (hCs : 0 ≤ Cs)
    (hS : StepHyp F α c Cs Xs) {cB CB : ℝ} (hcB : 0 < cB) (hCB : 0 ≤ CB) {L₀ : ℕ}
    (hseed : ∀ L M : ℕ, L₀ ≤ L → L ≤ M →
      (((Finset.Ico (F.p ^ M) (F.p ^ (M + 1))).filter
          (fun n => ∀ k, F.p ^ L ≤ F.Ct^[k] n)).card : ℝ)
        ≤ CB * (F.p : ℝ) ^ M * ((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(cB * L)))
    {c₁ : ℝ} (hc₁ : 0 < c₁) (hc₁a : c₁ ≤ cB / 2) (hc₁b : c₁ ≤ cB * c / 4)
    {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (hL0 : L₀ ≤ Nat.log F.p N₀) (hL1 : (1 : ℝ) ≤ Nat.log F.p N₀)
    (hLc : 64 * Real.log F.p / cB ^ 2 ≤ Nat.log F.p N₀) (hLX : 4 * Xs / cB ≤ Nat.log F.p N₀)
    (hLyw : (yw F α) ^ α ≤ Nat.log F.p N₀) (y : ℝ) (hy : 0 < y) :
    F.windowProb α N₀ y ≤ (6 * F.p * CB * (α ^ 3 / Real.log F.p + 1) ^ 2 + Cs / (1 - α ^ (-c))) *
      ((1 + 2 / c₁) * Real.exp (c₁ / 2) * (N₀ : ℝ) ^ (-(c₁ / (2 * Real.log F.p)))) := by
  have hp1 : 1 < F.p := F.one_lt_p
  have hp2 : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hlp : 0 < Real.log F.p := Real.log_pos (by linarith)
  have hα0 : 0 < α := by linarith
  have hr1 : α ^ (-c) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hα (by linarith)
  have hKE : 0 ≤ Cs / (1 - α ^ (-c)) := div_nonneg hCs (by linarith)
  obtain ⟨L, hLdef⟩ : ∃ L, L = Nat.log F.p N₀ := ⟨_, rfl⟩
  rw [← hLdef] at hL1 hLc hLX hLyw
  have hLw : (yw F α) ^ α ≤ (F.p : ℝ) ^ L := by
    have : L < F.p ^ L := Nat.lt_pow_self hp1
    have : (L : ℝ) ≤ (F.p : ℝ) ^ L := by exact_mod_cast this.le
    linarith
  obtain ⟨v, hvdef⟩ : ∃ v, v = Real.exp (cB * L / 4) := ⟨_, rfl⟩
  have hv1 : 1 ≤ v := by rw [hvdef]; exact Real.one_le_exp (by positivity)
  have hv0 : 0 < v := by linarith
  have hXs : Xs ≤ Real.exp v := by
    have h1 : Xs ≤ cB * L / 4 := by
      rw [div_le_iff₀ hcB] at hLX; linarith
    have h2 := Real.add_one_le_exp (cB * L / 4)
    have h3 := Real.add_one_le_exp v
    rw [← hvdef] at h2
    linarith
  have hN0v : (N₀ : ℝ) ≤ Real.exp v := by
    have hN0lt : (N₀ : ℝ) < (F.p : ℝ) ^ (L + 1) := by
      rw [hLdef]; exact_mod_cast Nat.lt_pow_succ_log_self hp1 N₀
    have hq : (cB * L / 4) ^ 2 / 2 ≤ v := by
      have := Real.pow_div_factorial_le_exp (x := cB * L / 4) (by positivity) 2
      rw [hvdef]; simpa using this
    have hq2 : ((L : ℝ) + 1) * Real.log F.p ≤ (cB * L / 4) ^ 2 / 2 := by
      have h1 : 64 * Real.log F.p ≤ cB ^ 2 * L := by
        rw [div_le_iff₀ (by positivity)] at hLc; linarith
      have h2 : ((L : ℝ) + 1) * Real.log F.p ≤ 2 * L * Real.log F.p := by nlinarith
      have e : (cB * L / 4) ^ 2 / 2 = cB ^ 2 * L * L / 32 := by ring
      rw [e]; nlinarith
    have h2 : (F.p : ℝ) ^ (L + 1) = Real.exp (((L : ℝ) + 1) * Real.log F.p) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]; push_cast; ring_nf
    rw [h2] at hN0lt
    exact le_trans hN0lt.le (Real.exp_le_exp.mpr (le_trans hq2 (le_trans hq (by
      have := Real.add_one_le_exp v; linarith))))
  have hwin := window_all F hα hc hCs hS hCB hseed hN₀ hL0 (hLdef ▸ hLw) hv0 hXs hN0v y hy
  rw [← hLdef, hvdef] at hwin
  have hT1 := arith_base (P := (F.p : ℝ)) (CB := CB) (c₁ := c₁) hα0 hlp (by positivity) hCB
    (Nat.cast_nonneg L) hcB hc₁a
  have hT2 := arith_err (c := c) (KE := Cs / (1 - α ^ (-c))) hKE (Nat.cast_nonneg L) hc₁b
  have hrate := rate_to_N0 F.p hp1 c₁ hc₁ N₀ hN₀
  rw [← hLdef] at hrate
  have hsum := add_le_add hT1 hT2
  calc F.windowProb α N₀ y ≤ _ := le_trans hwin hsum
    _ = (6 * F.p * CB * (α ^ 3 / Real.log F.p + 1) ^ 2 + Cs / (1 - α ^ (-c))) *
          (((L : ℝ) + 1) * Real.exp (-(c₁ * L))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrate (by positivity)

/-- **Theorem 5.7 (i) of the paper** (under `StepHyp` and the seed theorem): there are `K, c' > 0` such that for all
`N₀ ≥ 1` and `y > 0`, `P(N₀, y) ≤ K N₀^{-c'}`. -/
theorem uniform (F : Family) {α c Cs Xs : ℝ} (hα : 1 < α) (hc : 0 < c) (hCs : 0 ≤ Cs)
    (hS : StepHyp F α c Cs Xs) :
    ∃ K c' : ℝ, 0 < K ∧ 0 < c' ∧ ∀ N₀ : ℕ, 1 ≤ N₀ → ∀ y : ℝ, 0 < y →
      F.windowProb α N₀ y ≤ K * (N₀ : ℝ) ^ (-c') := by
  classical
  obtain ⟨cB, hcB, CB, hCB, L₀, hseed⟩ := F.seed
  have hp1 : 1 < F.p := F.one_lt_p
  have hp2 : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hlp : 0 < Real.log F.p := Real.log_pos (by linarith)
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁ : ℝ, c₁ = cB * min (1 / 2) (c / 4) := ⟨_, rfl⟩
  have hm0 : 0 < min (1 / 2 : ℝ) (c / 4) := lt_min (by norm_num) (by linarith)
  have hc₁ : 0 < c₁ := by rw [hc₁def]; exact mul_pos hcB hm0
  have hc₁a : c₁ ≤ cB / 2 := by
    have := mul_le_mul_of_nonneg_left (min_le_left (1 / 2 : ℝ) (c / 4)) hcB.le
    rw [hc₁def]; linarith
  have hc₁b : c₁ ≤ cB * c / 4 := by
    have := mul_le_mul_of_nonneg_left (min_le_right (1 / 2 : ℝ) (c / 4)) hcB.le
    rw [hc₁def]; linarith
  obtain ⟨c', hc'def⟩ : ∃ c' : ℝ, c' = c₁ / (2 * Real.log F.p) := ⟨_, rfl⟩
  have hc' : 0 < c' := by rw [hc'def]; positivity
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = max L₀ (max ⌈64 * Real.log F.p / cB ^ 2⌉₊
      (max ⌈4 * Xs / cB⌉₊ ⌈(yw F α) ^ α⌉₊)) := ⟨_, rfl⟩
  obtain ⟨Kbig, hKbig⟩ : ∃ Kbig : ℝ, Kbig =
      (6 * F.p * CB * (α ^ 3 / Real.log F.p + 1) ^ 2 + Cs / (1 - α ^ (-c))) *
        ((1 + 2 / c₁) * Real.exp (c₁ / 2)) := ⟨_, rfl⟩
  refine ⟨max (max Kbig 1) (((F.p : ℝ) ^ (M + 1)) ^ c'), c',
    lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_left _ _)), hc', ?_⟩
  intro N₀ hN₀ y hy
  have hN0pos : (0 : ℝ) < N₀ := by exact_mod_cast (by omega : 0 < N₀)
  have hNpow : 0 < (N₀ : ℝ) ^ (-c') := Real.rpow_pos_of_pos hN0pos _
  by_cases hsmall : Nat.log F.p N₀ < M + 1
  · -- `N₀ < p^{M+1}`: `P ≤ 1`
    have hN0lt : (N₀ : ℝ) ≤ (F.p : ℝ) ^ (M + 1) := by
      have h1 : N₀ < F.p ^ (Nat.log F.p N₀ + 1) := Nat.lt_pow_succ_log_self hp1 N₀
      have h2 : F.p ^ (Nat.log F.p N₀ + 1) ≤ F.p ^ (M + 1) := Nat.pow_le_pow_right F.p_pos hsmall
      exact_mod_cast (le_trans h1.le h2)
    have h1 : (N₀ : ℝ) ^ c' ≤ ((F.p : ℝ) ^ (M + 1)) ^ c' := Real.rpow_le_rpow hN0pos.le hN0lt hc'.le
    have h2 : (N₀ : ℝ) ^ c' * (N₀ : ℝ) ^ (-c') = 1 := by rw [← Real.rpow_add hN0pos]; simp
    calc F.windowProb α N₀ y ≤ 1 := windowProb_le_one F α N₀ y
      _ = (N₀ : ℝ) ^ c' * (N₀ : ℝ) ^ (-c') := h2.symm
      _ ≤ ((F.p : ℝ) ^ (M + 1)) ^ c' * (N₀ : ℝ) ^ (-c') := by gcongr
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · push Not at hsmall
    have hceil : ∀ z : ℝ, ⌈z⌉₊ ≤ M → z ≤ (Nat.log F.p N₀ : ℝ) := by
      intro z hz
      have h1 : (⌈z⌉₊ : ℝ) ≤ (Nat.log F.p N₀ : ℝ) := by exact_mod_cast le_trans hz (by omega)
      linarith [Nat.le_ceil z]
    have hL0 : L₀ ≤ Nat.log F.p N₀ := by
      have : L₀ ≤ M := by rw [hMdef]; exact le_max_left _ _
      omega
    have hL1 : (1 : ℝ) ≤ Nat.log F.p N₀ := by exact_mod_cast (by omega : 1 ≤ Nat.log F.p N₀)
    have hLc := hceil (64 * Real.log F.p / cB ^ 2) (by
      rw [hMdef]; exact le_trans (le_max_left _ _) (le_max_right _ _))
    have hLX := hceil (4 * Xs / cB) (by
      rw [hMdef]; exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
    have hLyw := hceil ((yw F α) ^ α) (by
      rw [hMdef]; exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
    have h := uniform_large F hα hc hCs hS hcB hCB.le hseed hc₁ hc₁a hc₁b hN₀ hL0 hL1 hLc hLX hLyw
      y hy
    rw [← hc'def] at h
    calc F.windowProb α N₀ y ≤ _ := h
      _ = Kbig * (N₀ : ℝ) ^ (-c') := by rw [hKbig]; ring
      _ ≤ _ := by gcongr; exact le_trans (le_max_left _ _) (le_max_left _ _)

end Asm

end GGMCollatz
