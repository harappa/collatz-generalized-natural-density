import GGMCollatz.Tao.Sec7.Expect
import GGMCollatz.Tao.Syracuse.SyracRV

/-!
# Tools for the pairing argument: rearranging the two coordinates of the one-stage law (generalization of `tsum_geom_pair` of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/Reduction.lean`
(`tsum_geom_pair`, `pre_cons`, `eC_char_add`); generalized to the GGM family (p, q, r). Modified.

* `Pair.tsum_geom_pair`: rearranging the expectation over two independent `G(μ)` (`a₀, a₁`) by `b = a₀ + a₁` gives
  a `Pascal(μ)` expectation and a uniform average over `a₁ ∈ [1, b-1]` (`geomP a₀ geomP a₁ = (p-1)² p^{-b}`,
  `pascalP b = (b-1)(p-1)² p^{-b}`).
* `Pair.tsum_stepLaw`: splits the expectation under the one-stage law `G(μ) ⊗ U(1..p-1)` into an expectation over the valuation and an average over the digit.
* `Pair.tsum_step_pair`: combining the two above, the rearrangement of a pair of stages (in `fCond` form).
* `Pair.pre_cons`: peeling off the head of a forward partial sum.
-/

open scoped ENNReal

namespace GGMCollatz

namespace Pair

/-- Peeling off the head of a forward partial sum: `pre (cons a w) (m+1) = a + pre w m`. -/
theorem pre_cons {n : ℕ} (a : ℕ) (w : Fin n → ℕ) (m : ℕ) :
    pre (Fin.cons a w : Fin (n + 1) → ℕ) (m + 1) = a + pre w m := by
  rw [pre_cons_head]
  simp

/-- The real masses of `G(μ)` are summable. -/
theorem summable_geomP (p : ℕ) : Summable fun a => (geomP p a).toReal :=
  ENNReal.summable_toReal (geomP p).tsum_coe_ne_top

/-- The real masses of `Pascal(μ)`. -/
theorem pascalP_toReal {p : ℕ} (hp : 2 ≤ p) (b : ℕ) :
    (pascalP p b).toReal
      = if b < 2 then 0 else ((b - 1 : ℕ) : ℝ) * ((p : ℝ) - 1) ^ 2 * ((p : ℝ)⁻¹) ^ b := by
  rw [pascalP_apply hp]
  split_ifs
  · simp
  · rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]

set_option maxHeartbeats 1000000 in
/-- **Rearranging two `G(μ)`** (generalization of `tsum_geom_pair` of tao-collatz). -/
theorem tsum_geom_pair {p : ℕ} (hp : 2 ≤ p) (G : ℕ → ℕ → ℂ) (hG : ∀ b a, ‖G b a‖ ≤ 1) :
    ∑' a₀ : ℕ, ((geomP p a₀).toReal : ℂ)
        * ∑' a₁ : ℕ, ((geomP p a₁).toReal : ℂ) * G (a₀ + a₁) a₁
      = ∑' b : ℕ, ((pascalP p b).toReal : ℂ)
          * (((b : ℂ) - 1)⁻¹ * ∑ a ∈ Finset.Icc 1 (b - 1), G b a) := by
  have hgr0 : ∀ a, (0 : ℝ) ≤ (geomP p a).toReal := fun a => ENNReal.toReal_nonneg
  have hgrS : Summable fun a => (geomP p a).toReal := summable_geomP p
  set f₁ : ℕ × ℕ → ℂ := fun x =>
    (((geomP p x.1).toReal : ℂ) * ((geomP p x.2).toReal : ℂ)) * G (x.1 + x.2) x.2
    with hf₁
  set F : ℕ × ℕ → ℂ := fun x =>
    if x.2 ≤ x.1 then
      (((geomP p (x.1 - x.2)).toReal : ℂ) * ((geomP p x.2).toReal : ℂ)) * G x.1 x.2
    else 0 with hF
  have hprod : Summable fun x : ℕ × ℕ => (geomP p x.1).toReal * (geomP p x.2).toReal :=
    hgrS.mul_of_nonneg hgrS hgr0 hgr0
  have hf₁norm : ∀ x : ℕ × ℕ, ‖f₁ x‖ ≤ (geomP p x.1).toReal * (geomP p x.2).toReal := by
    intro x
    rw [hf₁]
    dsimp only
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (hgr0 _), abs_of_nonneg (hgr0 _)]
    calc (geomP p x.1).toReal * (geomP p x.2).toReal * ‖G (x.1 + x.2) x.2‖
        ≤ (geomP p x.1).toReal * (geomP p x.2).toReal * 1 :=
          mul_le_mul_of_nonneg_left (hG _ _) (mul_nonneg (hgr0 _) (hgr0 _))
      _ = _ := mul_one _
  have hf₁S : Summable f₁ :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun x => norm_nonneg _) hf₁norm hprod)
  have hi : Function.Injective (fun x : ℕ × ℕ => (x.1 + x.2, x.2)) := by
    intro x x' h
    rw [Prod.ext_iff] at h ⊢
    obtain ⟨h1, h2⟩ := h
    dsimp only at h1 h2
    omega
  have hcomp : ∀ x : ℕ × ℕ, F (x.1 + x.2, x.2) = f₁ x := by
    intro x
    rw [hF, hf₁]
    dsimp only
    rw [if_pos (Nat.le_add_left _ _), Nat.add_sub_cancel]
  have hsupp : ∀ y : ℕ × ℕ, y ∉ Set.range (fun x : ℕ × ℕ => (x.1 + x.2, x.2)) → F y = 0 := by
    intro y hy
    rw [hF]
    dsimp only
    rw [if_neg]
    intro hle
    exact hy ⟨(y.1 - y.2, y.2), by
      rw [Prod.ext_iff]
      exact ⟨by dsimp only; omega, rfl⟩⟩
  have hFS : Summable F := by
    rw [← Function.Injective.summable_iff hi hsupp]
    exact hf₁S.congr fun x => (hcomp x).symm
  have hf₁fib : ∀ a₀, Summable fun a₁ => f₁ (a₀, a₁) := by
    intro a₀
    have hb : Summable fun a₁ : ℕ =>
        (geomP p (a₀, a₁).1).toReal * (geomP p (a₀, a₁).2).toReal := by
      simpa using hgrS.mul_left ((geomP p a₀).toReal)
    exact Summable.of_norm (Summable.of_nonneg_of_le (fun a₁ => norm_nonneg _)
      (fun a₁ => hf₁norm (a₀, a₁)) hb)
  have hFfib : ∀ b, Summable fun a => F (b, a) := by
    intro b
    refine summable_of_ne_finset_zero (s := Finset.range (b + 1)) (fun a ha => ?_)
    rw [hF]
    dsimp only
    rw [if_neg (by simp at ha; omega)]
  have hgeom : ∀ a, (geomP p a).toReal = if a = 0 then 0 else ((p : ℝ) - 1) * ((p : ℝ)⁻¹) ^ a :=
    fun a => geomP_toReal hp a
  calc ∑' a₀ : ℕ, ((geomP p a₀).toReal : ℂ)
        * ∑' a₁ : ℕ, ((geomP p a₁).toReal : ℂ) * G (a₀ + a₁) a₁
      = ∑' a₀, ∑' a₁, f₁ (a₀, a₁) := by
        refine tsum_congr fun a₀ => ?_
        rw [← tsum_mul_left]
        exact tsum_congr fun a₁ => by rw [hf₁]; dsimp only; ring
    _ = ∑' x : ℕ × ℕ, f₁ x := (hf₁S.tsum_prod' hf₁fib).symm
    _ = ∑' x : ℕ × ℕ, F (x.1 + x.2, x.2) := (tsum_congr fun x => (hcomp x).symm)
    _ = ∑' y : ℕ × ℕ, F y := Function.Injective.tsum_eq hi (Function.support_subset_iff'.2 hsupp)
    _ = ∑' b, ∑' a, F (b, a) := hFS.tsum_prod' hFfib
    _ = ∑' b : ℕ, ((pascalP p b).toReal : ℂ)
          * (((b : ℂ) - 1)⁻¹ * ∑ a ∈ Finset.Icc 1 (b - 1), G b a) := by
        refine tsum_congr fun b => ?_
        have hfin : ∑' a, F (b, a) = ∑ a ∈ Finset.Icc 1 (b - 1), F (b, a) := by
          refine tsum_eq_sum (fun a ha => ?_)
          rw [hF]
          dsimp only
          rcases Nat.lt_or_ge b a with hab | hab
          · rw [if_neg (by omega)]
          · rw [if_pos hab]
            simp only [Finset.mem_Icc, not_and_or, not_le] at ha
            rcases ha with h1 | h2
            · have ha0 : a = 0 := by omega
              rw [ha0]
              simp [hgeom]
            · have hab' : a = b := by omega
              rw [hab', Nat.sub_self]
              simp [hgeom]
        rw [hfin]
        rcases Nat.lt_or_ge b 2 with hb | hb
        · have hIcc : Finset.Icc 1 (b - 1) = (∅ : Finset ℕ) := by
            rw [Finset.Icc_eq_empty_iff]
            omega
          rw [hIcc, Finset.sum_empty, Finset.sum_empty, pascalP_toReal hp, if_pos hb]
          norm_num
        · have hterm : ∀ a ∈ Finset.Icc 1 (b - 1),
              F (b, a) = (((((p : ℝ) - 1) ^ 2 * ((p : ℝ)⁻¹) ^ b) : ℝ) : ℂ) * G b a := by
            intro a ha
            simp only [Finset.mem_Icc] at ha
            rw [hF]
            dsimp only
            rw [if_pos (by omega), hgeom, hgeom, if_neg (by omega), if_neg (by omega)]
            push_cast
            have hpow : ((p : ℂ)⁻¹) ^ (b - a) * ((p : ℂ)⁻¹) ^ a = ((p : ℂ)⁻¹) ^ b := by
              rw [← pow_add]
              congr 1
              omega
            rw [← hpow]
            ring
          rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, pascalP_toReal hp, if_neg (by omega)]
          have hne : ((b - 1 : ℕ) : ℂ) ≠ 0 := by
            rw [Nat.cast_ne_zero]
            omega
          have hcast : ((b : ℂ) - 1) = ((b - 1 : ℕ) : ℂ) := by
            push_cast [Nat.cast_sub (by omega : 1 ≤ b)]
            ring
          rw [hcast]
          push_cast
          field_simp

/-- Real masses (in `ℂ`) of the uniform digit law: `(p-1)⁻¹` for `0 < d < p`. -/
theorem unifDigit_toRealC {p : ℕ} (hp : 2 ≤ p) (d : ℕ) :
    (((unifDigit p d).toReal : ℝ) : ℂ) = if 0 < d ∧ d < p then ((p : ℂ) - 1)⁻¹ else 0 := by
  rw [unifDigit_apply hp]
  split_ifs
  · rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  · simp

/-- **Decomposition of the one-stage expectation**: `E h(𝒢, j) = Σ_a G(a) · (p-1)⁻¹ Σ_{0<d<p} h(a, d)` (bounded `h`). -/
theorem tsum_stepLaw {p : ℕ} (hp : 2 ≤ p) (h : ℕ × ℕ → ℂ) (hh : ∀ x, ‖h x‖ ≤ 1) :
    ∑' x : ℕ × ℕ, ((stepLaw p x).toReal : ℂ) * h x
      = ∑' a : ℕ, ((geomP p a).toReal : ℂ)
          * (((p : ℂ) - 1)⁻¹ * ∑ d ∈ Finset.Ioo 0 p, h (a, d)) := by
  have hsP : Summable fun x : ℕ × ℕ => (stepLaw p x).toReal :=
    ENNReal.summable_toReal (stepLaw p).tsum_coe_ne_top
  have hnorm : ∀ x : ℕ × ℕ, ‖((stepLaw p x).toReal : ℂ) * h x‖ ≤ (stepLaw p x).toReal := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (hh x)
  have hS : Summable fun x : ℕ × ℕ => ((stepLaw p x).toReal : ℂ) * h x :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun x => norm_nonneg _) hnorm hsP)
  have hfib : ∀ a : ℕ, Summable fun d : ℕ => ((stepLaw p (a, d)).toReal : ℂ) * h (a, d) := by
    intro a
    refine summable_of_ne_finset_zero (s := Finset.Ioo 0 p) (fun d hd => ?_)
    rw [stepLaw_apply, ENNReal.toReal_mul, unifDigit_apply hp, if_neg (by simpa using hd)]
    simp
  rw [hS.tsum_prod' hfib]
  refine tsum_congr fun a => ?_
  rw [tsum_eq_sum (s := Finset.Ioo 0 p) (fun d hd => by
    rw [stepLaw_apply, ENNReal.toReal_mul, unifDigit_apply hp, if_neg (by simpa using hd)]
    simp)]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : 0 < d ∧ d < p := by simpa using hd
  rw [stepLaw_apply, ENNReal.toReal_mul]
  push_cast
  rw [unifDigit_toRealC hp, if_pos hd']
  ring

/-- **Rearranging a pair of stages**: the conditional average in `fCond` form. -/
theorem tsum_step_pair {p : ℕ} (hp : 2 ≤ p) (Φ : ℕ → ℕ → ℕ → ℕ → ℂ)
    (hΦ : ∀ b a d d', ‖Φ b a d d'‖ ≤ 1) :
    ∑' x₀ : ℕ × ℕ, ((stepLaw p x₀).toReal : ℂ)
        * ∑' x₁ : ℕ × ℕ, ((stepLaw p x₁).toReal : ℂ) * Φ (x₀.1 + x₁.1) x₁.1 x₀.2 x₁.2
      = ∑' b : ℕ, ((pascalP p b).toReal : ℂ)
          * ((((b : ℂ) - 1) * ((p : ℂ) - 1) ^ 2)⁻¹
            * ∑ a ∈ Finset.Icc 1 (b - 1), ∑ d ∈ Finset.Ioo 0 p, ∑ d' ∈ Finset.Ioo 0 p,
                Φ b a d d') := by
  have hp1 : ((p : ℂ) - 1) ≠ 0 := by
    have : ((p : ℂ) - 1) = ((p - 1 : ℕ) : ℂ) := by push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
    rw [this, Nat.cast_ne_zero]; omega
  have hcnorm : ‖((p : ℂ) - 1)⁻¹‖ * ((p - 1 : ℕ) : ℝ) = 1 := by
    have : ((p : ℂ) - 1) = ((p - 1 : ℕ) : ℂ) := by push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
    rw [this, norm_inv, Complex.norm_natCast]
    exact inv_mul_cancel₀ (by exact_mod_cast (by omega : p - 1 ≠ 0))
  -- the digit average lies in the unit disc
  have hdigit : ∀ (g : ℕ → ℂ), (∀ d, ‖g d‖ ≤ 1) →
      ‖((p : ℂ) - 1)⁻¹ * ∑ d ∈ Finset.Ioo 0 p, g d‖ ≤ 1 := by
    intro g hg
    rw [norm_mul]
    calc ‖((p : ℂ) - 1)⁻¹‖ * ‖∑ d ∈ Finset.Ioo 0 p, g d‖
        ≤ ‖((p : ℂ) - 1)⁻¹‖ * ((p - 1 : ℕ) : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          calc ‖∑ d ∈ Finset.Ioo 0 p, g d‖ ≤ ∑ d ∈ Finset.Ioo 0 p, ‖g d‖ := norm_sum_le _ _
            _ ≤ ∑ d ∈ Finset.Ioo 0 p, (1 : ℝ) := Finset.sum_le_sum fun d _ => hg d
            _ = ((p - 1 : ℕ) : ℝ) := by simp
      _ = 1 := hcnorm
  -- inner part: the sum over `x₁`
  have hinner : ∀ x₀ : ℕ × ℕ,
      ∑' x₁ : ℕ × ℕ, ((stepLaw p x₁).toReal : ℂ) * Φ (x₀.1 + x₁.1) x₁.1 x₀.2 x₁.2
        = ∑' a₁ : ℕ, ((geomP p a₁).toReal : ℂ)
            * (((p : ℂ) - 1)⁻¹ * ∑ d' ∈ Finset.Ioo 0 p, Φ (x₀.1 + a₁) a₁ x₀.2 d') :=
    fun x₀ => tsum_stepLaw hp (fun x₁ => Φ (x₀.1 + x₁.1) x₁.1 x₀.2 x₁.2) (fun x₁ => hΦ _ _ _ _)
  have hgC : ∀ a, ‖((geomP p a).toReal : ℂ)‖ = (geomP p a).toReal := fun a => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have hsumG : ∀ (g : ℕ → ℂ), (∀ a, ‖g a‖ ≤ 1) →
      Summable fun a => ((geomP p a).toReal : ℂ) * g a := by
    intro g hg
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_)
      (summable_geomP p))
    rw [norm_mul, hgC]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (hg a)
  have hinner_norm : ∀ x₀ : ℕ × ℕ,
      ‖∑' a₁ : ℕ, ((geomP p a₁).toReal : ℂ)
          * (((p : ℂ) - 1)⁻¹ * ∑ d' ∈ Finset.Ioo 0 p, Φ (x₀.1 + a₁) a₁ x₀.2 d')‖ ≤ 1 := by
    intro x₀
    rw [← hinner x₀]
    have := Sec7.cexpect_norm_le (stepLaw p) (fun x₁ => Φ (x₀.1 + x₁.1) x₁.1 x₀.2 x₁.2)
      (fun _ => hΦ _ _ _ _)
    exact this
  rw [tsum_congr fun x₀ => by rw [hinner x₀]]
  rw [tsum_stepLaw hp _ (fun x₀ => hinner_norm x₀)]
  -- swap the finite sum over the digit `d` with the sum over `a₁`, bringing it into the form `G(b, a)`
  set G : ℕ → ℕ → ℂ := fun b a =>
    (((p : ℂ) - 1)⁻¹ * ((p : ℂ) - 1)⁻¹) *
      ∑ d ∈ Finset.Ioo 0 p, ∑ d' ∈ Finset.Ioo 0 p, Φ b a d d' with hGdef
  have hGnorm : ∀ b a, ‖G b a‖ ≤ 1 := by
    intro b a
    show ‖(((p : ℂ) - 1)⁻¹ * ((p : ℂ) - 1)⁻¹) *
      ∑ d ∈ Finset.Ioo 0 p, ∑ d' ∈ Finset.Ioo 0 p, Φ b a d d'‖ ≤ 1
    rw [mul_assoc, Finset.mul_sum]
    refine hdigit _ (fun d => ?_)
    exact hdigit _ (fun d' => hΦ _ _ _ _)
  have hswap : ∀ a₀ : ℕ,
      ((p : ℂ) - 1)⁻¹ * ∑ d ∈ Finset.Ioo 0 p, ∑' a₁ : ℕ, ((geomP p a₁).toReal : ℂ)
          * (((p : ℂ) - 1)⁻¹ * ∑ d' ∈ Finset.Ioo 0 p, Φ ((a₀, d).1 + a₁) a₁ (a₀, d).2 d')
        = ∑' a₁ : ℕ, ((geomP p a₁).toReal : ℂ) * G (a₀ + a₁) a₁ := by
    intro a₀
    rw [← Summable.tsum_finsetSum (fun d _ => hsumG _ (fun a₁ => hdigit _ (fun d' => hΦ _ _ _ _))),
      ← tsum_mul_left]
    refine tsum_congr fun a₁ => ?_
    simp only [hGdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.sum_congr rfl fun d' _ => ?_
    ring
  rw [tsum_congr fun a₀ => by rw [hswap a₀]]
  rw [tsum_geom_pair hp G hGnorm]
  refine tsum_congr fun b => ?_
  congr 1
  simp only [hGdef]
  rw [← Finset.mul_sum, ← mul_assoc, mul_inv, ← inv_pow]
  ring

end Pair

end GGMCollatz
