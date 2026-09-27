import GGMCollatz.Inter
import GGMCollatz.Tao.Fourier.Parseval

/-!
# Bridge between the additive character `ZMod.stdAddChar` and `eC`; lemmas on complex expectations

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2: `TaoCollatz/Fourier/ZMod3.lean` (`eC`),
`TaoCollatz/Sec7/Reduction.lean` (`eC_add`, `eC_intCast`, `cexpect_map`, `cexpect_norm_le`),
`TaoCollatz/Sec6/MixingCore.lean` (`norm_stdAddChar`, `stdAddChar_eq_eC`, `eC_val_congr`,
`stdAddChar_mul_eq_eC`, `stdAddChar_pow3_descent_right`); generalized to the GGM family (p, q, r):
the modulus `3ⁿ` is replaced by a general modulus `N` (the descent lemma becomes `q^{j+P} → q^j`). `eC` is defined in `GGMCollatz/Inter.lean`.

General (family-independent) lemmas are placed in the namespace `GGMCollatz.Mix` to avoid name clashes.
-/

open scoped BigOperators

namespace GGMCollatz

namespace Mix

/-! ### Complex expectations -/

open Classical in
/-- The complex expectation under a pushforward is the complex expectation of the composition (bounded observables). -/
theorem cexpect_map {α β : Type*} (p : PMF α) (f : α → β) (g : β → ℂ)
    (hg : ∀ b, ‖g b‖ ≤ 1) :
    (p.map f).cexpect g = p.cexpect fun a => g (f a) := by
  have hsumP : Summable fun a => (p a).toReal :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have hite0 : ∀ (b : β) (a : α), (0 : ℝ) ≤ (if b = f a then (p a).toReal else 0) := by
    intro b a; split <;> simp [ENNReal.toReal_nonneg]
  have hiteP : ∀ (b : β) (a : α), (if b = f a then (p a).toReal else 0) ≤ (p a).toReal := by
    intro b a; split <;> simp [ENNReal.toReal_nonneg]
  have hsIte : ∀ b : β, Summable fun a => (if b = f a then (p a).toReal else 0 : ℝ) :=
    fun b => Summable.of_nonneg_of_le (hite0 b) (hiteP b) hsumP
  have hreal : ∀ b, ((p.map f) b).toReal
      = ∑' a, (if b = f a then (p a).toReal else 0 : ℝ) := by
    intro b
    rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
    · exact tsum_congr fun a => by rw [apply_ite ENNReal.toReal, ENNReal.toReal_zero]
    · intro a
      split
      · exact p.apply_ne_top a
      · exact ENNReal.zero_ne_top
  have hmap : ∀ b, (((p.map f) b).toReal : ℂ)
      = ∑' a, ((if b = f a then (p a).toReal else 0 : ℝ) : ℂ) := by
    intro b
    rw [hreal b]
    exact (Complex.ofRealCLM.hasSum (hsIte b).hasSum).tsum_eq.symm
  have hG : Summable fun ab : β × α => (if ab.1 = f ab.2 then (p ab.2).toReal else 0 : ℝ) := by
    rw [summable_prod_of_nonneg (fun ab => hite0 ab.1 ab.2)]
    exact ⟨fun b => hsIte b,
      Summable.of_nonneg_of_le (fun b => tsum_nonneg (hite0 b))
        (fun b => (hreal b).ge)
        (ENNReal.summable_toReal (p.map f).tsum_coe_ne_top)⟩
  have hF : Summable fun ab : β × α =>
      ((if ab.1 = f ab.2 then (p ab.2).toReal else 0 : ℝ) : ℂ) * g ab.1 := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun ab => norm_nonneg _)
      (fun ab => ?_) hG)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hite0 ab.1 ab.2)]
    calc (if ab.1 = f ab.2 then (p ab.2).toReal else 0 : ℝ) * ‖g ab.1‖
        ≤ (if ab.1 = f ab.2 then (p ab.2).toReal else 0 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (hg ab.1) (hite0 ab.1 ab.2)
      _ = _ := mul_one _
  show ∑' b, (((p.map f) b).toReal : ℂ) * g b = ∑' a, ((p a).toReal : ℂ) * g (f a)
  calc ∑' b, (((p.map f) b).toReal : ℂ) * g b
      = ∑' b, ∑' a, ((if b = f a then (p a).toReal else 0 : ℝ) : ℂ) * g b := by
        refine tsum_congr fun b => ?_
        rw [hmap b, tsum_mul_right]
    _ = ∑' a, ∑' b, ((if b = f a then (p a).toReal else 0 : ℝ) : ℂ) * g b := by
        refine (Summable.tsum_comm' hF (fun b => ?_) (fun a => ?_)).symm
        · exact (Complex.ofRealCLM.summable (hsIte b)).mul_right (g b)
        · refine summable_of_ne_finset_zero (s := {f a}) (fun b hb => ?_)
          rw [if_neg (by simpa using hb), Complex.ofReal_zero, zero_mul]
    _ = ∑' a, ((p a).toReal : ℂ) * g (f a) := by
        refine tsum_congr fun a => ?_
        rw [tsum_eq_single (f a) (fun b hb => ?_)]
        · rw [if_pos rfl]
        · rw [if_neg hb, Complex.ofReal_zero, zero_mul]

/-- The complex expectation of an observable with values in the unit disc has norm at most 1. -/
theorem cexpect_norm_le {α : Type*} (p : PMF α) (f : α → ℂ) (hf : ∀ a, ‖f a‖ ≤ 1) :
    ‖p.cexpect f‖ ≤ 1 := by
  have hsumP : Summable fun a => (p a).toReal :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have hb : ∀ a, ‖((p a).toReal : ℂ) * f a‖ ≤ (p a).toReal := fun a => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    calc (p a).toReal * ‖f a‖ ≤ (p a).toReal * 1 :=
          mul_le_mul_of_nonneg_left (hf a) ENNReal.toReal_nonneg
      _ = _ := mul_one _
  have hsn : Summable fun a => ‖((p a).toReal : ℂ) * f a‖ :=
    Summable.of_nonneg_of_le (fun a => norm_nonneg _) hb hsumP
  calc ‖p.cexpect f‖ ≤ ∑' a, ‖((p a).toReal : ℂ) * f a‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' a, (p a).toReal := hsn.tsum_le_tsum hb hsumP
    _ = 1 := by
        rw [← ENNReal.tsum_toReal_eq (fun a => p.apply_ne_top a), p.tsum_coe,
          ENNReal.toReal_one]

/-! ### Properties of `eC` -/

/-- `eC` is additive: `e(a + b) = e(a) e(b)`. -/
theorem eC_add (a b : ℚ) : eC (a + b) = eC a * eC b := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

/-- `eC` equals 1 at integers. -/
theorem eC_intCast (k : ℤ) : eC (k : ℚ) = 1 := by
  unfold eC
  have harg : 2 * Real.pi * Complex.I * ((k : ℚ) : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [harg, Complex.exp_int_mul_two_pi_mul_I]

/-! ### Bridge between `stdAddChar` and `eC` (general modulus `N`) -/

/-- The standard additive character has norm 1. -/
theorem norm_stdAddChar {N : ℕ} [NeZero N] (x : ZMod N) : ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

/-- `ZMod.stdAddChar j = eC(j.val / N)`. -/
theorem stdAddChar_eq_eC {N : ℕ} [NeZero N] (j : ZMod N) :
    ZMod.stdAddChar j = eC ((j.val : ℚ) / N) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, eC]
  push_cast
  ring_nf

/-- `eC(a/N)` depends only on `a mod N`. -/
theorem eC_val_congr {N : ℕ} [NeZero N] (a b : ℤ) (h : (a : ZMod N) = (b : ZMod N)) :
    eC ((a : ℚ) / N) = eC ((b : ℚ) / N) := by
  have hdvd : ((N : ℤ)) ∣ (a - b) := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) N).mp (by push_cast [h]; ring)
    simpa using this
  obtain ⟨k, hk⟩ := hdvd
  have hN : ((N : ℚ)) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hab : (a : ℚ) / (N : ℚ) = (b : ℚ) / (N : ℚ) + (k : ℚ) := by
    have hq : (a : ℚ) = (b : ℚ) + (N : ℚ) * k := by
      exact_mod_cast (by linarith : a = b + N * k)
    rw [hq]; field_simp
  rw [hab, eC_add, eC_intCast, mul_one]

/-- `stdAddChar(-(Y·ξ)) = eC(-(ξ.val·Y.val)/N)` (the form used in the statement of Proposition 5.1). -/
theorem stdAddChar_mul_eq_eC {N : ℕ} [NeZero N] (ξ Y : ZMod N) :
    ZMod.stdAddChar (-(Y * ξ)) = eC (-(ξ.val * Y.val : ℚ) / N) := by
  rw [stdAddChar_eq_eC,
    show ((-(Y * ξ)).val : ℚ) = (((-(Y * ξ)).val : ℤ) : ℚ) by push_cast; ring,
    show (-(ξ.val * Y.val : ℚ)) = (((-(↑ξ.val * ↑Y.val) : ℤ)) : ℚ) by push_cast; ring]
  apply eC_val_congr; push_cast [ZMod.natCast_zmod_val]; ring

/-- **Descent of the modulus**: `stdAddChar_{bN}(b·w) = stdAddChar_N(w mod N)` (`w : ZMod (N·b)`, the modulus being a multiple of `N`,
scaled by `b`). Used for `q^{j+P} = q^j · q^P` (tao-collatz's `stdAddChar_pow3_descent_right`). -/
theorem stdAddChar_mul_descent {N b : ℕ} [NeZero N] [NeZero (N * b)] (w : ZMod (N * b)) :
    ZMod.stdAddChar ((b : ZMod (N * b)) * w)
      = ZMod.stdAddChar (ZMod.castHom (Dvd.intro b rfl) (ZMod N) w) := by
  set m : ℕ := w.val with hmdef
  have hw : w = ((m : ℕ) : ZMod (N * b)) := (ZMod.natCast_zmod_val w).symm
  rw [hw]
  have hL : (b : ZMod (N * b)) * ((m : ℕ) : ZMod (N * b)) = (((b * m : ℕ)) : ZMod (N * b)) := by
    push_cast; ring
  have hR : ZMod.castHom (Dvd.intro b rfl) (ZMod N) ((m : ℕ) : ZMod (N * b))
      = ((m : ℕ) : ZMod N) := by rw [map_natCast]
  have hb : (b : ℂ) ≠ 0 := by
    have : b ≠ 0 := by
      intro h0; apply NeZero.ne (N * b); rw [h0, mul_zero]
    exact_mod_cast this
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  rw [hL, hR,
     show (((b * m : ℕ)) : ZMod (N * b)) = (((b * m : ℕ) : ℤ) : ZMod (N * b)) by push_cast; ring,
     show ((m : ℕ) : ZMod N) = (((m : ℕ) : ℤ) : ZMod N) by push_cast; ring,
     ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  field_simp

end Mix

end GGMCollatz
