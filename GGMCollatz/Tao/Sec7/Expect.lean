import GGMCollatz.Inter

/-!
# Lemmas on expectations (`cexpect`, `expect`) (first half of `Sec7/Reduction.lean` of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/Reduction.lean`, the parts
"lemmas on `eC`" and "computation of `cexpect`". Modified: the proofs are unchanged (they do not depend on `p`, `q`, `r`);
placed in the namespace `GGMCollatz.Sec7` to avoid name clashes.
-/

open scoped ENNReal

namespace GGMCollatz

namespace Sec7

/-! ### Lemmas on `eC` -/

/-- `‖e(t)‖ = 1`. -/
theorem eC_norm (q : ℚ) : ‖eC q‖ = 1 := by
  unfold eC
  have harg : 2 * Real.pi * Complex.I * (q : ℂ) = ((2 * Real.pi * q : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.norm_exp_ofReal_mul_I]

/-- `e(q + r) = e(q) e(r)`. -/
theorem eC_add (q r : ℚ) : eC (q + r) = eC q * eC r := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

/-- `e` equals `1` at integers. -/
theorem eC_intCast (k : ℤ) : eC (k : ℚ) = 1 := by
  unfold eC
  have : 2 * Real.pi * Complex.I * ((k : ℚ) : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

/-- `‖1 + e(-q)‖ = 2 |cos(πq)|`. -/
theorem norm_one_add_eC_neg (q : ℚ) : ‖1 + eC (-q)‖ = 2 * |Real.cos (Real.pi * q)| := by
  have hfact : (1 : ℂ) + eC (-q)
      = Complex.exp (-(Real.pi * q) * Complex.I)
        * (2 * Complex.cos (((Real.pi * (q : ℝ) : ℝ) : ℂ))) := by
    rw [Complex.cos, mul_comm (2 : ℂ)]
    rw [div_mul_cancel₀ _ (by norm_num : (2 : ℂ) ≠ 0)]
    rw [mul_add, ← Complex.exp_add, ← Complex.exp_add]
    unfold eC
    congr 1
    · rw [← Complex.exp_zero]
      congr 1
      push_cast
      ring
    · congr 1
      push_cast
      ring
  rw [hfact, norm_mul]
  have h1 : ‖Complex.exp (-(Real.pi * q) * Complex.I)‖ = 1 := by
    have harg : -(Real.pi * (q : ℂ)) * Complex.I = ((-(Real.pi * q) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  rw [h1, one_mul, ← Complex.ofReal_cos, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_mul]
  norm_num

/-! ### Computation of `cexpect` -/

open Classical in
/-- `cexpect` of a pushforward is `cexpect` of the composition (bounded observables). -/
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

/-- The norm of `cexpect` of an observable with values in the unit disc is `≤ 1`. -/
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

/-- `cexpect` pulls out constants. -/
theorem cexpect_const_mul {α : Type*} (p : PMF α) (c : ℂ) (f : α → ℂ) :
    (p.cexpect fun a => c * f a) = c * p.cexpect f := by
  show ∑' a, ((p a).toReal : ℂ) * (c * f a) = c * ∑' a, ((p a).toReal : ℂ) * f a
  rw [← tsum_mul_left]
  exact tsum_congr fun a => by ring

open Classical in
/-- `cexpect` of a `bind` is the average of the fibrewise `cexpect` (bounded observables). -/
theorem cexpect_bind {α β : Type*} (p : PMF α) (q : α → PMF β) (g : β → ℂ)
    (hg : ∀ b, ‖g b‖ ≤ 1) :
    (p.bind q).cexpect g = ∑' a, ((p a).toReal : ℂ) * (q a).cexpect g := by
  have hsumP : Summable fun a => (p a).toReal :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have hq1 : ∀ (a : α) (b : β), (q a b).toReal ≤ 1 := fun a b => by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top ((q a).coe_le_one b)
  have hw0 : ∀ (b : β) (a : α), (0 : ℝ) ≤ (p a).toReal * (q a b).toReal := fun b a =>
    mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hwle : ∀ (b : β) (a : α), (p a).toReal * (q a b).toReal ≤ (p a).toReal := fun b a =>
    (mul_le_mul_of_nonneg_left (hq1 a b) ENNReal.toReal_nonneg).trans (mul_one _).le
  have hsFib : ∀ b : β, Summable fun a => (p a).toReal * (q a b).toReal := fun b =>
    Summable.of_nonneg_of_le (hw0 b) (hwle b) hsumP
  have hreal : ∀ b, ((p.bind q) b).toReal = ∑' a, (p a).toReal * (q a b).toReal := by
    intro b
    rw [PMF.bind_apply, ENNReal.tsum_toReal_eq
      (fun a => ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b))]
    exact tsum_congr fun a => ENNReal.toReal_mul
  have hmap : ∀ b, (((p.bind q) b).toReal : ℂ)
      = ∑' a, (((p a).toReal * (q a b).toReal : ℝ) : ℂ) := by
    intro b
    rw [hreal b]
    exact (Complex.ofRealCLM.hasSum (hsFib b).hasSum).tsum_eq.symm
  have hG : Summable fun ba : β × α => (p ba.2).toReal * (q ba.2 ba.1).toReal := by
    rw [summable_prod_of_nonneg (fun ba => hw0 ba.1 ba.2)]
    exact ⟨fun b => hsFib b,
      Summable.of_nonneg_of_le (fun b => tsum_nonneg (hw0 b)) (fun b => (hreal b).ge)
        (ENNReal.summable_toReal (p.bind q).tsum_coe_ne_top)⟩
  have hF : Summable fun ba : β × α =>
      (((p ba.2).toReal * (q ba.2 ba.1).toReal : ℝ) : ℂ) * g ba.1 := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun ba => norm_nonneg _)
      (fun ba => ?_) hG)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 ba.1 ba.2)]
    calc ((p ba.2).toReal * (q ba.2 ba.1).toReal) * ‖g ba.1‖
        ≤ ((p ba.2).toReal * (q ba.2 ba.1).toReal) * 1 :=
          mul_le_mul_of_nonneg_left (hg ba.1) (hw0 ba.1 ba.2)
      _ = _ := mul_one _
  show ∑' b, (((p.bind q) b).toReal : ℂ) * g b = _
  calc ∑' b, (((p.bind q) b).toReal : ℂ) * g b
      = ∑' b, ∑' a, (((p a).toReal * (q a b).toReal : ℝ) : ℂ) * g b := by
        refine tsum_congr fun b => ?_
        rw [hmap b, tsum_mul_right]
    _ = ∑' a, ∑' b, (((p a).toReal * (q a b).toReal : ℝ) : ℂ) * g b := by
        refine (Summable.tsum_comm' hF (fun b => ?_) (fun a => ?_)).symm
        · refine Summable.of_norm (Summable.of_nonneg_of_le (fun a => norm_nonneg _)
            (fun a => ?_) hsumP)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hw0 b a)]
          calc ((p a).toReal * (q a b).toReal) * ‖g b‖
              ≤ ((p a).toReal * (q a b).toReal) * 1 :=
                mul_le_mul_of_nonneg_left (hg b) (hw0 b a)
            _ ≤ (p a).toReal := (mul_one _).le.trans (hwle b a)
        · refine Summable.of_norm (Summable.of_nonneg_of_le (fun b => norm_nonneg _)
            (fun b => ?_) ((ENNReal.summable_toReal (q a).tsum_coe_ne_top).mul_left
              ((p a).toReal)))
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hw0 b a)]
          calc ((p a).toReal * (q a b).toReal) * ‖g b‖
              ≤ ((p a).toReal * (q a b).toReal) * 1 :=
                mul_le_mul_of_nonneg_left (hg b) (hw0 b a)
            _ = (p a).toReal * (q a b).toReal := mul_one _
    _ = ∑' a, ((p a).toReal : ℂ) * (q a).cexpect g := by
        refine tsum_congr fun a => ?_
        show ∑' b, (((p a).toReal * (q a b).toReal : ℝ) : ℂ) * g b
          = ((p a).toReal : ℂ) * ∑' b, ((q a b).toReal : ℂ) * g b
        rw [← tsum_mul_left]
        exact tsum_congr fun b => by push_cast; ring

/-- Peeling off one coordinate from `cexpect` over an i.i.d. vector. -/
theorem cexpect_iid_succ {α : Type*} (p : PMF α) (m : ℕ) (h : (Fin (m + 1) → α) → ℂ)
    (hh : ∀ v, ‖h v‖ ≤ 1) :
    (p.iid (m + 1)).cexpect h
      = ∑' a, ((p a).toReal : ℂ) * (p.iid m).cexpect fun w => h (Fin.cons a w) := by
  rw [show p.iid (m + 1) = p.bind fun a => (p.iid m).map (Fin.cons a) from rfl,
    cexpect_bind _ _ _ hh]
  exact tsum_congr fun a => by rw [cexpect_map _ _ _ hh]

/-! ### Real expectations -/

/-- Real expectation pulls out constants. -/
theorem expect_const_mul {α : Type*} (p : PMF α) (c : ℝ) (f : α → ℝ) :
    (p.expect fun a => c * f a) = c * p.expect f := by
  show ∑' a, (p a).toReal * (c * f a) = c * ∑' a, (p a).toReal * f a
  rw [← tsum_mul_left]
  exact tsum_congr fun a => by ring

/-- Monotonicity of expectations of observables bounded in `[0,1]`. -/
theorem expect_mono_le {α : Type*} (p : PMF α) (f g : α → ℝ) (hf0 : ∀ a, 0 ≤ f a)
    (hfg : ∀ a, f a ≤ g a) (hg1 : ∀ a, g a ≤ 1) : p.expect f ≤ p.expect g := by
  have hsumP : Summable fun a => (p a).toReal :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have hgle : ∀ a, (p a).toReal * g a ≤ (p a).toReal := fun a =>
    (mul_le_mul_of_nonneg_left (hg1 a) ENNReal.toReal_nonneg).trans (mul_one _).le
  have hfle : ∀ a, (p a).toReal * f a ≤ (p a).toReal := fun a =>
    (mul_le_mul_of_nonneg_left ((hfg a).trans (hg1 a)) ENNReal.toReal_nonneg).trans
      (mul_one _).le
  have hsumg : Summable fun a => (p a).toReal * g a :=
    Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg ((hf0 a).trans (hfg a))) hgle hsumP
  have hsumf : Summable fun a => (p a).toReal * f a :=
    Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg (hf0 a)) hfle hsumP
  exact hsumf.tsum_le_tsum
    (fun a => mul_le_mul_of_nonneg_left (hfg a) ENNReal.toReal_nonneg) hsumg

/-- The expectation of a `[0,1]`-valued observable is `≤ 1`. -/
theorem expect_le_one {α : Type*} (p : PMF α) (f : α → ℝ) (h0 : ∀ a, 0 ≤ f a)
    (h1 : ∀ a, f a ≤ 1) : p.expect f ≤ 1 := by
  calc p.expect f ≤ p.expect fun _ => 1 :=
        expect_mono_le p f (fun _ => 1) h0 h1 (fun _ => le_refl 1)
    _ = 1 := by
        show ∑' a, (p a).toReal * 1 = 1
        simp only [mul_one]
        rw [← ENNReal.tsum_toReal_eq (fun a => p.apply_ne_top a), p.tsum_coe,
          ENNReal.toReal_one]

/-- The expectation of a nonnegative observable is nonnegative. -/
theorem expect_nonneg {α : Type*} (p : PMF α) (f : α → ℝ) (h0 : ∀ a, 0 ≤ f a) :
    0 ≤ p.expect f :=
  tsum_nonneg fun a => mul_nonneg ENNReal.toReal_nonneg (h0 a)

/-- Real expectation of a pushforward is the expectation of the composition (nonnegative observables). -/
theorem expect_map {α β : Type*} (p : PMF α) (f : α → β) (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) :
    (p.map f).expect g = p.expect fun a => g (f a) := by
  show ∑' b, ((p.map f) b).toReal * g b = ∑' a, (p a).toReal * g (f a)
  rw [← PMF.toReal_tsum_mul_ofReal _ _ hg, PMF.tsum_map_mul,
    PMF.toReal_tsum_mul_ofReal _ _ (fun a => hg _)]

end Sec7

end GGMCollatz
