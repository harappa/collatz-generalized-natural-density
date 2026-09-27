import GGMCollatz.Tao.Sec7.White
import GGMCollatz.Tao.Sec7.Expect
import GGMCollatz.Tao.Sec7.Pair

/-!
# GGM §6 Step 1: the pairing argument and cancellation at white points (counterpart of §7.1 of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/Reduction.lean`;
generalized to the GGM family (p, q, r). Modified. GGM §6 Step 1, inequality (ineq:expectationfbound).

Pairing adjacent terms of `𝒮_n = Σ_{j<n} q^j p^{-𝒢_{[1,j+1]}} r(d_j)` (`syracZ`) gives
`𝒮_n ≡ Σ_{k<n/2} q^{2k} p^{-𝒫_{[1,k+1]}} (p^{𝒢_{2k+1}} r(d_{2k}) + q r(d_{2k+1}))` (`𝒫_k = 𝒢_{2k} + 𝒢_{2k+1}`,
Pascal distributed). Conditionally on `𝒫`, the pair factors are independent, so
`|E χ(𝒮_n)| ≤ E_𝒫 ∏_k |f(q^{2k} p^{-𝒫_{[1,k+1]}}, 𝒫_k)|`.

* `chiC`: the character `χ(y) = e(-ξ y/q^n)`.
* `xArg n j l = q^{2j} p^{-l}` (in `ZMod (q^n)`).
* `fCond n ξ x b`: `f(x, b) = E[χ(x(p^{𝒢₂}𝒰₁ + q𝒰₂)) | 𝒢₁+𝒢₂ = b]`
  `= ((b-1)(p-1)²)^{-1} Σ_{a=1}^{b-1} Σ_{d,d'} χ(x(p^a r(d) + q r(d')))`.
* `cexpect_pairing`: the pairing bound (induction `cexpect_pairing_gen`; the rearrangement of two coordinates is in `Pair.lean`).
* `fCond_three_norm_le`: `|f(q^{2j}p^{-l}, 3)| ≤ 1 - (1 - |cos πθ(j,l)|)/(p-1)` (`θ` with `c = ξ r(j₀)(p-1)`).
* `fCond_three_white`, `prod_fCond_le_damping`: the decay `exp(-ε³)` at white points (`ε ≤ 1/p`) and the product bound.
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- The character `χ(y) = e(-ξ y / q^n)` (of the same form as the integrand of `prop51_statement`). -/
noncomputable def chiC (n ξ : ℕ) (y : ZMod (F.q ^ n)) : ℂ :=
  eC (-(ξ * y.val : ℚ) / (F.q : ℚ) ^ n)

/-- The argument in renewal coordinates `x_j = q^{2j} p^{-l}` (`xArg` of tao-collatz). -/
noncomputable def xArg (n j l : ℕ) : ZMod (F.q ^ n) :=
  (F.q : ZMod (F.q ^ n)) ^ (2 * j) * ((F.p : ZMod (F.q ^ n))⁻¹) ^ l

/-- **Conditional pair factor** `f(x, b)` (GGM §6 Step 1, `fCond` of tao-collatz). It is `0` for `b ≤ 1`. -/
noncomputable def fCond (n ξ : ℕ) (x : ZMod (F.q ^ n)) (b : ℕ) : ℂ :=
  (((b : ℂ) - 1) * ((F.p : ℂ) - 1) ^ 2)⁻¹ *
    ∑ a ∈ Finset.Icc 1 (b - 1), ∑ d ∈ Finset.Ioo 0 F.p, ∑ d' ∈ Finset.Ioo 0 F.p,
      F.chiC n ξ (x * ((F.p : ZMod (F.q ^ n)) ^ a * (F.r d : ZMod (F.q ^ n))
        + (F.q : ZMod (F.q ^ n)) * (F.r d' : ZMod (F.q ^ n))))

/-- `‖χ(y)‖ = 1`. -/
theorem chiC_norm (n ξ : ℕ) (y : ZMod (F.q ^ n)) : ‖F.chiC n ξ y‖ = 1 := Sec7.eC_norm _

/-- `‖f(x, b)‖ ≤ 1` (an average of unit vectors; `0` for `b ≤ 1`). -/
theorem fCond_norm_le_one (n ξ : ℕ) (x : ZMod (F.q ^ n)) (b : ℕ) :
    ‖F.fCond n ξ x b‖ ≤ 1 := by
  unfold fCond
  rcases Nat.lt_or_ge b 2 with hb | hb
  · have h0 : b - 1 = 0 := by omega
    simp [h0]
  · have hp := F.two_le_p
    set S := ∑ a ∈ Finset.Icc 1 (b - 1), ∑ d ∈ Finset.Ioo 0 F.p, ∑ d' ∈ Finset.Ioo 0 F.p,
      F.chiC n ξ (x * ((F.p : ZMod (F.q ^ n)) ^ a * (F.r d : ZMod (F.q ^ n))
        + (F.q : ZMod (F.q ^ n)) * (F.r d' : ZMod (F.q ^ n)))) with hS
    have hcard : ((b - 1 : ℕ) : ℝ) * ((F.p - 1 : ℕ) : ℝ) ^ 2
        = ‖((b : ℂ) - 1) * ((F.p : ℂ) - 1) ^ 2‖ := by
      have hb' : ((b : ℂ) - 1) = (((b - 1 : ℕ) : ℕ) : ℂ) := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ b)]; ring
      have hp' : ((F.p : ℂ) - 1) = (((F.p - 1 : ℕ) : ℕ) : ℂ) := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ F.p)]; ring
      rw [hb', hp', norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
    have hSle : ‖S‖ ≤ ((b - 1 : ℕ) : ℝ) * ((F.p - 1 : ℕ) : ℝ) ^ 2 := by
      calc ‖S‖ ≤ ∑ a ∈ Finset.Icc 1 (b - 1), ∑ d ∈ Finset.Ioo 0 F.p,
            ∑ d' ∈ Finset.Ioo 0 F.p, (1 : ℝ) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d' _ => ?_)
            exact (F.chiC_norm _ _ _).le
        _ = ((b - 1 : ℕ) : ℝ) * ((F.p - 1 : ℕ) : ℝ) ^ 2 := by
            simp only [Finset.sum_const, Nat.card_Icc, Nat.card_Ioo, nsmul_eq_mul, mul_one,
              Nat.sub_zero]
            push_cast
            ring
    have hpos : (0 : ℝ) < ((b - 1 : ℕ) : ℝ) * ((F.p - 1 : ℕ) : ℝ) ^ 2 := by
      have h1 : (0 : ℝ) < ((b - 1 : ℕ) : ℝ) := by
        have : 1 ≤ b - 1 := by omega
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
      have h2 : (0 : ℝ) < ((F.p - 1 : ℕ) : ℝ) := by
        have : 1 ≤ F.p - 1 := by omega
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
      positivity
    rw [norm_mul, norm_inv, ← hcard]
    calc (((b - 1 : ℕ) : ℝ) * ((F.p - 1 : ℕ) : ℝ) ^ 2)⁻¹ * ‖S‖
        ≤ (((b - 1 : ℕ) : ℝ) * ((F.p - 1 : ℕ) : ℝ) ^ 2)⁻¹
            * (((b - 1 : ℕ) : ℝ) * ((F.p - 1 : ℕ) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hSle (inv_nonneg.mpr hpos.le)
      _ = 1 := inv_mul_cancel₀ hpos.ne'


/-! ### Properties of the character `χ` -/

/-- Additivity of `χ` (the `q^n` version of `eC_char_add` of tao-collatz). -/
theorem chiC_add (n ξ : ℕ) (y z : ZMod (F.q ^ n)) :
    F.chiC n ξ (y + z) = F.chiC n ξ y * F.chiC n ξ z := by
  have := F.neZero_q_pow n
  unfold chiC
  set t : ℕ := (y.val + z.val) / F.q ^ n with ht
  have hval : y.val + z.val = F.q ^ n * t + (y + z).val := by
    rw [ZMod.val_add, ht]
    exact (Nat.div_add_mod _ _).symm
  have hq : ((y.val : ℚ)) + ((z.val : ℚ)) = (F.q : ℚ) ^ n * (t : ℚ) + (((y + z).val : ℕ) : ℚ) := by
    exact_mod_cast hval
  have h3 : (F.q : ℚ) ^ n ≠ 0 := by
    have := F.q_pos
    positivity
  have hv : (((y + z).val : ℕ) : ℚ) = (y.val : ℚ) + (z.val : ℚ) - (F.q : ℚ) ^ n * (t : ℚ) := by
    linarith
  have hnat : eC (((ξ * t : ℕ) : ℚ)) = 1 := by
    have := Sec7.eC_intCast ((ξ * t : ℕ) : ℤ)
    simpa using this
  have hsplit : -((ξ : ℚ) * (((y + z).val : ℕ) : ℚ)) / (F.q : ℚ) ^ n
      = (-((ξ : ℚ) * ((y.val : ℕ) : ℚ)) / (F.q : ℚ) ^ n
          + -((ξ : ℚ) * ((z.val : ℕ) : ℚ)) / (F.q : ℚ) ^ n)
        + ((ξ * t : ℕ) : ℚ) := by
    rw [hv]
    field_simp
    push_cast
    ring
  rw [hsplit, Sec7.eC_add, Sec7.eC_add, hnat, mul_one]

/-- If `ξ y = W` (in `ZMod (q^n)`) then `χ(y) = e(-W/q^n)`. -/
theorem chiC_eq_of_mul (n ξ : ℕ) (y W : ZMod (F.q ^ n))
    (h : (ξ : ZMod (F.q ^ n)) * y = W) :
    F.chiC n ξ y = eC (-((W.val : ℕ) : ℚ) / (F.q : ℚ) ^ n) := by
  have := F.neZero_q_pow n
  unfold chiC
  have hdvd : ((F.q : ℤ) ^ n) ∣ ((ξ : ℤ) * (y.val : ℤ) - (W.val : ℤ)) := by
    have hz : (((ξ : ℤ) * (y.val : ℤ) - (W.val : ℤ) : ℤ) : ZMod (F.q ^ n)) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, h, sub_self]
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (F.q ^ n)).mp hz
    exact_mod_cast hd
  obtain ⟨t, ht⟩ := hdvd
  have h3 : (F.q : ℚ) ^ n ≠ 0 := by
    have := F.q_pos
    positivity
  have hsplit : -((ξ : ℚ) * ((y.val : ℕ) : ℚ)) / (F.q : ℚ) ^ n
      = -((W.val : ℕ) : ℚ) / (F.q : ℚ) ^ n + ((-t : ℤ) : ℚ) := by
    have hval : ((ξ : ℚ) * ((y.val : ℕ) : ℚ)) = ((W.val : ℕ) : ℚ) + (F.q : ℚ) ^ n * (t : ℚ) := by
      have h2 : ((ξ : ℤ) * (y.val : ℤ)) = (W.val : ℤ) + (F.q : ℤ) ^ n * t := by linarith [ht]
      exact_mod_cast h2
    rw [hval]
    field_simp
    push_cast
    ring
  rw [hsplit, Sec7.eC_add, Sec7.eC_intCast, mul_one]

/-- At phase points `χ` is `e(-θ)`: if `ξ y = W(j,l)` then `χ(y) = e(-θ(j,l))`. -/
theorem chiC_eq_theta (n ξ : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) (y : ZMod (F.q ^ n))
    (h : (ξ : ZMod (F.q ^ n)) * y = F.phasePt n c j l) :
    F.chiC n ξ y = eC (-(F.θq n c j l)) := by
  rw [F.chiC_eq_of_mul n ξ y _ h]
  have hround : -((((F.phasePt n c j l).val : ℕ)) : ℚ) / (F.q : ℚ) ^ n
      = -(F.θq n c j l)
        + ((-(round ((((F.phasePt n c j l).val : ℕ) : ℚ) / (F.q : ℚ) ^ n)) : ℤ) : ℚ) := by
    unfold θq sfrac
    push_cast
    ring
  rw [hround, Sec7.eC_add, Sec7.eC_intCast, mul_one]

/-- Powers of the unit `p`: `up^{1-l} = p · (p⁻¹)^l` (in `ZMod (q^n)`). -/
theorem up_zpow_one_sub (n l : ℕ) :
    (((F.up n) ^ ((1 : ℤ) - (l : ℤ)) : (ZMod (F.q ^ n))ˣ) : ZMod (F.q ^ n))
      = (F.p : ZMod (F.q ^ n)) * ((F.p : ZMod (F.q ^ n))⁻¹) ^ l := by
  have hinv : (F.p : ZMod (F.q ^ n))⁻¹ = (((F.up n)⁻¹ : (ZMod (F.q ^ n))ˣ) : ZMod (F.q ^ n)) := by
    rw [← F.up_val n, ZMod.inv_coe_unit]
  rw [hinv, ← Units.val_pow_eq_pow_val, inv_pow, sub_eq_add_neg, zpow_add (F.up n),
    zpow_one, zpow_neg, zpow_natCast, Units.val_mul, F.up_val]

/-- `ξ · (x_j · p(p-1) r(d)) = W(j,l)` (the phase point with `c = ξ r(d)(p-1)`). -/
theorem xi_mul_xArg_phase (n ξ j l d : ℕ) :
    (ξ : ZMod (F.q ^ n)) * (F.xArg n j l * ((F.p : ZMod (F.q ^ n)) * ((F.p : ZMod (F.q ^ n)) - 1)
        * (F.r d : ZMod (F.q ^ n))))
      = F.phasePt n ((ξ : ℤ) * F.r d * ((F.p : ℤ) - 1)) j (l : ℤ) := by
  unfold phasePt xArg
  rw [F.up_zpow_one_sub n l]
  push_cast
  ring


/-- Identity peeling off two coordinates: `x_{k,L} · offset(cons x₀ (cons x₁ w))
= x_{k, L+a₀+a₁} (p^{a₁} r(d₀) + q r(d₁)) + x_{k+1, L+a₀+a₁} · offset(w)`. -/
theorem xArg_offset_peel2 (n k L : ℕ) {m : ℕ} (x₀ x₁ : ℕ × ℕ) (w : Fin m → ℕ × ℕ) :
    F.xArg n k L * F.offsetIn (F.q ^ n)
        (Fin.cons x₀ (Fin.cons x₁ w : Fin (m + 1) → ℕ × ℕ) : Fin (m + 2) → ℕ × ℕ)
      = F.xArg n k (L + (x₀.1 + x₁.1))
          * ((F.p : ZMod (F.q ^ n)) ^ x₁.1 * (F.r x₀.2 : ZMod (F.q ^ n))
            + (F.q : ZMod (F.q ^ n)) * (F.r x₁.2 : ZMod (F.q ^ n)))
        + F.xArg n (k + 1) (L + (x₀.1 + x₁.1)) * F.offsetIn (F.q ^ n) w := by
  rw [F.offsetIn_peel (F.q ^ n) (Fin.cons x₀ (Fin.cons x₁ w : Fin (m + 1) → ℕ × ℕ))]
  simp only [Fin.cons_zero, Fin.tail_cons]
  rw [F.offsetIn_peel (F.q ^ n) (Fin.cons x₁ w)]
  simp only [Fin.cons_zero, Fin.tail_cons]
  have hPI : (F.p : ZMod (F.q ^ n)) ^ x₁.1 * ((F.p : ZMod (F.q ^ n))⁻¹) ^ x₁.1 = 1 := by
    rw [← mul_pow, F.p_mul_inv_zmod, one_pow]
  unfold xArg
  linear_combination (-((F.q : ZMod (F.q ^ n)) ^ (2 * k)
    * ((F.p : ZMod (F.q ^ n))⁻¹) ^ (L + x₀.1) * (F.r x₀.2 : ZMod (F.q ^ n)))) * hPI

open Classical in
/-- **Generalized pairing bound** (`cexpect_pairing_gen` of tao-collatz): from a pair-index shift `k` and a forward sum `L`
(multiplier `x_{k,L} = q^{2k} p^{-L}`), the expectation of the character over the remaining `m` stages is
bounded by the `Pascal(μ)` expectation over `⌊m/2⌋` pairs of `∏ ‖fCond‖`. -/
theorem cexpect_pairing_gen (n ξ : ℕ) :
    ∀ m k L : ℕ,
      ‖(PMF.iid (stepLaw F.p) m).cexpect fun v =>
          F.chiC n ξ (F.xArg n k L * F.offsetIn (F.q ^ n) v)‖
        ≤ (PMF.iid (pascalP F.p) (m / 2)).expect fun b =>
            ∏ j : Fin (m / 2),
              ‖F.fCond n ξ (F.xArg n (k + (j : ℕ)) (L + pre b ((j : ℕ) + 1))) (b j)‖ := by
  have hp := F.two_le_p
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro k L
    rcases Nat.lt_or_ge m 2 with hm | hm
    · have hdiv : m / 2 = 0 := by omega
      refine le_trans (Sec7.cexpect_norm_le _ _ (fun a => (F.chiC_norm _ _ _).le)) (le_of_eq ?_)
      rw [hdiv, PMF.expect_iid_zero]
      exact (Finset.prod_of_isEmpty _).symm
    · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
      rw [show (m + 2) / 2 = m / 2 + 1 from Nat.add_div_right m (by norm_num)]
      set T : ℕ → ℂ := fun b => (PMF.iid (stepLaw F.p) m).cexpect fun w =>
        F.chiC n ξ (F.xArg n (k + 1) (L + b) * F.offsetIn (F.q ^ n) w) with hT
      have hTle : ∀ b, ‖T b‖ ≤ 1 := fun b =>
        Sec7.cexpect_norm_le _ _ (fun w => (F.chiC_norm _ _ _).le)
      set H : ℕ → ℕ → ℕ → ℕ → ℂ := fun b a d d' =>
        F.chiC n ξ (F.xArg n k (L + b) * ((F.p : ZMod (F.q ^ n)) ^ a * (F.r d : ZMod (F.q ^ n))
          + (F.q : ZMod (F.q ^ n)) * (F.r d' : ZMod (F.q ^ n)))) with hH
      have hHT : ∀ b a d d', ‖H b a d d' * T b‖ ≤ 1 := by
        intro b a d d'
        rw [norm_mul, hH]
        calc ‖F.chiC n ξ _‖ * ‖T b‖ ≤ 1 * 1 :=
              mul_le_mul (F.chiC_norm _ _ _).le (hTle b) (norm_nonneg _) zero_le_one
          _ = 1 := mul_one 1
      have hpeel : ((PMF.iid (stepLaw F.p) (m + 2)).cexpect fun v =>
            F.chiC n ξ (F.xArg n k L * F.offsetIn (F.q ^ n) v))
          = ∑' b : ℕ, ((pascalP F.p b).toReal : ℂ)
              * ((((b : ℂ) - 1) * ((F.p : ℂ) - 1) ^ 2)⁻¹
                * ∑ a ∈ Finset.Icc 1 (b - 1), ∑ d ∈ Finset.Ioo 0 F.p, ∑ d' ∈ Finset.Ioo 0 F.p,
                    H b a d d' * T b) := by
        rw [Sec7.cexpect_iid_succ _ _ _ (fun v => (F.chiC_norm _ _ _).le)]
        have hinner : ∀ x₀ : ℕ × ℕ, ((PMF.iid (stepLaw F.p) (m + 1)).cexpect fun w =>
            F.chiC n ξ (F.xArg n k L * F.offsetIn (F.q ^ n)
              (Fin.cons x₀ w : Fin (m + 2) → ℕ × ℕ)))
            = ∑' x₁ : ℕ × ℕ, ((stepLaw F.p x₁).toReal : ℂ)
                * (H (x₀.1 + x₁.1) x₁.1 x₀.2 x₁.2 * T (x₀.1 + x₁.1)) := by
          intro x₀
          rw [Sec7.cexpect_iid_succ _ _ _ (fun v => (F.chiC_norm _ _ _).le)]
          refine tsum_congr fun x₁ => ?_
          congr 1
          calc ((PMF.iid (stepLaw F.p) m).cexpect fun w =>
                F.chiC n ξ (F.xArg n k L * F.offsetIn (F.q ^ n)
                  (Fin.cons x₀ (Fin.cons x₁ w : Fin (m + 1) → ℕ × ℕ) : Fin (m + 2) → ℕ × ℕ)))
              = (PMF.iid (stepLaw F.p) m).cexpect fun w => H (x₀.1 + x₁.1) x₁.1 x₀.2 x₁.2
                  * F.chiC n ξ (F.xArg n (k + 1) (L + (x₀.1 + x₁.1))
                    * F.offsetIn (F.q ^ n) w) := by
                congr 1
                funext w
                rw [F.xArg_offset_peel2 n k L x₀ x₁ w, F.chiC_add]
            _ = H (x₀.1 + x₁.1) x₁.1 x₀.2 x₁.2 * T (x₀.1 + x₁.1) := by
                rw [Sec7.cexpect_const_mul, hT]
        rw [tsum_congr fun x₀ => by rw [hinner x₀]]
        exact Pair.tsum_step_pair hp (fun b a d d' => H b a d d' * T b) hHT
      rw [hpeel]
      have hsum_fCond : ∀ b : ℕ,
          (((b : ℂ) - 1) * ((F.p : ℂ) - 1) ^ 2)⁻¹
              * ∑ a ∈ Finset.Icc 1 (b - 1), ∑ d ∈ Finset.Ioo 0 F.p, ∑ d' ∈ Finset.Ioo 0 F.p,
                  H b a d d' * T b
            = F.fCond n ξ (F.xArg n k (L + b)) b * T b := by
        intro b
        simp only [← Finset.sum_mul]
        rw [fCond, hH]
        ring
      have hIH : ∀ b, ‖T b‖ ≤ (PMF.iid (pascalP F.p) (m / 2)).expect fun c =>
          ∏ j : Fin (m / 2),
            ‖F.fCond n ξ (F.xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
              (c j)‖ :=
        fun b => IH m (by omega) (k + 1) (L + b)
      have hE0 : ∀ b, (0:ℝ) ≤ (PMF.iid (pascalP F.p) (m / 2)).expect fun c =>
          ∏ j : Fin (m / 2),
            ‖F.fCond n ξ (F.xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
              (c j)‖ :=
        fun b => Sec7.expect_nonneg _ _ fun c => Finset.prod_nonneg fun j _ => norm_nonneg _
      have hE1 : ∀ b, ((PMF.iid (pascalP F.p) (m / 2)).expect fun c =>
          ∏ j : Fin (m / 2),
            ‖F.fCond n ξ (F.xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
              (c j)‖) ≤ 1 :=
        fun b => Sec7.expect_le_one _ _
          (fun c => Finset.prod_nonneg fun j _ => norm_nonneg _)
          (fun c => Finset.prod_le_one (fun j _ => norm_nonneg _)
            (fun j _ => F.fCond_norm_le_one _ _ _ _))
      have hΦnorm : ∀ b : ℕ, ‖((pascalP F.p b).toReal : ℂ)
            * ((((b : ℂ) - 1) * ((F.p : ℂ) - 1) ^ 2)⁻¹
              * ∑ a ∈ Finset.Icc 1 (b - 1), ∑ d ∈ Finset.Ioo 0 F.p, ∑ d' ∈ Finset.Ioo 0 F.p,
                  H b a d d' * T b)‖
          = (pascalP F.p b).toReal * (‖F.fCond n ξ (F.xArg n k (L + b)) b‖ * ‖T b‖) := by
        intro b
        rw [hsum_fCond b, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ENNReal.toReal_nonneg]
      have hmass : Summable fun b => (pascalP F.p b).toReal :=
        ENNReal.summable_toReal (pascalP F.p).tsum_coe_ne_top
      have hΦbound : ∀ b : ℕ,
          (pascalP F.p b).toReal * (‖F.fCond n ξ (F.xArg n k (L + b)) b‖ * ‖T b‖)
            ≤ (pascalP F.p b).toReal := fun b => by
        calc (pascalP F.p b).toReal * (‖F.fCond n ξ (F.xArg n k (L + b)) b‖ * ‖T b‖)
            ≤ (pascalP F.p b).toReal * (1 * 1) := by
              refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
              exact mul_le_mul (F.fCond_norm_le_one _ _ _ _) (hTle b) (norm_nonneg _)
                zero_le_one
          _ = (pascalP F.p b).toReal := by ring
      have hΦS : Summable fun b : ℕ => ‖((pascalP F.p b).toReal : ℂ)
          * ((((b : ℂ) - 1) * ((F.p : ℂ) - 1) ^ 2)⁻¹
            * ∑ a ∈ Finset.Icc 1 (b - 1), ∑ d ∈ Finset.Ioo 0 F.p, ∑ d' ∈ Finset.Ioo 0 F.p,
                H b a d d' * T b)‖ :=
        Summable.of_nonneg_of_le (fun b => norm_nonneg _)
          (fun b => (hΦnorm b).le.trans (hΦbound b)) hmass
      have hRHSb : ∀ b : ℕ, (0:ℝ) ≤ (pascalP F.p b).toReal
          * (‖F.fCond n ξ (F.xArg n k (L + b)) b‖
            * (PMF.iid (pascalP F.p) (m / 2)).expect fun c =>
              ∏ j : Fin (m / 2),
                ‖F.fCond n ξ (F.xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
                  (c j)‖) :=
        fun b => mul_nonneg ENNReal.toReal_nonneg
          (mul_nonneg (norm_nonneg _) (hE0 b))
      have hRHSS : Summable fun b : ℕ => (pascalP F.p b).toReal
          * (‖F.fCond n ξ (F.xArg n k (L + b)) b‖
            * (PMF.iid (pascalP F.p) (m / 2)).expect fun c =>
              ∏ j : Fin (m / 2),
                ‖F.fCond n ξ (F.xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
                  (c j)‖) := by
        refine Summable.of_nonneg_of_le hRHSb (fun b => ?_) hmass
        calc (pascalP F.p b).toReal * (‖F.fCond n ξ (F.xArg n k (L + b)) b‖ * _)
            ≤ (pascalP F.p b).toReal * (1 * 1) := by
              refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
              exact mul_le_mul (F.fCond_norm_le_one _ _ _ _) (hE1 b) (hE0 b) zero_le_one
          _ = (pascalP F.p b).toReal := by ring
      have hprodcons : ∀ (b : ℕ) (c : Fin (m / 2) → ℕ),
          (∏ j : Fin (m / 2 + 1),
            ‖F.fCond n ξ (F.xArg n (k + (j : ℕ))
                (L + pre (Fin.cons b c : Fin (m / 2 + 1) → ℕ) ((j : ℕ) + 1)))
              ((Fin.cons b c : Fin (m / 2 + 1) → ℕ) j)‖)
            = ‖F.fCond n ξ (F.xArg n k (L + b)) b‖
              * ∏ j : Fin (m / 2),
                ‖F.fCond n ξ (F.xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
                  (c j)‖ := by
        intro b c
        rw [Fin.prod_univ_succ]
        simp only [Fin.val_zero, Fin.cons_zero, Fin.val_succ, Fin.cons_succ, Pair.pre_cons,
          pre_zero, add_zero]
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [show k + ((j : ℕ) + 1) = (k + 1) + (j : ℕ) from by ring,
          show L + (b + pre c ((j : ℕ) + 1)) = (L + b) + pre c ((j : ℕ) + 1) from by ring]
      have htarget : ((PMF.iid (pascalP F.p) (m / 2 + 1)).expect fun b =>
            ∏ j : Fin (m / 2 + 1),
              ‖F.fCond n ξ (F.xArg n (k + (j : ℕ)) (L + pre b ((j : ℕ) + 1))) (b j)‖)
          = ∑' b : ℕ, (pascalP F.p b).toReal
              * (‖F.fCond n ξ (F.xArg n k (L + b)) b‖
                * (PMF.iid (pascalP F.p) (m / 2)).expect fun c =>
                  ∏ j : Fin (m / 2),
                    ‖F.fCond n ξ (F.xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
                      (c j)‖) := by
        rw [PMF.expect_iid_succ _ _ _
          (fun v => Finset.prod_nonneg fun j _ => norm_nonneg _)
          (fun v => Finset.prod_le_one (fun j _ => norm_nonneg _)
            (fun j _ => F.fCond_norm_le_one _ _ _ _))]
        refine tsum_congr fun b => ?_
        congr 1
        rw [show (fun c : Fin (m / 2) → ℕ =>
            ∏ j : Fin (m / 2 + 1),
              ‖F.fCond n ξ (F.xArg n (k + (j : ℕ))
                  (L + pre (Fin.cons b c : Fin (m / 2 + 1) → ℕ) ((j : ℕ) + 1)))
                ((Fin.cons b c : Fin (m / 2 + 1) → ℕ) j)‖)
          = fun c : Fin (m / 2) → ℕ => ‖F.fCond n ξ (F.xArg n k (L + b)) b‖
              * ∏ j : Fin (m / 2),
                ‖F.fCond n ξ (F.xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
                  (c j)‖ from funext fun c => hprodcons b c, Sec7.expect_const_mul]
      calc ‖∑' b : ℕ, ((pascalP F.p b).toReal : ℂ)
            * ((((b : ℂ) - 1) * ((F.p : ℂ) - 1) ^ 2)⁻¹
              * ∑ a ∈ Finset.Icc 1 (b - 1), ∑ d ∈ Finset.Ioo 0 F.p, ∑ d' ∈ Finset.Ioo 0 F.p,
                  H b a d d' * T b)‖
          ≤ ∑' b : ℕ, ‖((pascalP F.p b).toReal : ℂ)
              * ((((b : ℂ) - 1) * ((F.p : ℂ) - 1) ^ 2)⁻¹
                * ∑ a ∈ Finset.Icc 1 (b - 1), ∑ d ∈ Finset.Ioo 0 F.p, ∑ d' ∈ Finset.Ioo 0 F.p,
                    H b a d d' * T b)‖ :=
            norm_tsum_le_tsum_norm hΦS
        _ ≤ ∑' b : ℕ, (pascalP F.p b).toReal
              * (‖F.fCond n ξ (F.xArg n k (L + b)) b‖
                * (PMF.iid (pascalP F.p) (m / 2)).expect fun c =>
                  ∏ j : Fin (m / 2),
                    ‖F.fCond n ξ (F.xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
                      (c j)‖) := by
            refine hΦS.tsum_le_tsum (fun b => ?_) hRHSS
            rw [hΦnorm b]
            refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
            exact mul_le_mul_of_nonneg_left (hIH b) (norm_nonneg _)
        _ = _ := htarget.symm

open Classical in
/-- **Pairing bound** (GGM (ineq:expectationfbound), `cexpect_pairing` of tao-collatz):
`‖E χ(𝒮_n)‖ ≤ E_{𝒫 ~ Pascal(μ)^{⌊n/2⌋}} ∏_k ‖f(q^{2k} p^{-𝒫_{[1,k+1]}}, 𝒫_k)‖`. -/
theorem cexpect_pairing (n ξ : ℕ) :
    ‖(F.syracZ n).cexpect (F.chiC n ξ)‖
      ≤ (PMF.iid (pascalP F.p) (n / 2)).expect fun b =>
          ∏ j : Fin (n / 2), ‖F.fCond n ξ (F.xArg n (j : ℕ) (pre b ((j : ℕ) + 1))) (b j)‖ := by
  have h := F.cexpect_pairing_gen n ξ n 0 0
  have hx : F.xArg n 0 0 = 1 := by
    unfold xArg
    simp
  simp only [hx, one_mul, zero_add] at h
  rw [syracZ, Sec7.cexpect_map _ _ _ (fun y => (F.chiC_norm _ _ _).le)]
  exact h

/-- **The factor at `b = 3`** (GGM §6 Step 1, `fCond_three_norm` of tao-collatz):
`‖f(q^{2j}p^{-l}, 3)‖ ≤ 1 - (1 - |cos πθ(j,l)|)/(p-1)`, where `θ` is the phase with `c = ξ r(j₀)(p-1)`. -/
theorem fCond_three_norm_le (n ξ j l : ℕ) :
    ‖F.fCond n ξ (F.xArg n j l) 3‖
      ≤ 1 - (1 - |F.cosπθ n (F.phaseC ξ) j (l : ℤ)|) / ((F.p : ℝ) - 1) := by
  have hp := F.two_le_p
  have hpR : (2 : ℝ) ≤ F.p := by exact_mod_cast hp
  have hp1 : (0 : ℝ) < (F.p : ℝ) - 1 := by linarith
  set x := F.xArg n j l with hx
  set P : ZMod (F.q ^ n) := (F.p : ZMod (F.q ^ n)) with hP
  set Q : ZMod (F.q ^ n) := (F.q : ZMod (F.q ^ n)) with hQ
  -- `a ∈ {1, 2}`, `χ(x(p² r + q r')) = χ(x(p r + q r')) χ(x p(p-1) r)`
  set B : ℕ → ZMod (F.q ^ n) := fun d => x * (P * (P - 1) * (F.r d : ZMod (F.q ^ n))) with hB
  set A : ℕ → ℕ → ZMod (F.q ^ n) := fun d d' =>
    x * (P ^ 1 * (F.r d : ZMod (F.q ^ n)) + Q * (F.r d' : ZMod (F.q ^ n))) with hA
  have hIcc : Finset.Icc 1 (3 - 1) = ({1, 2} : Finset ℕ) := by decide
  have hsum : ∑ a ∈ Finset.Icc 1 (3 - 1), ∑ d ∈ Finset.Ioo 0 F.p, ∑ d' ∈ Finset.Ioo 0 F.p,
        F.chiC n ξ (x * (P ^ a * (F.r d : ZMod (F.q ^ n)) + Q * (F.r d' : ZMod (F.q ^ n))))
      = ∑ d ∈ Finset.Ioo 0 F.p, ((1 + F.chiC n ξ (B d))
          * ∑ d' ∈ Finset.Ioo 0 F.p, F.chiC n ξ (A d d')) := by
    rw [hIcc, Finset.sum_pair (by norm_num), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d' _ => ?_
    have h2 : x * (P ^ 2 * (F.r d : ZMod (F.q ^ n)) + Q * (F.r d' : ZMod (F.q ^ n)))
        = A d d' + B d := by
      simp only [hA, hB]
      ring
    rw [h2, F.chiC_add]
    simp only [hA]
    ring
  -- bound for each term
  have hnormA : ∀ d, ‖∑ d' ∈ Finset.Ioo 0 F.p, F.chiC n ξ (A d d')‖ ≤ (F.p : ℝ) - 1 := by
    intro d
    calc ‖∑ d' ∈ Finset.Ioo 0 F.p, F.chiC n ξ (A d d')‖
        ≤ ∑ d' ∈ Finset.Ioo 0 F.p, ‖F.chiC n ξ (A d d')‖ := norm_sum_le _ _
      _ = ∑ d' ∈ Finset.Ioo 0 F.p, (1 : ℝ) :=
          Finset.sum_congr rfl fun d' _ => F.chiC_norm _ _ _
      _ = (F.p : ℝ) - 1 := by
          simp only [Finset.sum_const, Nat.card_Ioo, Nat.sub_zero, nsmul_eq_mul, mul_one]
          push_cast [Nat.cast_sub (by omega : 1 ≤ F.p)]
          ring
  have hnormB : ∀ d, ‖1 + F.chiC n ξ (B d)‖ ≤ 2 := by
    intro d
    calc ‖1 + F.chiC n ξ (B d)‖ ≤ ‖(1 : ℂ)‖ + ‖F.chiC n ξ (B d)‖ := norm_add_le _ _
      _ = 2 := by rw [norm_one, F.chiC_norm]; norm_num
  -- the value at the good digit `j₀`
  set j₀ := F.goodDigit ξ with hj₀
  have hj₀mem : j₀ ∈ Finset.Ioo 0 F.p := by
    have := F.goodDigit_pos_lt ξ
    simpa [hj₀] using this
  have hθ : ‖1 + F.chiC n ξ (B j₀)‖ = 2 * |F.cosπθ n (F.phaseC ξ) j (l : ℤ)| := by
    have hW := F.xi_mul_xArg_phase n ξ j l j₀
    have hc : (ξ : ℤ) * F.r j₀ * ((F.p : ℤ) - 1) = F.phaseC ξ := by
      unfold phaseC
      rfl
    rw [hc] at hW
    rw [F.chiC_eq_theta n ξ (F.phaseC ξ) j (l : ℤ) (B j₀) hW, Sec7.norm_one_add_eC_neg]
    rfl
  -- bound for the sum
  have hsumB : ∑ d ∈ Finset.Ioo 0 F.p, ‖1 + F.chiC n ξ (B d)‖
      ≤ 2 * |F.cosπθ n (F.phaseC ξ) j (l : ℤ)| + 2 * ((F.p : ℝ) - 2) := by
    rw [← Finset.add_sum_erase _ _ hj₀mem, hθ]
    have hcard : ((Finset.Ioo 0 F.p).erase j₀).card = F.p - 2 := by
      rw [Finset.card_erase_of_mem hj₀mem, Nat.card_Ioo]
      omega
    have : ∑ d ∈ (Finset.Ioo 0 F.p).erase j₀, ‖1 + F.chiC n ξ (B d)‖
        ≤ 2 * ((F.p : ℝ) - 2) := by
      calc ∑ d ∈ (Finset.Ioo 0 F.p).erase j₀, ‖1 + F.chiC n ξ (B d)‖
          ≤ ∑ d ∈ (Finset.Ioo 0 F.p).erase j₀, (2 : ℝ) := Finset.sum_le_sum fun d _ => hnormB d
        _ = 2 * ((F.p : ℝ) - 2) := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul]
            push_cast [Nat.cast_sub (by omega : 2 ≤ F.p)]
            ring
    linarith
  -- assembly
  unfold fCond
  rw [← hP, ← hQ, hsum]
  have hcoef : ‖(((((3 : ℕ) : ℂ)) - 1) * ((F.p : ℂ) - 1) ^ 2)⁻¹‖
      = (2 * ((F.p : ℝ) - 1) ^ 2)⁻¹ := by
    have h1 : ((((3 : ℕ) : ℂ)) - 1) * ((F.p : ℂ) - 1) ^ 2
        = (((2 * ((F.p : ℝ) - 1) ^ 2 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [h1, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [norm_mul, hcoef]
  have hS : ‖∑ d ∈ Finset.Ioo 0 F.p, ((1 + F.chiC n ξ (B d))
        * ∑ d' ∈ Finset.Ioo 0 F.p, F.chiC n ξ (A d d'))‖
      ≤ ((F.p : ℝ) - 1) * (2 * |F.cosπθ n (F.phaseC ξ) j (l : ℤ)| + 2 * ((F.p : ℝ) - 2)) := by
    calc ‖∑ d ∈ Finset.Ioo 0 F.p, ((1 + F.chiC n ξ (B d))
          * ∑ d' ∈ Finset.Ioo 0 F.p, F.chiC n ξ (A d d'))‖
        ≤ ∑ d ∈ Finset.Ioo 0 F.p, ‖(1 + F.chiC n ξ (B d))
            * ∑ d' ∈ Finset.Ioo 0 F.p, F.chiC n ξ (A d d')‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.Ioo 0 F.p, ‖1 + F.chiC n ξ (B d)‖ * ((F.p : ℝ) - 1) := by
          refine Finset.sum_le_sum fun d _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hnormA d) (norm_nonneg _)
      _ = ((F.p : ℝ) - 1) * ∑ d ∈ Finset.Ioo 0 F.p, ‖1 + F.chiC n ξ (B d)‖ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun d _ => by ring
      _ ≤ ((F.p : ℝ) - 1) * (2 * |F.cosπθ n (F.phaseC ξ) j (l : ℤ)| + 2 * ((F.p : ℝ) - 2)) :=
          mul_le_mul_of_nonneg_left hsumB hp1.le
  calc (2 * ((F.p : ℝ) - 1) ^ 2)⁻¹ * ‖∑ d ∈ Finset.Ioo 0 F.p, ((1 + F.chiC n ξ (B d))
          * ∑ d' ∈ Finset.Ioo 0 F.p, F.chiC n ξ (A d d'))‖
      ≤ (2 * ((F.p : ℝ) - 1) ^ 2)⁻¹
          * (((F.p : ℝ) - 1) * (2 * |F.cosπθ n (F.phaseC ξ) j (l : ℤ)| + 2 * ((F.p : ℝ) - 2))) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = 1 - (1 - |F.cosπθ n (F.phaseC ξ) j (l : ℤ)|) / ((F.p : ℝ) - 1) := by
        field_simp
        ring

/-- **Decay at white points**: if `0 ≤ ε ≤ 1/p` and `(j,l)` is white, then `‖f(q^{2j}p^{-l}, 3)‖ ≤ exp(-ε³)`. -/
theorem fCond_three_white (n ξ j l : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / (F.p : ℝ))
    (hw : F.white n (F.phaseC ξ) ε j (l : ℤ)) :
    ‖F.fCond n ξ (F.xArg n j l) 3‖ ≤ Real.exp (-(ε ^ 3)) := by
  have hp : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hp1 : (0 : ℝ) < (F.p : ℝ) - 1 := by linarith
  have hcos := F.white_cos_bound n (F.phaseC ξ) hε0 j (l : ℤ) hw
  have h1 := F.fCond_three_norm_le n ξ j l
  have h2 : 1 - (1 - |F.cosπθ n (F.phaseC ξ) j (l : ℤ)|) / ((F.p : ℝ) - 1)
      ≤ 1 - 2 * ε ^ 2 / ((F.p : ℝ) - 1) := by
    have : 2 * ε ^ 2 ≤ 1 - |F.cosπθ n (F.phaseC ξ) j (l : ℤ)| := by linarith
    have := div_le_div_of_nonneg_right this hp1.le
    linarith
  have h3 : ε ^ 3 ≤ 2 * ε ^ 2 / ((F.p : ℝ) - 1) := by
    rw [le_div_iff₀ hp1]
    have hεp : ε * ((F.p : ℝ) - 1) ≤ 2 := by
      have : ε * (F.p : ℝ) ≤ 1 := by
        have hpp : (0 : ℝ) < F.p := by linarith
        calc ε * (F.p : ℝ) ≤ (1 / (F.p : ℝ)) * F.p := mul_le_mul_of_nonneg_right hε hpp.le
          _ = 1 := by field_simp
      nlinarith
    have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
    nlinarith
  have h4 : 1 - 2 * ε ^ 2 / ((F.p : ℝ) - 1) ≤ Real.exp (-(2 * ε ^ 2 / ((F.p : ℝ) - 1))) := by
    have := Real.add_one_le_exp (-(2 * ε ^ 2 / ((F.p : ℝ) - 1)))
    linarith
  have h5 : Real.exp (-(2 * ε ^ 2 / ((F.p : ℝ) - 1))) ≤ Real.exp (-(ε ^ 3)) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

open Classical in
/-- **Product bound** (`prod_fCond_le_damping` of tao-collatz): if `half ≤ n/2` and `0 ≤ ε ≤ 1/p`, then
`∏_{j<n/2} ‖f‖ ≤ exp(-ε³ #{j < half : b_j = 3, (j, b_{[1,j+1]}) white})`. -/
theorem prod_fCond_le_damping (n ξ half : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / (F.p : ℝ)) (b : Fin (n / 2) → ℕ) :
    ∏ j : Fin (n / 2), ‖F.fCond n ξ (F.xArg n (j : ℕ) (pre b ((j : ℕ) + 1))) (b j)‖
      ≤ Real.exp (-(ε ^ 3) *
          ((Finset.univ.filter fun j : Fin (n / 2) =>
            (j : ℕ) < half ∧ b j = 3 ∧
              F.white n (F.phaseC ξ) ε (j : ℕ) ((pre b ((j : ℕ) + 1) : ℕ) : ℤ)).card : ℝ)) := by
  have hstep : ∏ j : Fin (n / 2),
        ‖F.fCond n ξ (F.xArg n (j : ℕ) (pre b ((j : ℕ) + 1))) (b j)‖
      ≤ ∏ j : Fin (n / 2),
        (if (j : ℕ) < half ∧ b j = 3 ∧
            F.white n (F.phaseC ξ) ε (j : ℕ) ((pre b ((j : ℕ) + 1) : ℕ) : ℤ)
          then Real.exp (-(ε ^ 3)) else 1) := by
    refine Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => ?_)
    by_cases h : (j : ℕ) < half ∧ b j = 3 ∧
        F.white n (F.phaseC ξ) ε (j : ℕ) ((pre b ((j : ℕ) + 1) : ℕ) : ℤ)
    · rw [if_pos h, h.2.1]
      exact F.fCond_three_white n ξ (j : ℕ) (pre b ((j : ℕ) + 1)) hε0 hε h.2.2
    · rw [if_neg h]
      exact F.fCond_norm_le_one n ξ _ _
  refine le_trans hstep (le_of_eq ?_)
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one,
    ← Real.exp_nat_mul]
  congr 1
  ring

end Family

end GGMCollatz
