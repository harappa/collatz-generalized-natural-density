import GGMCollatz.Tao.Sec6.Core

/-!
# Fourier decomposition of the conditioned density (the key identity of GGM §5 Step 1 and Plancherel)

Derived from `TaoCollatz/Sec6/MixingCore.lean` (second half, from `char_offset_split` to
`condDensW_osc_le`) of gotrevor/tao-collatz (Apache-2.0), commit 15efca2; generalized to the GGM family
(p, q, r): `3ⁿ` is replaced by `qⁿ`, `2⁻¹` by `p⁻¹`, `geomHalf` by the one-step law `stepLaw p` (pairs of
valuation and digit), and `fnat` by `fint (a, r ∘ d)`.

The orientation is the same reversed form as in tao-collatz (`syracZ_eq_rev_fint`): the **last** `P`
components of a vector of length `j + P` (`vt`, the first `k + 1 = P` pairs `(𝒢_i, 𝒰_i)` of GGM) give the
low `q`-adic digits `𝒮_{k+1}`, and the **first** `j` components (`vh`) give `q^{k+1} p^{-M} 𝒮'_{n-k-1}`
(the key identity of GGM §5).

* `roff_split`, `char_roff_split`: the key identity `𝒮_n = 𝒮_{k+1} + q^{k+1} p^{-M} 𝒮'`.
* `cond_char_factorW`: conditioned on `M = l`, the characteristic function factors as head × tail.
* `head_factor_eq_charFn`: the head factor is the characteristic function of `𝒮_j` at level `j`
  (frequency `p^{-l} ξ mod q^j`).
* `condDensW_osc_le`: `Osc(g) ≤ D √(q^{j+P} ∑ (tailDensW)²)` (Cauchy–Schwarz, Plancherel, decay `D` of the head).
-/

open scoped BigOperators ENNReal

namespace GGMCollatz

namespace Mix

/-- **DFT of the density of a conditioned pushforward** (general modulus `N`): the DFT of
`Y ↦ P(X = Y ∧ w)` is `E[e(-Xξ) 1_w]`. -/
theorem dft_cond_density {ι : Type*} {N : ℕ} [NeZero N] (P : PMF ι) (X : ι → ZMod N)
    (w : ι → Prop) [DecidablePred w] (ξ : ZMod N) :
    ZMod.dft (fun Y => (((∑' a, (P a).toReal * (if X a = Y ∧ w a then (1 : ℝ) else 0)) : ℝ) : ℂ))
        ξ
      = P.cexpect (fun a => ZMod.stdAddChar (-(X a * ξ)) * (if w a then (1 : ℂ) else 0)) := by
  classical
  have hbase : Summable (fun a => (P a).toReal) :=
    ENNReal.summable_toReal (by rw [P.tsum_coe]; exact ENNReal.one_ne_top)
  have hsum : ∀ Y : ZMod N, Summable (fun a => ZMod.stdAddChar (-(Y * ξ))
      * (((P a).toReal : ℂ) * ((if X a = Y ∧ w a then (1 : ℝ) else 0 : ℝ) : ℂ))) := by
    intro Y
    refine Summable.of_norm_bounded hbase (fun a => ?_)
    rw [norm_mul, norm_mul, norm_stdAddChar, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg]
    have hle : ‖((if X a = Y ∧ w a then (1 : ℝ) else 0 : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; by_cases h : X a = Y ∧ w a
      · rw [if_pos h]; simp
      · rw [if_neg h]; simp
    calc (P a).toReal * ‖((if X a = Y ∧ w a then (1 : ℝ) else 0 : ℝ) : ℂ)‖
        ≤ (P a).toReal * 1 := mul_le_mul_of_nonneg_left hle ENNReal.toReal_nonneg
      _ = (P a).toReal := mul_one _
  have hcore : ∀ a : ι, (∑ Y, ZMod.stdAddChar (-(Y * ξ))
        * ((if X a = Y ∧ w a then (1 : ℝ) else 0 : ℝ) : ℂ))
      = ZMod.stdAddChar (-(X a * ξ)) * (if w a then (1 : ℂ) else 0) := by
    intro a
    by_cases h : w a
    · simp only [h, and_true, mul_one, apply_ite (Complex.ofReal), Complex.ofReal_one,
        Complex.ofReal_zero, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ (X a) (fun Y => ZMod.stdAddChar (-(Y * ξ)))]
      simp
    · simp only [h, and_false, if_false, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero]
  have hterm : ∀ Y : ZMod N,
      ZMod.stdAddChar (-(Y * ξ)) * ((∑' a, (P a).toReal
          * (if X a = Y ∧ w a then (1 : ℝ) else 0) : ℝ) : ℂ)
        = ∑' a, ZMod.stdAddChar (-(Y * ξ)) * (((P a).toReal : ℂ)
          * ((if X a = Y ∧ w a then (1 : ℝ) else 0 : ℝ) : ℂ)) := by
    intro Y
    rw [Complex.ofReal_tsum, ← tsum_mul_left]
    refine tsum_congr (fun a => ?_); push_cast; ring
  rw [ZMod.dft_apply, PMF.cexpect]
  simp only [smul_eq_mul]
  rw [Finset.sum_congr rfl (fun Y _ => hterm Y), ← Summable.tsum_finsetSum (fun Y _ => hsum Y)]
  refine tsum_congr (fun a => ?_)
  rw [show (fun Y => ZMod.stdAddChar (-(Y * ξ)) * (((P a).toReal : ℂ)
        * ((if X a = Y ∧ w a then (1 : ℝ) else 0 : ℝ) : ℂ)))
      = (fun Y => ((P a).toReal : ℂ) * (ZMod.stdAddChar (-(Y * ξ))
        * ((if X a = Y ∧ w a then (1 : ℝ) else 0 : ℝ) : ℂ))) from by funext Y; ring,
    ← Finset.mul_sum, hcore a]

/-- Reduction of the collision entropy: if `0 ≤ d ≤ M` then `∑ d² ≤ M ∑ d`. -/
theorem sum_sq_le_max_mul_sum {N : ℕ} [NeZero N] (d : ZMod N → ℝ) (M : ℝ)
    (h0 : ∀ Y, 0 ≤ d Y) (hM : ∀ Y, d Y ≤ M) :
    ∑ Y, (d Y) ^ 2 ≤ M * ∑ Y, d Y := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun Y _ => ?_)
  rw [sq]
  exact mul_le_mul_of_nonneg_right (hM Y) (h0 Y)

end Mix

namespace Family

variable (F : Family)

/-! ### The offset in reversed form and the key identity -/

/-- The offset in reversed form `fint(a, r ∘ d) · p^{-|a|}` modulo `q^e` (`v i = (a_i, d_i)`).
`F.syracZ n` is the pushforward of `(stepLaw p)^{⊗n}` by `roff n` (`syracZ_eq_roff`). -/
noncomputable def roff (e : ℕ) {k : ℕ} (v : Fin k → ℕ × ℕ) : ZMod (F.q ^ e) :=
  ((F.fint (fun i => (v i).1) (fun i => F.r (v i).2) : ℤ) : ZMod (F.q ^ e))
    * ((F.p : ZMod (F.q ^ e))⁻¹) ^ pre (fun i => (v i).1) k

theorem syracZ_eq_roff (n : ℕ) : F.syracZ n = ((stepLaw F.p).iid n).map (F.roff n) := by
  rw [syracZ_eq_rev_fint]; rfl

/-- **The key identity** (GGM §5 Step 1, reversed form):
`roff(v) = q^P · roff(vh) · p^{-M} + roff(vt)` (`M = pre(valuations of vt)`). -/
theorem roff_split {j P : ℕ} (v : Fin (j + P) → ℕ × ℕ) :
    F.roff (j + P) v
      = (F.q : ZMod (F.q ^ (j + P))) ^ P * F.roff (j + P) (fun i => v (Fin.castAdd P i))
          * ((F.p : ZMod (F.q ^ (j + P)))⁻¹) ^ pre (fun i => (v (Fin.natAdd j i)).1) P
        + F.roff (j + P) (fun i => v (Fin.natAdd j i)) := by
  have h := F.syracZ_offset_split (j := j) (l := P) (fun i => (v i).1) (fun i => F.r (v i).2)
  have hpre : pre (fun i => (v i).1) j = pre (fun i => (v (Fin.castAdd P i)).1) j :=
    (pre_castAdd (fun i => (v i).1) (le_refl j)).symm
  unfold roff
  rw [h, hpre]

/-- Splitting the character (from addition to multiplication). -/
theorem char_roff_split {j P : ℕ} (v : Fin (j + P) → ℕ × ℕ) (ξ : ZMod (F.q ^ (j + P))) :
    ZMod.stdAddChar (-(F.roff (j + P) v * ξ))
      = ZMod.stdAddChar (-(((F.q : ZMod (F.q ^ (j + P))) ^ P
            * F.roff (j + P) (fun i => v (Fin.castAdd P i))
            * ((F.p : ZMod (F.q ^ (j + P)))⁻¹) ^ pre (fun i => (v (Fin.natAdd j i)).1) P) * ξ))
        * ZMod.stdAddChar (-(F.roff (j + P) (fun i => v (Fin.natAdd j i)) * ξ)) := by
  rw [F.roff_split v, add_mul, neg_add, AddChar.map_add_eq_mul]

/-! ### Descent of the modulus -/

/-- **Descent of the modulus** (multiplication by `q^P` takes `q^{j+P} → q^j`; tao-collatz's `stdAddChar_pow3_descent_right`). -/
theorem stdAddChar_qpow_descent_right {j P : ℕ} (w : ZMod (F.q ^ (j + P))) :
    ZMod.stdAddChar ((F.q : ZMod (F.q ^ (j + P))) ^ P * w)
      = ZMod.stdAddChar
          (ZMod.castHom (pow_dvd_pow F.q (Nat.le_add_right j P)) (ZMod (F.q ^ j)) w) := by
  set m : ℕ := w.val with hmdef
  have hw : w = ((m : ℕ) : ZMod (F.q ^ (j + P))) := (ZMod.natCast_zmod_val w).symm
  rw [hw]
  have hL : (F.q : ZMod (F.q ^ (j + P))) ^ P * ((m : ℕ) : ZMod (F.q ^ (j + P)))
      = (((F.q ^ P * m : ℕ)) : ZMod (F.q ^ (j + P))) := by push_cast; ring
  have hR : ZMod.castHom (pow_dvd_pow F.q (Nat.le_add_right j P)) (ZMod (F.q ^ j))
        ((m : ℕ) : ZMod (F.q ^ (j + P))) = ((m : ℕ) : ZMod (F.q ^ j)) := by rw [map_natCast]
  have hq : (F.q : ℂ) ≠ 0 := F.q_complex_ne_zero
  rw [hL, hR,
     show (((F.q ^ P * m : ℕ)) : ZMod (F.q ^ (j + P)))
         = (((F.q ^ P * m : ℕ) : ℤ) : ZMod (F.q ^ (j + P))) by push_cast; ring,
     show ((m : ℕ) : ZMod (F.q ^ j)) = (((m : ℕ) : ℤ) : ZMod (F.q ^ j)) by push_cast; ring,
     ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [pow_add]
  field_simp

/-- The projection commutes with `roff` (`p⁻¹` maps to `p⁻¹`). -/
theorem castHom_roff {e e' : ℕ} (h : e' ≤ e) {k : ℕ} (v : Fin k → ℕ × ℕ) :
    ZMod.castHom (pow_dvd_pow F.q h) (ZMod (F.q ^ e')) (F.roff e v) = F.roff e' v := by
  unfold roff
  rw [map_mul, map_pow, map_intCast, F.castHom_p_inv h]

/-- **Descent of the head factor** (pointwise): the prefactor `q^P` takes level `j + P` down to `j`, and the
frozen phase `p^{-l}` is absorbed into the frequency. -/
theorem head_char_descent {j P : ℕ} (l : ℕ) (ξ : ZMod (F.q ^ (j + P))) (vh : Fin j → ℕ × ℕ) :
    ZMod.stdAddChar (-(((F.q : ZMod (F.q ^ (j + P))) ^ P * F.roff (j + P) vh
          * ((F.p : ZMod (F.q ^ (j + P)))⁻¹) ^ l) * ξ))
      = ZMod.stdAddChar (-(F.roff j vh
          * (((F.p : ZMod (F.q ^ j))⁻¹) ^ l
            * ZMod.castHom (pow_dvd_pow F.q (Nat.le_add_right j P)) (ZMod (F.q ^ j)) ξ))) := by
  have harg : -(((F.q : ZMod (F.q ^ (j + P))) ^ P * F.roff (j + P) vh
          * ((F.p : ZMod (F.q ^ (j + P)))⁻¹) ^ l) * ξ)
      = (F.q : ZMod (F.q ^ (j + P))) ^ P * (-(F.roff (j + P) vh
          * (((F.p : ZMod (F.q ^ (j + P)))⁻¹) ^ l * ξ))) := by ring
  rw [harg, F.stdAddChar_qpow_descent_right]
  congr 1
  rw [map_neg, map_mul, map_mul, map_pow, F.castHom_p_inv (Nat.le_add_right j P),
    F.castHom_roff (Nat.le_add_right j P)]

/-- The expectation of the character of the offset in reversed form is the characteristic function of `𝒮_n`. -/
theorem roff_cexpect_eq_syracZ {n : ℕ} (freq : ZMod (F.q ^ n)) :
    ((stepLaw F.p).iid n).cexpect (fun v => ZMod.stdAddChar (-(F.roff n v * freq)))
      = (F.syracZ n).cexpect (fun Y => ZMod.stdAddChar (-(Y * freq))) := by
  rw [syracZ_eq_roff, Mix.cexpect_map _ _ _ (fun Y => le_of_eq (Mix.norm_stdAddChar _))]

/-- **The head factor is the characteristic function at level `j`** (in the form of the statement of Proposition 5.1, frequency `ζ = p^{-l} (ξ mod q^j)`). -/
theorem head_factor_eq_charFn {j P : ℕ} (l : ℕ) (ξ : ZMod (F.q ^ (j + P))) :
    ((stepLaw F.p).iid j).cexpect (fun vh => ZMod.stdAddChar
        (-(((F.q : ZMod (F.q ^ (j + P))) ^ P * F.roff (j + P) vh
          * ((F.p : ZMod (F.q ^ (j + P)))⁻¹) ^ l) * ξ)))
      = (F.syracZ j).cexpect (fun Y => eC (-(((((F.p : ZMod (F.q ^ j))⁻¹) ^ l
            * ZMod.castHom (pow_dvd_pow F.q (Nat.le_add_right j P)) (ZMod (F.q ^ j)) ξ).val)
            * Y.val : ℚ) / (F.q : ℚ) ^ j)) := by
  rw [congrArg (PMF.cexpect ((stepLaw F.p).iid j))
      (funext (fun vh : Fin j → ℕ × ℕ => F.head_char_descent l ξ vh)),
    F.roff_cexpect_eq_syracZ]
  refine congrArg (PMF.cexpect (F.syracZ j)) (funext (fun Y => ?_))
  rw [Mix.stdAddChar_mul_eq_eC]
  push_cast
  rfl

/-! ### The conditional factorization -/

/-- **Conditional factorization of the character** (GGM §5 Step 1: given `𝒢_{1,k+1} = M`, the two terms are
independent): conditioned on the tail event `pre(vt) = l ∧ W(vt)`, the characteristic function is the product
of the expectation over the head and the expectation over the tail. -/
theorem cond_char_factorW {j P : ℕ} (ξ : ZMod (F.q ^ (j + P))) (l : ℕ)
    (W : (Fin P → ℕ × ℕ) → Prop) [DecidablePred W] :
    ((stepLaw F.p).iid (j + P)).cexpect
        (fun v => ZMod.stdAddChar (-(F.roff (j + P) v * ξ))
          * (if pre (fun i => (v (Fin.natAdd j i)).1) P = l ∧ W (fun i => v (Fin.natAdd j i))
              then 1 else 0))
      = ((stepLaw F.p).iid j).cexpect
            (fun vh => ZMod.stdAddChar (-(((F.q : ZMod (F.q ^ (j + P))) ^ P * F.roff (j + P) vh
                  * ((F.p : ZMod (F.q ^ (j + P)))⁻¹) ^ l) * ξ)))
        * ((stepLaw F.p).iid P).cexpect
            (fun vt => ZMod.stdAddChar (-(F.roff (j + P) vt * ξ))
              * (if pre (fun i => (vt i).1) P = l ∧ W vt then 1 else 0)) := by
  set f : (Fin j → ℕ × ℕ) → ℂ := fun vh => ZMod.stdAddChar (-(((F.q : ZMod (F.q ^ (j + P))) ^ P
      * F.roff (j + P) vh * ((F.p : ZMod (F.q ^ (j + P)))⁻¹) ^ l) * ξ)) with hf
  set g : (Fin P → ℕ × ℕ) → ℂ := fun vt => ZMod.stdAddChar (-(F.roff (j + P) vt * ξ))
      * (if pre (fun i => (vt i).1) P = l ∧ W vt then 1 else 0) with hg
  have hfb : ∀ vh, ‖f vh‖ ≤ 1 := fun vh => le_of_eq (Mix.norm_stdAddChar _)
  have hgb : ∀ vt, ‖g vt‖ ≤ 1 := fun vt => by
    simp only [hg]
    by_cases h : pre (fun i => (vt i).1) P = l ∧ W vt
    · rw [if_pos h, mul_one]; exact le_of_eq (Mix.norm_stdAddChar _)
    · rw [if_neg h, mul_zero, norm_zero]; exact zero_le_one
  rw [← PMF.cexpect_iid_append (stepLaw F.p) j P f g hfb hgb]
  refine congrArg (PMF.cexpect ((stepLaw F.p).iid (j + P))) ?_
  funext v
  simp only [hf, hg]
  by_cases h : pre (fun i => (v (Fin.natAdd j i)).1) P = l ∧ W (fun i => v (Fin.natAdd j i))
  · simp only [if_pos h, mul_one]
    rw [F.char_roff_split v ξ, h.1]
  · simp only [if_neg h, mul_zero]

/-! ### The conditioned density and the tail density -/

/-- **The conditioned density** `g_{j,P,l,W}`: `𝒮_{j+P}` restricted to the tail event `pre(vt) = l ∧ W(vt)`. -/
noncomputable def condDensW (j P l : ℕ) (W : (Fin P → ℕ × ℕ) → Prop) [DecidablePred W] :
    ZMod (F.q ^ (j + P)) → ℝ := fun Y =>
  ∑' v : Fin (j + P) → ℕ × ℕ, (((stepLaw F.p).iid (j + P)) v).toReal
    * (if F.roff (j + P) v = Y
          ∧ (pre (fun i => (v (Fin.natAdd j i)).1) P = l ∧ W (fun i => v (Fin.natAdd j i)))
        then (1 : ℝ) else 0)

/-- **The tail density**: the pushforward of the tail offset (embedded at level `j + P`) on the event `pre = l ∧ W`. -/
noncomputable def tailDensW (j P l : ℕ) (W : (Fin P → ℕ × ℕ) → Prop) [DecidablePred W] :
    ZMod (F.q ^ (j + P)) → ℝ := fun Y =>
  ∑' vt : Fin P → ℕ × ℕ, (((stepLaw F.p).iid P) vt).toReal
    * (if F.roff (j + P) vt = Y ∧ (pre (fun i => (vt i).1) P = l ∧ W vt) then (1 : ℝ) else 0)

theorem dft_condDensW_eq_cond_char (j P l : ℕ) (W : (Fin P → ℕ × ℕ) → Prop) [DecidablePred W]
    (ξ : ZMod (F.q ^ (j + P))) :
    ZMod.dft (F.densC (j + P) (F.condDensW j P l W)) ξ
      = ((stepLaw F.p).iid (j + P)).cexpect (fun v =>
          ZMod.stdAddChar (-(F.roff (j + P) v * ξ))
            * (if pre (fun i => (v (Fin.natAdd j i)).1) P = l ∧ W (fun i => v (Fin.natAdd j i))
                then 1 else 0)) :=
  Mix.dft_cond_density ((stepLaw F.p).iid (j + P)) (F.roff (j + P))
    (fun v => pre (fun i => (v (Fin.natAdd j i)).1) P = l ∧ W (fun i => v (Fin.natAdd j i))) ξ

theorem tail_factor_dft_eqW (j P l : ℕ) (W : (Fin P → ℕ × ℕ) → Prop) [DecidablePred W]
    (ξ : ZMod (F.q ^ (j + P))) :
    ZMod.dft (F.densC (j + P) (F.tailDensW j P l W)) ξ
      = ((stepLaw F.p).iid P).cexpect (fun vt => ZMod.stdAddChar (-(F.roff (j + P) vt * ξ))
          * (if pre (fun i => (vt i).1) P = l ∧ W vt then 1 else 0)) :=
  Mix.dft_cond_density ((stepLaw F.p).iid P) (F.roff (j + P))
    (fun vt => pre (fun i => (vt i).1) P = l ∧ W vt) ξ

/-- **Collision entropy of the tail** (Plancherel): `∑_ξ ‖tail(ξ)‖² = q^{j+P} ∑_Y (tailDensW)²`. -/
theorem tail_factor_l2_eqW (j P l : ℕ) (W : (Fin P → ℕ × ℕ) → Prop) [DecidablePred W] :
    ∑ ξ, ‖((stepLaw F.p).iid P).cexpect (fun vt => ZMod.stdAddChar (-(F.roff (j + P) vt * ξ))
          * (if pre (fun i => (vt i).1) P = l ∧ W vt then 1 else 0))‖ ^ 2
      = (F.q : ℝ) ^ (j + P) * ∑ Y, (F.tailDensW j P l W Y) ^ 2 := by
  have h1 : ∀ ξ : ZMod (F.q ^ (j + P)),
      ((stepLaw F.p).iid P).cexpect (fun vt => ZMod.stdAddChar (-(F.roff (j + P) vt * ξ))
          * (if pre (fun i => (vt i).1) P = l ∧ W vt then 1 else 0))
        = ZMod.dft (F.densC (j + P) (F.tailDensW j P l W)) ξ :=
    fun ξ => (F.tail_factor_dft_eqW j P l W ξ).symm
  have hnorm : ∀ Y : ZMod (F.q ^ (j + P)),
      ‖F.densC (j + P) (F.tailDensW j P l W) Y‖ ^ 2 = (F.tailDensW j P l W Y) ^ 2 := by
    intro Y; rw [densC, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [h1]
  rw [dft_parseval (F.densC (j + P) (F.tailDensW j P l W))]
  simp_rw [hnorm]
  push_cast; ring

theorem tailDensW_nonneg (j P l : ℕ) (W : (Fin P → ℕ × ℕ) → Prop) [DecidablePred W]
    (Y : ZMod (F.q ^ (j + P))) : 0 ≤ F.tailDensW j P l W Y := by
  refine tsum_nonneg (fun vt => ?_)
  exact mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num)

/-- The total mass of the tail density is at most 1. -/
theorem tailDensW_sum_le_one (j P l : ℕ) (W : (Fin P → ℕ × ℕ) → Prop) [DecidablePred W] :
    ∑ Y, F.tailDensW j P l W Y ≤ 1 := by
  have hbase : Summable (fun vt : Fin P → ℕ × ℕ => (((stepLaw F.p).iid P) vt).toReal) :=
    ENNReal.summable_toReal (by rw [((stepLaw F.p).iid P).tsum_coe]; exact ENNReal.one_ne_top)
  have hone : ∑' vt : Fin P → ℕ × ℕ, (((stepLaw F.p).iid P) vt).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun vt => ((stepLaw F.p).iid P).apply_ne_top vt),
      ((stepLaw F.p).iid P).tsum_coe]; rfl
  have hsum : ∀ Y : ZMod (F.q ^ (j + P)), Summable (fun vt : Fin P → ℕ × ℕ =>
      (((stepLaw F.p).iid P) vt).toReal
        * (if F.roff (j + P) vt = Y ∧ (pre (fun i => (vt i).1) P = l ∧ W vt)
            then (1 : ℝ) else 0)) := by
    intro Y
    refine Summable.of_nonneg_of_le
      (fun vt => mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num)) (fun vt => ?_) hbase
    calc (((stepLaw F.p).iid P) vt).toReal
          * (if F.roff (j + P) vt = Y ∧ (pre (fun i => (vt i).1) P = l ∧ W vt)
              then (1 : ℝ) else 0)
        ≤ (((stepLaw F.p).iid P) vt).toReal * 1 :=
          mul_le_mul_of_nonneg_left (by split <;> norm_num) ENNReal.toReal_nonneg
      _ = (((stepLaw F.p).iid P) vt).toReal := mul_one _
  have hcollapse : ∀ vt : Fin P → ℕ × ℕ,
      ∑ Y : ZMod (F.q ^ (j + P)),
        (if F.roff (j + P) vt = Y ∧ (pre (fun i => (vt i).1) P = l ∧ W vt) then (1 : ℝ) else 0)
        = (if pre (fun i => (vt i).1) P = l ∧ W vt then (1 : ℝ) else 0) := by
    intro vt
    by_cases h : pre (fun i => (vt i).1) P = l ∧ W vt
    · simp only [h, and_true, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    · simp only [h, and_false, if_false, Finset.sum_const_zero]
  calc ∑ Y, F.tailDensW j P l W Y
      = ∑' vt : Fin P → ℕ × ℕ, (((stepLaw F.p).iid P) vt).toReal
          * ∑ Y : ZMod (F.q ^ (j + P)),
            (if F.roff (j + P) vt = Y ∧ (pre (fun i => (vt i).1) P = l ∧ W vt)
              then (1 : ℝ) else 0) := by
        simp only [tailDensW]
        rw [← Summable.tsum_finsetSum (fun Y _ => hsum Y)]
        refine tsum_congr (fun vt => ?_)
        rw [Finset.mul_sum]
    _ = ∑' vt : Fin P → ℕ × ℕ, (((stepLaw F.p).iid P) vt).toReal
          * (if pre (fun i => (vt i).1) P = l ∧ W vt then (1 : ℝ) else 0) := by
        refine tsum_congr (fun vt => ?_); rw [hcollapse vt]
    _ ≤ ∑' vt : Fin P → ℕ × ℕ, (((stepLaw F.p).iid P) vt).toReal := by
        have hle : ∀ vt : Fin P → ℕ × ℕ,
            (((stepLaw F.p).iid P) vt).toReal
                * (if pre (fun i => (vt i).1) P = l ∧ W vt then (1 : ℝ) else 0)
              ≤ (((stepLaw F.p).iid P) vt).toReal := by
          intro vt
          calc (((stepLaw F.p).iid P) vt).toReal
                * (if pre (fun i => (vt i).1) P = l ∧ W vt then (1 : ℝ) else 0)
              ≤ (((stepLaw F.p).iid P) vt).toReal * 1 :=
                mul_le_mul_of_nonneg_left (by split <;> norm_num) ENNReal.toReal_nonneg
            _ = (((stepLaw F.p).iid P) vt).toReal := mul_one _
        refine Summable.tsum_le_tsum hle ?_ hbase
        exact Summable.of_nonneg_of_le
          (fun vt => mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num)) hle hbase
    _ = 1 := hone

/-- From a pointwise upper bound `M`, the collision entropy satisfies `∑ (tailDensW)² ≤ M`. -/
theorem tailDensW_renyi_le (j P l : ℕ) (W : (Fin P → ℕ × ℕ) → Prop) [DecidablePred W] (M : ℝ)
    (hM : ∀ Y, F.tailDensW j P l W Y ≤ M) :
    ∑ Y, (F.tailDensW j P l W Y) ^ 2 ≤ M := by
  have hM0 : 0 ≤ M := le_trans (F.tailDensW_nonneg j P l W 0) (hM 0)
  calc ∑ Y, (F.tailDensW j P l W Y) ^ 2
      ≤ M * ∑ Y, F.tailDensW j P l W Y :=
        Mix.sum_sq_le_max_mul_sum _ M (F.tailDensW_nonneg j P l W) hM
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left (F.tailDensW_sum_le_one j P l W) hM0
    _ = M := mul_one M

/-- The `ℓ²` mass of the high frequencies is `≤ D² q^{j+P} ∑ (tailDensW)²` (under a uniform decay `D` of the head). -/
theorem condDensW_highfreq_l2_le (j P l m : ℕ) (W : (Fin P → ℕ × ℕ) → Prop) [DecidablePred W]
    (D : ℝ)
    (hunif : ∀ ξ ∈ F.highFreq m (j + P),
      ‖((stepLaw F.p).iid j).cexpect (fun vh => ZMod.stdAddChar
          (-(((F.q : ZMod (F.q ^ (j + P))) ^ P * F.roff (j + P) vh
            * ((F.p : ZMod (F.q ^ (j + P)))⁻¹) ^ l) * ξ)))‖ ≤ D) :
    ∑ ξ ∈ F.highFreq m (j + P), ‖ZMod.dft (F.densC (j + P) (F.condDensW j P l W)) ξ‖ ^ 2
      ≤ D ^ 2 * (F.q : ℝ) ^ (j + P) * ∑ Y, (F.tailDensW j P l W Y) ^ 2 := by
  have hpt : ∀ ξ ∈ F.highFreq m (j + P),
      ‖ZMod.dft (F.densC (j + P) (F.condDensW j P l W)) ξ‖ ^ 2
        ≤ D ^ 2 * ‖((stepLaw F.p).iid P).cexpect (fun vt =>
            ZMod.stdAddChar (-(F.roff (j + P) vt * ξ))
            * (if pre (fun i => (vt i).1) P = l ∧ W vt then 1 else 0))‖ ^ 2 := by
    intro ξ hξ
    rw [dft_condDensW_eq_cond_char, cond_char_factorW, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hunif ξ hξ) 2)
      (sq_nonneg _)
  calc ∑ ξ ∈ F.highFreq m (j + P), ‖ZMod.dft (F.densC (j + P) (F.condDensW j P l W)) ξ‖ ^ 2
      ≤ ∑ ξ ∈ F.highFreq m (j + P), D ^ 2 * ‖((stepLaw F.p).iid P).cexpect (fun vt =>
            ZMod.stdAddChar (-(F.roff (j + P) vt * ξ))
            * (if pre (fun i => (vt i).1) P = l ∧ W vt then 1 else 0))‖ ^ 2 :=
        Finset.sum_le_sum hpt
    _ = D ^ 2 * ∑ ξ ∈ F.highFreq m (j + P), ‖((stepLaw F.p).iid P).cexpect (fun vt =>
            ZMod.stdAddChar (-(F.roff (j + P) vt * ξ))
            * (if pre (fun i => (vt i).1) P = l ∧ W vt then 1 else 0))‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ D ^ 2 * ∑ ξ, ‖((stepLaw F.p).iid P).cexpect (fun vt =>
            ZMod.stdAddChar (-(F.roff (j + P) vt * ξ))
            * (if pre (fun i => (vt i).1) P = l ∧ W vt then 1 else 0))‖ ^ 2 :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => sq_nonneg _)) (sq_nonneg _)
    _ = D ^ 2 * ((F.q : ℝ) ^ (j + P) * ∑ Y, (F.tailDensW j P l W Y) ^ 2) := by
        rw [tail_factor_l2_eqW]
    _ = D ^ 2 * (F.q : ℝ) ^ (j + P) * ∑ Y, (F.tailDensW j P l W Y) ^ 2 := by ring

/-- **Oscillation bound for a single conditioning** (GGM §5 Step 1): `Osc(g) ≤ D √(q^{j+P} ∑ (tailDensW)²)`. -/
theorem condDensW_osc_le (j P l m : ℕ) (W : (Fin P → ℕ × ℕ) → Prop) [DecidablePred W]
    (hmn : m ≤ j + P) (D : ℝ) (hD : 0 ≤ D)
    (hunif : ∀ ξ ∈ F.highFreq m (j + P),
      ‖((stepLaw F.p).iid j).cexpect (fun vh => ZMod.stdAddChar
          (-(((F.q : ZMod (F.q ^ (j + P))) ^ P * F.roff (j + P) vh
            * ((F.p : ZMod (F.q ^ (j + P)))⁻¹) ^ l) * ξ)))‖ ≤ D) :
    F.osc m (j + P) hmn (F.condDensW j P l W)
      ≤ D * Real.sqrt ((F.q : ℝ) ^ (j + P) * ∑ Y, (F.tailDensW j P l W Y) ^ 2) := by
  calc F.osc m (j + P) hmn (F.condDensW j P l W)
      ≤ Real.sqrt (∑ ξ ∈ F.highFreq m (j + P),
          ‖ZMod.dft (F.densC (j + P) (F.condDensW j P l W)) ξ‖ ^ 2) :=
        F.osc_le_sqrt_highfreq _ _ _ _
    _ ≤ Real.sqrt (D ^ 2 * ((F.q : ℝ) ^ (j + P) * ∑ Y, (F.tailDensW j P l W Y) ^ 2)) := by
        apply Real.sqrt_le_sqrt
        rw [← mul_assoc]
        exact F.condDensW_highfreq_l2_le j P l m W D hunif
    _ = D * Real.sqrt ((F.q : ℝ) ^ (j + P) * ∑ Y, (F.tailDensW j P l W Y) ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hD]

end Family

end GGMCollatz
