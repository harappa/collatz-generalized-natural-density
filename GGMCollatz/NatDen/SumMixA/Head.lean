import GGMCollatz.NatDen.SumMixA.Basic

/-!
# Auxiliary (2) for Proposition 6.12 (a) of the paper: the Fourier decomposition of a piece conditioned on the sum, and the head factor

Adapted from `GGMCollatz/Tao/Sec6/Factor.lean` (`cond_char_factorW`, `condDensW_highfreq_l2_le`, `condDensW_osc_le`),
derived from `TaoCollatz/Sec6/MixingCore.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2, by adding
**the condition `s_N = σ` on the sum of all valuations**.

In the decomposition of the key identity, the sum of all valuations is "head sum + tail sum `l`", so the condition
`s_N = σ` enters the head factor as `1_{s_head + l = σ}` (the tail factor is as in Sec6). The head factor is the
characteristic function at level `j` conditioned on the sum (`headS_eq`), bounded by Proposition 6.7 of the paper (`sumcf_statement`)
or, outside its range, by Chernoff (`nb_dev_tail`) (`headS_bound`).

* `condDensWS`: the density of the push-forward restricted to the event of a piece and to `s_N = σ`.
* `headS`: the head factor `E[e(-q^P p^{-l} roff(vh) ξ) 1_{s_head + l = σ}]`.
* `condDensWS_osc_le`: `Osc ≤ D √(q^{j+P} Σ (tailDensW)²)` (with `‖headS‖ ≤ D` at high frequencies).
* `headS_bound`: for all `A`, `‖headS‖ ≤ K j^{-A}` (`j ≥ 2`, `q ∤ ξ`).
-/

open scoped BigOperators ENNReal

namespace GGMCollatz

namespace ND

namespace SumMixAAux

open Family

variable (F : Family)

/-- **The density of a piece conditioned on the sum**: the push-forward restricted to the tail event `pre(vt) = l ∧ W(vt)` and to `s_{j+P} = σ`. -/
noncomputable def condDensWS (j P l σ : ℕ) (W : (Fin P → ℕ × ℕ) → Prop) [DecidablePred W] :
    ZMod (F.q ^ (j + P)) → ℝ := fun Y =>
  ∑' v : Fin (j + P) → ℕ × ℕ, (((stepLaw F.p).iid (j + P)) v).toReal
    * (if F.roff (j + P) v = Y
          ∧ ((pre (fun i => (v (Fin.natAdd j i)).1) P = l ∧ W (fun i => v (Fin.natAdd j i)))
            ∧ pre (fun i => (v i).1) (j + P) = σ)
        then (1 : ℝ) else 0)

/-- **The head factor** (conditioned on the sum). -/
noncomputable def headS (j P l σ : ℕ) (ξ : ZMod (F.q ^ (j + P))) : ℂ :=
  ((stepLaw F.p).iid j).cexpect (fun vh => ZMod.stdAddChar
      (-(((F.q : ZMod (F.q ^ (j + P))) ^ P * F.roff (j + P) vh
        * ((F.p : ZMod (F.q ^ (j + P)))⁻¹) ^ l) * ξ))
      * (if pre (fun i => (vh i).1) j + l = σ then 1 else 0))

/-! ### The conditioned decomposition -/

/-- **Decomposition of the character conditioned on the sum**: head factor (conditioned on the sum) × tail factor (as in Sec6). -/
theorem cond_char_factorWS {j P : ℕ} (ξ : ZMod (F.q ^ (j + P))) (l σ : ℕ)
    (W : (Fin P → ℕ × ℕ) → Prop) [DecidablePred W] :
    ((stepLaw F.p).iid (j + P)).cexpect
        (fun v => ZMod.stdAddChar (-(F.roff (j + P) v * ξ))
          * (if (pre (fun i => (v (Fin.natAdd j i)).1) P = l ∧ W (fun i => v (Fin.natAdd j i)))
                ∧ pre (fun i => (v i).1) (j + P) = σ then 1 else 0))
      = headS F j P l σ ξ
        * ((stepLaw F.p).iid P).cexpect
            (fun vt => ZMod.stdAddChar (-(F.roff (j + P) vt * ξ))
              * (if pre (fun i => (vt i).1) P = l ∧ W vt then 1 else 0)) := by
  set f : (Fin j → ℕ × ℕ) → ℂ := fun vh => ZMod.stdAddChar (-(((F.q : ZMod (F.q ^ (j + P))) ^ P
      * F.roff (j + P) vh * ((F.p : ZMod (F.q ^ (j + P)))⁻¹) ^ l) * ξ))
      * (if pre (fun i => (vh i).1) j + l = σ then 1 else 0) with hf
  set g : (Fin P → ℕ × ℕ) → ℂ := fun vt => ZMod.stdAddChar (-(F.roff (j + P) vt * ξ))
      * (if pre (fun i => (vt i).1) P = l ∧ W vt then 1 else 0) with hg
  have hfb : ∀ vh, ‖f vh‖ ≤ 1 := fun vh => by
    simp only [hf]
    split_ifs
    · rw [mul_one]; exact le_of_eq (Mix.norm_stdAddChar _)
    · rw [mul_zero, norm_zero]; exact zero_le_one
  have hgb : ∀ vt, ‖g vt‖ ≤ 1 := fun vt => by
    simp only [hg]
    split_ifs
    · rw [mul_one]; exact le_of_eq (Mix.norm_stdAddChar _)
    · rw [mul_zero, norm_zero]; exact zero_le_one
  unfold headS
  rw [← PMF.cexpect_iid_append (stepLaw F.p) j P f g hfb hgb]
  refine congrArg (PMF.cexpect ((stepLaw F.p).iid (j + P))) ?_
  funext v
  simp only [hf, hg]
  have hpre : pre (fun i => (v i).1) (j + P) = pre (fun i => (v (Fin.castAdd P i)).1) j
      + pre (fun i => (v (Fin.natAdd j i)).1) P := by
    rw [pre_natAdd_split (fun i => (v i).1) (le_refl P),
      pre_castAdd (fun i => (v i).1) (le_refl j)]
  by_cases h : pre (fun i => (v (Fin.natAdd j i)).1) P = l ∧ W (fun i => v (Fin.natAdd j i))
  · by_cases hσ : pre (fun i => (v (Fin.castAdd P i)).1) j + l = σ
    · have hc : (pre (fun i => (v (Fin.natAdd j i)).1) P = l ∧ W (fun i => v (Fin.natAdd j i)))
          ∧ pre (fun i => (v i).1) (j + P) = σ := ⟨h, by rw [hpre, h.1]; exact hσ⟩
      rw [if_pos hc, if_pos hσ, if_pos h, F.char_roff_split v ξ, h.1]
      ring
    · have hc : ¬ ((pre (fun i => (v (Fin.natAdd j i)).1) P = l
          ∧ W (fun i => v (Fin.natAdd j i))) ∧ pre (fun i => (v i).1) (j + P) = σ) :=
        fun h' => hσ (by rw [← h.1, ← hpre]; exact h'.2)
      rw [if_neg hc, if_neg hσ]
      ring
  · rw [if_neg (fun h' => h h'.1), if_neg h]
    ring

theorem dft_condDensWS_eq (j P l σ : ℕ) (W : (Fin P → ℕ × ℕ) → Prop) [DecidablePred W]
    (ξ : ZMod (F.q ^ (j + P))) :
    ZMod.dft (F.densC (j + P) (condDensWS F j P l σ W)) ξ
      = ((stepLaw F.p).iid (j + P)).cexpect (fun v =>
          ZMod.stdAddChar (-(F.roff (j + P) v * ξ))
            * (if (pre (fun i => (v (Fin.natAdd j i)).1) P = l ∧ W (fun i => v (Fin.natAdd j i)))
                ∧ pre (fun i => (v i).1) (j + P) = σ then 1 else 0)) :=
  Mix.dft_cond_density ((stepLaw F.p).iid (j + P)) (F.roff (j + P))
    (fun v => (pre (fun i => (v (Fin.natAdd j i)).1) P = l ∧ W (fun i => v (Fin.natAdd j i)))
      ∧ pre (fun i => (v i).1) (j + P) = σ) ξ

/-- The high-frequency `ℓ²` mass is `≤ D² q^{j+P} ∑ (tailDensW)²` (under a uniform decay `D` of the head conditioned on the sum). -/
theorem condDensWS_highfreq_l2_le (j P l σ m : ℕ) (W : (Fin P → ℕ × ℕ) → Prop)
    [DecidablePred W] (D : ℝ)
    (hunif : ∀ ξ ∈ F.highFreq m (j + P), ‖headS F j P l σ ξ‖ ≤ D) :
    ∑ ξ ∈ F.highFreq m (j + P), ‖ZMod.dft (F.densC (j + P) (condDensWS F j P l σ W)) ξ‖ ^ 2
      ≤ D ^ 2 * (F.q : ℝ) ^ (j + P) * ∑ Y, (F.tailDensW j P l W Y) ^ 2 := by
  have hpt : ∀ ξ ∈ F.highFreq m (j + P),
      ‖ZMod.dft (F.densC (j + P) (condDensWS F j P l σ W)) ξ‖ ^ 2
        ≤ D ^ 2 * ‖((stepLaw F.p).iid P).cexpect (fun vt =>
            ZMod.stdAddChar (-(F.roff (j + P) vt * ξ))
            * (if pre (fun i => (vt i).1) P = l ∧ W vt then 1 else 0))‖ ^ 2 := by
    intro ξ hξ
    rw [dft_condDensWS_eq, cond_char_factorWS, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hunif ξ hξ) 2)
      (sq_nonneg _)
  calc ∑ ξ ∈ F.highFreq m (j + P), ‖ZMod.dft (F.densC (j + P) (condDensWS F j P l σ W)) ξ‖ ^ 2
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
        rw [F.tail_factor_l2_eqW]
    _ = D ^ 2 * (F.q : ℝ) ^ (j + P) * ∑ Y, (F.tailDensW j P l W Y) ^ 2 := by ring

/-- **Bound for the oscillation of a piece conditioned on the sum**. -/
theorem condDensWS_osc_le (j P l σ m : ℕ) (W : (Fin P → ℕ × ℕ) → Prop) [DecidablePred W]
    (hmn : m ≤ j + P) (D : ℝ) (hD : 0 ≤ D)
    (hunif : ∀ ξ ∈ F.highFreq m (j + P), ‖headS F j P l σ ξ‖ ≤ D) :
    F.osc m (j + P) hmn (condDensWS F j P l σ W)
      ≤ D * Real.sqrt ((F.q : ℝ) ^ (j + P) * ∑ Y, (F.tailDensW j P l W Y) ^ 2) := by
  calc F.osc m (j + P) hmn (condDensWS F j P l σ W)
      ≤ Real.sqrt (∑ ξ ∈ F.highFreq m (j + P),
          ‖ZMod.dft (F.densC (j + P) (condDensWS F j P l σ W)) ξ‖ ^ 2) :=
        F.osc_le_sqrt_highfreq _ _ _ _
    _ ≤ Real.sqrt (D ^ 2 * ((F.q : ℝ) ^ (j + P) * ∑ Y, (F.tailDensW j P l W Y) ^ 2)) := by
        apply Real.sqrt_le_sqrt
        rw [← mul_assoc]
        exact condDensWS_highfreq_l2_le F j P l σ m W D hunif
    _ = D * Real.sqrt ((F.q : ℝ) ^ (j + P) * ∑ Y, (F.tailDensW j P l W Y) ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hD]

/-! ### The head factor is a characteristic function at level `j` conditioned on the sum -/

/-- **Representation of the head factor**: if `l ≤ σ`, it is `Σ_Y P(𝒮_j = Y, s_j = σ - l) e(-ζ Y/q^j)` (`ζ = p^{-l} (ξ mod q^j)`);
otherwise it is 0. -/
theorem headS_eq (j P l σ : ℕ) (ξ : ZMod (F.q ^ (j + P))) :
    headS F j P l σ ξ = if l ≤ σ then
      ∑ Y : ZMod (F.q ^ j), (jp F j Y (σ - l) : ℂ) * eC (-((((F.p : ZMod (F.q ^ j))⁻¹) ^ l
        * ZMod.castHom (pow_dvd_pow F.q (Nat.le_add_right j P)) (ZMod (F.q ^ j)) ξ).val
          * Y.val : ℚ) / (F.q : ℚ) ^ j) else 0 := by
  set ζ := ((F.p : ZMod (F.q ^ j))⁻¹) ^ l
    * ZMod.castHom (pow_dvd_pow F.q (Nat.le_add_right j P)) (ZMod (F.q ^ j)) ξ with hζ
  have h1 : headS F j P l σ ξ = ((stepLaw F.p).iid j).cexpect (fun vh =>
      ZMod.stdAddChar (-(F.roff j vh * ζ)) * (if pre (fun i => (vh i).1) j + l = σ then 1 else 0)) := by
    unfold headS
    congr 1
    funext vh
    rw [F.head_char_descent l ξ vh]
  rw [h1]
  split_ifs with hl
  · have h2 : (fun vh : Fin j → ℕ × ℕ => ZMod.stdAddChar (-(F.roff j vh * ζ))
          * (if pre (fun i => (vh i).1) j + l = σ then (1 : ℂ) else 0))
        = (fun vh => ZMod.stdAddChar (-(F.roff j vh * ζ))
          * (if pre (fun i => (vh i).1) j = σ - l then (1 : ℂ) else 0)) := by
      funext vh
      congr 1
      exact if_congr (by omega) rfl rfl
    rw [h2, ← Mix.dft_cond_density ((stepLaw F.p).iid j) (F.roff j)
      (fun vh => pre (fun i => (vh i).1) j = σ - l) ζ, ZMod.dft_apply]
    refine Finset.sum_congr rfl (fun Y _ => ?_)
    rw [smul_eq_mul, Mix.stdAddChar_mul_eq_eC, jp_eq_jpR, mul_comm]
    unfold jpR Mix.restrictedDensity
    push_cast
    rfl
  · have h0 : ∀ vh : Fin j → ℕ × ℕ,
        (if pre (fun i => (vh i).1) j + l = σ then (1 : ℂ) else 0) = 0 :=
      fun vh => if_neg (by omega)
    simp only [h0, mul_zero]
    unfold PMF.cexpect
    simp

/-- The norm of `eC` is 1. -/
theorem norm_eC_val {N : ℕ} [NeZero N] (ζ Y : ZMod N) :
    ‖eC (-(ζ.val * Y.val : ℚ) / N)‖ = 1 := by
  rw [← Mix.stdAddChar_mul_eq_eC]; exact Mix.norm_stdAddChar _

/-- **Decay of the head factor** (Proposition 6.7 of the paper and Chernoff). -/
theorem headS_bound (hcf : sumcf_statement F) (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ (j P l σ : ℕ), 2 ≤ j → ∀ ξ : ZMod (F.q ^ (j + P)), ¬ F.q ∣ ξ.val →
      ‖headS F j P l σ ξ‖ ≤ K * (j : ℝ) ^ (-A) := by
  obtain ⟨c, Cc, hc, hCc, htail⟩ := nb_dev_tail F
  set C₃ : ℝ := 2 * A / c + 1 with hC₃def
  have hC₃ : 0 < C₃ := by positivity
  have hC₃1 : 1 ≤ C₃ := by have : 0 ≤ 2 * A / c := by positivity
                           linarith
  have hcC₃e : c * C₃ = 2 * A + c := by rw [hC₃def]; field_simp
  have hcC₃2 : 2 * A ≤ c * C₃ := by rw [hcC₃e]; linarith
  have hcC₃ : A ≤ c * C₃ := by linarith
  obtain ⟨Kcf, hKcf, hcf'⟩ := hcf A C₃ hA hC₃
  refine ⟨Kcf + 2 * Cc, by positivity, fun j P l σ hj ξ hξ => ?_⟩
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have hjA : 0 ≤ (j : ℝ) ^ (-A) := Real.rpow_nonneg hj0.le _
  set ζ := ((F.p : ZMod (F.q ^ j))⁻¹) ^ l
    * ZMod.castHom (pow_dvd_pow F.q (Nat.le_add_right j P)) (ZMod (F.q ^ j)) ξ with hζ
  have hζq : ¬ F.q ∣ ζ.val := F.not_dvd_val_unit_castHom (by omega) l ξ hξ
  rw [headS_eq]
  split_ifs with hl
  · set s' := σ - l with hs'
    set S := ∑ Y : ZMod (F.q ^ j), (jp F j Y s' : ℂ) * eC (-(ζ.val * Y.val : ℚ) / (F.q : ℚ) ^ j)
      with hS
    -- trivial upper bound `‖S‖ ≤ P(s_j = s')`
    have htriv : ‖S‖ ≤ nb F.p j s' := by
      rw [← sum_jp F j s']
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun Y _ => ?_)))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (jp_nonneg F j Y s')]
      have := norm_eC_val (N := F.q ^ j) ζ Y
      push_cast at this
      rw [this, mul_one]
    by_cases hin : |(s' : ℝ) - muP F.p * j| ≤ C₃ * Real.sqrt (j * Real.log j)
    · have h := hcf' j hj s' hin ζ hζq
      calc ‖S‖ ≤ Kcf * (j : ℝ) ^ (-A) * nb F.p j s' := h
        _ ≤ Kcf * (j : ℝ) ^ (-A) * 1 :=
            mul_le_mul_of_nonneg_left (nb_le_one F j s') (by positivity)
        _ ≤ (Kcf + 2 * Cc) * (j : ℝ) ^ (-A) := by nlinarith
    · push Not at hin
      set t : ℝ := |(s' : ℝ) - muP F.p * j| with ht
      have hlogj : 0 ≤ Real.log j := Real.log_nonneg (by linarith)
      have hsq0 : 0 ≤ Real.sqrt (j * Real.log j) := Real.sqrt_nonneg _
      -- `log j ≤ √(j log j)`
      have hlog_le : Real.log j ≤ Real.sqrt (j * Real.log j) := by
        have hlj : Real.log j ≤ j := by
          have := Real.log_le_sub_one_of_pos hj0; linarith
        have h2 : Real.log j ^ 2 ≤ j * Real.log j := by
          calc Real.log j ^ 2 = Real.log j * Real.log j := sq _
            _ ≤ j * Real.log j := mul_le_mul_of_nonneg_right hlj hlogj
        have h := Real.sqrt_le_sqrt h2
        rwa [Real.sqrt_sq hlogj] at h
      -- `j^{-A} = e^{-A log j}`
      have hjpow : (j : ℝ) ^ (-A) = Real.exp (-(A * Real.log j)) := by
        rw [Real.rpow_def_of_pos hj0]; ring_nf
      have hT1 : Real.exp (-(c * ((s' : ℝ) - muP F.p * j) ^ 2 / (j + 1))) ≤ (j : ℝ) ^ (-A) := by
        rw [hjpow]
        apply Real.exp_le_exp.mpr
        have hsq : ((s' : ℝ) - muP F.p * j) ^ 2 = t ^ 2 := (sq_abs _).symm
        rw [hsq]
        have ht2 : C₃ ^ 2 * (j * Real.log j) ≤ t ^ 2 := by
          have := pow_le_pow_left₀ (by positivity) hin.le 2
          rwa [mul_pow, Real.sq_sqrt (by positivity)] at this
        have hj1 : (j : ℝ) + 1 ≤ 2 * j := by linarith
        have key : A * Real.log j ≤ c * t ^ 2 / (j + 1) := by
          rw [le_div_iff₀ (by linarith)]
          have h1 : A * Real.log j * (j + 1) ≤ A * Real.log j * (2 * j) :=
            mul_le_mul_of_nonneg_left hj1 (by positivity)
          have h2 : A * 2 ≤ c * C₃ ^ 2 := by
            have : c * C₃ ≤ c * C₃ ^ 2 := by
              rw [sq]; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hC₃.le hC₃1) hc.le
            linarith
          have h3 : A * Real.log j * (2 * j) ≤ c * C₃ ^ 2 * (j * Real.log j) := by
            have : A * Real.log j * (2 * j) = (A * 2) * (j * Real.log j) := by ring
            rw [this]
            exact mul_le_mul_of_nonneg_right h2 (by positivity)
          have h4 : c * C₃ ^ 2 * (j * Real.log j) ≤ c * t ^ 2 := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ht2 hc.le
          linarith
        linarith
      have hT2 : Real.exp (-(c * t)) ≤ (j : ℝ) ^ (-A) := by
        rw [hjpow]
        apply Real.exp_le_exp.mpr
        have h1 : C₃ * Real.log j ≤ t :=
          (mul_le_mul_of_nonneg_left hlog_le hC₃.le).trans hin.le
        have h2 : A * Real.log j ≤ c * C₃ * Real.log j := mul_le_mul_of_nonneg_right hcC₃ hlogj
        have h3 : c * C₃ * Real.log j ≤ c * t := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1 hc.le
        linarith
      calc ‖S‖ ≤ nb F.p j s' := htriv
        _ ≤ Cc * (Real.exp (-(c * ((s' : ℝ) - muP F.p * j) ^ 2 / (j + 1)))
              + Real.exp (-(c * |(s' : ℝ) - muP F.p * j|))) := htail j s'
        _ ≤ Cc * ((j : ℝ) ^ (-A) + (j : ℝ) ^ (-A)) := by
            gcongr
        _ ≤ (Kcf + 2 * Cc) * (j : ℝ) ^ (-A) := by nlinarith
  · rw [norm_zero]; positivity

end SumMixAAux

end ND

end GGMCollatz
