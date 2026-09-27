import GGMCollatz.Tao.Sec7.FWEnc

/-!
# GGM §7: monotonicity of the encounter convolution (a component of Lemma 7.9, part 1)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/ManyTriangles.lean`
(`encExpect_of_count_ge`, `encExpect_anti`, `encExpect_normalize`, `encExpect_normalize_init`,
`encExpect_wander_le`); generalized to the GGM family (p, q, r). Modified.

Instead of `black n ξ` and `coveringTriangle` of tao-collatz, we use membership of the phase point in `T.blk` and
the chosen triangle `covTri` (`covTri_spec`).

* `encExpect_of_count_ge`: states with `count ≥ R` are frozen (the expectation is the integrand itself).
* `encExpect_anti`: the more white points a state has, the smaller its expectation (monotonicity).
* `encExpect_normalize`, `encExpect_normalize_init`: move an intermediate state to the initialized state with the same position and barrier,
  at the cost of a smaller budget (a factor `e^{κc}·max(e^{-k}, e^{-w})`).
* `encExpect_wander_le`: the upper bound `max 1 (e^κ e^{-w₀} Z)` for wandering after an encounter (`count = 0`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

namespace FW

variable (F : Family)

/-- **Saturated states are frozen** (`encExpect_of_count_ge` of tao-collatz). -/
theorem encExpect_of_count_ge {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ) (κ : ℝ)
    (hκ : 0 ≤ κ) (Tw : ℕ) (st : EncState) (hc : R ≤ st.count) :
    encExpect F T R g κ Tw st = encVal κ R st := by
  induction Tw generalizing st with
  | zero => exact encExpect_zero F T R g κ st
  | succ Tw IH =>
    rw [encExpect_succ F T R g κ hκ Tw st]
    have hval : ∀ d : ℕ × ℤ,
        encExpect F T R g κ Tw (encStep F T R g st d) = encVal κ R st := by
      intro d
      rw [IH (encStep F T R g st d) (le_trans hc (encStep_count_le T R g st d))]
      have hmin : min (encStep F T R g st d).count R = min st.count R := by
        have h1 := encStep_count_le T R g st d
        omega
      have hbank : (encStep F T R g st d).banked = st.banked := by
        unfold encStep
        split
        · dsimp only
          rw [if_neg (by omega)]
        · rfl
      rw [encVal, encVal, hbank, hmin]
    rw [tsum_congr fun d => by rw [hval d], tsum_mul_right, F.hold_tsum_toReal, one_mul]

/-- **Monotonicity in the number of white points** (`encExpect_anti` of tao-collatz): among states with equal position, barrier and
number of encounters, the one with more white points has the smaller expectation. -/
theorem encExpect_anti {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ) (κ : ℝ)
    (hκ : 0 ≤ κ) (Tw : ℕ) :
    ∀ st₁ st₂ : EncState, st₁.pos = st₂.pos → st₁.barrier = st₂.barrier →
    st₁.count = st₂.count → st₁.cumWhite ≤ st₂.cumWhite → st₁.banked ≤ st₂.banked →
    encExpect F T R g κ Tw st₂ ≤ encExpect F T R g κ Tw st₁ := by
  classical
  induction Tw with
  | zero =>
    intro st₁ st₂ hpos hbar hcnt hcw hbk
    rw [encExpect_zero, encExpect_zero, encVal, encVal, hcnt]
    apply Real.exp_le_exp.mpr
    have : (st₁.banked : ℝ) ≤ (st₂.banked : ℝ) := Nat.cast_le.mpr hbk
    linarith
  | succ Tw IH =>
    intro st₁ st₂ hpos hbar hcnt hcw hbk
    rw [encExpect_succ F T R g κ hκ Tw st₁, encExpect_succ F T R g κ hκ Tw st₂]
    have hstep : ∀ d : ℕ × ℤ,
        encExpect F T R g κ Tw (encStep F T R g st₂ d)
          ≤ encExpect F T R g κ Tw (encStep F T R g st₁ d) := by
      intro d
      obtain ⟨p₁, b₁, c₁, w₁, k₁⟩ := st₁
      obtain ⟨p₂, b₂, c₂, w₂, k₂⟩ := st₂
      simp only at hpos hbar hcnt hcw hbk
      subst hpos hbar hcnt
      simp only [encStep]
      by_cases hq : 1 ≤ (p₁ + d).1 ∧ (p₁ + d).1 + g ≤ half
          ∧ ((p₁ + d).1 - 1, (p₁ + d).2) ∈ T.blk ∧ b₁ < (p₁ + d).2
      · rw [if_pos hq, if_pos hq]
        refine IH _ _ rfl rfl rfl ?_ ?_
        · dsimp only
          split_ifs <;> omega
        · dsimp only
          split_ifs <;> omega
      · rw [if_neg hq, if_neg hq]
        refine IH _ _ rfl rfl rfl ?_ ?_
        · dsimp only
          split_ifs <;> omega
        · exact hbk
    have hnn : ∀ (st : EncState) (d : ℕ × ℤ),
        0 ≤ (F.hold d).toReal * encExpect F T R g κ Tw (encStep F T R g st d) :=
      fun st d => mul_nonneg ENNReal.toReal_nonneg (encExpect_nonneg F T R g κ Tw _)
    have hbound : ∀ (st : EncState) (d : ℕ × ℤ),
        (F.hold d).toReal * encExpect F T R g κ Tw (encStep F T R g st d)
          ≤ (F.hold d).toReal * Real.exp (κ * R) :=
      fun st d => mul_le_mul_of_nonneg_left (encExpect_le F T R g κ hκ Tw _)
        ENNReal.toReal_nonneg
    have hsumE : Summable (fun d : ℕ × ℤ => (F.hold d).toReal * Real.exp (κ * R)) :=
      (ENNReal.summable_toReal (by rw [F.hold.tsum_coe]; exact ENNReal.one_ne_top)).mul_right _
    have hsum1 : Summable (fun d : ℕ × ℤ =>
        (F.hold d).toReal * encExpect F T R g κ Tw (encStep F T R g st₁ d)) :=
      Summable.of_nonneg_of_le (hnn st₁) (hbound st₁) hsumE
    have hsum2 : Summable (fun d : ℕ × ℤ =>
        (F.hold d).toReal * encExpect F T R g κ Tw (encStep F T R g st₂ d)) :=
      Summable.of_nonneg_of_le (hnn st₂) (hbound st₂) hsumE
    exact Summable.tsum_le_tsum
      (fun d => mul_le_mul_of_nonneg_left (hstep d) ENNReal.toReal_nonneg) hsum2 hsum1

/-- **Monotonicity of state normalization** (`encExpect_normalize` of tao-collatz):
`E_{R'+c}(σ) ≤ e^{κc}·max(e^{-k}, e^{-w})·E_{R'}(τ)`. -/
theorem encExpect_normalize {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R' g : ℕ) (κ : ℝ)
    (hκ : 0 ≤ κ) (c w k : ℕ) (Tw : ℕ) :
    ∀ st τ : EncState, st.pos = τ.pos → st.barrier = τ.barrier →
    st.count = τ.count + c → st.cumWhite = τ.cumWhite + w →
    ((st.banked = k ∧ τ.banked = 0) ∨ st.banked = τ.banked + w) →
    encExpect F T (R' + c) g κ Tw st
      ≤ Real.exp (κ * c) * max (Real.exp (-(k : ℝ))) (Real.exp (-(w : ℝ)))
        * encExpect F T R' g κ Tw τ := by
  classical
  set M : ℝ := max (Real.exp (-(k : ℝ))) (Real.exp (-(w : ℝ))) with hM
  have hM0 : 0 < M := lt_max_of_lt_left (Real.exp_pos _)
  induction Tw with
  | zero =>
    intro st τ hpos hbar hcnt hcw hbk
    rw [encExpect_zero, encExpect_zero, encVal, encVal]
    have hmin : min st.count (R' + c) = min τ.count R' + c := by
      omega
    have hbank : Real.exp (-(st.banked : ℝ)) ≤ M * Real.exp (-(τ.banked : ℝ)) := by
      rcases hbk with ⟨hσk, hτ0⟩ | hoff
      · rw [hσk, hτ0, hM]
        simp only [Nat.cast_zero, neg_zero, Real.exp_zero, mul_one]
        exact le_max_left _ _
      · rw [hoff]
        push_cast
        rw [neg_add, Real.exp_add, mul_comm (Real.exp (-(τ.banked : ℝ)))]
        exact mul_le_mul_of_nonneg_right (hM ▸ le_max_right _ _)
          (Real.exp_pos _).le
    calc Real.exp (-(st.banked : ℝ) + κ * min st.count (R' + c))
        = Real.exp (-(st.banked : ℝ)) * Real.exp (κ * min τ.count R')
            * Real.exp (κ * c) := by
          rw [hmin, ← Real.exp_add, ← Real.exp_add]
          push_cast
          ring_nf
      _ ≤ (M * Real.exp (-(τ.banked : ℝ))) * Real.exp (κ * min τ.count R')
            * Real.exp (κ * c) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbank
            (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = Real.exp (κ * c) * M
            * Real.exp (-(τ.banked : ℝ) + κ * min τ.count R') := by
          rw [Real.exp_add]
          ring
  | succ Tw IH =>
    intro st τ hpos hbar hcnt hcw hbk
    rw [encExpect_succ F T (R' + c) g κ hκ Tw st, encExpect_succ F T R' g κ hκ Tw τ]
    have hstep : ∀ d : ℕ × ℤ,
        encExpect F T (R' + c) g κ Tw (encStep F T (R' + c) g st d)
          ≤ Real.exp (κ * c) * M * encExpect F T R' g κ Tw (encStep F T R' g τ d) := by
      intro d
      obtain ⟨p₁, b₁, c₁, w₁, k₁⟩ := st
      obtain ⟨p₂, b₂, c₂, w₂, k₂⟩ := τ
      simp only at hpos hbar hcnt hcw
      subst hpos hbar hcnt hcw
      simp only [encStep]
      by_cases hq : 1 ≤ (p₁ + d).1 ∧ (p₁ + d).1 + g ≤ half
          ∧ ((p₁ + d).1 - 1, (p₁ + d).2) ∈ T.blk ∧ b₁ < (p₁ + d).2
      · rw [if_pos hq, if_pos hq]
        refine IH _ _ rfl rfl (by dsimp only; omega) (by dsimp only; omega) ?_
        by_cases hcR : c₂ < R'
        · refine Or.inr ?_
          dsimp only
          rw [if_pos (show c₂ + c < R' + c by omega), if_pos hcR]
          omega
        · dsimp only
          rw [if_neg (show ¬ c₂ + c < R' + c by omega), if_neg hcR]
          simpa using hbk
      · rw [if_neg hq, if_neg hq]
        refine IH _ _ rfl rfl (by dsimp only) (by dsimp only; omega) ?_
        dsimp only
        simpa using hbk
    have hnnσ : ∀ d : ℕ × ℤ,
        0 ≤ (F.hold d).toReal * encExpect F T (R' + c) g κ Tw (encStep F T (R' + c) g st d) :=
      fun d => mul_nonneg ENNReal.toReal_nonneg (encExpect_nonneg F T _ _ κ Tw _)
    have hboundσ : ∀ d : ℕ × ℤ,
        (F.hold d).toReal * encExpect F T (R' + c) g κ Tw (encStep F T (R' + c) g st d)
          ≤ (F.hold d).toReal * Real.exp (κ * ((R' + c : ℕ) : ℝ)) :=
      fun d => mul_le_mul_of_nonneg_left (encExpect_le F T (R' + c) g κ hκ Tw _)
        ENNReal.toReal_nonneg
    have hsumH : Summable (fun d : ℕ × ℤ => (F.hold d).toReal) :=
      ENNReal.summable_toReal (by rw [F.hold.tsum_coe]; exact ENNReal.one_ne_top)
    have hsumσ : Summable (fun d : ℕ × ℤ =>
        (F.hold d).toReal * encExpect F T (R' + c) g κ Tw (encStep F T (R' + c) g st d)) :=
      Summable.of_nonneg_of_le hnnσ hboundσ (hsumH.mul_right _)
    have hboundτ : ∀ d : ℕ × ℤ,
        (F.hold d).toReal * encExpect F T R' g κ Tw (encStep F T R' g τ d)
          ≤ (F.hold d).toReal * Real.exp (κ * (R' : ℝ)) :=
      fun d => mul_le_mul_of_nonneg_left (encExpect_le F T R' g κ hκ Tw _)
        ENNReal.toReal_nonneg
    have hsumτ : Summable (fun d : ℕ × ℤ =>
        (F.hold d).toReal * encExpect F T R' g κ Tw (encStep F T R' g τ d)) :=
      Summable.of_nonneg_of_le
        (fun d => mul_nonneg ENNReal.toReal_nonneg (encExpect_nonneg F T _ _ κ Tw _))
        hboundτ (hsumH.mul_right _)
    calc ∑' d : ℕ × ℤ,
          (F.hold d).toReal * encExpect F T (R' + c) g κ Tw (encStep F T (R' + c) g st d)
        ≤ ∑' d : ℕ × ℤ, (F.hold d).toReal
            * (Real.exp (κ * c) * M * encExpect F T R' g κ Tw (encStep F T R' g τ d)) := by
          refine Summable.tsum_le_tsum
            (fun d => mul_le_mul_of_nonneg_left (hstep d) ENNReal.toReal_nonneg)
            hsumσ ?_
          have heq : (fun d : ℕ × ℤ => (F.hold d).toReal
              * (Real.exp (κ * c) * M * encExpect F T R' g κ Tw (encStep F T R' g τ d)))
              = fun d : ℕ × ℤ => Real.exp (κ * c) * M
                * ((F.hold d).toReal * encExpect F T R' g κ Tw (encStep F T R' g τ d)) := by
            funext d
            ring
          rw [heq]
          exact hsumτ.mul_left _
      _ = Real.exp (κ * c) * M
            * ∑' d : ℕ × ℤ, (F.hold d).toReal
              * encExpect F T R' g κ Tw (encStep F T R' g τ d) := by
          rw [← tsum_mul_left]
          exact tsum_congr fun d => by ring

/-- **Normalization to the initialized state** (`encExpect_normalize_init` of tao-collatz). -/
theorem encExpect_normalize_init {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ) (κ : ℝ)
    (hκ : 0 ≤ κ) (Tw : ℕ) (st : EncState) (hc : st.count ≤ R) :
    encExpect F T R g κ Tw st
      ≤ Real.exp (κ * st.count)
        * max (Real.exp (-(st.banked : ℝ))) (Real.exp (-(st.cumWhite : ℝ)))
        * encExpect F T (R - st.count) g κ Tw ⟨st.pos, st.barrier, 0, 0, 0⟩ := by
  have h := encExpect_normalize F T (R - st.count) g κ hκ st.count st.cumWhite st.banked Tw
    st ⟨st.pos, st.barrier, 0, 0, 0⟩ rfl rfl (by dsimp only; omega) (by dsimp only; omega)
    (Or.inl ⟨rfl, rfl⟩)
  rwa [show R - st.count + st.count = R by omega] at h

/-- **Upper bound for wandering** (`encExpect_wander_le` of tao-collatz): given a uniform upper bound `Z` (budget `R'`) for
just-encountered initialized states, a wandering state with a reserve `w ≥ w₀` of white points satisfies
`E_{R'+1} ≤ max 1 (e^κ e^{-w₀} Z)`. -/
theorem encExpect_wander_le {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R' g : ℕ) (κ : ℝ)
    (hκ : 0 ≤ κ) (Z : ℝ)
    (hfresh : ∀ (T' : ℕ) (q : ℕ × ℤ), 1 ≤ q.1 → q.1 + g ≤ half → (q.1 - 1, q.2) ∈ T.blk →
      encExpect F T R' g κ T' ⟨q, (covTri F T (q.1 - 1, q.2)).2.1, 0, 0, 0⟩ ≤ Z)
    (w₀ : ℕ) (Tw : ℕ) :
    ∀ (p : ℕ × ℤ) (b : ℤ) (w : ℕ), w₀ ≤ w →
    encExpect F T (R' + 1) g κ Tw ⟨p, b, 0, w, 0⟩
      ≤ max 1 (Real.exp κ * Real.exp (-(w₀ : ℝ)) * Z) := by
  classical
  induction Tw with
  | zero =>
    intro p b w hw
    rw [encExpect_zero]
    refine le_max_of_le_left ?_
    rw [encVal]
    simp
  | succ Tw IH =>
    intro p b w hw
    rw [encExpect_succ F T (R' + 1) g κ hκ Tw _]
    have hstep : ∀ d : ℕ × ℤ,
        encExpect F T (R' + 1) g κ Tw (encStep F T (R' + 1) g ⟨p, b, 0, w, 0⟩ d)
          ≤ max 1 (Real.exp κ * Real.exp (-(w₀ : ℝ)) * Z) := by
      intro d
      by_cases hq : 1 ≤ (p + d).1 ∧ (p + d).1 + g ≤ half
          ∧ ((p + d).1 - 1, (p + d).2) ∈ T.blk ∧ b < (p + d).2
      · set st' := encStep F T (R' + 1) g ⟨p, b, 0, w, 0⟩ d with hst'
        have hcnt : st'.count = 1 := by
          rw [hst', encStep, if_pos hq]
        have hcw : w₀ ≤ st'.cumWhite := by
          rw [hst', encStep, if_pos hq]
          dsimp only
          omega
        have hbk : st'.banked = st'.cumWhite := by
          rw [hst', encStep, if_pos hq]
          dsimp only
          rw [if_pos (show (0 : ℕ) < R' + 1 by omega)]
        have hnorm := encExpect_normalize_init F T (R' + 1) g κ hκ Tw st'
          (by rw [hcnt]; omega)
        refine le_max_of_le_right (le_trans hnorm ?_)
        rw [hbk, max_self, hcnt]
        have h2 : Real.exp (-(st'.cumWhite : ℝ)) ≤ Real.exp (-(w₀ : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have hle : (w₀ : ℝ) ≤ (st'.cumWhite : ℝ) := Nat.cast_le.mpr hcw
          linarith
        have hpos' : st'.pos = p + d := by
          rw [hst', encStep, if_pos hq]
        have hbar' : st'.barrier = (covTri F T ((p + d).1 - 1, (p + d).2)).2.1 := by
          rw [hst', encStep, if_pos hq]
        have h3 : encExpect F T (R' + 1 - 1) g κ Tw ⟨st'.pos, st'.barrier, 0, 0, 0⟩ ≤ Z := by
          rw [hpos', hbar']
          simpa using hfresh Tw (p + d) hq.1 hq.2.1 hq.2.2.1
        have hE0 : 0 ≤ encExpect F T (R' + 1 - 1) g κ Tw ⟨st'.pos, st'.barrier, 0, 0, 0⟩ :=
          encExpect_nonneg F T _ _ κ Tw _
        have hexp1 : Real.exp (κ * ((1 : ℕ) : ℝ)) = Real.exp κ := by norm_num
        calc Real.exp (κ * ((1 : ℕ) : ℝ)) * Real.exp (-(st'.cumWhite : ℝ))
              * encExpect F T (R' + 1 - 1) g κ Tw ⟨st'.pos, st'.barrier, 0, 0, 0⟩
            ≤ Real.exp (κ * ((1 : ℕ) : ℝ)) * Real.exp (-(w₀ : ℝ)) * Z :=
              mul_le_mul (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) h3 hE0
                (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
          _ = Real.exp κ * Real.exp (-(w₀ : ℝ)) * Z := by rw [hexp1]
      · have hs : encStep F T (R' + 1) g ⟨p, b, 0, w, 0⟩ d
            = ⟨p + d, b, 0, w + (if p + d ∈ whiteStrip half T.W then 1 else 0), 0⟩ := by
          rw [encStep, if_neg hq]
        rw [hs]
        exact IH (p + d) b _ (by omega)
    have hsumH : Summable (fun d : ℕ × ℤ => (F.hold d).toReal) :=
      ENNReal.summable_toReal (by rw [F.hold.tsum_coe]; exact ENNReal.one_ne_top)
    have hsumL : Summable (fun d : ℕ × ℤ => (F.hold d).toReal
        * encExpect F T (R' + 1) g κ Tw (encStep F T (R' + 1) g ⟨p, b, 0, w, 0⟩ d)) :=
      Summable.of_nonneg_of_le
        (fun d => mul_nonneg ENNReal.toReal_nonneg (encExpect_nonneg F T _ _ κ Tw _))
        (fun d => mul_le_mul_of_nonneg_left (encExpect_le F T _ _ κ hκ Tw _)
          ENNReal.toReal_nonneg)
        (hsumH.mul_right _)
    calc ∑' d : ℕ × ℤ, (F.hold d).toReal
          * encExpect F T (R' + 1) g κ Tw (encStep F T (R' + 1) g ⟨p, b, 0, w, 0⟩ d)
        ≤ ∑' d : ℕ × ℤ, (F.hold d).toReal
            * max 1 (Real.exp κ * Real.exp (-(w₀ : ℝ)) * Z) :=
          Summable.tsum_le_tsum
            (fun d => mul_le_mul_of_nonneg_left (hstep d) ENNReal.toReal_nonneg)
            hsumL (hsumH.mul_right _)
      _ = max 1 (Real.exp κ * Real.exp (-(w₀ : ℝ)) * Z) := by
          rw [tsum_mul_right, F.hold_tsum_toReal, one_mul]

end FW

end Family

end GGMCollatz
