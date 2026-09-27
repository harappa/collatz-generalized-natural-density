import GGMCollatz.Tao.Sec7.FW79Block

/-!
# GGM §7: arithmetic of the chain and induction for Lemma 7.9 (a component of Lemma 7.9, part 3)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/ManyTriangles.lean`
(`encChainX`, `encChainX_den_pos`, `one_le_encChainX`, `encChainX_le_exp`, `encChainX_fixed`,
`encExpect_entered_le`, `many_triangles_white_core`); generalized to the GGM family (p, q, r). Modified.

* `encChainX κ p₀ = p₀ / (1 - (1 - p₀) e^κ)`: the value of the chain of immediate re-encounters. `1 ≤ X ≤ e^κ`, and the fixed-point identity.
* `encExpect_entered_le`: from a just-encountered state (the position satisfies the gated encounter condition, and the barrier is
  the top of the family triangle containing it), the expectation is at most `X` (induction on `R`, using the bridge `encExpect_block_le` and the
  hypothesis `hwhite` that the white-exit mass is `≥ p₀`).
* `many_triangles_white_core`: from the white-exit kernel (in the `half - m` form), `encExpect ≤ e^{2κ}`
  (`κ ≤ min(1/100, (2 min(p₀,1) - 1)/2)`; since `κ > 0`, the condition includes `p₀ > 1/2`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

namespace FW

/-- The value of the chain of immediate re-encounters `X = p₀ / (1 - (1 - p₀) e^κ)` (`encChainX` of tao-collatz). -/
noncomputable def encChainX (κ p₀ : ℝ) : ℝ := p₀ / (1 - (1 - p₀) * Real.exp κ)

theorem encChainX_den_pos {κ p₀ : ℝ}
    (hsmall : (1 - p₀) * (Real.exp κ + 1) ≤ 1) :
    0 < 1 - (1 - p₀) * Real.exp κ := by
  nlinarith [Real.exp_pos κ]

theorem one_le_encChainX {κ p₀ : ℝ} (hκ : 0 ≤ κ) (hp1 : p₀ ≤ 1)
    (hsmall : (1 - p₀) * (Real.exp κ + 1) ≤ 1) :
    1 ≤ encChainX κ p₀ := by
  have hden := encChainX_den_pos hsmall
  rw [encChainX, le_div_iff₀ hden]
  nlinarith [Real.one_le_exp hκ]

theorem encChainX_le_exp {κ p₀ : ℝ} (hκ : 0 ≤ κ)
    (hsmall : (1 - p₀) * (Real.exp κ + 1) ≤ 1) :
    encChainX κ p₀ ≤ Real.exp κ := by
  have hden := encChainX_den_pos hsmall
  rw [encChainX, div_le_iff₀ hden]
  nlinarith [Real.one_le_exp hκ, Real.exp_pos κ]

/-- The fixed-point identity `p₀ + (1 - p₀) e^κ X = X`. -/
theorem encChainX_fixed {κ p₀ : ℝ}
    (hsmall : (1 - p₀) * (Real.exp κ + 1) ≤ 1) :
    p₀ + (1 - p₀) * Real.exp κ * encChainX κ p₀ = encChainX κ p₀ := by
  have hden := encChainX_den_pos hsmall
  rw [encChainX]
  field_simp
  ring

variable (F : Family)

/-- **Upper bound at a just-encountered state** (`encExpect_entered_le` of tao-collatz):
`E_R(Tw, ⟨w, l_t, 0, 0, 0⟩) ≤ X` (uniformly in `R`, the horizon and the starting point). -/
theorem encExpect_entered_le {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (g : ℕ) (κ p₀ : ℝ)
    (hκ : 0 ≤ κ) (hp1 : p₀ ≤ 1)
    (hsmall : (1 - p₀) * (Real.exp κ + 1) ≤ 1)
    (hXe1 : Real.exp (κ - 1) * encChainX κ p₀ ≤ 1)
    (hwhite : ∀ w : ℕ × ℤ, 1 ≤ w.1 → w.1 + g ≤ half →
      ∀ t ∈ T.T, (w.1 - 1, w.2) ∈ F.triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - w.2 →
      p₀ ≤ ∑' e : ℕ × ℤ, (F.fpDist s e).toReal
        * Set.indicator (whiteStrip half T.W) 1 (w + e)) :
    ∀ (R Tw : ℕ) (w : ℕ × ℤ), 1 ≤ w.1 → w.1 + g ≤ half →
      ∀ t ∈ T.T, (w.1 - 1, w.2) ∈ F.triangle t.1 t.2.1 t.2.2 →
      encExpect F T R g κ Tw ⟨w, t.2.1, 0, 0, 0⟩ ≤ encChainX κ p₀ := by
  classical
  have hX1 : 1 ≤ encChainX κ p₀ := one_le_encChainX hκ hp1 hsmall
  have hfix := encChainX_fixed hsmall
  have hexpX1 : 1 ≤ Real.exp κ * encChainX κ p₀ := by
    nlinarith [Real.one_le_exp hκ]
  intro R
  induction R with
  | zero =>
    intro Tw w hw1 hwg t ht hmem
    rw [encExpect_of_count_ge F T 0 g κ hκ Tw _ (Nat.zero_le _)]
    calc encVal κ 0 (⟨w, t.2.1, 0, 0, 0⟩ : EncState) = 1 := by simp [encVal]
      _ ≤ encChainX κ p₀ := hX1
  | succ ρ IH =>
    intro Tw w hw1 hwg t ht hmem
    have hfreshIH : ∀ (T' : ℕ) (q : ℕ × ℤ), 1 ≤ q.1 → q.1 + g ≤ half →
        (q.1 - 1, q.2) ∈ T.blk →
        encExpect F T ρ g κ T' ⟨q, (covTri F T (q.1 - 1, q.2)).2.1, 0, 0, 0⟩
          ≤ encChainX κ p₀ :=
      fun T' q h1 h2 hblk =>
        IH T' q h1 h2 _ (covTri_spec F T hblk).1 (covTri_spec F T hblk).2
    have hwt : w.2 ≤ t.2.1 := hmem.2.1
    set s : ℕ := (t.2.1 - w.2).toNat with hsdef
    have hsZ : (s : ℤ) = t.2.1 - w.2 := Int.toNat_of_nonneg (by omega)
    set f : ℕ × ℤ → ℝ := fun e =>
      if w + e ∈ whiteStrip half T.W then 1 else Real.exp κ * encChainX κ p₀ with hfdef
    have hf1' : ∀ e, (1 : ℝ) ≤ f e := by
      intro e
      rw [hfdef]
      dsimp only
      split
      · exact le_refl 1
      · exact hexpX1
    have hf0 : ∀ e, 0 ≤ f e := fun e => le_trans zero_le_one (hf1' e)
    have hfB : ∀ e, f e ≤ Real.exp κ * encChainX κ p₀ := by
      intro e
      rw [hfdef]
      dsimp only
      split
      · exact hexpX1
      · exact le_refl _
    have hstep : ∀ e : ℕ × ℤ, (s : ℤ) < e.2 → ∀ T' : ℕ, T' < Tw →
        encExpect F T (ρ + 1) g κ T'
          (encStep F T (ρ + 1) g ⟨w, t.2.1, 0, 0, 0⟩ e) ≤ f e := by
      intro e he T' hT'
      by_cases hq : 1 ≤ (w + e).1 ∧ (w + e).1 + g ≤ half
          ∧ ((w + e).1 - 1, (w + e).2) ∈ T.blk ∧ t.2.1 < (w + e).2
      · set st'' := encStep F T (ρ + 1) g ⟨w, t.2.1, 0, 0, 0⟩ e with hst''
        have hcnt : st''.count = 1 := by rw [hst'', encStep, if_pos hq]
        have hpos'' : st''.pos = w + e := by rw [hst'', encStep, if_pos hq]
        have hbar'' : st''.barrier = (covTri F T ((w + e).1 - 1, (w + e).2)).2.1 := by
          rw [hst'', encStep, if_pos hq]
        have hnorm := encExpect_normalize_init F T (ρ + 1) g κ hκ T' st''
          (by rw [hcnt]; omega)
        have hcont : encExpect F T (ρ + 1 - 1) g κ T'
            ⟨st''.pos, st''.barrier, 0, 0, 0⟩ ≤ encChainX κ p₀ := by
          rw [hpos'', hbar'']
          simpa using hfreshIH T' (w + e) hq.1 hq.2.1 hq.2.2.1
        by_cases hW : w + e ∈ whiteStrip half T.W
        · have hbk1 : st''.banked = 1 := by
            rw [hst'', encStep, if_pos hq]
            simp [hW]
          have hcw1 : st''.cumWhite = 1 := by
            rw [hst'', encStep, if_pos hq]
            simp [hW]
          rw [hcnt, hbk1, hcw1, max_self] at hnorm
          have hfe : f e = 1 := by rw [hfdef]; simp [hW]
          rw [hfe]
          refine le_trans hnorm (le_trans
            (mul_le_mul_of_nonneg_left hcont (by positivity)) ?_)
          have hee : Real.exp (κ * ((1 : ℕ) : ℝ)) * Real.exp (-((1 : ℕ) : ℝ))
              * encChainX κ p₀ = Real.exp (κ - 1) * encChainX κ p₀ := by
            rw [← Real.exp_add,
              show κ * ((1 : ℕ) : ℝ) + -((1 : ℕ) : ℝ) = κ - 1 by push_cast; ring]
          rw [hee]
          exact hXe1
        · have hbk0 : st''.banked = 0 := by
            rw [hst'', encStep, if_pos hq]
            simp [hW]
          have hcw0 : st''.cumWhite = 0 := by
            rw [hst'', encStep, if_pos hq]
            simp [hW]
          rw [hcnt, hbk0, hcw0, max_self] at hnorm
          have hfe : f e = Real.exp κ * encChainX κ p₀ := by rw [hfdef]; simp [hW]
          rw [hfe]
          refine le_trans hnorm (le_trans
            (mul_le_mul_of_nonneg_left hcont (by positivity)) ?_)
          have hee : Real.exp (κ * ((1 : ℕ) : ℝ)) * Real.exp (-((0 : ℕ) : ℝ))
              * encChainX κ p₀ = Real.exp κ * encChainX κ p₀ := by
            rw [← Real.exp_add]
            norm_num
          rw [hee]
      · by_cases hW : w + e ∈ whiteStrip half T.W
        · have hsx : encStep F T (ρ + 1) g ⟨w, t.2.1, 0, 0, 0⟩ e
              = ⟨w + e, t.2.1, 0, 1, 0⟩ := by
            rw [encStep, if_neg (by exact hq)]
            simp [hW]
          rw [hsx]
          have hwander := encExpect_wander_le F T ρ g κ hκ (encChainX κ p₀)
            hfreshIH 1 T' (w + e) t.2.1 1 (le_refl 1)
          refine le_trans hwander ?_
          have hfe : f e = 1 := by rw [hfdef]; simp [hW]
          rw [hfe]
          refine max_le (le_refl 1) ?_
          have hee : Real.exp κ * Real.exp (-((1 : ℕ) : ℝ)) * encChainX κ p₀
              = Real.exp (κ - 1) * encChainX κ p₀ := by
            rw [← Real.exp_add,
              show κ + -((1 : ℕ) : ℝ) = κ - 1 by push_cast; ring]
          rw [hee]
          exact hXe1
        · have hsx : encStep F T (ρ + 1) g ⟨w, t.2.1, 0, 0, 0⟩ e
              = ⟨w + e, t.2.1, 0, 0, 0⟩ := by
            rw [encStep, if_neg (by exact hq)]
            simp [hW]
          rw [hsx]
          have hwander := encExpect_wander_le F T ρ g κ hκ (encChainX κ p₀)
            hfreshIH 0 T' (w + e) t.2.1 0 (le_refl 0)
          refine le_trans hwander ?_
          have hfe : f e = Real.exp κ * encChainX κ p₀ := by rw [hfdef]; simp [hW]
          rw [hfe]
          refine max_le hexpX1 ?_
          have hee : Real.exp κ * Real.exp (-((0 : ℕ) : ℝ)) * encChainX κ p₀
              = Real.exp κ * encChainX κ p₀ := by
            rw [← Real.exp_add]
            norm_num
          rw [hee]
    have hval1 : encVal κ (ρ + 1) (⟨w, t.2.1, 0, 0, 0⟩ : EncState) = 1 := by
      simp [encVal]
    have hbridge := encExpect_block_le F T (ρ + 1) g κ hκ s ⟨w, t.2.1, 0, 0, 0⟩
      (show (s : ℤ) = t.2.1 - w.2 from hsZ) Tw f hf0
      (Real.exp κ * encChainX κ p₀) hfB (fun e => hval1.trans_le (hf1' e)) hstep
    refine le_trans hbridge ?_
    have hmass : Summable (fun e : ℕ × ℤ => (F.fpDist s e).toReal) :=
      ENNReal.summable_toReal (by rw [(F.fpDist s).tsum_coe]; exact ENNReal.one_ne_top)
    have hWsum : Summable (fun e : ℕ × ℤ =>
        (F.fpDist s e).toReal * Set.indicator (whiteStrip half T.W) 1 (w + e)) := by
      refine Summable.of_nonneg_of_le (fun e => mul_nonneg ENNReal.toReal_nonneg
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) (fun e => ?_) hmass
      refine mul_le_of_le_one_right ENNReal.toReal_nonneg ?_
      by_cases hW : w + e ∈ whiteStrip half T.W
      · simp [Set.indicator_of_mem hW]
      · simp [Set.indicator_of_notMem hW]
    have hfid : (fun e : ℕ × ℤ => (F.fpDist s e).toReal * f e)
        = fun e : ℕ × ℤ =>
          Real.exp κ * encChainX κ p₀ * (F.fpDist s e).toReal
            - (Real.exp κ * encChainX κ p₀ - 1)
              * ((F.fpDist s e).toReal * Set.indicator (whiteStrip half T.W) 1 (w + e)) := by
      funext e
      by_cases hW : w + e ∈ whiteStrip half T.W
      · rw [hfdef]
        simp only [if_pos hW, Set.indicator_of_mem hW, Pi.one_apply]
        ring
      · rw [hfdef]
        simp only [if_neg hW, Set.indicator_of_notMem hW]
        ring
    rw [show ∑' e : ℕ × ℤ, (F.fpDist s e).toReal * f e
        = ∑' e : ℕ × ℤ, (Real.exp κ * encChainX κ p₀ * (F.fpDist s e).toReal
          - (Real.exp κ * encChainX κ p₀ - 1)
            * ((F.fpDist s e).toReal * Set.indicator (whiteStrip half T.W) 1 (w + e)))
      from by rw [hfid],
      Summable.tsum_sub (hmass.mul_left _) (hWsum.mul_left _),
      tsum_mul_left, tsum_mul_left, fpDist_mass_toReal, mul_one]
    have hwm := hwhite w hw1 hwg t ht hmem s hsZ
    nlinarith [hwm, hexpX1, hfix]

/-- **Core of Lemma 7.9** (`many_triangles_white_core` of tao-collatz): from the white-exit kernel
(in the `half - m` form, mass `≥ p₀`, gate `g`), for `κ ≤ min(1/100, (2 min(p₀,1) - 1)/2)`,
`encExpect ≤ e^{2κ}` for all `R ≥ 1`, all horizons and all starting points. -/
theorem many_triangles_white_core {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (p₀ : ℝ) (g : ℕ)
    (hkernel : ∀ m : ℕ, g ≤ m → m ≤ half → ∀ l : ℤ, 1 ≤ half - m →
      ∀ t ∈ T.T, (half - m - 1, l) ∈ F.triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      p₀ ≤ ∑' e : ℕ × ℤ, (F.fpDist s e).toReal
        * Set.indicator (whiteStrip half T.W) 1 (half - m + e.1, l + e.2))
    (κ : ℝ) (hκ : 0 < κ) (hκκ₀ : κ ≤ min (1 / 100) ((2 * min p₀ 1 - 1) / 2))
    (R : ℕ) (hR : 1 ≤ R) (Tw j' : ℕ) (l' : ℤ) :
    encExpect F T R g κ Tw (encInit j' l') ≤ Real.exp (2 * κ) := by
  set p₁ : ℝ := min p₀ 1 with hp₁def
  have hp1 : p₁ ≤ 1 := min_le_right _ _
  have hκp : κ ≤ (2 * p₁ - 1) / 2 := le_trans hκκ₀ (min_le_right _ _)
  have hkey : Real.exp κ * (1 - κ) ≤ 1 := by
    have h := Real.add_one_le_exp (-κ)
    calc Real.exp κ * (1 - κ) = Real.exp κ * (-κ + 1) := by ring
      _ ≤ Real.exp κ * Real.exp (-κ) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos κ).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hκ100 : κ ≤ 1 / 100 := le_trans hκκ₀ (min_le_left _ _)
  have hsmall : (1 - p₁) * (Real.exp κ + 1) ≤ 1 := by
    have h2 : (Real.exp κ + 1) * (1 - κ) ≤ 2 - κ := by nlinarith
    have h3 : (1 - p₁) * (2 - κ) ≤ 1 - κ := by
      have hprod : κ * p₁ ≤ κ * 1 :=
        mul_le_mul_of_nonneg_left hp1 hκ.le
      nlinarith
    have h4 : (1 - p₁) * (Real.exp κ + 1) * (1 - κ) ≤ 1 * (1 - κ) := by
      have := mul_le_mul_of_nonneg_left h2 (show (0:ℝ) ≤ 1 - p₁ by linarith)
      calc (1 - p₁) * (Real.exp κ + 1) * (1 - κ)
          = (1 - p₁) * ((Real.exp κ + 1) * (1 - κ)) := by ring
        _ ≤ (1 - p₁) * (2 - κ) := this
        _ ≤ 1 - κ := h3
        _ = 1 * (1 - κ) := (one_mul _).symm
    exact le_of_mul_le_mul_right h4 (by linarith)
  have hXe : encChainX κ p₁ ≤ Real.exp κ := encChainX_le_exp hκ.le hsmall
  have hXe1 : Real.exp (κ - 1) * encChainX κ p₁ ≤ 1 := by
    calc Real.exp (κ - 1) * encChainX κ p₁
        ≤ Real.exp (κ - 1) * Real.exp κ :=
          mul_le_mul_of_nonneg_left hXe (Real.exp_pos _).le
      _ = Real.exp (κ - 1 + κ) := (Real.exp_add _ _).symm
      _ ≤ 1 := by
          rw [Real.exp_le_one_iff]
          linarith
  have hwhite : ∀ w : ℕ × ℤ, 1 ≤ w.1 → w.1 + g ≤ half →
      ∀ t ∈ T.T, (w.1 - 1, w.2) ∈ F.triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - w.2 →
      p₁ ≤ ∑' e : ℕ × ℤ, (F.fpDist s e).toReal
        * Set.indicator (whiteStrip half T.W) 1 (w + e) := by
    intro w hw1 hwg t ht hmem s hsZ
    have hm : half - (half - w.1) = w.1 := by omega
    have h := hkernel (half - w.1) (by omega) (by omega) w.2 (by omega) t ht
      (by rw [show half - (half - w.1) - 1 = w.1 - 1 from by omega]; exact hmem) s hsZ
    refine le_trans (min_le_left _ _) (h.trans_eq (tsum_congr fun e => ?_))
    rw [hm]
    rfl
  have hY := encExpect_entered_le F T g κ p₁ hκ.le hp1 hsmall hXe1 hwhite
  have hfresh : ∀ (T' : ℕ) (q : ℕ × ℤ), 1 ≤ q.1 → q.1 + g ≤ half →
      (q.1 - 1, q.2) ∈ T.blk →
      encExpect F T (R - 1) g κ T' ⟨q, (covTri F T (q.1 - 1, q.2)).2.1, 0, 0, 0⟩
        ≤ encChainX κ p₁ :=
    fun T' q h1 h2 hblk =>
      hY (R - 1) T' q h1 h2 _ (covTri_spec F T hblk).1 (covTri_spec F T hblk).2
  have hwander := encExpect_wander_le F T (R - 1) g κ hκ.le (encChainX κ p₁)
    hfresh 0 Tw (j', l') l' 0 (le_refl 0)
  rw [show R - 1 + 1 = R from by omega] at hwander
  refine le_trans hwander ?_
  refine max_le (Real.one_le_exp (by positivity)) ?_
  calc Real.exp κ * Real.exp (-((0 : ℕ) : ℝ)) * encChainX κ p₁
      = Real.exp κ * encChainX κ p₁ := by norm_num
    _ ≤ Real.exp κ * Real.exp κ :=
        mul_le_mul_of_nonneg_left hXe (Real.exp_pos _).le
    _ = Real.exp (2 * κ) := by rw [← Real.exp_add]; ring_nf

end FW

end Family

end GGMCollatz
