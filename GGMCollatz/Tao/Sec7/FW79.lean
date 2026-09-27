import GGMCollatz.Tao.Sec7.FW79Chain

/-!
# GGM §7: Lemma 7.9 (many triangles imply many white points) and the Markov bound

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, files `TaoCollatz/Sec7/ManyTriangles.lean`
(`many_triangles_white`) and `TaoCollatz/Sec7/Case3.lean` (`fstar_markov_le`, `encVal_ge_of_reaches`,
`reaches_fewWhite_mass_le`); generalized to the GGM family (p, q, r). Modified.

* `many_triangles_white` (**Lemma 7.9**, (7.57)): when the separation `σ = sep ε` is large (`ε ≤ ε₀`), there is a depth
  gate `g` such that `encExpect ≤ exp(2κ)` for all `0 < κ ≤ 1/100`, `R ≥ 1`, all horizons and all starting points.
  Obtained by feeding the white exit `fpDist_white_exit_deep` (`p₀ = 3/4`, gate `g = Cthr`) into
  `many_triangles_white_core` (`FW79Chain.lean`). After an encounter, the walk until it crosses the barrier is the first passage
  with budget `s = l_Δ - l` (`fpDist s`, bridge `encExpect_block_le`), whose endpoint is white and in the strip with probability `≥ 3/4`.
* `reach_mass_le`: Markov (proved). The probability of `R` encounters with `≤ K` white points is `≤ e^{2κ} e^{K - κR}`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

namespace FW

variable (F : Family)

/-- **Lemma 7.9** (`many_triangles_white` of tao-collatz, (7.57)). -/
theorem many_triangles_white :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ g : ℕ,
      ∀ κ : ℝ, 0 < κ → κ ≤ 1 / 100 →
      ∀ (half : ℕ) (T : F.TriFam half (F.sep ε)) (R : ℕ), 1 ≤ R → ∀ (Tw j' : ℕ) (l' : ℤ),
        encExpect F T R g κ Tw (encInit j' l') ≤ Real.exp (2 * κ) := by
  obtain ⟨ε₀, hε₀, hwe⟩ := F.fpDist_white_exit_deep
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨Cthr, hC⟩ := hwe ε hε hεε₀
  refine ⟨Cthr, fun κ hκ hκ100 half T R hR Tw j' l' => ?_⟩
  refine many_triangles_white_core F T (3 / 4) Cthr
    (fun m hm1 hm2 l hl t ht hmem s hs => hC half T m hm1 hm2 l hl t ht hmem s hs)
    κ hκ ?_ R hR Tw j' l'
  rw [min_eq_left (by norm_num : (3 / 4 : ℝ) ≤ 1)]
  exact le_min hκ100 (by linarith)

/-- Sums of `ofReal` against a PMF and expectations (bounded nonnegative observables). -/
theorem tsum_mul_ofReal_eq {α : Type*} (p : PMF α) (Y : α → ℝ) (h0 : ∀ a, 0 ≤ Y a)
    (B : ℝ) (hB : ∀ a, Y a ≤ B) :
    ∑' a, p a * ENNReal.ofReal (Y a) = ENNReal.ofReal (p.expect Y) := by
  have hne : ∑' a, p a * ENNReal.ofReal (Y a) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal B) ENNReal.ofReal_ne_top ?_
    calc ∑' a, p a * ENNReal.ofReal (Y a) ≤ ∑' a, p a * ENNReal.ofReal B :=
          ENNReal.tsum_le_tsum fun a => mul_le_mul_right (ENNReal.ofReal_le_ofReal (hB a)) _
      _ = ENNReal.ofReal B := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]
  rw [← ENNReal.ofReal_toReal hne, PMF.toReal_tsum_mul_ofReal p Y h0]
  rfl

/-- On the event of reaching, the integrand is large (`encVal_ge_of_reaches` of tao-collatz). -/
theorem encVal_ge_of_reaches {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g K : ℕ) (κ : ℝ)
    (q₀ : ℕ × ℤ) (L : List (ℕ × ℤ))
    (hreach : R ≤ (L.foldl (encStep F T R g) (encInit q₀.1 q₀.2)).count)
    (hwhite : (L.foldl (encStep F T R g) (encInit q₀.1 q₀.2)).cumWhite ≤ K) :
    Real.exp (-(K : ℝ) + κ * R) ≤ encVal κ R (L.foldl (encStep F T R g) (encInit q₀.1 q₀.2)) := by
  set st := L.foldl (encStep F T R g) (encInit q₀.1 q₀.2) with hst
  rw [encVal]
  apply Real.exp_le_exp.mpr
  have hbank : st.banked ≤ st.cumWhite := by
    rw [hst]; exact encFold_banked_le T R g L (encInit q₀.1 q₀.2) (by simp [encInit])
  have hbk : (st.banked : ℝ) ≤ (K : ℝ) := by exact_mod_cast le_trans hbank hwhite
  have hmin : min st.count R = R := min_eq_right hreach
  rw [hmin]
  linarith [hbk]

open Classical in
/-- **Markov** (`reaches_fewWhite_mass_le` of tao-collatz): given `encExpect ≤ e^{2κ}`, the mass of walks with `R` encounters
and `≤ K` white points is `≤ e^{2κ} e^{K - κR}`. -/
theorem reach_mass_le {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g K : ℕ) (κ : ℝ)
    (hκ : 0 ≤ κ) (Tw : ℕ) (q₀ : ℕ × ℤ)
    (hbound : encExpect F T R g κ Tw (encInit q₀.1 q₀.2) ≤ Real.exp (2 * κ)) :
    ∑' v : Fin Tw → ℕ × ℤ, F.hold.iid Tw v *
        ENNReal.ofReal (if R ≤ ((List.ofFn v).foldl (encStep F T R g) (encInit q₀.1 q₀.2)).count
            ∧ ((List.ofFn v).foldl (encStep F T R g) (encInit q₀.1 q₀.2)).cumWhite ≤ K
          then (1 : ℝ) else 0)
      ≤ ENNReal.ofReal (Real.exp (2 * κ) * Real.exp ((K : ℝ) - κ * R)) := by
  set c : ℝ := Real.exp ((K : ℝ) - κ * R) with hc
  have hc0 : 0 < c := Real.exp_pos _
  set X : (Fin Tw → ℕ × ℤ) → ℝ :=
    fun v => encVal κ R ((List.ofFn v).foldl (encStep F T R g) (encInit q₀.1 q₀.2)) with hX
  have hpt : ∀ v : Fin Tw → ℕ × ℤ,
      (if R ≤ ((List.ofFn v).foldl (encStep F T R g) (encInit q₀.1 q₀.2)).count
          ∧ ((List.ofFn v).foldl (encStep F T R g) (encInit q₀.1 q₀.2)).cumWhite ≤ K
        then (1 : ℝ) else 0) ≤ X v * c := by
    intro v
    split_ifs with h
    · have hge := encVal_ge_of_reaches F T R g K κ q₀ (List.ofFn v) h.1 h.2
      have hmul : Real.exp (-(K : ℝ) + κ * R) * c = 1 := by
        rw [hc, ← Real.exp_add]; ring_nf; exact Real.exp_zero
      calc (1 : ℝ) = Real.exp (-(K : ℝ) + κ * R) * c := hmul.symm
        _ ≤ X v * c := mul_le_mul_of_nonneg_right hge hc0.le
    · exact mul_nonneg (encVal_pos κ R _).le hc0.le
  have hXc0 : ∀ v, 0 ≤ X v * c := fun v => mul_nonneg (encVal_pos κ R _).le hc0.le
  have hXcB : ∀ v, X v * c ≤ Real.exp (κ * R) * c :=
    fun v => mul_le_mul_of_nonneg_right (encVal_le κ hκ R _) hc0.le
  refine le_trans (ENNReal.tsum_le_tsum fun v =>
    mul_le_mul_right (ENNReal.ofReal_le_ofReal (hpt v)) _) ?_
  rw [tsum_mul_ofReal_eq (F.hold.iid Tw) _ hXc0 _ hXcB]
  apply ENNReal.ofReal_le_ofReal
  have heq : ((F.hold.iid Tw).expect fun v => X v * c)
      = encExpect F T R g κ Tw (encInit q₀.1 q₀.2) * c := by
    rw [encExpect, PMF.expect, PMF.expect, ← tsum_mul_right]
    exact tsum_congr fun v => by rw [hX]; ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hbound hc0.le

end FW

end Family

end GGMCollatz
