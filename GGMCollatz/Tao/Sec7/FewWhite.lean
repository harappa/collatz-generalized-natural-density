import GGMCollatz.Tao.Sec7.FWMass

/-!
# GGM §7: expected decay from white points after the passage ((7.55)–(7.67) of tao-collatz, Lemmas 7.9 and 7.10)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, from the statements in `TaoCollatz/Sec7/Case3.lean`
(`damping_expectation_le`, `few_white_mass_le`) and `TaoCollatz/Sec7/ManyTriangles.lean`
(Lemma 7.9 `many_triangles_white`, Lemma 7.10 `triangle_encounter_le`); generalized to the GGM family (p, q, r). Modified.

* `damping_expectation_le`: from the starting point of a black edge of a deep triangle (`m / log² m < s`, `s log p ≤ (m+2) log q²`),
  the number `N_w` of white points in the strip met during the first passage and the following `P` steps satisfies `E exp(-ε³ N_w) ≤ δ`
  (for every `δ > 0` there are `P` and a threshold). Assembled from `few_white_mass_le` in `FWMass.lean` (proved).

Proof: splitting at `K = ⌈log(2/δ)/ε³⌉` gives `exp(-ε³ N_w) ≤ 1_{N_w ≤ K} + δ/2`.
`P(N_w ≤ K)` is small because a walk with few white points either (a) crosses many triangles (Lemma 7.9: each time it leaves a triangle
it reaches a white point with probability `≥ 3/4` (`fpDist_white_exit_deep`), so many triangles crossed means many white points), or (b) meets a large
triangle (Lemma 7.10: sum of the probabilities `≪ e^{-cS}` of meeting a triangle of size `S`, counted via separation); both are small.
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- **Expected decay from white points** (`damping_expectation_le` of tao-collatz, including Lemmas 7.9 and 7.10). -/
theorem damping_expectation_le :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ δ : ℝ, 0 < δ →
      ∃ P Cthr : ℕ, ∀ (half : ℕ) (T : F.TriFam half (F.sep ε)) (m : ℕ), Cthr ≤ m → m ≤ half →
        ∀ l : ℤ, 1 ≤ half - m → ∀ t ∈ T.T, (half - m - 1, l) ∈ F.triangle t.1 t.2.1 t.2.2 →
        ∀ s : ℕ, (s : ℤ) = t.2.1 - l → (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
        (s : ℝ) * Real.log F.p ≤ ((m : ℝ) + 2) * Real.log ((F.q : ℝ) ^ 2) →
        (∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
          ENNReal.ofReal (Real.exp (-(ε ^ 3) * ∑ p ∈ Finset.range P,
            Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
              (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))))
          ≤ ENNReal.ofReal δ := by
  obtain ⟨ε₀, hε₀, hFW⟩ := FW.few_white_mass_le F
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεle δ hδ
  have hε3 : 0 < ε ^ 3 := by positivity
  set K : ℕ := ⌈Real.log (2 / δ) / ε ^ 3⌉₊ with hKdef
  obtain ⟨P, Cthr, hmass⟩ := hFW ε hε hεle K (δ / 2) (by positivity)
  refine ⟨P, Cthr, ?_⟩
  intro half T m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hKε : Real.exp (-(ε ^ 3) * (K : ℝ)) ≤ δ / 2 := by
    have h1 : Real.log (2 / δ) / ε ^ 3 ≤ (K : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hε3] at h1
    have h2 : -(ε ^ 3) * (K : ℝ) ≤ Real.log (δ / 2) := by
      rw [show δ / 2 = (2 / δ)⁻¹ by field_simp, Real.log_inv]
      linarith
    calc Real.exp (-(ε ^ 3) * (K : ℝ)) ≤ Real.exp (Real.log (δ / 2)) := Real.exp_le_exp.mpr h2
      _ = δ / 2 := Real.exp_log (by positivity)
  classical
  have hpt : ∀ (e : ℕ × ℤ) (v : Fin P → ℕ × ℤ),
      ENNReal.ofReal (Real.exp (-(ε ^ 3) * ∑ p ∈ Finset.range P,
          Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
            (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)))
        ≤ ENNReal.ofReal (if (∑ p ∈ Finset.range P,
              Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) ≤ (K : ℝ)
            then (1 : ℝ) else 0) + ENNReal.ofReal (δ / 2) := by
    intro e v
    set Nw : ℝ := ∑ p ∈ Finset.range P,
      Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
        (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) with hNw
    have hNw0 : 0 ≤ Nw := Finset.sum_nonneg fun p _ =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    rw [← ENNReal.ofReal_add (by split_ifs <;> norm_num) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    by_cases hc : Nw ≤ (K : ℝ)
    · rw [if_pos hc]
      have : Real.exp (-(ε ^ 3) * Nw) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith
      linarith
    · rw [if_neg hc, zero_add]
      push Not at hc
      calc Real.exp (-(ε ^ 3) * Nw) ≤ Real.exp (-(ε ^ 3) * (K : ℝ)) :=
            Real.exp_le_exp.mpr (by nlinarith)
        _ ≤ δ / 2 := hKε
  refine le_trans (ENNReal.tsum_le_tsum fun e => mul_le_mul_right
    (ENNReal.tsum_le_tsum fun v => mul_le_mul_right (hpt e v) _) _) ?_
  simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, (F.hold.iid P).tsum_coe, one_mul,
    (F.fpDist s).tsum_coe]
  have hb := hmass half T m hm hmn l hpos t ht hmem s hs hs1 hs2
  calc _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hb le_rfl
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end Family

end GGMCollatz
