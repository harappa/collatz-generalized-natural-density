import GGMCollatz.Tao.Sec7.FWEnc
import GGMCollatz.Tao.Sec7.FW710Aux
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# GGM §7: Lemma 7.10 (meeting a large triangle after a long crossing is rare) and the E∗ sum

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, files `TaoCollatz/Sec7/ManyTriangles.lean`
(`bigTriangleSet`, `triangle_encounter_le_rpow`) and `TaoCollatz/Sec7/Case3.lean`
(`bigTriangle_walk_le_rpow`, `estar_union_le_rpow`); generalized to the GGM family (p, q, r). Modified.

* `bigTriSet T s'`: the union of the family triangles of size `≥ s'` (in phase coordinates).
* `triangle_encounter_le` (**Lemma 7.10**, (7.60)): from a point `(j,l)` of a triangle `t₀` (budget `s = l_Δ - l`,
  `(half - j)^{0.8} < s`), the probability that the endpoint of the first passage followed by `p` steps lies in a triangle of size `≥ s'` (`1 ≤ s' ≤ (half-j)^{0.4}`)
  is `≤ C A²(1+p)/s' + C e^{-cA²(1+p)}` (`A ≥ A₀`). Proved (given the black boxes
  `fpDist_col_le`, `fpDistPlus_height_tail`, `fpDistPlus_col_tail`).
  Proof: let `H = A²(1+p)`, `D = s·min(gap, ρ)/4` (`gap = log p / log q² - ρ > 0`, `ρ = (p-1)/(2p)`).
  If `s' < K₀H`, the left-hand side is `≤ 1` and the claim is trivial. Otherwise, outside the height tail (`x₂ ≥ s + H`) and the column tail (`|x₁ - sρ| ≥ 2D`),
  we have `x₁ log q² ≤ s log p` and `x₁ ≥ ⌈H⌉`; the apex column of a triangle met lies within `⌈H⌉` before `j + x₁`
  (`T710.proximity`), and the set of these apex columns is `⌊s'/(4 log q²)⌋ + 1`-separated (`T710.apex_sep`). The probability of a separated set
  is `≤ K(1/√(1+s) + 1/d)` by summing the Gaussian envelope of Lemma 7.7 (`T710.sparse_shift_le`). Since `s'² < s` (from the rpow hypothesis),
  `1/√(1+s) ≤ 1/s'`. The rpow bookkeeping of tao-collatz is not used; the width of the column tail is taken from the slope gap `gap` alone.
* `estar_union_le`: with `s' = ⌊4^A(1+p)³⌋` (`A` taken to be a natural number), the sum over `p ≤ Tw` can be made arbitrarily small
  by taking `A` large. Proved (from the lemma above).
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

namespace FW

variable (F : Family)

/-- The union of the family triangles of size `≥ s'` (`bigTriangleSet` of tao-collatz). -/
def bigTriSet {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (s' : ℕ) : Set (ℕ × ℤ) :=
  {x | ∃ t ∈ T.T, (s' : ℝ) ≤ t.2.2 ∧ x ∈ F.triangle t.1 t.2.1 t.2.2}

/-- **Lemma 7.10** (`triangle_encounter_le_rpow` of tao-collatz, (7.60)). Proved given the black boxes (the column envelope of Lemma 7.7,
the height and column tails of `fpDistPlus`). -/
theorem triangle_encounter_le :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      ∀ (half : ℕ) (T : F.TriFam half (F.sep ε)), ∀ t₀ ∈ T.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ F.triangle t₀.1 t₀.2.1 t₀.2.2 → ∀ s : ℕ, (s : ℤ) = t₀.2.1 - l →
        ((half - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) →
      ∀ (p s' : ℕ), 1 ≤ s' → (s' : ℝ) ≤ ((half - j : ℕ) : ℝ) ^ (0.4 : ℝ) →
        ∑' x : ℕ × ℤ, F.fpDistPlus s p x
            * Set.indicator (bigTriSet F T s') (1 : ℕ × ℤ → ℝ≥0∞) ((j, l) + x)
          ≤ ENNReal.ofReal (C * A ^ 2 * (1 + (p : ℝ)) / (s' : ℝ)
              + C * Real.exp (-c * A ^ 2 * (1 + (p : ℝ)))) := by
  obtain ⟨ch, hch, Ch, hCh, Kh, hKh, hht⟩ := F.fpDistPlus_height_tail
  obtain ⟨cc, hcc, Cc, hCc, Kc, hKc, hct⟩ := F.fpDistPlus_col_tail
  obtain ⟨Ks, hKs, hsp⟩ := T710.sparse_shift_le F
  have hLq : 0 < Real.log ((F.q : ℝ) ^ 2) := Family.WE.log_q_sq_pos F
  have hLp : 0 < Real.log (F.p : ℝ) := Family.WE.log_p_pos F
  have hp2 : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hq2 : (2 : ℝ) ≤ F.q := by exact_mod_cast F.two_le_q
  have hρ4 : 1 / 4 ≤ F.slopeInv := by
    rw [Family.slopeInv, le_div_iff₀ (by positivity)]; linarith
  -- the slope gap `gap = Lp/Lq - ρ > 0` and `g = min(gap, ρ)`
  obtain ⟨gap, hgap⟩ : ∃ gap : ℝ,
      gap = Real.log (F.p : ℝ) / Real.log ((F.q : ℝ) ^ 2) - F.slopeInv := ⟨_, rfl⟩
  have hgap0 : 0 < gap := by rw [hgap]; linarith [Family.WE.slope_gap F]
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = min gap F.slopeInv := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; exact lt_min hgap0 (by linarith)
  have hg_gap : g ≤ gap := by rw [hg]; exact min_le_left _ _
  have hg_ρ : g ≤ F.slopeInv := by rw [hg]; exact min_le_right _ _
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = cc * min (g ^ 2 / 32) (g / 4) := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := by rw [hc₁]; exact mul_pos hcc (lt_min (by positivity) (by positivity))
  -- constants
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = max (max (4 * Real.log ((F.q : ℝ) ^ 2))
      (8 * Real.log (F.p : ℝ))) (max 16 (4 * Kc / g)) := ⟨_, rfl⟩
  have hK₀q : 4 * Real.log ((F.q : ℝ) ^ 2) ≤ K₀ := by
    rw [hK₀]; exact le_max_of_le_left (le_max_left _ _)
  have hK₀p : 8 * Real.log (F.p : ℝ) ≤ K₀ := by
    rw [hK₀]; exact le_max_of_le_left (le_max_right _ _)
  have hK₀16 : 16 ≤ K₀ := by rw [hK₀]; exact le_max_of_le_right (le_max_left _ _)
  have hK₀c : 4 * Kc / g ≤ K₀ := by rw [hK₀]; exact le_max_of_le_right (le_max_right _ _)
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ,
      Cm = 2 * Cc / c₁ + 2 * Ks * (1 + 4 * Real.log ((F.q : ℝ) ^ 2)) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max (max Ch Cm) K₀ := ⟨_, rfl⟩
  have hCCh : Ch ≤ C := by rw [hC]; exact le_max_of_le_left (le_max_left _ _)
  have hCCm : Cm ≤ C := by rw [hC]; exact le_max_of_le_left (le_max_right _ _)
  have hCK₀ : K₀ ≤ C := by rw [hC]; exact le_max_right _ _
  have hC0 : 0 < C := by linarith
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro ε hε hεle
  have hσ : 0 < F.sep ε := by
    unfold Family.sep Family.sepc
    have h1 : 0 < Real.log ((F.p : ℝ) * (F.q : ℝ) ^ 2) := Real.log_pos (by nlinarith)
    have h2 : 0 < Real.log (1 / ε) := Real.log_pos (by rw [lt_div_iff₀ hε]; linarith)
    exact mul_pos (div_pos one_pos (by linarith)) h2
  refine ⟨C, hC0, ch, hch, max 1 Kh, le_max_left _ _, ?_⟩
  intro A hA half T t₀ ht₀ j l hmem s hs hdeep p s' hs'1 hs'M
  have hA1 : 1 ≤ A := le_trans (le_max_left _ _) hA
  have hAKh : Kh ≤ A := le_trans (le_max_right _ _) hA
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ, H = A ^ 2 * (1 + (p : ℝ)) := ⟨_, rfl⟩
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hA2 : 1 ≤ A ^ 2 := one_le_pow₀ hA1
  have hAA : A ≤ A ^ 2 := le_self_pow₀ hA1 (by norm_num)
  have hH1 : 1 + (p : ℝ) ≤ H := by
    rw [hHdef]; exact le_mul_of_one_le_left (by linarith) hA2
  have hH1' : 1 ≤ H := by linarith
  have hHKh : Kh * (1 + (p : ℝ)) ≤ H := by
    rw [hHdef]
    have : Kh ≤ A ^ 2 := le_trans hAKh hAA
    exact mul_le_mul_of_nonneg_right this (by linarith)
  have hs'1R : (1 : ℝ) ≤ s' := by exact_mod_cast hs'1
  have hs'pos : (0 : ℝ) < s' := by linarith
  have hgoal : C * A ^ 2 * (1 + (p : ℝ)) / (s' : ℝ) + C * Real.exp (-ch * A ^ 2 * (1 + (p : ℝ)))
      = C * (H / s') + C * Real.exp (-ch * H) := by
    rw [hHdef]; ring_nf
  rw [hgoal]
  by_cases hbig : (s' : ℝ) < K₀ * H
  · -- trivial case: the left-hand side is `≤ 1`
    have hle1 : ∑' x : ℕ × ℤ, F.fpDistPlus s p x
        * Set.indicator (bigTriSet F T s') (1 : ℕ × ℤ → ℝ≥0∞) ((j, l) + x) ≤ 1 := by
      calc _ ≤ ∑' x : ℕ × ℤ, F.fpDistPlus s p x := ENNReal.tsum_le_tsum fun x => by
            by_cases h : (j, l) + x ∈ bigTriSet F T s'
            · rw [Set.indicator_of_mem h, Pi.one_apply, mul_one]
            · rw [Set.indicator_of_notMem h, mul_zero]; exact zero_le
        _ = 1 := (F.fpDistPlus s p).tsum_coe
    refine hle1.trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hu0 : 0 ≤ H / s' := div_nonneg (by linarith) hs'pos.le
    have h1 : 1 < K₀ * (H / s') := by
      rw [← mul_div_assoc, lt_div_iff₀ hs'pos]; linarith
    have h2 : K₀ * (H / s') ≤ C * (H / s') := mul_le_mul_of_nonneg_right hCK₀ hu0
    have h3 : 0 ≤ C * Real.exp (-ch * H) := mul_nonneg hC0.le (Real.exp_pos _).le
    linarith
  have hbig' : K₀ * H ≤ s' := not_lt.mp hbig
  -- `s'² < s` (from `(half - j)^{0.8} < s` and `s' ≤ (half - j)^{0.4}`)
  have hM0 : (0 : ℝ) ≤ ((half - j : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsq : (s' : ℝ) ^ 2 < s := by
    have h1 : (s' : ℝ) ^ 2 ≤ (((half - j : ℕ) : ℝ) ^ (0.4 : ℝ)) ^ 2 := by
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hs'M 2
    have h2 : (((half - j : ℕ) : ℝ) ^ (0.4 : ℝ)) ^ 2 = ((half - j : ℕ) : ℝ) ^ (0.8 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hM0]; norm_num
    linarith
  have hs's : (s' : ℝ) ≤ s := by
    have := le_self_pow₀ hs'1R (show (2 : ℕ) ≠ 0 by norm_num)
    linarith
  have hs1 : (1 : ℝ) ≤ s := by linarith
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hs16 : 16 * H ≤ s := by
    have := mul_le_mul_of_nonneg_right hK₀16 (by linarith : (0 : ℝ) ≤ H)
    linarith
  -- column width `W₀ = ⌈H⌉`
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : ℕ, W₀ = ⌈H⌉₊ := ⟨_, rfl⟩
  have hHW : H ≤ W₀ := by rw [hW₀]; exact Nat.le_ceil H
  have hW₀H : (W₀ : ℝ) < H + 1 := by rw [hW₀]; exact Nat.ceil_lt_add_one (by linarith)
  have hW₀2 : (W₀ : ℝ) ≤ 2 * H := by linarith
  have hR1 : 2 * (W₀ : ℝ) * Real.log ((F.q : ℝ) ^ 2) ≤ s' := by
    have h1 := mul_le_mul_of_nonneg_right hK₀q (by linarith : (0 : ℝ) ≤ H)
    have h2 := mul_le_mul_of_nonneg_right hW₀2 hLq.le
    linarith
  have hR2 : 4 * (H + 1) * Real.log F.p ≤ s' := by
    have h1 := mul_le_mul_of_nonneg_right hK₀p (by linarith : (0 : ℝ) ≤ H)
    have h2 : (H + 1) * Real.log F.p ≤ 2 * H * Real.log F.p :=
      mul_le_mul_of_nonneg_right (by linarith) hLp.le
    linarith
  -- width of the column tail `D = s g / 4`
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = s * g / 4 := ⟨_, rfl⟩
  have hDK : Kc * (1 + (p : ℝ)) ≤ D := by
    have h1 := mul_le_mul_of_nonneg_right hK₀c (by linarith : (0 : ℝ) ≤ H)
    have h2 : Kc * (1 + (p : ℝ)) ≤ Kc * H := mul_le_mul_of_nonneg_left hH1 hKc.le
    have h4 : 4 * Kc / g * H ≤ s := by linarith
    have h5 : 4 * Kc / g * H * g ≤ s * g := mul_le_mul_of_nonneg_right h4 hg0.le
    have h3 : 4 * Kc / g * H * g = 4 * Kc * H := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hg0.ne']
    rw [hDdef]; linarith
  -- the set of apex columns of the large triangles that can be met, and its separation
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = ⌊(s' : ℝ) / (4 * Real.log ((F.q : ℝ) ^ 2))⌋₊ + 1 := ⟨_, rfl⟩
  have hd1 : 1 ≤ d := by rw [hd]; omega
  obtain ⟨Apex, hApex⟩ : ∃ Apex : Set ℕ, Apex = {a | ∃ t' ∈ T.T, (s' : ℝ) ≤ t'.2.2 ∧ t'.1 = a ∧
      ∃ X : ℕ × ℤ, (s : ℤ) < X.2 ∧ (X.2 : ℝ) < s + H ∧
        (X.1 : ℝ) * Real.log ((F.q : ℝ) ^ 2) ≤ (s : ℝ) * Real.log F.p ∧ W₀ ≤ X.1 ∧
        ((j + X.1, l + X.2) : ℕ × ℤ) ∈ F.triangle t'.1 t'.2.1 t'.2.2} := ⟨_, rfl⟩
  have hsep : ∀ a ∈ Apex, ∀ b ∈ Apex, a < b → a + d ≤ b := by
    intro a ha b hb hab
    rw [hApex] at ha hb
    obtain ⟨t', ht', hs', rfl, X', h1', h2', h3', h4', h5'⟩ := ha
    obtain ⟨t'', ht'', hs'', rfl, X'', h1'', h2'', h3'', h4'', h5''⟩ := hb
    have P' := T710.proximity F T hσ ht₀ hmem hs hHW h1' h2' h3' h4' ht' h5'
    have P'' := T710.proximity F T hσ ht₀ hmem hs hHW h1'' h2'' h3'' h4'' ht'' h5''
    have hne : t' ≠ t'' := fun h => by rw [h] at hab; exact lt_irrefl _ hab
    have := T710.apex_sep F T hσ ht' ht'' hne hs' hs'' P'.2.2.1 P'.2.2.2 P''.2.2.1 P''.2.2.2
      hR1 hR2 hab.le
    rw [hd]; omega
  -- pointwise bound: height tail, column tail, near an apex column
  have hpt : ∀ x : ℕ × ℤ,
      F.fpDistPlus s p x * Set.indicator (bigTriSet F T s') (1 : ℕ × ℤ → ℝ≥0∞) ((j, l) + x)
        ≤ F.fpDistPlus s p x
            * Set.indicator {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} (1 : ℕ × ℤ → ℝ≥0∞) x
          + F.fpDistPlus s p x
              * Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) * F.slopeInv|}
                (1 : ℕ × ℤ → ℝ≥0∞) x
          + ∑ r ∈ Finset.range W₀, F.fpDistPlus s p x
              * Set.indicator {y : ℕ × ℤ | r ≤ j + y.1 ∧ j + y.1 - r ∈ Apex}
                (1 : ℕ × ℤ → ℝ≥0∞) x := by
    intro x
    by_cases hμ : F.fpDistPlus s p x = 0
    · rw [hμ, zero_mul]; exact zero_le
    have hx2 : (s : ℤ) < x.2 := T710.fpDistPlus_support_snd_gt F s p x hμ
    by_cases hB : (j, l) + x ∈ bigTriSet F T s'
    swap
    · rw [Set.indicator_of_notMem hB, mul_zero]; exact zero_le
    rw [Set.indicator_of_mem hB, Pi.one_apply, mul_one]
    by_cases hHt : (s : ℝ) + H ≤ (x.2 : ℝ)
    · have e : F.fpDistPlus s p x
            * Set.indicator {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} (1 : ℕ × ℤ → ℝ≥0∞) x
          = F.fpDistPlus s p x := by
        rw [Set.indicator_of_mem (show x ∈ {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} from hHt),
          Pi.one_apply, mul_one]
      rw [e]; exact le_add_right (le_add_right le_rfl)
    by_cases hCt : 2 * D ≤ |(x.1 : ℝ) - (s : ℝ) * F.slopeInv|
    · have e : F.fpDistPlus s p x
            * Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) * F.slopeInv|}
              (1 : ℕ × ℤ → ℝ≥0∞) x
          = F.fpDistPlus s p x := by
        rw [Set.indicator_of_mem (show x ∈ {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) * F.slopeInv|}
          from hCt), Pi.one_apply, mul_one]
      rw [e]; exact le_add_right (le_add_left le_rfl)
    have hX2hi : (x.2 : ℝ) < s + H := not_le.mp hHt
    have hX1 := abs_lt.mp (not_le.mp hCt)
    rw [hDdef] at hX1
    have hX1col : (x.1 : ℝ) * Real.log ((F.q : ℝ) ^ 2) ≤ (s : ℝ) * Real.log F.p := by
      have e1 : (s : ℝ) * Real.log F.p / Real.log ((F.q : ℝ) ^ 2) = s * F.slopeInv + s * gap := by
        rw [hgap, mul_div_assoc]; ring
      have e2 : (s : ℝ) * g ≤ s * gap := mul_le_mul_of_nonneg_left hg_gap hs0
      have e3 : 0 ≤ (s : ℝ) * gap := mul_nonneg hs0 hgap0.le
      rw [← le_div_iff₀ hLq, e1]
      linarith [hX1.2]
    have hX1W : W₀ ≤ x.1 := by
      have e1 : (s : ℝ) * g ≤ s * F.slopeInv := mul_le_mul_of_nonneg_left hg_ρ hs0
      have e2 : (s : ℝ) * (1 / 4) ≤ s * F.slopeInv := mul_le_mul_of_nonneg_left hρ4 hs0
      have : (W₀ : ℝ) < x.1 := by linarith [hX1.1]
      exact_mod_cast this.le
    obtain ⟨t', ht', hsize, hx⟩ := hB
    have P := T710.proximity F T hσ ht₀ hmem hs hHW hx2 hX2hi hX1col hX1W ht' hx
    obtain ⟨r, hr⟩ : ∃ r : ℕ, r = j + x.1 - t'.1 := ⟨_, rfl⟩
    have hrW : r ∈ Finset.range W₀ := Finset.mem_range.mpr (by omega)
    have hxr : x ∈ {y : ℕ × ℤ | r ≤ j + y.1 ∧ j + y.1 - r ∈ Apex} := by
      show r ≤ j + x.1 ∧ j + x.1 - r ∈ Apex
      refine ⟨by omega, ?_⟩
      rw [show j + x.1 - r = t'.1 by omega, hApex]
      exact ⟨t', ht', hsize, rfl, x, hx2, hX2hi, hX1col, hX1W, hx⟩
    calc F.fpDistPlus s p x
        = F.fpDistPlus s p x * Set.indicator {y : ℕ × ℤ | r ≤ j + y.1 ∧ j + y.1 - r ∈ Apex}
            (1 : ℕ × ℤ → ℝ≥0∞) x := by
          rw [Set.indicator_of_mem hxr, Pi.one_apply, mul_one]
      _ ≤ ∑ r ∈ Finset.range W₀, F.fpDistPlus s p x
            * Set.indicator {y : ℕ × ℤ | r ≤ j + y.1 ∧ j + y.1 - r ∈ Apex}
              (1 : ℕ × ℤ → ℝ≥0∞) x :=
          Finset.single_le_sum (f := fun r => F.fpDistPlus s p x
            * Set.indicator {y : ℕ × ℤ | r ≤ j + y.1 ∧ j + y.1 - r ∈ Apex}
              (1 : ℕ × ℤ → ℝ≥0∞) x) (fun _ _ => zero_le) hrW
      _ ≤ _ := le_add_left le_rfl
  -- bounds for the three sums
  have hS1 : ∑' x, F.fpDistPlus s p x
      * Set.indicator {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} (1 : ℕ × ℤ → ℝ≥0∞) x
        ≤ ENNReal.ofReal (Ch * Real.exp (-ch * H)) := by
    rw [T710.tsum_mul_indicator_eq]; exact ENNReal.ofReal_le_ofReal (hht s p H hHKh)
  have hS2 : ∑' x, F.fpDistPlus s p x
      * Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) * F.slopeInv|}
        (1 : ℕ × ℤ → ℝ≥0∞) x
        ≤ ENNReal.ofReal (Cc * (Real.exp (-cc * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-cc * D))) := by
    rw [T710.tsum_mul_indicator_eq]; exact ENNReal.ofReal_le_ofReal (hct s p D hDK)
  -- real bounds
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = 1 / (s' : ℝ) := ⟨_, rfl⟩
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hHv : H / s' = H * v := by rw [hv, mul_one_div]
  have hexp : Real.exp (-(c₁ * s)) ≤ 1 / c₁ * v := by
    have h1 : Real.exp (-(c₁ * s)) ≤ 1 / (c₁ * s) := by
      rw [Real.exp_neg, ← one_div]
      apply one_div_le_one_div_of_le (mul_pos hc₁0 (by linarith))
      linarith [Real.add_one_le_exp (c₁ * s)]
    have h2 : 1 / (c₁ * (s : ℝ)) = 1 / c₁ * (1 / s) := by rw [div_mul_div_comm, one_mul]
    have h3 : 1 / (s : ℝ) ≤ v := by rw [hv]; exact one_div_le_one_div_of_le hs'pos hs's
    have h4 : 1 / c₁ * (1 / (s : ℝ)) ≤ 1 / c₁ * v :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have hmin1 := min_le_left (g ^ 2 / 32) (g / 4)
  have hmin2 := min_le_right (g ^ 2 / 32) (g / 4)
  have he1 : Real.exp (-cc * D ^ 2 / (1 + (s : ℝ))) ≤ Real.exp (-(c₁ * s)) := by
    apply Real.exp_le_exp.mpr
    have h1 : (s : ℝ) * g ^ 2 / 32 ≤ D ^ 2 / (1 + s) := by
      rw [le_div_iff₀ (by linarith), hDdef]
      have key : 0 ≤ (s : ℝ) * g ^ 2 * (s - 1) / 32 :=
        div_nonneg (mul_nonneg (mul_nonneg hs0 (sq_nonneg g)) (sub_nonneg.mpr hs1)) (by norm_num)
      have e : ((s : ℝ) * g / 4) ^ 2 - (s : ℝ) * g ^ 2 / 32 * (1 + s)
          = (s : ℝ) * g ^ 2 * (s - 1) / 32 := by ring
      linarith
    have h2 : min (g ^ 2 / 32) (g / 4) * s ≤ g ^ 2 / 32 * s := mul_le_mul_of_nonneg_right hmin1 hs0
    have h3 : cc * (min (g ^ 2 / 32) (g / 4) * s) ≤ cc * (g ^ 2 / 32 * s) :=
      mul_le_mul_of_nonneg_left h2 hcc.le
    have h4 : cc * ((s : ℝ) * g ^ 2 / 32) ≤ cc * (D ^ 2 / (1 + s)) :=
      mul_le_mul_of_nonneg_left h1 hcc.le
    have h5 : -cc * D ^ 2 / (1 + (s : ℝ)) = -(cc * (D ^ 2 / (1 + s))) := by ring
    rw [h5, hc₁]; linarith
  have he2 : Real.exp (-cc * D) ≤ Real.exp (-(c₁ * s)) := by
    apply Real.exp_le_exp.mpr
    have h2 : min (g ^ 2 / 32) (g / 4) * s ≤ g / 4 * s := mul_le_mul_of_nonneg_right hmin2 hs0
    have h3 : cc * (min (g ^ 2 / 32) (g / 4) * s) ≤ cc * (g / 4 * s) :=
      mul_le_mul_of_nonneg_left h2 hcc.le
    rw [hc₁, hDdef]; linarith
  have hP2 : Cc * (Real.exp (-cc * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-cc * D))
      ≤ 2 * Cc / c₁ * (H * v) := by
    have h1 : Cc * (Real.exp (-cc * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-cc * D))
        ≤ Cc * (2 * (1 / c₁ * v)) := mul_le_mul_of_nonneg_left (by linarith) hCc.le
    have h2 : 1 / c₁ * v ≤ 1 / c₁ * (H * v) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hv0 hH1') (by positivity)
    have h2' : Cc * (2 * (1 / c₁ * v)) ≤ Cc * (2 * (1 / c₁ * (H * v))) :=
      mul_le_mul_of_nonneg_left (by linarith) hCc.le
    have h3 : Cc * (2 * (1 / c₁ * (H * v))) = 2 * Cc / c₁ * (H * v) := by ring
    linarith
  have hsq1 : 1 / Real.sqrt (1 + s) ≤ v := by
    rw [hv]
    apply one_div_le_one_div_of_le hs'pos
    calc (s' : ℝ) = Real.sqrt ((s' : ℝ) ^ 2) := (Real.sqrt_sq hs'pos.le).symm
      _ ≤ Real.sqrt (1 + s) := Real.sqrt_le_sqrt (by linarith)
  have hdv : 1 / (d : ℝ) ≤ 4 * Real.log ((F.q : ℝ) ^ 2) * v := by
    have h1 : (s' : ℝ) / (4 * Real.log ((F.q : ℝ) ^ 2)) < d := by
      rw [hd]; push_cast; exact Nat.lt_floor_add_one _
    have h2 : 0 < (s' : ℝ) / (4 * Real.log ((F.q : ℝ) ^ 2)) := by positivity
    calc 1 / (d : ℝ) ≤ 1 / ((s' : ℝ) / (4 * Real.log ((F.q : ℝ) ^ 2))) :=
          one_div_le_one_div_of_le h2 h1.le
      _ = 4 * Real.log ((F.q : ℝ) ^ 2) * v := by rw [one_div_div, hv, mul_one_div]
  have hP3 : (W₀ : ℝ) * (Ks * (1 / Real.sqrt (1 + s) + 1 / d))
      ≤ 2 * Ks * (1 + 4 * Real.log ((F.q : ℝ) ^ 2)) * (H * v) := by
    have h1 : Ks * (1 / Real.sqrt (1 + s) + 1 / d)
        ≤ Ks * ((1 + 4 * Real.log ((F.q : ℝ) ^ 2)) * v) :=
      mul_le_mul_of_nonneg_left (by linarith) hKs.le
    have h2 : 0 ≤ Ks * (1 / Real.sqrt (1 + s) + 1 / d) :=
      mul_nonneg hKs.le (add_nonneg (by positivity) (by positivity))
    calc (W₀ : ℝ) * (Ks * (1 / Real.sqrt (1 + s) + 1 / d))
        ≤ (2 * H) * (Ks * ((1 + 4 * Real.log ((F.q : ℝ) ^ 2)) * v)) :=
          mul_le_mul hW₀2 h1 h2 (by linarith)
      _ = 2 * Ks * (1 + 4 * Real.log ((F.q : ℝ) ^ 2)) * (H * v) := by ring
  have hP1 : Ch * Real.exp (-ch * H) ≤ C * Real.exp (-ch * H) :=
    mul_le_mul_of_nonneg_right hCCh (Real.exp_pos _).le
  have hCm' : (2 * Cc / c₁ + 2 * Ks * (1 + 4 * Real.log ((F.q : ℝ) ^ 2))) * (H * v)
      ≤ C * (H * v) :=
    mul_le_mul_of_nonneg_right (by rw [← hCm]; exact hCCm) (mul_nonneg (by linarith) hv0)
  have hreal : Ch * Real.exp (-ch * H)
      + Cc * (Real.exp (-cc * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-cc * D))
      + (W₀ : ℝ) * (Ks * (1 / Real.sqrt (1 + s) + 1 / d))
      ≤ C * (H / s') + C * Real.exp (-ch * H) := by
    rw [hHv]; linarith
  -- assembly
  calc ∑' x : ℕ × ℤ, F.fpDistPlus s p x
        * Set.indicator (bigTriSet F T s') (1 : ℕ × ℤ → ℝ≥0∞) ((j, l) + x)
      ≤ ∑' x : ℕ × ℤ, (F.fpDistPlus s p x
            * Set.indicator {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} (1 : ℕ × ℤ → ℝ≥0∞) x
          + F.fpDistPlus s p x
              * Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) * F.slopeInv|}
                (1 : ℕ × ℤ → ℝ≥0∞) x
          + ∑ r ∈ Finset.range W₀, F.fpDistPlus s p x
              * Set.indicator {y : ℕ × ℤ | r ≤ j + y.1 ∧ j + y.1 - r ∈ Apex}
                (1 : ℕ × ℤ → ℝ≥0∞) x) := ENNReal.tsum_le_tsum hpt
    _ = ∑' x : ℕ × ℤ, F.fpDistPlus s p x
            * Set.indicator {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} (1 : ℕ × ℤ → ℝ≥0∞) x
          + ∑' x : ℕ × ℤ, F.fpDistPlus s p x
              * Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) * F.slopeInv|}
                (1 : ℕ × ℤ → ℝ≥0∞) x
          + ∑ r ∈ Finset.range W₀, ∑' x : ℕ × ℤ, F.fpDistPlus s p x
              * Set.indicator {y : ℕ × ℤ | r ≤ j + y.1 ∧ j + y.1 - r ∈ Apex}
                (1 : ℕ × ℤ → ℝ≥0∞) x := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add,
          Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ENNReal.ofReal (Ch * Real.exp (-ch * H))
          + ENNReal.ofReal (Cc * (Real.exp (-cc * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-cc * D)))
          + ∑ r ∈ Finset.range W₀, ENNReal.ofReal (Ks * (1 / Real.sqrt (1 + s) + 1 / d)) :=
        add_le_add (add_le_add hS1 hS2)
          (Finset.sum_le_sum fun r _ => hsp s p d hd1 Apex hsep j r)
    _ = ENNReal.ofReal (Ch * Real.exp (-ch * H)
          + Cc * (Real.exp (-cc * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-cc * D))
          + (W₀ : ℝ) * (Ks * (1 / Real.sqrt (1 + s) + 1 / d))) := by
        have hn1 : 0 ≤ Ch * Real.exp (-ch * H) := mul_nonneg hCh.le (Real.exp_pos _).le
        have hn2 : 0 ≤ Cc * (Real.exp (-cc * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-cc * D)) :=
          mul_nonneg hCc.le (by positivity)
        have hn3 : 0 ≤ Ks * (1 / Real.sqrt (1 + s) + 1 / d) :=
          mul_nonneg hKs.le (add_nonneg (by positivity) (by positivity))
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_add hn1 hn2,
          ← ENNReal.ofReal_add (add_nonneg hn1 hn2) (mul_nonneg (Nat.cast_nonneg _) hn3)]
    _ ≤ ENNReal.ofReal (C * (H / s') + C * Real.exp (-ch * H)) := ENNReal.ofReal_le_ofReal hreal

/-- Walk form (the left-hand side of `bigTriangle_walk_le_rpow` of tao-collatz): for `p ≤ Tw` it equals the `fpDistPlus` form. -/
theorem bigTri_walk_eq (j : ℕ) (l : ℤ) (s : ℕ)
    {Tw p : ℕ} (hp : p ≤ Tw) (S : Set (ℕ × ℤ)) :
    ∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin Tw → ℕ × ℤ, F.hold.iid Tw v *
        Set.indicator S (1 : ℕ × ℤ → ℝ≥0∞) (j + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)
      = ∑' x : ℕ × ℤ, F.fpDistPlus s p x * Set.indicator S (1 : ℕ × ℤ → ℝ≥0∞) ((j, l) + x) := by
  rw [← F.fpDist_walk_eq_fpDistPlus s hp (fun x => Set.indicator S 1 ((j, l) + x))]
  refine tsum_congr fun e => ?_
  congr 1
  refine tsum_congr fun v => ?_
  congr 1
  congr 1
  refine Prod.ext ?_ ?_
  · show j + e.1 + (pathSum v p).1 = j + (e.1 + (pathSum v p).1)
    omega
  · show l + e.2 + (pathSum v p).2 = l + (e.2 + (pathSum v p).2)
    ring

/-- `Σ_{p ≤ N} 1/(1+p)² ≤ S₂` (`S₂ = Σ 1/(k+1)²`). -/
theorem sum_inv_sq_le (N : ℕ) :
    ∑ p ∈ Finset.range N, 1 / (1 + (p : ℝ)) ^ 2 ≤ ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 := by
  have hs : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have h := (summable_nat_add_iff 1).mpr this
    refine h.congr fun k => ?_
    push_cast; ring_nf
  calc ∑ p ∈ Finset.range N, 1 / (1 + (p : ℝ)) ^ 2
      = ∑ p ∈ Finset.range N, 1 / ((p : ℝ) + 1) ^ 2 :=
        Finset.sum_congr rfl fun p _ => by ring_nf
    _ ≤ ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 :=
        hs.sum_le_tsum _ (fun k _ => by positivity)

/-- Geometric series: `Σ_{p < N} r^{1+p} ≤ r/(1-r)` (`0 ≤ r < 1`). -/
theorem sum_geom_succ_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (N : ℕ) :
    ∑ p ∈ Finset.range N, r ^ (1 + p) ≤ r / (1 - r) := by
  have hs : HasSum (fun p : ℕ => r ^ (1 + p)) (r / (1 - r)) := by
    have h := (hasSum_geometric_of_lt_one h0 h1).mul_left r
    rw [show (fun p : ℕ => r ^ (1 + p)) = fun i => r * r ^ i from
      funext fun p => by rw [pow_add, pow_one], div_eq_mul_inv]
    exact h
  exact hs.summable.sum_le_tsum _ (fun p _ => by positivity) |>.trans hs.tsum_eq.le

/-- **The E∗ sum** (`estar_union_le_rpow` of tao-collatz): arbitrarily small for large `A`. -/
theorem estar_union_le :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ η : ℝ, 0 < η →
      ∃ A : ℝ, 1 ≤ A ∧ ∀ (half : ℕ) (T : F.TriFam half (F.sep ε)), ∀ t₀ ∈ T.T,
      ∀ (j : ℕ) (l : ℤ), (j, l) ∈ F.triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ s : ℕ, (s : ℤ) = t₀.2.1 - l → ((half - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) →
      ∀ Tw : ℕ, (∀ p, p ≤ Tw →
          ((⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ) ≤ ((half - j : ℕ) : ℝ) ^ (0.4 : ℝ)) →
        ∑ p ∈ Finset.range (Tw + 1),
          ∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin Tw → ℕ × ℤ, F.hold.iid Tw v *
            Set.indicator (bigTriSet F T ⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊)
              (1 : ℕ × ℤ → ℝ≥0∞) (j + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)
          ≤ ENNReal.ofReal η := by
  obtain ⟨ε₀, hε₀, hTE⟩ := triangle_encounter_le F
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεle η hη
  obtain ⟨C, hC, c, hc, A₀, hA₀, hbound⟩ := hTE ε hε hεle
  set S₂ : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 with hS₂
  have hS₂0 : 0 ≤ S₂ := tsum_nonneg fun k => by positivity
  -- `n² (1/4)^n → 0`, `exp(-c)^n → 0`
  have hlim1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2
    (show |(1 / 4 : ℝ)| < 1 by rw [abs_of_pos (by norm_num)]; norm_num)
  have hev1 := hlim1.eventually (gt_mem_nhds (show (0 : ℝ) < η / (2 * (C * S₂ + 1)) by
    positivity))
  have hr1 : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hlim2 := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-c)).le hr1
  have hev2 := hlim2.eventually (gt_mem_nhds (show (0 : ℝ) < min (1 / 2) (η / (4 * C)) by
    positivity))
  rw [Filter.eventually_atTop] at hev1 hev2
  obtain ⟨N1, hN1⟩ := hev1
  obtain ⟨N2, hN2⟩ := hev2
  set n : ℕ := N1 + N2 + ⌈A₀⌉₊ + 1 with hn
  have hn1 : N1 ≤ n := by omega
  have hn2 : N2 ≤ n := by omega
  have hnA : A₀ ≤ (n : ℝ) := by
    have h1 : A₀ ≤ (⌈A₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈A₀⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : ⌈A₀⌉₊ ≤ n)
    linarith
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  refine ⟨(n : ℝ), hn1R, ?_⟩
  intro half T t₀ ht₀ j l hmem s hs hdeep Tw hreg
  have h4 : ∀ p : ℕ, (4 : ℝ) ^ (n : ℝ) * (1 + (p : ℝ)) ^ 3
      = (((4 ^ n * (1 + p) ^ 3 : ℕ)) : ℝ) := by
    intro p; rw [Real.rpow_natCast]; push_cast; ring
  have hfl : ∀ p : ℕ, ⌊(4 : ℝ) ^ (n : ℝ) * (1 + (p : ℝ)) ^ 3⌋₊ = 4 ^ n * (1 + p) ^ 3 := by
    intro p; rw [h4 p, Nat.floor_natCast]
  set r : ℝ := Real.exp (-c * (n : ℝ) ^ 2) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hrle : r ≤ Real.exp (-c) ^ n := by
    rw [hr, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hrsmall : r < min (1 / 2) (η / (4 * C)) := lt_of_le_of_lt hrle (hN2 n hn2)
  have hr12 : r < 1 / 2 := lt_of_lt_of_le hrsmall (min_le_left _ _)
  have hrη : r < η / (4 * C) := lt_of_lt_of_le hrsmall (min_le_right _ _)
  -- bound for each `p`
  have hterm : ∀ p ∈ Finset.range (Tw + 1),
      ∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin Tw → ℕ × ℤ, F.hold.iid Tw v *
          Set.indicator (bigTriSet F T ⌊(4 : ℝ) ^ (n : ℝ) * (1 + (p : ℝ)) ^ 3⌋₊)
            (1 : ℕ × ℤ → ℝ≥0∞) (j + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)
        ≤ ENNReal.ofReal (C * (n : ℝ) ^ 2 * (1 / 4) ^ n * (1 / (1 + (p : ℝ)) ^ 2)
            + C * r ^ (1 + p)) := by
    intro p hp
    have hpT : p ≤ Tw := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    rw [bigTri_walk_eq F j l s hpT]
    have hs'1 : 1 ≤ ⌊(4 : ℝ) ^ (n : ℝ) * (1 + (p : ℝ)) ^ 3⌋₊ := by
      rw [hfl p]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    refine le_trans (hbound (n : ℝ) hnA half T t₀ ht₀ j l hmem s hs hdeep p _ hs'1
      (hreg p hpT)) (ENNReal.ofReal_le_ofReal ?_)
    rw [hfl p]
    have hp1 : (0 : ℝ) < 1 + (p : ℝ) := by positivity
    have h4n : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
    have e1 : C * (n : ℝ) ^ 2 * (1 + (p : ℝ)) / ((4 ^ n * (1 + p) ^ 3 : ℕ) : ℝ)
        = C * (n : ℝ) ^ 2 * (1 / 4) ^ n * (1 / (1 + (p : ℝ)) ^ 2) := by
      push_cast
      rw [div_pow, one_pow]
      field_simp
    have e2 : C * Real.exp (-c * (n : ℝ) ^ 2 * (1 + (p : ℝ))) = C * r ^ (1 + p) := by
      rw [hr, ← Real.exp_nat_mul]
      congr 2
      push_cast; ring
    rw [e1, e2]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hA1 : (n : ℝ) ^ 2 * (1 / 4) ^ n < η / (2 * (C * S₂ + 1)) := hN1 n hn1
  have hsum1 := sum_inv_sq_le (Tw + 1)
  have hsum2 := sum_geom_succ_le hr0 (by linarith) (Tw + 1)
  have hq0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (1 / 4) ^ n := by positivity
  have hpart1 : C * (n : ℝ) ^ 2 * (1 / 4) ^ n
        * ∑ p ∈ Finset.range (Tw + 1), 1 / (1 + (p : ℝ)) ^ 2 ≤ η / 2 := by
    calc C * (n : ℝ) ^ 2 * (1 / 4) ^ n * ∑ p ∈ Finset.range (Tw + 1), 1 / (1 + (p : ℝ)) ^ 2
        ≤ C * (n : ℝ) ^ 2 * (1 / 4) ^ n * S₂ :=
          mul_le_mul_of_nonneg_left hsum1 (by positivity)
      _ = ((n : ℝ) ^ 2 * (1 / 4) ^ n) * (C * S₂) := by ring
      _ ≤ (η / (2 * (C * S₂ + 1))) * (C * S₂ + 1) := by
          apply mul_le_mul hA1.le (by linarith) (by positivity) (by positivity)
      _ = η / 2 := by field_simp
  have hpart2 : C * ∑ p ∈ Finset.range (Tw + 1), r ^ (1 + p) ≤ η / 2 := by
    have h1r : 1 / 2 ≤ 1 - r := by linarith
    calc C * ∑ p ∈ Finset.range (Tw + 1), r ^ (1 + p) ≤ C * (r / (1 - r)) :=
          mul_le_mul_of_nonneg_left hsum2 hC.le
      _ ≤ C * (2 * r) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          rw [div_le_iff₀ (by linarith)]
          nlinarith
      _ ≤ C * (2 * (η / (4 * C))) := by
          apply mul_le_mul_of_nonneg_left _ hC.le; linarith
      _ = η / 2 := by field_simp; ring
  linarith

end FW

end Family

end GGMCollatz
