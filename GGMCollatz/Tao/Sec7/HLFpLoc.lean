import GGMCollatz.Tao.Sec7.HLRenewF

/-!
# Distribution of the first-passage location (Lemma 7.7) and column sums

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/FpLocation.lean`
(`fpDist_location_bound_core`, `fpDist_location_bound`, `hasSum_int_shift_exp`, `fpDist_col_le_core`,
`fpDist_col_le`); generalized to the GGM family (p, q, r). Modified: the center `s/4` became `s · slopeInv`, and the one-step bound became
`e^{-γ d₁} e^{-γ d₂}` (without the mean offsets `4, 16`). No explicit constants (existential form).

Assembly: by the first-passage decomposition (`fpDist_le_renewal_conv`), bound the endpoint mass by the convolution of "the renewal measure below the budget line"
with "one step of `ℋ`"; insert the Gaussian bound (`renewalMass_boundHL`) for the renewal measure and the exponential bound
(`hold_step_boundHL`) for the step; close the sum over `j₁` with `conv_Gweight_exp`, the shift of the center with `Gweight_shift`,
and the sum over `m` with `sum_sqrt_exp_le`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace HL

/-- Sum over `ℤ` of an exponential with shifted support (`hasSum_int_shift_exp` of tao-collatz): `0` for indices `≤ s`, and
the positive tail is `∑_{k≥1} e^{-ck} = e^{-c}/(1-e^{-c})`. -/
theorem hasSum_int_shift_exp {c : ℝ} (hc : 0 < c) (s : ℕ) :
    HasSum (fun l : ℤ => if (s : ℤ) < l then Real.exp (-c * ((l : ℝ) - (s : ℝ))) else 0)
      (Real.exp (-c) / (1 - Real.exp (-c))) := by
  have he1 : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have he0 : (0 : ℝ) < Real.exp (-c) := Real.exp_pos _
  set f : ℤ → ℝ :=
    fun l => if (s : ℤ) < l then Real.exp (-c * ((l : ℝ) - (s : ℝ))) else 0 with hf
  have hgeom : HasSum (fun n : ℕ => Real.exp (-c) * Real.exp (-c) ^ n)
      (Real.exp (-c) / (1 - Real.exp (-c))) := by
    have h := (hasSum_geometric_of_lt_one he0.le he1).mul_left (Real.exp (-c))
    rwa [← div_eq_mul_inv] at h
  have hneg : HasSum (fun n : ℕ => f (-(↑n + 1))) 0 := by
    have h0 : (fun n : ℕ => f (-(↑n + 1))) = fun _ => (0 : ℝ) := by
      funext n; rw [hf]; dsimp only; rw [if_neg (by omega)]
    rw [h0]; exact hasSum_zero
  have hnat : HasSum (fun n : ℕ => f (n : ℤ)) (Real.exp (-c) / (1 - Real.exp (-c))) := by
    have h2 : HasSum (fun n : ℕ => f (((n + (s + 1) : ℕ)) : ℤ))
        (Real.exp (-c) / (1 - Real.exp (-c))) := by
      have he : (fun n : ℕ => f (((n + (s + 1) : ℕ)) : ℤ))
          = fun n : ℕ => Real.exp (-c) * Real.exp (-c) ^ n := by
        funext n; rw [hf]; dsimp only
        rw [if_pos (by push_cast; omega), ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1; push_cast; ring
      rw [he]; exact hgeom
    have hfront : ∑ i ∈ Finset.range (s + 1), f (i : ℤ) = 0 := by
      apply Finset.sum_eq_zero; intro i hi; rw [hf]; dsimp only
      rw [if_neg (by have := Finset.mem_range.mp hi; omega)]
    rw [← hasSum_nat_add_iff' (s + 1)]
    simpa [hfront] using h2
  simpa using hnat.of_nat_of_neg_add_one hneg

end HL

open GGMCollatz.HL

namespace Family

namespace HL

variable (F : Family)

/-- **Core of the assembly of Lemma 7.7** (the `ℋ` version of `fpDist_location_bound_core` of tao-collatz, with abstract constants):
from the Gaussian bound `(c₆, C₆)` for the renewal measure, the exponential one-step bound `(γ, C₇)` and the envelope `K` of the sum over `m`, the bound on the
first-passage location holds with rate `c_F = min (min (c₆/2) (γ/4) / 2) γ` and constant `C₆ C₇ (4 + 8/γ) · 2 · K`. -/
theorem fpDist_location_core (c6 C6 γ C7 K : ℝ)
    (hc6 : 0 < c6) (hC6 : 0 < C6) (hγ : 0 < γ) (hC7 : 0 < C7) (hK : 0 < K)
    (hU : ∀ (j : ℕ) (l : ℤ), 0 ≤ l →
      (renewalMass F (j, l)).toReal
        ≤ C6 / Real.sqrt (1 + (l : ℝ))
            * Gweight (1 + (l : ℝ)) (c6 * ((j : ℝ) - (l : ℝ) * F.slopeInv)))
    (hstep : ∀ d : ℕ × ℤ,
      (F.hold d).toReal ≤ C7 * Real.exp (-γ * (d.1 : ℝ)) * Real.exp (-γ * (d.2 : ℝ)))
    (hKs : ∀ s : ℕ,
      ∑ m ∈ Finset.range (s + 1), Real.exp (-(γ / 2) * ((s : ℝ) - m)) / Real.sqrt (1 + m)
        ≤ K / Real.sqrt (1 + s)) :
    ∀ (s : ℕ) (j : ℕ) (l : ℤ),
      (F.fpDist s (j, l)).toReal
        ≤ C6 * C7 * (4 + 8 / γ) * 2 * K
            * (Real.exp (-(min (min (c6 / 2) (γ / 4) / 2) γ) * ((l : ℝ) - s))
                / Real.sqrt (1 + s))
            * Gweight (1 + s)
                (min (min (c6 / 2) (γ / 4) / 2) γ * ((j : ℝ) - s * F.slopeInv)) := by
  set c9 : ℝ := min (c6 / 2) (γ / 4) with hc9def
  have hc9 : 0 < c9 := lt_min (by positivity) (by positivity)
  have hc9γ : c9 ≤ γ / 4 := min_le_right _ _
  set cF : ℝ := min (c9 / 2) γ with hcFdef
  have hcF : 0 < cF := lt_min (by positivity) hγ
  set D : ℝ := C6 * C7 * (4 + 8 / γ) * 2 with hDdef
  have hD : 0 < D := by rw [hDdef]; positivity
  have hι0 := slopeInv_nonneg F
  have hι1 := slopeInv_le_half F
  intro s j l
  have h1s : (0 : ℝ) < 1 + (s : ℝ) := by positivity
  have hsq : 0 < Real.sqrt (1 + (s : ℝ)) := Real.sqrt_pos.mpr h1s
  set X : ℝ := (j : ℝ) - s * F.slopeInv with hXdef
  have hGF : 0 ≤ Gweight (1 + (s : ℝ)) (cF * X) := Gweight_nonneg _ _
  by_cases hls : l ≤ (s : ℤ)
  · -- below the budget line there is no first-passage mass
    have h0 : F.fpDist s (j, l) = 0 := by
      by_contra h
      exact absurd (F.fpDist_support_snd_gt s (j, l) (by rwa [PMF.mem_support_iff]))
        (not_lt.mpr hls)
    rw [h0, ENNReal.toReal_zero]
    positivity
  push Not at hls
  have hlsR : (s : ℝ) ≤ (l : ℝ) := by exact_mod_cast hls.le
  -- ── Stage 1: turn the renewal convolution into a finite sum (in `ℝ≥0∞`) ──
  set Fs : Finset (ℕ × ℤ) := (Finset.range (j + 1)) ×ˢ (Finset.Icc (0 : ℤ) (s : ℤ))
    with hFs
  have hinner : ∀ p : ℕ × ℤ,
      (∑' d : ℕ × ℤ, if (j, l) = p + d then F.hold d else 0)
        = if p.1 ≤ j then F.hold (j - p.1, l - p.2) else 0 := by
    intro p
    by_cases hp : p.1 ≤ j
    · rw [if_pos hp, tsum_eq_single ((j - p.1, l - p.2) : ℕ × ℤ) ?_, if_pos ?_]
      · apply Prod.ext
        · show j = p.1 + (j - p.1)
          omega
        · show l = p.2 + (l - p.2)
          ring
      · intro d hd
        rw [if_neg]
        intro he
        apply hd
        have h1 : j = p.1 + d.1 := congrArg Prod.fst he
        have h2 : l = p.2 + d.2 := congrArg Prod.snd he
        obtain ⟨d1, d2⟩ := d
        apply Prod.ext
        · show d1 = j - p.1
          simp only at h1
          omega
        · show d2 = l - p.2
          simp only at h2
          omega
    · rw [if_neg hp]
      refine ENNReal.tsum_eq_zero.mpr fun d => ?_
      rw [if_neg]
      intro he
      apply hp
      have h1 : j = p.1 + d.1 := congrArg Prod.fst he
      omega
  have hred : (∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then renewalMass F p else 0)
        * ∑' d : ℕ × ℤ, (if (j, l) = p + d then F.hold d else 0))
      = ∑ p ∈ Fs, renewalMass F p * F.hold (j - p.1, l - p.2) := by
    rw [tsum_congr fun p => by rw [hinner p]]
    rw [tsum_eq_sum (s := Fs) ?_]
    · refine Finset.sum_congr rfl fun p hp => ?_
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      have h1 : p.1 ≤ j := by
        have := Finset.mem_range.mp hp1
        omega
      have h2 := (Finset.mem_Icc.mp hp2).2
      rw [if_pos h2, if_pos h1]
    · intro p hp
      by_cases h1 : p.1 ≤ j
      · by_cases h2 : p.2 ≤ (s : ℤ)
        · have h3 : p.2 < 0 := by
            by_contra h3
            push Not at h3
            exact hp (Finset.mem_product.mpr
              ⟨Finset.mem_range.mpr (by omega), Finset.mem_Icc.mpr ⟨h3, h2⟩⟩)
          rw [renewalMass_zero_of_snd_neg F h3, ite_self, zero_mul]
        · rw [if_neg h2, zero_mul]
      · rw [if_neg h1, mul_zero]
  have hfp : F.fpDist s (j, l) ≤ ∑ p ∈ Fs, renewalMass F p * F.hold (j - p.1, l - p.2) :=
    hred ▸ fpDist_le_renewal_conv F s (j, l)
  -- ── Stage 2: move to reals ──
  have hterm_ne : ∀ p ∈ Fs, renewalMass F p * F.hold (j - p.1, l - p.2) ≠ ⊤ := fun p _ =>
    ENNReal.mul_ne_top (renewalMass_ne_top F p) (PMF.apply_ne_top _ _)
  have hsum_ne : (∑ p ∈ Fs, renewalMass F p * F.hold (j - p.1, l - p.2)) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr fun p hp => (hterm_ne p hp).lt_top).ne
  have hreal : (F.fpDist s (j, l)).toReal
      ≤ ∑ p ∈ Fs, (renewalMass F p).toReal * (F.hold (j - p.1, l - p.2)).toReal := by
    calc (F.fpDist s (j, l)).toReal
        ≤ (∑ p ∈ Fs, renewalMass F p * F.hold (j - p.1, l - p.2)).toReal :=
          ENNReal.toReal_mono hsum_ne hfp
      _ = ∑ p ∈ Fs, (renewalMass F p).toReal * (F.hold (j - p.1, l - p.2)).toReal := by
          rw [ENNReal.toReal_sum hterm_ne]
          exact Finset.sum_congr rfl fun p _ => ENNReal.toReal_mul
  refine hreal.trans ?_
  -- ── Stage 3: double sum over `ℕ` indices ──
  have hIcc : Finset.Icc (0 : ℤ) (s : ℤ) = (Finset.range (s + 1)).image
      (fun m : ℕ => (m : ℤ)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h0, hs'⟩
      exact ⟨x.toNat, by omega, by omega⟩
    · rintro ⟨m, hm, rfl⟩
      omega
  have hsplit : ∑ p ∈ Fs, (renewalMass F p).toReal * (F.hold (j - p.1, l - p.2)).toReal
      = ∑ j₁ ∈ Finset.range (j + 1), ∑ m ∈ Finset.range (s + 1),
          (renewalMass F (j₁, (m : ℤ))).toReal * (F.hold (j - j₁, l - m)).toReal := by
    rw [hFs, Finset.sum_product]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    rw [hIcc, Finset.sum_image (fun a _ b _ h => by exact_mod_cast h)]
  rw [hsplit]
  -- ── Stage 4: envelope for each `(j₁, m)`, convolution in `j₁`, shift of the center, sum over `m` ──
  set G2 : ℝ := Gweight (1 + (s : ℝ)) (c9 / 2 * X) with hG2def
  have hG2 : 0 ≤ G2 := Gweight_nonneg _ _
  have hmsum : ∀ m ∈ Finset.range (s + 1),
      ∑ j₁ ∈ Finset.range (j + 1),
        (renewalMass F (j₁, (m : ℤ))).toReal * (F.hold (j - j₁, l - m)).toReal
      ≤ D * Real.exp (-γ * ((l : ℝ) - s)) * G2
          * (Real.exp (-(γ / 2) * ((s : ℝ) - m)) / Real.sqrt (1 + m)) := by
    intro m hm
    have hms : m ≤ s := by
      have := Finset.mem_range.mp hm
      omega
    have hmsR : (m : ℝ) ≤ (s : ℝ) := by exact_mod_cast hms
    have h1m : (0 : ℝ) < 1 + (m : ℝ) := by positivity
    have h1ms : 1 + (m : ℝ) ≤ 1 + (s : ℝ) := by linarith
    -- envelope of each term
    have hterm : ∀ j₁ ∈ Finset.range (j + 1),
        (renewalMass F (j₁, (m : ℤ))).toReal * (F.hold (j - j₁, l - m)).toReal
        ≤ (C7 * Real.exp (-γ * ((l : ℝ) - m)))
            * (C6 / Real.sqrt (1 + m))
            * (Gweight (1 + (m : ℝ)) (c6 * ((j₁ : ℝ) - (m : ℝ) * F.slopeInv))
              * Real.exp (-γ * |(((j : ℤ)) : ℝ) - (j₁ : ℝ)|)) := by
      intro j₁ hj₁
      have hj₁j : j₁ ≤ j := by
        have := Finset.mem_range.mp hj₁
        omega
      have hUb := hU j₁ (m : ℤ) (Int.natCast_nonneg m)
      simp only [Int.cast_natCast] at hUb
      have hsb := hstep (j - j₁, l - m)
      have hc1 : (((j - j₁ : ℕ) : ℝ)) = (j : ℝ) - j₁ := by
        rw [Nat.cast_sub hj₁j]
      have hc2 : (((l - m : ℤ) : ℝ)) = (l : ℝ) - m := by push_cast; ring
      dsimp only at hsb
      rw [hc1, hc2] at hsb
      have habs1 : (j : ℝ) - j₁ = |(((j : ℤ)) : ℝ) - (j₁ : ℝ)| := by
        rw [Int.cast_natCast, abs_of_nonneg]
        have : (j₁ : ℝ) ≤ j := by exact_mod_cast hj₁j
        linarith
      rw [habs1] at hsb
      calc (renewalMass F (j₁, (m : ℤ))).toReal * (F.hold (j - j₁, l - m)).toReal
          ≤ (C6 / Real.sqrt (1 + (m : ℝ))
              * Gweight (1 + (m : ℝ)) (c6 * ((j₁ : ℝ) - (m : ℝ) * F.slopeInv)))
            * (C7 * Real.exp (-γ * |(((j : ℤ)) : ℝ) - (j₁ : ℝ)|)
              * Real.exp (-γ * ((l : ℝ) - m))) := by
            apply mul_le_mul hUb hsb ENNReal.toReal_nonneg
              (mul_nonneg (by positivity) (Gweight_nonneg _ _))
        _ = (C7 * Real.exp (-γ * ((l : ℝ) - m)))
            * (C6 / Real.sqrt (1 + m))
            * (Gweight (1 + (m : ℝ)) (c6 * ((j₁ : ℝ) - (m : ℝ) * F.slopeInv))
              * Real.exp (-γ * |(((j : ℤ)) : ℝ) - (j₁ : ℝ)|)) := by
            ring
    -- convolution in `j₁`
    have hconv := conv_Gweight_exp (t := 1 + (m : ℝ)) (c := c6) (γ := γ)
      h1m hc6 hγ ((m : ℝ) * F.slopeInv) (j : ℤ) (j + 1) (by rw [Int.toNat_natCast]; omega)
    -- move the center to `j - s·slopeInv` and the time scale to `1+s`
    have hshift : Gweight (1 + (m : ℝ)) (c9 * ((((j : ℤ)) : ℝ) - (m : ℝ) * F.slopeInv))
        ≤ 2 * Real.exp ((c9 / 2) * ((s : ℝ) - m)) * G2 := by
      have harg : (((j : ℤ)) : ℝ) - (m : ℝ) * F.slopeInv
          = X + F.slopeInv * ((s : ℝ) - m) := by
        rw [hXdef, Int.cast_natCast]
        ring
      rw [harg, hG2def]
      refine (Gweight_shift h1m h1ms hc9 X (F.slopeInv * ((s : ℝ) - m))).trans ?_
      have hδ : |F.slopeInv * ((s : ℝ) - m)| ≤ ((s : ℝ) - m) / 2 := by
        rw [abs_of_nonneg (mul_nonneg hι0 (by linarith))]
        nlinarith
      have hE : Real.exp (c9 * |F.slopeInv * ((s : ℝ) - m)|)
          ≤ Real.exp ((c9 / 2) * ((s : ℝ) - m)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hδ hc9.le]
      apply mul_le_mul_of_nonneg_right ?_ (Gweight_nonneg _ _)
      apply mul_le_mul_of_nonneg_left hE (by norm_num)
    -- balancing the exponentials: `e^{-γ(l-m)} e^{(c₉/2)(s-m)} ≤ e^{-γ(l-s)} e^{-(γ/2)(s-m)}`
    have hexps : Real.exp (-γ * ((l : ℝ) - m)) * Real.exp ((c9 / 2) * ((s : ℝ) - m))
        ≤ Real.exp (-γ * ((l : ℝ) - s)) * Real.exp (-(γ / 2) * ((s : ℝ) - m)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hc9γ (by linarith : (0:ℝ) ≤ (s : ℝ) - m)]
    calc ∑ j₁ ∈ Finset.range (j + 1),
        (renewalMass F (j₁, (m : ℤ))).toReal * (F.hold (j - j₁, l - m)).toReal
        ≤ ∑ j₁ ∈ Finset.range (j + 1),
          (C7 * Real.exp (-γ * ((l : ℝ) - m)))
            * (C6 / Real.sqrt (1 + m))
            * (Gweight (1 + (m : ℝ)) (c6 * ((j₁ : ℝ) - (m : ℝ) * F.slopeInv))
              * Real.exp (-γ * |(((j : ℤ)) : ℝ) - (j₁ : ℝ)|)) :=
          Finset.sum_le_sum hterm
      _ = (C7 * Real.exp (-γ * ((l : ℝ) - m)))
          * (C6 / Real.sqrt (1 + m))
          * ∑ j₁ ∈ Finset.range (j + 1),
            Gweight (1 + (m : ℝ)) (c6 * ((j₁ : ℝ) - (m : ℝ) * F.slopeInv))
              * Real.exp (-γ * |(((j : ℤ)) : ℝ) - (j₁ : ℝ)|) := by
          rw [Finset.mul_sum]
      _ ≤ (C7 * Real.exp (-γ * ((l : ℝ) - m)))
          * (C6 / Real.sqrt (1 + m))
          * ((4 + 8 / γ)
            * (2 * Real.exp ((c9 / 2) * ((s : ℝ) - m)) * G2)) := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine hconv.trans ?_
          exact mul_le_mul_of_nonneg_left hshift (by positivity)
      _ = (D * G2) * (Real.exp (-γ * ((l : ℝ) - m))
            * Real.exp ((c9 / 2) * ((s : ℝ) - m)))
          * (1 / Real.sqrt (1 + m)) := by
          rw [hDdef]
          ring
      _ ≤ (D * G2) * (Real.exp (-γ * ((l : ℝ) - s))
            * Real.exp (-(γ / 2) * ((s : ℝ) - m)))
          * (1 / Real.sqrt (1 + m)) := by
          apply mul_le_mul_of_nonneg_right ?_ (by positivity)
          apply mul_le_mul_of_nonneg_left hexps (by positivity)
      _ = D * Real.exp (-γ * ((l : ℝ) - s)) * G2
          * (Real.exp (-(γ / 2) * ((s : ℝ) - m)) / Real.sqrt (1 + m)) := by
          ring
  -- ── Stage 5: the sum over `m`, and relaxing the constants and the decay ──
  calc ∑ j₁ ∈ Finset.range (j + 1), ∑ m ∈ Finset.range (s + 1),
        (renewalMass F (j₁, (m : ℤ))).toReal * (F.hold (j - j₁, l - m)).toReal
      = ∑ m ∈ Finset.range (s + 1), ∑ j₁ ∈ Finset.range (j + 1),
        (renewalMass F (j₁, (m : ℤ))).toReal * (F.hold (j - j₁, l - m)).toReal :=
        Finset.sum_comm
    _ ≤ ∑ m ∈ Finset.range (s + 1),
        D * Real.exp (-γ * ((l : ℝ) - s)) * G2
          * (Real.exp (-(γ / 2) * ((s : ℝ) - m)) / Real.sqrt (1 + m)) :=
        Finset.sum_le_sum hmsum
    _ = D * Real.exp (-γ * ((l : ℝ) - s)) * G2
        * ∑ m ∈ Finset.range (s + 1),
          Real.exp (-(γ / 2) * ((s : ℝ) - m)) / Real.sqrt (1 + m) := by
        rw [Finset.mul_sum]
    _ ≤ D * Real.exp (-γ * ((l : ℝ) - s)) * G2 * (K / Real.sqrt (1 + s)) := by
        apply mul_le_mul_of_nonneg_left (hKs s) (by positivity)
    _ ≤ D * K * (Real.exp (-cF * ((l : ℝ) - s)) / Real.sqrt (1 + s))
        * Gweight (1 + (s : ℝ)) (cF * X) := by
        have hexpF : Real.exp (-γ * ((l : ℝ) - s)) ≤ Real.exp (-cF * ((l : ℝ) - s)) := by
          apply Real.exp_le_exp.mpr
          have hcFγ : cF ≤ γ := min_le_right _ _
          have h := mul_le_mul_of_nonneg_right hcFγ (sub_nonneg.mpr hlsR)
          linarith only [h]
        have hGrel : G2 ≤ Gweight (1 + (s : ℝ)) (cF * X) := by
          rw [hG2def, ← Gweight_abs _ (c9 / 2 * X), ← Gweight_abs _ (cF * X),
            abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < c9 / 2),
            abs_of_pos hcF]
          apply Gweight_anti h1s (by positivity)
          have hcF9 : cF ≤ c9 / 2 := min_le_left _ _
          linarith only [mul_le_mul_of_nonneg_right hcF9 (abs_nonneg X)]
        calc D * Real.exp (-γ * ((l : ℝ) - s)) * G2 * (K / Real.sqrt (1 + s))
            ≤ D * Real.exp (-cF * ((l : ℝ) - s))
              * Gweight (1 + (s : ℝ)) (cF * X) * (K / Real.sqrt (1 + s)) := by
              apply mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc D * Real.exp (-γ * ((l : ℝ) - s)) * G2
                  ≤ D * Real.exp (-cF * ((l : ℝ) - s)) * G2 := by
                    apply mul_le_mul_of_nonneg_right ?_ hG2
                    exact mul_le_mul_of_nonneg_left hexpF hD.le
                _ ≤ D * Real.exp (-cF * ((l : ℝ) - s))
                    * Gweight (1 + (s : ℝ)) (cF * X) := by
                    apply mul_le_mul_of_nonneg_left hGrel (by positivity)
            _ = D * K * (Real.exp (-cF * ((l : ℝ) - s)) / Real.sqrt (1 + s))
                * Gweight (1 + (s : ℝ)) (cF * X) := by ring

/-- **The `ℋ` version of Lemma 7.7** (distribution of the first-passage location):
`P(endpoint = (j,l)) ≤ C e^{-c(l-s)}/√(1+s) · G_{1+s}(c(j - s·slopeInv))`. -/
theorem fpDist_location_boundHL :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ (s : ℕ) (j : ℕ) (l : ℤ),
      (F.fpDist s (j, l)).toReal
        ≤ C * (Real.exp (-c * ((l : ℝ) - s)) / Real.sqrt (1 + s))
            * Sec7.Gweight (1 + s) (c * ((j : ℝ) - s * F.slopeInv)) := by
  obtain ⟨c6, hc6, C6, hC6, hU⟩ := renewalMass_boundHL F
  obtain ⟨γ, hγ, C7, hC7, hstep⟩ := hold_step_boundHL F
  obtain ⟨K, hK, hKs⟩ := sum_sqrt_exp_le (γ := γ / 2) (by positivity)
  have h := fpDist_location_core F c6 C6 γ C7 K hc6 hC6 hγ hC7 hK hU hstep hKs
  refine ⟨min (min (c6 / 2) (γ / 4) / 2) γ, lt_min (by positivity) hγ,
    C6 * C7 * (4 + 8 / γ) * 2 * K, by positivity, fun s j l => ?_⟩
  exact h s j l

/-- **Core of the column sums** (the `ℋ` version of `fpDist_col_le_core` of tao-collatz): summing the location bound over the height `l`
(the mass lives only on `l > s`, and `e^{-c(l-s)}` is a geometric series) gives the column bound with constant `C e^{-c}/(1-e^{-c})`. -/
theorem fpDist_col_core (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hbound : ∀ (s : ℕ) (j : ℕ) (l : ℤ),
      (F.fpDist s (j, l)).toReal
        ≤ C * (Real.exp (-c * ((l : ℝ) - s)) / Real.sqrt (1 + s))
            * Gweight (1 + s) (c * ((j : ℝ) - s * F.slopeInv))) :
    ∀ (s j : ℕ),
      ∑' l : ℤ, (F.fpDist s (j, l)).toReal
        ≤ C * (Real.exp (-c) / (1 - Real.exp (-c)))
            * (Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) * F.slopeInv))
                  / Real.sqrt (1 + (s : ℝ))) := by
  have he1 : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have he0 : (0 : ℝ) < Real.exp (-c) := Real.exp_pos _
  have hpos : (0 : ℝ) < 1 - Real.exp (-c) := by linarith
  intro s j
  set G : ℝ := Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) * F.slopeInv)) with hG
  have hGnn : 0 ≤ G := Gweight_nonneg _ _
  have hsq : (0 : ℝ) < Real.sqrt (1 + (s : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  set A : ℝ := C * G / Real.sqrt (1 + (s : ℝ)) with hA
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  have hdom : HasSum
      (fun l : ℤ => A * (if (s : ℤ) < l then Real.exp (-c * ((l : ℝ) - (s : ℝ))) else 0))
      (A * (Real.exp (-c) / (1 - Real.exp (-c)))) := (hasSum_int_shift_exp hc s).mul_left A
  have hptw : ∀ l : ℤ, (F.fpDist s (j, l)).toReal
      ≤ A * (if (s : ℤ) < l then Real.exp (-c * ((l : ℝ) - (s : ℝ))) else 0) := by
    intro l
    by_cases hl : (s : ℤ) < l
    · rw [if_pos hl, hA, hG]
      calc (F.fpDist s (j, l)).toReal
          ≤ C * (Real.exp (-c * ((l : ℝ) - (s : ℝ))) / Real.sqrt (1 + (s : ℝ)))
              * Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) * F.slopeInv)) := hbound s j l
        _ = C * Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) * F.slopeInv))
              / Real.sqrt (1 + (s : ℝ)) * Real.exp (-c * ((l : ℝ) - (s : ℝ))) := by ring
    · rw [if_neg hl, mul_zero]
      have h0 : F.fpDist s (j, l) = 0 := by
        by_contra h
        exact hl (F.fpDist_support_snd_gt s (j, l) (by rwa [PMF.mem_support_iff]))
      rw [h0, ENNReal.toReal_zero]
  have hslice : Summable (fun l : ℤ => (F.fpDist s (j, l)).toReal) := by
    have h2d : Summable (fun p : ℕ × ℤ => (F.fpDist s p).toReal) :=
      ENNReal.summable_toReal (by rw [(F.fpDist s).tsum_coe]; exact ENNReal.one_ne_top)
    exact h2d.comp_injective (fun a b h => by simpa using h)
  calc ∑' l : ℤ, (F.fpDist s (j, l)).toReal
      ≤ ∑' l : ℤ, A * (if (s : ℤ) < l then Real.exp (-c * ((l : ℝ) - (s : ℝ))) else 0) :=
        hslice.tsum_le_tsum hptw hdom.summable
    _ = A * (Real.exp (-c) / (1 - Real.exp (-c))) := hdom.tsum_eq
    _ = C * (Real.exp (-c) / (1 - Real.exp (-c))) * (G / Real.sqrt (1 + (s : ℝ))) := by
        rw [hA]; ring

/-- **The `ℋ` version of the column form of Lemma 7.7**: the marginal law of the endpoint column `j` is `≤ C' G_{1+s}(c(j - s·slopeInv))/√(1+s)`. -/
theorem fpDist_col_leHL :
    ∃ c : ℝ, 0 < c ∧ ∃ C' : ℝ, 0 < C' ∧ ∀ (s j : ℕ),
      ∑' l : ℤ, (F.fpDist s (j, l)).toReal
        ≤ C' * (Sec7.Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) * F.slopeInv))
                  / Real.sqrt (1 + (s : ℝ))) := by
  obtain ⟨c, hc, C, hC, hb⟩ := fpDist_location_boundHL F
  have he1 : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  refine ⟨c, hc, C * (Real.exp (-c) / (1 - Real.exp (-c))),
    mul_pos hC (div_pos (Real.exp_pos _) (by linarith)), ?_⟩
  exact fpDist_col_core F c C hc hC hb

end HL

end Family

end GGMCollatz
