import GGMCollatz.Tao.Prob.CharFn
import GGMCollatz.Tao.Prob.Tilt

/-!
# Local bound at the center via a finite circle method (general PMF; decay of the characteristic function from atom masses)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/Unroll.lean` (`modPair`,
`pair_transfer`, `charFn_decay_of_atoms`, `iidSum_apply_le_center_of_decay`). Modified: the proofs are unchanged
(they do not depend on `p`, `q`, `r`); in the generalization to the GGM family they are used for the tilted law of `ℋ`.
They are placed in the namespace `GGMCollatz.HL` to avoid name clashes.
-/

open scoped ENNReal

namespace GGMCollatz

namespace HL

/-- The mod-`N` reduction of the renewal lattice `ℕ × ℤ`. -/
def modPair (N : ℕ) (d : ℕ × ℤ) : ZMod N × ZMod N := ((d.1 : ZMod N), (d.2 : ZMod N))

/-- Transfer a two-atom anti-concentration bound through mass lower bounds and a
Jordan bound (helper for `charFn_hold_decay`). -/
theorem pair_transfer {X m0 m1 c0 c1 R u : ℝ} (hm0 : c0 ≤ m0) (hm1 : c1 ≤ m1)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hJ : 8 * u ^ 2 ≤ 1 - R)
    (hb : 2 * m0 * m1 * (1 - R) ≤ X) : 2 * c0 * c1 * (8 * u ^ 2) ≤ X := by
  have h1R : 0 ≤ 1 - R := le_trans (by positivity) hJ
  have hm0' : 0 ≤ m0 := le_trans hc0 hm0
  have hm1' : 0 ≤ m1 := le_trans hc1 hm1
  calc 2 * c0 * c1 * (8 * u ^ 2) ≤ 2 * c0 * c1 * (1 - R) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ ≤ 2 * m0 * m1 * (1 - R) := by
        have hcm : c0 * c1 ≤ m0 * m1 := mul_le_mul hm0 hm1 hc1 hm0'
        nlinarith
    _ ≤ X := hb

/-! ### Character decay for `hold mod N` -/

/-- **Parametric character decay from four atom-mass lower bounds** ((F3) of node S3):
any PMF `r` on `ZMod N × ZMod N` (`N ≥ 4`) whose masses at the four projected points
`(1,3), (2,5), (2,7), (2,8) mod N` are all `≥ μ` has characteristic function decaying
quadratically in the cyclic frequency distance, with explicit constant `2·μ²`.
This is `charFn_hold_decay` with the hold atom masses abstracted out, so it applies
verbatim to the exponentially tilted hold walk (whose atom masses at the same four
points are merely perturbed) — the tilting step (F) of Lemma 2.2(i), paper pp.14–15. -/
theorem charFn_decay_of_atoms {N : ℕ} [NeZero N] (hN : 4 ≤ N)
    (r : PMF (ZMod N × ZMod N)) {μ : ℝ} (hμ : 0 ≤ μ)
    (hm13 : μ ≤ (r (modPair N (1, 3))).toReal)
    (hm25 : μ ≤ (r (modPair N (2, 5))).toReal)
    (hm27 : μ ≤ (r (modPair N (2, 7))).toReal)
    (hm28 : μ ≤ (r (modPair N (2, 8))).toReal)
    (ξ : ZMod N × ZMod N) :
    ‖charFn r ξ‖ ^ 2
      ≤ 1 - 2 * μ ^ 2 * (((nd ξ.1 : ℝ) / N) ^ 2 + ((nd ξ.2 : ℝ) / N) ^ 2) := by
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  -- distinctness of the projected atoms (any collision forces N ∣ 1, 2 or 3)
  have hdvd : ∀ k : ℕ, 0 < k → k < 4 → ¬ ((k : ZMod N) = 0) := by
    intro k hk0 hk4 h
    have := (ZMod.natCast_eq_zero_iff k N).mp h
    have := Nat.le_of_dvd hk0 this
    omega
  have hd1 : modPair N (2, 5) ≠ modPair N (1, 3) := by
    intro h
    have h1 : ((2 : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) := by
      have := congrArg Prod.fst h
      simpa [modPair] using this
    exact hdvd 1 (by omega) (by omega) (by
      have : ((2 : ℕ) : ZMod N) - ((1 : ℕ) : ZMod N) = 0 := by rw [h1, sub_self]
      calc ((1 : ℕ) : ZMod N) = ((2 : ℕ) : ZMod N) - ((1 : ℕ) : ZMod N) := by
            push_cast
            ring
        _ = 0 := this)
  have hd2 : modPair N (2, 7) ≠ modPair N (2, 5) := by
    intro h
    have h1 : ((7 : ℤ) : ZMod N) = ((5 : ℤ) : ZMod N) := by
      have := congrArg Prod.snd h
      simpa [modPair] using this
    exact hdvd 2 (by omega) (by omega) (by
      have : ((7 : ℤ) : ZMod N) - ((5 : ℤ) : ZMod N) = 0 := by rw [h1, sub_self]
      calc ((2 : ℕ) : ZMod N) = ((7 : ℤ) : ZMod N) - ((5 : ℤ) : ZMod N) := by
            push_cast
            ring
        _ = 0 := this)
  have hd3 : modPair N (2, 8) ≠ modPair N (2, 5) := by
    intro h
    have h1 : ((8 : ℤ) : ZMod N) = ((5 : ℤ) : ZMod N) := by
      have := congrArg Prod.snd h
      simpa [modPair] using this
    exact hdvd 3 (by omega) (by omega) (by
      have : ((8 : ℤ) : ZMod N) - ((5 : ℤ) : ZMod N) = 0 := by rw [h1, sub_self]
      calc ((3 : ℕ) : ZMod N) = ((8 : ℤ) : ZMod N) - ((5 : ℤ) : ZMod N) := by
            push_cast
            ring
        _ = 0 := this)
  -- the three atom differences
  have hw1 : modPair N (2, 5) - modPair N (1, 3) = (((1 : ℕ) : ZMod N), ((2 : ℕ) : ZMod N)) := by
    rw [modPair, modPair, Prod.ext_iff]
    constructor <;> (show _ - _ = _) <;> push_cast <;> ring
  have hw2 : modPair N (2, 7) - modPair N (2, 5) = (((0 : ℕ) : ZMod N), ((2 : ℕ) : ZMod N)) := by
    rw [modPair, modPair, Prod.ext_iff]
    constructor <;> (show _ - _ = _) <;> push_cast <;> ring
  have hw3 : modPair N (2, 8) - modPair N (2, 5) = (((0 : ℕ) : ZMod N), ((3 : ℕ) : ZMod N)) := by
    rw [modPair, modPair, Prod.ext_iff]
    constructor <;> (show _ - _ = _) <;> push_cast <;> ring
  -- pinned frequencies
  set j1 : ZMod N := ξ.1 * ((1 : ℕ) : ZMod N) + ξ.2 * ((2 : ℕ) : ZMod N) with hj1
  set j2 : ZMod N := ξ.1 * ((0 : ℕ) : ZMod N) + ξ.2 * ((2 : ℕ) : ZMod N) with hj2
  set j3 : ZMod N := ξ.1 * ((0 : ℕ) : ZMod N) + ξ.2 * ((3 : ℕ) : ZMod N) with hj3
  set u1 : ℝ := (nd j1 : ℝ) / N with hu1
  set u2 : ℝ := (nd j2 : ℝ) / N with hu2
  set u3 : ℝ := (nd j3 : ℝ) / N with hu3
  -- Jordan bounds
  have hJ1 : 8 * u1 ^ 2 ≤ 1 - (pairChar ξ (((1 : ℕ) : ZMod N), ((2 : ℕ) : ZMod N))).re :=
    one_sub_re_stdAddChar_ge' j1
  have hJ2 : 8 * u2 ^ 2 ≤ 1 - (pairChar ξ (((0 : ℕ) : ZMod N), ((2 : ℕ) : ZMod N))).re :=
    one_sub_re_stdAddChar_ge' j2
  have hJ3 : 8 * u3 ^ 2 ≤ 1 - (pairChar ξ (((0 : ℕ) : ZMod N), ((3 : ℕ) : ZMod N))).re :=
    one_sub_re_stdAddChar_ge' j3
  -- pair anti-concentration bounds
  have hb1 := charFn_normSq_pair_bound r ξ _ _ hd1
  have hb2 := charFn_normSq_pair_bound r ξ _ _ hd2
  have hb3 := charFn_normSq_pair_bound r ξ _ _ hd3
  rw [hw1] at hb1
  rw [hw2] at hb2
  rw [hw3] at hb3
  -- combined per-pair lower bounds on 1 - ‖φ‖²
  set X : ℝ := 1 - ‖charFn r ξ‖ ^ 2 with hX
  have hA1 : 2 * μ * μ * (8 * u1 ^ 2) ≤ X :=
    pair_transfer hm25 hm13 hμ hμ hJ1 hb1
  have hA2 : 2 * μ * μ * (8 * u2 ^ 2) ≤ X :=
    pair_transfer hm27 hm25 hμ hμ hJ2 hb2
  have hA3 : 2 * μ * μ * (8 * u3 ^ 2) ≤ X :=
    pair_transfer hm28 hm25 hμ hμ hJ3 hb3
  have hu1X : 16 * (μ ^ 2 * u1 ^ 2) ≤ X := by linarith [hA1]
  have hu2X : 16 * (μ ^ 2 * u2 ^ 2) ≤ X := by linarith [hA2]
  have hu3X : 16 * (μ ^ 2 * u3 ^ 2) ≤ X := by linarith [hA3]
  -- triangle: recover ξ from the pinned frequencies
  have ht1 : nd ξ.1 ≤ nd j1 + nd j2 := by
    have h := nd_sub_le j1 j2
    have hsub : j1 - j2 = ξ.1 := by
      rw [hj1, hj2]
      push_cast
      ring
    rwa [hsub] at h
  have ht2 : nd ξ.2 ≤ nd j3 + nd j2 := by
    have h := nd_sub_le j3 j2
    have hsub : j3 - j2 = ξ.2 := by
      rw [hj3, hj2]
      push_cast
      ring
    rwa [hsub] at h
  have ht1R : (nd ξ.1 : ℝ) / N ≤ u1 + u2 := by
    rw [hu1, hu2, ← add_div]
    gcongr
    exact_mod_cast ht1
  have ht2R : (nd ξ.2 : ℝ) / N ≤ u3 + u2 := by
    rw [hu3, hu2, ← add_div]
    gcongr
    exact_mod_cast ht2
  have hnd1nn : (0 : ℝ) ≤ (nd ξ.1 : ℝ) / N := by positivity
  have hnd2nn : (0 : ℝ) ≤ (nd ξ.2 : ℝ) / N := by positivity
  have ha2 : ((nd ξ.1 : ℝ) / N) ^ 2 ≤ 2 * u1 ^ 2 + 2 * u2 ^ 2 := by
    nlinarith [ht1R, hnd1nn, sq_nonneg (u1 - u2)]
  have hb2' : ((nd ξ.2 : ℝ) / N) ^ 2 ≤ 2 * u3 ^ 2 + 2 * u2 ^ 2 := by
    nlinarith [ht2R, hnd2nn, sq_nonneg (u3 - u2)]
  -- 2μ²·D ≤ 2μ²(2u1² + 4u2² + 2u3²) = 4(μ²u1²) + 8(μ²u2²) + 4(μ²u3²) ≤ X/4 + X/2 + X/4
  have hDa : μ ^ 2 * ((nd ξ.1 : ℝ) / N) ^ 2 ≤ μ ^ 2 * (2 * u1 ^ 2 + 2 * u2 ^ 2) :=
    mul_le_mul_of_nonneg_left ha2 (sq_nonneg μ)
  have hDb : μ ^ 2 * ((nd ξ.2 : ℝ) / N) ^ 2 ≤ μ ^ 2 * (2 * u3 ^ 2 + 2 * u2 ^ 2) :=
    mul_le_mul_of_nonneg_left hb2' (sq_nonneg μ)
  linarith [hDa, hDb, hu1X, hu2X, hu3X]

/-- **Parametric center-regime local bound** ((F4) of node S3, Gaussian summation
at `N = ⌊√n⌋ + 1` from a character-decay hypothesis with constant `c`): any walk on
the renewal lattice whose projected characteristic functions decay like
`1 - (nd-sum)/c` uniformly in `N ≥ 4` has point masses `≤ (32c)²/(1+n)`.
Instantiated at `hold` (`c = 768`) and at the tilted hold walk
(`c = 80000`, via `charFn_decay_of_atoms` + `tilt_hold_apply_ge`). -/
theorem iidSum_apply_le_center_of_decay (p : PMF (ℕ × ℤ)) {c : ℝ} (hc : 1 ≤ c)
    (hdec : ∀ (N : ℕ) [NeZero N], 4 ≤ N → ∀ ξ : ZMod N × ZMod N,
      ‖charFn (p.map (modPair N)) ξ‖ ^ 2
        ≤ 1 - (((nd ξ.1 : ℝ) / N) ^ 2 + ((nd ξ.2 : ℝ) / N) ^ 2) / c)
    (n : ℕ) (v : ℕ × ℤ) :
    ((iidSum p n) v).toReal ≤ (32 * c) ^ 2 / (1 + (n : ℝ)) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  have h1n : (0 : ℝ) < 1 + n := by positivity
  rcases le_or_gt n 8 with hn8 | hn9
  · -- small n: the trivial mass bound suffices
    have h1 : (((iidSum p n)) v).toReal ≤ 1 := by
      have := (iidSum p n).coe_le_one v
      calc (((iidSum p n)) v).toReal ≤ (1 : ℝ≥0∞).toReal :=
            ENNReal.toReal_mono ENNReal.one_ne_top this
        _ = 1 := ENNReal.toReal_one
    have hcast : (n : ℝ) ≤ 8 := by exact_mod_cast hn8
    refine le_trans h1 ?_
    rw [le_div_iff₀ h1n]
    nlinarith
  · -- large n: circle method at N = √n + 1
    have hn9' : 9 ≤ n := hn9
    set N := n.sqrt + 1 with hN
    have : NeZero N := ⟨Nat.succ_ne_zero _⟩
    have hs3 : 3 ≤ n.sqrt := (Nat.le_sqrt.mpr (by omega))
    have hN4 : 4 ≤ N := by omega
    have hNlow : n + 1 ≤ N ^ 2 := Nat.lt_succ_sqrt' n
    have hNhigh : N ^ 2 ≤ 2 * n := by
      have h1 := Nat.sqrt_le' n
      have : N ^ 2 = n.sqrt ^ 2 + 2 * n.sqrt + 1 := by ring
      nlinarith [hs3, h1]
    have hNR : (0 : ℝ) < N := by
      have : 0 < N := by omega
      exact_mod_cast this
    -- the decay rate
    set a : ℝ := (n : ℝ) / (4 * c * (N : ℝ) ^ 2) with ha
    have hNlowR : (n : ℝ) + 1 ≤ (N : ℝ) ^ 2 := by exact_mod_cast hNlow
    have hNhighR : (N : ℝ) ^ 2 ≤ 2 * n := by exact_mod_cast hNhigh
    have ha0 : 0 < a := by
      rw [ha]
      have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      positivity
    have ha1 : a ≤ 1 := by
      rw [ha, div_le_one (by positivity)]
      nlinarith
    have ha_low : 1 / (8 * c) ≤ a := by
      rw [ha, le_div_iff₀ (by positivity)]
      have hkey : 1 / (8 * c) * (4 * c * (N : ℝ) ^ 2) = (N : ℝ) ^ 2 / 2 := by
        field_simp
        ring
      rw [hkey]
      linarith
    -- per-frequency exponential bound
    have hfreq : ∀ ξ : ZMod N × ZMod N,
        ‖charFn (p.map (modPair N)) ξ‖ ^ n
          ≤ Real.exp (-(a * ((nd ξ.1 : ℝ)) ^ 2)) * Real.exp (-(a * ((nd ξ.2 : ℝ)) ^ 2)) := by
      intro ξ
      have hdecay := hdec N hN4 ξ
      set D : ℝ := (((nd ξ.1 : ℝ) / N) ^ 2 + ((nd ξ.2 : ℝ) / N) ^ 2) / c with hD
      have hD0 : 0 ≤ D := by positivity
      have hpow := pow_le_exp_of_sq_le_one_sub n (by omega) (norm_nonneg _) hD0
        (by rw [hD]; linarith)
      refine le_trans hpow (le_of_eq ?_)
      rw [← Real.exp_add]
      congr 1
      rw [hD, ha]
      field_simp
      ring
    -- assemble
    have hle1 : (iidSum p n) v ≤ (iidSum (p.map (modPair N)) n) (modPair N v) := by
      calc (iidSum p n) v
          ≤ ((iidSum p n).map (modPair N)) (modPair N v) :=
            PMF.apply_le_map_apply _ _ _
        _ = (iidSum (p.map (modPair N)) n) (modPair N v) := by
            rw [iidSum_map p (modPair N) (by simp [modPair])
              (fun _ _ => by simp [modPair])]
    have hmain : ((iidSum p n) v).toReal
        ≤ ((N : ℝ) ^ 2)⁻¹ * ∑ ξ : ZMod N × ZMod N, ‖charFn (p.map (modPair N)) ξ‖ ^ n :=
      le_trans (ENNReal.toReal_mono
          ((iidSum (p.map (modPair N)) n).apply_ne_top _) hle1)
        (iidSum_apply_toReal_le (p.map (modPair N)) n (modPair N v))
    set g : ZMod N → ℝ := fun t => Real.exp (-(a * ((nd t : ℝ)) ^ 2)) with hg
    have hsum2 : ∑ ξ : ZMod N × ZMod N, ‖charFn (p.map (modPair N)) ξ‖ ^ n
        ≤ (∑ t : ZMod N, g t) ^ 2 := by
      calc ∑ ξ : ZMod N × ZMod N, ‖charFn (p.map (modPair N)) ξ‖ ^ n
          ≤ ∑ ξ : ZMod N × ZMod N, g ξ.1 * g ξ.2 :=
            Finset.sum_le_sum fun ξ _ => hfreq ξ
        _ = (∑ t : ZMod N, g t) * (∑ t : ZMod N, g t) := by
            rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
        _ = (∑ t : ZMod N, g t) ^ 2 := (sq _).symm
    have hg_bound : ∑ t : ZMod N, g t ≤ 32 * c := by
      calc ∑ t : ZMod N, g t ≤ 2 * (1 - Real.exp (-a))⁻¹ := sum_exp_neg_nd_sq_le ha0
        _ ≤ 2 * (2 / a) := by
            have := one_sub_exp_neg_inv_le ha0 ha1
            linarith
        _ = 4 / a := by ring
        _ ≤ 32 * c := by
            rw [div_le_iff₀ ha0]
            have hkey : 32 * c * (1 / (8 * c)) = 4 := by
              field_simp
              ring
            calc (4 : ℝ) = 32 * c * (1 / (8 * c)) := hkey.symm
              _ ≤ 32 * c * a := by
                  exact mul_le_mul_of_nonneg_left ha_low (by positivity)
    have hgnn : 0 ≤ ∑ t : ZMod N, g t :=
      Finset.sum_nonneg fun t _ => (Real.exp_pos _).le
    have hinvN : ((N : ℝ) ^ 2)⁻¹ ≤ (1 + (n : ℝ))⁻¹ := by
      gcongr
      linarith
    calc ((iidSum p n) v).toReal
        ≤ ((N : ℝ) ^ 2)⁻¹ * ∑ ξ : ZMod N × ZMod N,
            ‖charFn (p.map (modPair N)) ξ‖ ^ n := hmain
      _ ≤ ((N : ℝ) ^ 2)⁻¹ * (∑ t : ZMod N, g t) ^ 2 := by
          gcongr
      _ ≤ ((N : ℝ) ^ 2)⁻¹ * (32 * c) ^ 2 := by
          gcongr
      _ ≤ (1 + (n : ℝ))⁻¹ * (32 * c) ^ 2 := by
          gcongr
      _ = (32 * c) ^ 2 / (1 + (n : ℝ)) := inv_mul_eq_div _ _

end HL

end GGMCollatz
