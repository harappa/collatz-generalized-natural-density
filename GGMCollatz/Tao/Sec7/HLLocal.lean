import GGMCollatz.Tao.Sec7.HLQuad
import GGMCollatz.Tao.Sec7.HLCircle

/-!
# The `ℋ` version of Lemma 2.2: local bound and tails (counterpart of `Sec7/HoldLocal.lean` of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, files `TaoCollatz/Sec7/HoldLocal.lean`
(`tiltHold_apply_le_center`, `holdSum_apply_le_chernoff`, `hold_local_bound`, `holdSum_halfspace_le`,
`hold_tail_bound`) and `TaoCollatz/Prob/LocalInstances.lean` (`chernoff_clip_le`);
generalized to the GGM family (p, q, r). Modified: the numerical values of tao-collatz (box `1/200`, `1000`, `80000`, `c = 1/400`) were replaced by
constants built from the constants `b`, `K` of `HLQuad` (existential form).

* `holdSum_eq_iidSum`, `holdTilt_center`: the central bound `≤ C₀/(1+n)` for the tilted walk (uniform in the tilt).
* `chernoff_clip_gen`: with `λ = clip(dev/(2Kn), b)`, `Knλ² - λ·dev ≤ -min(dev²/(4Kn), b|dev|/2)`.
* `hold_local_boundHL`, `hold_tail_boundHL`: the same form as the statements in `HoldLocal.lean`.
-/

open scoped ENNReal

namespace GGMCollatz

open GGMCollatz.HL

namespace Family

namespace HL

variable (F : Family)

/-- `holdSum` is the i.i.d. sum of `ℋ`. -/
theorem holdSum_eq_iidSum (n : ℕ) : F.holdSum n = iidSum F.hold n := by
  rw [holdSum, iidSum]
  have hf : (fun v : Fin n → ℕ × ℤ => ((∑ i, (v i).1, ∑ i, (v i).2) : ℕ × ℤ))
      = fun v : Fin n → ℕ × ℤ => ∑ i, v i := by
    funext v
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
    · rw [Prod.snd_sum]
  rw [hf]

/-- The constants `b`, `K` (`K ≥ 1`) and the constant `C₀` of the central bound for the tilted walk. -/
theorem holdTilt_center :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 / 4 ∧ ∃ K : ℝ, 1 ≤ K ∧
      (∀ l1 l2 : ℝ, |l1| ≤ b → |l2| ≤ b →
        tiltZ F.hold (expW2 l1 l2)
          ≤ ENNReal.ofReal (Real.exp (F.holdMean1 * l1 + F.holdMean2 * l2
              + K * (l1 ^ 2 + l2 ^ 2)))) ∧
      ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ l1 l2 : ℝ, |l1| ≤ b → |l2| ≤ b → ∀ (n : ℕ) (v : ℕ × ℤ),
        ((iidSum (holdTilt F l1 l2) n) v).toReal ≤ C₀ / (1 + (n : ℝ)) := by
  obtain ⟨b, hb0, hb1, K₀, hK₀, hZ₀⟩ := hold_mgf_exp F
  set K : ℝ := max K₀ 1 with hKdef
  have hK1 : 1 ≤ K := le_max_right _ _
  have hZ : ∀ l1 l2 : ℝ, |l1| ≤ b → |l2| ≤ b →
      tiltZ F.hold (expW2 l1 l2)
        ≤ ENNReal.ofReal (Real.exp (F.holdMean1 * l1 + F.holdMean2 * l2
            + K * (l1 ^ 2 + l2 ^ 2))) := by
    intro l1 l2 h1 h2
    refine le_trans (hZ₀ l1 l2 h1 h2) (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    have : K₀ * (l1 ^ 2 + l2 ^ 2) ≤ K * (l1 ^ 2 + l2 ^ 2) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    linarith
  refine ⟨b, hb0, hb1, K, hK1, hZ, ?_⟩
  obtain ⟨ha13, ha25, ha27, ha28⟩ := hold_atoms_pos F
  set m₀ : ℝ := min (min (F.hold (1, 3)).toReal (F.hold (2, 5)).toReal)
    (min (F.hold (2, 7)).toReal (F.hold (2, 8)).toReal) with hm₀
  have hm₀pos : 0 < m₀ := lt_min (lt_min ha13 ha25) (lt_min ha27 ha28)
  set μ₀ : ℝ := m₀ * Real.exp (-(10 * b))
    / Real.exp (F.holdMean1 * b + F.holdMean2 * b + 2 * K * b ^ 2) with hμ₀
  have hμ₀pos : 0 < μ₀ := by positivity
  set c : ℝ := max 1 (1 / (2 * μ₀ ^ 2)) with hc
  have hc1 : 1 ≤ c := le_max_left _ _
  refine ⟨(32 * c) ^ 2, by positivity, ?_⟩
  intro l1 l2 hl1 hl2 n v
  have hK0 : 0 ≤ K := by linarith
  -- the tilted mass of each atom is `≥ μ₀`
  have hatom : ∀ y : ℕ × ℤ, (y.1 : ℝ) ≤ 2 → (0 : ℝ) ≤ y.2 → (y.2 : ℝ) ≤ 8 →
      m₀ ≤ (F.hold y).toReal → μ₀ ≤ (holdTilt F l1 l2 y).toReal := by
    intro y hy1 hy2 hy2' hm
    refine le_trans ?_ (holdTilt_apply_ge F hb0 hZ hK0 hl1 hl2 y hy1 hy2 hy2')
    rw [hμ₀]
    gcongr
  have hmap : ∀ {N : ℕ} [NeZero N] (y : ℕ × ℤ), (y.1 : ℝ) ≤ 2 → (0 : ℝ) ≤ y.2 →
      (y.2 : ℝ) ≤ 8 → m₀ ≤ (F.hold y).toReal →
      μ₀ ≤ (((holdTilt F l1 l2).map (modPair N)) (modPair N y)).toReal := by
    intro N _ y hy1 hy2 hy2' hm
    exact le_trans (hatom y hy1 hy2 hy2' hm)
      (ENNReal.toReal_mono (PMF.apply_ne_top _ _) (PMF.apply_le_map_apply _ _ _))
  have hdec : ∀ (N : ℕ) [NeZero N], 4 ≤ N → ∀ ξ : ZMod N × ZMod N,
      ‖charFn ((holdTilt F l1 l2).map (modPair N)) ξ‖ ^ 2
        ≤ 1 - (((nd ξ.1 : ℝ) / N) ^ 2 + ((nd ξ.2 : ℝ) / N) ^ 2) / c := by
    intro N _ hN ξ
    have h13 := hmap (N := N) (1, 3) (by norm_num) (by norm_num) (by norm_num)
      (le_trans (min_le_left _ _) (min_le_left _ _))
    have h25 := hmap (N := N) (2, 5) (by norm_num) (by norm_num) (by norm_num)
      (le_trans (min_le_left _ _) (min_le_right _ _))
    have h27 := hmap (N := N) (2, 7) (by norm_num) (by norm_num) (by norm_num)
      (le_trans (min_le_right _ _) (min_le_left _ _))
    have h28 := hmap (N := N) (2, 8) (by norm_num) (by norm_num) (by norm_num)
      (le_trans (min_le_right _ _) (min_le_right _ _))
    have h := charFn_decay_of_atoms hN ((holdTilt F l1 l2).map (modPair N)) hμ₀pos.le
      h13 h25 h27 h28 ξ
    refine le_trans h ?_
    set D : ℝ := ((nd ξ.1 : ℝ) / N) ^ 2 + ((nd ξ.2 : ℝ) / N) ^ 2 with hD
    have hD0 : 0 ≤ D := by positivity
    have hinv : 1 / c ≤ 2 * μ₀ ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      have : 1 / (2 * μ₀ ^ 2) ≤ c := le_max_right _ _
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have : D / c ≤ 2 * μ₀ ^ 2 * D := by
      rw [div_eq_mul_one_div, mul_comm D]
      exact mul_le_mul_of_nonneg_right hinv hD0
    linarith
  exact iidSum_apply_le_center_of_decay (holdTilt F l1 l2) hc1 hdec n v

/-- **Chernoff bridge**: `P(ℋ_{[1,n]} = (j,l)) ≤ C₀/(1+n) e^{n(λλ₁+νλ₂+K|λ|²) - (λ₁j + λ₂l)}`. -/
theorem holdSum_apply_le_chernoff {b K C₀ : ℝ}
    (hZ : ∀ l1 l2 : ℝ, |l1| ≤ b → |l2| ≤ b →
      tiltZ F.hold (expW2 l1 l2)
        ≤ ENNReal.ofReal (Real.exp (F.holdMean1 * l1 + F.holdMean2 * l2
            + K * (l1 ^ 2 + l2 ^ 2))))
    (hC : ∀ l1 l2 : ℝ, |l1| ≤ b → |l2| ≤ b → ∀ (n : ℕ) (v : ℕ × ℤ),
        ((iidSum (holdTilt F l1 l2) n) v).toReal ≤ C₀ / (1 + (n : ℝ)))
    {l1 l2 : ℝ} (hl1 : |l1| ≤ b) (hl2 : |l2| ≤ b) (n : ℕ) (j : ℕ) (l : ℤ) :
    ((F.holdSum n) (j, l)).toReal
      ≤ C₀ / (1 + (n : ℝ))
        * Real.exp ((n : ℝ) * (F.holdMean1 * l1 + F.holdMean2 * l2 + K * (l1 ^ 2 + l2 ^ 2))
            - (l1 * j + l2 * l)) := by
  have hZl := hZ l1 l2 hl1 hl2
  have hZt : tiltZ F.hold (expW2 l1 l2) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hZl
  have hZ0 := tiltZ_hold_ne_zero F l1 l2
  set u : ℝ := F.holdMean1 * l1 + F.holdMean2 * l2 + K * (l1 ^ 2 + l2 ^ 2) with hu
  set θ : ℝ := l1 * j + l2 * l with hθ
  have hwv0 : expW2 l1 l2 (j, l) ≠ 0 := by
    simp only [expW2]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hwvt : expW2 l1 l2 (j, l) ≠ ⊤ := by
    simp only [expW2]
    exact ENNReal.ofReal_ne_top
  have key := iidSum_apply_eq_tilt F.hold (expW2_zero l1 l2) (expW2_add l1 l2)
    hZ0 hZt n (j, l) hwv0 hwvt
  have hBpow : tiltZ F.hold (expW2 l1 l2) ^ n ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * u)) := by
    calc tiltZ F.hold (expW2 l1 l2) ^ n
        ≤ ENNReal.ofReal (Real.exp u) ^ n := by gcongr
      _ = ENNReal.ofReal (Real.exp u ^ n) :=
          (ENNReal.ofReal_pow (Real.exp_pos _).le n).symm
      _ = ENNReal.ofReal (Real.exp ((n : ℝ) * u)) := by rw [← Real.exp_nat_mul]
  have hB : ((tiltZ F.hold (expW2 l1 l2)) ^ n).toReal ≤ Real.exp ((n : ℝ) * u) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hBpow
    rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at h
  have hCeq : ((expW2 l1 l2 (j, l))⁻¹).toReal = Real.exp (-θ) := by
    simp only [expW2]
    rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, hθ]
  have hA := hC l1 l2 hl1 hl2 n (j, l)
  rw [holdTilt_eq F hZt] at hA
  rw [holdSum_eq_iidSum, key, ENNReal.toReal_mul, ENNReal.toReal_mul, hCeq]
  calc ((iidSum (tilt F.hold (expW2 l1 l2) hZ0 hZt) n) (j, l)).toReal
        * ((tiltZ F.hold (expW2 l1 l2)) ^ n).toReal * Real.exp (-θ)
      ≤ (C₀ / (1 + (n : ℝ)) * Real.exp ((n : ℝ) * u)) * Real.exp (-θ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        exact mul_le_mul hA hB ENNReal.toReal_nonneg (le_trans ENNReal.toReal_nonneg hA)
    _ = C₀ / (1 + (n : ℝ)) * Real.exp ((n : ℝ) * u - θ) := by
        rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg]

/-- **Optimization of the truncated λ** (general `K, b`). -/
theorem chernoff_clip_gen {K b : ℝ} (hK : 0 < K) (hb : 0 < b) {n : ℕ} (hn : 1 ≤ n) (dev : ℝ) :
    ∃ lam : ℝ, |lam| ≤ b ∧
      K * (n : ℝ) * lam ^ 2 - lam * dev ≤ -min (dev ^ 2 / (4 * K * n)) (b * |dev| / 2) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hKn : 0 < K * n := by positivity
  by_cases hc : |dev| ≤ 2 * K * n * b
  · refine ⟨dev / (2 * K * n), ?_, ?_⟩
    · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * K * n), div_le_iff₀ (by positivity)]
      linarith
    · have heq : K * (n : ℝ) * (dev / (2 * K * n)) ^ 2 - dev / (2 * K * n) * dev
          = -(dev ^ 2 / (4 * K * n)) := by
        field_simp
        ring
      rw [heq, neg_le_neg_iff]
      exact min_le_left _ _
  · push Not at hc
    refine ⟨if 0 ≤ dev then b else -b, ?_, ?_⟩
    · split_ifs <;> simp [abs_of_pos hb]
    · have habs : (if 0 ≤ dev then b else -b) * dev = b * |dev| := by
        split_ifs with h
        · rw [abs_of_nonneg h]
        · rw [abs_of_neg (lt_of_not_ge h)]; ring
      have hsq : (if 0 ≤ dev then b else -b) ^ 2 = b ^ 2 := by
        split_ifs <;> ring
      rw [habs, hsq]
      refine le_trans ?_ (neg_le_neg (min_le_right (dev ^ 2 / (4 * K * n)) (b * |dev| / 2)))
      have : K * n * b ^ 2 ≤ b * |dev| / 2 := by
        have : 2 * K * n * b * b ≤ |dev| * b := mul_le_mul_of_nonneg_right hc.le hb.le
        nlinarith
      linarith

/-- The form for nonnegative deviations. -/
theorem chernoff_clip_gen_nonneg {K b : ℝ} (hK : 0 < K) (hb : 0 < b) {n : ℕ} (hn : 1 ≤ n)
    {dev : ℝ} (hdev : 0 ≤ dev) :
    ∃ mu : ℝ, 0 ≤ mu ∧ mu ≤ b ∧
      K * (n : ℝ) * mu ^ 2 - mu * dev ≤ -min (dev ^ 2 / (4 * K * n)) (b * dev / 2) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  by_cases hc : dev ≤ 2 * K * n * b
  · refine ⟨dev / (2 * K * n), by positivity, ?_, ?_⟩
    · rw [div_le_iff₀ (by positivity)]; linarith
    · have heq : K * (n : ℝ) * (dev / (2 * K * n)) ^ 2 - dev / (2 * K * n) * dev
          = -(dev ^ 2 / (4 * K * n)) := by
        field_simp
        ring
      rw [heq, neg_le_neg_iff]
      exact min_le_left _ _
  · push Not at hc
    refine ⟨b, hb.le, le_refl _, ?_⟩
    refine le_trans ?_ (neg_le_neg (min_le_right (dev ^ 2 / (4 * K * n)) (b * dev / 2)))
    have : 2 * K * n * b * b ≤ dev * b := mul_le_mul_of_nonneg_right hc.le hb.le
    nlinarith

/-- Matching the optimized exponent to `Gweight`: `K ≥ 1`, `c = min(b/2, 1/(4K))`. -/
theorem exp_neg_min_le_Gweight_gen {K b : ℝ} (hK : 1 ≤ K) (hb : 0 < b) {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-min (x ^ 2 / (4 * K * n)) (b * x / 2))
      ≤ Sec7.Gweight (1 + n) (min (b / 2) (1 / (4 * K)) * x) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  set c : ℝ := min (b / 2) (1 / (4 * K)) with hc
  have hc0 : 0 < c := lt_min (by linarith) (by positivity)
  have hcb : c ≤ b / 2 := min_le_left _ _
  have hcK : c ≤ 1 / (4 * K) := min_le_right _ _
  have hc2 : c ^ 2 ≤ 1 / (4 * K) := by
    have h1 : c ≤ 1 := le_trans hcK (by rw [div_le_one (by positivity)]; linarith)
    calc c ^ 2 ≤ c := by nlinarith
      _ ≤ 1 / (4 * K) := hcK
  rcases min_cases (x ^ 2 / (4 * K * n)) (b * x / 2) with ⟨hm, _⟩ | ⟨hm, _⟩
  · rw [hm]
    have hbr : Real.exp (-(x ^ 2 / (4 * K * n)))
        ≤ Real.exp (-((c * x) ^ 2) / (1 + (n : ℝ))) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 : c ^ 2 * (4 * K) ≤ 1 := by
        rw [le_div_iff₀ (by positivity)] at hc2; linarith
      have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
      nlinarith [mul_nonneg hx2 hnpos.le, mul_nonneg (mul_nonneg hx2 hnpos.le) (sq_nonneg c)]
    exact le_trans hbr (le_add_of_nonneg_right (Real.exp_pos _).le)
  · rw [hm]
    have hbr : Real.exp (-(b * x / 2)) ≤ Real.exp (-|c * x|) := by
      apply Real.exp_le_exp.mpr
      rw [abs_of_nonneg (by positivity), neg_le_neg_iff]
      nlinarith
    exact le_trans hbr (le_add_of_nonneg_left (Real.exp_pos _).le)

/-- **The `ℋ` version of Lemma 2.2(i)** (the same statement as `hold_local_bound` in `HoldLocal.lean`). -/
theorem hold_local_boundHL :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (j : ℕ) (l : ℤ),
      ((F.holdSum n) (j, l)).toReal
        ≤ C / (1 + n) * Sec7.Gweight (1 + n)
            (c * ‖(((j : ℝ) - F.holdMean1 * n, (l : ℝ) - F.holdMean2 * n) : ℝ × ℝ)‖) := by
  obtain ⟨b, hb0, hb1, K, hK1, hZ, C₀, hC₀, hC⟩ := holdTilt_center F
  set c : ℝ := min (b / 2) (1 / (4 * K)) with hcdef
  have hc0 : 0 < c := lt_min (by linarith) (div_pos one_pos (by linarith))
  refine ⟨c, hc0, max C₀ 1, lt_max_of_lt_right one_pos, fun n j l => ?_⟩
  have hK0 : 0 < K := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [holdSum_eq_iidSum, iidSum_zero, PMF.pure_apply]
    split_ifs with h
    · have hj : j = 0 := congrArg Prod.fst h
      have hl : l = 0 := congrArg Prod.snd h
      subst hj; subst hl
      rw [ENNReal.toReal_one]
      simp only [mul_zero, sub_zero, CharP.cast_eq_zero, Int.cast_zero,
        add_zero]
      rw [show (((0 : ℝ), (0 : ℝ)) : ℝ × ℝ) = 0 from rfl, norm_zero, mul_zero]
      simp only [Sec7.Gweight, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        neg_zero, zero_div, Real.exp_zero, abs_zero]
      have : (1 : ℝ) ≤ max C₀ 1 := le_max_right _ _
      linarith
    · rw [ENNReal.toReal_zero]
      exact mul_nonneg (by positivity) (Sec7.Gweight_pos _ _).le
  · have hn1 : 1 ≤ n := hn
    set d1 : ℝ := (j : ℝ) - F.holdMean1 * n with hd1
    set d2 : ℝ := (l : ℝ) - F.holdMean2 * n with hd2
    obtain ⟨l1, hl1, hE1⟩ := chernoff_clip_gen hK0 hb0 hn1 d1
    obtain ⟨l2, hl2, hE2⟩ := chernoff_clip_gen hK0 hb0 hn1 d2
    have hch := holdSum_apply_le_chernoff F hZ hC hl1 hl2 n j l
    have hEeq : (n : ℝ) * (F.holdMean1 * l1 + F.holdMean2 * l2 + K * (l1 ^ 2 + l2 ^ 2))
          - (l1 * j + l2 * l)
        = (K * n * l1 ^ 2 - l1 * d1) + (K * n * l2 ^ 2 - l2 * d2) := by
      rw [hd1, hd2]; ring
    rw [hEeq] at hch
    set M : ℝ := max |d1| |d2| with hM
    have hnorm : ‖((d1, d2) : ℝ × ℝ)‖ = M := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    have hM0 : 0 ≤ M := le_trans (abs_nonneg d1) (le_max_left _ _)
    have hmin_nonneg : ∀ x : ℝ, 0 ≤ min (x ^ 2 / (4 * K * n)) (b * |x| / 2) := fun x =>
      le_min (by positivity) (by positivity)
    have hEle : (K * n * l1 ^ 2 - l1 * d1) + (K * n * l2 ^ 2 - l2 * d2)
        ≤ -min (M ^ 2 / (4 * K * n)) (b * M / 2) := by
      rcases max_cases |d1| |d2| with ⟨hMe, _⟩ | ⟨hMe, _⟩
      · have h2np : K * n * l2 ^ 2 - l2 * d2 ≤ 0 :=
          le_trans hE2 (neg_nonpos.mpr (hmin_nonneg d2))
        have hsq : M ^ 2 = d1 ^ 2 := by rw [hM, hMe, sq_abs]
        have habs : M = |d1| := by rw [hM, hMe]
        calc (K * n * l1 ^ 2 - l1 * d1) + (K * n * l2 ^ 2 - l2 * d2)
            ≤ -min (d1 ^ 2 / (4 * K * n)) (b * |d1| / 2) + 0 := add_le_add hE1 h2np
          _ = -min (M ^ 2 / (4 * K * n)) (b * M / 2) := by rw [add_zero, hsq, habs]
      · have h1np : K * n * l1 ^ 2 - l1 * d1 ≤ 0 :=
          le_trans hE1 (neg_nonpos.mpr (hmin_nonneg d1))
        have hsq : M ^ 2 = d2 ^ 2 := by rw [hM, hMe, sq_abs]
        have habs : M = |d2| := by rw [hM, hMe]
        calc (K * n * l1 ^ 2 - l1 * d1) + (K * n * l2 ^ 2 - l2 * d2)
            ≤ 0 + -min (d2 ^ 2 / (4 * K * n)) (b * |d2| / 2) := add_le_add h1np hE2
          _ = -min (M ^ 2 / (4 * K * n)) (b * M / 2) := by rw [zero_add, hsq, habs]
    have hGw : Real.exp ((K * n * l1 ^ 2 - l1 * d1) + (K * n * l2 ^ 2 - l2 * d2))
        ≤ Sec7.Gweight (1 + n) (c * M) :=
      le_trans (Real.exp_le_exp.mpr hEle) (exp_neg_min_le_Gweight_gen hK1 hb0 hn1 hM0)
    calc ((F.holdSum n) (j, l)).toReal
        ≤ C₀ / (1 + (n : ℝ))
          * Real.exp ((K * n * l1 ^ 2 - l1 * d1) + (K * n * l2 ^ 2 - l2 * d2)) := hch
      _ ≤ max C₀ 1 / (1 + (n : ℝ)) * Sec7.Gweight (1 + n) (c * M) := by
          apply mul_le_mul _ hGw (Real.exp_pos _).le (by positivity)
          gcongr
          exact le_max_left _ _
      _ = max C₀ 1 / (1 + (n : ℝ)) * Sec7.Gweight (1 + n) (c * ‖((d1, d2) : ℝ × ℝ)‖) := by
          rw [hnorm]

/-- **Markov half-space bound under tilting** (`holdSum_halfspace_le` of tao-collatz). -/
theorem holdSum_halfspace_le {b K : ℝ}
    (hZ : ∀ l1 l2 : ℝ, |l1| ≤ b → |l2| ≤ b →
      tiltZ F.hold (expW2 l1 l2)
        ≤ ENNReal.ofReal (Real.exp (F.holdMean1 * l1 + F.holdMean2 * l2
            + K * (l1 ^ 2 + l2 ^ 2))))
    {l1 l2 : ℝ} (hl1 : |l1| ≤ b) (hl2 : |l2| ≤ b)
    (n : ℕ) (cond : ℕ × ℤ → Prop) [DecidablePred cond] (a : ℝ)
    (hcond : ∀ d : ℕ × ℤ, cond d → a ≤ l1 * d.1 + l2 * d.2) :
    (∑' d : ℕ × ℤ, if cond d then (iidSum F.hold n) d else 0)
      ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * (F.holdMean1 * l1 + F.holdMean2 * l2
          + K * (l1 ^ 2 + l2 ^ 2)) - a)) := by
  have hZl := hZ l1 l2 hl1 hl2
  have hZt : tiltZ F.hold (expW2 l1 l2) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hZl
  have hZ0 := tiltZ_hold_ne_zero F l1 l2
  set u : ℝ := F.holdMean1 * l1 + F.holdMean2 * l2 + K * (l1 ^ 2 + l2 ^ 2) with hu
  have hM : (∑' d : ℕ × ℤ, if cond d then (iidSum F.hold n) d else 0)
      ≤ ENNReal.ofReal (Real.exp (-a)) * tiltZ F.hold (expW2 l1 l2) ^ n := by
    rw [← tiltZ_iidSum F.hold (expW2_zero l1 l2) (expW2_add l1 l2) hZ0 hZt n, tiltZ,
      ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun d => ?_
    split_ifs with h
    · have hw : ENNReal.ofReal (Real.exp a) ≤ expW2 l1 l2 d := by
        simp only [expW2]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hcond d h))
      calc (iidSum F.hold n) d
          = ENNReal.ofReal (Real.exp (-a))
              * (ENNReal.ofReal (Real.exp a) * (iidSum F.hold n) d) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
              neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
        _ ≤ ENNReal.ofReal (Real.exp (-a))
              * ((iidSum F.hold n) d * expW2 l1 l2 d) := by
            rw [mul_comm (ENNReal.ofReal (Real.exp a))]
            gcongr
    · exact bot_le
  refine le_trans hM ?_
  have hBpow : tiltZ F.hold (expW2 l1 l2) ^ n
      ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * u)) := by
    calc tiltZ F.hold (expW2 l1 l2) ^ n
        ≤ ENNReal.ofReal (Real.exp u) ^ n := by gcongr
      _ = ENNReal.ofReal (Real.exp u ^ n) :=
          (ENNReal.ofReal_pow (Real.exp_pos _).le n).symm
      _ = ENNReal.ofReal (Real.exp ((n : ℝ) * u)) := by rw [← Real.exp_nat_mul]
  calc ENNReal.ofReal (Real.exp (-a)) * tiltZ F.hold (expW2 l1 l2) ^ n
      ≤ ENNReal.ofReal (Real.exp (-a)) * ENNReal.ofReal (Real.exp ((n : ℝ) * u)) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp ((n : ℝ) * u - a)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, sub_eq_add_neg,
          add_comm (-a)]

/-- **The `ℋ` version of Lemma 2.2(ii)** (the same statement as `hold_tail_bound` in `HoldLocal.lean`). -/
theorem hold_tail_boundHL :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' d : ℕ × ℤ,
          if lam ≤ ‖(((d.1 : ℝ) - F.holdMean1 * n, (d.2 : ℝ) - F.holdMean2 * n) : ℝ × ℝ)‖
          then ((F.holdSum n) d).toReal else 0)
        ≤ C * Sec7.Gweight (1 + n) (c * lam) := by
  obtain ⟨b, hb0, hb1, K, hK1, hZ, -, -, -⟩ := holdTilt_center F
  have hK0 : 0 < K := by linarith
  set c : ℝ := min (b / 2) (1 / (4 * K)) with hcdef
  have hc0 : 0 < c := lt_min (by linarith) (div_pos one_pos (by linarith))
  refine ⟨c, hc0, 4, by norm_num, fun n lam hlam => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [holdSum_eq_iidSum, iidSum_zero]
    rw [tsum_eq_single (0 : ℕ × ℤ) (fun d hd => by
      rw [PMF.pure_apply, if_neg hd, ENNReal.toReal_zero, ite_self])]
    rw [PMF.pure_apply, if_pos rfl, ENNReal.toReal_one]
    split_ifs with h0
    · have hlam0 : lam = 0 := by
        simp only [Prod.fst_zero, Prod.snd_zero] at h0
        norm_num [Prod.norm_def] at h0
        linarith
      rw [hlam0, Sec7.Gweight]
      norm_num [Real.exp_zero]
    · exact mul_nonneg (by norm_num) (Sec7.Gweight_pos _ _).le
  · have hn1 : 1 ≤ n := hn
    obtain ⟨mu, hmu0, hmuhi, hexp⟩ := chernoff_clip_gen_nonneg hK0 hb0 hn1 hlam
    set B : ℝ := Real.exp (K * n * mu ^ 2 - mu * lam) with hB
    have hmu_abs : |mu| ≤ b := by rw [abs_of_nonneg hmu0]; exact hmuhi
    have hmu_abs' : |-mu| ≤ b := by rw [abs_neg, abs_of_nonneg hmu0]; exact hmuhi
    have hz : |(0 : ℝ)| ≤ b := by rw [abs_zero]; exact hb0.le
    set m1 := F.holdMean1
    set m2 := F.holdMean2
    have hT1 := holdSum_halfspace_le F hZ hmu_abs hz n
      (fun d : ℕ × ℤ => lam ≤ (d.1 : ℝ) - m1 * n) (mu * (m1 * n + lam))
      (fun d hd => by
        have h := mul_le_mul_of_nonneg_left
          (show (m1 * (n : ℝ) + lam) ≤ (d.1 : ℝ) by linarith) hmu0
        simp only [zero_mul, add_zero]
        linarith)
    have hT2 := holdSum_halfspace_le F hZ hmu_abs' hz n
      (fun d : ℕ × ℤ => (d.1 : ℝ) - m1 * n ≤ -lam) (-mu * (m1 * n - lam))
      (fun d hd => by
        have h := mul_le_mul_of_nonneg_left
          (show (d.1 : ℝ) ≤ m1 * (n : ℝ) - lam by linarith) hmu0
        simp only [zero_mul, add_zero]
        nlinarith)
    have hT3 := holdSum_halfspace_le F hZ hz hmu_abs n
      (fun d : ℕ × ℤ => lam ≤ (d.2 : ℝ) - m2 * n) (mu * (m2 * n + lam))
      (fun d hd => by
        have h := mul_le_mul_of_nonneg_left
          (show (m2 * (n : ℝ) + lam) ≤ (d.2 : ℝ) by linarith) hmu0
        simp only [zero_mul, zero_add]
        linarith)
    have hT4 := holdSum_halfspace_le F hZ hz hmu_abs' n
      (fun d : ℕ × ℤ => (d.2 : ℝ) - m2 * n ≤ -lam) (-mu * (m2 * n - lam))
      (fun d hd => by
        have h := mul_le_mul_of_nonneg_left
          (show (d.2 : ℝ) ≤ m2 * (n : ℝ) - lam by linarith) hmu0
        simp only [zero_mul, zero_add]
        nlinarith)
    have he1 : (n : ℝ) * (m1 * mu + m2 * 0 + K * (mu ^ 2 + 0 ^ 2))
        - mu * (m1 * n + lam) = K * n * mu ^ 2 - mu * lam := by ring
    have he2 : (n : ℝ) * (m1 * -mu + m2 * 0 + K * ((-mu) ^ 2 + 0 ^ 2))
        - -mu * (m1 * n - lam) = K * n * mu ^ 2 - mu * lam := by ring
    have he3 : (n : ℝ) * (m1 * 0 + m2 * mu + K * (0 ^ 2 + mu ^ 2))
        - mu * (m2 * n + lam) = K * n * mu ^ 2 - mu * lam := by ring
    have he4 : (n : ℝ) * (m1 * 0 + m2 * -mu + K * (0 ^ 2 + (-mu) ^ 2))
        - -mu * (m2 * n - lam) = K * n * mu ^ 2 - mu * lam := by ring
    rw [he1] at hT1
    rw [he2] at hT2
    rw [he3] at hT3
    rw [he4] at hT4
    have hsplit : ∀ d : ℕ × ℤ,
        (if lam ≤ ‖(((d.1 : ℝ) - m1 * n, (d.2 : ℝ) - m2 * n) : ℝ × ℝ)‖
            then (iidSum F.hold n) d else 0)
          ≤ (if lam ≤ (d.1 : ℝ) - m1 * n then (iidSum F.hold n) d else 0)
            + (if (d.1 : ℝ) - m1 * n ≤ -lam then (iidSum F.hold n) d else 0)
            + (if lam ≤ (d.2 : ℝ) - m2 * n then (iidSum F.hold n) d else 0)
            + (if (d.2 : ℝ) - m2 * n ≤ -lam then (iidSum F.hold n) d else 0) := by
      intro d
      by_cases h0 : lam ≤ ‖(((d.1 : ℝ) - m1 * n, (d.2 : ℝ) - m2 * n) : ℝ × ℝ)‖
      · rw [if_pos h0]
        rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at h0
        rcases le_max_iff.mp h0 with h | h
        · rcases le_abs.mp h with h' | h'
          · exact le_of_eq (if_pos h').symm |>.trans
              (((self_le_add_right _ _).trans (self_le_add_right _ _)).trans
                (self_le_add_right _ _))
          · have hc : (d.1 : ℝ) - m1 * n ≤ -lam := by linarith
            exact le_of_eq (if_pos hc).symm |>.trans
              (((self_le_add_left _ _).trans (self_le_add_right _ _)).trans
                (self_le_add_right _ _))
        · rcases le_abs.mp h with h' | h'
          · exact le_of_eq (if_pos h').symm |>.trans
              ((self_le_add_left _ _).trans (self_le_add_right _ _))
          · have hc : (d.2 : ℝ) - m2 * n ≤ -lam := by linarith
            exact le_of_eq (if_pos hc).symm |>.trans (self_le_add_left _ _)
      · rw [if_neg h0]
        exact bot_le
    have hchain : (∑' d : ℕ × ℤ,
        if lam ≤ ‖(((d.1 : ℝ) - m1 * n, (d.2 : ℝ) - m2 * n) : ℝ × ℝ)‖
          then (iidSum F.hold n) d else 0)
        ≤ 4 * ENNReal.ofReal B := by
      refine le_trans (ENNReal.tsum_le_tsum hsplit) ?_
      rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
      calc _ ≤ ENNReal.ofReal B + ENNReal.ofReal B + ENNReal.ofReal B
            + ENNReal.ofReal B :=
            add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4
        _ = 4 * ENNReal.ofReal B := by ring
    have hTop : ∀ d : ℕ × ℤ,
        (if lam ≤ ‖(((d.1 : ℝ) - m1 * n, (d.2 : ℝ) - m2 * n) : ℝ × ℝ)‖
          then (iidSum F.hold n) d else 0) ≠ ⊤ := fun d => by
      split_ifs
      · exact PMF.apply_ne_top _ _
      · exact ENNReal.zero_ne_top
    have hlhs : (∑' d : ℕ × ℤ,
        if lam ≤ ‖(((d.1 : ℝ) - m1 * n, (d.2 : ℝ) - m2 * n) : ℝ × ℝ)‖
          then ((F.holdSum n) d).toReal else 0)
        = (∑' d : ℕ × ℤ,
            if lam ≤ ‖(((d.1 : ℝ) - m1 * n, (d.2 : ℝ) - m2 * n) : ℝ × ℝ)‖
              then (iidSum F.hold n) d else 0).toReal := by
      rw [ENNReal.tsum_toReal_eq hTop]
      refine tsum_congr fun d => ?_
      rw [holdSum_eq_iidSum, apply_ite ENNReal.toReal, ENNReal.toReal_zero]
    rw [hlhs]
    have hfin : (4 : ℝ≥0∞) * ENNReal.ofReal B ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
    calc (∑' d : ℕ × ℤ,
        if lam ≤ ‖(((d.1 : ℝ) - m1 * n, (d.2 : ℝ) - m2 * n) : ℝ × ℝ)‖
          then (iidSum F.hold n) d else 0).toReal
        ≤ ((4 : ℝ≥0∞) * ENNReal.ofReal B).toReal := ENNReal.toReal_mono hfin hchain
      _ = 4 * B := by
          rw [hB, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
          norm_num
      _ ≤ 4 * Sec7.Gweight (1 + n) (c * lam) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          have h1 : Real.exp (K * n * mu ^ 2 - mu * lam)
              ≤ Real.exp (-min (lam ^ 2 / (4 * K * n)) (b * lam / 2)) :=
            Real.exp_le_exp.mpr hexp
          exact le_trans h1 (exp_neg_min_le_Gweight_gen hK1 hb0 hn1 hlam)

end HL

end Family

end GGMCollatz
