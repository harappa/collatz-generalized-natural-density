import GGMCollatz.Tao.Prob.Mgf
import GGMCollatz.Tao.Prob.CharFn1

/-!
# Chernoff-type tails and local bounds for sums of `G(μ)`, `P(μ)` (the `G(μ)` version of Tao's Lemma 2.2)

Derived from `TaoCollatz/Prob/LocalInstances.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2;
generalized to the GGM family (p, q, r): `geomHalf` (mean 2) is replaced by `geomP p` (`G(μ)`, mean `μ = p/(p-1)`),
and `pascal` (mean 4) by `pascalP p` (mean `2μ`). The general Chernoff machinery
(`chernoff_clip_le`, `iidSum_nat_halfspace_le`, `iidSum_nat_tail_of_quad`) does not depend on `p` and is unchanged.
In the general local-bound lemma `iidSum_nat_local_of_quad`, the lower bound on the masses of two points was
generalized from `3/16` to a general `δ ≤ 1/2` (the mass `(p-1)/p²` of `G(μ)` at 2 falls below `3/16` for `p ≥ 5`).
The parts concerning the `Hold` distribution (the `geomQuarter` instance) are not carried over.

* `muP p = p/(p-1)`: GGM's `μ` (the mean of `G(μ)`).
* `tiltZ_geomP_le_quad`: for `|λ| ≤ 1/200`, `Z(λ) ≤ 1 + μλ + 8λ²` (uniformly in all `p ≥ 2`).
* `geomP_tail_bound`: `P(||G(μ)^{(n)}| - μn| ≥ λ) ≤ 2 G_{1+n}(λ/400)` (the same constants for all `p ≥ 2`).
* `pascalP_tail_bound`: the tail of the same form for sums of `P(μ)`.
* `geomP_local_bound`, `pascalP_local_bound`: Lemma 2.2(i), `P(S_n = L) ≪ (1+n)^{-1/2} G_n(c(L - mean·n))`
  (`C` depends on `p`).
-/

open scoped ENNReal

namespace GGMCollatz

/-- GGM's `μ = p/(p-1)` (the mean of `G(μ)`). -/
noncomputable def muP (p : ℕ) : ℝ := (p : ℝ) / ((p : ℝ) - 1)

theorem muP_pos {p : ℕ} (hp : 2 ≤ p) : 0 < muP p := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold muP
  apply div_pos <;> linarith

/-- `1 < μ ≤ 2`. -/
theorem one_lt_muP {p : ℕ} (hp : 2 ≤ p) : 1 < muP p := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold muP
  rw [one_lt_div (by linarith)]
  linarith

theorem muP_le_two {p : ℕ} (hp : 2 ≤ p) : muP p ≤ 2 := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold muP
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- **Optimization of the truncation of λ**: for `n ≥ 1` and a deviation `dev`, with `λ = clip(dev/(2000n), 1/200)`
the Chernoff exponent `1000nλ² − λ·dev` is at most `−min(dev²/(4000n), |dev|/400)`. -/
theorem chernoff_clip_le {n : ℕ} (hn : 1 ≤ n) (dev : ℝ) :
    ∃ lam : ℝ, -(1 / 200) ≤ lam ∧ lam ≤ 1 / 200 ∧
      1000 * (n : ℝ) * lam ^ 2 - lam * dev
        ≤ -min (dev ^ 2 / (4000 * n)) (|dev| / 400) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hne : (n : ℝ) ≠ 0 := hnpos.ne'
  by_cases hc : |dev| ≤ 10 * n
  · have habs : |dev / (2000 * n)| ≤ 1 / 200 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2000 * n),
        div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg dev]
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    refine ⟨dev / (2000 * n), hlo, hhi, ?_⟩
    have heq : 1000 * (n : ℝ) * (dev / (2000 * n)) ^ 2 - dev / (2000 * n) * dev
        = -(dev ^ 2 / (4000 * n)) := by
      field_simp
      ring
    rw [heq, neg_le_neg_iff]
    exact min_le_left _ _
  · push Not at hc
    refine ⟨if 0 ≤ dev then (1 / 200 : ℝ) else -(1 / 200), ?_, ?_, ?_⟩
    · split_ifs <;> norm_num
    · split_ifs <;> norm_num
    · have habs : (if 0 ≤ dev then (1 / 200 : ℝ) else -(1 / 200)) * dev
          = |dev| / 200 := by
        split_ifs with h
        · rw [abs_of_nonneg h]; ring
        · rw [abs_of_neg (lt_of_not_ge h)]; ring
      have hsq : (if 0 ≤ dev then (1 / 200 : ℝ) else -(1 / 200)) ^ 2
          = 1 / 40000 := by
        split_ifs <;> norm_num
      rw [habs, hsq]
      refine le_trans ?_
        (neg_le_neg (min_le_right (dev ^ 2 / (4000 * n)) (|dev| / 400)))
      linarith

/-- **Optimization of the truncation of λ, form for a nonnegative deviation**. -/
theorem chernoff_clip_le_nonneg {n : ℕ} (hn : 1 ≤ n) {dev : ℝ} (hdev : 0 ≤ dev) :
    ∃ mu : ℝ, 0 ≤ mu ∧ mu ≤ 1 / 200 ∧
      1000 * (n : ℝ) * mu ^ 2 - mu * dev
        ≤ -min (dev ^ 2 / (4000 * n)) (dev / 400) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hne : (n : ℝ) ≠ 0 := hnpos.ne'
  by_cases hc : dev ≤ 10 * n
  · refine ⟨dev / (2000 * n), by positivity, ?_, ?_⟩
    · rw [div_le_iff₀ (by positivity)]
      linarith
    · have heq : 1000 * (n : ℝ) * (dev / (2000 * n)) ^ 2 - dev / (2000 * n) * dev
          = -(dev ^ 2 / (4000 * n)) := by
        field_simp
        ring
      rw [heq, neg_le_neg_iff]
      exact min_le_left _ _
  · push Not at hc
    refine ⟨1 / 200, by norm_num, le_refl _, ?_⟩
    refine le_trans ?_ (neg_le_neg (min_le_right (dev ^ 2 / (4000 * n)) (dev / 400)))
    nlinarith

/-- Matching the optimized Chernoff exponent to the two branches of `Gweight`: for `n ≥ 1`, `x ≥ 0`,
`e^{−min(x²/4000n, x/400)} ≤ G_{1+n}(x/400)`. -/
theorem exp_neg_min_le_Gweight {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-min (x ^ 2 / (4000 * n)) (x / 400)) ≤ Gweight (1 + n) (1 / 400 * x) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  rcases min_cases (x ^ 2 / (4000 * (n : ℝ))) (x / 400) with ⟨hm, _⟩ | ⟨hm, _⟩
  · rw [hm]
    have hbr : Real.exp (-(x ^ 2 / (4000 * n)))
        ≤ Real.exp (-((1 / 400 * x) ^ 2) / (1 + (n : ℝ))) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_le_neg_iff,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) hnpos.le]
    exact le_trans hbr (le_add_of_nonneg_right (Real.exp_pos _).le)
  · rw [hm]
    have hbr : -(x / 400) = -|1 / 400 * x| := by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 400 * x)]
      ring
    rw [hbr]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

/-- `Gweight` is even in its argument. -/
theorem Gweight_abs (t x : ℝ) : Gweight t |x| = Gweight t x := by
  rw [Gweight, Gweight, sq_abs, abs_abs]

/-! ### One-dimensional quadratic bounds on the moment generating function (the mean is exact to first order) -/

/-- **Quadratic bound on the moment generating function of `G(μ)`** (the mean `μ` is exact): for `|λ| ≤ 1/200`,
`Z(λ) ≤ 1 + μλ + 8λ²`. The same constants for all `p ≥ 2` (`p = 2` is the worst case). From the closed form
`tiltZ_geomP_frac` and the envelope `e^λ ≤ 1 + λ + 2λ²`. Generalizes tao-collatz's `tiltZ_geomHalf_le_quad`. -/
theorem tiltZ_geomP_le_quad {p : ℕ} (hp : 2 ≤ p) {lam : ℝ} (hlo : -(1 / 200) ≤ lam)
    (hhi : lam ≤ 1 / 200) :
    tiltZ (geomP p) (expW lam) ≤ ENNReal.ofReal (1 + muP p * lam + 8 * lam ^ 2) := by
  set P : ℝ := (p : ℝ) with hPdef
  have hP : (2 : ℝ) ≤ P := by rw [hPdef]; exact_mod_cast hp
  set E : ℝ := 1 + lam + 2 * lam ^ 2 with hE
  have hexpE : Real.exp lam ≤ E := exp_le_one_add_add_two_sq (by linarith)
  have hEpos : (0 : ℝ) < E := by rw [hE]; nlinarith
  have hEP : E < P := by rw [hE]; nlinarith
  have hPpos : (0 : ℝ) < P := by linarith
  rw [tiltZ_geomP_frac hp]
  refine le_trans (frac_closed_le (a' := (P - 1) * E / P) (r' := E / P)
    (div_nonneg (mul_nonneg (by linarith) (Real.exp_pos lam).le) hPpos.le)
    (by gcongr; linarith)
    (by have := Real.exp_pos lam; positivity)
    (by gcongr)
    (by rw [div_lt_one hPpos]; exact hEP)) ?_
  apply ENNReal.ofReal_le_ofReal
  have hPE : (0 : ℝ) < P - E := by linarith
  have hP1 : (0 : ℝ) < P - 1 := by linarith
  have hsimp : (P - 1) * E / P / (1 - E / P) = (P - 1) * E / (P - E) := by
    field_simp
  have hrew : 1 + muP p * lam + 8 * lam ^ 2
      = ((P - 1) * (1 + 8 * lam ^ 2) + P * lam) / (P - 1) := by
    unfold muP
    rw [← hPdef]
    field_simp
    ring
  rw [hsimp, hrew, div_le_div_iff₀ hPE hP1]
  -- the difference is `λ²·B`, `B = 6g² − 3g − 1 − 2(g+1)λ − 8gλ − 16gλ²` (`g = P − 1 ≥ 1`)
  set g : ℝ := P - 1 with hg
  have hg1 : (1 : ℝ) ≤ g := by rw [hg]; linarith
  have hB : 0 ≤ 6 * g ^ 2 - 3 * g - 1 - 2 * (g + 1) * lam - 8 * g * lam - 16 * g * lam ^ 2 := by
    have hl2 : lam ^ 2 ≤ 1 / 40000 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hg1) (sub_nonneg.mpr hg1),
      mul_nonneg (sub_nonneg.mpr hg1) (by linarith : (0 : ℝ) ≤ 1 / 200 - lam),
      mul_nonneg (sub_nonneg.mpr hg1) (by linarith : (0 : ℝ) ≤ 1 / 200 + lam),
      mul_nonneg (by linarith : (0 : ℝ) ≤ g) (sq_nonneg lam)]
  have hid : ((P - 1) * (1 + 8 * lam ^ 2) + P * lam) * (P - E) - (P - 1) * E * (P - 1)
      = lam ^ 2 * (6 * g ^ 2 - 3 * g - 1 - 2 * (g + 1) * lam - 8 * g * lam
          - 16 * g * lam ^ 2) := by
    rw [hg, hE]
    ring
  nlinarith [mul_nonneg (sq_nonneg lam) hB]

/-- **Quadratic bound on the moment generating function of `P(μ)`** (the mean `2μ` is exact): for `|λ| ≤ 1/200`,
`Z(λ) ≤ 1 + 2μλ + 1000λ²` (the square of the bound for `G(μ)`). -/
theorem tiltZ_pascalP_le_quad {p : ℕ} (hp : 2 ≤ p) {lam : ℝ} (hlo : -(1 / 200) ≤ lam)
    (hhi : lam ≤ 1 / 200) :
    tiltZ (pascalP p) (expW lam) ≤ ENNReal.ofReal (1 + 2 * muP p * lam + 1000 * lam ^ 2) := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hstrip : Real.exp lam < p :=
    lt_of_le_of_lt (exp_le_one_add_add_two_sq (by linarith)) (by nlinarith)
  have hgh := tiltZ_geomP_le_quad hp hlo hhi
  have hmu1 := one_lt_muP hp
  have hmu2 := muP_le_two hp
  have hP0 : (0 : ℝ) ≤ 1 + muP p * lam + 8 * lam ^ 2 := by nlinarith
  calc tiltZ (pascalP p) (expW lam)
      = tiltZ (geomP p) (expW lam) ^ 2 := tiltZ_pascalP hp hstrip
    _ ≤ ENNReal.ofReal (1 + muP p * lam + 8 * lam ^ 2) ^ 2 := by gcongr
    _ = ENNReal.ofReal ((1 + muP p * lam + 8 * lam ^ 2) ^ 2) :=
        (ENNReal.ofReal_pow hP0 2).symm
    _ ≤ ENNReal.ofReal (1 + 2 * muP p * lam + 1000 * lam ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have hb1 : (0 : ℝ) ≤ 1 / 200 - lam := by linarith
        have hb2 : (0 : ℝ) ≤ 1 / 200 + lam := by linarith
        have hl2 : lam ^ 2 ≤ 1 / 40000 := by nlinarith
        have hm : (muP p) ^ 2 ≤ 4 := by nlinarith
        nlinarith [sq_nonneg lam, mul_nonneg hb1 (sq_nonneg lam),
          mul_nonneg hb2 (sq_nonneg lam), mul_nonneg (sq_nonneg lam) (sq_nonneg lam),
          mul_nonneg (mul_nonneg hb1 hb2) (sq_nonneg lam),
          mul_nonneg (sq_nonneg lam) (by linarith : (0 : ℝ) ≤ 4 - (muP p) ^ 2),
          mul_nonneg (sq_nonneg lam) (by linarith : (0 : ℝ) ≤ 2 - muP p),
          mul_nonneg (mul_nonneg (sq_nonneg lam) hb1) (by linarith : (0 : ℝ) ≤ muP p),
          mul_nonneg (mul_nonneg (sq_nonneg lam) hb2) (by linarith : (0 : ℝ) ≤ muP p)]

/-! ### General machinery for one-dimensional Chernoff tails -/

/-- **One-sided Markov bound on a one-dimensional half-line**: if the tilting weight is `≥ e^a` on the region `cond`,
then the `iidSum` mass of that region is `≤ e^{-a}·Z(λ)ⁿ`. -/
theorem iidSum_nat_halfspace_le (p : PMF ℕ) {t : ℝ}
    (hZt : tiltZ p (expW t) ≠ ∞) (n : ℕ)
    (cond : ℕ → Prop) [DecidablePred cond] (a : ℝ)
    (hcond : ∀ L : ℕ, cond L → a ≤ t * L) :
    (∑' L : ℕ, if cond L then (iidSum p n) L else 0)
      ≤ ENNReal.ofReal (Real.exp (-a)) * tiltZ p (expW t) ^ n := by
  have hZ0 := tiltZ_expW_ne_zero p t
  rw [← tiltZ_iidSum p (expW_zero t) (expW_add t) hZ0 hZt n, tiltZ,
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun L => ?_
  split_ifs with h
  · have hw : ENNReal.ofReal (Real.exp a) ≤ expW t L := by
      rw [expW]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hcond L h))
    calc (iidSum p n) L
        = ENNReal.ofReal (Real.exp (-a))
            * (ENNReal.ofReal (Real.exp a) * (iidSum p n) L) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
            neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (Real.exp (-a))
            * ((iidSum p n) L * expW t L) := by
          rw [mul_comm (ENNReal.ofReal (Real.exp a))]
          gcongr
  · exact bot_le

/-- **General one-dimensional Lemma 2.2(ii)** (direct Chernoff): a walk on ℕ with the quadratic moment generating
function bound `Z(λ) ≤ 1 + mλ + 1000λ²` for `|λ| ≤ 1/200` satisfies the tail bound with `c = 1/400`, `C = 2`. -/
theorem iidSum_nat_tail_of_quad (p : PMF ℕ) (m : ℝ)
    (hquad : ∀ lam : ℝ, -(1 / 200) ≤ lam → lam ≤ 1 / 200 →
      tiltZ p (expW lam) ≤ ENNReal.ofReal (1 + m * lam + 1000 * lam ^ 2))
    (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∑' L : ℕ, if lam ≤ |(L : ℝ) - m * n| then ((iidSum p n) L).toReal else 0)
      ≤ 2 * Gweight (1 + n) (1 / 400 * lam) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [iidSum_zero]
    rw [tsum_eq_single (0 : ℕ) (fun L hL => by
      rw [PMF.pure_apply, if_neg hL, ENNReal.toReal_zero, ite_self])]
    rw [PMF.pure_apply, if_pos rfl, ENNReal.toReal_one]
    split_ifs with h0
    · have hlam0 : lam = 0 := by
        simp only [Nat.cast_zero, mul_zero, zero_sub, abs_neg, abs_zero] at h0
        linarith
      rw [hlam0]
      rw [Gweight]
      norm_num [Real.exp_zero]
    · exact mul_nonneg (by norm_num) (Gweight_nonneg _ _)
  · have hn1 : 1 ≤ n := hn
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    obtain ⟨mu, hmu0, hmuhi, hexp⟩ := chernoff_clip_le_nonneg hn1 hlam
    set B : ℝ := Real.exp (1000 * n * mu ^ 2 - mu * lam) with hB
    have hmulo : -(1 / 200) ≤ mu := by linarith
    have hmulo' : -(1 / 200) ≤ -mu := by linarith
    have hmuhi' : -mu ≤ 1 / 200 := by linarith
    have hq1 : tiltZ p (expW mu) ≤ ENNReal.ofReal (Real.exp (m * mu + 1000 * mu ^ 2)) :=
      le_trans (hquad mu hmulo hmuhi) (ENNReal.ofReal_le_ofReal (by
        have h := Real.add_one_le_exp (m * mu + 1000 * mu ^ 2)
        linarith))
    have hq2 : tiltZ p (expW (-mu))
        ≤ ENNReal.ofReal (Real.exp (m * -mu + 1000 * mu ^ 2)) :=
      le_trans (hquad (-mu) hmulo' hmuhi') (ENNReal.ofReal_le_ofReal (by
        have h := Real.add_one_le_exp (m * -mu + 1000 * mu ^ 2)
        nlinarith [sq_nonneg mu]))
    have hZt1 : tiltZ p (expW mu) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hq1
    have hZt2 : tiltZ p (expW (-mu)) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hq2
    have hpow : ∀ {t q : ℝ}, tiltZ p (expW t) ≤ ENNReal.ofReal (Real.exp q) →
        tiltZ p (expW t) ^ n ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * q)) := by
      intro t q hZq
      calc tiltZ p (expW t) ^ n
          ≤ ENNReal.ofReal (Real.exp q) ^ n := by gcongr
        _ = ENNReal.ofReal (Real.exp q ^ n) :=
            (ENNReal.ofReal_pow (Real.exp_pos _).le n).symm
        _ = ENNReal.ofReal (Real.exp ((n : ℝ) * q)) := by rw [← Real.exp_nat_mul]
    have hT1 : (∑' L : ℕ, if lam ≤ (L : ℝ) - m * n then (iidSum p n) L else 0)
        ≤ ENNReal.ofReal B := by
      refine le_trans (le_trans (le_of_eq rfl)
        (iidSum_nat_halfspace_le p hZt1 n _ (mu * (m * n + lam))
          (fun L hL => by nlinarith))) ?_
      calc ENNReal.ofReal (Real.exp (-(mu * (m * n + lam)))) * tiltZ p (expW mu) ^ n
          ≤ ENNReal.ofReal (Real.exp (-(mu * (m * n + lam))))
            * ENNReal.ofReal (Real.exp ((n : ℝ) * (m * mu + 1000 * mu ^ 2))) := by
            gcongr
            exact hpow hq1
        _ = ENNReal.ofReal B := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, hB]
            congr 2
            ring
    have hT2 : (∑' L : ℕ, if (L : ℝ) - m * n ≤ -lam then (iidSum p n) L else 0)
        ≤ ENNReal.ofReal B := by
      refine le_trans (le_trans (le_of_eq rfl)
        (iidSum_nat_halfspace_le p hZt2 n _ (-mu * (m * n - lam))
          (fun L hL => by nlinarith))) ?_
      calc ENNReal.ofReal (Real.exp (-(-mu * (m * n - lam)))) * tiltZ p (expW (-mu)) ^ n
          ≤ ENNReal.ofReal (Real.exp (-(-mu * (m * n - lam))))
            * ENNReal.ofReal (Real.exp ((n : ℝ) * (m * -mu + 1000 * mu ^ 2))) := by
            gcongr
            exact hpow hq2
        _ = ENNReal.ofReal B := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, hB]
            congr 2
            ring
    have hsplit : ∀ L : ℕ,
        (if lam ≤ |(L : ℝ) - m * n| then (iidSum p n) L else 0)
          ≤ (if lam ≤ (L : ℝ) - m * n then (iidSum p n) L else 0)
            + (if (L : ℝ) - m * n ≤ -lam then (iidSum p n) L else 0) := by
      intro L
      by_cases h0 : lam ≤ |(L : ℝ) - m * n|
      · rw [if_pos h0]
        rcases le_abs.mp h0 with h' | h'
        · exact le_of_eq (if_pos h').symm |>.trans (self_le_add_right _ _)
        · have hc : (L : ℝ) - m * n ≤ -lam := by linarith
          exact le_of_eq (if_pos hc).symm |>.trans (self_le_add_left _ _)
      · rw [if_neg h0]
        exact bot_le
    have hchain : (∑' L : ℕ, if lam ≤ |(L : ℝ) - m * n| then (iidSum p n) L else 0)
        ≤ 2 * ENNReal.ofReal B := by
      refine le_trans (ENNReal.tsum_le_tsum hsplit) ?_
      rw [ENNReal.tsum_add]
      calc _ ≤ ENNReal.ofReal B + ENNReal.ofReal B := add_le_add hT1 hT2
        _ = 2 * ENNReal.ofReal B := (two_mul _).symm
    have hTop : ∀ L : ℕ,
        (if lam ≤ |(L : ℝ) - m * n| then (iidSum p n) L else 0) ≠ ∞ := fun L => by
      split_ifs
      · exact PMF.apply_ne_top _ _
      · exact ENNReal.zero_ne_top
    have hlhs : (∑' L : ℕ, if lam ≤ |(L : ℝ) - m * n| then ((iidSum p n) L).toReal else 0)
        = (∑' L : ℕ, if lam ≤ |(L : ℝ) - m * n| then (iidSum p n) L else 0).toReal := by
      rw [ENNReal.tsum_toReal_eq hTop]
      refine tsum_congr fun L => ?_
      rw [apply_ite ENNReal.toReal, ENNReal.toReal_zero]
    rw [hlhs]
    have hfin : (2 : ℝ≥0∞) * ENNReal.ofReal B ≠ ∞ :=
      ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
    calc (∑' L : ℕ, if lam ≤ |(L : ℝ) - m * n| then (iidSum p n) L else 0).toReal
        ≤ ((2 : ℝ≥0∞) * ENNReal.ofReal B).toReal := ENNReal.toReal_mono hfin hchain
      _ = 2 * B := by
          rw [hB, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
          norm_num
      _ ≤ 2 * Gweight (1 + n) (1 / 400 * lam) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact le_trans (Real.exp_le_exp.mpr hexp) (exp_neg_min_le_Gweight hn1 hlam)

/-! ### Tail bounds for `G(μ)`, `P(μ)` (the `G(μ)` version of Tao's Lemma 2.2(ii); GGM §2.1) -/

/-- The `c` of `geomP_tail_bound` (tao-collatz's `c_geomTail`; independent of `p`). -/
noncomputable def c_geomTail : ℝ := 1 / 400

theorem c_geomTail_pos : 0 < c_geomTail := by norm_num [c_geomTail]

/-- The `C` of `geomP_tail_bound` (tao-collatz's `C_geomTail`; independent of `p`). -/
noncomputable def C_geomTail : ℝ := 2

theorem C_geomTail_pos : 0 < C_geomTail := by norm_num [C_geomTail]

/-- **Tail of sums of `G(μ)`** (form with fixed constants): `P(||G(μ)^{(n)}| − μn| ≥ λ) ≤ 2 G_{1+n}(λ/400)`. -/
theorem geomP_tail_bound_atC {p : ℕ} (hp : 2 ≤ p) :
    ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' L : ℕ, if lam ≤ |(L : ℝ) - muP p * n| then ((iidSum (geomP p) n) L).toReal else 0)
        ≤ C_geomTail * Gweight (1 + n) (c_geomTail * lam) := by
  intro n lam hlam
  unfold C_geomTail c_geomTail
  exact iidSum_nat_tail_of_quad (geomP p) (muP p)
    (fun t hlo hhi => le_trans (tiltZ_geomP_le_quad hp hlo hhi)
      (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg t]))) n lam hlam

/-- **The `G(μ)` version of Lemma 2.2(ii)**: `P(||G(μ)^{(n)}| − μn| ≥ λ) ≪ G_n(cλ)` (constants independent of `p`). -/
theorem geomP_tail_bound {p : ℕ} (hp : 2 ≤ p) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' L : ℕ, if lam ≤ |(L : ℝ) - muP p * n| then ((iidSum (geomP p) n) L).toReal else 0)
        ≤ C * Gweight (1 + n) (c * lam) :=
  ⟨c_geomTail, c_geomTail_pos, C_geomTail, C_geomTail_pos, geomP_tail_bound_atC hp⟩

/-- **The `P(μ)` version of Lemma 2.2(ii)** (mean `2μ`). -/
theorem pascalP_tail_bound {p : ℕ} (hp : 2 ≤ p) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' L : ℕ, if lam ≤ |(L : ℝ) - 2 * muP p * n| then ((iidSum (pascalP p) n) L).toReal
          else 0)
        ≤ C * Gweight (1 + n) (c * lam) := by
  refine ⟨1 / 400, by norm_num, 2, by norm_num, fun n lam hlam => ?_⟩
  exact iidSum_nat_tail_of_quad (pascalP p) (2 * muP p)
    (fun t hlo hhi => tiltZ_pascalP_le_quad hp hlo hhi) n lam hlam

/-! ### General one-dimensional local bound (Lemma 2.2(i)) -/

/-- **General one-dimensional Lemma 2.2(i)** (tilted circle method): a walk on ℕ with mean `m ∈ [0, 4]`, the
quadratic moment generating function bound `Z(λ) ≤ 1 + mλ + 1000λ²` for `|λ| ≤ 1/200`, and mass at least `δ`
(`0 < δ ≤ 1/2`) at two adjacent points `a, a+1 ≤ 3` satisfies the local bound with `c = 1/400`, `C = 8/δ²`.
This is tao-collatz's `iidSum_nat_local_of_quad` (`δ = 3/16`, `C = 128`) with the lower bound on the point masses
made general (because for `G(μ)` with `p ≥ 5` the mass `(p-1)/p²` of the second point falls below `3/16`).
The tilted walk keeps mass `≥ δ/2` at the two points (weight `≥ e^{-3/200}`, `Z ≤ 209/200`), and
`charFn_embMod_decay_of_adjacent_atoms` gives the decay constant `c = 1/(4δ²)`. -/
theorem iidSum_nat_local_of_quad (p : PMF ℕ) (m : ℝ) (hm0 : 0 ≤ m) (hm4 : m ≤ 4)
    (hquad : ∀ lam : ℝ, -(1 / 200) ≤ lam → lam ≤ 1 / 200 →
      tiltZ p (expW lam) ≤ ENNReal.ofReal (1 + m * lam + 1000 * lam ^ 2))
    (a : ℕ) (ha3 : a + 1 ≤ 3) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hpa : δ ≤ (p a).toReal) (hpb : δ ≤ (p (a + 1)).toReal)
    (n L : ℕ) :
    ((iidSum p n) L).toReal
      ≤ 8 / δ ^ 2 / Real.sqrt (1 + n) * Gweight (1 + n) (1 / 400 * ((L : ℝ) - m * n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: the point mass at the origin
    rw [iidSum_zero, PMF.pure_apply]
    simp only [Nat.cast_zero, mul_zero, sub_zero]
    split_ifs with h
    · subst h
      rw [ENNReal.toReal_one]
      simp only [Nat.cast_zero]
      rw [Gweight]
      have hδ2 : δ ^ 2 ≤ 1 / 4 := by nlinarith
      have h8 : 1 ≤ 8 / δ ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      norm_num [Real.exp_zero]
      linarith
    · rw [ENNReal.toReal_zero]
      exact mul_nonneg (by positivity) (Gweight_nonneg _ _)
  · have hn1 : 1 ≤ n := hn
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    set dev : ℝ := (L : ℝ) - m * n with hdev
    obtain ⟨lam, hllo, hlhi, hexp⟩ := chernoff_clip_le hn1 dev
    have hZ0 := tiltZ_expW_ne_zero p lam
    have hZq := hquad lam hllo hlhi
    have hZt : tiltZ p (expW lam) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hZq
    set q : PMF ℕ := tilt p (expW lam) hZ0 hZt with hq
    have hZle : (tiltZ p (expW lam)).toReal ≤ 209 / 200 := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hZq
      rw [ENNReal.toReal_ofReal (by nlinarith)] at h
      nlinarith
    have hZpos : 0 < (tiltZ p (expW lam)).toReal := ENNReal.toReal_pos hZ0 hZt
    -- the tilted masses at the two points are at least `δ/2`
    have hatom : ∀ b : ℕ, b ≤ 3 → δ ≤ (p b).toReal → δ / 2 ≤ (q b).toReal := by
      intro b hb3 hpb'
      have hqb : q b = p b * expW lam b * (tiltZ p (expW lam))⁻¹ := rfl
      rw [hqb, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
      have hw : (expW lam b).toReal = Real.exp (lam * b) := by
        rw [expW, ENNReal.toReal_ofReal (Real.exp_pos _).le]
      rw [hw]
      have hb3R : (b : ℝ) ≤ 3 := by exact_mod_cast hb3
      have hbn : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg _
      have harg : -(3 / 200 : ℝ) ≤ lam * b := by nlinarith
      have hwge : (197 / 200 : ℝ) ≤ Real.exp (lam * b) := by
        have h := Real.add_one_le_exp (lam * (b : ℝ))
        linarith [Real.exp_le_exp.mpr harg, Real.add_one_le_exp (-(3 / 200 : ℝ))]
      have hinv : (200 / 209 : ℝ) ≤ ((tiltZ p (expW lam)).toReal)⁻¹ := by
        rw [show (200 / 209 : ℝ) = (209 / 200 : ℝ)⁻¹ from by norm_num]
        gcongr
      have hppos : (0 : ℝ) ≤ (p b).toReal := ENNReal.toReal_nonneg
      calc δ / 2 ≤ δ * (197 / 200) * (200 / 209) := by nlinarith
        _ ≤ (p b).toReal * Real.exp (lam * b) * ((tiltZ p (expW lam)).toReal)⁻¹ := by
            have h1 : δ * (197 / 200) ≤ (p b).toReal * Real.exp (lam * b) :=
              mul_le_mul hpb' hwge (by norm_num) hppos
            have h2 : (0 : ℝ) ≤ (p b).toReal * Real.exp (lam * b) := by positivity
            exact mul_le_mul h1 hinv (by norm_num) h2
    have hqa := hatom a (by omega) hpa
    have hqb := hatom (a + 1) ha3 hpb
    -- the tilted central bound (one-dimensional circle method, decay constant `c = 1/(4δ²)`)
    set cdec : ℝ := 1 / (4 * δ ^ 2) with hcdec
    have hcdec1 : 1 ≤ cdec := by
      rw [hcdec, le_div_iff₀ (by positivity)]
      nlinarith
    have hdec : ∀ (N : ℕ) [NeZero N], 4 ≤ N → ∀ j : ZMod N,
        ‖charFn (q.map (embMod N)) (j, 0)‖ ^ 2 ≤ 1 - ((nd j : ℝ) / N) ^ 2 / cdec := by
      intro N _ hN4 j
      have hma : δ / 2 ≤ ((q.map (embMod N)) (embMod N a)).toReal :=
        le_trans hqa (ENNReal.toReal_mono (PMF.apply_ne_top _ _)
          (PMF.apply_le_map_apply _ _ _))
      have hmb : δ / 2 ≤ ((q.map (embMod N)) (embMod N (a + 1))).toReal :=
        le_trans hqb (ENNReal.toReal_mono (PMF.apply_ne_top _ _)
          (PMF.apply_le_map_apply _ _ _))
      have h := charFn_embMod_decay_of_adjacent_atoms hN4 (q.map (embMod N))
        (μ := δ / 2) (by positivity) a hma hmb j
      have heq : ((nd j : ℝ) / N) ^ 2 / cdec = 16 * (δ / 2) ^ 2 * ((nd j : ℝ) / N) ^ 2 := by
        rw [hcdec]
        field_simp
        ring
      rw [heq]
      exact h
    have hcenter := iidSum_nat_apply_le_center_of_decay q hcdec1 hdec n L
    have h32 : 32 * cdec = 8 / δ ^ 2 := by
      rw [hcdec]
      field_simp
      ring
    rw [h32] at hcenter
    -- the Chernoff bridge
    have hwv0 : expW lam L ≠ 0 := by
      rw [expW]
      exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    have hwvt : expW lam L ≠ ∞ := by
      rw [expW]
      exact ENNReal.ofReal_ne_top
    have key := iidSum_apply_eq_tilt p (expW_zero lam) (expW_add lam)
      hZ0 hZt n L hwv0 hwvt
    have hqZ : tiltZ p (expW lam) ≤ ENNReal.ofReal (Real.exp (m * lam + 1000 * lam ^ 2)) :=
      le_trans hZq (ENNReal.ofReal_le_ofReal (by
        have h := Real.add_one_le_exp (m * lam + 1000 * lam ^ 2)
        linarith))
    have hBpow : tiltZ p (expW lam) ^ n
        ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * (m * lam + 1000 * lam ^ 2))) := by
      calc tiltZ p (expW lam) ^ n
          ≤ ENNReal.ofReal (Real.exp (m * lam + 1000 * lam ^ 2)) ^ n := by gcongr
        _ = ENNReal.ofReal (Real.exp (m * lam + 1000 * lam ^ 2) ^ n) :=
            (ENNReal.ofReal_pow (Real.exp_pos _).le n).symm
        _ = ENNReal.ofReal (Real.exp ((n : ℝ) * (m * lam + 1000 * lam ^ 2))) := by
            rw [← Real.exp_nat_mul]
    have hB : ((tiltZ p (expW lam)) ^ n).toReal
        ≤ Real.exp ((n : ℝ) * (m * lam + 1000 * lam ^ 2)) := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hBpow
      rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at h
    have hCeq : ((expW lam L)⁻¹).toReal = Real.exp (-(lam * L)) := by
      rw [expW, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg,
        ENNReal.toReal_ofReal (Real.exp_pos _).le]
    have hsq0 : (0 : ℝ) < Real.sqrt (1 + (n : ℝ)) := Real.sqrt_pos.mpr (by positivity)
    have hbridge : ((iidSum p n) L).toReal
        ≤ 8 / δ ^ 2 / Real.sqrt (1 + n)
          * Real.exp (1000 * n * lam ^ 2 - lam * dev) := by
      rw [key, ENNReal.toReal_mul, ENNReal.toReal_mul, hCeq]
      have hEeq : (n : ℝ) * (m * lam + 1000 * lam ^ 2) + -(lam * L)
          = 1000 * n * lam ^ 2 - lam * dev := by
        rw [hdev]
        ring
      calc ((iidSum q n) L).toReal * ((tiltZ p (expW lam)) ^ n).toReal
            * Real.exp (-(lam * L))
          ≤ (8 / δ ^ 2 / Real.sqrt (1 + n)
              * Real.exp ((n : ℝ) * (m * lam + 1000 * lam ^ 2)))
              * Real.exp (-(lam * L)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            exact mul_le_mul hcenter hB ENNReal.toReal_nonneg (by positivity)
        _ = 8 / δ ^ 2 / Real.sqrt (1 + n)
              * Real.exp (1000 * n * lam ^ 2 - lam * dev) := by
            rw [mul_assoc, ← Real.exp_add, hEeq]
    -- optimizing the exponent and matching it to `Gweight`
    have hGw : Real.exp (1000 * n * lam ^ 2 - lam * dev)
        ≤ Gweight (1 + n) (1 / 400 * dev) := by
      have h1 := Real.exp_le_exp.mpr hexp
      have h2 : Real.exp (-min (dev ^ 2 / (4000 * n)) (|dev| / 400))
          ≤ Gweight (1 + n) (1 / 400 * |dev|) := by
        have h := exp_neg_min_le_Gweight hn1 (abs_nonneg dev)
        rwa [sq_abs] at h
      have h3 : Gweight (1 + n) (1 / 400 * |dev|) = Gweight (1 + n) (1 / 400 * dev) := by
        rw [show (1 / 400 : ℝ) * |dev| = |1 / 400 * dev| from by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 400)],
          Gweight_abs]
      rw [← h3]
      exact le_trans h1 h2
    calc ((iidSum p n) L).toReal
        ≤ 8 / δ ^ 2 / Real.sqrt (1 + n) * Real.exp (1000 * n * lam ^ 2 - lam * dev) :=
          hbridge
      _ ≤ 8 / δ ^ 2 / Real.sqrt (1 + n) * Gweight (1 + n) (1 / 400 * dev) :=
          mul_le_mul_of_nonneg_left hGw (by positivity)

/-! ### Local bounds for `G(μ)`, `P(μ)` (the `G(μ)` version of Tao's Lemma 2.2(i)) -/

/-- The masses of `G(μ)` at 1 and 2 are at least `(p-1)/p²`. -/
theorem geomP_toReal_one_two_ge {p : ℕ} (hp : 2 ≤ p) :
    ((p : ℝ) - 1) / (p : ℝ) ^ 2 ≤ (geomP p 1).toReal ∧
      ((p : ℝ) - 1) / (p : ℝ) ^ 2 ≤ (geomP p 2).toReal := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hP0 : (0 : ℝ) < p := by linarith
  rw [geomP_toReal hp, geomP_toReal hp, if_neg (by omega), if_neg (by omega)]
  constructor
  · rw [pow_one, div_le_iff₀ (by positivity)]
    have : ((p : ℝ) - 1) * ((p : ℝ)⁻¹) * (p : ℝ) ^ 2 = ((p : ℝ) - 1) * p := by
      field_simp
    rw [this]
    nlinarith
  · rw [inv_pow]
    exact le_of_eq (div_eq_mul_inv _ _)

/-- **The `G(μ)` version of Lemma 2.2(i)**: `P(|G(μ)^{(n)}| = L) ≪ (n+1)^{-1/2} G_n(c(L − μn))`
(`c = 1/400`, `C = 8p⁴/(p-1)²`; depends on `p`). -/
theorem geomP_local_bound {p : ℕ} (hp : 2 ≤ p) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n L : ℕ),
      ((iidSum (geomP p) n) L).toReal
        ≤ C / Real.sqrt (1 + n) * Gweight (1 + n) (c * ((L : ℝ) - muP p * n)) := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp
  set δ : ℝ := ((p : ℝ) - 1) / (p : ℝ) ^ 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; apply div_pos <;> nlinarith
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδ, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨h1, h2⟩ := geomP_toReal_one_two_ge hp
  refine ⟨1 / 400, by norm_num, 8 / δ ^ 2, by positivity, fun n L => ?_⟩
  exact iidSum_nat_local_of_quad (geomP p) (muP p) (muP_pos hp).le (by linarith [muP_le_two hp])
    (fun t hlo hhi => le_trans (tiltZ_geomP_le_quad hp hlo hhi)
      (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg t])))
    1 (by omega) δ hδ0 hδ1 h1 h2 n L

/-- The masses of `P(μ)` at 2 and 3 are at least `(p-1)²/p³`. -/
theorem pascalP_toReal_two_three_ge {p : ℕ} (hp : 2 ≤ p) :
    ((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ 3 ≤ (pascalP p 2).toReal ∧
      ((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ 3 ≤ (pascalP p 3).toReal := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hP0 : (0 : ℝ) < p := by linarith
  have hcast : (((p - 1 : ℕ) : ℝ≥0∞)).toReal = (p : ℝ) - 1 := by
    rw [ENNReal.toReal_natCast, Nat.cast_sub (by omega), Nat.cast_one]
  have hform : ∀ b : ℕ, 2 ≤ b → (pascalP p b).toReal
      = ((b : ℝ) - 1) * ((p : ℝ) - 1) ^ 2 * ((p : ℝ)⁻¹) ^ b := by
    intro b hb
    rw [pascalP_apply hp, if_neg (by omega), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      hcast, ENNReal.toReal_natCast, Nat.cast_sub (by omega), Nat.cast_one]
  rw [hform 2 le_rfl, hform 3 (by norm_num)]
  constructor
  · rw [div_le_iff₀ (by positivity)]
    have : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
    rw [this]
    have hkey : 1 * ((p : ℝ) - 1) ^ 2 * ((p : ℝ)⁻¹) ^ 2 * (p : ℝ) ^ 3
        = ((p : ℝ) - 1) ^ 2 * p := by
      field_simp
    rw [hkey]
    nlinarith [sq_nonneg ((p : ℝ) - 1)]
  · rw [div_le_iff₀ (by positivity)]
    have hkey : (((3 : ℕ) : ℝ) - 1) * ((p : ℝ) - 1) ^ 2 * ((p : ℝ)⁻¹) ^ 3 * (p : ℝ) ^ 3
        = 2 * ((p : ℝ) - 1) ^ 2 := by
      field_simp
      norm_num
      ring
    rw [hkey]
    nlinarith [sq_nonneg ((p : ℝ) - 1)]

/-- **The `P(μ)` version of Lemma 2.2(i)** (mean `2μ`, `c = 1/400`, `C = 8p⁶/(p-1)⁴`). -/
theorem pascalP_local_bound {p : ℕ} (hp : 2 ≤ p) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n L : ℕ),
      ((iidSum (pascalP p) n) L).toReal
        ≤ C / Real.sqrt (1 + n) * Gweight (1 + n) (c * ((L : ℝ) - 2 * muP p * n)) := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp
  set δ : ℝ := ((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ 3 with hδ
  have hδ0 : 0 < δ := by
    rw [hδ]; apply div_pos
    · have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    · positivity
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδ, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((p : ℝ) - 1), sq_nonneg (p : ℝ)]
  obtain ⟨h1, h2⟩ := pascalP_toReal_two_three_ge hp
  refine ⟨1 / 400, by norm_num, 8 / δ ^ 2, by positivity, fun n L => ?_⟩
  have hmu := muP_le_two hp
  have hmu0 := (muP_pos hp).le
  exact iidSum_nat_local_of_quad (pascalP p) (2 * muP p) (by linarith) (by linarith)
    (fun t hlo hhi => tiltZ_pascalP_le_quad hp hlo hhi)
    2 (by omega) δ hδ0 hδ1 h1 h2 n L

end GGMCollatz
