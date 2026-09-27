import GGMCollatz.NatDen.UProf.DKern.Asym

/-!
# Pieces of the main body of (DK) (1): the Gaussian mass of the central window, and the tail outside the window

Notation as in `Asym.lean` (`t = L^{1/20}`, window `J = [⌊c - t^{11}⌋, ⌈c + t^{11}⌉)`, `c ∈ [c₁t^{20}, t^{20}]`).

* `W_piece` ((E3)): `|Σ_J g - μ/(μ-λ)| ≤ K/t^8`.
* `T_piece` ((c)): `Phi(k) ≤ 1/t^{22}` on the rows outside the window (Chernoff, `Hs_tail`).
-/

namespace GGMCollatz

namespace ND

namespace DKernAux

/-- A sum over the window as a sum over `range`. -/
theorem Wt_eq_range (p : ℕ) (lam c t : ℝ) :
    Wt p lam c t = ∑ i ∈ Finset.range (jb c t - ja c t),
      gau (gA p c) (gB p lam c) c ((ja c t : ℝ) + i) := by
  unfold Wt gg
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast; rfl

/-- **(E3)**: the Gaussian mass of the central window is `μ/(μ-λ) + O(t^{-8})`. -/
theorem W_piece {p : ℕ} (hp : 2 ≤ p) {lam : ℝ} (hlam : lam < muP p) {c₁ : ℝ} (hc₁ : 0 < c₁) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t : ℝ in Filter.atTop, ∀ c : ℝ, c₁ * t ^ 20 ≤ c → c ≤ t ^ 20 →
      |Wt p lam c t - muP p / (muP p - lam)| ≤ K / t ^ 8 := by
  have hσ := sig2_pos hp
  have hμ := muP_pos hp
  have hdl : 0 < muP p - lam := by linarith
  set A₀ := muP p / Real.sqrt (2 * Real.pi * sig2 p * c₁) with hA₀
  set B₀ := (muP p - lam) ^ 2 / (2 * sig2 p * c₁) with hB₀
  set B₁ := (muP p - lam) ^ 2 / (2 * sig2 p) with hB₁
  have hA₀0 : 0 < A₀ := by positivity
  have hB₀0 : 0 < B₀ := by positivity
  have hB₁0 : 0 < B₁ := by positivity
  refine ⟨16 * A₀ * B₀ + 1, by positivity, ?_⟩
  have hev1 := exp_small (show 0 < B₁ / 2 by positivity) (Real.sqrt 2 * (muP p / (muP p - lam))) 8
  have hev2 : ∀ᶠ t : ℝ in Filter.atTop, 2 ≤ c₁ * t ^ 9 := by
    have h := (Filter.tendsto_pow_atTop (n := 9) (by norm_num)).const_mul_atTop hc₁
    exact h.eventually_ge_atTop 2
  filter_upwards [hev1, hev2, Filter.eventually_ge_atTop 1] with t h1 h2 ht1 c hc1 hc2
  have ht0 : 0 < t := by linarith
  set R := t ^ 11 with hR
  have hR1 : 1 ≤ R := one_le_pow₀ ht1
  have hcR : c₁ * t ^ 20 = c₁ * t ^ 9 * R := by rw [hR]; ring
  have hwin : 0 ≤ c - R := by nlinarith
  have hc0 : 0 < c := by linarith
  set A := gA p c with hA
  set B := gB p lam c with hB
  have hApos : 0 < A := gA_pos hp hc0
  have hBpos : 0 < B := gB_pos hp hlam hc0
  have hAle : A ≤ A₀ / t ^ 10 := gA_le hp hc₁ ht0 hc1
  have hBle : B ≤ B₀ / t ^ 20 := gB_le hp hc₁ ht0 hc1
  have hBge : B₁ / t ^ 20 ≤ B := gB_ge hp hc0 hc2
  -- the hypotheses of `gau_sum`
  have hjab := ja_le_jb ht0.le hwin
  have hN : (((jb c t - ja c t : ℕ)) : ℝ) = jb c t - ja c t := by rw [Nat.cast_sub hjab]
  have h1a := ja_le hwin
  have h2a := ja_gt (c := c) (t := t)
  have h1b := jb_ge (c := c) (t := t)
  have h2b := jb_lt (c := c) (t := t) (by linarith)
  have hs := gau_sum (A := A) (B := B) (c := c) (R := R) (a := (ja c t : ℝ)) (jb c t - ja c t)
    hApos.le hBpos (by linarith) (by linarith) h1a (by rw [hN]; linarith) (by rw [hN]; linarith)
  rw [← Wt_eq_range, gA_mul_sqrt hp hlam hc0, gA_mul_sqrt2 hp hlam hc0] at hs
  refine le_trans hs ?_
  -- first term
  have hNle : ((jb c t - ja c t : ℕ) : ℝ) ≤ 4 * R := by rw [hN]; linarith
  have hterm1 : ((jb c t - ja c t : ℕ) : ℝ) * (A * B * (2 * R + 2)) ≤ 16 * A₀ * B₀ / t ^ 8 := by
    calc ((jb c t - ja c t : ℕ) : ℝ) * (A * B * (2 * R + 2))
        ≤ (4 * R) * ((A₀ / t ^ 10) * (B₀ / t ^ 20) * (4 * R)) := by
          gcongr
          linarith
      _ = 16 * A₀ * B₀ / t ^ 8 := by
          rw [hR]; field_simp; norm_num
  -- second term
  have hexp : Real.exp (-(B * R ^ 2 / 2)) ≤ Real.exp (-(B₁ / 2 * t ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have : B₁ * t ^ 2 ≤ B * R ^ 2 := by
      have e : B₁ * t ^ 2 = B₁ / t ^ 20 * R ^ 2 := by rw [hR]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right hBge (sq_nonneg _)
    linarith
  have hterm2 : Real.sqrt 2 * (muP p / (muP p - lam)) * Real.exp (-(B * R ^ 2 / 2)) ≤ 1 / t ^ 8 := by
    rw [le_div_iff₀ (by positivity)]
    calc Real.sqrt 2 * (muP p / (muP p - lam)) * Real.exp (-(B * R ^ 2 / 2)) * t ^ 8
        ≤ Real.sqrt 2 * (muP p / (muP p - lam)) * Real.exp (-(B₁ / 2 * t ^ 2)) * t ^ 8 := by
          gcongr
      _ = Real.sqrt 2 * (muP p / (muP p - lam)) * t ^ 8 * Real.exp (-(B₁ / 2 * t ^ 2)) := by ring
      _ ≤ 1 := h1
  have e : (16 * A₀ * B₀ + 1) / t ^ 8 = 16 * A₀ * B₀ / t ^ 8 + 1 / t ^ 8 := by ring
  rw [e]
  linarith

/-- **The tail in (c)**: `Phi(k) ≤ 1/t^{22}` on the rows outside the window. -/
theorem T_piece {p : ℕ} (hp : 2 ≤ p) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < muP p) {c₁ : ℝ}
    (hc₁ : 0 < c₁) :
    ∀ᶠ t : ℝ in Filter.atTop, ∀ u c : ℝ, c = u / (muP p - lam) → c₁ * t ^ 20 ≤ c → c ≤ t ^ 20 →
      ∀ k : ℕ, 1 ≤ k → k ∉ Finset.Ico (ja c t) (jb c t) → (k : ℝ) ≤ t ^ 20 →
        Phi p lam u k ≤ 1 / t ^ 22 := by
  obtain ⟨cG, hcG, CG, hCG, htail⟩ := Hs_tail hp
  have hdl : 0 < muP p - lam := by linarith
  set dl := muP p - lam with hdldef
  set a := min (cG ^ 2 * dl ^ 2 / 8) (cG * dl / 2) with hadef
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have hev1 := exp_small ha (2 * CG * (lam + dl)) 42
  have hev2 : ∀ᶠ t : ℝ in Filter.atTop, 2 ≤ c₁ * t ^ 9 := by
    have h := (Filter.tendsto_pow_atTop (n := 9) (by norm_num)).const_mul_atTop hc₁
    exact h.eventually_ge_atTop 2
  have hev3 : ∀ᶠ t : ℝ in Filter.atTop, 2 ≤ dl * t ^ 11 := by
    have h := (Filter.tendsto_pow_atTop (n := 11) (by norm_num)).const_mul_atTop hdl
    exact h.eventually_ge_atTop 2
  filter_upwards [hev1, hev2, hev3, Filter.eventually_ge_atTop 1] with t h1 h2 h3 ht1
  intro u c hcu hc1 hc2 k hk hkJ hkt
  have ht0 : 0 < t := by linarith
  have hR1 : 1 ≤ t ^ 11 := one_le_pow₀ ht1
  have hwin : 0 ≤ c - t ^ 11 := by nlinarith
  have hc0 : 0 < c := by linarith
  have hu : u = dl * c := by rw [hcu]; field_simp
  have hu0 : 0 < u := by rw [hu]; positivity
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 ≤ (k : ℝ) * lam + u := by positivity
  set S := fl lam u k with hSdef
  set θ := th lam u k with hθdef
  have hθ0 : 0 ≤ θ := th_nonneg hpos
  have hθ1 : θ < 1 := th_lt_one lam u k
  have hSeq : (S : ℝ) = k * lam + u - θ := by rw [hθdef]; unfold th; rw [← hSdef]; ring
  -- `Phi ≤ Hs`
  have hPhi : Phi p lam u k ≤ Hs p k S := by
    unfold Phi
    rw [← hSdef, ← hθdef]
    have : Real.exp (-θ * Real.log p) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := Real.log_nonneg (show (1 : ℝ) ≤ p by exact_mod_cast (by omega : 1 ≤ p))
      nlinarith
    calc Real.exp (-θ * Real.log p) * Hs p k S ≤ 1 * Hs p k S :=
          mul_le_mul_of_nonneg_right this (Hs_nonneg _ _ _)
      _ = Hs p k S := one_mul _
  -- `S/k ≤ (λ + μ - λ) t^{20}`
  have hSk : (S : ℝ) / k ≤ (lam + dl) * t ^ 20 := by
    rw [div_le_iff₀ hk0]
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have ht20 : 1 ≤ t ^ 20 := one_le_pow₀ ht1
    have : u ≤ dl * t ^ 20 := by rw [hu]; exact mul_le_mul_of_nonneg_left hc2 hdl.le
    have e2 : dl * t ^ 20 ≤ k * (dl * t ^ 20) := le_mul_of_one_le_left (by positivity) hk1
    have e3 : k * lam ≤ k * lam * t ^ 20 := le_mul_of_one_le_right (by positivity) ht20
    have e4 : (lam + dl) * t ^ 20 * k = k * lam * t ^ 20 + k * (dl * t ^ 20) := by ring
    linarith
  -- lower bound for the deviation
  have hdev : cG * dl * t ^ 11 / 2 ≤ |cG * ((S : ℝ) - muP p * k)| := by
    have hkc := le_abs_sub_of_not_mem hwin hkJ
    have e : (S : ℝ) - muP p * k = dl * (c - k) - θ := by rw [hSeq, hu, hdldef]; ring
    rw [e, abs_mul, abs_of_pos hcG]
    have h4 : dl * t ^ 11 - 1 ≤ |dl * (c - k) - θ| := by
      have : dl * t ^ 11 ≤ |dl * (c - k)| := by
        rw [abs_mul, abs_of_pos hdl, abs_sub_comm]
        exact mul_le_mul_of_nonneg_left hkc hdl.le
      have := abs_sub_abs_le_abs_sub (dl * (c - k)) θ
      rw [abs_of_nonneg hθ0] at this
      linarith
    have : dl * t ^ 11 / 2 ≤ |dl * (c - k) - θ| := by linarith
    calc cG * dl * t ^ 11 / 2 = cG * (dl * t ^ 11 / 2) := by ring
      _ ≤ cG * |dl * (c - k) - θ| := mul_le_mul_of_nonneg_left this hcG.le
  -- `Gweight ≤ 2 e^{-at²}`
  have hG : Gweight (1 + k) (cG * ((S : ℝ) - muP p * k)) ≤ 2 * Real.exp (-(a * t ^ 2)) := by
    unfold Gweight
    set x := cG * ((S : ℝ) - muP p * k) with hx
    have hX0 : 0 ≤ cG * dl * t ^ 11 / 2 := by positivity
    have ht2 : t ^ 2 ≤ t ^ 11 := pow_le_pow_right₀ ht1 (by norm_num)
    have hq1 : a * t ^ 2 ≤ x ^ 2 / (1 + k) := by
      have hx2 : (cG * dl * t ^ 11 / 2) ^ 2 ≤ x ^ 2 := by
        rw [← sq_abs x]; exact pow_le_pow_left₀ hX0 hdev 2
      have hden : 1 + (k : ℝ) ≤ 2 * t ^ 20 := by
        have : 1 ≤ t ^ 20 := one_le_pow₀ ht1
        linarith
      have e : (cG * dl * t ^ 11 / 2) ^ 2 = cG ^ 2 * dl ^ 2 / 8 * t ^ 2 * (2 * t ^ 20) := by ring
      rw [le_div_iff₀ (by positivity)]
      have ha1 : a ≤ cG ^ 2 * dl ^ 2 / 8 := min_le_left _ _
      calc a * t ^ 2 * (1 + k) ≤ cG ^ 2 * dl ^ 2 / 8 * t ^ 2 * (2 * t ^ 20) := by
            gcongr
        _ = (cG * dl * t ^ 11 / 2) ^ 2 := e.symm
        _ ≤ x ^ 2 := hx2
    have hq2 : a * t ^ 2 ≤ |x| := by
      have ha2 : a ≤ cG * dl / 2 := min_le_right _ _
      calc a * t ^ 2 ≤ cG * dl / 2 * t ^ 11 := by gcongr
        _ = cG * dl * t ^ 11 / 2 := by ring
        _ ≤ |x| := hdev
    have e1 : Real.exp (-x ^ 2 / (1 + k)) ≤ Real.exp (-(a * t ^ 2)) := by
      apply Real.exp_le_exp.mpr; rw [neg_div]; linarith
    have e2 : Real.exp (-|x|) ≤ Real.exp (-(a * t ^ 2)) := Real.exp_le_exp.mpr (by linarith)
    linarith
  -- assembly
  have hS0 : 0 ≤ (S : ℝ) / k := by positivity
  have hmain : Phi p lam u k ≤ (lam + dl) * t ^ 20 * CG * (2 * Real.exp (-(a * t ^ 2))) := by
    refine le_trans hPhi (le_trans (htail k S hk) ?_)
    have := Gweight_nonneg (1 + k) (cG * ((S : ℝ) - muP p * k))
    calc (S : ℝ) / k * CG * Gweight (1 + k) (cG * ((S : ℝ) - muP p * k))
        ≤ (lam + dl) * t ^ 20 * CG * Gweight (1 + k) (cG * ((S : ℝ) - muP p * k)) := by
          gcongr
      _ ≤ (lam + dl) * t ^ 20 * CG * (2 * Real.exp (-(a * t ^ 2))) := by
          gcongr
  refine le_trans hmain ?_
  rw [le_div_iff₀ (by positivity)]
  calc (lam + dl) * t ^ 20 * CG * (2 * Real.exp (-(a * t ^ 2))) * t ^ 22
      = 2 * CG * (lam + dl) * t ^ 42 * Real.exp (-(a * t ^ 2)) := by ring
    _ ≤ 1 := h1

end DKernAux

end ND

end GGMCollatz
