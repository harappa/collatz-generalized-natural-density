import GGMCollatz.NatDen.UProf.DKern.PiecesA

/-!
# Pieces of the main body of (DK) (2): comparison with the Gauss envelope in the central window ((E1))

`E_piece`: on each row of the window `J`, `|Hs(k, ⌊kλ+u⌋) - g(k)| ≤ (K/t^7) g(k)`. We feed (LCLT) (`|S - μk| ≤ k^{3/5}`)
into `env_rel`. From `k ≥ κt^{20}` (`κ = c₁/2`), `|k - c| ≤ 2t^{11}`, `|S - μk| ≤ D₀t^{11}` (`D₀ = 2(μ-λ)+1`),
each of the four relative errors is `O(t^{-7})` (the worst are `|S - μk|³/k² ≍ t^{33-40}` and `(k-c)³/(ck) ≍ t^{33-40}`).
-/

namespace GGMCollatz

namespace ND

namespace DKernAux

/-- If `k ≥ κ t^{20}`, then `k^{-1/2} ≤ (1/√κ)/t^{10}`. -/
theorem rpow_neg_half_le {κ t k : ℝ} (hκ : 0 < κ) (ht : 0 < t) (hk : κ * t ^ 20 ≤ k) :
    k ^ (-(1 / 2 : ℝ)) ≤ 1 / Real.sqrt κ / t ^ 10 := by
  have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk
  rw [Real.rpow_neg hk0.le, ← Real.sqrt_eq_rpow, div_div, one_div]
  apply inv_anti₀ (by positivity)
  have e : Real.sqrt κ * t ^ 10 = Real.sqrt (κ * t ^ 20) := by
    rw [show κ * t ^ 20 = κ * (t ^ 10) ^ 2 by ring, Real.sqrt_mul hκ.le,
      Real.sqrt_sq (by positivity)]
  rw [e]
  exact Real.sqrt_le_sqrt hk

/-- If `k ≥ κ t^{20}`, then `κ^{3/5} t^{12} ≤ k^{3/5}`. -/
theorem rpow_three_fifths_ge {κ t k : ℝ} (hκ : 0 < κ) (ht : 0 < t) (hk : κ * t ^ 20 ≤ k) :
    κ ^ (3 / 5 : ℝ) * t ^ 12 ≤ k ^ (3 / 5 : ℝ) := by
  have h := Real.rpow_le_rpow (by positivity) hk (show (0 : ℝ) ≤ 3 / 5 by norm_num)
  refine le_trans (le_of_eq ?_) h
  rw [Real.mul_rpow hκ.le (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  norm_num

set_option maxHeartbeats 1000000 in
/-- **(E1)**: comparison of `Hs` with the Gauss envelope in the central window. -/
theorem E_piece {p : ℕ} (hp : 2 ≤ p) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < muP p)
    (hL : lclt_statement p) {c₁ : ℝ} (hc₁ : 0 < c₁) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t : ℝ in Filter.atTop, ∀ u c : ℝ, c = u / (muP p - lam) →
      c₁ * t ^ 20 ≤ c → c ≤ t ^ 20 → ∀ k ∈ Finset.Ico (ja c t) (jb c t),
        |Hs p k (fl lam u k) - gg p lam c k| ≤ K / t ^ 7 * gg p lam c k := by
  obtain ⟨CL, hCL, hlclt⟩ := hL
  have hσ := sig2_pos hp
  have hμ1 := one_lt_muP hp
  have hdl : 0 < muP p - lam := by linarith
  set μ := muP p with hμdef
  set σ2 := sig2 p with hσdef
  set dl := μ - lam with hdldef
  set κ := c₁ / 2 with hκdef
  have hκ : 0 < κ := by positivity
  set D₀ := 2 * dl + 1 with hD₀
  have hD₀0 : 0 < D₀ := by positivity
  set K₁ := CL * (1 / Real.sqrt κ + D₀ ^ 3 / κ ^ 2) with hK₁
  set K₂ := D₀ / κ with hK₂
  set K₃ := 2 / κ with hK₃
  set K₄ := (8 * dl ^ 2 / c₁ + 4 * dl + 1) / (2 * σ2 * κ) with hK₄
  have hK₁0 : 0 < K₁ := by positivity
  have hK₂0 : 0 < K₂ := by positivity
  have hK₃0 : 0 < K₃ := by positivity
  have hK₄0 : 0 < K₄ := by positivity
  refine ⟨8 * (K₁ + K₂ + K₃ + K₄), by positivity, ?_⟩
  have hev1 : ∀ᶠ t : ℝ in Filter.atTop, 4 ≤ c₁ * t ^ 9 := by
    have h := (Filter.tendsto_pow_atTop (n := 9) (by norm_num)).const_mul_atTop hc₁
    exact h.eventually_ge_atTop 4
  have hev2 : ∀ᶠ t : ℝ in Filter.atTop, 2 * (K₁ + K₂ + K₃ + K₄) ≤ t ^ 7 :=
    (Filter.tendsto_pow_atTop (n := 7) (by norm_num)).eventually_ge_atTop _
  have hev3 : ∀ᶠ t : ℝ in Filter.atTop, D₀ ≤ κ ^ (3 / 5 : ℝ) * t := by
    have h := Filter.tendsto_id.const_mul_atTop (Real.rpow_pos_of_pos hκ (3 / 5 : ℝ))
    exact h.eventually_ge_atTop D₀
  filter_upwards [hev1, hev2, hev3, Filter.eventually_ge_atTop 1] with t h1 h2 h3 ht1
  intro u c hcu hc1 hc2 k hk
  have ht0 : 0 < t := by linarith
  have ht7 : 0 < t ^ 7 := by positivity
  have hR1 : 1 ≤ t ^ 11 := one_le_pow₀ ht1
  have hwin : 0 ≤ c - t ^ 11 := by nlinarith
  have hc0 : 0 < c := by linarith
  have hu : u = dl * c := by rw [hcu]; field_simp
  -- size of the rows in the window
  have hkc := abs_sub_lt_of_mem ht0.le hk
  have hkc2 : |(k : ℝ) - c| ≤ 2 * t ^ 11 := by linarith
  have hkκ : κ * t ^ 20 ≤ k := by
    have : c - t ^ 11 - 1 ≤ k := by
      have := (abs_lt.mp hkc).1; linarith
    have e : c₁ * t ^ 20 = c₁ * t ^ 9 * t ^ 11 := by ring
    have : 2 * t ^ 11 ≤ κ * t ^ 20 := by
      rw [hκdef, show c₁ / 2 * t ^ 20 = c₁ * t ^ 9 * t ^ 11 / 2 by ring]; nlinarith
    have : κ * t ^ 20 = c₁ * t ^ 20 / 2 := by rw [hκdef]; ring
    linarith
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hkκ
  have hk1 : 1 ≤ k := by exact_mod_cast hk0
  have hpos : 0 ≤ (k : ℝ) * lam + u := by rw [hu]; positivity
  set S := fl lam u k with hSdef
  set θ := th lam u k with hθdef
  have hθ0 : 0 ≤ θ := th_nonneg hpos
  have hθ1 : θ < 1 := th_lt_one lam u k
  have hS : (S : ℝ) = k * lam + (μ - lam) * c - θ := by
    rw [hθdef]; unfold th; rw [← hSdef, ← hdldef, ← hu]; ring
  -- `|S - μk| ≤ D₀ t^{11}`
  have hδ : |(S : ℝ) - μ * k| ≤ D₀ * t ^ 11 := by
    have e : (S : ℝ) - μ * k = dl * (c - k) - θ := by rw [hS, hdldef]; ring
    rw [e]
    calc |dl * (c - k) - θ| ≤ |dl * (c - k)| + |θ| := abs_sub _ _
      _ = dl * |(k : ℝ) - c| + θ := by
          rw [abs_mul, abs_of_pos hdl, abs_sub_comm, abs_of_nonneg hθ0]
      _ ≤ dl * (2 * t ^ 11) + 1 := by gcongr
      _ ≤ D₀ * t ^ 11 := by rw [hD₀]; nlinarith
  -- (LCLT)
  have happ : |(S : ℝ) - muP p * k| ≤ (k : ℝ) ^ (3 / 5 : ℝ) := by
    refine le_trans hδ (le_trans ?_ (rpow_three_fifths_ge hκ ht0 hkκ))
    calc D₀ * t ^ 11 ≤ κ ^ (3 / 5 : ℝ) * t * t ^ 11 := by gcongr
      _ = κ ^ (3 / 5 : ℝ) * t ^ 12 := by ring
  have hl := hlclt k hk1 S happ
  set e₁ := CL * ((k : ℝ) ^ (-(1 / 2 : ℝ)) + |(S : ℝ) - μ * k| ^ 3 / (k : ℝ) ^ 2) with he₁
  have hl' : |nb p k S - gauss p k S| ≤ e₁ * gauss p k S := by
    rw [he₁]; linarith [hl]
  -- the four relative errors
  have hb1 : e₁ ≤ K₁ / t ^ 7 := by
    have ha : (k : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / Real.sqrt κ / t ^ 7 := by
      refine le_trans (rpow_neg_half_le hκ ht0 hkκ) ?_
      apply div_le_div_of_nonneg_left (by positivity) ht7
      exact pow_le_pow_right₀ ht1 (by norm_num)
    have hb : |(S : ℝ) - μ * k| ^ 3 / (k : ℝ) ^ 2 ≤ D₀ ^ 3 / κ ^ 2 / t ^ 7 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h3' : |(S : ℝ) - μ * k| ^ 3 ≤ (D₀ * t ^ 11) ^ 3 :=
        pow_le_pow_left₀ (abs_nonneg _) hδ 3
      have hk2 : (κ * t ^ 20) ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hkκ 2
      calc |(S : ℝ) - μ * k| ^ 3 * t ^ 7 ≤ (D₀ * t ^ 11) ^ 3 * t ^ 7 := by
            gcongr
        _ = D₀ ^ 3 / κ ^ 2 * (κ * t ^ 20) ^ 2 := by field_simp
        _ ≤ D₀ ^ 3 / κ ^ 2 * (k : ℝ) ^ 2 := by gcongr
    rw [he₁, hK₁]
    calc CL * ((k : ℝ) ^ (-(1 / 2 : ℝ)) + |(S : ℝ) - μ * k| ^ 3 / (k : ℝ) ^ 2)
        ≤ CL * (1 / Real.sqrt κ / t ^ 7 + D₀ ^ 3 / κ ^ 2 / t ^ 7) := by gcongr
      _ = CL * (1 / Real.sqrt κ + D₀ ^ 3 / κ ^ 2) / t ^ 7 := by ring
  have hb2 : |(S : ℝ) - μ * k| / (μ * k) ≤ K₂ / t ^ 7 := by
    rw [div_le_div_iff₀ (by positivity) ht7]
    have ht11 : t ^ 7 * t ^ 11 ≤ t ^ 20 := by
      rw [← pow_add]; exact pow_le_pow_right₀ ht1 (by norm_num)
    calc |(S : ℝ) - μ * k| * t ^ 7 ≤ D₀ * t ^ 11 * t ^ 7 := by gcongr
      _ = D₀ * (t ^ 7 * t ^ 11) := by ring
      _ ≤ D₀ * t ^ 20 := by gcongr
      _ = K₂ * (1 * (κ * t ^ 20)) := by rw [hK₂]; field_simp
      _ ≤ K₂ * (μ * k) := by gcongr
  have hb3 : |c - (k : ℝ)| / k ≤ K₃ / t ^ 7 := by
    rw [div_le_div_iff₀ hk0 ht7, abs_sub_comm]
    have ht11 : t ^ 7 * t ^ 11 ≤ t ^ 20 := by
      rw [← pow_add]; exact pow_le_pow_right₀ ht1 (by norm_num)
    calc |(k : ℝ) - c| * t ^ 7 ≤ 2 * t ^ 11 * t ^ 7 := by gcongr
      _ = 2 * (t ^ 7 * t ^ 11) := by ring
      _ ≤ 2 * t ^ 20 := by gcongr
      _ = K₃ * (κ * t ^ 20) := by rw [hK₃]; field_simp
      _ ≤ K₃ * k := by gcongr
  have hb4 : e4 dl σ2 c k ≤ K₄ / t ^ 7 := by
    unfold e4
    rw [div_le_div_iff₀ (by positivity) ht7]
    have hc3 : |(k : ℝ) - c| ^ 3 / c ≤ 8 * t ^ 13 / c₁ := by
      rw [div_le_div_iff₀ hc0 hc₁]
      have h3' : |(k : ℝ) - c| ^ 3 ≤ (2 * t ^ 11) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hkc2 3
      calc |(k : ℝ) - c| ^ 3 * c₁ ≤ (2 * t ^ 11) ^ 3 * c₁ := by gcongr
        _ = 8 * t ^ 13 * (c₁ * t ^ 20) := by ring
        _ ≤ 8 * t ^ 13 * c := by gcongr
    have ht1113 : t ^ 11 ≤ t ^ 13 := pow_le_pow_right₀ ht1 (by norm_num)
    have ht13 : 1 ≤ t ^ 13 := one_le_pow₀ ht1
    have hnum : dl ^ 2 * |(k : ℝ) - c| ^ 3 / c + 2 * dl * |(k : ℝ) - c| + 1
        ≤ (8 * dl ^ 2 / c₁ + 4 * dl + 1) * t ^ 13 := by
      have e1 : dl ^ 2 * |(k : ℝ) - c| ^ 3 / c = dl ^ 2 * (|(k : ℝ) - c| ^ 3 / c) := by ring
      have e2 : dl ^ 2 * (|(k : ℝ) - c| ^ 3 / c) ≤ dl ^ 2 * (8 * t ^ 13 / c₁) := by gcongr
      have e3 : 2 * dl * |(k : ℝ) - c| ≤ 2 * dl * (2 * t ^ 13) := by
        gcongr; linarith
      have e4' : dl ^ 2 * (8 * t ^ 13 / c₁) = 8 * dl ^ 2 / c₁ * t ^ 13 := by ring
      nlinarith
    have hnum0 : 0 ≤ dl ^ 2 * |(k : ℝ) - c| ^ 3 / c + 2 * dl * |(k : ℝ) - c| + 1 := by positivity
    have ht11 : t ^ 13 * t ^ 7 = t ^ 20 := by rw [← pow_add]
    calc (dl ^ 2 * |(k : ℝ) - c| ^ 3 / c + 2 * dl * |(k : ℝ) - c| + 1) * t ^ 7
        ≤ (8 * dl ^ 2 / c₁ + 4 * dl + 1) * t ^ 13 * t ^ 7 := by gcongr
      _ = (8 * dl ^ 2 / c₁ + 4 * dl + 1) * t ^ 20 := by rw [mul_assoc, ht11]
      _ = K₄ * (2 * σ2 * (κ * t ^ 20)) := by
          rw [hK₄, div_mul_eq_mul_div, eq_div_iff (by positivity)]; ring
      _ ≤ K₄ * (2 * σ2 * k) := by gcongr
  have hsm : K₁ / t ^ 7 + K₂ / t ^ 7 + K₃ / t ^ 7 + K₄ / t ^ 7 ≤ 1 / 2 := by
    rw [← add_div, ← add_div, ← add_div, div_le_iff₀ ht7]; linarith
  have hK0 : 0 ≤ K₁ / t ^ 7 := by positivity
  have hK20 : 0 ≤ K₂ / t ^ 7 := by positivity
  have hK30 : 0 ≤ K₃ / t ^ 7 := by positivity
  have hK40 : 0 ≤ K₄ / t ^ 7 := by positivity
  have hcS : |c - (k : ℝ)| / k = |c - (k : ℝ)| / k := rfl
  have henv := env_rel hp hlam hc0 hk1 hθ0 hθ1 hS hl' (by linarith) (by linarith) (by linarith)
    (by rw [← hdldef]; linarith)
  have hg0 : 0 ≤ gg p lam c k := by
    unfold gg; exact gau_nonneg (gA_pos hp hc0).le _ _ _
  unfold gg
  refine le_trans henv ?_
  apply mul_le_mul_of_nonneg_right _ (gau_nonneg (gA_pos hp hc0).le _ _ _)
  have : 8 * (K₁ + K₂ + K₃ + K₄) / t ^ 7
      = 8 * (K₁ / t ^ 7 + K₂ / t ^ 7 + K₃ / t ^ 7 + K₄ / t ^ 7) := by ring
  rw [this, ← hdldef]
  linarith

end DKernAux

end ND

end GGMCollatz
