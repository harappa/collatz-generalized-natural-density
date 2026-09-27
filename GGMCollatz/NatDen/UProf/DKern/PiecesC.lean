import GGMCollatz.NatDen.UProf.DKern.PiecesB

/-!
# Pieces of the main body of (DK) (3): weighted equidistribution of the Kronecker orbit ((e))

`K_piece`: `|Σ_J p^{-θ(k)} g(k) - W/(μ log p)| ≤ K t^{-2/μ_irr}`. We apply (KRON-W) (`kron_apply`) to the
Gaussian weight `wt` truncated to the window `J`, with `ℓ = ⌊t²⌋`. Variation `V ≤ (9A₀B₀ + 1)/t^8` (`wt_var`),
`W ≤ μ/(μ-λ) + K_W` (`W_piece`), `ℓ^{-1/μ} ≤ 2t^{-2/μ}`. `∫₀¹ p^{-θ} = 1/(μ log p)`.
-/

namespace GGMCollatz

namespace ND

namespace DKernAux

/-- The phase: `{kλ + u} = θ(k)` (`kλ + u ≥ 0`). -/
theorem fract_eq_th {lam u : ℝ} {k : ℕ} (h : 0 ≤ (k : ℝ) * lam + u) :
    Int.fract (((k : ℤ) : ℝ) * lam + u) = th lam u k := by
  rw [Int.cast_natCast, ← Int.self_sub_floor, ← Int.natCast_floor_eq_floor h]
  unfold th fl
  push_cast
  ring

/-- `1 - 1/p = 1/μ`. -/
theorem one_sub_inv_eq {p : ℕ} (hp : 2 ≤ p) :
    (1 - ((p : ℝ))⁻¹) / Real.log p = 1 / (muP p * Real.log p) := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hl : 0 < Real.log p := Real.log_pos (by linarith)
  unfold muP
  have : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/-- For `ℓ = ⌊t²⌋`, `ℓ^{-1/μ} ≤ 2 t^{-2/μ}` (`t² ≥ 2`). -/
theorem floor_sq_rpow_le {t μi : ℝ} (hμi : 1 ≤ μi) (ht : 0 < t) (ht2 : 2 ≤ t ^ 2) :
    ((⌊t ^ 2⌋₊ : ℕ) : ℝ) ^ (-(1 / μi)) ≤ 2 * t ^ (-(2 / μi)) := by
  have hμ0 : 0 < μi := by linarith
  have hfl : t ^ 2 / 2 ≤ ((⌊t ^ 2⌋₊ : ℕ) : ℝ) := by
    have := Nat.sub_one_lt_floor (t ^ 2); linarith
  have h1 := Real.rpow_le_rpow_of_nonpos (by positivity) hfl
    (show -(1 / μi) ≤ 0 by have : 0 < 1 / μi := by positivity
                           linarith)
  have e1 : (t ^ 2 : ℝ) ^ (-(1 / μi)) = t ^ (-(2 / μi)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1; push_cast; ring
  have e2 : (t ^ 2 / 2 : ℝ) ^ (-(1 / μi)) = t ^ (-(2 / μi)) * (2 : ℝ) ^ (1 / μi) := by
    rw [Real.div_rpow (by positivity) (by norm_num), e1, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      div_inv_eq_mul]
  have e3 : (2 : ℝ) ^ (1 / μi) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / μi) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [div_le_one hμ0]; exact hμi)
      _ = 2 := Real.rpow_one 2
  calc ((⌊t ^ 2⌋₊ : ℕ) : ℝ) ^ (-(1 / μi)) ≤ (t ^ 2 / 2) ^ (-(1 / μi)) := h1
    _ = t ^ (-(2 / μi)) * (2 : ℝ) ^ (1 / μi) := e2
    _ ≤ t ^ (-(2 / μi)) * 2 := mul_le_mul_of_nonneg_left e3 (Real.rpow_nonneg ht.le _)
    _ = 2 * t ^ (-(2 / μi)) := by ring

/-- If `t ≥ 1` and `2/μ ≤ n`, then `1/t^n ≤ t^{-2/μ}`. -/
theorem inv_pow_le_rate {t μi : ℝ} (ht : 1 ≤ t) (n : ℕ) (hn : 2 / μi ≤ n) :
    1 / t ^ n ≤ t ^ (-(2 / μi)) := by
  have ht0 : 0 < t := by linarith
  rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg ht0.le]
  exact Real.rpow_le_rpow_of_exponent_le ht (by linarith)

set_option maxHeartbeats 1000000 in
/-- **(e)**: weighted equidistribution of the Kronecker orbit. -/
theorem K_piece {p : ℕ} (hp : 2 ≤ p) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < muP p) {μi : ℝ}
    (hμi : 2 ≤ μi) (hkw : kronW_statement lam μi) {c₁ : ℝ} (hc₁ : 0 < c₁) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t : ℝ in Filter.atTop, ∀ u c : ℝ, c = u / (muP p - lam) →
      c₁ * t ^ 20 ≤ c → c ≤ t ^ 20 →
        |∑ k ∈ Finset.Ico (ja c t) (jb c t), Real.exp (-(th lam u k) * Real.log p) * gg p lam c k
          - Wt p lam c t / (muP p * Real.log p)| ≤ K * t ^ (-(2 / μi)) := by
  have hP1 : (1 : ℝ) < p := by have : (2 : ℝ) ≤ p := by exact_mod_cast hp
                               linarith
  obtain ⟨CK, hCK, hkron⟩ := kron_apply hkw hP1
  obtain ⟨KW, hKW, hW⟩ := W_piece hp hlam hc₁
  have hσ := sig2_pos hp
  have hμ := muP_pos hp
  have hdl : 0 < muP p - lam := by linarith
  set A₀ := muP p / Real.sqrt (2 * Real.pi * sig2 p * c₁) with hA₀
  set B₀ := (muP p - lam) ^ 2 / (2 * sig2 p * c₁) with hB₀
  set B₁ := (muP p - lam) ^ 2 / (2 * sig2 p) with hB₁
  have hA₀0 : 0 < A₀ := by positivity
  have hB₀0 : 0 < B₀ := by positivity
  have hB₁0 : 0 < B₁ := by positivity
  set KV := 9 * A₀ * B₀ + 1 with hKV
  have hKV0 : 0 < KV := by positivity
  set WM := muP p / (muP p - lam) + KW with hWM
  have hWM0 : 0 < WM := by positivity
  refine ⟨3 * KV + CK * (2 * WM + KV), by positivity, ?_⟩
  have hev1 := exp_small (show 0 < B₁ / 4 by positivity) (3 * A₀) 9
  have hev2 : ∀ᶠ t : ℝ in Filter.atTop, 2 ≤ c₁ * t ^ 9 := by
    have h := (Filter.tendsto_pow_atTop (n := 9) (by norm_num)).const_mul_atTop hc₁
    exact h.eventually_ge_atTop 2
  filter_upwards [hev1, hev2, hW, Filter.eventually_ge_atTop 2] with t h1 h2 hWt ht2
  intro u c hcu hc1 hc2
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  set R := t ^ 11 with hR
  have hR3 : 3 ≤ R := by
    have : 2 ^ 11 ≤ t ^ 11 := pow_le_pow_left₀ (by norm_num) ht2 11
    rw [hR]; linarith
  have hwin : 0 ≤ c - R := by nlinarith
  have hc0 : 0 < c := by linarith
  have hu : u = (muP p - lam) * c := by rw [hcu]; field_simp
  set A := gA p c with hA
  set B := gB p lam c with hB
  have hApos : 0 < A := gA_pos hp hc0
  have hBpos : 0 < B := gB_pos hp hlam hc0
  have hAle : A ≤ A₀ / t ^ 10 := gA_le hp hc₁ ht0 hc1
  have hBle : B ≤ B₀ / t ^ 20 := gB_le hp hc₁ ht0 hc1
  have hBge : B₁ / t ^ 20 ≤ B := gB_ge hp hc0 hc2
  -- the window
  set a := ja c t with ha
  set b := jb c t with hb
  have hab : a ≤ b := ja_le_jb ht0.le hwin
  set N := b - a with hN
  have hNab : a + N = b := Nat.add_sub_cancel' hab
  have hNr : (N : ℝ) = b - a := by rw [hN, Nat.cast_sub hab]
  have h1a := ja_le hwin
  have h2a := ja_gt (c := c) (t := t)
  have h1b := jb_ge (c := c) (t := t)
  have h2b := jb_lt (c := c) (t := t) (by linarith)
  set w := wt A B c (a : ℤ) N with hw
  set ℓ := ⌊t ^ 2⌋₊ with hℓ
  have ht22 : 4 ≤ t ^ 2 := by nlinarith
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; exact Nat.le_floor (by push_cast; linarith)
  have hℓle : (ℓ : ℝ) ≤ t ^ 2 := Nat.floor_le (by positivity)
  have hk := hkron u (a : ℤ) N w (wt_nonneg hApos.le B c _ N) (wt_out A B c _ N) ℓ hℓ1
  -- rewriting the sum
  have hsum1 : ∑ n ∈ Finset.Ico (a : ℤ) ((a : ℤ) + N),
      w n * Real.exp (-(Int.fract ((n : ℝ) * lam + u)) * Real.log p)
      = ∑ k ∈ Finset.Ico a b, Real.exp (-(th lam u k) * Real.log p) * gg p lam c k := by
    rw [sum_Ico_natCast, hNab]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    have hpos : 0 ≤ (k : ℝ) * lam + u := by rw [hu]; positivity
    rw [fract_eq_th hpos, mul_comm]
    congr 1
    rw [hw]; unfold wt gg
    have h' : k < a + N := by rw [hNab]; exact hk.2
    rw [if_pos ⟨by exact_mod_cast hk.1, by exact_mod_cast h'⟩, Int.cast_natCast]
  have hsum2 : ∑ n ∈ Finset.Ico (a : ℤ) ((a : ℤ) + N), w n = Wt p lam c t := by
    rw [sum_Ico_natCast, hNab]
    unfold Wt
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    rw [hw]; unfold wt gg
    have h' : k < a + N := by rw [hNab]; exact hk.2
    rw [if_pos ⟨by exact_mod_cast hk.1, by exact_mod_cast h'⟩, Int.cast_natCast]
  rw [hsum1, hsum2, one_sub_inv_eq hp] at hk
  rw [show Wt p lam c t / (muP p * Real.log p) = Wt p lam c t * (1 / (muP p * Real.log p)) by ring]
  refine le_trans hk ?_
  -- the variation `V ≤ KV/t^8`
  set V := ∑ n ∈ Finset.Ico ((a : ℤ) - 1) ((a : ℤ) + N), |w (n + 1) - w n| with hV
  have hVb := wt_var (A := A) (B := B) (c := c) (R := R) (a := (a : ℤ)) (N := N) hApos.le hBpos.le
    (by linarith) (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; rw [hNr]; linarith) (by push_cast; rw [hNr]; linarith)
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hVle : V ≤ KV / t ^ 8 := by
    refine le_trans hVb ?_
    have hN1 : (N : ℝ) + 1 ≤ 3 * R := by rw [hNr]; linarith
    have hRAB : R ^ 2 * A * B ≤ A₀ * B₀ / t ^ 8 := by
      calc R ^ 2 * A * B ≤ R ^ 2 * (A₀ / t ^ 10) * (B₀ / t ^ 20) := by gcongr
        _ = A₀ * B₀ / t ^ 8 := by rw [hR]; field_simp
    have hexp : Real.exp (-(B * (R - 1) ^ 2)) ≤ Real.exp (-(B₁ / 4 * t ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have hR1 : R ^ 2 / 4 ≤ (R - 1) ^ 2 := by nlinarith
      have e : B₁ / 4 * t ^ 2 = B₁ / t ^ 20 * (R ^ 2 / 4) := by rw [hR]; field_simp
      have : B₁ / t ^ 20 * (R ^ 2 / 4) ≤ B * (R - 1) ^ 2 :=
        mul_le_mul hBge hR1 (by positivity) hBpos.le
      linarith
    have hRA : 3 * R * (A * Real.exp (-(B * (R - 1) ^ 2))) ≤ 1 / t ^ 8 := by
      rw [le_div_iff₀ (by positivity)]
      calc 3 * R * (A * Real.exp (-(B * (R - 1) ^ 2))) * t ^ 8
          ≤ 3 * R * (A₀ / t ^ 10 * Real.exp (-(B₁ / 4 * t ^ 2))) * t ^ 8 := by gcongr
        _ = 3 * A₀ * t ^ 9 * Real.exp (-(B₁ / 4 * t ^ 2)) := by rw [hR]; field_simp
        _ ≤ 1 := h1
    calc ((N : ℝ) + 1) * (A * B * (2 * R + 1) + A * Real.exp (-(B * (R - 1) ^ 2)))
        ≤ 3 * R * (A * B * (3 * R) + A * Real.exp (-(B * (R - 1) ^ 2))) := by
          gcongr; linarith
      _ = 9 * (R ^ 2 * A * B) + 3 * R * (A * Real.exp (-(B * (R - 1) ^ 2))) := by ring
      _ ≤ 9 * (A₀ * B₀ / t ^ 8) + 1 / t ^ 8 := by gcongr
      _ = KV / t ^ 8 := by rw [hKV]; ring
  -- `W ≤ WM`
  have hWle : Wt p lam c t ≤ WM := by
    have h := hWt c hc1 hc2
    have : KW / t ^ 8 ≤ KW := div_le_self hKW.le (one_le_pow₀ ht1)
    rw [hWM]; linarith [(abs_le.mp h).2]
  have hW0 : 0 ≤ Wt p lam c t := by
    unfold Wt; exact Finset.sum_nonneg fun k _ => gau_nonneg (gA_pos hp hc0).le _ _ _
  -- powers of `ℓ`
  have hℓr1 : (ℓ : ℝ) ^ (-(1 / μi)) ≤ 2 * t ^ (-(2 / μi)) :=
    floor_sq_rpow_le (by linarith) ht0 (by linarith)
  have hℓr2 : (ℓ : ℝ) ^ (1 - 1 / μi) ≤ t ^ 2 := by
    have hℓ1' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
    calc (ℓ : ℝ) ^ (1 - 1 / μi) ≤ (ℓ : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hℓ1'
            (by have : 0 < 1 / μi := by positivity
                linarith)
      _ = ℓ := Real.rpow_one _
      _ ≤ t ^ 2 := hℓle
  have hrate6 : 1 / t ^ 6 ≤ t ^ (-(2 / μi)) :=
    inv_pow_le_rate ht1 6 (by rw [div_le_iff₀ (by linarith)]; push_cast; nlinarith)
  have hVt : V * t ^ 2 ≤ KV * t ^ (-(2 / μi)) := by
    calc V * t ^ 2 ≤ KV / t ^ 8 * t ^ 2 := by gcongr
      _ = KV * (1 / t ^ 6) := by field_simp
      _ ≤ KV * t ^ (-(2 / μi)) := by gcongr
  have hrate0 : 0 ≤ t ^ (-(2 / μi)) := Real.rpow_nonneg ht0.le _
  calc 3 * (ℓ : ℝ) * V + CK * (Wt p lam c t * (ℓ : ℝ) ^ (-(1 / μi)) + V * (ℓ : ℝ) ^ (1 - 1 / μi))
      ≤ 3 * (V * t ^ 2) + CK * (WM * (2 * t ^ (-(2 / μi))) + V * t ^ 2) := by
        have e1 : 3 * (ℓ : ℝ) * V ≤ 3 * (V * t ^ 2) := by nlinarith
        have e2 : Wt p lam c t * (ℓ : ℝ) ^ (-(1 / μi)) ≤ WM * (2 * t ^ (-(2 / μi))) :=
          mul_le_mul hWle hℓr1 (Real.rpow_nonneg (Nat.cast_nonneg _) _) hWM0.le
        have e3 : V * (ℓ : ℝ) ^ (1 - 1 / μi) ≤ V * t ^ 2 := mul_le_mul_of_nonneg_left hℓr2 hV0
        have := mul_le_mul_of_nonneg_left (add_le_add e2 e3) hCK.le
        linarith
    _ ≤ 3 * (KV * t ^ (-(2 / μi))) + CK * (WM * (2 * t ^ (-(2 / μi))) + KV * t ^ (-(2 / μi))) := by
        gcongr
    _ = (3 * KV + CK * (2 * WM + KV)) * t ^ (-(2 / μi)) := by ring

end DKernAux

end ND

end GGMCollatz
