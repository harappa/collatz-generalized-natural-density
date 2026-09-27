import GGMCollatz.Tao.Sec7.WETail

/-!
# GGM §7: the white exit of the first passage ((7.50), (7.51), (7.59) of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, from the statements in `TaoCollatz/Sec7/BlackEdge.lean` (`whiteStrip`) and
`TaoCollatz/Sec7/ManyTriangles.lean` (`fpDist_white_exit_deep`); generalized to the GGM family (p, q, r). Modified.

* `whiteStrip half W = {x ∈ W | x.1 ≤ half}`.
* `fpDist_white_exit_deep`: **deep white exit**. If `ε` is small and `m` is large, then from the starting point `(half - m, l)` of a black edge
  (the phase point `(half - m - 1, l)` lies in a triangle `t`, budget `s = l_Δ - l`, no upper limit on the budget
  assumed), the first-passage endpoint is white and in the strip with probability `≥ 3/4`. Used both by Case 2 (`fpDist_white_exit`) and by
  Case 3 (Lemma 7.9).

Proof (the idea of `fpDist_white_exit_deep_core` of tao-collatz, rebuilt; the 13-row white gap of tao-collatz
(a fact about phases) is not used, only separation): let `a₀ = ⌊s log p / log q²⌋`. The endpoint lies above the top of the triangle `t`
(`e₂ > s`). If `e₁ ≤ a₀ + B` and `e₂ - s ≤ Y`, the phase point `(j₀ + e₁, l + e₂)` is at distance `≤ √(B² + Y²) < σ` from the point
`(j₀ + min(e₁, a₀), l_Δ)` of the top side of `t` (`white_of_close`); by separation it lies in no other triangle,
and being above the top it does not lie in `t` either. For being in the strip (`e₁ ≤ m`), the edge condition `T.confined` of the triangle gives `a₀ ≤ m`,
i.e. `s log p / log q² < m + 1`. The three exceptional probabilities (`e₁ > m`, `e₁ > a₀ + B`, `e₂ > s + Y`) are each
`≤ 1/12`: the first two by the column form of Lemma 7.7 (`WE.colTail`) and the slope gap (condition (b), `WE.slope_gap`),
the last by `WE.fpDist_high_toReal_le` (the tail of `ℋ`).
-/

open scoped ENNReal

namespace GGMCollatz

/-- White points in the strip `j ≤ half` (renewal coordinates). -/
def whiteStrip (half : ℕ) (W : Set (ℕ × ℤ)) : Set (ℕ × ℤ) := {x | x.1 ≤ half ∧ x ∈ W}

namespace Family

variable (F : Family)

/-- **White because close** (the deterministic part): for a triangle family with `σ ≥ B + Y + 1`, if the phase point of the starting point
`(half - m - 1, l)` lies in a triangle `t`, `s = l_Δ - l` and `a₀ = ⌊s log p / log q²⌋`, then
`s < e₂ ≤ s + Y`, `e₁ ≤ m`, `e₁ ≤ a₀ + B` imply that `(half - m + e₁, l + e₂)` is a white point in the strip. -/
theorem WE.white_of_close {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) {B Y : ℕ}
    (hσ : (B : ℝ) + Y + 1 ≤ σ) {m : ℕ} (hmn : m ≤ half) {l : ℤ} (hl : 1 ≤ half - m)
    {t : ℕ × ℤ × ℝ} (ht : t ∈ T.T) (hmem : (half - m - 1, l) ∈ F.triangle t.1 t.2.1 t.2.2)
    {s : ℕ} (hs : (s : ℤ) = t.2.1 - l) {e : ℕ × ℤ} (he2 : (s : ℤ) < e.2)
    (he2Y : e.2 ≤ (s : ℤ) + Y) (he1m : e.1 ≤ m)
    (he1a : e.1 ≤ ⌊(s : ℝ) * Real.log (F.p : ℝ) / Real.log ((F.q : ℝ) ^ 2)⌋₊ + B) :
    (half - m + e.1, l + e.2) ∈ whiteStrip half T.W := by
  set Lp := Real.log (F.p : ℝ) with hLpdef
  set Lq := Real.log ((F.q : ℝ) ^ 2) with hLqdef
  have hLp : 0 < Lp := WE.log_p_pos F
  have hLq : 0 < Lq := WE.log_q_sq_pos F
  set a₀ : ℕ := ⌊(s : ℝ) * Lp / Lq⌋₊ with ha₀def
  set j₀ := half - m - 1 with hj₀
  obtain ⟨htj, hltl, hlin⟩ := hmem
  have hsR : (s : ℝ) = (t.2.1 : ℝ) - l := by exact_mod_cast hs
  have ha₀Lq : (a₀ : ℝ) * Lq ≤ (s : ℝ) * Lp := by
    have h := Nat.floor_le (show 0 ≤ (s : ℝ) * Lp / Lq by positivity)
    rw [← ha₀def] at h
    rwa [le_div_iff₀ hLq] at h
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hY0 : (0 : ℝ) ≤ Y := Nat.cast_nonneg Y
  have hσ0 : 0 ≤ σ := by linarith
  refine ⟨by omega, by omega, ?_⟩
  have hx1 : half - m + e.1 - 1 = j₀ + e.1 := by omega
  show (half - m + e.1 - 1, l + e.2) ∉ T.blk
  rw [hx1]
  intro hb
  simp only [TriFam.blk, Set.mem_iUnion, exists_prop] at hb
  obtain ⟨t', ht', hP⟩ := hb
  by_cases htt : t' = t
  · subst htt
    have := hP.2.1
    simp only at this
    omega
  · -- the point `Q = (j₀ + min(e₁, a₀), l_Δ)` of the top side lies in `t`
    have hQ : ((j₀ + min e.1 a₀, t.2.1) : ℕ × ℤ) ∈ F.triangle t.1 t.2.1 t.2.2 := by
      refine ⟨by simp only; omega, le_refl _, ?_⟩
      simp only
      have hmin : ((min e.1 a₀ : ℕ) : ℝ) ≤ a₀ := by exact_mod_cast min_le_right _ _
      rw [Nat.cast_add, ← hLqdef, ← hLpdef]
      have : (((j₀ : ℝ) + ((min e.1 a₀ : ℕ) : ℝ)) - t.1) * Lq + ((t.2.1 : ℝ) - t.2.1) * Lp
          = ((j₀ : ℝ) - t.1) * Lq + ((min e.1 a₀ : ℕ) : ℝ) * Lq := by ring
      rw [this]
      have h2 : ((min e.1 a₀ : ℕ) : ℝ) * Lq ≤ (a₀ : ℝ) * Lq :=
        mul_le_mul_of_nonneg_right hmin hLq.le
      have hlin' : ((j₀ : ℝ) - t.1) * Lq + ((t.2.1 : ℝ) - l) * Lp ≤ t.2.2 := hlin
      nlinarith
    have hsep := T.separated t' ht' t ht htt _ hP _ hQ
    simp only at hsep
    -- distance bound
    have h1 : j₀ + min e.1 a₀ ≤ j₀ + e.1 := by omega
    have h2 : j₀ + e.1 ≤ j₀ + min e.1 a₀ + B := by omega
    have h1r : ((j₀ + min e.1 a₀ : ℕ) : ℝ) ≤ ((j₀ + e.1 : ℕ) : ℝ) := by exact_mod_cast h1
    have h2r : ((j₀ + e.1 : ℕ) : ℝ) ≤ ((j₀ + min e.1 a₀ : ℕ) : ℝ) + B := by exact_mod_cast h2
    have h3 : (s : ℤ) < e.2 := he2
    have h3r : (t.2.1 : ℝ) - l < (e.2 : ℝ) := by rw [← hsR]; exact_mod_cast h3
    have h4r : (e.2 : ℝ) ≤ (t.2.1 : ℝ) - l + Y := by
      rw [← hsR]; exact_mod_cast he2Y
    have hd1 : (((j₀ + e.1 : ℕ) : ℝ) - ((j₀ + min e.1 a₀ : ℕ) : ℝ)) ^ 2 ≤ (B : ℝ) ^ 2 := by
      apply pow_le_pow_left₀ (by linarith) (by linarith)
    have hd2 : (((l + e.2 : ℤ) : ℝ) - (t.2.1 : ℝ)) ^ 2 ≤ (Y : ℝ) ^ 2 := by
      push_cast
      apply pow_le_pow_left₀ (by linarith) (by linarith)
    have hσK : ((B : ℝ) + Y + 1) ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ (by positivity) hσ 2
    nlinarith

/-! ### Constants and the three exceptional probabilities -/

/-- The slope gap `γ = log p / log q² - (p-1)/(2p) > 0`. -/
noncomputable def WE.gam : ℝ := Real.log (F.p : ℝ) / Real.log ((F.q : ℝ) ^ 2) - F.slopeInv

/-- `κ = (p-1)/(2p) · log q² / log p < 1`. -/
noncomputable def WE.kap : ℝ := F.slopeInv * (Real.log ((F.q : ℝ) ^ 2) / Real.log (F.p : ℝ))

/-- `γ₂ = (1 - κ)/(1 + log q² / log p)`. -/
noncomputable def WE.gam2 : ℝ :=
  (1 - WE.kap F) / (1 + Real.log ((F.q : ℝ) ^ 2) / Real.log (F.p : ℝ))

theorem WE.gam_pos : 0 < WE.gam F := by
  have := WE.slope_gap F
  unfold WE.gam; linarith

theorem WE.slopeInv_pos : 0 < F.slopeInv := by
  unfold slopeInv
  have : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  apply div_pos <;> linarith

theorem WE.kap_pos : 0 < WE.kap F := by
  unfold WE.kap
  have := WE.slopeInv_pos F
  have := WE.log_p_pos F
  have := WE.log_q_sq_pos F
  positivity

theorem WE.kap_lt_one : WE.kap F < 1 := by
  have hLp := WE.log_p_pos F
  have hLq := WE.log_q_sq_pos F
  have h := mul_lt_mul_of_pos_right (WE.slope_gap F)
    (show 0 < Real.log ((F.q : ℝ) ^ 2) / Real.log (F.p : ℝ) by positivity)
  unfold WE.kap
  rwa [show Real.log (F.p : ℝ) / Real.log ((F.q : ℝ) ^ 2)
      * (Real.log ((F.q : ℝ) ^ 2) / Real.log (F.p : ℝ)) = 1 by field_simp] at h

theorem WE.gam2_pos : 0 < WE.gam2 F := by
  unfold WE.gam2
  have := WE.kap_lt_one F
  have := WE.log_p_pos F
  have := WE.log_q_sq_pos F
  apply div_pos <;> [linarith; positivity]

/-- **Probability of leaving the strip**: if `s log p / log q² < m + 1` then `P(e₁ > m) ≤ 2C' e^{-c₂(1-κ)m}/(1 - e^{-c₂})`. -/
theorem WE.tail_out {c C' : ℝ} (hc : 0 < c) (hC' : 0 < C')
    (hcol : ∀ s j : ℕ, ∑' l : ℤ, (F.fpDist s (j, l)).toReal
        ≤ C' * (Sec7.Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) * F.slopeInv))
                  / Real.sqrt (1 + (s : ℝ))))
    (s m : ℕ)
    (hsm : (s : ℝ) * Real.log (F.p : ℝ) / Real.log ((F.q : ℝ) ^ 2) < (m : ℝ) + 1) :
    ∑' e : ℕ × ℤ, (F.fpDist s e).toReal * (if (m : ℝ) + 1 ≤ (e.1 : ℝ) then 1 else 0)
      ≤ 2 * C' * Real.exp (-(min (c ^ 2 * WE.gam2 F) c) * ((1 - WE.kap F) * m))
          / (1 - Real.exp (-(min (c ^ 2 * WE.gam2 F) c))) := by
  have hLp := WE.log_p_pos F
  have hLq := WE.log_q_sq_pos F
  have hκpos := WE.kap_pos F
  have hκ1 := WE.kap_lt_one F
  have h1κ : 0 ≤ 1 - WE.kap F := by linarith
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hsx : (s : ℝ) * F.slopeInv = ((s : ℝ) * Real.log (F.p : ℝ) / Real.log ((F.q : ℝ) ^ 2))
      * WE.kap F := by
    unfold WE.kap; field_simp
  set Lp := Real.log (F.p : ℝ)
  set Lq := Real.log ((F.q : ℝ) ^ 2)
  have hsx₀ : (s : ℝ) * F.slopeInv < ((m : ℝ) + 1) * WE.kap F := by
    rw [hsx]; exact mul_lt_mul_of_pos_right hsm hκpos
  have hs_lt : (s : ℝ) < ((m : ℝ) + 1) * (Lq / Lp) := by
    have h := mul_lt_mul_of_pos_right hsm (show 0 < Lq / Lp by positivity)
    rwa [show (s : ℝ) * Lp / Lq * (Lq / Lp) = s by field_simp] at h
  have hy : WE.gam2 F * (1 + (s : ℝ)) ≤ ((m : ℝ) + 1) - s * F.slopeInv := by
    have h1 : 1 + (s : ℝ) ≤ ((m : ℝ) + 1) * (1 + Lq / Lp) := by
      have e : ((m : ℝ) + 1) * (1 + Lq / Lp) = ((m : ℝ) + 1) + ((m : ℝ) + 1) * (Lq / Lp) := by
        ring
      rw [e]; linarith
    have h2 : WE.gam2 F * (1 + (s : ℝ)) ≤ (1 - WE.kap F) * ((m : ℝ) + 1) := by
      unfold WE.gam2
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      calc (1 - WE.kap F) * (1 + (s : ℝ))
          ≤ (1 - WE.kap F) * (((m : ℝ) + 1) * (1 + Lq / Lp)) := mul_le_mul_of_nonneg_left h1 h1κ
        _ = (1 - WE.kap F) * ((m : ℝ) + 1) * (1 + Lq / Lp) := by ring
    have e : (1 - WE.kap F) * ((m : ℝ) + 1) = ((m : ℝ) + 1) - ((m : ℝ) + 1) * WE.kap F := by
      ring
    linarith
  refine le_trans (WE.colTail F hc hC' hcol s (WE.gam2_pos F) hy) ?_
  set c₂ := min (c ^ 2 * WE.gam2 F) c with hc₂
  have hc₂pos : 0 < c₂ := lt_min (mul_pos (by positivity) (WE.gam2_pos F)) hc
  have hd₂ : 0 < 1 - Real.exp (-c₂) := by
    have : Real.exp (-c₂) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hD : (1 - WE.kap F) * (m : ℝ) ≤ ((m : ℝ) + 1) - s * F.slopeInv := by
    have e : ((m : ℝ) + 1) - ((m : ℝ) + 1) * WE.kap F
        = (1 - WE.kap F) * (m : ℝ) + (1 - WE.kap F) := by ring
    linarith
  have hexp : Real.exp (-c₂ * (((m : ℝ) + 1) - s * F.slopeInv))
      ≤ Real.exp (-c₂ * ((1 - WE.kap F) * m)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hD hc₂pos.le
    linarith
  apply div_le_div_of_nonneg_right _ hd₂.le
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- **Far column tail**: if `γ ≤ B` and `s log p / log q² < a₀ + 1` then
`P(e₁ > a₀ + B) ≤ 2C' e^{-c₁ B}/(1 - e^{-c₁})` (`c₁ = min(c²γ, c)`). -/
theorem WE.tail_far {c C' : ℝ} (hc : 0 < c) (hC' : 0 < C')
    (hcol : ∀ s j : ℕ, ∑' l : ℤ, (F.fpDist s (j, l)).toReal
        ≤ C' * (Sec7.Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) * F.slopeInv))
                  / Real.sqrt (1 + (s : ℝ))))
    (s a₀ B : ℕ) (hB : WE.gam F ≤ (B : ℝ))
    (ha₀ : (s : ℝ) * Real.log (F.p : ℝ) / Real.log ((F.q : ℝ) ^ 2) < (a₀ : ℝ) + 1) :
    ∑' e : ℕ × ℤ, (F.fpDist s e).toReal * (if (a₀ : ℝ) + B + 1 ≤ (e.1 : ℝ) then 1 else 0)
      ≤ 2 * C' * Real.exp (-(min (c ^ 2 * WE.gam F) c) * B)
          / (1 - Real.exp (-(min (c ^ 2 * WE.gam F) c))) := by
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hγ := WE.gam_pos F
  have hgs : WE.gam F * (s : ℝ)
      = (s : ℝ) * Real.log (F.p : ℝ) / Real.log ((F.q : ℝ) ^ 2) - s * F.slopeInv := by
    unfold WE.gam; ring
  have hy : WE.gam F * (1 + (s : ℝ)) ≤ ((a₀ : ℝ) + B + 1) - s * F.slopeInv := by
    have e : WE.gam F * (1 + (s : ℝ)) = WE.gam F + WE.gam F * (s : ℝ) := by ring
    rw [e]; linarith
  refine le_trans (WE.colTail F hc hC' hcol s hγ hy) ?_
  set c₁ := min (c ^ 2 * WE.gam F) c with hc₁
  have hc₁pos : 0 < c₁ := lt_min (mul_pos (by positivity) hγ) hc
  have hd₁ : 0 < 1 - Real.exp (-c₁) := by
    have : Real.exp (-c₁) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hD : (B : ℝ) ≤ ((a₀ : ℝ) + B + 1) - s * F.slopeInv := by
    have := mul_nonneg hγ.le hs0
    linarith
  have hexp : Real.exp (-c₁ * (((a₀ : ℝ) + B + 1) - s * F.slopeInv))
      ≤ Real.exp (-c₁ * B) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hD hc₁pos.le
    linarith
  apply div_le_div_of_nonneg_right _ hd₁.le
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- A `B` with `C e^{-a B}/(1-e^{-a}) ≤ 1/12` (and simultaneously `B ≥ b₀`). -/
theorem WE.exists_small_tail {a C : ℝ} (ha : 0 < a) (hC : 0 < C) (b₀ : ℝ) :
    ∃ B : ℕ, b₀ ≤ (B : ℝ) ∧ C * Real.exp (-a * B) / (1 - Real.exp (-a)) ≤ 1 / 12 := by
  have hd : 0 < 1 - Real.exp (-a) := by
    have : Real.exp (-a) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  obtain ⟨M, hM⟩ := WE.exp_neg_mul_le_eventually ha
    (η := (1 / 12) * (1 - Real.exp (-a)) / C) (by positivity)
  refine ⟨max M ⌈b₀⌉₊, le_trans (Nat.le_ceil b₀) (by exact_mod_cast le_max_right M ⌈b₀⌉₊), ?_⟩
  have h := hM (max M ⌈b₀⌉₊) (le_max_left _ _)
  rw [div_le_iff₀ hd]
  calc C * Real.exp (-a * ((max M ⌈b₀⌉₊ : ℕ) : ℝ))
      ≤ C * ((1 / 12) * (1 - Real.exp (-a)) / C) := mul_le_mul_of_nonneg_left h hC.le
    _ = 1 / 12 * (1 - Real.exp (-a)) := by field_simp

/-- An `ε₀` for which the separation width is at least `K`. -/
theorem WE.exists_eps (K : ℝ) : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → K ≤ F.sep ε := by
  have hsepc : 0 < F.sepc := by
    unfold sepc
    have hlpq : 0 < Real.log ((F.p : ℝ) * (F.q : ℝ) ^ 2) := by
      apply Real.log_pos
      have hp : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
      have hq : (2 : ℝ) ≤ F.q := by exact_mod_cast F.two_le_q
      nlinarith
    positivity
  refine ⟨Real.exp (-(K / F.sepc)), Real.exp_pos _, fun ε hε hεle => ?_⟩
  unfold sep
  have hlog : Real.log ε ≤ -(K / F.sepc) := by
    calc Real.log ε ≤ Real.log (Real.exp (-(K / F.sepc))) := Real.log_le_log hε hεle
      _ = -(K / F.sepc) := Real.log_exp _
  rw [one_div, Real.log_inv]
  have : K / F.sepc ≤ -Real.log ε := by linarith
  calc K = F.sepc * (K / F.sepc) := by field_simp
    _ ≤ F.sepc * -Real.log ε := mul_le_mul_of_nonneg_left this hsepc.le

/-- From the edge condition of the triangle, `⌊s log p / log q²⌋ ≤ m`. -/
theorem WE.a0_le_m {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (hσ0 : 0 ≤ σ) {m : ℕ}
    (_hl : 1 ≤ half - m) {l : ℤ} {t : ℕ × ℤ × ℝ} (ht : t ∈ T.T)
    (hmem : (half - m - 1, l) ∈ F.triangle t.1 t.2.1 t.2.2)
    {s : ℕ} (hs : (s : ℤ) = t.2.1 - l) :
    ⌊(s : ℝ) * Real.log (F.p : ℝ) / Real.log ((F.q : ℝ) ^ 2)⌋₊ ≤ m := by
  have hLp := WE.log_p_pos F
  have hLq := WE.log_q_sq_pos F
  set a₀ := ⌊(s : ℝ) * Real.log (F.p : ℝ) / Real.log ((F.q : ℝ) ^ 2)⌋₊ with ha₀def
  obtain ⟨htj, hltl, hlin⟩ := hmem
  have hsR : (s : ℝ) = (t.2.1 : ℝ) - l := by exact_mod_cast hs
  have ha₀Lq : (a₀ : ℝ) * Real.log ((F.q : ℝ) ^ 2) ≤ (s : ℝ) * Real.log (F.p : ℝ) := by
    have h := Nat.floor_le
      (show 0 ≤ (s : ℝ) * Real.log (F.p : ℝ) / Real.log ((F.q : ℝ) ^ 2) by positivity)
    rw [← ha₀def] at h
    rwa [le_div_iff₀ hLq] at h
  have hQ₀ : ((half - m - 1 + a₀, t.2.1) : ℕ × ℤ) ∈ F.triangle t.1 t.2.1 t.2.2 := by
    refine ⟨by simp only at htj ⊢; omega, le_refl _, ?_⟩
    simp only at hlin ⊢
    rw [Nat.cast_add]
    rw [hsR] at ha₀Lq
    nlinarith
  have hconf := T.confined t ht _ hQ₀
  simp only at hconf
  have h1 : ((half - m - 1 + a₀ : ℕ) : ℝ) + 1 ≤ (half : ℝ) := by linarith
  have h2 : half - m - 1 + a₀ + 1 ≤ half := by exact_mod_cast h1
  omega

/-- **Summing the bounds** (assembly of the white exit): if each of the three exceptional probabilities is `≤ 1/12`, the probability is `≥ 3/4`. -/
theorem WE.exit_main {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) {B Y : ℕ}
    (hσ : (B : ℝ) + Y + 1 ≤ σ) {m : ℕ} (hmn : m ≤ half) {l : ℤ} (hl : 1 ≤ half - m)
    {t : ℕ × ℤ × ℝ} (ht : t ∈ T.T) (hmem : (half - m - 1, l) ∈ F.triangle t.1 t.2.1 t.2.2)
    {s : ℕ} (hs : (s : ℤ) = t.2.1 - l)
    (hPout : ∑' e : ℕ × ℤ, (F.fpDist s e).toReal
      * (if (m : ℝ) + 1 ≤ (e.1 : ℝ) then 1 else 0) ≤ 1 / 12)
    (hPfar : ∑' e : ℕ × ℤ, (F.fpDist s e).toReal
      * (if ((⌊(s : ℝ) * Real.log (F.p : ℝ) / Real.log ((F.q : ℝ) ^ 2)⌋₊ : ℕ) : ℝ) + B + 1
          ≤ (e.1 : ℝ) then 1 else 0) ≤ 1 / 12)
    (hPhigh : ∑' e : ℕ × ℤ, (F.fpDist s e).toReal
      * (if (s : ℤ) + Y < e.2 then 1 else 0) ≤ 1 / 12) :
    3 / 4 ≤ ∑' e : ℕ × ℤ, (F.fpDist s e).toReal
      * Set.indicator (whiteStrip half T.W) 1 (half - m + e.1, l + e.2) := by
  set a₀ := ⌊(s : ℝ) * Real.log (F.p : ℝ) / Real.log ((F.q : ℝ) ^ 2)⌋₊ with ha₀def
  set iO : ℕ × ℤ → ℝ := fun e => if (m : ℝ) + 1 ≤ (e.1 : ℝ) then 1 else 0 with hiO
  set iF : ℕ × ℤ → ℝ := fun e => if (a₀ : ℝ) + B + 1 ≤ (e.1 : ℝ) then 1 else 0 with hiF
  set iH : ℕ × ℤ → ℝ := fun e => if (s : ℤ) + Y < e.2 then 1 else 0 with hiH
  set iW : ℕ × ℤ → ℝ := fun e =>
    Set.indicator (whiteStrip half T.W) 1 (half - m + e.1, l + e.2) with hiW
  have hiW0 : ∀ e, 0 ≤ iW e := fun e => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hiW1 : ∀ e, iW e ≤ 1 := fun e => by
    simp only [hiW]
    by_cases h : (half - m + e.1, l + e.2) ∈ whiteStrip half T.W
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  have hpt : ∀ e : ℕ × ℤ, (F.fpDist s e).toReal * (1 - iO e - iF e - iH e)
      ≤ (F.fpDist s e).toReal * iW e := by
    intro e
    by_cases hfe : F.fpDist s e = 0
    · rw [hfe, ENNReal.toReal_zero, zero_mul, zero_mul]
    have he2 : (s : ℤ) < e.2 := F.fpDist_support_snd_gt s e (by rwa [PMF.mem_support_iff])
    by_cases hall : ¬ ((m : ℝ) + 1 ≤ (e.1 : ℝ)) ∧ ¬ ((a₀ : ℝ) + B + 1 ≤ (e.1 : ℝ))
        ∧ ¬ ((s : ℤ) + Y < e.2)
    · obtain ⟨h1, h2, h3⟩ := hall
      have he1m : e.1 ≤ m := by
        have : (e.1 : ℝ) < (m : ℝ) + 1 := lt_of_not_ge h1
        have : e.1 < m + 1 := by exact_mod_cast this
        omega
      have he1a : e.1 ≤ a₀ + B := by
        have : (e.1 : ℝ) < (a₀ : ℝ) + B + 1 := lt_of_not_ge h2
        have : e.1 < a₀ + B + 1 := by exact_mod_cast this
        omega
      have he2Y : e.2 ≤ (s : ℤ) + Y := by omega
      have hwhite := WE.white_of_close F T hσ hmn hl ht hmem hs he2 he2Y he1m he1a
      have hiWe : iW e = 1 := by
        simp only [hiW]
        rw [Set.indicator_of_mem hwhite]
        rfl
      simp only [hiO, hiF, hiH, if_neg h1, if_neg h2, if_neg h3]
      rw [hiWe]
      linarith
    · have hle : 1 - iO e - iF e - iH e ≤ 0 := by
        simp only [hiO, hiF, hiH]
        by_cases h1 : (m : ℝ) + 1 ≤ (e.1 : ℝ)
        · rw [if_pos h1]; split_ifs <;> norm_num
        · by_cases h2 : (a₀ : ℝ) + B + 1 ≤ (e.1 : ℝ)
          · rw [if_neg h1, if_pos h2]; split_ifs <;> norm_num
          · by_cases h3 : (s : ℤ) + Y < e.2
            · rw [if_neg h1, if_neg h2, if_pos h3]; norm_num
            · exact absurd ⟨h1, h2, h3⟩ hall
      calc (F.fpDist s e).toReal * (1 - iO e - iF e - iH e) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg hle
        _ ≤ (F.fpDist s e).toReal * iW e := mul_nonneg ENNReal.toReal_nonneg (hiW0 e)
  have hfp : Summable fun e => (F.fpDist s e).toReal :=
    ENNReal.summable_toReal (F.fpDist s).tsum_coe_ne_top
  have hfp1 : ∑' e, (F.fpDist s e).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun e => (F.fpDist s).apply_ne_top e), (F.fpDist s).tsum_coe,
      ENNReal.toReal_one]
  have hsumI : ∀ i : ℕ × ℤ → ℝ, (∀ e, 0 ≤ i e) → (∀ e, i e ≤ 1) →
      Summable fun e => (F.fpDist s e).toReal * i e := fun i h0 h1 =>
    Summable.of_nonneg_of_le (fun e => mul_nonneg ENNReal.toReal_nonneg (h0 e))
      (fun e => mul_le_of_le_one_right ENNReal.toReal_nonneg (h1 e)) hfp
  have hsO := hsumI iO (fun e => by simp only [hiO]; split_ifs <;> norm_num)
    (fun e => by simp only [hiO]; split_ifs <;> norm_num)
  have hsF := hsumI iF (fun e => by simp only [hiF]; split_ifs <;> norm_num)
    (fun e => by simp only [hiF]; split_ifs <;> norm_num)
  have hsH := hsumI iH (fun e => by simp only [hiH]; split_ifs <;> norm_num)
    (fun e => by simp only [hiH]; split_ifs <;> norm_num)
  have hsW := hsumI iW hiW0 hiW1
  have hsG : Summable fun e => (F.fpDist s e).toReal * (1 - iO e - iF e - iH e) :=
    (((hfp.sub hsO).sub hsF).sub hsH).congr fun e => by ring
  have hG : ∑' e, (F.fpDist s e).toReal * (1 - iO e - iF e - iH e)
      = 1 - ∑' e, (F.fpDist s e).toReal * iO e - ∑' e, (F.fpDist s e).toReal * iF e
        - ∑' e, (F.fpDist s e).toReal * iH e := by
    rw [show (fun e => (F.fpDist s e).toReal * (1 - iO e - iF e - iH e))
        = fun e => (F.fpDist s e).toReal - (F.fpDist s e).toReal * iO e
          - (F.fpDist s e).toReal * iF e - (F.fpDist s e).toReal * iH e from
        funext fun e => by ring,
      Summable.tsum_sub ((hfp.sub hsO).sub hsF) hsH, Summable.tsum_sub (hfp.sub hsO) hsF,
      Summable.tsum_sub hfp hsO, hfp1]
  have hO' : ∑' e, (F.fpDist s e).toReal * iO e ≤ 1 / 12 := hPout
  have hF' : ∑' e, (F.fpDist s e).toReal * iF e ≤ 1 / 12 := hPfar
  have hH' : ∑' e, (F.fpDist s e).toReal * iH e ≤ 1 / 12 := hPhigh
  calc (3 : ℝ) / 4 ≤ 1 - 1 / 12 - 1 / 12 - 1 / 12 := by norm_num
    _ ≤ ∑' e, (F.fpDist s e).toReal * (1 - iO e - iF e - iH e) := by
        rw [hG]; linarith
    _ ≤ ∑' e, (F.fpDist s e).toReal * iW e := hsG.tsum_le_tsum hpt hsW

/-- **Deep white exit** (`fpDist_white_exit_deep` of tao-collatz, the form of (7.59)). -/
theorem fpDist_white_exit_deep :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ Cthr : ℕ, ∀ (half : ℕ) (T : F.TriFam half (F.sep ε)) (m : ℕ),
        Cthr ≤ m → m ≤ half → ∀ l : ℤ, 1 ≤ half - m →
        ∀ t ∈ T.T, (half - m - 1, l) ∈ F.triangle t.1 t.2.1 t.2.2 →
        ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
        3 / 4 ≤ ∑' e : ℕ × ℤ, (F.fpDist s e).toReal
          * Set.indicator (whiteStrip half T.W) 1 (half - m + e.1, l + e.2) := by
  obtain ⟨c, hc, C', hC', hcol⟩ := F.fpDist_col_le
  obtain ⟨ch, hch, Ch, hCh, htail⟩ := F.hold_tail_bound
  have hc₁ : 0 < min (c ^ 2 * WE.gam F) c := lt_min (mul_pos (by positivity) (WE.gam_pos F)) hc
  have hc₂ : 0 < min (c ^ 2 * WE.gam2 F) c :=
    lt_min (mul_pos (by positivity) (WE.gam2_pos F)) hc
  have h1κ : 0 < 1 - WE.kap F := by linarith [WE.kap_lt_one F]
  -- `B` for the far column tail
  obtain ⟨B, hBγ, hBtail⟩ := WE.exists_small_tail hc₁ (show 0 < 2 * C' by positivity) (WE.gam F)
  -- `Y` for the height tail (`e^{-ch(Y - ν)} = e^{ch ν} e^{-ch Y}`)
  obtain ⟨Y, hYν, hYtail⟩ := WE.exists_small_tail hch
    (show 0 < 3 * Ch * Real.exp (ch * F.holdMean2) by positivity) F.holdMean2
  have hYtail' : 3 * Ch * Real.exp (-ch * ((Y : ℝ) - F.holdMean2)) / (1 - Real.exp (-ch))
      ≤ 1 / 12 := by
    have e : 3 * Ch * Real.exp (-ch * ((Y : ℝ) - F.holdMean2))
        = 3 * Ch * Real.exp (ch * F.holdMean2) * Real.exp (-ch * Y) := by
      rw [mul_assoc (3 * Ch), ← Real.exp_add]; congr 2; ring
    rw [e]; exact hYtail
  -- the threshold `M` for leaving the strip
  obtain ⟨M, hM⟩ := WE.exp_neg_mul_le_eventually (mul_pos hc₂ h1κ)
    (η := (1 / 12) * (1 - Real.exp (-(min (c ^ 2 * WE.gam2 F) c))) / (2 * C'))
    (by
      have : Real.exp (-(min (c ^ 2 * WE.gam2 F) c)) < 1 := by
        rw [Real.exp_lt_one_iff]; linarith
      have : 0 < 1 - Real.exp (-(min (c ^ 2 * WE.gam2 F) c)) := by linarith
      positivity)
  obtain ⟨ε₀, hε₀, hsep⟩ := WE.exists_eps F ((B : ℝ) + Y + 1)
  refine ⟨ε₀, hε₀, fun ε hε hεle => ⟨M, ?_⟩⟩
  intro half T m hm hmn l hl t ht hmem s hs
  have hσ := hsep ε hε hεle
  have hσ0 : 0 ≤ F.sep ε := by
    have : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    have : (0 : ℝ) ≤ Y := Nat.cast_nonneg Y
    linarith
  have ha₀m := WE.a0_le_m F T hσ0 hl ht hmem hs
  have ha₀lt := Nat.lt_floor_add_one
    ((s : ℝ) * Real.log (F.p : ℝ) / Real.log ((F.q : ℝ) ^ 2))
  have hsm : (s : ℝ) * Real.log (F.p : ℝ) / Real.log ((F.q : ℝ) ^ 2) < (m : ℝ) + 1 := by
    have : ((⌊(s : ℝ) * Real.log (F.p : ℝ) / Real.log ((F.q : ℝ) ^ 2)⌋₊ : ℕ) : ℝ) ≤ m := by
      exact_mod_cast ha₀m
    linarith
  refine WE.exit_main F T hσ hmn hl ht hmem hs ?_ ?_ ?_
  · refine le_trans (WE.tail_out F hc hC' hcol s m hsm) ?_
    have hd : 0 < 1 - Real.exp (-(min (c ^ 2 * WE.gam2 F) c)) := by
      have : Real.exp (-(min (c ^ 2 * WE.gam2 F) c)) < 1 := by
        rw [Real.exp_lt_one_iff]; linarith
      linarith
    have hη := hM m hm
    rw [div_le_iff₀ hd]
    have e : -min (c ^ 2 * WE.gam2 F) c * ((1 - WE.kap F) * (m : ℝ))
        = -(min (c ^ 2 * WE.gam2 F) c * (1 - WE.kap F)) * m := by ring
    rw [e]
    calc 2 * C' * Real.exp (-(min (c ^ 2 * WE.gam2 F) c * (1 - WE.kap F)) * m)
        ≤ 2 * C' * ((1 / 12) * (1 - Real.exp (-(min (c ^ 2 * WE.gam2 F) c))) / (2 * C')) :=
          mul_le_mul_of_nonneg_left hη (by positivity)
      _ = 1 / 12 * (1 - Real.exp (-(min (c ^ 2 * WE.gam2 F) c))) := by field_simp
  · exact le_trans (WE.tail_far F hc hC' hcol s _ B hBγ ha₀lt) hBtail
  · exact le_trans (WE.fpDist_high_toReal_le F hch htail Y hYν s) hYtail'

end Family

end GGMCollatz
