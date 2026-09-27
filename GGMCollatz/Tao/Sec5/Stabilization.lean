import GGMCollatz.Tao.Sec5.ApproxFormula

/-!
# Stability across windows and GGM's Proposition 3.5 (GGM §4, Tao's Proposition 1.11, tao-collatz's `stabilization`)

Derived from `TaoCollatz/Sec5/Stabilization.lean` (`Iy_count_ratio`, `approxMainTerm_window_stable`,
`stabilization_atCX`, `stabilization`) of gotrevor/tao-collatz (Apache-2.0), commit 15efca2;
generalized to the GGM family (p, q, r).

* `Iy_ratio`: `#I_y / Z_y = μ/d + O(log^{-1/5} x)` (see the accompanying paper; the `1/μ` in GGM
  `eq: size of I_y` is superfluous, (G2) in the accompanying paper).
* `window_formula`: `P(Pass_x(L_y) ∈ E) = (#I_y/Z_y) Ψ(E) + O(log^{-1/5} x)`.
* `passLoc_approx`: normalization at `E = ℕ` gives `Ψ(ℕ) = O(1)`, hence
  `P(Pass_x(L_y) ∈ E) = (μ/d) Ψ(E) + O(log^{-1/5} x)`, and the right-hand side does not depend on
  `y ∈ {x^β, x^{αβ}}` (GGM `eq: pass goal`).
* `prop35_of_inter`: **Proposition 3.5 from GGM's Propositions 3.1 and 4.1**.
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

variable (F : Family)

/-! ### Ratio of the number of rows to the window mass -/

/-- **Ratio of the number of rows to the window mass** (see the accompanying paper). -/
theorem Iy_ratio : ∀ α β : ℝ, 1 < α → 1 < β → α ^ 2 * β ≤ F.thetaMax →
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop, ∀ y : ℝ, x ^ β ≤ y → y ≤ x ^ (α * β) →
      0 < F.windowMass y (y ^ α) ∧
        |((F.Iy x y α).card : ℝ) / F.windowMass y (y ^ α) - F.mu / F.drift|
          ≤ K * Real.log x ^ (-(1 / 5 : ℝ)) := by
  classical
  intro α β hα hβ hθ
  have hμ := F.mu_pos
  have hd := F.drift_pos
  have hq := F.log_q_pos
  have hα1 : 0 < α - 1 := by linarith
  set K : ℝ := (3 * F.drift + F.mu) * (2 * F.mu) / (F.drift * (α - 1)) with hK
  refine ⟨K, by positivity, ?_⟩
  filter_upwards [F.eventually_windowMass_ge hα, F.eventually_window_nonempty hα,
    eventually_add_mul_rpow_le (show (0.8:ℝ) < 1 by norm_num) one_pos 0 2
      (show 0 < (α - 1) / F.drift by positivity),
    eventually_log_ge 1, Filter.eventually_ge_atTop (F.p : ℝ), Filter.eventually_gt_atTop 1] with
    x hZ hne hV hL hxp hx1
  intro y hy1 hy2
  rw [Real.rpow_one, zero_add] at hV
  have hx0 : 0 < x := by linarith
  have hxβ : x ≤ x ^ β := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ β := Real.rpow_le_rpow_of_exponent_le hx1.le hβ.le
  have hxy : x ≤ y := le_trans hxβ hy1
  have hy0 : 0 < y := by linarith
  have hW := hne y hxy
  have hZpos := F.windowMass_pos hW
  refine ⟨hZpos, ?_⟩
  set L := Real.log x with hLdef
  set V := L ^ (0.8 : ℝ) with hVdef
  have hLpos : 0 < L := by linarith
  have hV1 : 1 ≤ V := Real.one_le_rpow hL (by norm_num)
  have hly : L ≤ Real.log y := Real.log_le_log hx0 hxy
  -- endpoints
  set A : ℝ := Real.log (y / x) / F.drift + V with hAdef
  set B : ℝ := Real.log (y ^ α / x) / F.drift - V with hBdef
  have hlogyx : Real.log (y / x) = Real.log y - L := Real.log_div hy0.ne' hx0.ne'
  have hlogyαx : Real.log (y ^ α / x) = α * Real.log y - L := by
    rw [Real.log_div (by positivity) hx0.ne', Real.log_rpow hy0]
  have hA0 : 0 ≤ A := by
    rw [hAdef, hlogyx]
    have : 0 ≤ (Real.log y - L) / F.drift := div_nonneg (by linarith) hd.le
    linarith
  have hBA : B - A = (α - 1) * Real.log y / F.drift - 2 * V := by
    rw [hAdef, hBdef, hlogyx, hlogyαx]; field_simp; ring
  have hAB : A ≤ B := by
    have h1 : (α - 1) * L / F.drift ≤ (α - 1) * Real.log y / F.drift :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hly hα1.le) hd.le
    have h2 : (α - 1) / F.drift * L = (α - 1) * L / F.drift := by ring
    linarith
  have hBn : B < F.nZero x + 1 := by
    have hlogy2 : α * Real.log y ≤ α ^ 2 * β * L := by
      have : Real.log y ≤ α * β * L := by
        rw [hLdef, ← Real.log_rpow hx0]; exact Real.log_le_log hy0 hy2
      nlinarith
    have hB1 : B ≤ (α ^ 2 * β - 1) * L / F.drift := by
      rw [hBdef, hlogyαx]
      have : (α * Real.log y - L) / F.drift ≤ (α ^ 2 * β * L - L) / F.drift :=
        div_le_div_of_nonneg_right (by linarith) hd.le
      have : (α ^ 2 * β * L - L) / F.drift = (α ^ 2 * β - 1) * L / F.drift := by ring
      have hV0 : 0 ≤ V := by linarith
      linarith
    have hB2 : (α ^ 2 * β - 1) * L / F.drift ≤ L / (20 * Real.log F.q) := by
      have h1 : α ^ 2 * β - 1 ≤ F.drift / (20 * Real.log F.q) := by unfold thetaMax at hθ; linarith
      calc (α ^ 2 * β - 1) * L / F.drift ≤ F.drift / (20 * Real.log F.q) * L / F.drift :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hLpos.le) hd.le
        _ = L / (20 * Real.log F.q) := by field_simp
    have hn0 : L / (5 * Real.log F.q) - 1 < F.nZero x := Nat.sub_one_lt_floor _
    have : L / (20 * Real.log F.q) ≤ L / (5 * Real.log F.q) :=
      div_le_div_of_nonneg_left hLpos.le (by positivity) (by linarith)
    linarith
  have hIdef : F.Iy x y α = (Finset.range (F.nZero x + 1)).filter
      (fun n : ℕ => A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B) := by
    unfold Iy; rfl
  obtain ⟨hc1, hc2⟩ := card_filter_range_bounds (n₀ := F.nZero x) hA0 hAB hBn
  rw [← hIdef] at hc1 hc2
  -- window mass
  have hyα : y ≤ y ^ α := by
    calc y = y ^ (1 : ℝ) := (Real.rpow_one y).symm
      _ ≤ y ^ α := Real.rpow_le_rpow_of_exponent_le (by linarith) hα.le
  have hm := F.windowMass_approx (by linarith) hyα
  have hlogyy : Real.log (y ^ α / y) = (α - 1) * Real.log y := by
    rw [Real.log_div (by positivity) hy0.ne', Real.log_rpow hy0]; ring
  rw [hlogyy] at hm
  have hpy : (F.p : ℝ) / y ≤ 1 := by rw [div_le_one hy0]; linarith
  set Z := F.windowMass y (y ^ α) with hZdef
  set I := ((F.Iy x y α).card : ℝ) with hIcard
  have hZy := hZ y hxy
  have hZ' : 0 < (α - 1) * L / (2 * F.mu) := by positivity
  -- bound on `d I - μ Z`
  have hnum : |F.drift * I - F.mu * Z| ≤ (3 * F.drift + F.mu) * V := by
    have e1 : F.drift * (B - A) = (α - 1) * Real.log y - 2 * F.drift * V := by
      rw [hBA]; field_simp
    have e2 : F.mu * ((α - 1) * Real.log y / F.mu) = (α - 1) * Real.log y := by field_simp
    have hm' := abs_le.mp hm
    set Y := (α - 1) * Real.log y with hY
    have f1 := mul_le_mul_of_nonneg_left hc1 hd.le
    have f2 := mul_le_mul_of_nonneg_left hc2 hd.le
    have f3 := mul_le_mul_of_nonneg_left hm'.1 hμ.le
    have f4 := mul_le_mul_of_nonneg_left hm'.2 hμ.le
    have f5 := mul_le_mul_of_nonneg_left hpy hμ.le
    have f6 : F.mu * (F.p / y) ≥ 0 := by positivity
    have f7 : F.drift ≤ F.drift * V := le_mul_of_one_le_right hd.le hV1
    have f8 : F.mu ≤ F.mu * V := le_mul_of_one_le_right hμ.le hV1
    have e3 : F.mu * (Z - Y / F.mu) = F.mu * Z - Y := by field_simp
    have e4 : F.drift * (B - A - 1) = Y - 2 * F.drift * V - F.drift := by rw [mul_sub, e1]; ring
    have e5 : F.drift * (B - A + 1) = Y - 2 * F.drift * V + F.drift := by rw [mul_add, e1]; ring
    rw [e3] at f3 f4
    rw [e4] at f1
    rw [e5] at f2
    rw [abs_le]
    constructor <;> linarith
  have hkey : I / Z - F.mu / F.drift = (F.drift * I - F.mu * Z) / (F.drift * Z) := by
    field_simp
  rw [hkey, abs_div, abs_of_pos (by positivity : 0 < F.drift * Z)]
  have hVL : V / L = L ^ (-(1 / 5 : ℝ)) := by
    rw [hVdef, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hLpos]; norm_num
  calc |F.drift * I - F.mu * Z| / (F.drift * Z)
      ≤ (3 * F.drift + F.mu) * V / (F.drift * ((α - 1) * L / (2 * F.mu))) :=
        div_le_div₀ (by positivity) hnum (by positivity) (mul_le_mul_of_nonneg_left hZy hd.le)
    _ = K * (V / L) := by rw [hK]; field_simp
    _ = K * L ^ (-(1 / 5 : ℝ)) := by rw [hVL]

/-! ### The profile `Ψ` -/

theorem psi_nonneg (β x : ℝ) (E : Set ℕ) : 0 ≤ F.psi β x E := by
  unfold psi
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun M _ =>
    mul_nonneg ENNReal.toReal_nonneg (by positivity))

theorem Eprime_mono (β x : ℝ) {E E' : Set ℕ} (h : E ⊆ E') :
    F.Eprime β x E ⊆ F.Eprime β x E' := by
  intro M hM
  unfold Eprime at hM ⊢
  simp only [Finset.mem_filter] at hM ⊢
  exact ⟨hM.1, hM.2.1, hM.2.2.1, hM.2.2.2.1, hM.2.2.2.2.1, h hM.2.2.2.2.2⟩

theorem psi_mono (β x : ℝ) {E E' : Set ℕ} (h : E ⊆ E') : F.psi β x E ≤ F.psi β x E' := by
  unfold psi
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum_of_subset_of_nonneg (F.Eprime_mono β x h) (fun M _ _ =>
    mul_nonneg ENNReal.toReal_nonneg (by positivity))

/-! ### The per-window formula and normalization -/

/-- **Per-window formula**: `P(Pass_x(L_y) ∈ E) = (#I_y/Z_y) Ψ(E) + O(log^{-1/5} x)` (uniformly in `E`). -/
theorem window_formula (h33 : F.prop33_statement) (h41 : F.prop41_statement) :
    ∀ α β : ℝ, 1 < α → 1 < β → α ^ 2 * β ≤ F.thetaMax → ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop,
      ∀ y : ℝ, x ^ β ≤ y → y ≤ x ^ (α * β) → ∀ E : Set ℕ,
        |expect (F.logUnif y (y ^ α)) (Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ E} 1)
          - ((F.Iy x y α).card : ℝ) / F.windowMass y (y ^ α) * F.psi β x E|
          ≤ K * Real.log x ^ (-(1 / 5 : ℝ)) := by
  intro α β hα hβ hθ
  obtain ⟨K₁, hK₁, h1⟩ := F.first_passage_approx h33 α β hα hβ hθ
  obtain ⟨K₂, hK₂, h2⟩ := F.row_eval h41 α β hα hβ hθ
  obtain ⟨K₃, hK₃, h3⟩ := F.Iy_ratio α β hα hβ hθ
  have hμd : 0 < F.mu / F.drift := div_pos F.mu_pos F.drift_pos
  refine ⟨K₁ + (F.mu / F.drift + K₃) * K₂, by positivity, ?_⟩
  filter_upwards [h1, h2, h3, eventually_log_ge 1] with x hx1 hx2 hx3 hL
  intro y hy1 hy2 E
  obtain ⟨hZ, hratio⟩ := hx3 y hy1 hy2
  have hLpos : 0 < Real.log x := by linarith
  set Z := F.windowMass y (y ^ α) with hZdef
  set I := F.Iy x y α with hIdef
  set Ψ := F.psi β x E with hΨdef
  set L5 := Real.log x ^ (-(1 / 5 : ℝ)) with hL5def
  set L2 := Real.log x ^ (-2 : ℝ) with hL2def
  have hL5nn : 0 ≤ L5 := Real.rpow_nonneg hLpos.le _
  have hL5le : L5 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by norm_num)
  have hL25 : L2 ≤ L5 := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hL2nn : 0 ≤ L2 := Real.rpow_nonneg hLpos.le _
  -- identity for the sum over rows
  have hsum : ∑ n ∈ I, F.rowTerm β x E y α n - (I.card : ℝ) / Z * Ψ
      = (∑ n ∈ I, (Z * F.rowTerm β x E y α n - Ψ)) / Z := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    field_simp
  have hbound : |∑ n ∈ I, (Z * F.rowTerm β x E y α n - Ψ)| ≤ (I.card : ℝ) * (K₂ * L2) := by
    calc |∑ n ∈ I, (Z * F.rowTerm β x E y α n - Ψ)|
        ≤ ∑ n ∈ I, |Z * F.rowTerm β x E y α n - Ψ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ I, K₂ * L2 := Finset.sum_le_sum fun n hn => hx2 y hy1 hy2 E n hn
      _ = (I.card : ℝ) * (K₂ * L2) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hIZ : (I.card : ℝ) / Z ≤ F.mu / F.drift + K₃ := by
    have := (abs_le.mp hratio).2
    nlinarith
  have hIZnn : 0 ≤ (I.card : ℝ) / Z := div_nonneg (Nat.cast_nonneg _) hZ.le
  have hrows : |∑ n ∈ I, F.rowTerm β x E y α n - (I.card : ℝ) / Z * Ψ|
      ≤ (F.mu / F.drift + K₃) * K₂ * L5 := by
    rw [hsum, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
    calc _ ≤ (I.card : ℝ) * (K₂ * L2) := hbound
      _ = (I.card : ℝ) / Z * (K₂ * L2) * Z := by field_simp
      _ ≤ (F.mu / F.drift + K₃) * (K₂ * L5) * Z := by
          apply mul_le_mul_of_nonneg_right _ hZ.le
          exact mul_le_mul hIZ (mul_le_mul_of_nonneg_left hL25 hK₂.le) (by positivity)
            (by positivity)
      _ = _ := by ring
  have hA := hx1 y hy1 hy2 E
  calc _ ≤ |expect (F.logUnif y (y ^ α)) (Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ E} 1)
            - ∑ n ∈ I, F.rowTerm β x E y α n|
          + |∑ n ∈ I, F.rowTerm β x E y α n - (I.card : ℝ) / Z * Ψ| := abs_sub_le _ _ _
    _ ≤ K₁ * L5 + (F.mu / F.drift + K₃) * K₂ * L5 := add_le_add hA hrows
    _ = _ := by ring

/-- **Approximation by a window-independent profile** (GGM `eq: pass goal`): `Φ_x(E) = (μ/d) Ψ(E)` does not
depend on `y`, and the first-passage laws of the two windows `[x^β, x^{αβ}]`, `[x^{αβ}, x^{α²β}]` are both
close to `Φ_x`. -/
theorem passLoc_approx (h33 : F.prop33_statement) (h41 : F.prop41_statement) :
    ∃ c : ℝ, 0 < c ∧ ∀ α β : ℝ, 1 < α → 1 < β → α ^ 2 * β ≤ F.thetaMax →
      ∃ K : ℝ, 0 < K ∧ ∃ Φ : ℝ → Set ℕ → ℝ, ∀ᶠ x : ℝ in Filter.atTop, ∀ E : Set ℕ,
        |expect (F.logUnif (x ^ β) (x ^ (α * β))) (Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ E} 1)
            - Φ x E| ≤ K * Real.log x ^ (-c) ∧
        |expect (F.logUnif (x ^ (α * β)) (x ^ (α ^ 2 * β)))
            (Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ E} 1) - Φ x E| ≤ K * Real.log x ^ (-c) := by
  refine ⟨1 / 5, by norm_num, ?_⟩
  intro α β hα hβ hθ
  obtain ⟨K, hK, hW⟩ := F.window_formula h33 h41 α β hα hβ hθ
  obtain ⟨K₃, hK₃, h3⟩ := F.Iy_ratio α β hα hβ hθ
  have hμ := F.mu_pos
  have hd := F.drift_pos
  have hμd : 0 < F.mu / F.drift := div_pos hμ hd
  set B : ℝ := (1 + K) * (2 * F.drift / F.mu) with hBdef
  have hB : 0 < B := by positivity
  refine ⟨K + K₃ * B, by positivity, fun x E => F.mu / F.drift * F.psi β x E, ?_⟩
  have hsmall := eventually_log_rpow_neg_le (a := 1 / 5) (by norm_num)
    (show 0 < F.mu / F.drift / (2 * K₃) by positivity)
  filter_upwards [hW, h3, hsmall, eventually_log_ge 1, Filter.eventually_ge_atTop 1]
    with x hxW hx3 hxs hL hx1
  have hLpos : 0 < Real.log x := by linarith
  set L5 := Real.log x ^ (-(1 / 5 : ℝ)) with hL5def
  have hL5nn : 0 ≤ L5 := Real.rpow_nonneg hLpos.le _
  have hL5le : L5 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by norm_num)
  have hx0 : 0 ≤ x := by linarith
  -- the two windows
  have hβle : β ≤ α * β := by nlinarith
  have hαβle : α * β ≤ α * β := le_refl _
  have hy1 : x ^ β ≤ x ^ β ∧ x ^ β ≤ x ^ (α * β) :=
    ⟨le_refl _, Real.rpow_le_rpow_of_exponent_le hx1 hβle⟩
  have hy2 : x ^ β ≤ x ^ (α * β) ∧ x ^ (α * β) ≤ x ^ (α * β) :=
    ⟨Real.rpow_le_rpow_of_exponent_le hx1 hβle, le_refl _⟩
  have hw1 : (x ^ β) ^ α = x ^ (α * β) := by rw [← Real.rpow_mul hx0]; ring_nf
  have hw2 : (x ^ (α * β)) ^ α = x ^ (α ^ 2 * β) := by rw [← Real.rpow_mul hx0]; ring_nf
  -- per-window bound (general `y`)
  have key : ∀ y : ℝ, x ^ β ≤ y → y ≤ x ^ (α * β) → ∀ E : Set ℕ,
      |expect (F.logUnif y (y ^ α)) (Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ E} 1)
        - F.mu / F.drift * F.psi β x E| ≤ (K + K₃ * B) * L5 := by
    intro y hy1 hy2 E
    obtain ⟨hZ, hratio⟩ := hx3 y hy1 hy2
    set r := ((F.Iy x y α).card : ℝ) / F.windowMass y (y ^ α) with hrdef
    have hrlo : F.mu / F.drift / 2 ≤ r := by
      have h1 := (abs_le.mp hratio).1
      have h2 : K₃ * L5 ≤ F.mu / F.drift / 2 := by
        have := mul_le_mul_of_nonneg_left hxs hK₃.le
        rw [show K₃ * (F.mu / F.drift / (2 * K₃)) = F.mu / F.drift / 2 by field_simp] at this
        exact this
      linarith
    have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hrlo
    -- normalization: at `E = ℕ` the probability is 1
    have huniv := hxW y hy1 hy2 Set.univ
    have hone : expect (F.logUnif y (y ^ α)) (Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ Set.univ} 1)
        = 1 := by
      have hset : {N | F.passLoc ⌊x⌋₊ N ∈ (Set.univ : Set ℕ)} = Set.univ := by
        ext N; simp
      rw [hset]
      unfold expect
      simp only [Set.indicator_univ, Pi.one_apply, mul_one]
      exact tsum_toReal_eq_one _
    rw [hone] at huniv
    have hΨu : F.psi β x Set.univ ≤ B := by
      have h1 : r * F.psi β x Set.univ ≤ 1 + K := by
        have := (abs_le.mp huniv).1
        nlinarith
      have h2 : F.psi β x Set.univ ≤ (1 + K) / r := by
        rw [le_div_iff₀ hrpos]; linarith
      calc F.psi β x Set.univ ≤ (1 + K) / r := h2
        _ ≤ (1 + K) / (F.mu / F.drift / 2) := by
            apply div_le_div_of_nonneg_left (by linarith) (by positivity) hrlo
        _ = B := by rw [hBdef]; field_simp
    have hΨ0 := F.psi_nonneg β x E
    have hΨB : F.psi β x E ≤ B := le_trans (F.psi_mono β x (Set.subset_univ E)) hΨu
    have hE := hxW y hy1 hy2 E
    calc _ ≤ |expect (F.logUnif y (y ^ α)) (Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ E} 1)
              - r * F.psi β x E| + |r * F.psi β x E - F.mu / F.drift * F.psi β x E| :=
            abs_sub_le _ _ _
      _ ≤ K * L5 + K₃ * L5 * B := by
          apply add_le_add hE
          rw [← sub_mul, abs_mul, abs_of_nonneg hΨ0]
          exact mul_le_mul hratio hΨB hΨ0 (by positivity)
      _ = (K + K₃ * B) * L5 := by ring
  intro E
  constructor
  · have := key (x ^ β) hy1.1 hy1.2 E
    rwa [hw1] at this
  · have := key (x ^ (α * β)) hy2.1 hy2.2 E
    rwa [hw2] at this

/-! ### GGM's Proposition 3.5 -/

/-- Absorbing the range of small `x`: if `0 < c` and `1 ≤ u ≤ U` then `1 ≤ U^c · u^{-c}`. -/
theorem one_le_rpow_mul_rpow_neg {c u U : ℝ} (hc : 0 ≤ c) (hu : 0 < u) (huU : u ≤ U) :
    1 ≤ U ^ c * u ^ (-c) := by
  rw [Real.rpow_neg hu.le]
  have hpos : 0 < u ^ c := Real.rpow_pos_of_pos hu c
  rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
  exact Real.rpow_le_rpow hu.le huU hc

/-- **Proposition 3.5 from GGM's Propositions 3.1 and 4.1** (GGM §4 "Proof that Proposition 4.1 ⇒
Proposition 3.5", Tao's Proposition 1.11). -/
theorem prop35_of_inter (h33 : F.prop33_statement) (h41 : F.prop41_statement) :
    F.prop35_statement := by
  obtain ⟨c₁, hc₁, hNE⟩ := F.nonescape h33
  obtain ⟨c₂, hc₂, hPL⟩ := F.passLoc_approx h33 h41
  have hθ : 1 < F.thetaMax := F.one_lt_thetaMax
  set c : ℝ := min (min c₁ c₂) (min 1 ((F.thetaMax - 1) / 7)) with hcdef
  have hcpos : 0 < c := lt_min (lt_min hc₁ hc₂) (lt_min one_pos (by linarith))
  have hcc₁ : c ≤ c₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcc₂ : c ≤ c₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hc1 : c ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hcθ : c ≤ (F.thetaMax - 1) / 7 := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨c, hcpos, ?_⟩
  intro α β hα1 hαc hβ1 hβc
  -- the window exponent is at most `θ₀`
  have hcube : (1 + c) ^ 3 ≤ F.thetaMax := by
    have hc2 : c * c ≤ c := by nlinarith
    have hc3 : c * c * c ≤ c := by nlinarith
    have hexp : (1 + c) ^ 3 = 1 + 3 * c + 3 * (c * c) + c * c * c := by ring
    have h7 : 7 * c ≤ F.thetaMax - 1 := by linarith
    linarith
  have hαβ' : α * β < (1 + c) ^ 2 := by nlinarith
  have hαβ : α * β ≤ F.thetaMax := by nlinarith
  have hα2β : α ^ 2 * β ≤ F.thetaMax := by
    have : α ^ 2 * β < (1 + c) ^ 3 := by
      have h1 : α ^ 2 < (1 + c) ^ 2 := by nlinarith
      nlinarith
    linarith
  obtain ⟨K₁, hK₁, hev1⟩ := hNE α β hα1 hβ1 hαβ
  obtain ⟨K₂, hK₂, Φ, hev2⟩ := hPL α β hα1 hβ1 hα2β
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp (hev1.and hev2)
  set X : ℝ := max X₀ (Real.exp 1) with hXdef
  have hXe : Real.exp 1 ≤ X := le_max_right _ _
  have he2 : (2 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have hlogX : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hXe
  set K : ℝ := max (max K₁ (X ^ c)) (max (4 * K₂) (2 * Real.log X ^ c)) with hKdef
  have hKK₁ : K₁ ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKX : X ^ c ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have hKK₂ : 4 * K₂ ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKL : 2 * Real.log X ^ c ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨K, lt_of_lt_of_le hK₁ hKK₁, fun x hx => ⟨?_, ?_⟩⟩
  · -- first half: the probability of not hitting
    have hx0 : 0 < x := by linarith
    have hxc : 0 ≤ x ^ (-c) := Real.rpow_nonneg hx0.le _
    by_cases hxX : X ≤ x
    · have h1 := (hX₀ x (le_trans (le_max_left _ _) hxX)).1
      have hmono : x ^ (-c₁) ≤ x ^ (-c) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg hcc₁)
      calc _ ≤ K₁ * x ^ (-c₁) := h1
        _ ≤ K₁ * x ^ (-c) := mul_le_mul_of_nonneg_left hmono hK₁.le
        _ ≤ K * x ^ (-c) := mul_le_mul_of_nonneg_right hKK₁ hxc
    · have hle := expect_indicator_le_one (F.logUnif (x ^ β) (x ^ (α * β))) {N | ¬ F.passes ⌊x⌋₊ N}
      calc _ ≤ 1 := hle
        _ ≤ X ^ c * x ^ (-c) := one_le_rpow_mul_rpow_neg hcpos.le hx0 (le_of_lt (not_le.mp hxX))
        _ ≤ K * x ^ (-c) := mul_le_mul_of_nonneg_right hKX hxc
  · -- second half: total variation of the law of the first-passage location
    have hx0 : 0 < x := by linarith
    have hlogx0 : 0 < Real.log x := Real.log_pos (by linarith)
    have hLc : 0 ≤ Real.log x ^ (-c) := Real.rpow_nonneg hlogx0.le _
    by_cases hxX : X ≤ x
    · have h2 := (hX₀ x (le_trans (le_max_left _ _) hxX)).2
      have hlogx1 : 1 ≤ Real.log x := le_trans hlogX (Real.log_le_log (by linarith) hxX)
      have hmono : Real.log x ^ (-c₂) ≤ Real.log x ^ (-c) :=
        Real.rpow_le_rpow_of_exponent_le hlogx1 (neg_le_neg hcc₂)
      have hev : ∀ E : Set ℕ,
          |expect ((F.logUnif (x ^ β) (x ^ (α * β))).map (F.passLoc ⌊x⌋₊)) (Set.indicator E 1)
            - expect ((F.logUnif (x ^ (α * β)) (x ^ (α ^ 2 * β))).map (F.passLoc ⌊x⌋₊))
                (Set.indicator E 1)| ≤ 2 * (K₂ * Real.log x ^ (-c₂)) := by
        intro E
        rw [expect_map_indicator, expect_map_indicator]
        obtain ⟨hA, hB⟩ := h2 E
        have := abs_sub_le
          (expect (F.logUnif (x ^ β) (x ^ (α * β))) (Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ E} 1))
          (Φ x E)
          (expect (F.logUnif (x ^ (α * β)) (x ^ (α ^ 2 * β)))
            (Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ E} 1))
        rw [abs_sub_comm (Φ x E)] at this
        linarith
      have hd := dTV_le_of_forall_event _ _ _ hev
      calc _ ≤ 2 * (2 * (K₂ * Real.log x ^ (-c₂))) := hd
        _ = 4 * K₂ * Real.log x ^ (-c₂) := by ring
        _ ≤ 4 * K₂ * Real.log x ^ (-c) := mul_le_mul_of_nonneg_left hmono (by linarith)
        _ ≤ K * Real.log x ^ (-c) := mul_le_mul_of_nonneg_right hKK₂ hLc
    · have hlogxX : Real.log x ≤ Real.log X := Real.log_le_log hx0 (le_of_lt (not_le.mp hxX))
      calc _ ≤ 2 := dTV_le_two _ _
        _ = 2 * 1 := by ring
        _ ≤ 2 * (Real.log X ^ c * Real.log x ^ (-c)) :=
            mul_le_mul_of_nonneg_left (one_le_rpow_mul_rpow_neg hcpos.le hlogx0 hlogxX)
              (by norm_num)
        _ = (2 * Real.log X ^ c) * Real.log x ^ (-c) := by ring
        _ ≤ K * Real.log x ^ (-c) := mul_le_mul_of_nonneg_right hKL hLc

end Family

end GGMCollatz
