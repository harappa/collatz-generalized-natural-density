import GGMCollatz.Tao.Sec7.EWWeight

/-!
# GGM §7: Case 2 of Proposition 7.8 (shallow triangles, (7.44)–(7.51) of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, files `TaoCollatz/Sec7/BlackEdge.lean` (`whiteStrip`,
`edgeWeight`, `Q_fp_endpoint_le`) and `TaoCollatz/Sec7/BlackEdgeQ.lean` (the assembly of `Q_black_edge_case2_at`);
generalized to the GGM family (p, q, r). Modified. The white set `W` is general (`T.W` is plugged in at the assembly stage).

* `edgeWeight A m e` (the mean depth weight one step beyond the endpoint).
* `Q_fp_endpoint_le`: one step at the endpoint ((7.46)).
* `fpDist_edgeWeight_le` ((7.48), weight degradation `≤ (1+δ) m^{-A}`, `s ≤ m / log² m`): from `EWWeight.lean`.
* `fpDist_white_exit` ((7.50), (7.51), the endpoint is white and in the strip with positive probability): from the deep form in `WhiteExit.lean`.
* `Q_black_edge_case2`: assembly of Case 2 (proved, using the two leaves above).
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- The mean depth weight one step beyond the endpoint `e` (`edgeWeight` of (7.46) of tao-collatz). -/
noncomputable def edgeWeight (A : ℝ) (m : ℕ) (e : ℕ × ℤ) : ℝ :=
  ∑' d : ℕ × ℤ, (F.hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)

theorem edgeWeight_nonneg (A : ℝ) (m : ℕ) (e : ℕ × ℤ) : 0 ≤ F.edgeWeight A m e :=
  tsum_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Beyond the edge (`e₁ > m`), `edgeWeight = 1`. -/
theorem edgeWeight_of_deep (A : ℝ) {m : ℕ} {e : ℕ × ℤ} (he : m < e.1) :
    F.edgeWeight A m e = 1 := by
  unfold edgeWeight
  have h1 : ∀ d : ℕ × ℤ,
      (F.hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)
        = (F.hold d).toReal := by
    intro d
    have h0 : m - e.1 - d.1 = 0 := by omega
    rw [h0]
    simp [Real.one_rpow]
  rw [tsum_congr h1, F.hold_tsum_toReal]

/-- `edgeWeight ≤ 1` (`A ≥ 0`). -/
theorem edgeWeight_le_one {A : ℝ} (hA : 0 ≤ A) (m : ℕ) (e : ℕ × ℤ) :
    F.edgeWeight A m e ≤ 1 := by
  have hterm : ∀ d : ℕ × ℤ,
      (F.hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) ≤ (F.hold d).toReal := by
    intro d
    have h1 : ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast Nat.le_max_right (m - e.1 - d.1) 1) (by linarith)
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg h1
  have hsummLHS : Summable (fun d : ℕ × ℤ =>
      (F.hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)) :=
    Summable.of_nonneg_of_le
      (fun d => mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      hterm F.hold_summable_toReal
  calc F.edgeWeight A m e
      = ∑' d : ℕ × ℤ, (F.hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) := rfl
    _ ≤ ∑' d : ℕ × ℤ, (F.hold d).toReal :=
        hsummLHS.tsum_le_tsum hterm F.hold_summable_toReal
    _ = 1 := F.hold_tsum_toReal

/-- `m^{-A} ≤ edgeWeight` (`A ≥ 0`, `m ≥ 1`). -/
theorem rpow_neg_le_edgeWeight {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : 1 ≤ m) (e : ℕ × ℤ) :
    (m : ℝ) ^ (-A) ≤ F.edgeWeight A m e := by
  have hterm : ∀ d : ℕ × ℤ,
      (F.hold d).toReal * (m : ℝ) ^ (-A)
        ≤ (F.hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) := by
    intro d
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    have hmax_le : ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
      have : (max (m - e.1 - d.1) 1 : ℕ) ≤ m := by omega
      exact_mod_cast this
    have hmax_pos : (0 : ℝ) < ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) := by
      have : 0 < (max (m - e.1 - d.1) 1 : ℕ) := by omega
      exact_mod_cast this
    exact Real.rpow_le_rpow_of_nonpos hmax_pos hmax_le (by linarith)
  have hsummL : Summable (fun d : ℕ × ℤ => (F.hold d).toReal * (m : ℝ) ^ (-A)) :=
    F.hold_summable_toReal.mul_right _
  have hsummR : Summable (fun d : ℕ × ℤ =>
      (F.hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)) :=
    Summable.of_nonneg_of_le
      (fun d => mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (fun d => mul_le_of_le_one_right ENNReal.toReal_nonneg
        (Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast Nat.le_max_right (m - e.1 - d.1) 1) (by linarith)))
      F.hold_summable_toReal
  calc (m : ℝ) ^ (-A)
      = ∑' d : ℕ × ℤ, (F.hold d).toReal * (m : ℝ) ^ (-A) := by
        rw [tsum_mul_right, F.hold_tsum_toReal, one_mul]
    _ ≤ F.edgeWeight A m e := hsummL.tsum_le_tsum hterm hsummR

/-- `Q_m ≥ 1` (weight `1` and `Q = 1` at points outside the strip). -/
theorem one_le_Qm (half : ℕ) (W : Set (ℕ × ℤ)) {κ : ℝ} (hκ : 0 ≤ κ) (A : ℝ) (hA : 0 ≤ A)
    (m : ℕ) : 1 ≤ F.Qm half W κ A m := by
  have h := F.le_Qm half W hκ A hA m (p1 := half + 1) (l := 0) (by omega) (by omega)
  have hw : (max (half - (half + 1)) 1 : ℕ) = 1 := by omega
  rw [hw, F.Q_boundary _ _ _ _ _ (by omega)] at h
  simpa using h

/-- **One step at the endpoint** (`Q_fp_endpoint_le` of tao-collatz, (7.46)). -/
theorem Q_fp_endpoint_le (half : ℕ) (W : Set (ℕ × ℤ)) {κ : ℝ} (hκ : 0 ≤ κ) (A : ℝ)
    (hA : 0 ≤ A) (m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ half) (l : ℤ) (e : ℕ × ℤ) :
    F.Q half W κ (half - m + e.1) (l + e.2)
      ≤ (1 - (1 - Real.exp (-κ))
            * Set.indicator (whiteStrip half W) 1 (half - m + e.1, l + e.2))
        * (F.edgeWeight A m e * F.Qm half W κ A (m - 1)) := by
  set j' := half - m + e.1 with hj'
  set QM := F.Qm half W κ A (m - 1) with hQM
  have hQM0 : 0 ≤ QM := F.Qm_nonneg _ _ _ _ _
  have hQM1 : 1 ≤ QM := F.one_le_Qm _ _ hκ _ hA _
  rcases Nat.lt_or_ge half j' with hout | hin
  · rw [F.Q_boundary _ _ _ _ _ hout,
      Set.indicator_of_notMem (fun hmem => absurd (show j' ≤ half from hmem.1) (by omega)) 1,
      mul_zero, sub_zero, one_mul, F.edgeWeight_of_deep A (by omega), one_mul]
    exact hQM1
  · rw [F.Q_rec _ _ _ _ _ hin]
    have hatom : ∀ d : ℕ × ℤ,
        (F.hold d).toReal * F.Q half W κ (j' + d.1) (l + e.2 + d.2)
          ≤ (F.hold d).toReal * (((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM) := by
      intro d
      rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
      · rw [F.hold_zero_of_fst_zero h0, ENNReal.toReal_zero, zero_mul, zero_mul]
      · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        have h1 : 1 ≤ j' + d.1 := by omega
        have h2 : half - (m - 1) ≤ j' + d.1 := by omega
        have hkey := F.Q_le_Qm half W hκ A hA (m - 1) (l := l + e.2 + d.2) h1 h2
        have heq : half - (j' + d.1) = m - e.1 - d.1 := by omega
        rwa [heq] at hkey
    have hwle : ∀ d : ℕ × ℤ,
        (F.hold d).toReal * (((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM)
          ≤ (F.hold d).toReal * QM := by
      intro d
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      calc ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM
          ≤ 1 * QM := mul_le_mul_of_nonneg_right
            (Real.rpow_le_one_of_one_le_of_nonpos
              (by exact_mod_cast Nat.le_max_right (m - e.1 - d.1) 1)
              (by linarith)) hQM0
        _ = QM := one_mul _
    have hsumR : Summable fun d : ℕ × ℤ =>
        (F.hold d).toReal * (((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM) :=
      Summable.of_nonneg_of_le
        (fun d => mul_nonneg ENNReal.toReal_nonneg
          (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hQM0))
        hwle (F.hold_summable_toReal.mul_right QM)
    have hsumL : Summable fun d : ℕ × ℤ =>
        (F.hold d).toReal * F.Q half W κ (j' + d.1) (l + e.2 + d.2) :=
      Summable.of_nonneg_of_le
        (fun d => mul_nonneg ENNReal.toReal_nonneg (F.Q_nonneg _ _ _ _ _))
        (fun d => (hatom d).trans (hwle d)) (F.hold_summable_toReal.mul_right QM)
    have htsum : ∑' d : ℕ × ℤ,
        (F.hold d).toReal * F.Q half W κ (j' + d.1) (l + e.2 + d.2)
          ≤ F.edgeWeight A m e * QM := by
      calc ∑' d : ℕ × ℤ,
          (F.hold d).toReal * F.Q half W κ (j' + d.1) (l + e.2 + d.2)
          ≤ ∑' d : ℕ × ℤ,
            (F.hold d).toReal * (((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM) :=
            hsumL.tsum_le_tsum hatom hsumR
        _ = ∑' d : ℕ × ℤ,
            ((F.hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)) * QM :=
            tsum_congr fun d => (mul_assoc _ _ _).symm
        _ = F.edgeWeight A m e * QM := tsum_mul_right
    have hdamp : Real.exp (-κ * Set.indicator W 1 (j', l + e.2))
        = 1 - (1 - Real.exp (-κ))
            * Set.indicator (whiteStrip half W) 1 (j', l + e.2) := by
      by_cases hw : (j', l + e.2) ∈ W
      · have e1 : Set.indicator W (1 : ℕ × ℤ → ℝ) (j', l + e.2) = 1 :=
          Set.indicator_of_mem hw 1
        have hmem : (j', l + e.2) ∈ whiteStrip half W := ⟨hin, hw⟩
        have e2 : Set.indicator (whiteStrip half W) (1 : ℕ × ℤ → ℝ) (j', l + e.2) = 1 :=
          Set.indicator_of_mem hmem 1
        rw [e1, e2, mul_one, mul_one]
        ring
      · have e1 : Set.indicator W (1 : ℕ × ℤ → ℝ) (j', l + e.2) = 0 :=
          Set.indicator_of_notMem hw 1
        have e2 : Set.indicator (whiteStrip half W) (1 : ℕ × ℤ → ℝ) (j', l + e.2) = 0 :=
          Set.indicator_of_notMem (fun hmem => hw hmem.2) 1
        rw [e1, e2, mul_zero, mul_zero, sub_zero, Real.exp_zero]
    calc Real.exp (-κ * Set.indicator W 1 (j', l + e.2)) *
          ∑' d : ℕ × ℤ,
            (F.hold d).toReal * F.Q half W κ (j' + d.1) (l + e.2 + d.2)
        ≤ Real.exp (-κ * Set.indicator W 1 (j', l + e.2))
            * (F.edgeWeight A m e * QM) :=
          mul_le_mul_of_nonneg_left htsum (Real.exp_pos _).le
      _ = (1 - (1 - Real.exp (-κ))
            * Set.indicator (whiteStrip half W) 1 (j', l + e.2))
            * (F.edgeWeight A m e * QM) := by rw [hdamp]

/-- **Degradation of the weight** (`fpDist_edgeWeight_le` of tao-collatz, (7.42), (7.48)): for `A, δ > 0` there is a threshold such that,
if `m` is large and `s ≤ m / log² m`, then `Σ_e P(endpoint = e) edgeWeight(A, m, e) ≤ (1+δ) m^{-A}` (`EW.edgeWeight_bound`). -/
theorem fpDist_edgeWeight_le (A : ℝ) (hA : 0 < A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Cthr : ℕ, ∀ m : ℕ, Cthr ≤ m → ∀ s : ℕ,
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      ∑' e : ℕ × ℤ, (F.fpDist s e).toReal * F.edgeWeight A m e
        ≤ (1 + δ) * (m : ℝ) ^ (-A) :=
  EW.edgeWeight_bound F A hA δ hδ

/-- **White exit** (`fpDist_white_exit` of tao-collatz, (7.50), (7.51)): if `ε` is small, there are `p₀ > 0` and
a threshold such that, from the starting point `(half - m, l)` of a black edge (the phase point `(half - m - 1, l)` lies in a triangle `t`),
the endpoint of the first passage with budget `s = l_Δ - l ≤ m / log² m` is white and in the strip with probability `≥ p₀`. From the deep form
`fpDist_white_exit_deep` (`p₀ = 3/4`, no upper limit on the budget). -/
theorem fpDist_white_exit :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ p₀ : ℝ, 0 < p₀ ∧ ∃ Cthr : ℕ, ∀ (half : ℕ) (T : F.TriFam half (F.sep ε)) (m : ℕ),
        Cthr ≤ m → m ≤ half → ∀ l : ℤ, 1 ≤ half - m →
        ∀ t ∈ T.T, (half - m - 1, l) ∈ F.triangle t.1 t.2.1 t.2.2 →
        ∀ s : ℕ, (s : ℤ) = t.2.1 - l → (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
        p₀ ≤ ∑' e : ℕ × ℤ, (F.fpDist s e).toReal
          * Set.indicator (whiteStrip half T.W) 1 (half - m + e.1, l + e.2) := by
  obtain ⟨ε₀, hε₀, hdeep⟩ := F.fpDist_white_exit_deep
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  obtain ⟨Cthr, hC⟩ := hdeep ε hε hεle
  exact ⟨3 / 4, by norm_num, Cthr,
    fun half T m hm hmn l hl t ht hmem s hs _ => hC half T m hm hmn l hl t ht hmem s hs⟩

/-- **Case 2** (`Q_black_edge_case2` of tao-collatz): at the starting point of a black edge with budget `s ≤ m / log² m`,
`Q ≤ m^{-A} Q_{m-1}`. Assembled from `fpDist_white_exit` and `fpDist_edgeWeight_le` (`δ = c p₀ / 2`,
`c = 1 - e^{-ε³}`). -/
theorem Q_black_edge_case2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ A : ℝ, 0 < A →
      ∃ Cthr : ℕ, ∀ (half : ℕ) (T : F.TriFam half (F.sep ε)) (m : ℕ), Cthr ≤ m → m ≤ half →
        ∀ l : ℤ, 1 ≤ half - m → ∀ t ∈ T.T, (half - m - 1, l) ∈ F.triangle t.1 t.2.1 t.2.2 →
        ∀ s : ℕ, (s : ℤ) = t.2.1 - l → (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
        F.Q half T.W (ε ^ 3) (half - m) l
          ≤ (m : ℝ) ^ (-A) * F.Qm half T.W (ε ^ 3) A (m - 1) := by
  obtain ⟨ε₀, hε₀, hWE⟩ := F.fpDist_white_exit
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεle A hA
  obtain ⟨p₀, hp₀pos, Cw, hwhiteAll⟩ := hWE ε hε hεle
  set κ : ℝ := ε ^ 3 with hκdef
  have hκ0 : 0 ≤ κ := by positivity
  have hc_pos : 0 < 1 - Real.exp (-κ) := by
    rw [sub_pos]; exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (by positivity))
  obtain ⟨Ce, hedgeAll⟩ := F.fpDist_edgeWeight_le A hA ((1 - Real.exp (-κ)) * p₀ / 2)
    (div_pos (mul_pos hc_pos hp₀pos) (by norm_num))
  refine ⟨max (max Cw Ce) 2, ?_⟩
  intro half T m hm hmn l hl t ht htmem s hs hbudget
  have hmCw : Cw ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hmCe : Ce ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm2 : 2 ≤ m := le_trans (le_max_right _ _) hm
  have hm1 : 1 ≤ m := by omega
  have hwhite := hwhiteAll half T m hmCw hmn l hl t ht htmem s hs hbudget
  have hedge := hedgeAll m hmCe s hbudget
  set W := T.W with hWdef
  have hendpt : ∀ e : ℕ × ℤ,
      F.Q half W κ (half - m + e.1) (l + e.2)
        ≤ (1 - (1 - Real.exp (-κ))
              * Set.indicator (whiteStrip half W) 1 (half - m + e.1, l + e.2))
          * (F.edgeWeight A m e * F.Qm half W κ A (m - 1)) :=
    fun e => F.Q_fp_endpoint_le half W hκ0 A hA.le m hm1 hmn l e
  have hstart_enn := F.Q_le_fpDist_expect half W κ hκ0 s (half - m) l
  have hRne : (∑' e : ℕ × ℤ, F.fpDist s e
        * ENNReal.ofReal (F.Q half W κ (half - m + e.1) (l + e.2))) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (PMF.tsum_mul_ofReal_le_one (F.fpDist s) _ (fun e => F.Q_le_one _ _ _ hκ0 _ _))
  have hRtoReal : (∑' e : ℕ × ℤ, F.fpDist s e
        * ENNReal.ofReal (F.Q half W κ (half - m + e.1) (l + e.2))).toReal
      = ∑' e : ℕ × ℤ, (F.fpDist s e).toReal * F.Q half W κ (half - m + e.1) (l + e.2) :=
    PMF.toReal_tsum_mul_ofReal (F.fpDist s) _ (fun e => F.Q_nonneg _ _ _ _ _)
  have hstep1 : F.Q half W κ (half - m) l
      ≤ ∑' e : ℕ × ℤ, (F.fpDist s e).toReal * F.Q half W κ (half - m + e.1) (l + e.2) := by
    have h := ENNReal.toReal_mono hRne hstart_enn
    rwa [ENNReal.toReal_ofReal (F.Q_nonneg _ _ _ _ _), hRtoReal] at h
  set c : ℝ := 1 - Real.exp (-κ) with hc
  set QM : ℝ := F.Qm half W κ A (m - 1) with hQMdef
  set mA : ℝ := (m : ℝ) ^ (-A) with hmAdef
  have hQM0 : 0 ≤ QM := F.Qm_nonneg _ _ _ _ _
  have hmA0 : 0 ≤ mA := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hmA_le1 : mA ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm1) (by linarith)
  have hf_nonneg : ∀ e : ℕ × ℤ, 0 ≤ (F.fpDist s e).toReal := fun _ => ENNReal.toReal_nonneg
  have hf_summable : Summable (fun e : ℕ × ℤ => (F.fpDist s e).toReal) :=
    ENNReal.summable_toReal (by rw [(F.fpDist s).tsum_coe]; exact ENNReal.one_ne_top)
  have hind0 : ∀ e : ℕ × ℤ,
      0 ≤ Set.indicator (whiteStrip half W) (1 : ℕ × ℤ → ℝ) (half - m + e.1, l + e.2) :=
    fun e => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hind1 : ∀ e : ℕ × ℤ,
      Set.indicator (whiteStrip half W) (1 : ℕ × ℤ → ℝ) (half - m + e.1, l + e.2) ≤ 1 := by
    intro e
    by_cases h : (half - m + e.1, l + e.2) ∈ whiteStrip half W
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  have hew_ge : ∀ e : ℕ × ℤ, mA ≤ F.edgeWeight A m e :=
    fun e => F.rpow_neg_le_edgeWeight hA.le hm1 e
  have hbound : ∀ g : ℕ × ℤ → ℝ, (∀ e, 0 ≤ g e) → (∀ e, g e ≤ 1) →
      Summable (fun e : ℕ × ℤ => (F.fpDist s e).toReal * g e) := by
    intro g hg0 hg1
    exact Summable.of_nonneg_of_le (fun e => mul_nonneg (hf_nonneg e) (hg0 e))
      (fun e => mul_le_of_le_one_right (hf_nonneg e) (hg1 e)) hf_summable
  have hsum_ew : Summable (fun e : ℕ × ℤ => (F.fpDist s e).toReal * F.edgeWeight A m e) :=
    hbound _ (fun e => F.edgeWeight_nonneg A m e) (fun e => F.edgeWeight_le_one hA.le m e)
  have hsum_Qe : Summable (fun e : ℕ × ℤ => (F.fpDist s e).toReal
      * F.Q half W κ (half - m + e.1) (l + e.2)) :=
    hbound _ (fun e => F.Q_nonneg _ _ _ _ _) (fun e => F.Q_le_one _ _ _ hκ0 _ _)
  have hsum_indew : Summable (fun e : ℕ × ℤ => (F.fpDist s e).toReal
      * (Set.indicator (whiteStrip half W) 1 (half - m + e.1, l + e.2)
          * F.edgeWeight A m e)) :=
    hbound _ (fun e => mul_nonneg (hind0 e) (F.edgeWeight_nonneg A m e))
      (fun e => mul_le_one₀ (hind1 e) (F.edgeWeight_nonneg A m e)
        (F.edgeWeight_le_one hA.le m e))
  have hsum_indmA : Summable (fun e : ℕ × ℤ => (F.fpDist s e).toReal
      * (Set.indicator (whiteStrip half W) 1 (half - m + e.1, l + e.2) * mA)) :=
    hbound _ (fun e => mul_nonneg (hind0 e) hmA0)
      (fun e => mul_le_one₀ (hind1 e) hmA0 hmA_le1)
  have hsum_main : Summable (fun e : ℕ × ℤ => (F.fpDist s e).toReal
      * ((1 - c * Set.indicator (whiteStrip half W) 1 (half - m + e.1, l + e.2))
          * F.edgeWeight A m e)) :=
    (hsum_ew.sub (hsum_indew.mul_left c)).congr (fun e => by ring)
  have hindew_ge : p₀ * mA ≤ ∑' e : ℕ × ℤ, (F.fpDist s e).toReal
      * (Set.indicator (whiteStrip half W) 1 (half - m + e.1, l + e.2)
          * F.edgeWeight A m e) := by
    have hge : ∀ e : ℕ × ℤ,
        (F.fpDist s e).toReal
            * (Set.indicator (whiteStrip half W) 1 (half - m + e.1, l + e.2) * mA)
          ≤ (F.fpDist s e).toReal
            * (Set.indicator (whiteStrip half W) 1 (half - m + e.1, l + e.2)
                * F.edgeWeight A m e) :=
      fun e => mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hew_ge e) (hind0 e)) (hf_nonneg e)
    calc p₀ * mA
        ≤ (∑' e : ℕ × ℤ, (F.fpDist s e).toReal
            * Set.indicator (whiteStrip half W) 1 (half - m + e.1, l + e.2)) * mA :=
          mul_le_mul_of_nonneg_right hwhite hmA0
      _ = ∑' e : ℕ × ℤ, (F.fpDist s e).toReal
            * (Set.indicator (whiteStrip half W) 1 (half - m + e.1, l + e.2) * mA) := by
          rw [← tsum_mul_right]; exact tsum_congr (fun e => by ring)
      _ ≤ _ := hsum_indmA.tsum_le_tsum hge hsum_indew
  have hSmain : ∑' e : ℕ × ℤ, (F.fpDist s e).toReal
      * ((1 - c * Set.indicator (whiteStrip half W) 1 (half - m + e.1, l + e.2))
          * F.edgeWeight A m e) ≤ mA := by
    have hcong : ∀ e : ℕ × ℤ,
        (F.fpDist s e).toReal
            * ((1 - c * Set.indicator (whiteStrip half W) 1 (half - m + e.1, l + e.2))
                * F.edgeWeight A m e)
          = (F.fpDist s e).toReal * F.edgeWeight A m e
            - c * ((F.fpDist s e).toReal
                * (Set.indicator (whiteStrip half W) 1 (half - m + e.1, l + e.2)
                    * F.edgeWeight A m e)) := fun e => by ring
    rw [tsum_congr hcong, Summable.tsum_sub hsum_ew (hsum_indew.mul_left c), tsum_mul_left]
    nlinarith [hedge, mul_le_mul_of_nonneg_left hindew_ge hc_pos.le, hmA0,
      mul_nonneg (mul_nonneg hc_pos.le hp₀pos.le) hmA0]
  have hpt : ∀ e : ℕ × ℤ,
      (F.fpDist s e).toReal * F.Q half W κ (half - m + e.1) (l + e.2)
        ≤ QM * ((F.fpDist s e).toReal
            * ((1 - c * Set.indicator (whiteStrip half W) 1 (half - m + e.1, l + e.2))
                * F.edgeWeight A m e)) := by
    intro e
    calc (F.fpDist s e).toReal * F.Q half W κ (half - m + e.1) (l + e.2)
        ≤ (F.fpDist s e).toReal
            * ((1 - c * Set.indicator (whiteStrip half W) 1 (half - m + e.1, l + e.2))
                * (F.edgeWeight A m e * QM)) :=
          mul_le_mul_of_nonneg_left (hendpt e) (hf_nonneg e)
      _ = QM * ((F.fpDist s e).toReal
            * ((1 - c * Set.indicator (whiteStrip half W) 1 (half - m + e.1, l + e.2))
                * F.edgeWeight A m e)) := by ring
  calc F.Q half W κ (half - m) l
      ≤ ∑' e : ℕ × ℤ, (F.fpDist s e).toReal
          * F.Q half W κ (half - m + e.1) (l + e.2) := hstep1
    _ ≤ ∑' e : ℕ × ℤ, QM * ((F.fpDist s e).toReal
          * ((1 - c * Set.indicator (whiteStrip half W) 1 (half - m + e.1, l + e.2))
              * F.edgeWeight A m e)) := hsum_Qe.tsum_le_tsum hpt (hsum_main.mul_left QM)
    _ = QM * ∑' e : ℕ × ℤ, (F.fpDist s e).toReal
          * ((1 - c * Set.indicator (whiteStrip half W) 1 (half - m + e.1, l + e.2))
              * F.edgeWeight A m e) := tsum_mul_left
    _ ≤ QM * mA := mul_le_mul_of_nonneg_left hSmain hQM0
    _ = mA * QM := mul_comm _ _

end Family

end GGMCollatz
