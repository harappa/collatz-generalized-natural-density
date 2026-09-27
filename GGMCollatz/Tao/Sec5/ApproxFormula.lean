import GGMCollatz.Tao.Sec5.Reindex

/-!
# The approximation formula (GGM §4 Step 2, Tao's Proposition 5.2, tao-collatz's node C8) and the per-row values

Derived from `TaoCollatz/Sec5/ApproxFormula.lean` (`first_passage_approx`, `approxMainTerm_eq_steppedMid`)
and `TaoCollatz/Sec5/Stabilization.lean` (`cn_bound`, `harmZfine_sub_mainZ_le_osc`, `perNTerm_eval`) of
gotrevor/tao-collatz (Apache-2.0), commit 15efca2; generalized to the GGM family (p, q, r). This is the
rewritten form of the approximation formula (its logarithmic part) and of Lemma 7.25 (the logarithmic profile) in the accompanying paper:

* `first_passage_approx`: `P(Pass_x(L_y) ∈ E) = Σ_{n ∈ I_y} P(a^{(n')} ∈ A^{(n')}, S^{n'}(L_y) ∈ E'(E))
  + O(log^{-1/5} x)` (`n' = n - m₀`, trimmed `I_y`; avoids GGM's gap (G1)).
* `row_reindex`: recount the term of row `n` via preimages (Lemma 7.9 of the paper, Tao's Lemma 2.1). The rows are
  complete (`N_{a,R,M} ∈ [y, y^α]`, see the accompanying paper), and
  `Z · (row) = E[1_{A} C^E_{n'}(F_{n'}(𝒢, 𝒰))] (1 + O(x^{-1/2}))`.
* `cE_le`: `C^E_k ≤ 1 + 2 log^{0.7} x` (crude upper bound from `E' ⊂ [Mlo, Mhi]`; replaces (G3) in the
  accompanying paper).
* `expect_good_cE`: remove the good-tuple restriction (the probability outside `A` is small).
* `expect_syracZ_cE`: `E[C^E_{n'}(𝒮_{n'})] = Ψ(E) + O(max C · Osc_{m₀, n'})` (the form in which GGM's
  Proposition 4.1 is used).
* `row_eval`: `|Z · (row n) - Ψ(E)| ≤ K log^{-2} x` (the per-row value depends neither on `n` nor on `y`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

variable (F : Family)

/-! ### The approximation formula -/

/-- **The approximation formula** (first half of GGM `eq: formula for pass depending on Aff_a,r`,
logarithmic form of Tao's Proposition 5.2). -/
theorem first_passage_approx (h33 : F.prop33_statement) :
    ∀ α β : ℝ, 1 < α → 1 < β → α ^ 2 * β ≤ F.thetaMax → ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop,
      ∀ y : ℝ, x ^ β ≤ y → y ≤ x ^ (α * β) → ∀ E : Set ℕ,
        |expect (F.logUnif y (y ^ α)) (Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ E} 1)
          - ∑ n ∈ F.Iy x y α, F.rowTerm β x E y α n| ≤ K * Real.log x ^ (-(1 / 5 : ℝ)) := by
  classical
  intro α β hα hβ hθ
  obtain ⟨Ke, hKe, hedge⟩ := F.edge_mass α hα
  refine ⟨Ke + 2, by positivity, ?_⟩
  filter_upwards [F.good_whp h33 α hα, hedge, F.event_identity β hβ, F.Iy_bounds α β hα hβ hθ,
    F.mem_Iy_of_not_edge α β hα hβ hθ, F.eventually_window_nonempty hα,
    eventually_log_ge 3, Filter.eventually_gt_atTop 1] with
    x hgood hedgex hEI hIb hIne hne hL hx1
  intro y hy1 hy2 E
  have hx0 : 0 ≤ x := by linarith
  have hLpos : 0 < Real.log x := by linarith
  have hxy : x < y := lt_of_lt_of_le (by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ < x ^ β := Real.rpow_lt_rpow_of_exponent_lt hx1 hβ) hy1
  have hy0 : 0 ≤ y := by linarith
  have hyα : y ^ α ≤ x ^ F.thetaMax := by
    calc y ^ α ≤ (x ^ (α * β)) ^ α := Real.rpow_le_rpow hy0 hy2 (by linarith)
      _ = x ^ (α ^ 2 * β) := by rw [← Real.rpow_mul hx0]; ring_nf
      _ ≤ x ^ F.thetaMax := Real.rpow_le_rpow_of_exponent_le hx1.le hθ
  have hW := hne y hxy.le
  set μ := F.logUnif y (y ^ α) with hμ
  set I := F.Iy x y α with hIdef
  set n₀ := F.nZero x with hn₀
  set m₀ := F.mZero β x with hm₀
  have hIcard : (I.card : ℝ) ≤ n₀ + 1 := by
    have : I.card ≤ n₀ + 1 := by
      rw [hIdef]; unfold Iy
      exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
    exact_mod_cast this
  set S : Set ℕ := {N | F.passLoc ⌊x⌋₊ N ∈ E} with hS
  set R : ℕ → Set ℕ := fun n => {N | F.goodVec x (F.valVec N (n - m₀)) ∧
      F.S^[n - m₀] N ∈ F.Eprime β x E} with hR
  set G : Set ℕ := {N | ¬ F.goodVec x (F.valVec N n₀)} with hG
  set Ed : Set ℕ := {N | F.edge x y α N} with hEd
  have hn0nn : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  set B : ℝ := n₀ + 2 with hB
  have hind : ∀ (T : Set ℕ) N, |Set.indicator T (1 : ℕ → ℝ) N| ≤ B := fun T N =>
    (abs_indicator_le_one T N).trans (by linarith)
  have hsumrow : ∑ n ∈ I, F.rowTerm β x E y α n
      = expect μ (fun N => ∑ n ∈ I, Set.indicator (R n) (1 : ℕ → ℝ) N) := by
    rw [expect_finset_sum μ I (fun n => Set.indicator (R n) 1) 1
      (fun n _ N => abs_indicator_le_one _ N)]
    rfl
  rw [hsumrow]
  set h : ℕ → ℝ := fun N => Set.indicator Ed 1 N + (n₀ + 1) * Set.indicator G 1 N with hh
  have hSumle : ∀ N, ∑ n ∈ I, Set.indicator (R n) (1 : ℕ → ℝ) N ≤ n₀ + 1 := by
    intro N
    calc _ ≤ ∑ _n ∈ I, (1 : ℝ) := Finset.sum_le_sum fun n _ =>
          (le_abs_self _).trans (abs_indicator_le_one _ N)
      _ = I.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ n₀ + 1 := hIcard
  have hSum0 : ∀ N, 0 ≤ ∑ n ∈ I, Set.indicator (R n) (1 : ℕ → ℝ) N := fun N =>
    Finset.sum_nonneg fun n _ => Set.indicator_nonneg (fun _ _ => zero_le_one) N
  have hsumbd : ∀ N, |∑ n ∈ I, Set.indicator (R n) (1 : ℕ → ℝ) N| ≤ B := by
    intro N
    rw [abs_of_nonneg (hSum0 N)]; linarith [hSumle N]
  have hhbd : ∀ N, |h N| ≤ B + (n₀ + 1) * B := by
    intro N
    have hE0 := Set.indicator_nonneg (fun _ _ => zero_le_one) (s := Ed) (f := (1 : ℕ → ℝ)) N
    have hG0 := Set.indicator_nonneg (fun _ _ => zero_le_one) (s := G) (f := (1 : ℕ → ℝ)) N
    have hE1 := (le_abs_self _).trans (abs_indicator_le_one Ed N)
    have hG1 := (le_abs_self _).trans (abs_indicator_le_one G N)
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  set B' : ℝ := B + (n₀ + 1) * B with hB'
  have hBB' : B ≤ B' := by
    have : 0 ≤ (n₀ + 1) * B := by positivity
    linarith
  -- pointwise bound
  have hpt : ∀ N ∈ μ.support, |Set.indicator S (1 : ℕ → ℝ) N
      - ∑ n ∈ I, Set.indicator (R n) (1 : ℕ → ℝ) N| ≤ h N := by
    intro N hN
    have hNW := F.mem_logWindow_of_mem_support hW hN
    obtain ⟨hNp, hyN, hNy⟩ := (F.mem_logWindow_iff).mp hNW
    have hxN : x < N := lt_of_lt_of_le hxy hyN
    have hNθ : (N : ℝ) ≤ x ^ F.thetaMax := le_trans hNy hyα
    have hS1 := (le_abs_self _).trans (abs_indicator_le_one S N)
    have hS0 := Set.indicator_nonneg (fun _ _ => zero_le_one) (s := S) (f := (1 : ℕ → ℝ)) N
    have hE0 := Set.indicator_nonneg (fun _ _ => zero_le_one) (s := Ed) (f := (1 : ℕ → ℝ)) N
    by_cases hg : F.goodVec x (F.valVec N n₀)
    · -- good tuple: the sum over rows is `1[T ∈ I ∧ Pass ∈ E]`
      have hRn : ∀ n ∈ I, Set.indicator (R n) (1 : ℕ → ℝ) N
          = if F.passTime ⌊x⌋₊ N = n then (if F.passLoc ⌊x⌋₊ N ∈ E then 1 else 0) else 0 := by
        intro n hn
        obtain ⟨h2m, hn0⟩ := hIb y hy1 hy2 n hn
        have hiff := hEI N hNp hxN hNθ hg n h2m hn0 E
        have hgn : F.goodVec x (F.valVec N (n - m₀)) := F.goodVec_prefix hg (by omega)
        simp only [hR, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
        by_cases h1 : F.passTime ⌊x⌋₊ N = n
        · by_cases h2 : F.passLoc ⌊x⌋₊ N ∈ E
          · rw [if_pos ⟨hgn, hiff.mpr ⟨h1, h2⟩⟩, if_pos h1, if_pos h2]
          · rw [if_neg (fun h' => h2 (hiff.mp h'.2).2), if_pos h1, if_neg h2]
        · rw [if_neg (fun h' => h1 (hiff.mp h'.2).1), if_neg h1]
      have hsum : ∑ n ∈ I, Set.indicator (R n) (1 : ℕ → ℝ) N
          = if F.passTime ⌊x⌋₊ N ∈ I then (if F.passLoc ⌊x⌋₊ N ∈ E then 1 else 0) else 0 := by
        rw [Finset.sum_congr rfl hRn, Finset.sum_ite_eq]
      have hGN : Set.indicator G (1 : ℕ → ℝ) N = 0 := by
        rw [Set.indicator_of_notMem (by simp only [hG, Set.mem_setOf_eq, not_not]; exact hg)]
      by_cases hed : F.edge x y α N
      · -- edge: the difference is at most 1
        have hEd1 : Set.indicator Ed (1 : ℕ → ℝ) N = 1 := by
          rw [Set.indicator_of_mem (by simpa [hEd] using hed)]; rfl
        have hsum1 : ∑ n ∈ I, Set.indicator (R n) (1 : ℕ → ℝ) N ≤ 1 := by
          rw [hsum]; split_ifs <;> norm_num
        have hh1 : h N = 1 := by simp only [hh, hEd1, hGN, mul_zero, add_zero]
        rw [hh1, abs_le]; constructor <;> linarith [hSum0 N]
      · have hTI := hIne y hy1 hy2 N hNW hg hed
        have hSN : Set.indicator S (1 : ℕ → ℝ) N = if F.passLoc ⌊x⌋₊ N ∈ E then 1 else 0 := by
          simp only [hS, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
        rw [hsum, if_pos hTI, hSN, sub_self, abs_zero]
        have hh0 : h N = Set.indicator Ed (1 : ℕ → ℝ) N := by
          simp only [hh, hGN, mul_zero, add_zero]
        rw [hh0]; exact hE0
    · -- bad tuple: the difference is at most `n₀ + 1`
      have hGN : Set.indicator G (1 : ℕ → ℝ) N = 1 := by
        rw [Set.indicator_of_mem (by simpa [hG] using hg)]; rfl
      have hhN : h N = Set.indicator Ed (1 : ℕ → ℝ) N + (n₀ + 1) := by
        simp only [hh, hGN, mul_one]
      rw [hhN, abs_le]; constructor <;> linarith [hSum0 N, hSumle N]
  have hmain := abs_expect_sub_le_of_support μ B' (fun N => (hind S N).trans hBB')
    (fun N => (hsumbd N).trans hBB') hhbd hpt
  have hexp : expect μ h
      = expect μ (Set.indicator Ed 1) + (n₀ + 1) * expect μ (Set.indicator G 1) := by
    rw [hh, expect_add μ ((n₀ + 1) * 1) (fun N => (abs_indicator_le_one Ed N).trans (by linarith))
      (fun N => by
        rw [abs_mul, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (abs_indicator_le_one G N) (by positivity)),
      expect_const_mul]
  have hEdb := hedgex y hxy.le
  have hGb := hgood y hxy.le
  set L := Real.log x with hLdef
  have hn0L : (n₀ : ℝ) + 1 ≤ L := by
    have := F.nZero_le hx1.le; linarith
  have hL4 : L * L ^ (-4 : ℝ) ≤ L ^ (-(1 / 5 : ℝ)) := by
    have : L * L ^ (-4 : ℝ) = L ^ (-3 : ℝ) := by
      rw [show (-3 : ℝ) = 1 + (-4) by norm_num, Real.rpow_add hLpos, Real.rpow_one]
    rw [this]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hL4nn : 0 ≤ L ^ (-4 : ℝ) := Real.rpow_nonneg hLpos.le _
  calc _ ≤ expect μ h := hmain
    _ = expect μ (Set.indicator Ed 1) + (n₀ + 1) * expect μ (Set.indicator G 1) := hexp
    _ ≤ Ke * L ^ (-(1 / 5 : ℝ)) + L * (2 * L ^ (-4 : ℝ)) := by
        apply add_le_add hEdb
        exact mul_le_mul hn0L hGb (expect_indicator_nonneg _ _) (by linarith)
    _ ≤ Ke * L ^ (-(1 / 5 : ℝ)) + 2 * L ^ (-(1 / 5 : ℝ)) := by nlinarith
    _ = (Ke + 2) * L ^ (-(1 / 5 : ℝ)) := by ring


/-! ### Per-row values -/

/-- `C^E_k ≥ 0`. -/
theorem cE_nonneg (β x : ℝ) (E : Set ℕ) (k : ℕ) (Y : ZMod (F.q ^ k)) : 0 ≤ F.cE β x E k Y := by
  unfold cE
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun M _ => by positivity)

/-- **Crude upper bound on `C_k`** (replaces `C_n = O(1)` of GGM Step 3): for `k ≤ n₀`,
`C^E_k(Y) ≤ 1 + 2 log^{0.7} x`. -/
theorem cE_le : ∀ β : ℝ, 1 < β → ∀ᶠ x : ℝ in Filter.atTop, ∀ E : Set ℕ, ∀ k ≤ F.nZero x,
    ∀ Y : ZMod (F.q ^ k), F.cE β x E k Y ≤ 1 + 2 * Real.log x ^ (0.7 : ℝ) := by
  classical
  intro β hβ
  have hq := F.log_q_pos
  have hd := F.drift_pos
  filter_upwards [eventually_add_mul_rpow_le (show (0.7:ℝ) < 1 by norm_num) one_pos 0 1
      (show (0:ℝ) < 4 / 5 by norm_num), eventually_log_ge 0, Filter.eventually_gt_atTop 0] with
    x hW hL0 hx0
  rw [zero_add, one_mul, Real.rpow_one] at hW
  intro E k hk Y
  set L := Real.log x with hLdef
  set W := L ^ (0.7 : ℝ) with hWdef
  set m₀ := F.mZero β x with hm₀
  have hMlo : 0 < F.Mlo β x := Real.exp_pos _
  have hMlohi : F.Mlo β x ≤ F.Mhi β x := by
    unfold Mlo Mhi; apply Real.exp_le_exp.mpr
    have : 0 ≤ W := Real.rpow_nonneg hL0 _
    linarith
  have hQ : 0 < F.q ^ k := pow_pos F.q_pos k
  have hsum := sum_inv_le_of_modEq hQ hMlo
    ((F.Eprime β x E).filter (fun M : ℕ => ((M : ℕ) : ZMod (F.q ^ k)) = Y)) (F.Mhi β x) hMlohi
    (fun M hM => by
      have hM' := (Finset.mem_filter.mp hM).1
      unfold Eprime at hM'
      simp only [Finset.mem_filter, Finset.mem_range] at hM'
      refine ⟨hM'.2.2.1, ?_⟩
      have : M ≤ ⌊F.Mhi β x⌋₊ := by omega
      exact le_trans (by exact_mod_cast this) (Nat.floor_le (le_trans hMlo.le hMlohi)))
    (fun M hM M' hM' => by
      have h1 := (Finset.mem_filter.mp hM).2
      have h2 := (Finset.mem_filter.mp hM').2
      exact (ZMod.natCast_eq_natCast_iff' M M' (F.q ^ k)).mp (h1.trans h2.symm))
  have hratio : Real.log (F.Mhi β x / F.Mlo β x) = 2 * W := by
    unfold Mhi Mlo; rw [← Real.exp_sub, Real.log_exp]; ring
  rw [hratio] at hsum
  -- `q^k ≤ Mlo`
  have hqk : ((F.q ^ k : ℕ) : ℝ) ≤ F.Mlo β x := by
    have hn0 : (F.nZero x : ℝ) ≤ L / (5 * Real.log F.q) := by
      unfold nZero; exact Nat.floor_le (by positivity)
    have hkR : (k : ℝ) ≤ F.nZero x := by exact_mod_cast hk
    push_cast
    rw [← Real.exp_log F.q_real_pos, ← Real.exp_nat_mul]
    unfold Mlo
    apply Real.exp_le_exp.mpr
    have h1 : (k : ℝ) * Real.log F.q ≤ L / 5 := by
      calc (k : ℝ) * Real.log F.q ≤ L / (5 * Real.log F.q) * Real.log F.q :=
            mul_le_mul_of_nonneg_right (le_trans hkR hn0) hq.le
        _ = L / 5 := by field_simp
    have h2 : 0 ≤ F.drift * m₀ := mul_nonneg hd.le (Nat.cast_nonneg _)
    linarith
  unfold cE
  have hQR : (0 : ℝ) < ((F.q ^ k : ℕ) : ℝ) := by exact_mod_cast hQ
  calc (F.q : ℝ) ^ k * ∑ M ∈ (F.Eprime β x E).filter
          (fun M : ℕ => ((M : ℕ) : ZMod (F.q ^ k)) = Y), (M : ℝ)⁻¹
      ≤ ((F.q ^ k : ℕ) : ℝ) * ((F.Mlo β x)⁻¹ + 2 * W / ((F.q ^ k : ℕ) : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hsum hQR.le
        push_cast at this ⊢
        exact this
    _ = ((F.q ^ k : ℕ) : ℝ) / F.Mlo β x + 2 * W := by field_simp
    _ ≤ 1 + 2 * W := by
        have : ((F.q ^ k : ℕ) : ℝ) / F.Mlo β x ≤ 1 := by rw [div_le_one hMlo]; exact hqk
        linarith

/-- **Recounting via preimages** (Lemma 7.9 of the paper, Tao's Lemma 2.1; the rows are complete). -/
theorem row_reindex : ∀ α β : ℝ, 1 < α → 1 < β → α ^ 2 * β ≤ F.thetaMax →
    ∀ᶠ x : ℝ in Filter.atTop, ∀ y : ℝ, x ^ β ≤ y → y ≤ x ^ (α * β) → ∀ E : Set ℕ,
      ∀ n ∈ F.Iy x y α,
        |F.windowMass y (y ^ α) * F.rowTerm β x E y α n
          - expect (PMF.iid (stepLaw F.p) (n - F.mZero β x))
              (fun v => Set.indicator {v : Fin (n - F.mZero β x) → ℕ × ℕ |
                  F.goodVec x (fun i => (v i).1)} 1 v *
                F.cE β x E (n - F.mZero β x) (F.offsetFwd v))|
          ≤ Real.log x ^ (-4 : ℝ) := by
  classical
  intro α β hα hβ hθ
  have hp := F.log_p_pos
  have hq := F.log_q_pos
  have hd := F.drift_pos
  have hμ := F.mu_pos
  set R : ℝ := (F.rBound : ℝ) with hR
  have hR0 : 0 ≤ R := Int.cast_nonneg_iff.mpr F.rBound_nonneg
  filter_upwards [F.cE_le β hβ, F.Iy_bounds α β hα hβ hθ, F.eventually_window_nonempty hα,
    eventually_add_mul_rpow_le (show (0.6:ℝ) < 0.8 by norm_num) (by norm_num) 1 (Real.log F.p)
      (show 0 < F.drift / 2 by positivity),
    eventually_add_mul_rpow_le (show (0.7:ℝ) < 0.8 by norm_num) (by norm_num) 0 1
      (show 0 < F.drift / 2 by positivity),
    eventually_add_mul_rpow_le (show (0.7:ℝ) < 1 by norm_num) one_pos 0 1
      (show (0:ℝ) < 1 / 5 by norm_num),
    eventually_mul_rpow_neg_le_log (show (0:ℝ) < 3 / 5 by norm_num) 5 (6 * R),
    eventually_log_ge 1, Filter.eventually_gt_atTop 1] with
    x hC hIb hne hc1 hc2 hW5 hε hL hx1
  intro y hy1 hy2 E n hn
  rw [zero_add, one_mul] at hc2
  rw [zero_add, one_mul, Real.rpow_one] at hW5
  set L := Real.log x with hLdef
  set t := L ^ (0.6 : ℝ) with htdef
  set W := L ^ (0.7 : ℝ) with hWdef
  set V := L ^ (0.8 : ℝ) with hVdef
  set m₀ := F.mZero β x with hm₀
  set k := n - m₀ with hk
  have hLpos : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  have ht0 : 0 ≤ t := Real.rpow_nonneg hLpos.le _
  have hW0 : 0 ≤ W := Real.rpow_nonneg hLpos.le _
  obtain ⟨h2m, hnn₀⟩ := hIb y hy1 hy2 n hn
  have hkn₀ : k ≤ F.nZero x := by omega
  have hkm : k + m₀ = n := by omega
  have hxβ : x < x ^ β := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ < x ^ β := Real.rpow_lt_rpow_of_exponent_lt hx1 hβ
  have hxy : x < y := lt_of_lt_of_le hxβ hy1
  have hy0 : 0 < y := by linarith
  have hWne := hne y hxy.le
  have hZpos := F.windowMass_pos hWne
  set Wd := F.logWindow y (y ^ α) with hWd
  set Ep := F.Eprime β x E with hEp
  set Rp : ℕ → Prop := fun N => F.goodVec x (F.valVec N k) ∧ F.S^[k] N ∈ Ep with hRp
  set SN := Wd.filter Rp with hSN
  -- size of the elements of `E'`
  have hEpmem : ∀ M ∈ Ep, M % F.p ≠ 0 ∧ F.Mlo β x ≤ (M : ℝ) ∧ (M : ℝ) ≤ F.Mhi β x := by
    intro M hM
    rw [hEp] at hM
    unfold Eprime at hM
    simp only [Finset.mem_filter, Finset.mem_range] at hM
    refine ⟨hM.2.1, hM.2.2.1, ?_⟩
    have hMhi0 : 0 ≤ F.Mhi β x := (Real.exp_pos _).le
    have : M ≤ ⌊F.Mhi β x⌋₊ := by omega
    exact le_trans (by exact_mod_cast this) (Nat.floor_le hMhi0)
  -- `q^k R / M ≤ ε₀ = log^{-5} x / 6`
  set ε₀ : ℝ := L ^ (-5 : ℝ) / 6 with hε₀
  have hqk : (F.q : ℝ) ^ k ≤ Real.exp (L / 5) := by
    rw [← Real.exp_log F.q_real_pos, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hn0 : (F.nZero x : ℝ) ≤ L / (5 * Real.log F.q) := by
      unfold nZero; exact Nat.floor_le (by positivity)
    have hkR : (k : ℝ) ≤ F.nZero x := by exact_mod_cast hkn₀
    calc (k : ℝ) * Real.log F.q ≤ L / (5 * Real.log F.q) * Real.log F.q :=
          mul_le_mul_of_nonneg_right (le_trans hkR hn0) hq.le
      _ = L / 5 := by field_simp
  have hMlo : Real.exp (4 * L / 5) ≤ F.Mlo β x := by
    unfold Mlo; apply Real.exp_le_exp.mpr
    have : 0 ≤ F.drift * m₀ := mul_nonneg hd.le (Nat.cast_nonneg _)
    rw [← hLdef, ← hWdef, ← hm₀]; linarith
  have hsmall : ∀ M : ℝ, F.Mlo β x ≤ M → (F.q : ℝ) ^ k * R / M ≤ ε₀ := by
    intro M hM
    have hMpos : 0 < M := lt_of_lt_of_le (Real.exp_pos _) (le_trans hMlo hM)
    rw [div_le_iff₀ hMpos]
    have h1 : (F.q : ℝ) ^ k * R ≤ Real.exp (L / 5) * R := mul_le_mul_of_nonneg_right hqk hR0
    have h2 : 6 * R * x ^ (-(3 / 5 : ℝ)) ≤ L ^ (-5 : ℝ) := hε
    have h3 : x ^ (-(3 / 5 : ℝ)) = Real.exp (-(3 * L / 5)) := by
      rw [Real.rpow_def_of_pos hx0]; congr 1; ring
    rw [h3] at h2
    have h4 : Real.exp (L / 5) * Real.exp (-(3 * L / 5)) * Real.exp (4 * L / 5) = Real.exp (2 * L / 5) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    -- `exp(L/5) R ≤ ε₀ exp(4L/5)`
    have h5 : Real.exp (L / 5) * R ≤ ε₀ * Real.exp (4 * L / 5) := by
      rw [hε₀]
      have h6 : R * Real.exp (-(3 * L / 5)) ≤ L ^ (-5 : ℝ) / 6 := by linarith
      have h7 : Real.exp (L / 5) * R = R * Real.exp (-(3 * L / 5)) * Real.exp (4 * L / 5) := by
        have e : -(3 * L / 5) + 4 * L / 5 = L / 5 := by ring
        rw [mul_assoc, ← Real.exp_add, e, mul_comm]
      rw [h7]
      exact mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le
    calc (F.q : ℝ) ^ k * R ≤ Real.exp (L / 5) * R := h1
      _ ≤ ε₀ * Real.exp (4 * L / 5) := h5
      _ ≤ ε₀ * M := by
          apply mul_le_mul_of_nonneg_left (le_trans hMlo hM)
          rw [hε₀]; exact div_nonneg (Real.rpow_nonneg hLpos.le _) (by norm_num)
  have hε₀le : ε₀ ≤ 1 / 2 := by
    rw [hε₀]
    have : L ^ (-5 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by norm_num)
    linarith
  -- size of the preimage: `log N = log M + (|a| - μk) log p + dk + O(1)`
  have hlogN : ∀ (N M A : ℕ) (f : ℤ), 0 < N → M % F.p ≠ 0 → F.Mlo β x ≤ (M : ℝ) →
      (F.q : ℤ) ^ k * N = (F.p : ℤ) ^ A * M - f → |(f : ℝ)| ≤ (F.p : ℝ) ^ A * (F.q : ℝ) ^ k * R →
      |Real.log N - (Real.log M + A * Real.log F.p - k * Real.log F.q)| ≤ 1 ∧
        |(N : ℝ)⁻¹ - ((F.p : ℝ) ^ A)⁻¹ * (F.q : ℝ) ^ k * (M : ℝ)⁻¹|
          ≤ 2 * ε₀ * (((F.p : ℝ) ^ A)⁻¹ * (F.q : ℝ) ^ k * (M : ℝ)⁻¹) := by
    intro N M A f hN0 _ hMlo' hNeq hfb
    have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (Real.exp_pos _) hMlo'
    have hpA : (0 : ℝ) < (F.p : ℝ) ^ A := pow_pos F.p_real_pos A
    have hqk0 : (0 : ℝ) < (F.q : ℝ) ^ k := pow_pos F.q_real_pos k
    set B := (F.p : ℝ) ^ A * M with hB
    have hBpos : 0 < B := mul_pos hpA hMpos
    set u := (f : ℝ) / B with hu
    have hu2 : |u| ≤ ε₀ := by
      rw [hu, abs_div, abs_of_pos hBpos, div_le_iff₀ hBpos]
      have := hsmall M hMlo'
      rw [div_le_iff₀ hMpos] at this
      calc |(f : ℝ)| ≤ (F.p : ℝ) ^ A * ((F.q : ℝ) ^ k * R) := by linarith
        _ ≤ (F.p : ℝ) ^ A * (ε₀ * M) := mul_le_mul_of_nonneg_left this hpA.le
        _ = ε₀ * B := by rw [hB]; ring
    have hu12 : |u| ≤ 1 / 2 := le_trans hu2 hε₀le
    have hNR : (F.q : ℝ) ^ k * N = B * (1 - u) := by
      have : ((F.q : ℤ) ^ k * N : ℤ) = ((F.p : ℤ) ^ A * M - f : ℤ) := hNeq
      have h' : (F.q : ℝ) ^ k * N = (F.p : ℝ) ^ A * M - f := by exact_mod_cast this
      rw [h', hu, hB]; field_simp
    have hN : (N : ℝ) = B * (1 - u) / (F.q : ℝ) ^ k := by
      rw [eq_div_iff hqk0.ne', mul_comm]; exact hNR
    have h1u : 0 < 1 - u := by linarith [(abs_le.mp hu12).2]
    constructor
    · have hlogNval : Real.log N
          = A * Real.log F.p + Real.log M + Real.log (1 - u) - k * Real.log F.q := by
        rw [hN, Real.log_div (by positivity) hqk0.ne', Real.log_mul hBpos.ne' h1u.ne',
          hB, Real.log_mul hpA.ne' hMpos.ne', Real.log_pow, Real.log_pow]
      rw [hlogNval]
      convert abs_log_one_sub_le hu12 using 2
      ring
    · have hinv : (N : ℝ)⁻¹ = (F.q : ℝ) ^ k * (B * (1 - u))⁻¹ := by
        rw [hN, inv_div, div_eq_mul_inv]
      have hg : ((F.p : ℝ) ^ A)⁻¹ * (F.q : ℝ) ^ k * (M : ℝ)⁻¹ = (F.q : ℝ) ^ k * B⁻¹ := by
        rw [hB, mul_inv]; ring
      rw [hinv, hg, ← mul_sub, abs_mul, abs_of_pos hqk0]
      have := abs_inv_mul_one_sub_sub_le hBpos hu12
      calc (F.q : ℝ) ^ k * |(B * (1 - u))⁻¹ - B⁻¹| ≤ (F.q : ℝ) ^ k * (2 * |u| * B⁻¹) :=
            mul_le_mul_of_nonneg_left this hqk0.le
        _ ≤ (F.q : ℝ) ^ k * (2 * ε₀ * B⁻¹) := by
            apply mul_le_mul_of_nonneg_left _ hqk0.le
            apply mul_le_mul_of_nonneg_right _ (inv_pos.mpr hBpos).le
            linarith
        _ = 2 * ε₀ * ((F.q : ℝ) ^ k * B⁻¹) := by ring
  -- completeness of the rows (see the accompanying paper)
  have hcomplete : ∀ v : Fin k → ℕ × ℕ, F.validVec v → F.goodVec x (fun i => (v i).1) →
      ∀ M ∈ Ep, ((M : ℕ) : ZMod (F.q ^ k)) = F.offsetFwd v →
        ∃ N ∈ SN, F.vecOf N k = v ∧ F.S^[k] N = M := by
    intro v hv hg M hM hMc
    obtain ⟨hMp, hMlo', hMhi'⟩ := hEpmem M hM
    have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (Real.exp_pos _) hMlo'
    set A := pre (fun i => (v i).1) k with hA
    set f := F.fint (fun i => (v i).1) (fun i => F.r (v i).2) with hf
    have hfb : |(f : ℝ)| ≤ (F.p : ℝ) ^ A * (F.q : ℝ) ^ k * R := by
      have := F.abs_fint_le (fun i => (v i).1) (fun i => F.r (v i).2) F.rBound_nonneg
        (fun m => F.abs_r_le_rBound (hv m).2.2)
      rw [hR]; exact_mod_cast this
    have hpos : f < (F.p : ℤ) ^ A * M := by
      have h1 := hsmall M hMlo'
      rw [div_le_iff₀ hMpos] at h1
      have h2 : (f : ℝ) < (F.p : ℝ) ^ A * M := by
        have hpA : (0 : ℝ) < (F.p : ℝ) ^ A := pow_pos F.p_real_pos A
        calc (f : ℝ) ≤ |(f : ℝ)| := le_abs_self _
          _ ≤ (F.p : ℝ) ^ A * ((F.q : ℝ) ^ k * R) := by linarith
          _ ≤ (F.p : ℝ) ^ A * (ε₀ * M) := mul_le_mul_of_nonneg_left h1 hpA.le
          _ < (F.p : ℝ) ^ A * M := by
              apply mul_lt_mul_of_pos_left _ hpA
              nlinarith
      exact_mod_cast h2
    obtain ⟨N, hNp, hvN, hSN', hqN⟩ := F.exists_preimage hv hMp hMc hpos
    have hN0 : 0 < N := Nat.pos_of_ne_zero (fun h0 => hNp (by simp [h0]))
    have hval : F.valVec N k = fun i => (v i).1 := by
      rw [← hvN]; rfl
    have hgN : F.goodVec x (F.valVec N k) := by rw [hval]; exact hg
    refine ⟨N, ?_, hvN, hSN'⟩
    rw [hSN, Finset.mem_filter]
    refine ⟨?_, hgN, by rw [hSN']; exact hM⟩
    -- lies in the window
    obtain ⟨hlog, _⟩ := hlogN N M A f hN0 hMp hMlo' hqN hfb
    have hAdev : |(A : ℝ) - F.mu * k| < t := hg k le_rfl
    have hlogM1 : F.drift * m₀ + L - W ≤ Real.log M := by
      have := Real.log_le_log (Real.exp_pos _) hMlo'
      unfold Mlo at this; rwa [Real.log_exp] at this
    have hlogM2 : Real.log M ≤ F.drift * m₀ + L + W := by
      have := Real.log_le_log hMpos hMhi'
      unfold Mhi at this; rwa [Real.log_exp] at this
    have hnR : (n : ℝ) = k + m₀ := by rw [← hkm]; push_cast; ring
    have hIn := hn
    unfold Iy at hIn
    rw [Finset.mem_filter] at hIn
    obtain ⟨_, hI1, hI2⟩ := hIn
    rw [Real.log_div hy0.ne' hx0.ne'] at hI1
    rw [Real.log_div (by positivity) hx0.ne', Real.log_rpow hy0] at hI2
    have hI1' : Real.log y - L + F.drift * V ≤ F.drift * n := by
      have := mul_le_mul_of_nonneg_left hI1 hd.le
      rw [mul_add, mul_div_cancel₀ _ hd.ne', ← hLdef, ← hVdef] at this; linarith
    have hI2' : F.drift * n ≤ α * Real.log y - L - F.drift * V := by
      have := mul_le_mul_of_nonneg_left hI2 hd.le
      rw [mul_sub, mul_div_cancel₀ _ hd.ne', ← hLdef, ← hVdef] at this; linarith
    have hdk : A * Real.log F.p - k * Real.log F.q
        = ((A : ℝ) - F.mu * k) * Real.log F.p + F.drift * k := by
      unfold drift; ring
    have hdev2 : |((A : ℝ) - F.mu * k) * Real.log F.p| ≤ t * Real.log F.p := by
      rw [abs_mul, abs_of_pos hp]; exact mul_le_mul_of_nonneg_right hAdev.le hp.le
    have hN0R : (0 : ℝ) < N := by exact_mod_cast hN0
    have hdn : F.drift * n = F.drift * k + F.drift * m₀ := by rw [hnR]; ring
    have hly : Real.log y ≤ Real.log N := by
      have := (abs_le.mp hlog).1
      have := (abs_le.mp hdev2).1
      linarith
    have hlyα : Real.log N ≤ α * Real.log y := by
      have := (abs_le.mp hlog).2
      have := (abs_le.mp hdev2).2
      linarith
    refine (F.mem_logWindow_iff).mpr ⟨hNp, ?_, ?_⟩
    · rw [← Real.exp_log hy0, ← Real.exp_log hN0R]; exact Real.exp_le_exp.mpr hly
    · rw [← Real.exp_log hN0R, ← Real.exp_log (show 0 < y ^ α by positivity), Real.log_rpow hy0]
      exact Real.exp_le_exp.mpr hlyα
  -- left-hand side: `Z · (row) = Σ_{N ∈ SN} 1/N`
  have hLHS : F.windowMass y (y ^ α) * F.rowTerm β x E y α n = ∑ N ∈ SN, (N : ℝ)⁻¹ := by
    unfold rowTerm
    rw [F.expect_logUnif hWne, ← hWd, mul_div_assoc', mul_div_cancel_left₀ _ hZpos.ne', hSN,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun N _ => ?_
    by_cases hR' : Rp N
    · rw [if_pos hR', Set.indicator_of_mem (show N ∈ {N | F.goodVec x (F.valVec N (n - m₀)) ∧
        F.S^[n - m₀] N ∈ F.Eprime β x E} from hR')]; simp
    · rw [if_neg hR', Set.indicator_of_notMem (show N ∉ {N | F.goodVec x (F.valVec N (n - m₀)) ∧
        F.S^[n - m₀] N ∈ F.Eprime β x E} from hR')]; simp
  -- right-hand side: `E[1_A C(F)] = Σ_{N ∈ SN} p^{-|a|} q^k / S^k(N)`
  set g : ℕ → ℝ := fun N => ((F.p : ℝ) ^ pre (F.valVec N k) k)⁻¹ * (F.q : ℝ) ^ k *
    ((F.S^[k] N : ℕ) : ℝ)⁻¹ with hg
  set V := SN.image (fun N => F.vecOf N k) with hV
  have hSNmem : ∀ N ∈ SN, N % F.p ≠ 0 ∧ F.goodVec x (F.valVec N k) ∧ F.S^[k] N ∈ Ep := by
    intro N hN
    rw [hSN, Finset.mem_filter] at hN
    exact ⟨((F.mem_logWindow_iff).mp hN.1).1, hN.2.1, hN.2.2⟩
  have hfiber : ∀ v ∈ V, (Ep.filter (fun M : ℕ => ((M : ℕ) : ZMod (F.q ^ k)) = F.offsetFwd v))
      = (SN.filter (fun N => F.vecOf N k = v)).image (fun N => F.S^[k] N) := by
    intro v hv
    rw [hV, Finset.mem_image] at hv
    obtain ⟨N₀, hN₀, rfl⟩ := hv
    obtain ⟨hN₀p, hN₀g, _⟩ := hSNmem N₀ hN₀
    ext M
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hM, hMc⟩
      obtain ⟨N, hN, hvN, hSM⟩ := hcomplete (F.vecOf N₀ k) (F.vecOf_valid hN₀p k) hN₀g M hM hMc
      exact ⟨N, Finset.mem_filter.mpr ⟨hN, hvN⟩, hSM⟩
    · rintro ⟨N, hN, rfl⟩
      rw [Finset.mem_filter] at hN
      obtain ⟨hNp, _, hNE⟩ := hSNmem N hN.1
      refine ⟨hNE, ?_⟩
      rw [← hN.2, F.offsetFwd_vecOf hNp]
  have hinj : ∀ v ∈ V, Set.InjOn (fun N => F.S^[k] N)
      ((SN.filter (fun N => F.vecOf N k = v)) : Set ℕ) := by
    intro v _ N hN N' hN' hS
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hN hN'
    exact F.vecOf_injective (hSNmem N hN.1).1 (hSNmem N' hN'.1).1 (hN.2.trans hN'.2.symm) hS
  have hRHS : expect (PMF.iid (stepLaw F.p) k)
      (fun v => Set.indicator {v : Fin k → ℕ × ℕ | F.goodVec x (fun i => (v i).1)} 1 v *
        F.cE β x E k (F.offsetFwd v)) = ∑ N ∈ SN, g N := by
    unfold expect
    have hzero : ∀ v ∉ V, ((PMF.iid (stepLaw F.p) k) v).toReal *
        (Set.indicator {v : Fin k → ℕ × ℕ | F.goodVec x (fun i => (v i).1)} 1 v *
          F.cE β x E k (F.offsetFwd v)) = 0 := by
      intro v hv
      by_cases hP : (PMF.iid (stepLaw F.p) k) v = 0
      · rw [hP]; simp
      · have hvalid := F.validVec_of_ne_zero hP
        by_cases hgood : F.goodVec x (fun i => (v i).1)
        · have hempty : Ep.filter (fun M : ℕ => ((M : ℕ) : ZMod (F.q ^ k)) = F.offsetFwd v) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro M hM hMc
            obtain ⟨N, hN, hvN, _⟩ := hcomplete v hvalid hgood M hM hMc
            exact hv (by rw [hV, Finset.mem_image]; exact ⟨N, hN, hvN⟩)
          unfold cE
          rw [← hEp, hempty, Finset.sum_empty]; simp
        · rw [Set.indicator_of_notMem (show v ∉ {v : Fin k → ℕ × ℕ |
            F.goodVec x (fun i => (v i).1)} from hgood)]; simp
    rw [tsum_eq_sum hzero]
    · rw [← Finset.sum_fiberwise_of_maps_to (s := SN) (t := V) (g := fun N => F.vecOf N k)
        (fun N hN => Finset.mem_image_of_mem _ hN)]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hv' := hv
      rw [hV, Finset.mem_image] at hv'
      obtain ⟨N₀, hN₀, hvN₀⟩ := hv'
      obtain ⟨hN₀p, hN₀g, _⟩ := hSNmem N₀ hN₀
      have hvalid : F.validVec v := by rw [← hvN₀]; exact F.vecOf_valid hN₀p k
      have hgood : F.goodVec x (fun i => (v i).1) := by rw [← hvN₀]; exact hN₀g
      rw [F.stepLaw_iid_toReal_of_valid hvalid, Set.indicator_of_mem (show v ∈ {v : Fin k → ℕ × ℕ |
        F.goodVec x (fun i => (v i).1)} from hgood), Pi.one_apply, one_mul]
      unfold cE
      rw [← hEp, hfiber v hv, Finset.sum_image (hinj v hv), Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun N hN => ?_
      rw [Finset.mem_filter] at hN
      have hpre : pre (fun i => (v i).1) k = pre (F.valVec N k) k := by rw [← hN.2]; rfl
      rw [hg, hpre]; ring
  -- upper bound on the right-hand side
  have hRHSle : ∑ N ∈ SN, g N ≤ 1 + 2 * W := by
    rw [← hRHS]
    have hB : ∀ v, |Set.indicator {v : Fin k → ℕ × ℕ | F.goodVec x (fun i => (v i).1)} 1 v *
        F.cE β x E k (F.offsetFwd v)| ≤ 1 + 2 * W := by
      intro v
      rw [abs_mul, abs_of_nonneg (F.cE_nonneg β x E k _)]
      calc |Set.indicator {v : Fin k → ℕ × ℕ | F.goodVec x (fun i => (v i).1)} (1 : (Fin k → ℕ × ℕ) → ℝ) v|
            * F.cE β x E k (F.offsetFwd v) ≤ 1 * (1 + 2 * W) :=
            mul_le_mul (abs_indicator_le_one _ v) (hC E k hkn₀ _) (F.cE_nonneg β x E k _) zero_le_one
        _ = 1 + 2 * W := one_mul _
    have := expect_mono (PMF.iid (stepLaw F.p) k) (g := fun _ => 1 + 2 * W) (1 + 2 * W) hB
      (fun _ => by rw [abs_of_nonneg (by linarith)]) (fun v => (le_abs_self _).trans (hB v))
    refine this.trans (le_of_eq ?_)
    unfold expect
    rw [tsum_mul_right, tsum_toReal_eq_one, one_mul]
  -- termwise comparison
  have hterm : ∀ N ∈ SN, |(N : ℝ)⁻¹ - g N| ≤ 2 * ε₀ * g N := by
    intro N hN
    obtain ⟨hNp, _, hNE⟩ := hSNmem N hN
    obtain ⟨hMp, hMlo', _⟩ := hEpmem _ hNE
    have hN0 : 0 < N := Nat.pos_of_ne_zero (fun h0 => hNp (by simp [h0]))
    have hkey := F.syr_iterate_key hNp k
    have hfb : |((F.fint (F.valVec N k) (F.resVec N k) : ℤ) : ℝ)|
        ≤ (F.p : ℝ) ^ pre (F.valVec N k) k * (F.q : ℝ) ^ k * R := by
      have := F.abs_fint_le (F.valVec N k) (F.resVec N k) F.rBound_nonneg
        (fun m => F.abs_r_le_rBound (F.digVec_pos_lt hNp k m).2)
      rw [hR]; exact_mod_cast this
    have hqN : (F.q : ℤ) ^ k * N = (F.p : ℤ) ^ pre (F.valVec N k) k * (F.S^[k] N : ℕ)
        - F.fint (F.valVec N k) (F.resVec N k) := by
      linarith [hkey]
    exact (hlogN N (F.S^[k] N) (pre (F.valVec N k) k) _ hN0 hMp hMlo' hqN hfb).2
  rw [hLHS, hRHS, ← Finset.sum_sub_distrib]
  have hgnn : ∀ N ∈ SN, 0 ≤ g N := fun N _ => by rw [hg]; positivity
  calc |∑ N ∈ SN, ((N : ℝ)⁻¹ - g N)| ≤ ∑ N ∈ SN, |(N : ℝ)⁻¹ - g N| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ N ∈ SN, 2 * ε₀ * g N := Finset.sum_le_sum hterm
    _ = 2 * ε₀ * ∑ N ∈ SN, g N := by rw [Finset.mul_sum]
    _ ≤ 2 * ε₀ * (1 + 2 * W) := by
        apply mul_le_mul_of_nonneg_left hRHSle
        rw [hε₀]; exact mul_nonneg (by norm_num) (div_nonneg (Real.rpow_nonneg hLpos.le _) (by norm_num))
    _ ≤ L ^ (-4 : ℝ) := by
        rw [hε₀]
        have hW1 : W ≤ L := by linarith
        have h5 : L ^ (-5 : ℝ) * L = L ^ (-4 : ℝ) := by
          rw [show (-4 : ℝ) = -5 + 1 by norm_num, Real.rpow_add hLpos, Real.rpow_one]
        have h5nn : 0 ≤ L ^ (-5 : ℝ) := Real.rpow_nonneg hLpos.le _
        have : 1 + 2 * W ≤ 3 * L := by linarith
        calc 2 * (L ^ (-5 : ℝ) / 6) * (1 + 2 * W) ≤ 2 * (L ^ (-5 : ℝ) / 6) * (3 * L) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = L ^ (-5 : ℝ) * L := by ring
          _ = L ^ (-4 : ℝ) := h5


/-- **Removing the good-tuple restriction** (`syracZ_eq_rev_fint` and the probability outside `A`). -/
theorem expect_good_cE : ∀ β : ℝ, 1 < β → ∀ᶠ x : ℝ in Filter.atTop, ∀ E : Set ℕ, ∀ k ≤ F.nZero x,
    |expect (PMF.iid (stepLaw F.p) k)
        (fun v => Set.indicator {v : Fin k → ℕ × ℕ | F.goodVec x (fun i => (v i).1)} 1 v *
          F.cE β x E k (F.offsetFwd v))
      - expect (F.syracZ k) (F.cE β x E k)|
      ≤ (1 + 2 * Real.log x ^ (0.7 : ℝ)) * Real.log x ^ (-4 : ℝ) := by
  classical
  intro β hβ
  filter_upwards [F.cE_le β hβ, F.geom_good_tail, eventually_log_ge 0] with x hC hG hL0
  intro E k hk
  set B := 1 + 2 * Real.log x ^ (0.7 : ℝ) with hB
  have hB0 : 0 ≤ B := by have := Real.rpow_nonneg hL0 (0.7 : ℝ); linarith
  set G : Set (Fin k → ℕ × ℕ) := {v | F.goodVec x (fun i => (v i).1)} with hGdef
  set μ := PMF.iid (stepLaw F.p) k with hμ
  have hcb : ∀ Y, |F.cE β x E k Y| ≤ B := fun Y => by
    rw [abs_of_nonneg (F.cE_nonneg β x E k Y)]; exact hC E k hk Y
  -- `𝒮_k` is the pushforward of the forward offset
  have hS : F.syracZ k = μ.map F.offsetFwd := F.syracZ_eq_rev_fint k
  rw [hS, expect_map_of_nonneg μ F.offsetFwd (F.cE β x E k) (F.cE_nonneg β x E k)]
  -- the difference is the contribution from outside `A`
  have hbd1 : ∀ v, |Set.indicator G 1 v * F.cE β x E k (F.offsetFwd v)| ≤ B := fun v => by
    rw [abs_mul]
    calc |Set.indicator G (1 : (Fin k → ℕ × ℕ) → ℝ) v| * |F.cE β x E k (F.offsetFwd v)|
        ≤ 1 * B := mul_le_mul (abs_indicator_le_one G v) (hcb _) (abs_nonneg _) zero_le_one
      _ = B := one_mul B
  have hbd2 : ∀ v, |F.cE β x E k (F.offsetFwd v)| ≤ B := fun v => hcb _
  have hbd3 : ∀ v, |B * Set.indicator Gᶜ (1 : (Fin k → ℕ × ℕ) → ℝ) v| ≤ B := fun v => by
    rw [abs_mul, abs_of_nonneg hB0]
    exact mul_le_of_le_one_right hB0 (abs_indicator_le_one _ v)
  have h1 := abs_expect_sub_le_of_support μ B hbd1 hbd2 hbd3 (fun v _ => by
    by_cases hv : v ∈ G
    · rw [Set.indicator_of_mem hv, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hv)]
      simp
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_mem (Set.mem_compl hv)]
      simp only [zero_mul, zero_sub, abs_neg, Pi.one_apply, mul_one]
      exact hcb _)
  rw [expect_const_mul] at h1
  -- the probability outside `A` is a tail of the geometric distribution
  have hGc : expect μ (Set.indicator Gᶜ 1)
      = expect (PMF.iid (geomP F.p) k) (Set.indicator {a | ¬ F.goodVec x a} 1) := by
    rw [← iid_stepLaw_map_fst, expect_map_indicator]
    rfl
  rw [hGc] at h1
  calc _ ≤ B * expect (PMF.iid (geomP F.p) k) (Set.indicator {a | ¬ F.goodVec x a} 1) := h1
    _ ≤ B * Real.log x ^ (-4 : ℝ) := mul_le_mul_of_nonneg_left (hG k hk) hB0

/-- **Projection to the fine scale** (the last computation of GGM Step 2, `eq:syracmoduloidentity`):
`|E[C^E_k(𝒮_k)] - Ψ(E)| ≤ B · Osc_{m₀,k}(𝒮_k)` (`C^E_k ≤ B`). -/
theorem expect_syracZ_cE (β x : ℝ) (E : Set ℕ) {k : ℕ} (hk : F.mZero β x ≤ k) (B : ℝ)
    (hB : ∀ Y, F.cE β x E k Y ≤ B) :
    |expect (F.syracZ k) (F.cE β x E k) - F.psi β x E|
      ≤ B * F.osc (F.mZero β x) k hk (fun Y => ((F.syracZ k) Y).toReal) := by
  classical
  set m₀ := F.mZero β x with hm₀
  set φ := ZMod.castHom (pow_dvd_pow F.q hk) (ZMod (F.q ^ m₀)) with hφ
  -- the sum over a fibre is the law at the coarse scale
  have hfib : ∀ Y : ZMod (F.q ^ k),
      (∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (F.q ^ k) => φ Y' = φ Y), ((F.syracZ k) Y').toReal)
        = ((F.syracZ m₀) (φ Y)).toReal := by
    intro Y
    rw [← ENNReal.toReal_sum (fun Y' _ => PMF.apply_ne_top _ _)]
    congr 1
    rw [← F.syracZ_map_cast hk, PMF.map_apply, tsum_fintype, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases hc : φ a = φ Y
    · rw [if_pos hc, if_pos hc.symm]
    · rw [if_neg hc, if_neg (fun h => hc h.symm)]
  have hosc : F.osc m₀ k hk (fun Y => ((F.syracZ k) Y).toReal)
      = ∑ Y : ZMod (F.q ^ k), |((F.syracZ k) Y).toReal
          - (F.q : ℝ) ^ ((m₀ : ℤ) - (k : ℤ)) * ((F.syracZ m₀) (φ Y)).toReal| := by
    unfold osc
    refine Finset.sum_congr rfl (fun Y _ => ?_)
    rw [← hfib Y]
  -- rewrite `Ψ` in terms of the fine classes
  have hq0 : (F.q : ℝ) ≠ 0 := F.q_real_pos.ne'
  have hpow : (F.q : ℝ) ^ m₀ = (F.q : ℝ) ^ ((m₀ : ℤ) - (k : ℤ)) * (F.q : ℝ) ^ k := by
    rw [← zpow_natCast (F.q : ℝ) k, ← zpow_add₀ hq0, ← zpow_natCast (F.q : ℝ) m₀]
    congr 1; ring
  have hpsi : F.psi β x E = ∑ Y : ZMod (F.q ^ k),
      (F.q : ℝ) ^ ((m₀ : ℤ) - (k : ℤ)) * ((F.syracZ m₀) (φ Y)).toReal * F.cE β x E k Y := by
    unfold psi cE
    rw [Finset.mul_sum]
    rw [← Finset.sum_fiberwise (F.Eprime β x E) (fun M : ℕ => ((M : ℕ) : ZMod (F.q ^ k)))]
    refine Finset.sum_congr rfl (fun Y _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun M hM => ?_)
    have hMY : ((M : ℕ) : ZMod (F.q ^ k)) = Y := (Finset.mem_filter.mp hM).2
    have hcast : ((M : ℕ) : ZMod (F.q ^ m₀)) = φ Y := by
      rw [← hMY, map_natCast]
    rw [hcast, hpow]
    ring
  have hexp : expect (F.syracZ k) (F.cE β x E k)
      = ∑ Y : ZMod (F.q ^ k), ((F.syracZ k) Y).toReal * F.cE β x E k Y := by
    unfold expect; rw [tsum_fintype]
  rw [hexp, hpsi, hosc, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun Y _ => ?_))
  rw [show ((F.syracZ k) Y).toReal * F.cE β x E k Y
      - (F.q : ℝ) ^ ((m₀ : ℤ) - (k : ℤ)) * ((F.syracZ m₀) (φ Y)).toReal * F.cE β x E k Y
      = (((F.syracZ k) Y).toReal
          - (F.q : ℝ) ^ ((m₀ : ℤ) - (k : ℤ)) * ((F.syracZ m₀) (φ Y)).toReal) * F.cE β x E k Y
      by ring, abs_mul, abs_of_nonneg (F.cE_nonneg β x E k Y), mul_comm B]
  exact mul_le_mul_of_nonneg_left (hB Y) (abs_nonneg _)

/-- **Per-row value** (see the accompanying paper): `|Z · (row n) - Ψ(E)| ≤ K log^{-2} x`. -/
theorem row_eval (h41 : F.prop41_statement) : ∀ α β : ℝ, 1 < α → 1 < β → α ^ 2 * β ≤ F.thetaMax →
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop, ∀ y : ℝ, x ^ β ≤ y → y ≤ x ^ (α * β) →
      ∀ E : Set ℕ, ∀ n ∈ F.Iy x y α,
        |F.windowMass y (y ^ α) * F.rowTerm β x E y α n - F.psi β x E|
          ≤ K * Real.log x ^ (-2 : ℝ) := by
  intro α β hα hβ hθ
  obtain ⟨C₄, hC₄, hosc⟩ := h41 3 (by norm_num)
  have hd := F.drift_pos
  have hβ1 : 0 < β - 1 := by linarith
  set cβ : ℝ := (β - 1) / (8 * F.drift) with hcβ
  have hcβpos : 0 < cβ := by positivity
  refine ⟨5 + 3 * C₄ * cβ ^ (-3 : ℝ), by positivity, ?_⟩
  filter_upwards [F.row_reindex α β hα hβ hθ, F.cE_le β hβ, F.expect_good_cE β hβ,
    F.Iy_bounds α β hα hβ hθ, F.eventually_mZero_ge hβ, eventually_log_ge 1] with
    x hR hC hG hI hm hL
  intro y hy1 hy2 E n hn
  have hLpos : 0 < Real.log x := by linarith
  obtain ⟨h2m, hnn₀⟩ := hI y hy1 hy2 n hn
  set m₀ := F.mZero β x with hm₀
  set k := n - m₀ with hk
  have hkm : m₀ ≤ k := by omega
  have hkn₀ : k ≤ F.nZero x := by omega
  set W := Real.log x ^ (0.7 : ℝ) with hW
  have hW1 : 1 ≤ W := Real.one_le_rpow hL (by norm_num)
  have hBd : ∀ Y, F.cE β x E k Y ≤ 1 + 2 * W := hC E k hkn₀
  have h1 := hR y hy1 hy2 E n hn
  have h2 := hG E k hkn₀
  have h3 := F.expect_syracZ_cE β x E hkm (1 + 2 * W) hBd
  have h4 := hosc k m₀ hkm hm.2
  -- `m₀^{-3} ≤ cβ^{-3} L^{-3}`
  have hm0 : cβ * Real.log x ≤ (m₀ : ℝ) := by
    rw [hcβ]; have := hm.1; rw [div_mul_eq_mul_div]; exact this
  have hmpow : (m₀ : ℝ) ^ (-3 : ℝ) ≤ cβ ^ (-3 : ℝ) * Real.log x ^ (-3 : ℝ) := by
    rw [← Real.mul_rpow hcβpos.le hLpos.le]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hm0 (by norm_num)
  have hosc' : F.osc m₀ k hkm (fun Y => ((F.syracZ k) Y).toReal)
      ≤ C₄ * cβ ^ (-3 : ℝ) * Real.log x ^ (-3 : ℝ) := by
    calc _ ≤ C₄ * (m₀ : ℝ) ^ (-3 : ℝ) := h4
      _ ≤ C₄ * (cβ ^ (-3 : ℝ) * Real.log x ^ (-3 : ℝ)) := mul_le_mul_of_nonneg_left hmpow hC₄.le
      _ = _ := by ring
  -- comparison of powers
  set L := Real.log x with hLdef
  have hWL3 : W * L ^ (-3 : ℝ) ≤ L ^ (-2 : ℝ) := by
    rw [hW, ← Real.rpow_add hLpos]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hWL4 : W * L ^ (-4 : ℝ) ≤ L ^ (-2 : ℝ) := by
    rw [hW, ← Real.rpow_add hLpos]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hL4 : L ^ (-4 : ℝ) ≤ L ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hL4nn : 0 ≤ L ^ (-4 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hL3nn : 0 ≤ L ^ (-3 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hL2nn : 0 ≤ L ^ (-2 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hcpow : 0 ≤ C₄ * cβ ^ (-3 : ℝ) := by positivity
  have hoscnn : 0 ≤ F.osc m₀ k hkm (fun Y => ((F.syracZ k) Y).toReal) := by
    unfold osc; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hmid : (1 + 2 * W) * F.osc m₀ k hkm (fun Y => ((F.syracZ k) Y).toReal)
      ≤ 3 * C₄ * cβ ^ (-3 : ℝ) * L ^ (-2 : ℝ) := by
    calc _ ≤ (3 * W) * (C₄ * cβ ^ (-3 : ℝ) * L ^ (-3 : ℝ)) :=
          mul_le_mul (by linarith) hosc' hoscnn (by positivity)
      _ = 3 * (C₄ * cβ ^ (-3 : ℝ)) * (W * L ^ (-3 : ℝ)) := by ring
      _ ≤ 3 * (C₄ * cβ ^ (-3 : ℝ)) * L ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_left hWL3 (by positivity)
      _ = _ := by ring
  have hmid2 : (1 + 2 * W) * L ^ (-4 : ℝ) ≤ 3 * L ^ (-2 : ℝ) := by
    nlinarith
  calc _ ≤ |F.windowMass y (y ^ α) * F.rowTerm β x E y α n
            - expect (PMF.iid (stepLaw F.p) k)
                (fun v => Set.indicator {v : Fin k → ℕ × ℕ | F.goodVec x (fun i => (v i).1)} 1 v *
                  F.cE β x E k (F.offsetFwd v))|
          + |expect (PMF.iid (stepLaw F.p) k)
                (fun v => Set.indicator {v : Fin k → ℕ × ℕ | F.goodVec x (fun i => (v i).1)} 1 v *
                  F.cE β x E k (F.offsetFwd v)) - expect (F.syracZ k) (F.cE β x E k)|
          + |expect (F.syracZ k) (F.cE β x E k) - F.psi β x E| := by
        have := abs_sub_le (F.windowMass y (y ^ α) * F.rowTerm β x E y α n)
          (expect (PMF.iid (stepLaw F.p) k)
                (fun v => Set.indicator {v : Fin k → ℕ × ℕ | F.goodVec x (fun i => (v i).1)} 1 v *
                  F.cE β x E k (F.offsetFwd v))) (F.psi β x E)
        have := abs_sub_le (expect (PMF.iid (stepLaw F.p) k)
                (fun v => Set.indicator {v : Fin k → ℕ × ℕ | F.goodVec x (fun i => (v i).1)} 1 v *
                  F.cE β x E k (F.offsetFwd v))) (expect (F.syracZ k) (F.cE β x E k)) (F.psi β x E)
        linarith
    _ ≤ L ^ (-4 : ℝ) + (1 + 2 * W) * L ^ (-4 : ℝ)
          + (1 + 2 * W) * F.osc m₀ k hkm (fun Y => ((F.syracZ k) Y).toReal) := by
        gcongr
    _ ≤ L ^ (-2 : ℝ) + 3 * L ^ (-2 : ℝ) + 3 * C₄ * cβ ^ (-3 : ℝ) * L ^ (-2 : ℝ) := by
        linarith
    _ ≤ (5 + 3 * C₄ * cβ ^ (-3 : ℝ)) * L ^ (-2 : ℝ) := by nlinarith

end Family

end GGMCollatz
