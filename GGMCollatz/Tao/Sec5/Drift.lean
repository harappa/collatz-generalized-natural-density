import GGMCollatz.Tao.Sec5.FirstPassage

/-!
# Drift, passage time and the event identity (first half of GGM §4 Step 2; (i)(ii) in the accompanying paper)

Derived from `TaoCollatz/Sec5/ApproxFormula.lean` (`syr_iterate_good_bracket`, `passTime_stepback`,
`stepback_passage_scale`, `eprime_forces_passTime`, `mem_Iy_bounds`) of gotrevor/tao-collatz
(Apache-2.0), commit 15efca2; generalized to the GGM family (p, q, r). Only deterministic statements are
placed here.

* `drift_log`: on good tuples, `log S^k(N) = log N - dk + O(log^{0.6} x)` (GGM `ineq:Sestimate2`).
* `passTime_est`: `1 ≤ T_x(N) ≤ n₀`, `|d T_x(N) - log(N/x)| = O(log^{0.6} x)`.
* `event_identity`: for `n ∈ [2m₀, n₀]`, `S^{n-m₀}(N) ∈ E'(E) ⟺ T_x(N) = n ∧ Pass_x(N) ∈ E` (GGM's
  claim about `B_n`; `E'` with the range condition, (G4) in the accompanying paper).
* `Iy_bounds`, `mem_Iy_of_not_edge`: `I_y ⊂ [2m₀, n₀]`, and `T_x(N) ∈ I_y` off the edge.
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- A prefix of a good tuple is a good tuple (`a^{(k)}(N)` is a prefix of `a^{(n)}(N)`). -/
theorem goodVec_prefix {x : ℝ} {N n k : ℕ} (h : F.goodVec x (F.valVec N n)) (hk : k ≤ n) :
    F.goodVec x (F.valVec N k) := by
  intro j hj
  have := h j (le_trans hj hk)
  rwa [F.pre_valVec (le_trans hj hk), ← F.pre_valVec hj] at this

/-- `m₀ ≥ (β-1) log x/(8d)` and `m₀ ≥ 1` (for `x` large). -/
theorem eventually_mZero_ge {β : ℝ} (hβ : 1 < β) : ∀ᶠ x : ℝ in Filter.atTop,
    (β - 1) * Real.log x / (8 * F.drift) ≤ F.mZero β x ∧ 1 ≤ F.mZero β x := by
  have hd := F.drift_pos
  filter_upwards [eventually_log_ge (16 * F.drift / (β - 1))] with x hL
  have hβ1 : 0 < β - 1 := by linarith
  have hu : 4 ≤ (β - 1) * Real.log x / (4 * F.drift) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hL hβ1.le
    rw [show (β - 1) * (16 * F.drift / (β - 1)) = 16 * F.drift by field_simp] at this
    linarith
  have hfl := Nat.sub_one_lt_floor ((β - 1) * Real.log x / (4 * F.drift))
  unfold mZero
  constructor
  · have : (β - 1) * Real.log x / (8 * F.drift) = ((β - 1) * Real.log x / (4 * F.drift)) / 2 := by
      field_simp; ring
    rw [this]; linarith
  · have : (1 : ℝ) ≤ (⌊(β - 1) * Real.log x / (4 * F.drift)⌋₊ : ℝ) := by linarith
    exact_mod_cast this

/-- **Drift** (GGM `ineq:Sestimate2`): if `x` is large, `p ∤ N`, `N ≥ x` and `a^{(n₀)}(N) ∈ A^{(n₀)}`,
then for `k ≤ n₀`, `|log S^k(N) - (log N - dk)| ≤ log p · log^{0.6} x + 1`. -/
theorem drift_log : ∀ᶠ x : ℝ in Filter.atTop, ∀ N : ℕ, N % F.p ≠ 0 → x ≤ N →
    F.goodVec x (F.valVec N (F.nZero x)) → ∀ k ≤ F.nZero x,
      |Real.log (F.S^[k] N) - (Real.log N - F.drift * k)|
        ≤ Real.log F.p * Real.log x ^ (0.6 : ℝ) + 1 := by
  have hp := F.log_p_pos
  have hq := F.log_q_pos
  have hpq := F.log_p_lt_log_q
  have hμ2 := F.mu_le_two
  have hμ := F.mu_pos
  set R : ℝ := (F.rBound : ℝ) with hR
  have hR0 : 0 ≤ R := Int.cast_nonneg_iff.mpr F.rBound_nonneg
  filter_upwards [eventually_mul_log_rpow_le (show (0.6:ℝ) < 1 by norm_num) (5 * Real.log F.p),
    eventually_log_ge (5 * Real.log (2 * R + 2)), eventually_log_ge 1,
    Filter.eventually_gt_atTop 0] with x h1 h2 hL hx0
  intro N hN hxN hgood k hk
  set L := Real.log x with hLdef
  set t := L ^ (0.6 : ℝ) with htdef
  have hLpos : 0 < L := by linarith
  have ht0 : 0 ≤ t := Real.rpow_nonneg hLpos.le _
  rw [Real.rpow_one] at h1
  have hN0 : 0 < (N : ℝ) := lt_of_lt_of_le hx0 hxN
  -- iteration formula
  have hkey := F.syr_iterate_key hN k
  rw [F.pre_valVec le_rfl] at hkey
  set a := F.valSum N k with ha
  set f : ℤ := F.fint (F.valVec N k) (F.resVec N k) with hf
  have hkeyR : (F.p : ℝ) ^ a * (F.S^[k] N : ℝ) = (F.q : ℝ) ^ k * N + (f : ℝ) := by
    exact_mod_cast hkey
  have hfb := F.abs_fint_le (F.valVec N k) (F.resVec N k) F.rBound_nonneg
    (fun m => F.abs_r_le_rBound (F.digVec_pos_lt hN k m).2)
  rw [F.pre_valVec le_rfl] at hfb
  have hfbR : |(f : ℝ)| ≤ (F.p : ℝ) ^ a * (F.q : ℝ) ^ k * R := by
    rw [hR]; exact_mod_cast hfb
  -- deviation of the sum of valuations
  have hdev : |(a : ℝ) - F.mu * k| < t := by
    have := hgood k hk
    rwa [F.pre_valVec hk] at this
  -- `p^a R ≤ N/2`
  have hn0 : (F.nZero x : ℝ) ≤ L / (5 * Real.log F.q) := by
    unfold nZero; exact Nat.floor_le (by positivity)
  have hkR : (k : ℝ) ≤ F.nZero x := by exact_mod_cast hk
  have hpa : (F.p : ℝ) ^ a ≤ Real.exp (3 * L / 5) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos F.p_real_pos]
    apply Real.exp_le_exp.mpr
    have hak : (a : ℝ) ≤ F.mu * k + t := by linarith [(abs_lt.mp hdev).2]
    have h3 : F.mu * k * Real.log F.p ≤ 2 * L / 5 := by
      have : F.mu * Real.log F.p ≤ 2 * Real.log F.q := by nlinarith
      calc F.mu * k * Real.log F.p = (F.mu * Real.log F.p) * k := by ring
        _ ≤ (2 * Real.log F.q) * (L / (5 * Real.log F.q)) :=
            mul_le_mul this (le_trans hkR hn0) (Nat.cast_nonneg _) (by positivity)
        _ = 2 * L / 5 := by field_simp
    have h4 : t * Real.log F.p ≤ L / 5 := by nlinarith
    calc Real.log F.p * a ≤ Real.log F.p * (F.mu * k + t) := mul_le_mul_of_nonneg_left hak hp.le
      _ = F.mu * k * Real.log F.p + t * Real.log F.p := by ring
      _ ≤ 3 * L / 5 := by linarith
  have hRle : R ≤ Real.exp (L / 5) / 2 := by
    have h5 : Real.log (2 * R + 2) ≤ L / 5 := by linarith
    have h6 : 2 * R + 2 ≤ Real.exp (L / 5) := by
      rw [← Real.exp_log (show 0 < 2 * R + 2 by linarith)]; exact Real.exp_le_exp.mpr h5
    linarith
  have hpaR : (F.p : ℝ) ^ a * R ≤ N / 2 := by
    calc (F.p : ℝ) ^ a * R ≤ Real.exp (3 * L / 5) * (Real.exp (L / 5) / 2) :=
          mul_le_mul hpa hRle hR0 (Real.exp_pos _).le
      _ = Real.exp (4 * L / 5) / 2 := by rw [mul_div_assoc', ← Real.exp_add]; ring_nf
      _ ≤ Real.exp L / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact Real.exp_le_exp.mpr (by linarith)
      _ = x / 2 := by rw [hLdef, Real.exp_log hx0]
      _ ≤ N / 2 := by linarith
  -- `u = f/(q^k N)`, `|u| ≤ 1/2`
  have hqk : 0 < (F.q : ℝ) ^ k := pow_pos F.q_real_pos k
  have hpa0 : 0 < (F.p : ℝ) ^ a := pow_pos F.p_real_pos a
  set u : ℝ := (f : ℝ) / ((F.q : ℝ) ^ k * N) with hu
  have hqN : 0 < (F.q : ℝ) ^ k * N := mul_pos hqk hN0
  have hu2 : |u| ≤ 1 / 2 := by
    rw [hu, abs_div, abs_of_pos hqN, div_le_iff₀ hqN]
    calc |(f : ℝ)| ≤ (F.p : ℝ) ^ a * (F.q : ℝ) ^ k * R := hfbR
      _ = (F.q : ℝ) ^ k * ((F.p : ℝ) ^ a * R) := by ring
      _ ≤ (F.q : ℝ) ^ k * (N / 2) := mul_le_mul_of_nonneg_left hpaR hqk.le
      _ = 1 / 2 * ((F.q : ℝ) ^ k * N) := by ring
  have hu1 : 0 < 1 + u := by linarith [(abs_le.mp hu2).1]
  have hS : (F.S^[k] N : ℝ) = (F.q : ℝ) ^ k * N * (1 + u) / (F.p : ℝ) ^ a := by
    rw [eq_div_iff hpa0.ne', mul_add, mul_one, hu, mul_div_cancel₀ _ hqN.ne', mul_comm]
    exact hkeyR
  have hlogS : Real.log (F.S^[k] N) = k * Real.log F.q + Real.log N + Real.log (1 + u)
      - a * Real.log F.p := by
    rw [hS, Real.log_div (by positivity) hpa0.ne', Real.log_mul (by positivity) hu1.ne',
      Real.log_mul hqk.ne' hN0.ne', Real.log_pow, Real.log_pow]
  have hlog1 : |Real.log (1 + u)| ≤ 1 := by
    rw [abs_le]
    constructor
    · have := Real.one_sub_inv_le_log_of_pos hu1
      have h7 : (1 + u)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hu1 (by norm_num)]; linarith [(abs_le.mp hu2).1]
      linarith
    · have := Real.log_le_sub_one_of_pos hu1
      linarith [(abs_le.mp hu2).2]
  have hexp : Real.log (F.S^[k] N) - (Real.log N - F.drift * k)
      = Real.log (1 + u) - ((a : ℝ) - F.mu * k) * Real.log F.p := by
    rw [hlogS]; unfold drift; ring
  rw [hexp]
  calc |Real.log (1 + u) - ((a : ℝ) - F.mu * k) * Real.log F.p|
      ≤ |Real.log (1 + u)| + |((a : ℝ) - F.mu * k) * Real.log F.p| := abs_sub _ _
    _ ≤ 1 + t * Real.log F.p := by
        rw [abs_mul, abs_of_pos hp]
        exact add_le_add hlog1 (mul_le_mul_of_nonneg_right hdev.le hp.le)
    _ = Real.log F.p * t + 1 := by ring

/-! ### General properties of the passage time (tao-collatz's `passTime_stepback`) -/

theorem passes_of_le {xn N n : ℕ} (h : F.S^[n] N ≤ xn) : F.passes xn N := ⟨n, h⟩

theorem passTime_spec {xn N : ℕ} (h : F.passes xn N) : F.S^[F.passTime xn N] N ≤ xn :=
  Nat.sInf_mem h

theorem lt_of_lt_passTime {xn N k : ℕ} (hk : k < F.passTime xn N) : xn < F.S^[k] N := by
  have := Nat.notMem_of_lt_sInf hk
  simp only [Set.mem_setOf_eq, not_le] at this
  exact this

theorem passTime_le_of {xn N n : ℕ} (h : F.S^[n] N ≤ xn) : F.passTime xn N ≤ n := Nat.sInf_le h

theorem passTime_eq_of {xn N n : ℕ} (h : F.S^[n] N ≤ xn) (h' : ∀ j < n, xn < F.S^[j] N) :
    F.passTime xn N = n := by
  apply le_antisymm (F.passTime_le_of h)
  by_contra hlt
  push_neg at hlt
  have h1 := h' _ hlt
  have h2 := F.passTime_spec (F.passes_of_le h)
  omega

theorem passes_of_passTime_pos {xn N : ℕ} (h : 0 < F.passTime xn N) : F.passes xn N := by
  by_contra hp
  have hempty : {n | F.S^[n] N ≤ xn} = ∅ := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hn => hp ⟨n, hn⟩
  unfold passTime at h
  rw [hempty, Nat.sInf_empty] at h
  omega

theorem passLoc_of_passes {xn N : ℕ} (h : F.passes xn N) :
    F.passLoc xn N = F.S^[F.passTime xn N] N := by
  unfold passLoc; rw [if_pos h]

/-- **Step back** (tao-collatz's `passTime_stepback`). -/
theorem passTime_stepback {xn N k : ℕ} (hpass : F.passes xn N) (hk : k ≤ F.passTime xn N) :
    F.passes xn (F.S^[k] N) ∧ F.passTime xn (F.S^[k] N) = F.passTime xn N - k ∧
      F.passLoc xn (F.S^[k] N) = F.passLoc xn N := by
  set T := F.passTime xn N with hT
  have hTmem : F.S^[T] N ≤ xn := F.passTime_spec hpass
  have hshift : ∀ i, F.S^[i] (F.S^[k] N) = F.S^[k + i] N := by
    intro i; rw [← Function.iterate_add_apply]; congr 1; omega
  have hpassM : F.passes xn (F.S^[k] N) := by
    refine ⟨T - k, ?_⟩
    rw [hshift, show k + (T - k) = T from by omega]; exact hTmem
  have hTM : F.passTime xn (F.S^[k] N) = T - k := by
    apply F.passTime_eq_of
    · rw [hshift, show k + (T - k) = T from by omega]; exact hTmem
    · intro j hj
      rw [hshift]
      exact F.lt_of_lt_passTime (by omega)
  refine ⟨hpassM, hTM, ?_⟩
  rw [F.passLoc_of_passes hpassM, F.passLoc_of_passes hpass, hTM, hshift,
    show k + (T - k) = T from by omega]

/-- **Passage time** (GGM `T_x(L) = log(L/x)/log(p^μ/q) + O(log^{0.6} x)`). -/
theorem passTime_est : ∀ᶠ x : ℝ in Filter.atTop, ∀ N : ℕ, N % F.p ≠ 0 → x < N →
    (N : ℝ) ≤ x ^ F.thetaMax → F.goodVec x (F.valVec N (F.nZero x)) →
      F.passes ⌊x⌋₊ N ∧ 1 ≤ F.passTime ⌊x⌋₊ N ∧ F.passTime ⌊x⌋₊ N ≤ F.nZero x ∧
        |F.drift * F.passTime ⌊x⌋₊ N - Real.log (N / x)|
          ≤ 2 * Real.log F.p * Real.log x ^ (0.6 : ℝ) + F.drift + 2 := by
  have hp := F.log_p_pos
  have hq := F.log_q_pos
  have hd := F.drift_pos
  filter_upwards [F.drift_log,
    eventually_add_mul_rpow_le (show (0.6:ℝ) < 1 by norm_num) one_pos (F.drift + 1) (Real.log F.p)
      (show 0 < 3 * F.drift / (20 * Real.log F.q) by positivity),
    eventually_log_ge 1, Filter.eventually_gt_atTop 0] with x hdr h1 hL hx0
  intro N hN hxN hNθ hgood
  set L := Real.log x with hLdef
  set t := L ^ (0.6 : ℝ) with htdef
  set n₀ := F.nZero x with hn₀
  rw [Real.rpow_one] at h1
  have hLpos : 0 < L := by linarith
  have ht0 : 0 ≤ t := Real.rpow_nonneg hLpos.le _
  have hN0 : 0 < (N : ℝ) := by linarith
  have hlogN : Real.log N ≤ F.thetaMax * L := by
    rw [hLdef, ← Real.log_rpow hx0]; exact Real.log_le_log hN0 hNθ
  have hlogxN : L < Real.log N := Real.log_lt_log hx0 hxN
  have hSpos : ∀ k, 0 < (F.S^[k] N : ℝ) := fun k => by exact_mod_cast F.syr_iterate_pos hN k
  have hx0' : (0 : ℝ) ≤ x := hx0.le
  -- `S^{n₀}(N) ≤ x`
  have hdn := hdr N hN hxN.le hgood n₀ le_rfl
  have hn0ge : L / (5 * Real.log F.q) - 1 ≤ n₀ := F.nZero_ge x
  have hSn0 : Real.log (F.S^[n₀] N) ≤ L := by
    have h2 := (abs_le.mp hdn).2
    have h3 : F.drift * (L / (5 * Real.log F.q) - 1) ≤ F.drift * n₀ :=
      mul_le_mul_of_nonneg_left hn0ge hd.le
    have e1 : F.drift * (L / (5 * Real.log F.q)) = 4 * (F.drift * L / (20 * Real.log F.q)) := by
      field_simp; ring
    have e2 : 3 * F.drift / (20 * Real.log F.q) * L = 3 * (F.drift * L / (20 * Real.log F.q)) := by
      field_simp
    have e3 : F.thetaMax * L = L + F.drift * L / (20 * Real.log F.q) := by
      unfold thetaMax; field_simp
    have h1' : F.drift + 1 + Real.log F.p * t ≤ 3 * (F.drift * L / (20 * Real.log F.q)) := by
      rw [← e2]; exact h1
    nlinarith
  have hSn0x : F.S^[n₀] N ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    have := Real.exp_le_exp.mpr hSn0
    rwa [Real.exp_log (hSpos n₀), hLdef, Real.exp_log hx0] at this
  have hpass : F.passes ⌊x⌋₊ N := F.passes_of_le hSn0x
  set T := F.passTime ⌊x⌋₊ N with hT
  have hTle : T ≤ n₀ := F.passTime_le_of hSn0x
  have hT1 : 1 ≤ T := by
    by_contra h0
    have hT0 : T = 0 := by omega
    have := F.passTime_spec hpass
    rw [← hT, hT0, Function.iterate_zero, id] at this
    have : (N : ℝ) ≤ x := le_trans (by exact_mod_cast this) (Nat.floor_le hx0')
    linarith
  refine ⟨hpass, hT1, hTle, ?_⟩
  -- `S^T ≤ x < S^{T-1}`
  have hST : (F.S^[T] N : ℝ) ≤ x :=
    le_trans (by exact_mod_cast F.passTime_spec hpass) (Nat.floor_le hx0')
  have hST1 : x < (F.S^[T - 1] N : ℝ) := by
    have := F.lt_of_lt_passTime (xn := ⌊x⌋₊) (N := N) (k := T - 1) (by omega)
    have h' : ⌊x⌋₊ + 1 ≤ F.S^[T - 1] N := this
    have := Nat.lt_floor_add_one x
    have h'' : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ (F.S^[T - 1] N : ℝ) := by exact_mod_cast h'
    push_cast at h''
    linarith
  have hlT : Real.log (F.S^[T] N) ≤ L := by
    rw [hLdef]; exact Real.log_le_log (hSpos T) hST
  have hlT1 : L < Real.log (F.S^[T - 1] N) := Real.log_lt_log hx0 hST1
  have hdT := abs_le.mp (hdr N hN hxN.le hgood T hTle)
  have hdT1 := abs_le.mp (hdr N hN hxN.le hgood (T - 1) (by omega))
  have hcast : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
    rw [Nat.cast_sub hT1]; simp
  rw [hcast] at hdT1
  rw [Real.log_div hN0.ne' hx0.ne', abs_le]
  constructor <;> nlinarith [hdT.1, hdT.2, hdT1.1, hdT1.2]

/-- **Event identity** (GGM's claim about `B_n`; (ii) in the accompanying paper). -/
theorem event_identity : ∀ β : ℝ, 1 < β → ∀ᶠ x : ℝ in Filter.atTop, ∀ N : ℕ, N % F.p ≠ 0 → x < N →
    (N : ℝ) ≤ x ^ F.thetaMax → F.goodVec x (F.valVec N (F.nZero x)) →
    ∀ n : ℕ, 2 * F.mZero β x ≤ n → n ≤ F.nZero x → ∀ E : Set ℕ,
      (F.S^[n - F.mZero β x] N ∈ F.Eprime β x E ↔
        (F.passTime ⌊x⌋₊ N = n ∧ F.passLoc ⌊x⌋₊ N ∈ E)) := by
  intro β hβ
  have hp := F.log_p_pos
  have hd := F.drift_pos
  have hβ1 : 0 < β - 1 := by linarith
  filter_upwards [F.drift_log, F.eventually_mZero_ge hβ,
    eventually_add_mul_rpow_le (show (0.6:ℝ) < 0.7 by norm_num) (by norm_num) (F.drift + 2)
      (2 * Real.log F.p) one_pos,
    eventually_add_mul_rpow_le (show (0.7:ℝ) < 1 by norm_num) one_pos 0 2
      (show 0 < (β - 1) / 16 by positivity),
    eventually_log_ge 1, Filter.eventually_gt_atTop 0] with x hdr hm hE1 hE2 hL hx0
  intro N hN hxN hNθ hgood n h2m hnn₀ E
  rw [one_mul] at hE1
  rw [Real.rpow_one, zero_add] at hE2
  set L := Real.log x with hLdef
  set t := L ^ (0.6 : ℝ) with htdef
  set W := L ^ (0.7 : ℝ) with hWdef
  set m₀ := F.mZero β x with hm₀def
  set n' := n - m₀ with hn'def
  have hLpos : 0 < L := by linarith
  have ht0 : 0 ≤ t := Real.rpow_nonneg hLpos.le _
  have hm1 : 1 ≤ m₀ := hm.2
  have hdm : W + 2 * Real.log F.p * t + 2 < F.drift * m₀ := by
    have h' : (β - 1) * L / 8 ≤ F.drift * m₀ := by
      have := mul_le_mul_of_nonneg_left hm.1 hd.le
      rwa [show F.drift * ((β - 1) * L / (8 * F.drift)) = (β - 1) * L / 8 by field_simp] at this
    have h'' : 0 < (β - 1) * L := by positivity
    nlinarith
  have hSpos : ∀ k, 0 < (F.S^[k] N : ℝ) := fun k => by exact_mod_cast F.syr_iterate_pos hN k
  have hiter : F.S^[n] N = F.S^[m₀] (F.S^[n'] N) := by
    rw [← Function.iterate_add_apply, show m₀ + n' = n by omega]
  have hdr' : ∀ k ≤ F.nZero x, Real.log (F.S^[k] N) - (Real.log N - F.drift * k)
      ≤ Real.log F.p * t + 1 ∧
        -(Real.log F.p * t + 1) ≤ Real.log (F.S^[k] N) - (Real.log N - F.drift * k) :=
    fun k hk => ⟨(abs_le.mp (hdr N hN hxN.le hgood k hk)).2,
      (abs_le.mp (hdr N hN hxN.le hgood k hk)).1⟩
  have hn'R : (n' : ℝ) = n - m₀ := by rw [hn'def, Nat.cast_sub (by omega)]
  constructor
  · intro hM
    unfold Eprime at hM
    simp only [Finset.mem_filter, Finset.mem_range] at hM
    obtain ⟨_, _, hMlo, hMpass, hMT, hMloc⟩ := hM
    rw [← hm₀def] at hMT
    set M := F.S^[n'] N with hMdef
    have hMspec := F.passTime_spec hMpass
    rw [hMT] at hMspec
    have hSn : F.S^[n] N ≤ ⌊x⌋₊ := by rw [hiter]; exact hMspec
    have hlogM : F.drift * m₀ + L - W ≤ Real.log M := by
      have := Real.log_le_log (Real.exp_pos _) hMlo
      unfold Mlo at this; rwa [Real.log_exp] at this
    have hlt : ∀ j < n, ⌊x⌋₊ < F.S^[j] N := by
      intro j hj
      by_cases hjn : n' ≤ j
      · have : F.S^[j] N = F.S^[j - n'] M := by
          rw [hMdef, ← Function.iterate_add_apply, show j - n' + n' = j by omega]
        rw [this]; apply F.lt_of_lt_passTime; rw [hMT]; omega
      · push_neg at hjn
        have h1 := hdr' j (by omega)
        have h2 := hdr' n' (by omega)
        have hjn' : (j : ℝ) ≤ n' := by exact_mod_cast hjn.le
        have hlog : L < Real.log (F.S^[j] N) := by nlinarith
        have hx' : x < (F.S^[j] N : ℝ) := by
          have := Real.exp_lt_exp.mpr hlog
          rwa [Real.exp_log (hSpos j), hLdef, Real.exp_log hx0] at this
        have hfl := Nat.floor_le hx0.le
        exact_mod_cast (lt_of_le_of_lt hfl hx')
    have hTN : F.passTime ⌊x⌋₊ N = n := F.passTime_eq_of hSn hlt
    refine ⟨hTN, ?_⟩
    have hpassN := F.passes_of_le hSn
    rw [F.passLoc_of_passes hpassN, hTN, hiter, ← hMT, ← F.passLoc_of_passes hMpass]
    exact hMloc
  · rintro ⟨hTN, hloc⟩
    have hpassN : F.passes ⌊x⌋₊ N := F.passes_of_passTime_pos (by omega)
    obtain ⟨hpM, hTM, hlocM⟩ :=
      F.passTime_stepback hpassN (show n' ≤ F.passTime ⌊x⌋₊ N by omega)
    set M := F.S^[n'] N with hMdef
    have hTM' : F.passTime ⌊x⌋₊ M = m₀ := by rw [hTM, hTN]; omega
    have hSn : (F.S^[n] N : ℝ) ≤ x := by
      have := F.passTime_spec hpassN
      rw [hTN] at this
      exact le_trans (by exact_mod_cast this) (Nat.floor_le hx0.le)
    have hSn1 : x < (F.S^[n - 1] N : ℝ) := by
      have h' := F.lt_of_lt_passTime (xn := ⌊x⌋₊) (N := N) (k := n - 1) (by omega)
      have h'' : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ (F.S^[n - 1] N : ℝ) := by exact_mod_cast h'
      have := Nat.lt_floor_add_one x
      push_cast at h''
      linarith
    have hlSn : Real.log (F.S^[n] N) ≤ L := Real.log_le_log (hSpos n) hSn
    have hlSn1 : L < Real.log (F.S^[n - 1] N) := Real.log_lt_log hx0 hSn1
    have h1 := hdr' n hnn₀
    have h2 := hdr' n' (by omega)
    have h3 := hdr' (n - 1) (by omega)
    have hn1R : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [hn1R] at h3
    rw [hn'R] at h2
    have hMpos : 0 < (M : ℝ) := hSpos n'
    have hup : Real.log M ≤ F.drift * m₀ + L + W := by nlinarith
    have hlo : F.drift * m₀ + L - W ≤ Real.log M := by nlinarith
    have hMhi : (M : ℝ) ≤ F.Mhi β x := by
      unfold Mhi
      rw [← Real.exp_log hMpos]
      exact Real.exp_le_exp.mpr (by linarith)
    have hMlo : F.Mlo β x ≤ (M : ℝ) := by
      unfold Mlo
      rw [← Real.exp_log hMpos]
      exact Real.exp_le_exp.mpr (by linarith)
    unfold Eprime
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_succ_of_le (Nat.le_floor hMhi), F.syr_iterate_mod_ne_zero hN n', hMlo, hpM,
      hTM', ?_⟩
    rw [hlocM]; exact hloc

/-- `I_y ⊂ [2m₀, n₀]` (GGM "note `I_y ⊂ [2m₀, n₀]`"). -/
theorem Iy_bounds : ∀ α β : ℝ, 1 < α → 1 < β → α ^ 2 * β ≤ F.thetaMax → ∀ᶠ x : ℝ in Filter.atTop,
    ∀ y : ℝ, x ^ β ≤ y → y ≤ x ^ (α * β) → ∀ n ∈ F.Iy x y α,
      2 * F.mZero β x ≤ n ∧ n ≤ F.nZero x := by
  intro α β hα hβ hθ
  have hd := F.drift_pos
  filter_upwards [eventually_log_ge 0, Filter.eventually_gt_atTop 0] with x hL hx0
  intro y hy1 hy2 n hn
  unfold Iy at hn
  rw [Finset.mem_filter, Finset.mem_range] at hn
  refine ⟨?_, by omega⟩
  have hy0 : 0 < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 β) hy1
  have hlogy : β * Real.log x ≤ Real.log y := by
    rw [← Real.log_rpow hx0]; exact Real.log_le_log (Real.rpow_pos_of_pos hx0 β) hy1
  have hV : 0 ≤ Real.log x ^ (0.8 : ℝ) := Real.rpow_nonneg hL _
  have h1 := hn.2.1
  rw [Real.log_div hy0.ne' hx0.ne'] at h1
  have hβ1 : 0 ≤ β - 1 := by linarith
  have hm : (F.mZero β x : ℝ) ≤ (β - 1) * Real.log x / (4 * F.drift) := by
    unfold mZero; exact Nat.floor_le (by positivity)
  have h2 : (β - 1) * Real.log x / F.drift ≤ (Real.log y - Real.log x) / F.drift := by
    apply div_le_div_of_nonneg_right _ hd.le; linarith
  have h3 : 2 * ((β - 1) * Real.log x / (4 * F.drift)) ≤ (β - 1) * Real.log x / F.drift := by
    rw [show 2 * ((β - 1) * Real.log x / (4 * F.drift)) = ((β - 1) * Real.log x / F.drift) / 2 by
      field_simp; ring]
    have : 0 ≤ (β - 1) * Real.log x / F.drift := by
      have : 0 ≤ β - 1 := by linarith
      positivity
    linarith
  have : (2 * F.mZero β x : ℝ) ≤ n := by
    linarith
  exact_mod_cast this

/-- For a good tuple off the edge of the window, `T_x(N) ∈ I_y` (the logarithmic side of (iv) in the
accompanying paper). -/
theorem mem_Iy_of_not_edge : ∀ α β : ℝ, 1 < α → 1 < β → α ^ 2 * β ≤ F.thetaMax →
    ∀ᶠ x : ℝ in Filter.atTop, ∀ y : ℝ, x ^ β ≤ y → y ≤ x ^ (α * β) → ∀ N ∈ F.logWindow y (y ^ α),
      F.goodVec x (F.valVec N (F.nZero x)) → ¬ F.edge x y α N →
        F.passTime ⌊x⌋₊ N ∈ F.Iy x y α := by
  intro α β hα hβ hθ
  have hp := F.log_p_pos
  have hd := F.drift_pos
  filter_upwards [F.passTime_est,
    eventually_add_mul_rpow_le (show (0.6:ℝ) < 0.8 by norm_num) (by norm_num) (F.drift + 2)
      (2 * Real.log F.p) hd,
    Filter.eventually_gt_atTop 1] with x hPT hK hx1
  intro y hy1 hy2 N hNW hgood hed
  obtain ⟨hNp, hyN, hNy⟩ := (F.mem_logWindow_iff).mp hNW
  have hx0 : 0 < x := by linarith
  have hxβ : x < x ^ β := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ < x ^ β := Real.rpow_lt_rpow_of_exponent_lt hx1 hβ
  have hxy : x < y := lt_of_lt_of_le hxβ hy1
  have hy0 : 0 < y := by linarith
  have hxN : x < N := lt_of_lt_of_le hxy hyN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNθ : (N : ℝ) ≤ x ^ F.thetaMax := by
    calc (N : ℝ) ≤ y ^ α := hNy
      _ ≤ (x ^ (α * β)) ^ α := Real.rpow_le_rpow hy0.le hy2 (by linarith)
      _ = x ^ (α ^ 2 * β) := by rw [← Real.rpow_mul hx0.le]; ring_nf
      _ ≤ x ^ F.thetaMax := Real.rpow_le_rpow_of_exponent_le hx1.le hθ
  obtain ⟨_, _, hTle, hTest⟩ := hPT N hNp hxN hNθ hgood
  set T := F.passTime ⌊x⌋₊ N with hT
  set V := Real.log x ^ (0.8 : ℝ) with hV
  unfold edge at hed
  push_neg at hed
  obtain ⟨he1, he2⟩ := hed
  rw [Real.log_div hN0.ne' hx0.ne'] at hTest
  have hT' := abs_le.mp hTest
  unfold Iy
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨by omega, ?_, ?_⟩
  · have e : Real.log (y / x) / F.drift + V = (Real.log (y / x) + F.drift * V) / F.drift := by
      field_simp
    rw [e, div_le_iff₀ hd, Real.log_div hy0.ne' hx0.ne']
    nlinarith
  · have e : Real.log (y ^ α / x) / F.drift - V = (Real.log (y ^ α / x) - F.drift * V) / F.drift := by
      field_simp
    rw [e, le_div_iff₀ hd, Real.log_div (by positivity) hx0.ne', Real.log_rpow hy0]
    nlinarith

end Family

end GGMCollatz
