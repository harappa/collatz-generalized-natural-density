import GGMCollatz.NatDen.UProf.Master.Prob

/-!
# Ingredients of (UM): counting over `E'` (the flattening (F), the part (P), and the upper bound for the kernel)

* `ep1_avg`: from (EP1) `C_j(X) ≤ K`, `Σ_{M ∈ E'} (q^j/M) g(M mod q^j) ≤ K Σ_X g(X)` (`g ≥ 0`).
* `ep2_fiber`: by the flatness (EP2), `Σ_{M ∈ E', s ∈ Σ(n,M)} p^s e(M mod q^k) ≤ (p^s q^{-k} ν̄ + p^s x^{1/2} 1[ν̄ ≥ 1]) Σ_X e(X)`.
* `geom_sum_le`: if `r > 1` and `r^s ≤ T` (`s ∈ S`) then `Σ_{s∈S} r^s ≤ r/(r-1) T`.
* `kernC_le`: the kernel restricted to central `s`, `Σ_n Σ_{s ∈ Σ(n,M), |s - μk| ≤ R} p^s q^{-k} ≤ (p/(p-1))(Y/M) N_R`,
  `N_R = 2R log p/d + 1 + e^d/(e^d - 1)` (a geometric series in `s`, and a count of the central window in `k`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace MasterAux

variable (F : Family)

/-- **The averaged form of (EP1)**. -/
theorem ep1_avg {α x K : ℝ} {j : ℕ} (hK : ∀ X : ZMod (F.q ^ j), F.cE α x Set.univ j X ≤ K)
    (g : ZMod (F.q ^ j) → ℝ) (hg : ∀ X, 0 ≤ g X) :
    ∑ M ∈ F.Eprime α x Set.univ, (F.q : ℝ) ^ j / (M : ℝ) * g (M : ZMod (F.q ^ j))
      ≤ K * ∑ X, g X := by
  classical
  rw [← Finset.sum_fiberwise (F.Eprime α x Set.univ) (fun M : ℕ => (M : ZMod (F.q ^ j))),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun X _ => ?_
  have h : ∑ M ∈ (F.Eprime α x Set.univ).filter (fun M : ℕ => (M : ZMod (F.q ^ j)) = X),
      (F.q : ℝ) ^ j / (M : ℝ) * g (M : ZMod (F.q ^ j)) = g X * F.cE α x Set.univ j X := by
    unfold Family.cE
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun M hM => ?_
    rw [(Finset.mem_filter.mp hM).2]
    ring
  rw [h, mul_comm K]
  exact mul_le_mul_of_nonneg_left (hK X) (hg X)

/-- `inWin` written as an interval in `M`. -/
theorem inWin_iff {y Y : ℝ} {k s : ℕ} {M : ℝ} :
    inWin F y Y k s M ↔
      y * (F.q : ℝ) ^ k / (F.p : ℝ) ^ s < M ∧ M ≤ Y * (F.q : ℝ) ^ k / (F.p : ℝ) ^ s := by
  have hp : 0 < (F.p : ℝ) ^ s := pow_pos F.p_real_pos s
  have hq : 0 < (F.q : ℝ) ^ k := pow_pos F.q_real_pos k
  unfold inWin
  rw [lt_div_iff₀ hq, div_le_iff₀ hq, div_lt_iff₀ hp, le_div_iff₀ hp]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- `p^s ≤ Y q^k / M` from the upper end of the window. -/
theorem pow_le_of_inWin {y Y : ℝ} {k s : ℕ} {M : ℝ} (h : inWin F y Y k s M) (hM : 0 < M) :
    (F.p : ℝ) ^ s ≤ Y * (F.q : ℝ) ^ k / M := by
  have hq : 0 < (F.q : ℝ) ^ k := pow_pos F.q_real_pos k
  have h2 := h.2
  rw [div_le_iff₀ hq] at h2
  rw [le_div_iff₀ hM]
  linarith

/-- `p^s/q^k ≤ Y / M` from the upper end of the window. -/
theorem pow_div_le_of_inWin {y Y : ℝ} {k s : ℕ} {M : ℝ} (h : inWin F y Y k s M) (hM : 0 < M) :
    (F.p : ℝ) ^ s / (F.q : ℝ) ^ k ≤ Y / M := by
  have hq : 0 < (F.q : ℝ) ^ k := pow_pos F.q_real_pos k
  have h2 := h.2
  rw [div_le_iff₀ hq] at h2
  rw [div_le_div_iff₀ hq hM]
  linarith

open Classical in
/-- **Flattening the residue-class weights by (EP2)** (the (F) of the accompanying paper). -/
theorem ep2_fiber {α x y Y : ℝ} {k s : ℕ}
    (hflat : ∀ X : ZMod (F.q ^ k), ∀ A B : ℝ,
      |(((F.Eprime α x Set.univ).filter (fun M : ℕ =>
            A < (M : ℝ) ∧ (M : ℝ) ≤ B ∧ ((M : ℕ) : ZMod (F.q ^ k)) = X)).card : ℝ)
        - (F.q : ℝ) ^ (-(k : ℤ)) *
          (((F.Eprime α x Set.univ).filter (fun M : ℕ => A < (M : ℝ) ∧ (M : ℝ) ≤ B)).card : ℝ)|
        ≤ x ^ (1 / 2 : ℝ))
    (e : ZMod (F.q ^ k) → ℝ) (he : ∀ X, 0 ≤ e X) :
    ∑ M ∈ F.Eprime α x Set.univ,
        (if inWin F y Y k s M then (F.p : ℝ) ^ s * e (M : ZMod (F.q ^ k)) else 0)
      ≤ ((F.p : ℝ) ^ s / (F.q : ℝ) ^ k *
            (((F.Eprime α x Set.univ).filter (fun M : ℕ => inWin F y Y k s M)).card : ℝ)
          + (if 0 < ((F.Eprime α x Set.univ).filter (fun M : ℕ => inWin F y Y k s M)).card
              then (F.p : ℝ) ^ s * x ^ (1 / 2 : ℝ) else 0)) * ∑ X, e X := by
  set W := (F.Eprime α x Set.univ).filter (fun M : ℕ => inWin F y Y k s M) with hW
  set A := y * (F.q : ℝ) ^ k / (F.p : ℝ) ^ s with hA
  set B := Y * (F.q : ℝ) ^ k / (F.p : ℝ) ^ s with hB
  have hWeq : W = (F.Eprime α x Set.univ).filter (fun M : ℕ => A < (M : ℝ) ∧ (M : ℝ) ≤ B) :=
    Finset.filter_congr (fun M _ => inWin_iff F)
  have hps : 0 ≤ (F.p : ℝ) ^ s := (pow_pos F.p_real_pos s).le
  rw [← Finset.sum_filter, ← hW]
  rcases Nat.eq_zero_or_pos W.card with hW0 | hpos
  · rw [Finset.card_eq_zero.mp hW0]
    simp
  rw [if_pos hpos, ← Finset.sum_fiberwise W (fun M : ℕ => (M : ZMod (F.q ^ k))), Finset.mul_sum]
  refine Finset.sum_le_sum fun X _ => ?_
  have h1 : ∑ M ∈ W.filter (fun M : ℕ => (M : ZMod (F.q ^ k)) = X),
      (F.p : ℝ) ^ s * e (M : ZMod (F.q ^ k))
        = ((W.filter (fun M : ℕ => (M : ZMod (F.q ^ k)) = X)).card : ℝ) * ((F.p : ℝ) ^ s * e X) := by
    rw [Finset.sum_congr rfl (fun M hM => by rw [(Finset.mem_filter.mp hM).2]), Finset.sum_const,
      nsmul_eq_mul]
  rw [h1]
  have h2 : ((W.filter (fun M : ℕ => (M : ZMod (F.q ^ k)) = X)).card : ℝ)
      ≤ (F.q : ℝ) ^ (-(k : ℤ)) * (W.card : ℝ) + x ^ (1 / 2 : ℝ) := by
    have hf := hflat X A B
    have e1 : W.filter (fun M : ℕ => (M : ZMod (F.q ^ k)) = X)
        = (F.Eprime α x Set.univ).filter (fun M : ℕ =>
            A < (M : ℝ) ∧ (M : ℝ) ≤ B ∧ ((M : ℕ) : ZMod (F.q ^ k)) = X) := by
      rw [hWeq, Finset.filter_filter]
      exact Finset.filter_congr (fun M _ => and_assoc)
    rw [e1]
    rw [← hWeq] at hf
    linarith [(abs_le.mp hf).2]
  have hzp : (F.q : ℝ) ^ (-(k : ℤ)) = 1 / (F.q : ℝ) ^ k := by
    rw [zpow_neg, zpow_natCast, one_div]
  calc ((W.filter (fun M : ℕ => (M : ZMod (F.q ^ k)) = X)).card : ℝ) * ((F.p : ℝ) ^ s * e X)
      ≤ ((F.q : ℝ) ^ (-(k : ℤ)) * (W.card : ℝ) + x ^ (1 / 2 : ℝ)) * ((F.p : ℝ) ^ s * e X) :=
        mul_le_mul_of_nonneg_right h2 (mul_nonneg hps (he X))
    _ = ((F.p : ℝ) ^ s / (F.q : ℝ) ^ k * (W.card : ℝ) + (F.p : ℝ) ^ s * x ^ (1 / 2 : ℝ)) * e X := by
        rw [hzp]; ring

/-- **Geometric series**: if `r > 1`, `0 ≤ T` and `r^s ≤ T` for all `s` in `S`, then `Σ_{s ∈ S} r^s ≤ r/(r-1) T`. -/
theorem geom_sum_le {r T : ℝ} (hr : 1 < r) (hT : 0 ≤ T) (S : Finset ℕ) (h : ∀ s ∈ S, r ^ s ≤ T) :
    ∑ s ∈ S, r ^ s ≤ r / (r - 1) * T := by
  have hr0 : 0 < r - 1 := by linarith
  rcases S.eq_empty_or_nonempty with rfl | hS
  · rw [Finset.sum_empty]
    exact mul_nonneg (div_nonneg (by linarith) hr0.le) hT
  set m := S.max' hS
  have hsub : S ⊆ Finset.range (m + 1) := fun s hs =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (S.le_max' s hs))
  calc ∑ s ∈ S, r ^ s ≤ ∑ s ∈ Finset.range (m + 1), r ^ s :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s _ _ => pow_nonneg (by linarith) _)
    _ = (r ^ (m + 1) - 1) / (r - 1) := geom_sum_eq (by linarith) _
    _ ≤ r ^ (m + 1) / (r - 1) := by
        apply div_le_div_of_nonneg_right _ hr0.le; linarith
    _ = r / (r - 1) * r ^ m := by rw [pow_succ]; ring
    _ ≤ r / (r - 1) * T :=
        mul_le_mul_of_nonneg_left (h m (S.max'_mem hS)) (div_nonneg (by linarith) hr0.le)

/-- The constant `N_R = 2R log p/d + 1 + e^d/(e^d - 1)` of the count of the central window. -/
noncomputable def NR (R : ℝ) : ℝ :=
  2 * R * Real.log F.p / F.drift + 1 + Real.exp F.drift / (Real.exp F.drift - 1)

/-- `p^s/q^k = exp((s - μk) log p + dk)`. -/
theorem pow_div_pow_eq_exp (k s : ℕ) :
    (F.p : ℝ) ^ s / (F.q : ℝ) ^ k
      = Real.exp (((s : ℝ) - F.mu * k) * Real.log F.p + F.drift * k) := by
  have h : ((s : ℝ) - F.mu * k) * Real.log F.p + F.drift * k
      = (s : ℝ) * Real.log F.p - (k : ℝ) * Real.log F.q := by
    unfold Family.drift; ring
  rw [h, Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log F.p_real_pos,
    Real.exp_log F.q_real_pos]

open Classical in
/-- **The inner sum of each row**: the geometric series in `s` restricted to the centre. Empty if `d k > log(Y/M) + R log p`. -/
theorem inner_le {y Y R M : ℝ} (hY : 0 < Y) (hM : 0 < M) (k : ℕ) (S : Finset ℕ) :
    ∑ s ∈ S, (if inWin F y Y k s M ∧ |(s : ℝ) - F.mu * k| ≤ R
        then (F.p : ℝ) ^ s / (F.q : ℝ) ^ k else 0)
      ≤ (F.p : ℝ) / ((F.p : ℝ) - 1) *
        (if F.drift * k ≤ Real.log (Y / M) + R * Real.log F.p
          then min (Real.exp (Real.log (Y / M))) (Real.exp (R * Real.log F.p + F.drift * k))
          else 0) := by
  have hYM : 0 < Y / M := div_pos hY hM
  have hlp := F.log_p_pos
  have hq : 0 < (F.q : ℝ) ^ k := pow_pos F.q_real_pos k
  have hp1 : 1 < (F.p : ℝ) := F.one_lt_p_real
  rw [← Finset.sum_filter]
  set S' := S.filter (fun s => inWin F y Y k s M ∧ |(s : ℝ) - F.mu * k| ≤ R) with hS'
  have hterm : ∀ s ∈ S', (F.p : ℝ) ^ s / (F.q : ℝ) ^ k ≤ Real.exp (Real.log (Y / M)) ∧
      (F.p : ℝ) ^ s / (F.q : ℝ) ^ k ≤ Real.exp (R * Real.log F.p + F.drift * k) ∧
      Real.exp (-(R * Real.log F.p) + F.drift * k) ≤ (F.p : ℝ) ^ s / (F.q : ℝ) ^ k := by
    intro s hs
    obtain ⟨hw, hc⟩ := (Finset.mem_filter.mp hs).2
    refine ⟨?_, ?_, ?_⟩
    · rw [Real.exp_log hYM]; exact pow_div_le_of_inWin F hw hM
    · rw [pow_div_pow_eq_exp]
      apply Real.exp_le_exp.mpr
      have := (abs_le.mp hc).2
      nlinarith
    · rw [pow_div_pow_eq_exp]
      apply Real.exp_le_exp.mpr
      have := (abs_le.mp hc).1
      nlinarith
  by_cases hcond : F.drift * k ≤ Real.log (Y / M) + R * Real.log F.p
  · rw [if_pos hcond]
    set T := min (Real.exp (Real.log (Y / M))) (Real.exp (R * Real.log F.p + F.drift * k))
    have hT : 0 ≤ T := le_min (Real.exp_pos _).le (Real.exp_pos _).le
    rw [← Finset.sum_div, div_le_iff₀ hq]
    have hg := geom_sum_le (r := (F.p : ℝ)) (T := T * (F.q : ℝ) ^ k) hp1 (by positivity) S'
      (fun s hs => by
        have h := hterm s hs
        have : (F.p : ℝ) ^ s / (F.q : ℝ) ^ k ≤ T := le_min h.1 h.2.1
        rwa [div_le_iff₀ hq] at this)
    calc ∑ s ∈ S', (F.p : ℝ) ^ s ≤ (F.p : ℝ) / ((F.p : ℝ) - 1) * (T * (F.q : ℝ) ^ k) := hg
      _ = _ := by ring
  · rw [if_neg hcond, mul_zero]
    have hempty : S' = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro s hs
      have h := hterm s hs
      have h1 := h.2.2.trans h.1
      rw [Real.exp_le_exp] at h1
      exact hcond (by linarith)
    rw [hempty, Finset.sum_empty]

/-- The number of natural numbers in a real interval `[lo, hi]` is at most `hi - lo + 1`. -/
theorem card_le_of_real_bounds (T : Finset ℕ) {lo hi : ℝ} (hlh : lo ≤ hi)
    (h : ∀ k ∈ T, lo ≤ (k : ℝ) ∧ (k : ℝ) ≤ hi) : (T.card : ℝ) ≤ hi - lo + 1 := by
  rcases T.eq_empty_or_nonempty with rfl | ⟨k₀, hk₀⟩
  · simp only [Finset.card_empty, Nat.cast_zero]; linarith
  have hhi : 0 ≤ hi := le_trans (Nat.cast_nonneg k₀) (h k₀ hk₀).2
  have hsub : T ⊆ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊ := fun k hk => by
    rw [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.mpr (h k hk).1, Nat.le_floor (h k hk).2⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have h1 : (⌊hi⌋₊ : ℝ) ≤ hi := Nat.floor_le hhi
  have h2 : lo ≤ (⌈lo⌉₊ : ℝ) := Nat.le_ceil lo
  rcases le_or_gt ⌈lo⌉₊ (⌊hi⌋₊ + 1) with hle | hgt
  · have : (T.card : ℝ) ≤ ((⌊hi⌋₊ + 1 - ⌈lo⌉₊ : ℕ) : ℝ) := by exact_mod_cast hc
    rw [Nat.cast_sub hle] at this
    push_cast at this
    linarith
  · have : T.card = 0 := by omega
    rw [this, Nat.cast_zero]; linarith

/-- **The sum over rows**: a count of the central window (width `2a/d + 1`) and the geometric series below it. -/
theorem rows_sum_le {α x v a : ℝ} (ha : 0 ≤ a) :
    ∑ n ∈ rows F α x, (if F.drift * ((n - F.mZero α x : ℕ) : ℝ) ≤ v + a
        then min (Real.exp v) (Real.exp (a + F.drift * ((n - F.mZero α x : ℕ) : ℝ))) else 0)
      ≤ Real.exp v * (2 * a / F.drift + 1 + Real.exp F.drift / (Real.exp F.drift - 1)) := by
  classical
  set m₀ := F.mZero α x with hm₀
  set d := F.drift with hd_def
  have hd : 0 < d := F.drift_pos
  have hinj : Set.InjOn (fun n : ℕ => n - m₀) ↑(rows F α x) := by
    intro n hn n' hn' h
    simp only [rows, Finset.coe_Icc, Set.mem_Icc] at hn hn'
    simp only at h
    omega
  have hpt : ∀ n ∈ rows F α x, (if d * ((n - m₀ : ℕ) : ℝ) ≤ v + a
        then min (Real.exp v) (Real.exp (a + d * ((n - m₀ : ℕ) : ℝ))) else 0)
      ≤ (if v - a < d * ((n - m₀ : ℕ) : ℝ) ∧ d * ((n - m₀ : ℕ) : ℝ) ≤ v + a
            then Real.exp v else 0)
        + (if d * ((n - m₀ : ℕ) : ℝ) ≤ v - a
            then Real.exp (a + d * ((n - m₀ : ℕ) : ℝ)) else 0) := by
    intro n _
    set t := d * ((n - m₀ : ℕ) : ℝ)
    by_cases h1 : t ≤ v + a
    · rw [if_pos h1]
      by_cases h2 : t ≤ v - a
      · rw [if_neg (fun h => by linarith [h.1]), if_pos h2, zero_add]
        exact min_le_right _ _
      · rw [if_pos ⟨lt_of_not_ge h2, h1⟩, if_neg h2, add_zero]
        exact min_le_left _ _
    · rw [if_neg h1]
      have e1 : 0 ≤ (if v - a < t ∧ t ≤ v + a then Real.exp v else 0) := by
        split_ifs <;> positivity
      have e2 : 0 ≤ (if t ≤ v - a then Real.exp (a + t) else 0) := by
        split_ifs <;> positivity
      linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib]
  have hA : ∑ n ∈ rows F α x, (if v - a < d * ((n - m₀ : ℕ) : ℝ) ∧ d * ((n - m₀ : ℕ) : ℝ) ≤ v + a
      then Real.exp v else 0) ≤ Real.exp v * (2 * a / d + 1) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos v).le
    set Fl := (rows F α x).filter
      (fun n => v - a < d * ((n - m₀ : ℕ) : ℝ) ∧ d * ((n - m₀ : ℕ) : ℝ) ≤ v + a) with hFl
    have hcard : Fl.card = (Fl.image (fun n => n - m₀)).card :=
      (Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))).symm
    rw [hcard]
    have hb := card_le_of_real_bounds (Fl.image (fun n => n - m₀)) (lo := (v - a) / d)
      (hi := (v + a) / d) (by gcongr; linarith) (fun k hk => by
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
        obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hn).2
        constructor
        · rw [div_le_iff₀ hd]; linarith
        · rw [le_div_iff₀ hd]; linarith)
    calc _ ≤ (v + a) / d - (v - a) / d + 1 := hb
      _ = 2 * a / d + 1 := by field_simp; ring
  have hB : ∑ n ∈ rows F α x, (if d * ((n - m₀ : ℕ) : ℝ) ≤ v - a
      then Real.exp (a + d * ((n - m₀ : ℕ) : ℝ)) else 0)
        ≤ Real.exp v * (Real.exp d / (Real.exp d - 1)) := by
    rw [← Finset.sum_filter]
    set Fl := (rows F α x).filter (fun n => d * ((n - m₀ : ℕ) : ℝ) ≤ v - a) with hFl
    have hre : ∀ n : ℕ, Real.exp (a + d * ((n - m₀ : ℕ) : ℝ))
        = Real.exp a * Real.exp d ^ (n - m₀) := by
      intro n; rw [Real.exp_add, mul_comm d, Real.exp_nat_mul]
    rw [Finset.sum_congr rfl (fun n _ => hre n), ← Finset.mul_sum]
    rw [← Finset.sum_image (f := fun k => Real.exp d ^ k)
      (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]
    have hed : 1 < Real.exp d := by have := Real.add_one_lt_exp hd.ne'; linarith
    have hg := geom_sum_le hed (T := Real.exp (v - a)) (Real.exp_pos _).le
      (Fl.image (fun n => n - m₀)) (fun k hk => by
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
        rw [← Real.exp_nat_mul, Real.exp_le_exp]
        have := (Finset.mem_filter.mp hn).2
        linarith)
    have hed1 : 0 < Real.exp d - 1 := by linarith
    calc Real.exp a * ∑ k ∈ Fl.image (fun n => n - m₀), Real.exp d ^ k
        ≤ Real.exp a * (Real.exp d / (Real.exp d - 1) * Real.exp (v - a)) :=
          mul_le_mul_of_nonneg_left hg (Real.exp_pos a).le
      _ = Real.exp v * (Real.exp d / (Real.exp d - 1)) := by
          rw [Real.exp_sub]; field_simp
  calc _ ≤ Real.exp v * (2 * a / d + 1) + Real.exp v * (Real.exp d / (Real.exp d - 1)) :=
        add_le_add hA hB
    _ = _ := by ring

open Classical in
/-- **Upper bound for the kernel restricted to the centre**. -/
theorem kernC_le {α x y Y R M : ℝ} (hY : 0 < Y) (hM : 0 < M) (hR : 0 ≤ R) (S : Finset ℕ) :
    ∑ n ∈ rows F α x, ∑ s ∈ S,
        (if inWin F y Y (n - F.mZero α x) s M ∧
            |(s : ℝ) - F.mu * ((n - F.mZero α x : ℕ) : ℝ)| ≤ R
          then (F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - F.mZero α x) else 0)
      ≤ (F.p : ℝ) / ((F.p : ℝ) - 1) * (Y / M) * NR F R := by
  have hYM : 0 < Y / M := div_pos hY hM
  have hp1 : 0 < (F.p : ℝ) / ((F.p : ℝ) - 1) :=
    div_pos F.p_real_pos (by linarith [F.one_lt_p_real])
  have ha : 0 ≤ R * Real.log F.p := mul_nonneg hR F.log_p_pos.le
  calc _ ≤ ∑ n ∈ rows F α x, (F.p : ℝ) / ((F.p : ℝ) - 1) *
          (if F.drift * ((n - F.mZero α x : ℕ) : ℝ) ≤ Real.log (Y / M) + R * Real.log F.p
            then min (Real.exp (Real.log (Y / M)))
              (Real.exp (R * Real.log F.p + F.drift * ((n - F.mZero α x : ℕ) : ℝ)))
            else 0) :=
        Finset.sum_le_sum fun n _ => inner_le F hY hM _ S
    _ = (F.p : ℝ) / ((F.p : ℝ) - 1) * ∑ n ∈ rows F α x,
          (if F.drift * ((n - F.mZero α x : ℕ) : ℝ) ≤ Real.log (Y / M) + R * Real.log F.p
            then min (Real.exp (Real.log (Y / M)))
              (Real.exp (R * Real.log F.p + F.drift * ((n - F.mZero α x : ℕ) : ℝ)))
            else 0) := by rw [Finset.mul_sum]
    _ ≤ (F.p : ℝ) / ((F.p : ℝ) - 1) * (Real.exp (Real.log (Y / M)) *
          (2 * (R * Real.log F.p) / F.drift + 1 + Real.exp F.drift / (Real.exp F.drift - 1))) :=
        mul_le_mul_of_nonneg_left (rows_sum_le F ha) hp1.le
    _ = _ := by rw [Real.exp_log hYM]; unfold NR; ring

end MasterAux

end ND

end GGMCollatz
