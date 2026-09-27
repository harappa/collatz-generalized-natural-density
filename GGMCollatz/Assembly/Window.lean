import GGMCollatz.Statement
import GGMCollatz.Assembly.Prob
import GGMCollatz.Assembly.Orbit

/-!
# The assembly of (A), part 4: window probabilities and the seed ((o)(i) of the accompanying paper)

* `expect_logUnif_indicator`: the probability of an event under the logarithmic distribution on a window
  is `(∑_{W ∩ E} 1/N)/(∑_W 1/N)`.
* `windowProb_eq`, `bad_mass_eq`: the window probability is "logarithmic mass of the bad points / total
  mass of the window".
* `mass_ge`: if `y ≥ 2` and `3py ≤ y^α`, the total mass of the window is at least `1/(6p)`.
* `bad_mass_le`: from the seed (Theorem 4.1 of the paper), the logarithmic mass of the bad points of the window
  `[lo, hi]` is at most `C (ℓ_max + 1)² (L+1) e^{-cL}` (`ℓ_max = ⌊log_p ⌊hi⌋⌋`). For each shell the window
  meets, we bound by `#(bad points of the shell) · p^{-ℓ}`, and place the bad points of the shell in the
  set of the seed.
* `windowProb_base`: if `log y ≤ Λ` then `P(N₀, y) ≤ 6pC(αΛ/log p + 1)²(L+1)e^{-cL}` ((o)(i) of the
  accompanying paper).

**Deviation from the accompanying paper**: the paper cancels the asymptotic window mass `π(α-1)ln y`
against the number of shells `≈ (α-1)log_p y` to obtain `P ≤ K_w max f`. Here we only bound the window
mass from below by the constant `1/(6p)`, and keep the factor `ℓ_max + 1` from the number of shells
(squared: `(ℓ_max+1)²`). This factor is absorbed by taking `v = e^{c_B L/4}` (the paper uses
`e^{c_B L/2}`) (`Uniform.lean`). Only the exponent of the rate changes; the form of (A) is the same.
-/

namespace GGMCollatz

namespace Asm

theorem mem_logWindow {F : Family} {lo hi : ℝ} {N : ℕ} :
    N ∈ F.logWindow lo hi ↔ N % F.p ≠ 0 ∧ lo ≤ (N : ℝ) ∧ (N : ℝ) ≤ hi := by
  unfold Family.logWindow
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have h1 : (N : ℝ) ≤ (⌈hi⌉₊ : ℝ) := le_trans h.2.2 (Nat.le_ceil hi)
    have h2 : N ≤ ⌈hi⌉₊ := by exact_mod_cast h1
    omega

theorem ne_zero_of_mem_logWindow {F : Family} {lo hi : ℝ} {N : ℕ} (h : N ∈ F.logWindow lo hi) :
    N ≠ 0 := by
  intro h0
  have := (mem_logWindow.mp h).1
  rw [h0, Nat.zero_mod] at this
  exact this rfl

/-- The probability of an event under the logarithmic distribution on a window. -/
theorem expect_logUnif_indicator (F : Family) (lo hi : ℝ) (P : ℕ → Prop) [DecidablePred P]
    (h : (F.logWindow lo hi).Nonempty ∨ ¬ P 1) :
    Family.expect (F.logUnif lo hi) ({N | P N}.indicator 1) =
      (∑ N ∈ (F.logWindow lo hi).filter P, (N : ℝ)⁻¹) / (∑ N ∈ F.logWindow lo hi, (N : ℝ)⁻¹) := by
  by_cases hW : (F.logWindow lo hi).Nonempty
  · set W := F.logWindow lo hi with hWdef
    set D : ENNReal := ∑ M ∈ W, (M : ENNReal)⁻¹ with hD
    have hμ : ∀ N, F.logUnif lo hi N = if N ∈ W then (N : ENNReal)⁻¹ / D else 0 := by
      intro N
      unfold Family.logUnif
      rw [dif_pos hW]
      rfl
    have hWne : ∀ M ∈ W, (M : ENNReal)⁻¹ ≠ ⊤ := by
      intro M hM
      rw [ENNReal.inv_ne_top]
      exact_mod_cast ne_zero_of_mem_logWindow hM
    have hDreal : D.toReal = ∑ M ∈ W, (M : ℝ)⁻¹ := by
      rw [hD, ENNReal.toReal_sum hWne]
      refine Finset.sum_congr rfl fun M _ => ?_
      rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [expect_indicator, PMF.toOuterMeasure_apply]
    have hsum : ∑' N, {N | P N}.indicator (F.logUnif lo hi) N =
        ∑ N ∈ W.filter P, (N : ENNReal)⁻¹ / D := by
      rw [tsum_eq_sum (s := W)]
      · rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun N hN => ?_
        by_cases hP : P N
        · rw [Set.indicator_of_mem (show N ∈ {N | P N} from hP), hμ, if_pos hN, if_pos hP]
        · rw [Set.indicator_of_notMem (show N ∉ {N | P N} from hP), if_neg hP]
      · intro N hN
        by_cases hP : P N
        · rw [Set.indicator_of_mem (show N ∈ {N | P N} from hP), hμ, if_neg hN]
        · rw [Set.indicator_of_notMem (show N ∉ {N | P N} from hP)]
    rw [hsum, ENNReal.toReal_sum]
    · rw [← hDreal, Finset.sum_div]
      refine Finset.sum_congr rfl fun N _ => ?_
      rw [ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    · intro N hN
      exact ENNReal.div_ne_top (hWne N (Finset.mem_filter.mp hN).1) (by
        rw [hD]
        intro h0
        rw [Finset.sum_eq_zero_iff] at h0
        obtain ⟨M₀, hM₀⟩ := hW
        have := h0 M₀ hM₀
        rw [ENNReal.inv_eq_zero] at this
        exact ENNReal.natCast_ne_top M₀ this)
  · have hP1 : ¬ P 1 := h.resolve_left hW
    have hW0 : F.logWindow lo hi = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    have hμ : F.logUnif lo hi = PMF.pure 1 := by
      unfold Family.logUnif
      rw [dif_neg hW]
    rw [hμ, expect_pure_indicator, hW0]
    simp [hP1]

theorem not_lt_Smin_one' (F : Family) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) : ¬ N₀ < F.Smin 1 :=
  not_lt_Smin_one F hN₀

/-- The window probability is "logarithmic mass of the bad points / total mass of the window". -/
theorem windowProb_eq (F : Family) (α : ℝ) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (y : ℝ) :
    F.windowProb α N₀ y =
      (∑ N ∈ (F.logWindow y (y ^ α)).filter (fun N => N₀ < F.Smin N), (N : ℝ)⁻¹) /
        (∑ N ∈ F.logWindow y (y ^ α), (N : ℝ)⁻¹) :=
  expect_logUnif_indicator F y (y ^ α) (fun N => N₀ < F.Smin N)
    (Or.inr (not_lt_Smin_one F hN₀))

theorem windowProb_nonneg (F : Family) (α : ℝ) (N₀ : ℕ) (y : ℝ) : 0 ≤ F.windowProb α N₀ y :=
  expect_indicator_nonneg _ _

theorem windowProb_le_one (F : Family) (α : ℝ) (N₀ : ℕ) (y : ℝ) : F.windowProb α N₀ y ≤ 1 :=
  expect_indicator_le_one _ _

/-- Logarithmic mass of the bad points = window probability × total mass of the window. -/
theorem bad_mass_eq (F : Family) (α : ℝ) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (y : ℝ) :
    ∑ N ∈ (F.logWindow y (y ^ α)).filter (fun N => N₀ < F.Smin N), (N : ℝ)⁻¹ =
      F.windowProb α N₀ y * ∑ N ∈ F.logWindow y (y ^ α), (N : ℝ)⁻¹ := by
  rw [windowProb_eq F α hN₀ y]
  set A := ∑ N ∈ (F.logWindow y (y ^ α)).filter (fun N => N₀ < F.Smin N), (N : ℝ)⁻¹
  set B := ∑ N ∈ F.logWindow y (y ^ α), (N : ℝ)⁻¹
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun N _ => by positivity
  have hAB : A ≤ B := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun N _ _ => by positivity)
  by_cases hB : B = 0
  · have : A = 0 := le_antisymm (hB ▸ hAB) hA0
    rw [this, hB]; simp
  · rw [div_mul_cancel₀ A hB]

/-- Lower bound for the total mass of the window: if `y ≥ 2` and `3py ≤ y^α` then `∑_W 1/N ≥ 1/(6p)`. -/
theorem mass_ge (F : Family) {α y : ℝ} (hy : 2 ≤ y) (hyα : 3 * F.p * y ≤ y ^ α) :
    1 / (6 * F.p) ≤ ∑ N ∈ F.logWindow y (y ^ α), (N : ℝ)⁻¹ := by
  have hp2 : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hp1 : 1 < F.p := F.one_lt_p
  have hy0 : 0 ≤ y := by linarith
  set a := ⌈y⌉₊ with ha
  set n := ⌊y⌋₊ with hn
  have hay : y ≤ (a : ℝ) := Nat.le_ceil y
  have hay' : (a : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
  have hny : (n : ℝ) ≤ y := Nat.floor_le hy0
  have hny' : y - 1 < (n : ℝ) := Nat.sub_one_lt_floor y
  set img := (Finset.range n).image (fun i => (a + i) * F.p + 1) with himg
  have hmem : ∀ i, i < n → ((a + i) * F.p + 1 : ℕ) ∈ F.logWindow y (y ^ α) ∧
      ((3 * F.p * y) : ℝ)⁻¹ ≤ (((a + i) * F.p + 1 : ℕ) : ℝ)⁻¹ := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
    have hle : ((a + i) * F.p + 1 : ℕ) ≤ (a + n) * F.p := by
      have : (a + i) * F.p + F.p ≤ (a + n) * F.p := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
      omega
    have hle' : (((a + i) * F.p + 1 : ℕ) : ℝ) ≤ 3 * F.p * y := by
      have h1 : (((a + i) * F.p + 1 : ℕ) : ℝ) ≤ ((a + n) * F.p : ℕ) := by exact_mod_cast hle
      have h3 : ((a : ℝ) + n) * F.p ≤ 3 * F.p * y := by
        have : (a : ℝ) + n ≤ 3 * y := by linarith
        nlinarith
      push_cast at h1 ⊢
      linarith
    have hpos : (0 : ℝ) < (((a + i) * F.p + 1 : ℕ) : ℝ) := by positivity
    refine ⟨mem_logWindow.mpr ⟨?_, ?_, le_trans hle' hyα⟩, inv_anti₀ hpos hle'⟩
    · rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hp1]; exact one_ne_zero
    · push_cast
      nlinarith
  have hsub : img ⊆ F.logWindow y (y ^ α) := by
    intro N hN
    rw [himg, Finset.mem_image] at hN
    obtain ⟨i, hi, rfl⟩ := hN
    exact (hmem i (Finset.mem_range.mp hi)).1
  have hcard : img.card = n := by
    rw [himg, Finset.card_image_of_injective _ (fun i j h => by
      have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < F.p) (by omega : (a + i) * F.p = (a + j) * F.p)
      omega), Finset.card_range]
  have h1 : (n : ℝ) * (3 * F.p * y)⁻¹ ≤ ∑ N ∈ img, (N : ℝ)⁻¹ := by
    rw [← hcard, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro N hN
    rw [himg, Finset.mem_image] at hN
    obtain ⟨i, hi, rfl⟩ := hN
    exact (hmem i (Finset.mem_range.mp hi)).2
  have h2 : ∑ N ∈ img, (N : ℝ)⁻¹ ≤ ∑ N ∈ F.logWindow y (y ^ α), (N : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun N _ _ => by positivity)
  have h3 : 1 / (6 * F.p) ≤ (n : ℝ) * (3 * F.p * y)⁻¹ := by
    have hyp : 0 < 3 * (F.p : ℝ) * y := by positivity
    rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hyp]
    nlinarith
  linarith

open Classical in
/-- From the seed, an upper bound for the logarithmic mass of the bad points of the window `[lo, hi]`. -/
theorem bad_mass_le (F : Family) {c C : ℝ} (hC : 0 ≤ C) {L₀ : ℕ}
    (hseed : ∀ L M : ℕ, L₀ ≤ L → L ≤ M →
      (((Finset.Ico (F.p ^ M) (F.p ^ (M + 1))).filter
          (fun n => ∀ k, F.p ^ L ≤ F.Ct^[k] n)).card : ℝ)
        ≤ C * (F.p : ℝ) ^ M * ((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(c * L)))
    {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (hL : L₀ ≤ Nat.log F.p N₀) (lo hi : ℝ) :
    ∑ N ∈ (F.logWindow lo hi).filter (fun N => N₀ < F.Smin N), (N : ℝ)⁻¹ ≤
      C * ((Nat.log F.p ⌊hi⌋₊ : ℝ) + 1) ^ 2 * ((Nat.log F.p N₀ : ℝ) + 1) *
        Real.exp (-(c * Nat.log F.p N₀)) := by
  set L := Nat.log F.p N₀ with hLdef
  set lm := Nat.log F.p ⌊hi⌋₊ with hlm
  set S := (F.logWindow lo hi).filter (fun N => N₀ < F.Smin N) with hS
  set E : ℝ := C * ((L : ℝ) + 1) * Real.exp (-(c * L)) with hE
  have hE0 : 0 ≤ E := by positivity
  have hp1 : 1 < F.p := F.one_lt_p
  have hpL : F.p ^ L ≤ N₀ := Nat.pow_log_le_self F.p (by omega)
  have hmaps : ∀ N ∈ S, Nat.log F.p N ∈ Finset.range (lm + 1) := by
    intro N hN
    rw [hS, Finset.mem_filter] at hN
    have h1 := (mem_logWindow.mp hN.1).2.2
    have h2 : N ≤ ⌊hi⌋₊ := Nat.le_floor h1
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right h2)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ ℓ ∈ Finset.range (lm + 1),
      ∑ N ∈ S.filter (fun N => Nat.log F.p N = ℓ), (N : ℝ)⁻¹ ≤ ((lm : ℝ) + 1) * E := by
    intro ℓ hℓ
    have hℓ' : (ℓ : ℝ) ≤ lm := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)
    set T := (Finset.Ico (F.p ^ ℓ) (F.p ^ (ℓ + 1))).filter (fun n => ∀ k, F.p ^ L ≤ F.Ct^[k] n)
    have hsubT : S.filter (fun N => Nat.log F.p N = ℓ) ⊆ T := by
      intro N hN
      rw [Finset.mem_filter, hS, Finset.mem_filter] at hN
      obtain ⟨⟨hW, hbad⟩, hlog⟩ := hN
      have hN0 : N ≠ 0 := ne_zero_of_mem_logWindow hW
      rw [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨hlog ▸ Nat.pow_log_le_self F.p hN0, hlog ▸ Nat.lt_pow_succ_log_self hp1 N⟩, ?_⟩
      exact Ct_iterate_ge_of_lt_Smin F (mem_logWindow.mp hW).1 hpL hbad
    have h1 : ∑ N ∈ S.filter (fun N => Nat.log F.p N = ℓ), (N : ℝ)⁻¹ ≤
        (T.card : ℝ) * ((F.p : ℝ) ^ ℓ)⁻¹ := by
      calc _ ≤ ∑ N ∈ S.filter (fun N => Nat.log F.p N = ℓ), ((F.p : ℝ) ^ ℓ)⁻¹ := by
            apply Finset.sum_le_sum
            intro N hN
            have hNT := hsubT hN
            rw [Finset.mem_filter, Finset.mem_Ico] at hNT
            apply inv_anti₀ (by positivity)
            exact_mod_cast hNT.1.1
        _ = ((S.filter (fun N => Nat.log F.p N = ℓ)).card : ℝ) * ((F.p : ℝ) ^ ℓ)⁻¹ := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (T.card : ℝ) * ((F.p : ℝ) ^ ℓ)⁻¹ := by
            gcongr
    have h2 : (T.card : ℝ) * ((F.p : ℝ) ^ ℓ)⁻¹ ≤ ((ℓ : ℝ) + 1) * E := by
      by_cases hLℓ : L ≤ ℓ
      · have hs := hseed L ℓ hL hLℓ
        have hpℓ : (0 : ℝ) < (F.p : ℝ) ^ ℓ := by have := F.p_pos; positivity
        rw [← div_eq_mul_inv, div_le_iff₀ hpℓ]
        calc (T.card : ℝ) ≤ _ := hs
          _ = ((ℓ : ℝ) + 1) * E * (F.p : ℝ) ^ ℓ := by rw [hE]; ring
      · have hT : T = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro n hn hk
          rw [Finset.mem_Ico] at hn
          have h0 := hk 0
          simp only [Function.iterate_zero, id] at h0
          have : F.p ^ (ℓ + 1) ≤ F.p ^ L := Nat.pow_le_pow_right F.p_pos (by omega)
          omega
        rw [hT, Finset.card_empty, Nat.cast_zero, zero_mul]
        positivity
    calc _ ≤ _ := h1
      _ ≤ ((ℓ : ℝ) + 1) * E := h2
      _ ≤ ((lm : ℝ) + 1) * E := by gcongr
  calc _ ≤ ∑ ℓ ∈ Finset.range (lm + 1), ((lm : ℝ) + 1) * E := Finset.sum_le_sum hfib
    _ = ((lm : ℝ) + 1) * (((lm : ℝ) + 1) * E) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ = C * ((lm : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) * Real.exp (-(c * L)) := by rw [hE]; ring

/-- The threshold for the lower end of the window, `y_w = max(2, (3p)^{1/(α-1)})`. -/
noncomputable def yw (F : Family) (α : ℝ) : ℝ := max 2 ((3 * F.p : ℝ) ^ (1 / (α - 1)))

theorem two_le_yw (F : Family) (α : ℝ) : 2 ≤ yw F α := le_max_left _ _

/-- If `y ≥ y_w` then `3py ≤ y^α`. -/
theorem three_p_mul_le (F : Family) {α y : ℝ} (hα : 1 < α) (hy : yw F α ≤ y) :
    3 * F.p * y ≤ y ^ α := by
  have hy2 : 2 ≤ y := le_trans (two_le_yw F α) hy
  have hy0 : 0 < y := by linarith
  have h3p : (0 : ℝ) ≤ 3 * F.p := by positivity
  have h1 : (3 * F.p : ℝ) ≤ y ^ (α - 1) := by
    have hb : (3 * F.p : ℝ) ^ (1 / (α - 1)) ≤ y := le_trans (le_max_right _ _) hy
    have := Real.rpow_le_rpow (by positivity) hb (by linarith : (0 : ℝ) ≤ α - 1)
    rwa [← Real.rpow_mul h3p, one_div_mul_cancel (by linarith), Real.rpow_one] at this
  have h2 : y ^ α = y ^ (α - 1) * y := by
    rw [Real.rpow_sub_one hy0.ne']; field_simp
  rw [h2]
  nlinarith

open Classical in
/-- The bottom windows ((o)(i) of the accompanying paper): if `log y ≤ Λ` then
`P(N₀, y) ≤ 6pC(αΛ/log p + 1)²(L+1)e^{-cL}`. We assume `L ≥ L₀` and `y_w^α ≤ p^L`. -/
theorem windowProb_base (F : Family) {α : ℝ} (hα : 1 < α) {c C : ℝ} (hC : 0 ≤ C) {L₀ : ℕ}
    (hseed : ∀ L M : ℕ, L₀ ≤ L → L ≤ M →
      (((Finset.Ico (F.p ^ M) (F.p ^ (M + 1))).filter
          (fun n => ∀ k, F.p ^ L ≤ F.Ct^[k] n)).card : ℝ)
        ≤ C * (F.p : ℝ) ^ M * ((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(c * L)))
    {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (hL : L₀ ≤ Nat.log F.p N₀)
    (hLw : (yw F α) ^ α ≤ (F.p : ℝ) ^ Nat.log F.p N₀)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {y : ℝ} (hy : 0 < y) (hyΛ : Real.log y ≤ Λ) :
    F.windowProb α N₀ y ≤ 6 * F.p * C * (α * Λ / Real.log F.p + 1) ^ 2 *
      ((Nat.log F.p N₀ : ℝ) + 1) * Real.exp (-(c * Nat.log F.p N₀)) := by
  set L := Nat.log F.p N₀ with hLdef
  have hp2 : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hlp : 0 < Real.log F.p := Real.log_pos (by linarith)
  have hα0 : 0 < α := by linarith
  have hRHS : 0 ≤ 6 * F.p * C * (α * Λ / Real.log F.p + 1) ^ 2 *
      ((L : ℝ) + 1) * Real.exp (-(c * L)) := by positivity
  by_cases hyw : y < yw F α
  · -- (o) Empty window: the points of the window satisfy `N ≤ y^α < y_w^α ≤ p^L ≤ N₀`
    have hpL : F.p ^ L ≤ N₀ := Nat.pow_log_le_self F.p (by omega)
    have hempty : (F.logWindow y (y ^ α)).filter (fun N => N₀ < F.Smin N) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro N hN hbad
      have h1 := (mem_logWindow.mp hN).2.2
      have h2 : y ^ α < (yw F α) ^ α := Real.rpow_lt_rpow hy.le hyw hα0
      have h3 : (N : ℝ) < (N₀ : ℝ) := by
        have : ((F.p ^ L : ℕ) : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hpL
        push_cast at this
        linarith
      have h4 : N < N₀ := by exact_mod_cast h3
      have := Smin_le_self F N
      omega
    rw [windowProb_eq F α hN₀ y, hempty, Finset.sum_empty, zero_div]
    exact hRHS
  · -- (i) Shell estimate and the seed
    push Not at hyw
    have hy2 : 2 ≤ y := le_trans (two_le_yw F α) hyw
    have hyα := three_p_mul_le F hα hyw
    have hmass := mass_ge F hy2 hyα
    have hbad := bad_mass_le F hC hseed hN₀ hL y (y ^ α)
    set lm := Nat.log F.p ⌊y ^ α⌋₊ with hlm
    -- `ℓ_max ≤ αΛ / log p`
    have hlm' : (lm : ℝ) ≤ α * Λ / Real.log F.p := by
      have hyα1 : 1 ≤ y ^ α := Real.one_le_rpow (by linarith) hα0.le
      have hfl : ⌊y ^ α⌋₊ ≠ 0 := by
        have := Nat.floor_pos.mpr hyα1; omega
      have h1 : F.p ^ lm ≤ ⌊y ^ α⌋₊ := Nat.pow_log_le_self F.p hfl
      have h2 : ((F.p : ℝ) ^ lm) ≤ y ^ α := by
        have : ((F.p ^ lm : ℕ) : ℝ) ≤ (⌊y ^ α⌋₊ : ℝ) := by exact_mod_cast h1
        push_cast at this
        exact le_trans this (Nat.floor_le (by positivity))
      have h3 := Real.log_le_log (by positivity) h2
      rw [Real.log_pow, Real.log_rpow hy] at h3
      rw [le_div_iff₀ hlp]
      nlinarith
    rw [windowProb_eq F α hN₀ y]
    set A := ∑ N ∈ (F.logWindow y (y ^ α)).filter (fun N => N₀ < F.Smin N), (N : ℝ)⁻¹
    set B := ∑ N ∈ F.logWindow y (y ^ α), (N : ℝ)⁻¹
    have hB : 0 < B := lt_of_lt_of_le (by positivity) hmass
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun N _ => by positivity
    rw [div_le_iff₀ hB]
    have hsq : ((lm : ℝ) + 1) ^ 2 ≤ (α * Λ / Real.log F.p + 1) ^ 2 := by
      have : (0 : ℝ) ≤ (lm : ℝ) + 1 := by positivity
      gcongr
    have hK : 0 ≤ C * ((L : ℝ) + 1) * Real.exp (-(c * L)) := by positivity
    have hA : A ≤ C * (α * Λ / Real.log F.p + 1) ^ 2 * ((L : ℝ) + 1) * Real.exp (-(c * L)) := by
      calc A ≤ C * ((lm : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) * Real.exp (-(c * L)) := hbad
        _ = (C * ((L : ℝ) + 1) * Real.exp (-(c * L))) * ((lm : ℝ) + 1) ^ 2 := by ring
        _ ≤ (C * ((L : ℝ) + 1) * Real.exp (-(c * L))) * (α * Λ / Real.log F.p + 1) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq hK
        _ = _ := by ring
    have hp0 : (0 : ℝ) < 6 * F.p := by positivity
    have hmass' : 1 ≤ 6 * F.p * B := by
      rw [div_le_iff₀ hp0] at hmass; linarith
    calc A ≤ C * (α * Λ / Real.log F.p + 1) ^ 2 * ((L : ℝ) + 1) * Real.exp (-(c * L)) := hA
      _ ≤ C * (α * Λ / Real.log F.p + 1) ^ 2 * ((L : ℝ) + 1) * Real.exp (-(c * L)) *
            (6 * F.p * B) := le_mul_of_one_le_right (by positivity) hmass'
      _ = _ := by ring

end Asm

end GGMCollatz
