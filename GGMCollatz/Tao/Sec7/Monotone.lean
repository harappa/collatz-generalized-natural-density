import GGMCollatz.Tao.Sec7.Holding
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# GGM §7: the monotone quantity `Q_m` and Proposition 7.8 (counterpart of §7.4 of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, files `TaoCollatz/Sec7/Monotone.lean` and
`TaoCollatz/Sec7/BlackEdgeQ.lean` (`prop_7_8_at`, `Q_polynomial_decay_at`); generalized to the GGM family (p, q, r). Modified.
GGM §7 (the proof of Theorem 1.9). Everything is written for a general white set `W` (tao-collatz fixed it to `whiteSet n ξ`).

* `Qm`: `Q_m := sup_{j ≥ half - m} max(half - j, 1)^A Q(j,l)` ((7.38) of tao-collatz).
* `hold_weight_expect`: `E[max(m - 𝒥, 1)^{-A}] ≤ exp(κ/2) m^{-A}` (for large `m`). `𝒥` is geometric with success probability
  `2(p-1)²/p³` (tao-collatz used powers of `3/4` and an explicit threshold; here only the existence of a threshold).
* `Q_white_case1`: Case 1 (white starting point).
* `prop_7_8_of`: Proposition 7.8 (`Q_m ≤ Q_{m-1}`) from the bounds at black edges (Cases 2 and 3).
* `Q_polynomial_decay_of`: (7.37) `Q(j,l) ≤ C max(half - j, 1)^{-A}` from Proposition 7.8.
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- (7.38) of tao-collatz: the supremum of the weighted `Q` over points within depth `m` of the edge. -/
noncomputable def Qm (half : ℕ) (W : Set (ℕ × ℤ)) (κ A : ℝ) (m : ℕ) : ℝ :=
  ⨆ x : {x : ℕ × ℤ // 1 ≤ x.1 ∧ half - m ≤ x.1},
    ((max (half - x.1.1) 1 : ℕ) : ℝ) ^ A * F.Q half W κ x.1.1 x.1.2

/-- (7.39) of tao-collatz: `Q_m ≤ m^A`. -/
theorem Qm_le_rpow (half : ℕ) (W : Set (ℕ × ℤ)) {κ : ℝ} (hκ : 0 ≤ κ) (A : ℝ) (hA : 0 ≤ A)
    (m : ℕ) (hm : 1 ≤ m) : F.Qm half W κ A m ≤ (m : ℝ) ^ A := by
  refine Real.iSup_le (fun x => ?_) (Real.rpow_nonneg (Nat.cast_nonneg m) A)
  have hw : ((max (half - x.1.1) 1 : ℕ) : ℝ) ^ A ≤ (m : ℝ) ^ A := by
    apply Real.rpow_le_rpow (by positivity) _ hA
    have hle : half - x.1.1 ≤ m := by obtain ⟨-, h2⟩ := x.2; omega
    exact_mod_cast max_le hle hm
  calc ((max (half - x.1.1) 1 : ℕ) : ℝ) ^ A * F.Q half W κ x.1.1 x.1.2
      ≤ (m : ℝ) ^ A * 1 := by
        apply mul_le_mul hw (F.Q_le_one _ _ _ hκ _ _) (F.Q_nonneg _ _ _ _ _)
        exact Real.rpow_nonneg (Nat.cast_nonneg m) A
    _ = (m : ℝ) ^ A := mul_one _

/-- The weighted value at an admissible point is at most `Q_m`. -/
theorem le_Qm (half : ℕ) (W : Set (ℕ × ℤ)) {κ : ℝ} (hκ : 0 ≤ κ) (A : ℝ) (hA : 0 ≤ A) (m : ℕ)
    {p1 : ℕ} {l : ℤ} (h1 : 1 ≤ p1) (h2 : half - m ≤ p1) :
    ((max (half - p1) 1 : ℕ) : ℝ) ^ A * F.Q half W κ p1 l ≤ F.Qm half W κ A m := by
  have hbdd : BddAbove (Set.range fun x : {x : ℕ × ℤ // 1 ≤ x.1 ∧ half - m ≤ x.1} =>
      ((max (half - x.1.1) 1 : ℕ) : ℝ) ^ A * F.Q half W κ x.1.1 x.1.2) := by
    refine ⟨((max half 1 : ℕ) : ℝ) ^ A, ?_⟩
    rintro y ⟨x, rfl⟩
    calc ((max (half - x.1.1) 1 : ℕ) : ℝ) ^ A * F.Q half W κ x.1.1 x.1.2
        ≤ ((max half 1 : ℕ) : ℝ) ^ A * 1 := by
          apply mul_le_mul _ (F.Q_le_one _ _ _ hκ _ _) (F.Q_nonneg _ _ _ _ _)
            (Real.rpow_nonneg (by positivity) A)
          apply Real.rpow_le_rpow (by positivity) _ hA
          exact_mod_cast max_le_max (Nat.sub_le _ _) le_rfl
      _ = ((max half 1 : ℕ) : ℝ) ^ A := mul_one _
  exact le_ciSup hbdd ⟨(p1, l), h1, h2⟩

/-- Inverse form: at admissible points, `Q ≤ max(half - p₁, 1)^{-A} Q_m`. -/
theorem Q_le_Qm (half : ℕ) (W : Set (ℕ × ℤ)) {κ : ℝ} (hκ : 0 ≤ κ) (A : ℝ) (hA : 0 ≤ A) (m : ℕ)
    {p1 : ℕ} {l : ℤ} (h1 : 1 ≤ p1) (h2 : half - m ≤ p1) :
    F.Q half W κ p1 l ≤ ((max (half - p1) 1 : ℕ) : ℝ) ^ (-A) * F.Qm half W κ A m := by
  have hwpos : (0:ℝ) < ((max (half - p1) 1 : ℕ) : ℝ) := by
    have h : (1 : ℕ) ≤ max (half - p1) 1 := le_max_right _ _
    have : (1:ℝ) ≤ ((max (half - p1) 1 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  have hApos : (0:ℝ) < ((max (half - p1) 1 : ℕ) : ℝ) ^ A :=
    Real.rpow_pos_of_pos hwpos A
  have hle := F.le_Qm half W hκ A hA m (l := l) h1 h2
  rw [Real.rpow_neg hwpos.le]
  calc F.Q half W κ p1 l
      = (((max (half - p1) 1 : ℕ) : ℝ) ^ A)⁻¹
        * (((max (half - p1) 1 : ℕ) : ℝ) ^ A * F.Q half W κ p1 l) := by
        field_simp
    _ ≤ (((max (half - p1) 1 : ℕ) : ℝ) ^ A)⁻¹ * F.Qm half W κ A m :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hApos.le)

/-- `Q_m ≥ 0`. -/
theorem Qm_nonneg (half : ℕ) (W : Set (ℕ × ℤ)) (κ A : ℝ) (m : ℕ) : 0 ≤ F.Qm half W κ A m :=
  Real.iSup_nonneg fun x =>
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (F.Q_nonneg _ _ _ _ _)

/-! ### Tails of the law of `𝒥` (geometric with success probability `s = 2(p-1)²/p³`) -/

/-- The ratio `ρ = 1 - s` of the geometric law (as a real). -/
noncomputable def holdRatio : ℝ := 1 - (pascalP F.p 3).toReal

theorem holdRatio_nonneg : 0 ≤ F.holdRatio := by
  have h := (holdGeom_prob F.two_le_p).2
  have : (pascalP F.p 3).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top h
    simpa using this
  unfold holdRatio; linarith

theorem holdRatio_lt_one : F.holdRatio < 1 := by
  have h := holdGeom_prob F.two_le_p
  have hne : pascalP F.p 3 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top h.2
  have : 0 < (pascalP F.p 3).toReal := ENNReal.toReal_pos h.1.ne' hne
  unfold holdRatio; linarith

theorem holdGeom_tsum_toReal : ∑' k : ℕ, (holdGeom F.p k).toReal = 1 :=
  geomS_tsum_toReal _

theorem holdGeom_summable_toReal : Summable fun k : ℕ => (holdGeom F.p k).toReal :=
  geomS_summable_toReal _

/-- Tail: `P(𝒥 > t) = ρ^t`. -/
theorem holdGeom_tail (t : ℕ) :
    ∑' k : ℕ, (if t < k then (holdGeom F.p k).toReal else 0) = F.holdRatio ^ t :=
  geomS_tail (holdGeom_prob F.two_le_p) t

/-- **Core of `hold_weight_expect`** (the lemma of the same name in tao-collatz, generalized to the ratio `ρ`): given three thresholds
`K` (middle zone), `M1` (head zone) and `T` (tail zone), for `m ≥ K + M1 + 2T + 4` we have
`E[max(m - 𝒥, 1)^{-A}] ≤ (1+δ) m^{-A}`. -/
theorem hold_weight_expect_core (A : ℝ) (hA : 0 < A) (δ : ℝ) (hδ : 0 < δ) (K M1 T : ℕ)
    (hK : F.holdRatio ^ K < δ / 3 * (2 : ℝ) ^ (-A))
    (hM1 : (K : ℝ) * (1 + δ / 3) ^ A⁻¹ / ((1 + δ / 3) ^ A⁻¹ - 1) ≤ (M1 : ℝ))
    (hT : ∀ t : ℕ, T ≤ t → (t : ℝ) ^ ⌈A⌉₊ * F.holdRatio ^ t < δ / 3 * (3 : ℝ) ^ (-A)) :
    ∀ m : ℕ, K + M1 + 2 * T + 4 ≤ m →
      ∑' d : ℕ × ℤ, (F.hold d).toReal * ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A)
        ≤ (1 + δ) * (m : ℝ) ^ (-A) := by
  intro m hm
  set ρ := F.holdRatio with hρdef
  have hρ0 : 0 ≤ ρ := F.holdRatio_nonneg
  set c := (1 + δ / 3) ^ A⁻¹ with hcdef
  have hc1 : 1 < c := by
    rw [hcdef, Real.one_lt_rpow_iff_of_pos (by linarith)]
    exact Or.inl ⟨by linarith, by positivity⟩
  have hcA : c ^ A = 1 + δ / 3 := by
    rw [hcdef, ← Real.rpow_mul (by linarith), inv_mul_cancel₀ hA.ne', Real.rpow_one]
  set kA := ⌈A⌉₊ with hkAdef
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  refine le_trans (le_of_eq (F.hold_tsum_fst (fun k => ((max (m - k) 1 : ℕ) : ℝ) ^ (-A))
    (fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _))) ?_
  have hp0 : ∀ k, (0 : ℝ) ≤ (holdGeom F.p k).toReal := fun _ => ENNReal.toReal_nonneg
  have hw0 : ∀ k, (0 : ℝ) ≤ ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) :=
    fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hw1 : ∀ k, ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) ≤ 1 := fun k =>
    Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast Nat.le_max_right (m - k) 1) (by linarith)
  have hterm_le : ∀ k, (holdGeom F.p k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A)
      ≤ (holdGeom F.p k).toReal := fun k => by
    calc (holdGeom F.p k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A)
        ≤ (holdGeom F.p k).toReal * 1 := mul_le_mul_of_nonneg_left (hw1 k) (hp0 k)
      _ = (holdGeom F.p k).toReal := mul_one _
  have hterm0 : ∀ k, (0 : ℝ) ≤ (holdGeom F.p k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) :=
    fun k => mul_nonneg (hp0 k) (hw0 k)
  have hpsum := F.holdGeom_summable_toReal
  set g1 : ℕ → ℝ := fun k => if k ≤ K then
    (holdGeom F.p k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) else 0 with hg1def
  set g2 : ℕ → ℝ := fun k => if K < k ∧ k ≤ m / 2 then
    (holdGeom F.p k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) else 0 with hg2def
  set g3 : ℕ → ℝ := fun k => if K < k ∧ m / 2 < k then
    (holdGeom F.p k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) else 0 with hg3def
  have hsplit : ∀ k, (holdGeom F.p k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A)
      = g1 k + g2 k + g3 k := by
    intro k
    simp only [hg1def, hg2def, hg3def]
    rcases le_or_gt k K with h1 | h1
    · rw [if_pos h1, if_neg (by omega), if_neg (by omega)]; ring
    · rcases le_or_gt k (m / 2) with h2 | h2
      · rw [if_neg (by omega), if_pos ⟨h1, h2⟩, if_neg (by omega)]; ring
      · rw [if_neg (by omega), if_neg (by omega), if_pos ⟨h1, h2⟩]; ring
  have hg1sum : Summable g1 := Summable.of_nonneg_of_le
    (fun k => by simp only [hg1def]; split_ifs; exacts [hterm0 k, le_rfl])
    (fun k => by simp only [hg1def]; split_ifs; exacts [hterm_le k, hp0 k]) hpsum
  have hg2sum : Summable g2 := Summable.of_nonneg_of_le
    (fun k => by simp only [hg2def]; split_ifs; exacts [hterm0 k, le_rfl])
    (fun k => by simp only [hg2def]; split_ifs; exacts [hterm_le k, hp0 k]) hpsum
  have hg3sum : Summable g3 := Summable.of_nonneg_of_le
    (fun k => by simp only [hg3def]; split_ifs; exacts [hterm0 k, le_rfl])
    (fun k => by simp only [hg3def]; split_ifs; exacts [hterm_le k, hp0 k]) hpsum
  -- head zone
  have hmKpos : (0 : ℝ) < ((m - K : ℕ) : ℝ) := by
    have h : 1 ≤ m - K := by omega
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h
  have hW1 : ((m - K : ℕ) : ℝ) ^ (-A) ≤ (1 + δ / 3) * (m : ℝ) ^ (-A) := by
    have hcast : ((m - K : ℕ) : ℝ) = (m : ℝ) - K := by
      rw [Nat.cast_sub (by omega)]
    have hcpos : (0 : ℝ) < c - 1 := by linarith
    have hmge : (K : ℝ) * c / (c - 1) ≤ (m : ℝ) := by
      calc (K : ℝ) * c / (c - 1) ≤ (M1 : ℝ) := hM1
        _ ≤ (m : ℝ) := by exact_mod_cast (by omega : M1 ≤ m)
    have hKc : (K : ℝ) * c ≤ (m : ℝ) * (c - 1) := by
      rw [div_le_iff₀ hcpos] at hmge; linarith
    have hmc : (m : ℝ) / c ≤ (m : ℝ) - K := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < c)]
      nlinarith
    have hstep : ((m : ℝ) - K) ^ (-A) ≤ ((m : ℝ) / c) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hmc (by linarith)
    have hdiv : ((m : ℝ) / c) ^ (-A) = (m : ℝ) ^ (-A) * (1 + δ / 3) := by
      rw [Real.div_rpow hm0.le (by linarith : (0 : ℝ) ≤ c), Real.rpow_neg
        (by linarith : (0 : ℝ) ≤ c), div_inv_eq_mul, hcA]
    rw [hcast]
    calc ((m : ℝ) - K) ^ (-A) ≤ ((m : ℝ) / c) ^ (-A) := hstep
      _ = (1 + δ / 3) * (m : ℝ) ^ (-A) := by rw [hdiv]; ring
  have hreg1w : ∀ k, k ≤ K → ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) ≤ ((m - K : ℕ) : ℝ) ^ (-A) :=
    fun k hk => Real.rpow_le_rpow_of_nonpos hmKpos
      (by exact_mod_cast (by omega : m - K ≤ max (m - k) 1)) (by linarith)
  have hb1 : ∑' k, g1 k ≤ (1 + δ / 3) * (m : ℝ) ^ (-A) := by
    have hle : ∀ k, g1 k ≤ (holdGeom F.p k).toReal * ((m - K : ℕ) : ℝ) ^ (-A) := fun k => by
      simp only [hg1def]; split_ifs with h
      · exact mul_le_mul_of_nonneg_left (hreg1w k h) (hp0 k)
      · exact mul_nonneg (hp0 k) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    calc ∑' k, g1 k
        ≤ ∑' k, (holdGeom F.p k).toReal * ((m - K : ℕ) : ℝ) ^ (-A) :=
          hg1sum.tsum_le_tsum hle (hpsum.mul_right _)
      _ = ((m - K : ℕ) : ℝ) ^ (-A) := by
          rw [tsum_mul_right, F.holdGeom_tsum_toReal, one_mul]
      _ ≤ (1 + δ / 3) * (m : ℝ) ^ (-A) := hW1
  -- middle zone
  have hreg2w : ∀ k, k ≤ m / 2 →
      ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) ≤ (2 : ℝ) ^ A * (m : ℝ) ^ (-A) := by
    intro k hk
    have hb : (m : ℝ) / 2 ≤ ((max (m - k) 1 : ℕ) : ℝ) := by
      have h2 : m ≤ 2 * max (m - k) 1 := by omega
      have h2' : (m : ℝ) ≤ 2 * ((max (m - k) 1 : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    have hstep : ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) ≤ ((m : ℝ) / 2) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hb (by linarith)
    have hdiv : ((m : ℝ) / 2) ^ (-A) = (2 : ℝ) ^ A * (m : ℝ) ^ (-A) := by
      rw [Real.div_rpow hm0.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg
        (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
      ring
    calc ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) ≤ ((m : ℝ) / 2) ^ (-A) := hstep
      _ = (2 : ℝ) ^ A * (m : ℝ) ^ (-A) := hdiv
  have htailsum : Summable (fun k => if K < k then (holdGeom F.p k).toReal else 0) :=
    Summable.of_nonneg_of_le
      (fun k => by split_ifs; exacts [hp0 k, le_rfl])
      (fun k => by split_ifs; exacts [le_rfl, hp0 k]) hpsum
  have hb2 : ∑' k, g2 k ≤ δ / 3 * (m : ℝ) ^ (-A) := by
    have hle : ∀ k, g2 k
        ≤ (if K < k then (holdGeom F.p k).toReal else 0)
          * ((2 : ℝ) ^ A * (m : ℝ) ^ (-A)) := by
      intro k
      simp only [hg2def]
      split_ifs with h1 h2
      · exact mul_le_mul_of_nonneg_left (hreg2w k h1.2) (hp0 k)
      · exact absurd h1.1 h2
      · exact mul_nonneg (hp0 k) (by positivity)
      · rw [zero_mul]
    calc ∑' k, g2 k
        ≤ ∑' k, (if K < k then (holdGeom F.p k).toReal else 0)
            * ((2 : ℝ) ^ A * (m : ℝ) ^ (-A)) :=
          hg2sum.tsum_le_tsum hle (htailsum.mul_right _)
      _ = ρ ^ K * ((2 : ℝ) ^ A * (m : ℝ) ^ (-A)) := by
          rw [tsum_mul_right, F.holdGeom_tail]
      _ ≤ δ / 3 * (2 : ℝ) ^ (-A) * ((2 : ℝ) ^ A * (m : ℝ) ^ (-A)) :=
          mul_le_mul_of_nonneg_right hK.le (by positivity)
      _ = δ / 3 * ((2 : ℝ) ^ (-A) * (2 : ℝ) ^ A) * (m : ℝ) ^ (-A) := by ring
      _ = δ / 3 * (m : ℝ) ^ (-A) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel,
            Real.rpow_zero, mul_one]
  -- tail zone
  have htail3 : ρ ^ (m / 2) ≤ δ / 3 * (m : ℝ) ^ (-A) := by
    have ht1 : 1 ≤ m / 2 := by omega
    have htT : T ≤ m / 2 := by omega
    have htpos : (1 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := by exact_mod_cast ht1
    have hhead := (hT (m / 2) htT).le
    have hm3t : (m : ℝ) ≤ 3 * ((m / 2 : ℕ) : ℝ) := by
      have h : m ≤ 3 * (m / 2) := by omega
      exact_mod_cast h
    have hcancel : ((m / 2 : ℕ) : ℝ) ^ (kA : ℝ) * ((m / 2 : ℕ) : ℝ) ^ (-(kA : ℝ)) = 1 := by
      rw [← Real.rpow_add (by linarith), add_neg_cancel, Real.rpow_zero]
    have h1 : ρ ^ (m / 2)
        = ((m / 2 : ℕ) : ℝ) ^ kA * ρ ^ (m / 2) * ((m / 2 : ℕ) : ℝ) ^ (-(kA : ℝ)) := by
      rw [mul_comm (((m / 2 : ℕ) : ℝ) ^ kA), mul_assoc, ← Real.rpow_natCast _ kA, hcancel,
        mul_one]
    have h2 : ρ ^ (m / 2)
        ≤ δ / 3 * (3 : ℝ) ^ (-A) * ((m / 2 : ℕ) : ℝ) ^ (-(kA : ℝ)) := by
      rw [h1]
      exact mul_le_mul_of_nonneg_right hhead (Real.rpow_nonneg (by linarith) _)
    have h3 : ((m / 2 : ℕ) : ℝ) ^ (-(kA : ℝ)) ≤ ((m / 2 : ℕ) : ℝ) ^ (-A) := by
      apply Real.rpow_le_rpow_of_exponent_le htpos
      have := Nat.le_ceil A
      rw [neg_le_neg_iff]
      exact_mod_cast this
    have h4 : (3 : ℝ) ^ (-A) * ((m / 2 : ℕ) : ℝ) ^ (-A) ≤ (m : ℝ) ^ (-A) := by
      rw [← Real.mul_rpow (by norm_num) (by linarith)]
      exact Real.rpow_le_rpow_of_nonpos hm0 hm3t (by linarith)
    calc ρ ^ (m / 2)
        ≤ δ / 3 * (3 : ℝ) ^ (-A) * ((m / 2 : ℕ) : ℝ) ^ (-(kA : ℝ)) := h2
      _ ≤ δ / 3 * (3 : ℝ) ^ (-A) * ((m / 2 : ℕ) : ℝ) ^ (-A) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = δ / 3 * ((3 : ℝ) ^ (-A) * ((m / 2 : ℕ) : ℝ) ^ (-A)) := by ring
      _ ≤ δ / 3 * (m : ℝ) ^ (-A) := mul_le_mul_of_nonneg_left h4 (by positivity)
  have htail2sum : Summable (fun k => if m / 2 < k then (holdGeom F.p k).toReal else 0) :=
    Summable.of_nonneg_of_le
      (fun k => by split_ifs; exacts [hp0 k, le_rfl])
      (fun k => by split_ifs; exacts [le_rfl, hp0 k]) hpsum
  have hb3 : ∑' k, g3 k ≤ δ / 3 * (m : ℝ) ^ (-A) := by
    have hle : ∀ k, g3 k ≤ (if m / 2 < k then (holdGeom F.p k).toReal else 0) := by
      intro k
      simp only [hg3def]
      split_ifs with h1 h2
      · exact hterm_le k
      · exact absurd h1.2 h2
      · exact hp0 k
      · exact le_rfl
    calc ∑' k, g3 k
        ≤ ∑' k, (if m / 2 < k then (holdGeom F.p k).toReal else 0) :=
          hg3sum.tsum_le_tsum hle htail2sum
      _ = ρ ^ (m / 2) := F.holdGeom_tail (m / 2)
      _ ≤ δ / 3 * (m : ℝ) ^ (-A) := htail3
  calc ∑' k : ℕ, (holdGeom F.p k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A)
      = ∑' k, g1 k + ∑' k, g2 k + ∑' k, g3 k := by
        rw [tsum_congr hsplit, (hg1sum.add hg2sum).tsum_add hg3sum, hg1sum.tsum_add hg2sum]
    _ ≤ (1 + δ / 3) * (m : ℝ) ^ (-A) + δ / 3 * (m : ℝ) ^ (-A) + δ / 3 * (m : ℝ) ^ (-A) :=
        add_le_add (add_le_add hb1 hb2) hb3
    _ = (1 + δ) * (m : ℝ) ^ (-A) := by ring

/-- **`hold_weight_expect`** (the leaf of tao-collatz's Case 1 on the geometric expectation; only the existence of the threshold):
for `δ > 0`, `A > 0`, if `m` is large then `E[max(m - 𝒥, 1)^{-A}] ≤ (1+δ) m^{-A}`. -/
theorem hold_weight_expect (A : ℝ) (hA : 0 < A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Cthr : ℕ, 1 ≤ Cthr ∧ ∀ m : ℕ, Cthr ≤ m →
      ∑' d : ℕ × ℤ, (F.hold d).toReal * ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A)
        ≤ (1 + δ) * (m : ℝ) ^ (-A) := by
  have hρ0 := F.holdRatio_nonneg
  have hρ1 := F.holdRatio_lt_one
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < δ / 3 * (2 : ℝ) ^ (-A) by positivity) hρ1
  obtain ⟨M1, hM1⟩ := exists_nat_ge
    ((K : ℝ) * (1 + δ / 3) ^ A⁻¹ / ((1 + δ / 3) ^ A⁻¹ - 1))
  have hlim := tendsto_pow_const_mul_const_pow_of_abs_lt_one ⌈A⌉₊
    (show |F.holdRatio| < 1 by rw [abs_of_nonneg hρ0]; exact hρ1)
  have hev := (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 3 * (3 : ℝ) ^ (-A) by
    positivity)))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨T, hT⟩ := hev
  exact ⟨K + M1 + 2 * T + 4, by omega,
    F.hold_weight_expect_core A hA δ hδ K M1 T hK hM1 (fun t ht => hT t ht)⟩

/-! ### Case 1 (white starting point) and the assembly of Proposition 7.8 -/

/-- **Case 1** (`Q_white_case1` of tao-collatz, (7.41)–(7.43)): at a white starting point at depth `m` from the edge,
`Q ≤ exp(-κ/2) m^{-A} Q_{m-1}` (for large `m`, with a threshold independent of `half` and `W`). -/
theorem Q_white_case1 {κ : ℝ} (hκ : 0 < κ) (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ, 1 ≤ Cthr ∧ ∀ (half : ℕ) (W : Set (ℕ × ℤ)) (m : ℕ), Cthr ≤ m → m ≤ half →
      ∀ l : ℤ, (half - m, l) ∈ W →
      F.Q half W κ (half - m) l
        ≤ Real.exp (-κ / 2) * (m : ℝ) ^ (-A) * F.Qm half W κ A (m - 1) := by
  have hδ : 0 < Real.exp (κ / 2) - 1 := by
    have h2 := Real.add_one_lt_exp (show κ / 2 ≠ 0 by positivity)
    linarith
  obtain ⟨C0, hC0one, hC0⟩ := F.hold_weight_expect A hA (Real.exp (κ / 2) - 1) hδ
  refine ⟨C0, hC0one, ?_⟩
  intro half W m hm hmn l hw
  have hκ0 : 0 ≤ κ := hκ.le
  have hm1 : 1 ≤ m := le_trans hC0one hm
  set QM := F.Qm half W κ A (m - 1) with hQMdef
  have hQM0 : 0 ≤ QM := F.Qm_nonneg _ _ _ _ _
  rw [F.Q_rec _ _ _ _ _ (Nat.sub_le _ _)]
  have hind : Set.indicator W (1 : ℕ × ℤ → ℝ) (half - m, l) = 1 :=
    Set.indicator_of_mem hw 1
  have hatom : ∀ d : ℕ × ℤ,
      (F.hold d).toReal * F.Q half W κ (half - m + d.1) (l + d.2)
        ≤ (F.hold d).toReal * (((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM) := by
    intro d
    rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
    · rw [F.hold_zero_of_fst_zero h0, ENNReal.toReal_zero, zero_mul, zero_mul]
    · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      have h1 : 1 ≤ half - m + d.1 := by omega
      have h2 : half - (m - 1) ≤ half - m + d.1 := by omega
      have hkey := F.Q_le_Qm half W hκ0 A hA.le (m - 1) (l := l + d.2) h1 h2
      have heq : half - (half - m + d.1) = m - d.1 := by omega
      rwa [heq] at hkey
  have hble : ∀ d : ℕ × ℤ,
      (F.hold d).toReal * (((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM)
        ≤ (F.hold d).toReal * QM := by
    intro d
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    calc ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM
        ≤ 1 * QM := mul_le_mul_of_nonneg_right
          (Real.rpow_le_one_of_one_le_of_nonpos
            (by exact_mod_cast Nat.le_max_right (m - d.1) 1) (by linarith)) hQM0
      _ = QM := one_mul _
  have hsumR : Summable fun d : ℕ × ℤ =>
      (F.hold d).toReal * (((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM) :=
    Summable.of_nonneg_of_le
      (fun d => mul_nonneg ENNReal.toReal_nonneg
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hQM0))
      hble (F.hold_summable_toReal.mul_right QM)
  have hsumL : Summable fun d : ℕ × ℤ =>
      (F.hold d).toReal * F.Q half W κ (half - m + d.1) (l + d.2) :=
    Summable.of_nonneg_of_le
      (fun d => mul_nonneg ENNReal.toReal_nonneg (F.Q_nonneg _ _ _ _ _))
      (fun d => (hatom d).trans (hble d)) (F.hold_summable_toReal.mul_right QM)
  have hE : 1 + (Real.exp (κ / 2) - 1) = Real.exp (κ / 2) := by ring
  have htsum : ∑' d : ℕ × ℤ,
      (F.hold d).toReal * F.Q half W κ (half - m + d.1) (l + d.2)
        ≤ Real.exp (κ / 2) * (m : ℝ) ^ (-A) * QM := by
    calc ∑' d : ℕ × ℤ, (F.hold d).toReal * F.Q half W κ (half - m + d.1) (l + d.2)
        ≤ ∑' d : ℕ × ℤ, (F.hold d).toReal * (((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM) :=
          hsumL.tsum_le_tsum hatom hsumR
      _ = ∑' d : ℕ × ℤ, ((F.hold d).toReal * ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A)) * QM :=
          tsum_congr fun d => (mul_assoc _ _ _).symm
      _ = (∑' d : ℕ × ℤ, (F.hold d).toReal * ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A)) * QM :=
          tsum_mul_right
      _ ≤ Real.exp (κ / 2) * (m : ℝ) ^ (-A) * QM := by
          apply mul_le_mul_of_nonneg_right _ hQM0
          have := hC0 m hm
          rwa [hE] at this
  rw [hind, mul_one]
  calc Real.exp (-κ) *
        ∑' d : ℕ × ℤ, (F.hold d).toReal * F.Q half W κ (half - m + d.1) (l + d.2)
      ≤ Real.exp (-κ) * (Real.exp (κ / 2) * (m : ℝ) ^ (-A) * QM) :=
        mul_le_mul_of_nonneg_left htsum (Real.exp_pos _).le
    _ = (Real.exp (-κ) * Real.exp (κ / 2)) * ((m : ℝ) ^ (-A) * QM) := by ring
    _ = Real.exp (-κ / 2) * ((m : ℝ) ^ (-A) * QM) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
    _ = Real.exp (-κ / 2) * (m : ℝ) ^ (-A) * QM := by ring

/-- **Assembly of Proposition 7.8** (`prop_7_8_at` of tao-collatz): from the Case 1 threshold `C1` and the threshold `C2` of the
bounds at black edges, `Q_m ≤ Q_{m-1}` for `max (max C1 C2) 1 ≤ m ≤ half`. -/
theorem prop_7_8_of (half : ℕ) (W : Set (ℕ × ℤ)) {κ : ℝ} (hκ : 0 ≤ κ) (A : ℝ) (hA : 0 < A)
    (C1 C2 : ℕ)
    (hC1 : ∀ m : ℕ, C1 ≤ m → m ≤ half → ∀ l : ℤ, (half - m, l) ∈ W →
      F.Q half W κ (half - m) l
        ≤ Real.exp (-κ / 2) * (m : ℝ) ^ (-A) * F.Qm half W κ A (m - 1))
    (hC2 : ∀ m : ℕ, C2 ≤ m → m ≤ half → ∀ l : ℤ, 1 ≤ half - m → (half - m, l) ∉ W →
      F.Q half W κ (half - m) l ≤ (m : ℝ) ^ (-A) * F.Qm half W κ A (m - 1)) :
    ∀ m : ℕ, max (max C1 C2) 1 ≤ m → m ≤ half →
      F.Qm half W κ A m ≤ F.Qm half W κ A (m - 1) := by
  intro m hm hmn
  have hmC1 : C1 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hmC2 : C2 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hQM0 : 0 ≤ F.Qm half W κ A (m - 1) := F.Qm_nonneg _ _ _ _ _
  have hcancel : (m : ℝ) ^ A * (m : ℝ) ^ (-A) = 1 := by
    rw [← Real.rpow_add hm0, add_neg_cancel, Real.rpow_zero]
  refine Real.iSup_le (fun x => ?_) hQM0
  obtain ⟨⟨p1, l⟩, hp1, hpm⟩ := x
  have hp1' : 1 ≤ p1 := hp1
  have hpm' : half - m ≤ p1 := hpm
  show ((max (half - p1) 1 : ℕ) : ℝ) ^ A * F.Q half W κ p1 l ≤ F.Qm half W κ A (m - 1)
  rcases eq_or_lt_of_le hpm' with heq | hlt
  · have hp1eq : p1 = half - m := heq.symm
    have hwt : (max (half - p1) 1 : ℕ) = m := by omega
    have hedge : F.Q half W κ p1 l ≤ (m : ℝ) ^ (-A) * F.Qm half W κ A (m - 1) := by
      by_cases hw : (p1, l) ∈ W
      · have h := hC1 m hmC1 hmn l (hp1eq ▸ hw)
        rw [hp1eq]
        calc F.Q half W κ (half - m) l
            ≤ Real.exp (-κ / 2) * (m : ℝ) ^ (-A) * F.Qm half W κ A (m - 1) := h
          _ ≤ (m : ℝ) ^ (-A) * F.Qm half W κ A (m - 1) := by
              apply mul_le_mul_of_nonneg_right _ hQM0
              have hexp : Real.exp (-κ / 2) ≤ 1 := by
                rw [Real.exp_le_one_iff]; linarith
              calc Real.exp (-κ / 2) * (m : ℝ) ^ (-A)
                  ≤ 1 * (m : ℝ) ^ (-A) :=
                    mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg hm0.le _)
                _ = (m : ℝ) ^ (-A) := one_mul _
      · exact hp1eq ▸ hC2 m hmC2 hmn l (by omega) (hp1eq ▸ hw)
    calc ((max (half - p1) 1 : ℕ) : ℝ) ^ A * F.Q half W κ p1 l
        ≤ ((max (half - p1) 1 : ℕ) : ℝ) ^ A
            * ((m : ℝ) ^ (-A) * F.Qm half W κ A (m - 1)) :=
          mul_le_mul_of_nonneg_left hedge (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = (m : ℝ) ^ A * (m : ℝ) ^ (-A) * F.Qm half W κ A (m - 1) := by
          rw [hwt]; ring
      _ = F.Qm half W κ A (m - 1) := by rw [hcancel, one_mul]
  · exact F.le_Qm half W hκ A hA.le (m - 1) hp1 (by omega)

/-- **(7.37)** (`Q_polynomial_decay_at` of tao-collatz): if Proposition 7.8 holds with threshold `C0`, then
`Q(j,l) ≤ (max C0 1)^A max(half - j, 1)^{-A}` (`j ≥ 1`). -/
theorem Q_polynomial_decay_of (half : ℕ) (W : Set (ℕ × ℤ)) {κ : ℝ} (hκ : 0 ≤ κ)
    (A : ℝ) (hA : 0 < A) (C0 : ℕ)
    (hC0 : ∀ m : ℕ, C0 ≤ m → m ≤ half → F.Qm half W κ A m ≤ F.Qm half W κ A (m - 1)) :
    ∀ (j : ℕ) (l : ℤ), 1 ≤ j →
      F.Q half W κ j l ≤ ((max C0 1 : ℕ) : ℝ) ^ A * ((max (half - j) 1 : ℕ) : ℝ) ^ (-A) := by
  set Cb := max C0 1 with hCbdef
  have hCb1 : 1 ≤ Cb := le_max_right _ _
  have hCbR : (1 : ℝ) ≤ ((Cb : ℕ) : ℝ) := by exact_mod_cast hCb1
  have hCbA1 : (1 : ℝ) ≤ ((Cb : ℕ) : ℝ) ^ A := by
    calc (1 : ℝ) = (1 : ℝ) ^ A := (Real.one_rpow A).symm
      _ ≤ ((Cb : ℕ) : ℝ) ^ A := Real.rpow_le_rpow zero_le_one hCbR hA.le
  intro j l hj
  have hQmb : ∀ m : ℕ, 1 ≤ m → m ≤ half → F.Qm half W κ A m ≤ ((Cb : ℕ) : ℝ) ^ A := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IH =>
      intro hm1 hmn
      rcases le_or_gt m Cb with hle | hgt
      · calc F.Qm half W κ A m ≤ (m : ℝ) ^ A := F.Qm_le_rpow _ _ hκ _ hA.le _ hm1
          _ ≤ ((Cb : ℕ) : ℝ) ^ A :=
              Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hle) hA.le
      · have h78 := hC0 m (by omega) hmn
        exact le_trans h78 (IH (m - 1) (by omega) (by omega) (by omega))
  rcases Nat.lt_or_ge j half with hjlt | hjge
  · have hle := F.Q_le_Qm half W hκ A hA.le (half - j) (l := l) hj (by omega)
    calc F.Q half W κ j l
        ≤ ((max (half - j) 1 : ℕ) : ℝ) ^ (-A) * F.Qm half W κ A (half - j) := hle
      _ ≤ ((max (half - j) 1 : ℕ) : ℝ) ^ (-A) * (((Cb : ℕ) : ℝ) ^ A) :=
          mul_le_mul_of_nonneg_left (hQmb (half - j) (by omega) (by omega))
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = ((Cb : ℕ) : ℝ) ^ A * ((max (half - j) 1 : ℕ) : ℝ) ^ (-A) := mul_comm _ _
  · have hw : (max (half - j) 1 : ℕ) = 1 := by omega
    calc F.Q half W κ j l ≤ 1 := F.Q_le_one _ _ _ hκ _ _
      _ ≤ ((Cb : ℕ) : ℝ) ^ A := hCbA1
      _ = ((Cb : ℕ) : ℝ) ^ A * ((max (half - j) 1 : ℕ) : ℝ) ^ (-A) := by
          rw [hw, Nat.cast_one, Real.one_rpow, mul_one]

end Family

end GGMCollatz
