import GGMCollatz.Tao.Sec7.FW79
import GGMCollatz.Tao.Sec7.FWDet
import GGMCollatz.Tao.Sec7.FW710
import GGMCollatz.Tao.Sec7.ColTail

/-!
# GGM §7: the mass of walks with few white points ((7.56) of tao-collatz, `few_white_mass_le`)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/Case3.lean`
(`few_white_pointwise_split`, `few_white_reach_mass_le`, `few_white_estar_mass_le`,
`few_white_mass_le_core`); generalized to the GGM family (p, q, r). Modified.

A walk with `≤ K` white points lies, pointwise, in one of three events (`few_white_pointwise_split`):
(1) the encounter convolution has `R` encounters and `cumWhite ≤ K+1` (Lemma 7.9 and Markov, `reach_mass_le`),
(2) at some time `p ≤ P` it enters a triangle of size `≥ ⌊4^A(1+p)³⌋` (the sum of Lemma 7.10, `estar_union_le`),
(3) a bad column `e₁ + (pathSum v P)₁ ≥ colFrac · m` (`col_tail_mass_le`, `ColTail.lean`).
On good columns the depth `≥ g` is preserved, and the deterministic statement (`FWDet.lean`) gives (1) or (2). Each of the three masses is made `η/3`.
The threshold `0.9m` of tao-collatz became `colFrac · m`, and the depth-gate condition `g ≤ 0.1m` became `g ≤ (1 - colFrac) m`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

namespace FW

variable (F : Family)

/-! ### Numerical lemmas -/

/-- Deep-triangle condition: for `m ≥ 800^{10}`, `m / log² m < s` implies `(m+1)^{0.8} < s`. -/
theorem deep_of_large (m : ℕ) (hm : 800 ^ 10 ≤ m) (s : ℕ)
    (hs : (m : ℝ) / Real.log m ^ 2 < (s : ℝ)) :
    ((m + 1 : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) := by
  set x : ℝ := (m : ℝ) with hx
  have hx8 : (800 : ℝ) ^ 10 ≤ x := by rw [hx]; exact_mod_cast hm
  have hx2 : (2 : ℝ) ≤ x := le_trans (by norm_num) hx8
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hL : Real.log x ≤ 20 * x ^ (0.05 : ℝ) := by
    have h := Real.log_le_rpow_div hx0.le (show (0 : ℝ) < 0.05 by norm_num)
    have : x ^ (0.05 : ℝ) / 0.05 = 20 * x ^ (0.05 : ℝ) := by ring
    linarith
  have hL2 : Real.log x ^ 2 ≤ 400 * x ^ (0.1 : ℝ) := by
    have h1 : Real.log x ^ 2 ≤ (20 * x ^ (0.05 : ℝ)) ^ 2 := by
      exact pow_le_pow_left₀ hlog.le hL 2
    have h2 : (20 * x ^ (0.05 : ℝ)) ^ 2 = 400 * x ^ (0.1 : ℝ) := by
      rw [mul_pow, ← Real.rpow_natCast (x ^ (0.05 : ℝ)) 2, ← Real.rpow_mul hx0.le]
      norm_num
    linarith
  have hcast : ((m + 1 : ℕ) : ℝ) = x + 1 := by rw [hx]; push_cast; ring
  have h81 : (x + 1) ^ (0.8 : ℝ) ≤ 2 * x ^ (0.8 : ℝ) := by
    have h1 : (x + 1) ^ (0.8 : ℝ) ≤ (2 * x) ^ (0.8 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    have h2 : (2 * x) ^ (0.8 : ℝ) = (2 : ℝ) ^ (0.8 : ℝ) * x ^ (0.8 : ℝ) :=
      Real.mul_rpow (by norm_num) hx0.le
    have h3 : (2 : ℝ) ^ (0.8 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (0.8 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have h4 : 0 ≤ x ^ (0.8 : ℝ) := Real.rpow_nonneg hx0.le _
    nlinarith
  have h01 : (800 : ℝ) ≤ x ^ (0.1 : ℝ) := by
    have h1 : ((800 : ℝ) ^ 10) ^ (0.1 : ℝ) ≤ x ^ (0.1 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hx8 (by norm_num)
    have h2 : ((800 : ℝ) ^ 10) ^ (0.1 : ℝ) = 800 := by
      rw [← Real.rpow_natCast (800 : ℝ) 10, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  have hsplit : x = x ^ (0.1 : ℝ) * x ^ (0.9 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  have hprod : (x + 1) ^ (0.8 : ℝ) * Real.log x ^ 2 ≤ x := by
    have h09 : x ^ (0.8 : ℝ) * x ^ (0.1 : ℝ) = x ^ (0.9 : ℝ) := by
      rw [← Real.rpow_add hx0]; norm_num
    have hA : 0 ≤ x ^ (0.8 : ℝ) := Real.rpow_nonneg hx0.le _
    have hB : 0 ≤ x ^ (0.1 : ℝ) := Real.rpow_nonneg hx0.le _
    have hC : 0 ≤ x ^ (0.9 : ℝ) := Real.rpow_nonneg hx0.le _
    calc (x + 1) ^ (0.8 : ℝ) * Real.log x ^ 2
        ≤ (2 * x ^ (0.8 : ℝ)) * (400 * x ^ (0.1 : ℝ)) :=
          mul_le_mul h81 hL2 (sq_nonneg _) (by positivity)
      _ = 800 * x ^ (0.9 : ℝ) := by rw [← h09]; ring
      _ ≤ x ^ (0.1 : ℝ) * x ^ (0.9 : ℝ) := mul_le_mul_of_nonneg_right h01 hC
      _ = x := hsplit.symm
  have hlog2 : 0 < Real.log x ^ 2 := by positivity
  rw [hcast]
  have : (x + 1) ^ (0.8 : ℝ) ≤ x / Real.log x ^ 2 := by
    rw [le_div_iff₀ hlog2]; exact hprod
  linarith

/-- Regime condition: `X^{2.5} ≤ m` implies `X ≤ (m+1)^{0.4}`. -/
theorem reg_of_large {X : ℝ} (hX : 0 ≤ X) (m : ℕ) (hm : X ^ (2.5 : ℝ) ≤ (m : ℝ)) :
    X ≤ ((m + 1 : ℕ) : ℝ) ^ (0.4 : ℝ) := by
  have h1 : (X ^ (2.5 : ℝ)) ^ (0.4 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ (0.4 : ℝ) := by
    apply Real.rpow_le_rpow (Real.rpow_nonneg hX _) _ (by norm_num)
    have : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
    linarith
  have h2 : (X ^ (2.5 : ℝ)) ^ (0.4 : ℝ) = X := by
    rw [← Real.rpow_mul hX]; norm_num
  linarith

/-! ### Pointwise three-way split -/

open Classical in
/-- **Pointwise three-way split** (`few_white_pointwise_split` of tao-collatz). -/
theorem few_white_pointwise_split {half : ℕ} {σ : ℝ} (T : F.TriFam half σ)
    (m : ℕ) (hmn : m ≤ half) (hpos : 1 ≤ half - m) (l : ℤ)
    (g R K : ℕ) (A : ℝ) (hA : 1 ≤ A) (P : ℕ) (hP : encWindowIter A (K + 1) R ≤ P)
    (hg : (g : ℝ) ≤ (1 - F.colFrac) * (m : ℝ))
    (e : ℕ × ℤ) (v : Fin P → ℕ × ℤ) (hv : ∀ i, v i ∈ F.hold.support) :
    ENNReal.ofReal (if (∑ p ∈ Finset.range P,
          Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
            (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) ≤ (K : ℝ)
      then (1 : ℝ) else 0)
    ≤ ENNReal.ofReal (if R ≤ ((List.ofFn v).foldl (encStep F T R g)
            (encInit (half - m + e.1) (l + e.2))).count
          ∧ ((List.ofFn v).foldl (encStep F T R g)
            (encInit (half - m + e.1) (l + e.2))).cumWhite ≤ K + 1
        then (1 : ℝ) else 0)
      + (∑ p ∈ Finset.range (P + 1),
          Set.indicator (bigTriSet F T ⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊)
            (1 : ℕ × ℤ → ℝ≥0∞)
            (half - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))
      + ENNReal.ofReal (if F.colFrac * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
          then (1 : ℝ) else 0) := by
  set q₀ : ℕ × ℤ := (half - m + e.1, l + e.2) with hq₀def
  have hq1 : q₀.1 = half - m + e.1 := rfl
  set Nw : ℝ := ∑ p ∈ Finset.range P,
      Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
        (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) with hNwdef
  set T1 : ℝ≥0∞ := ENNReal.ofReal (if R ≤ ((List.ofFn v).foldl (encStep F T R g)
        (encInit (half - m + e.1) (l + e.2))).count
      ∧ ((List.ofFn v).foldl (encStep F T R g)
        (encInit (half - m + e.1) (l + e.2))).cumWhite ≤ K + 1 then (1 : ℝ) else 0) with hT1def
  set T2 : ℝ≥0∞ := ∑ p ∈ Finset.range (P + 1),
      Set.indicator (bigTriSet F T ⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊)
        (1 : ℕ × ℤ → ℝ≥0∞)
        (half - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) with hT2def
  set T3 : ℝ≥0∞ := ENNReal.ofReal (if F.colFrac * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
      then (1 : ℝ) else 0) with hT3def
  by_cases hfew : Nw ≤ (K : ℝ)
  · rw [if_pos hfew, ENNReal.ofReal_one]
    by_cases hcol : F.colFrac * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
    · have hT3one : T3 = 1 := by rw [hT3def, if_pos hcol, ENNReal.ofReal_one]
      calc (1 : ℝ≥0∞) = T3 := hT3one.symm
        _ ≤ T1 + T2 + T3 := self_le_add_left _ _
    · have hset : T.W ∩ {q : ℕ × ℤ | q.1 ≤ half} = whiteStrip half T.W := by
        ext q; simp only [whiteStrip, Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto
      have hcast : Nw = ((∑ p ∈ Finset.range P,
              (if q₀ + pathSum v p ∈ whiteStrip half T.W then (1 : ℕ) else 0) : ℕ) : ℝ) := by
        rw [hNwdef, Nat.cast_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        have hpt : (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)
            = q₀ + pathSum v p := rfl
        rw [hpt, hset, Set.indicator_apply, Pi.one_apply, Nat.cast_ite, Nat.cast_one,
          Nat.cast_zero]
      have hNatK : (∑ p ∈ Finset.range P,
          (if q₀ + pathSum v p ∈ whiteStrip half T.W then (1 : ℕ) else 0)) ≤ K := by
        have h := hfew; rw [hcast] at h; exact_mod_cast h
      have hadv : (e.1 + (pathSum v P).1 : ℕ) + g ≤ m := by
        have hlt : ((e.1 + (pathSum v P).1 : ℕ) : ℝ) < F.colFrac * (m : ℝ) := not_le.mp hcol
        have hsum : ((e.1 + (pathSum v P).1 : ℕ) : ℝ) + (g : ℝ) ≤ (m : ℝ) := by
          nlinarith [hlt, hg]
        exact_mod_cast hsum
      have hqone : 1 ≤ q₀.1 := by rw [hq1]; omega
      have hendpt : q₀.1 + (pathSum v P).1 + g ≤ half := by rw [hq1]; omega
      have hdepth : ∀ p, p ≤ P → (q₀ + pathSum v p).1 + g ≤ half :=
        pathSum_depth_le v q₀ g half hendpt
      have hdich := few_white_pointwise_dichotomy F T g R K A hA P hP q₀ hqone v hv hdepth hNatK
      rcases hdich with ⟨hreach, hcw⟩ | ⟨p, hp, t, ht, hmem, hbig⟩
      · have hT1one : T1 = 1 := by
          rw [hT1def, if_pos ⟨hreach, hcw⟩, ENNReal.ofReal_one]
        calc (1 : ℝ≥0∞) = T1 := hT1one.symm
          _ ≤ T1 + T2 := self_le_add_right _ _
          _ ≤ T1 + T2 + T3 := self_le_add_right _ _
      · have hpt : ((q₀ + pathSum v p).1 - 1, (q₀ + pathSum v p).2)
            = (half - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) := by
          have h1 : (q₀ + pathSum v p).1 = half - m + e.1 + (pathSum v p).1 := rfl
          have h2 : (q₀ + pathSum v p).2 = l + e.2 + (pathSum v p).2 := rfl
          refine Prod.ext_iff.mpr ⟨?_, h2⟩
          rw [h1]; omega
        have hbigmem : (half - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)
            ∈ bigTriSet F T ⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊ := by
          rw [← hpt]
          refine ⟨t, ht, ?_, hmem⟩
          calc ((⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
              ≤ (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 := Nat.floor_le (by positivity)
            _ ≤ t.2.2 := hbig
        have hone : Set.indicator (bigTriSet F T ⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊)
            (1 : ℕ × ℤ → ℝ≥0∞)
            (half - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) = 1 := by
          rw [Set.indicator_of_mem hbigmem]; rfl
        have hT2ge : (1 : ℝ≥0∞) ≤ T2 := by
          have hsingle := Finset.single_le_sum (f := fun p : ℕ =>
            Set.indicator (bigTriSet F T ⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊)
              (1 : ℕ × ℤ → ℝ≥0∞)
              (half - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))
            (fun i _ => zero_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hp))
          rw [hone] at hsingle
          rw [hT2def]; exact hsingle
        calc (1 : ℝ≥0∞) ≤ T2 := hT2ge
          _ ≤ T1 + T2 := self_le_add_left _ _
          _ ≤ T1 + T2 + T3 := self_le_add_right _ _
  · rw [if_neg hfew, ENNReal.ofReal_zero]
    exact zero_le

/-! ### The mass of walks with few white points -/

open Classical in
/-- **The mass of walks with few white points** (`few_white_mass_le` of tao-collatz, (7.56)): for every `K` and `η > 0` there are
`P` and a threshold such that, from the starting point of a black edge of a deep triangle, the mass of walks with `≤ K` white points during the first passage and the following `P` steps is
`≤ η`. -/
theorem few_white_mass_le :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ (K : ℕ) (η : ℝ), 0 < η →
      ∃ P Cthr : ℕ, ∀ (half : ℕ) (T : F.TriFam half (F.sep ε)) (m : ℕ), Cthr ≤ m → m ≤ half →
        ∀ l : ℤ, 1 ≤ half - m → ∀ t ∈ T.T, (half - m - 1, l) ∈ F.triangle t.1 t.2.1 t.2.2 →
        ∀ s : ℕ, (s : ℤ) = t.2.1 - l → (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
        (s : ℝ) * Real.log F.p ≤ ((m : ℝ) + 2) * Real.log ((F.q : ℝ) ^ 2) →
        (∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
          ENNReal.ofReal (if (∑ p ∈ Finset.range P,
                Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                  (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) ≤ (K : ℝ)
            then (1 : ℝ) else 0))
          ≤ ENNReal.ofReal η := by
  obtain ⟨ε₁, hε₁, hMT⟩ := many_triangles_white F
  obtain ⟨ε₂, hε₂, hES⟩ := estar_union_le F
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro ε hε hεle K η hη
  obtain ⟨g, hMTg⟩ := hMT ε hε (le_trans hεle (min_le_left _ _))
  set κ : ℝ := 1 / 100 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; norm_num
  -- `R`: make the Markov term at most `η/3`
  set R : ℕ := ⌈(2 * κ + ((K : ℝ) + 1) - Real.log (η / 3)) / κ⌉₊ + 1 with hRdef
  have hR1 : 1 ≤ R := by omega
  have hRbound : Real.exp (2 * κ) * Real.exp (((K + 1 : ℕ) : ℝ) - κ * R) ≤ η / 3 := by
    rw [← Real.exp_add]
    have hceil : (2 * κ + ((K : ℝ) + 1) - Real.log (η / 3)) / κ ≤ (R : ℝ) := by
      have := Nat.le_ceil ((2 * κ + ((K : ℝ) + 1) - Real.log (η / 3)) / κ)
      have h2 : (⌈(2 * κ + ((K : ℝ) + 1) - Real.log (η / 3)) / κ⌉₊ : ℝ) ≤ (R : ℝ) := by
        rw [hRdef]; push_cast; linarith
      linarith
    rw [div_le_iff₀ hκ0] at hceil
    have hexp : 2 * κ + (((K + 1 : ℕ) : ℝ) - κ * R) ≤ Real.log (η / 3) := by
      push_cast; nlinarith
    calc Real.exp (2 * κ + (((K + 1 : ℕ) : ℝ) - κ * R)) ≤ Real.exp (Real.log (η / 3)) :=
          Real.exp_le_exp.mpr hexp
      _ = η / 3 := Real.exp_log (by positivity)
  -- `A`: make the E∗ term at most `η/3`
  obtain ⟨A, hA1, hEA⟩ := hES ε hε (le_trans hεle (min_le_right _ _)) (η / 3) (by positivity)
  set P : ℕ := encWindowIter A (K + 1) R with hPdef
  obtain ⟨Cct, hCct⟩ := F.col_tail_mass_le 1 one_pos P
  set Cthr : ℕ := max (max Cct (⌈3 / (2 * η)⌉₊ + 1))
    (max (max ⌈(g : ℝ) / (1 - F.colFrac)⌉₊ (800 ^ 10))
      ⌈((4 : ℝ) ^ A * (1 + (P : ℝ)) ^ 3) ^ (2.5 : ℝ)⌉₊) with hCthr
  refine ⟨P, Cthr, ?_⟩
  intro half T m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hmCct : Cct ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hmη : ⌈3 / (2 * η)⌉₊ + 1 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hmg : ⌈(g : ℝ) / (1 - F.colFrac)⌉₊ ≤ m :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hm
  have hm800 : 800 ^ 10 ≤ m :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hm
  have hmreg : ⌈((4 : ℝ) ^ A * (1 + (P : ℝ)) ^ 3) ^ (2.5 : ℝ)⌉₊ ≤ m :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : 1 ≤ m := le_trans (by norm_num) hm800
    exact_mod_cast this
  -- the depth-gate condition `g ≤ (1 - colFrac) m`
  have hc0 : 0 < 1 - F.colFrac := by have := F.colFrac_lt_one; linarith
  have hg : (g : ℝ) ≤ (1 - F.colFrac) * (m : ℝ) := by
    have h1 : (g : ℝ) / (1 - F.colFrac) ≤ (m : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hmg)
    rw [div_le_iff₀ hc0] at h1
    linarith
  -- integrate the pointwise three-way split
  set T1 : ℕ × ℤ → (Fin P → ℕ × ℤ) → ℝ≥0∞ := fun e v =>
    ENNReal.ofReal (if R ≤ ((List.ofFn v).foldl (encStep F T R g)
          (encInit (half - m + e.1) (l + e.2))).count
        ∧ ((List.ofFn v).foldl (encStep F T R g)
          (encInit (half - m + e.1) (l + e.2))).cumWhite ≤ K + 1
      then (1 : ℝ) else 0) with hT1def
  set T2 : ℕ × ℤ → (Fin P → ℕ × ℤ) → ℝ≥0∞ := fun e v =>
    ∑ p ∈ Finset.range (P + 1),
      Set.indicator (bigTriSet F T ⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊)
        (1 : ℕ × ℤ → ℝ≥0∞)
        (half - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) with hT2def
  set T3 : ℕ × ℤ → (Fin P → ℕ × ℤ) → ℝ≥0∞ := fun e v =>
    ENNReal.ofReal (if F.colFrac * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
      then (1 : ℝ) else 0) with hT3def
  have hpt : ∀ (e : ℕ × ℤ) (v : Fin P → ℕ × ℤ),
      F.hold.iid P v * ENNReal.ofReal (if (∑ p ∈ Finset.range P,
          Set.indicator (T.W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
            (half - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) ≤ (K : ℝ)
        then (1 : ℝ) else 0)
        ≤ F.hold.iid P v * (T1 e v + T2 e v + T3 e v) := by
    intro e v
    by_cases hv0 : F.hold.iid P v = 0
    · rw [hv0, zero_mul, zero_mul]
    · refine mul_le_mul_right ?_ _
      have hvs : ∀ i, v i ∈ F.hold.support :=
        PMF.iid_support_coord F.hold P v ((PMF.mem_support_iff _ _).mpr hv0)
      exact few_white_pointwise_split F T m hmn hpos l g R K A hA1 P le_rfl hg e v hvs
  refine le_trans (ENNReal.tsum_le_tsum fun e => mul_le_mul_right
    (ENNReal.tsum_le_tsum fun v => hpt e v) _) ?_
  simp only [mul_add, ENNReal.tsum_add]
  -- (1) the reaching term
  have hS1 : ∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v * T1 e v
      ≤ ENNReal.ofReal (η / 3) := by
    have hin : ∀ e : ℕ × ℤ, ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v * T1 e v
        ≤ ENNReal.ofReal (η / 3) := by
      intro e
      have hb := hMTg κ hκ0 (by rw [hκ]) half T R hR1 P (half - m + e.1) (l + e.2)
      have hr := reach_mass_le F T R g (K + 1) κ hκ0.le P (half - m + e.1, l + e.2) hb
      exact le_trans hr (ENNReal.ofReal_le_ofReal hRbound)
    calc ∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v * T1 e v
        ≤ ∑' e : ℕ × ℤ, F.fpDist s e * ENNReal.ofReal (η / 3) :=
          ENNReal.tsum_le_tsum fun e => mul_le_mul_right (hin e) _
      _ = ENNReal.ofReal (η / 3) := by rw [ENNReal.tsum_mul_right, (F.fpDist s).tsum_coe, one_mul]
  -- (2) the E∗ term
  have hS2 : ∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v * T2 e v
      ≤ ENNReal.ofReal (η / 3) := by
    have hswap : ∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v * T2 e v
        = ∑ p ∈ Finset.range (P + 1), ∑' e : ℕ × ℤ, F.fpDist s e *
            ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v *
              Set.indicator (bigTriSet F T ⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊)
                (1 : ℕ × ℤ → ℝ≥0∞)
                (half - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) := by
      simp only [hT2def, Finset.mul_sum]
      rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
      refine tsum_congr fun e => ?_
      rw [Summable.tsum_finsetSum (fun i _ => ENNReal.summable), Finset.mul_sum]
    rw [hswap]
    have hj : half - (half - m - 1) = m + 1 := by omega
    have hdeep : ((half - (half - m - 1) : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) := by
      rw [hj]; exact deep_of_large m hm800 s hs1
    have hreg : ∀ p, p ≤ P →
        ((⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
          ≤ ((half - (half - m - 1) : ℕ) : ℝ) ^ (0.4 : ℝ) := by
      intro p hp
      rw [hj]
      have hX0 : (0 : ℝ) ≤ (4 : ℝ) ^ A * (1 + (P : ℝ)) ^ 3 := by positivity
      have hXm : ((4 : ℝ) ^ A * (1 + (P : ℝ)) ^ 3) ^ (2.5 : ℝ) ≤ (m : ℝ) :=
        le_trans (Nat.le_ceil _) (by exact_mod_cast hmreg)
      have h1 := reg_of_large hX0 m hXm
      calc ((⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
          ≤ (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 := Nat.floor_le (by positivity)
        _ ≤ (4 : ℝ) ^ A * (1 + (P : ℝ)) ^ 3 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have : (p : ℝ) ≤ (P : ℝ) := by exact_mod_cast hp
            exact pow_le_pow_left₀ (by positivity) (by linarith) 3
        _ ≤ _ := h1
    have hjl : (half - m - 1, l) ∈ F.triangle t.1 t.2.1 t.2.2 := hmem
    exact hEA half T t ht (half - m - 1) l hjl s hs hdeep P hreg
  -- (3) the bad-column term
  have hS3 : ∑' e : ℕ × ℤ, F.fpDist s e * ∑' v : Fin P → ℕ × ℤ, F.hold.iid P v * T3 e v
      ≤ ENNReal.ofReal (η / 3) := by
    refine le_trans (hCct m hmCct s hs2) (ENNReal.ofReal_le_ofReal ?_)
    have hmη' : 3 / (2 * η) ≤ (m : ℝ) := by
      have h1 : 3 / (2 * η) ≤ (⌈3 / (2 * η)⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈3 / (2 * η)⌉₊ : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : ⌈3 / (2 * η)⌉₊ ≤ m)
      linarith
    rw [Real.rpow_neg_one]
    have : (m : ℝ)⁻¹ ≤ 2 * η / 3 := by
      rw [inv_le_comm₀ hmR (by positivity), inv_div]
      exact hmη'
    linarith
  calc _ ≤ ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) :=
        add_le_add (add_le_add hS1 hS2) hS3
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end FW

end Family

end GGMCollatz
