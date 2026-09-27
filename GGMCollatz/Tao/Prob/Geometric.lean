import GGMCollatz.Tao.Prob.Basic

/-!
# Geometric distribution, Pascal distribution, negative binomial (counterpart of node S2 of tao-collatz)

Derived from `TaoCollatz/Prob/Geometric.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2;
generalized to the GGM family (p, q, r). Notation of GGM (arXiv:2111.06170) §2.1; §3, §4, §7.

* `geomP p`: `G(μ)` (`μ = p/(p-1)`): `P(k) = (p-1) p^{-k}` (`k ≥ 1`). tao-collatz's `geomHalf` is `p = 2`.
* `pascalP p`: `P(μ) = G(μ) + G(μ)` (sum of two independent copies): `P(b) = (b-1)(p-1)² p^{-b}` (`b ≥ 2`).
* `pascalNe3P p`: Pascal conditioned to avoid `b = 3` (the grouping of GGM §7; tao-collatz's `pascalNe3`).
* `geomS s`: the geometric distribution with success probability `s`, `P(k) = s(1-s)^{k-1}`.
  `holdGeom p = geomS (P(P = 3))` is the law of `J` in GGM §7 (the first time with `P_J = 3`, `J ≡ G(λ)`,
  `λ = p³/(2(p-1)²)`) (tao-collatz's `geomQuarter`).
* `negBinomial_apply`: `P(G_1 + ⋯ + G_n = L) = C(L-1, n-1)(p-1)^n p^{-L}`.
* `unifDigit p`: the uniform distribution on `{1, …, p-1}` (the index `j` of `U = r(j)` in GGM §4).
  `stepLaw p`: the one-step law `G(μ) ⊗ U(1..p-1)` (independent).

For `p` not satisfying `p ≥ 2` the definitions are formal (`pure`), and all lemmas assume `2 ≤ p`.
The coefficient `p - 1` is written as the ℕ subtraction lifted to `ℝ≥0∞`, `((p - 1 : ℕ) : ℝ≥0∞)`
(these agree for `p ≥ 1`).
-/

open scoped ENNReal NNReal

namespace GGMCollatz

/-- Shift by one a `∑'` whose 0-th term vanishes. -/
theorem tsum_ite_zero_eq_succ (g : ℕ → ℝ≥0∞) :
    ∑' a : ℕ, (if a = 0 then 0 else g a) = ∑' n : ℕ, g (n + 1) := by
  rw [tsum_eq_zero_add' ENNReal.summable]; simp

/-! ### Basic facts about `p⁻¹` -/

theorem natCast_inv_ne_top {p : ℕ} (hp : 1 ≤ p) : ((p : ℝ≥0∞)⁻¹) ≠ ⊤ :=
  ENNReal.inv_ne_top.mpr (by exact_mod_cast (by omega : p ≠ 0))

theorem natCast_inv_ne_zero (p : ℕ) : ((p : ℝ≥0∞)⁻¹) ≠ 0 :=
  ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top p)

theorem natCast_sub_one_ne_zero {p : ℕ} (hp : 2 ≤ p) : ((p - 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast (by omega : p - 1 ≠ 0)

/-- `1 - p⁻¹ = (p-1) p⁻¹` (`p ≥ 1`). -/
theorem one_sub_inv_natCast {p : ℕ} (hp : 1 ≤ p) :
    (1 : ℝ≥0∞) - (p : ℝ≥0∞)⁻¹ = ((p - 1 : ℕ) : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ := by
  apply ENNReal.sub_eq_of_eq_add (natCast_inv_ne_top hp)
  rw [show ((p - 1 : ℕ) : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹
      = (((p - 1 : ℕ) : ℝ≥0∞) + 1) * (p : ℝ≥0∞)⁻¹ by ring,
    show ((p - 1 : ℕ) : ℝ≥0∞) + 1 = (p : ℝ≥0∞) by exact_mod_cast Nat.sub_add_cancel hp,
    ENNReal.mul_inv_cancel (by exact_mod_cast (by omega : p ≠ 0)) (ENNReal.natCast_ne_top p)]

/-! ### The geometric distribution `G(μ)` -/

/-- The mass function of the geometric distribution sums to 1. -/
theorem geomP_hasSum {p : ℕ} (hp : 2 ≤ p) :
    HasSum (fun k : ℕ => if k = 0 then (0 : ℝ≥0∞)
      else ((p - 1 : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ k) 1 := by
  have h : ∑' k : ℕ, (if k = 0 then (0 : ℝ≥0∞)
      else ((p - 1 : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ k) = 1 := by
    rw [tsum_ite_zero_eq_succ (fun k => ((p - 1 : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ k),
      ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one, one_sub_inv_natCast (by omega),
      ← mul_assoc]
    apply ENNReal.mul_inv_cancel
    · exact mul_ne_zero (natCast_sub_one_ne_zero hp) (natCast_inv_ne_zero p)
    · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (natCast_inv_ne_top (by omega))
  have hs := ENNReal.summable.hasSum (f := fun k : ℕ => if k = 0 then (0 : ℝ≥0∞)
      else ((p - 1 : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ k)
  rwa [h] at hs

/-- The body of `geomP` (when `2 ≤ p`). -/
noncomputable def geomPAux {p : ℕ} (hp : 2 ≤ p) : PMF ℕ :=
  ⟨fun k => if k = 0 then 0 else ((p - 1 : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ k, geomP_hasSum hp⟩

/-- **`G(μ)`** (`μ = p/(p-1)`): `P(k) = (p-1) p^{-k}` (`k ≥ 1`). GGM §2.1, §3. -/
noncomputable def geomP (p : ℕ) : PMF ℕ :=
  if hp : 2 ≤ p then geomPAux hp else PMF.pure 1

/-- The pointwise mass of `geomP`. -/
theorem geomP_apply {p : ℕ} (hp : 2 ≤ p) (k : ℕ) :
    geomP p k = if k = 0 then 0 else ((p - 1 : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ k := by
  unfold geomP; rw [dif_pos hp]; rfl

/-- For `p = 2` this is tao-collatz's `geomHalf` (`P(k) = 2^{-k}`). -/
theorem geomP_two_apply (k : ℕ) : geomP 2 k = if k = 0 then 0 else ((2 : ℝ≥0∞)⁻¹) ^ k := by
  rw [geomP_apply (le_refl 2)]
  norm_num

/-- The real-valued mass of `geomP`. -/
theorem geomP_toReal {p : ℕ} (hp : 2 ≤ p) (k : ℕ) :
    (geomP p k).toReal = if k = 0 then 0 else ((p : ℝ) - 1) * ((p : ℝ)⁻¹) ^ k := by
  rw [geomP_apply hp]
  split_ifs
  · simp
  · rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast, Nat.cast_sub (by omega), Nat.cast_one]

/-- The mass of the i.i.d. `G(μ)ⁿ` at a point whose components are all at least 1: `(p-1)^n p^{-Σa}`. -/
theorem iid_geomP_apply_of_pos {p : ℕ} (hp : 2 ≤ p) (n : ℕ) (a : Fin n → ℕ)
    (ha : ∀ i, 1 ≤ a i) :
    (PMF.iid (geomP p) n) a = ((p - 1 : ℕ) : ℝ≥0∞) ^ n * ((p : ℝ≥0∞)⁻¹) ^ (∑ i, a i) := by
  rw [PMF.iid_apply_eq_prod]
  calc (∏ i : Fin n, geomP p (a i))
      = ∏ i : Fin n, (((p - 1 : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ a i) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [geomP_apply hp, if_neg (by have := ha i; omega)]
    _ = ((p - 1 : ℕ) : ℝ≥0∞) ^ n * ((p : ℝ≥0∞)⁻¹) ^ (∑ i, a i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.prod_pow_eq_pow_sum]

/-- The mass at a point having a component equal to 0 is 0. -/
theorem iid_geomP_apply_eq_zero_of_not_pos {p : ℕ} (hp : 2 ≤ p) (n : ℕ) (a : Fin n → ℕ)
    (ha : ¬ ∀ i, 1 ≤ a i) : (PMF.iid (geomP p) n) a = 0 := by
  rw [PMF.iid_apply_eq_prod]
  push Not at ha
  obtain ⟨i, hi⟩ := ha
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [geomP_apply hp, if_pos (by omega)]

/-- The mass at a point with total sum 0 is 0 (`n ≥ 1`). -/
theorem iid_geomP_sum_zero {p : ℕ} (hp : 2 ≤ p) {n : ℕ} (hn : 1 ≤ n) (w : Fin n → ℕ)
    (hw : ∑ i, w i = 0) : (PMF.iid (geomP p) n) w = 0 := by
  apply iid_geomP_apply_eq_zero_of_not_pos hp
  intro hpos
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hz : w 0 = 0 := Finset.sum_eq_zero_iff.mp hw 0 (Finset.mem_univ _)
  have := hpos 0
  omega

/-- The mass of the pushforward under the sum, written as a weighted indicator function. -/
theorem map_sum_apply (μ : PMF ℕ) (n L : ℕ) :
    ((μ.iid n).map fun v => ∑ i, v i) L
      = ∑' v : Fin n → ℕ, (μ.iid n) v * (if L = ∑ i, v i then 1 else 0) := by
  rw [PMF.map_apply]
  exact tsum_congr fun v => by split_ifs <;> simp

/-- Column sums of Pascal's triangle (hockey stick): `∑_{j<K} C(j,m) = C(K, m+1)`. -/
theorem sum_range_choose_col (K m : ℕ) :
    ∑ j ∈ Finset.range K, j.choose m = K.choose (m + 1) := by
  induction K with
  | zero => simp
  | succ K IH =>
    rw [Finset.sum_range_succ, IH, Nat.choose_succ_succ, Nat.succ_eq_add_one]
    omega

/-- The index shift used in the negative binomial convolution. -/
theorem sum_Ico_choose_shift (m L : ℕ) :
    ∑ a ∈ Finset.Ico 1 L, (L - a - 1).choose m = (L - 1).choose (m + 1) := by
  rw [← sum_range_choose_col (L - 1) m]
  refine Finset.sum_nbij' (i := fun a => L - 1 - a) (j := fun b => L - 1 - b)
    ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_Ico] at ha
    rw [Finset.mem_range]
    omega
  · intro b hb
    rw [Finset.mem_range] at hb
    rw [Finset.mem_Ico]
    omega
  · intro a ha
    rw [Finset.mem_Ico] at ha
    omega
  · intro b hb
    rw [Finset.mem_range] at hb
    omega
  · intro a ha
    rw [Finset.mem_Ico] at ha
    congr 1
    omega

/-- **Negative binomial**: the sum of `G(μ)ⁿ` puts mass `C(L-1, n-1)(p-1)^n p^{-L}` at `L` (`n, L ≥ 1`). -/
theorem negBinomial_apply {p : ℕ} (hp : 2 ≤ p) (n L : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    ((PMF.iid (geomP p) n).map (fun v => ∑ i, v i)) L
      = (L - 1).choose (n - 1) * ((p - 1 : ℕ) : ℝ≥0∞) ^ n * ((p : ℝ≥0∞)⁻¹) ^ L := by
  set c : ℝ≥0∞ := ((p - 1 : ℕ) : ℝ≥0∞) with hc
  set r : ℝ≥0∞ := (p : ℝ≥0∞)⁻¹ with hr
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  clear hn
  simp only [Nat.add_sub_cancel]
  induction m generalizing L with
  | zero =>
    rw [map_sum_apply, PMF.tsum_iid_succ_mul]
    have hinner : ∀ a : ℕ,
        geomP p a * (∑' w : Fin 0 → ℕ, ((geomP p).iid 0) w
          * (if L = ∑ i, Fin.cons (α := fun _ => ℕ) a w i then 1 else 0))
        = geomP p a * (if L = a then (1 : ℝ≥0∞) else 0) := by
      intro a
      congr 1
      rw [PMF.tsum_iid_zero_mul]
      have hiff : (L = ∑ i, Fin.cons (α := fun _ => ℕ) a (fun i : Fin 0 => i.elim0) i)
          ↔ L = a := by
        rw [Fin.sum_cons]
        simp
      exact if_congr hiff rfl rfl
    rw [tsum_congr hinner,
      tsum_eq_single L (fun a ha => by rw [if_neg (Ne.symm ha), mul_zero]),
      if_pos rfl, mul_one, geomP_apply hp, if_neg (by omega), Nat.choose_zero_right,
      Nat.cast_one, one_mul, pow_one]
  | succ m IH =>
    rw [map_sum_apply, PMF.tsum_iid_succ_mul]
    have hinner : ∀ a : ℕ,
        geomP p a * (∑' w : Fin (m + 1) → ℕ, ((geomP p).iid (m + 1)) w
          * (if L = ∑ i, Fin.cons (α := fun _ => ℕ) a w i then 1 else 0))
        = if a ∈ Finset.Ico 1 L
            then ((L - a - 1).choose m : ℝ≥0∞) * c ^ (m + 1 + 1) * r ^ L else 0 := by
      intro a
      rcases Nat.eq_zero_or_pos a with rfl | ha1
      · rw [geomP_apply hp, if_pos rfl, zero_mul,
          if_neg (by rw [Finset.mem_Ico]; omega)]
      rcases lt_or_ge a L with haL | haL
      · have hin : (∑' w : Fin (m + 1) → ℕ, ((geomP p).iid (m + 1)) w
              * (if L = ∑ i, Fin.cons (α := fun _ => ℕ) a w i then 1 else 0))
            = (((geomP p).iid (m + 1)).map fun v => ∑ i, v i) (L - a) := by
          rw [map_sum_apply]
          refine tsum_congr fun w => ?_
          congr 1
          have hiff : (L = ∑ i, Fin.cons (α := fun _ => ℕ) a w i)
              ↔ (L - a = ∑ i, w i) := by
            rw [Fin.sum_cons]
            omega
          exact if_congr hiff rfl rfl
        have hpow : r ^ a * r ^ (L - a) = r ^ L := by
          rw [← pow_add, Nat.add_sub_cancel' haL.le]
        rw [hin, IH (L - a) (by omega), if_pos (by rw [Finset.mem_Ico]; omega),
          geomP_apply hp, if_neg (by omega), show L - a - 1 = L - a - 1 from rfl, ← hpow]
        ring
      · have hin : (∑' w : Fin (m + 1) → ℕ, ((geomP p).iid (m + 1)) w
              * (if L = ∑ i, Fin.cons (α := fun _ => ℕ) a w i then 1 else 0)) = 0 := by
          refine ENNReal.tsum_eq_zero.mpr fun w => ?_
          rw [Fin.sum_cons]
          split_ifs with h
          · rw [iid_geomP_sum_zero hp (by omega) w (by omega), zero_mul]
          · rw [mul_zero]
        rw [hin, mul_zero, if_neg (by rw [Finset.mem_Ico]; omega)]
    rw [tsum_congr hinner,
      tsum_eq_sum (s := Finset.Ico 1 L) (fun a ha => if_neg ha),
      Finset.sum_congr rfl (fun a ha => if_pos ha), ← Finset.sum_mul, ← Finset.sum_mul,
      ← Nat.cast_sum, sum_Ico_choose_shift]

/-! ### The Pascal distribution `P(μ) = G(μ) + G(μ)` -/

/-- **Pascal distribution**: the law of the sum of two independent copies of `G(μ)` (GGM §2.1, §7). -/
noncomputable def pascalP (p : ℕ) : PMF ℕ := (PMF.iid (geomP p) 2).map (fun v => v 0 + v 1)

/-- By definition: Pascal is the pushforward of `G(μ)²` under the sum (tao-collatz's `pascal_eq_map_iid`). -/
theorem pascal_eq_map_iid (p : ℕ) :
    pascalP p = (PMF.iid (geomP p) 2).map (fun v => v 0 + v 1) := rfl

/-- **Pascal mass**: `P(b) = (b-1)(p-1)² p^{-b}` (`b ≥ 2`; 0 otherwise). -/
theorem pascalP_apply {p : ℕ} (hp : 2 ≤ p) (b : ℕ) :
    pascalP p b = if b < 2 then 0
      else ((b - 1 : ℕ) : ℝ≥0∞) * ((p - 1 : ℕ) : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ b := by
  have hsum : (fun v : Fin 2 → ℕ => v 0 + v 1) = fun v : Fin 2 → ℕ => ∑ i, v i := by
    funext v
    rw [Fin.sum_univ_two]
  rw [pascal_eq_map_iid, hsum]
  rcases b with _ | b
  · rw [if_pos (by omega), map_sum_apply]
    refine ENNReal.tsum_eq_zero.mpr fun v => ?_
    split_ifs with h
    · rw [iid_geomP_sum_zero hp (by omega) v (by omega), zero_mul]
    · rw [mul_zero]
  · rw [negBinomial_apply hp 2 (b + 1) (by omega) (by omega)]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · rw [if_pos (by omega)]
      simp
    · rw [if_neg (by omega), Nat.add_sub_cancel, Nat.choose_one_right]

/-- `P(Pascal = 3) = 2(p-1)² p^{-3}`. -/
theorem pascalP_three {p : ℕ} (hp : 2 ≤ p) :
    pascalP p 3 = 2 * ((p - 1 : ℕ) : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ 3 := by
  rw [pascalP_apply hp, if_neg (by omega)]
  norm_num

/-- `P(Pascal = 3) > 0`. -/
theorem pascalP_three_pos {p : ℕ} (hp : 2 ≤ p) : 0 < pascalP p 3 := by
  rw [pascalP_three hp]
  exact ENNReal.mul_pos (mul_ne_zero (by norm_num) (pow_ne_zero _ (natCast_sub_one_ne_zero hp)))
    (pow_ne_zero _ (natCast_inv_ne_zero p))

/-- `P(Pascal = 2) > 0`. -/
theorem pascalP_two_pos {p : ℕ} (hp : 2 ≤ p) : 0 < pascalP p 2 := by
  rw [pascalP_apply hp, if_neg (by omega)]
  exact ENNReal.mul_pos (mul_ne_zero (by norm_num) (pow_ne_zero _ (natCast_sub_one_ne_zero hp)))
    (pow_ne_zero _ (natCast_inv_ne_zero p))

/-- **Pascal avoiding `b = 3`** (the grouping of GGM §7; tao-collatz's `pascalNe3`):
`pascalP p` restricted to `{b ≠ 3}` and normalized. -/
noncomputable def pascalNe3P (p : ℕ) : PMF ℕ :=
  if hp : 2 ≤ p then
    (pascalP p).filter {b | b ≠ 3}
      ⟨2, by simp, (PMF.mem_support_iff _ _).mpr (pascalP_two_pos hp).ne'⟩
  else PMF.pure 2

/-- The Pascal mass on `{b ≠ 3}` sums to `1 - P(3)`. -/
theorem tsum_pascalP_ne_three (p : ℕ) :
    ∑' b, ({b | b ≠ 3} : Set ℕ).indicator (pascalP p) b = 1 - pascalP p 3 := by
  apply ENNReal.eq_sub_of_add_eq (PMF.apply_ne_top _ _)
  have h := ENNReal.tsum_eq_add_tsum_ite (f := pascalP p) 3
  rw [PMF.tsum_coe] at h
  rw [h, add_comm]
  congr 1
  apply tsum_congr
  intro b
  by_cases hb : b = 3
  · simp [hb]
  · simp [hb]

/-- **Mass of `pascalNe3P`**: `P(b) / (1 - P(3))` (`b ≠ 3`), and 0 at `b = 3`. -/
theorem pascalNe3P_apply {p : ℕ} (hp : 2 ≤ p) (b : ℕ) :
    pascalNe3P p b = if b = 3 then 0 else (1 - pascalP p 3)⁻¹ * pascalP p b := by
  unfold pascalNe3P
  rw [dif_pos hp, PMF.filter_apply, tsum_pascalP_ne_three]
  by_cases hb : b = 3
  · rw [if_pos hb, hb]; simp
  · rw [if_neg hb, Set.indicator_of_mem (show b ∈ ({b | b ≠ 3} : Set ℕ) from hb), mul_comm]

/-! ### The geometric distribution with success probability `s` (`J` in GGM §7) -/

/-- The mass function of the geometric distribution with success probability `s` sums to 1 (`0 < s ≤ 1`). -/
theorem geomS_hasSum {s : ℝ≥0∞} (hs : 0 < s ∧ s ≤ 1) :
    HasSum (fun k : ℕ => if k = 0 then (0 : ℝ≥0∞) else s * (1 - s) ^ (k - 1)) 1 := by
  have hst : s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hs.2
  have h : ∑' k : ℕ, (if k = 0 then (0 : ℝ≥0∞) else s * (1 - s) ^ (k - 1)) = 1 := by
    rw [tsum_ite_zero_eq_succ (fun k => s * (1 - s) ^ (k - 1))]
    simp only [Nat.add_sub_cancel]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
      ENNReal.sub_sub_cancel ENNReal.one_ne_top hs.2, ENNReal.mul_inv_cancel hs.1.ne' hst]
  have hsum := ENNReal.summable.hasSum
    (f := fun k : ℕ => if k = 0 then (0 : ℝ≥0∞) else s * (1 - s) ^ (k - 1))
  rwa [h] at hsum

/-- The body of `geomS` (when `0 < s ≤ 1`). -/
noncomputable def geomSAux {s : ℝ≥0∞} (hs : 0 < s ∧ s ≤ 1) : PMF ℕ :=
  ⟨fun k => if k = 0 then 0 else s * (1 - s) ^ (k - 1), geomS_hasSum hs⟩

/-- **Geometric distribution with success probability `s`**: `P(k) = s(1-s)^{k-1}` (`k ≥ 1`). Formal when `0 < s ≤ 1` fails. -/
noncomputable def geomS (s : ℝ≥0∞) : PMF ℕ :=
  if hs : 0 < s ∧ s ≤ 1 then geomSAux hs else PMF.pure 1

theorem geomS_apply {s : ℝ≥0∞} (hs : 0 < s ∧ s ≤ 1) (k : ℕ) :
    geomS s k = if k = 0 then 0 else s * (1 - s) ^ (k - 1) := by
  unfold geomS; rw [dif_pos hs]; rfl

/-- The real-valued mass of `geomS`. -/
theorem geomS_toReal {s : ℝ≥0∞} (hs : 0 < s ∧ s ≤ 1) (k : ℕ) :
    (geomS s k).toReal = if k = 0 then 0 else s.toReal * (1 - s.toReal) ^ (k - 1) := by
  rw [geomS_apply hs]
  split_ifs
  · simp
  · rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_sub_of_le hs.2 ENNReal.one_ne_top,
      ENNReal.toReal_one]

/-- The real-valued masses of `geomS` sum to 1. -/
theorem geomS_tsum_toReal (s : ℝ≥0∞) : ∑' k : ℕ, (geomS s k).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun k => (geomS s).apply_ne_top k),
    (geomS s).tsum_coe, ENNReal.toReal_one]

theorem geomS_summable_toReal (s : ℝ≥0∞) : Summable fun k : ℕ => (geomS s k).toReal :=
  ENNReal.summable_toReal (geomS s).tsum_coe_ne_top

/-- **Tail of the geometric distribution**: the mass beyond `t` is exactly `(1-s)^t` (tao-collatz's `geomQuarter_tail`). -/
theorem geomS_tail {s : ℝ≥0∞} (hs : 0 < s ∧ s ≤ 1) (t : ℕ) :
    ∑' k : ℕ, (if t < k then (geomS s k).toReal else 0) = (1 - s.toReal) ^ t := by
  have hst : s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hs.2
  have hs0 : 0 < s.toReal := ENNReal.toReal_pos hs.1.ne' hst
  have hs1 : s.toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hs.2
    simpa using this
  have hinj : Function.Injective (fun i : ℕ => t + 1 + i) := add_right_injective (t + 1)
  have hzero : ∀ k ∉ Set.range (fun i : ℕ => t + 1 + i),
      (if t < k then (geomS s k).toReal else 0) = 0 := by
    intro k hk
    have hlt : ¬ t < k := fun h => hk ⟨k - (t + 1), by show t + 1 + (k - (t + 1)) = k; omega⟩
    rw [if_neg hlt]
  have heq : ((fun k => if t < k then (geomS s k).toReal else 0)
        ∘ (fun i : ℕ => t + 1 + i))
      = fun i : ℕ => (s.toReal * (1 - s.toReal) ^ t) * (1 - s.toReal) ^ i := by
    funext i
    simp only [Function.comp]
    rw [if_pos (by omega : t < t + 1 + i), geomS_toReal hs,
      if_neg (by omega : ¬ t + 1 + i = 0),
      show t + 1 + i - 1 = t + i from by omega, pow_add]
    ring
  have hgeo : HasSum (fun i : ℕ => (1 - s.toReal) ^ i) (s.toReal)⁻¹ := by
    have h := hasSum_geometric_of_lt_one (r := 1 - s.toReal) (by linarith) (by linarith)
    rwa [show 1 - (1 - s.toReal) = s.toReal by ring] at h
  have hcomp : HasSum ((fun k => if t < k then (geomS s k).toReal else 0)
      ∘ (fun i : ℕ => t + 1 + i)) ((1 - s.toReal) ^ t) := by
    rw [heq]
    have h := hgeo.mul_left (s.toReal * (1 - s.toReal) ^ t)
    have hval : s.toReal * (1 - s.toReal) ^ t * (s.toReal)⁻¹ = (1 - s.toReal) ^ t := by
      field_simp
    rwa [hval] at h
  exact ((hinj.hasSum_iff hzero).mp hcomp).tsum_eq

/-- **The law of `J` in GGM §7**: the geometric distribution with success probability `P(Pascal = 3)` (tao-collatz's `geomQuarter`). -/
noncomputable def holdGeom (p : ℕ) : PMF ℕ := geomS (pascalP p 3)

/-- The success probability of `holdGeom` lies in `(0, 1]`. -/
theorem holdGeom_prob {p : ℕ} (hp : 2 ≤ p) : 0 < pascalP p 3 ∧ pascalP p 3 ≤ 1 :=
  ⟨pascalP_three_pos hp, PMF.coe_le_one _ _⟩

/-! ### Uniform digits and the one-step law -/

/-- The uniform distribution on `{1, …, p-1}` (the index of the residue `U = r(j)` in GGM §4). -/
noncomputable def unifDigit (p : ℕ) : PMF ℕ :=
  if hp : 2 ≤ p then
    PMF.uniformOfFinset (Finset.Ioo 0 p) (show (Finset.Ioo 0 p).Nonempty from ⟨1, by simp; omega⟩)
  else PMF.pure 1

/-- The mass of `unifDigit`: `(p-1)⁻¹` (`0 < d < p`). -/
theorem unifDigit_apply {p : ℕ} (hp : 2 ≤ p) (d : ℕ) :
    unifDigit p d = if 0 < d ∧ d < p then ((p - 1 : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  unfold unifDigit
  rw [dif_pos hp, PMF.uniformOfFinset_apply, Nat.card_Ioo, Nat.sub_zero]
  simp only [Finset.mem_Ioo]

/-- **One-step law**: the independent pair of the valuation `G(μ)` and the digit `U(1..p-1)`. -/
noncomputable def stepLaw (p : ℕ) : PMF (ℕ × ℕ) :=
  (geomP p).bind fun a => (unifDigit p).map fun d => (a, d)

/-- The mass of the one-step law is a product. -/
theorem stepLaw_apply (p a d : ℕ) : stepLaw p (a, d) = geomP p a * unifDigit p d := by
  unfold stepLaw
  rw [PMF.bind_apply, tsum_eq_single a]
  · rw [PMF.map_apply, tsum_eq_single d]
    · simp
    · intro d' hd'
      rw [if_neg]
      intro h
      exact hd' (Prod.mk.inj h).2.symm
  · intro a' ha'
    rw [PMF.map_apply]
    rw [ENNReal.tsum_eq_zero.mpr, mul_zero]
    intro d'
    rw [if_neg]
    intro h
    exact ha' (Prod.mk.inj h).1.symm

/-- The first component of the one-step law is `G(μ)`. -/
theorem stepLaw_map_fst (p : ℕ) : (stepLaw p).map Prod.fst = geomP p := by
  unfold stepLaw
  rw [PMF.map_bind]
  conv_lhs =>
    arg 2; ext a
    rw [PMF.map_comp]
    rw [show (Prod.fst ∘ fun d : ℕ => (a, d)) = Function.const ℕ a from rfl, PMF.map_const]
  exact PMF.bind_pure _

/-- The second component of the one-step law is `U(1..p-1)`. -/
theorem stepLaw_map_snd (p : ℕ) : (stepLaw p).map Prod.snd = unifDigit p := by
  unfold stepLaw
  rw [PMF.map_bind]
  conv_lhs =>
    arg 2; ext a
    rw [PMF.map_comp, show (Prod.snd ∘ fun d : ℕ => (a, d)) = id from rfl, PMF.map_id]
  exact PMF.bind_const _ _

/-- Mapping an i.i.d. vector componentwise gives the i.i.d. vector of the mapped law. -/
theorem iid_map_comp {α β : Type*} (μ : PMF α) (f : α → β) :
    ∀ n : ℕ, (μ.iid n).map (fun v => f ∘ v) = (μ.map f).iid n := by
  intro n
  induction n with
  | zero =>
    rw [show (fun v : Fin 0 → α => f ∘ v) = Function.const _ (fun i : Fin 0 => i.elim0) from by
      funext v; funext i; exact i.elim0, PMF.map_const]
    rfl
  | succ n ih =>
    rw [show μ.iid (n + 1) = μ.bind fun a => (μ.iid n).map (Fin.cons a) from rfl,
      show (μ.map f).iid (n + 1) = (μ.map f).bind fun b => ((μ.map f).iid n).map (Fin.cons b)
        from rfl, PMF.map_bind, PMF.bind_map]
    congr 1
    funext a
    rw [PMF.map_comp, Function.comp_apply, ← ih, PMF.map_comp]
    congr 1
    funext w
    funext i
    refine Fin.cases ?_ (fun k => ?_) i <;> simp

/-- The valuation components of the i.i.d. one-step law are `G(μ)ⁿ`. -/
theorem iid_stepLaw_map_fst (p n : ℕ) :
    ((stepLaw p).iid n).map (fun v => Prod.fst ∘ v) = (geomP p).iid n := by
  rw [iid_map_comp, stepLaw_map_fst]

/-- The digit components of the i.i.d. one-step law are `U(1..p-1)ⁿ`. -/
theorem iid_stepLaw_map_snd (p n : ℕ) :
    ((stepLaw p).iid n).map (fun v => Prod.snd ∘ v) = (unifDigit p).iid n := by
  rw [iid_map_comp, stepLaw_map_snd]

/-- The mass of the i.i.d. one-step law is a product. -/
theorem iid_stepLaw_apply (p n : ℕ) (v : Fin n → ℕ × ℕ) :
    ((stepLaw p).iid n) v = ∏ i, geomP p (v i).1 * unifDigit p (v i).2 := by
  rw [PMF.iid_apply_eq_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [← stepLaw_apply]

end GGMCollatz
