import GGMCollatz.NatDen.UProf.Defs

/-!
# Ingredients of (UM): the probabilistic side (step (0) of the master formula and around the identity (K))

* `jp_eq_jpG_true` (orientation, (0)): `jp F k X s` (the pushforward under `offsetIn`) equals `jpG F k X s (fun _ => True)`, written with
  the forward offset `offsetFwd` and the unrestricted event (reversing the order of the i.i.d. variables, `iid_map_rev`).
* `jpG_true_sub`: the difference after removing the restriction is `jpG` of the complementary event.
* `sum_jpG`, `sum_pG_le`: summing over residue classes gives `P(Σa = s, G)`, and further summing over `s` gives at most `P(G)`.
* `nb_le_local` (the local bound `P(s_k = s) ≪ k^{-1/2}`) and `nb_tail_cen` (the tail outside the centre `≤ 4/k²`).

The proof of `offsetFwd_eq_rev` extracts, as a lemma, the identity inside `syracZ_eq_rev_fint` of `Tao/Syracuse/SyracRV.lean`
(derived from `syracZ_eq_rev_fnat` of `TaoCollatz/Syracuse/SyracRV.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2).
`sum_fst_toReal` and `sum_jp` are copies of the lemmas of the same names in `NatDen/SumMixC/Compose.lean`
(so as not to depend on another contributor's work area).
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace MasterAux

variable (F : Family)

open Classical in
/-- `P(Σa = s, G(a))` (for i.i.d. variables with the one-step law). -/
noncomputable def pG (k s : ℕ) (G : (Fin k → ℕ) → Prop) : ℝ :=
  ∑' v : Fin k → ℕ × ℕ, ((PMF.iid (stepLaw F.p) k) v).toReal *
    (if (∑ i, (v i).1 = s ∧ G (fun i => (v i).1)) then 1 else 0)

/-- The product of a mass function and a bounded function is summable. -/
theorem summable_mass_mul (k : ℕ) (f : (Fin k → ℕ × ℕ) → ℝ) (hf : ∀ v, |f v| ≤ 1) :
    Summable fun v : Fin k → ℕ × ℕ => ((PMF.iid (stepLaw F.p) k) v).toReal * f v :=
  Family.summable_mul_of_bounded _ _ 1 hf

theorem jpG_nonneg (k : ℕ) (X : ZMod (F.q ^ k)) (s : ℕ) (G : (Fin k → ℕ) → Prop) :
    0 ≤ jpG F k X s G := by
  unfold jpG
  exact tsum_nonneg fun v => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num)

theorem pG_nonneg (k s : ℕ) (G : (Fin k → ℕ) → Prop) : 0 ≤ pG F k s G := by
  unfold pG
  exact tsum_nonneg fun v => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num)

/-- The forward offset is `offsetIn` of the reversed vector. -/
theorem offsetFwd_eq_rev (n : ℕ) (b : Fin n → ℕ × ℕ) :
    F.offsetFwd b = F.offsetIn (F.q ^ n) (b ∘ Fin.rev) := by
  have hunit := F.p_mul_inv_zmod n
  unfold Family.offsetFwd
  set a : Fin n → ℕ := fun i => (b i).1 with ha
  rw [F.fint_eq_sum_range, Int.cast_sum, Finset.sum_mul, ← Finset.sum_range_reflect]
  unfold Family.offsetIn
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hj' : n - 1 - (n - 1 - j) = j := by omega
  rw [hj']
  have hsplit : pre (a ∘ Fin.rev) (j + 1) + pre a (n - 1 - j) = pre a n := by
    have := pre_comp_rev a (m := j + 1) (by omega)
    rwa [show n - (j + 1) = n - 1 - j from by omega] at this
  have hvget : vget (fun i => F.r (b i).2) 0 (n - 1 - j)
      = F.r (vget (fun i => ((b ∘ Fin.rev) i).2) 0 j) := by
    rw [vget_of_lt _ _ (by omega), vget_of_lt _ _ hj]
    simp only [Function.comp_apply]
    congr 3
    apply Fin.ext
    rw [Fin.val_rev]
    simp only
    omega
  rw [hvget]
  have hpre_eq : pre (fun i => ((b ∘ Fin.rev) i).1) (j + 1) = pre (a ∘ Fin.rev) (j + 1) := rfl
  rw [hpre_eq]
  set P := pre a (n - 1 - j)
  set Q := pre (a ∘ Fin.rev) (j + 1)
  push_cast
  rw [← hsplit, pow_add]
  have h2 : (F.p : ZMod (F.q ^ n)) ^ P * ((F.p : ZMod (F.q ^ n))⁻¹) ^ P = 1 := by
    rw [← mul_pow, hunit, one_pow]
  linear_combination ((F.q : ZMod (F.q ^ n)) ^ j * ((F.p : ZMod (F.q ^ n))⁻¹) ^ Q
    * (F.r (vget (fun i => ((b ∘ Fin.rev) i).2) 0 j) : ZMod (F.q ^ n))) * h2

/-- The joint law of `(𝒮_n, s_n)` can also be written with the forward offset. -/
theorem jointSZ_eq_fwd (k : ℕ) :
    jointSZ F k = ((stepLaw F.p).iid k).map (fun v => (F.offsetFwd v, ∑ i, (v i).1)) := by
  unfold jointSZ
  conv_lhs => rw [← iid_map_rev (stepLaw F.p) k]
  rw [PMF.map_comp]
  congr 1
  funext v
  simp only [Function.comp_apply]
  rw [offsetFwd_eq_rev]
  congr 1
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun i => by rw [Fin.revPerm_apply])

open Classical in
/-- **Orientation** (step (0) of the master formula): `jp = jpG(·, True)`. -/
theorem jp_eq_jpG_true (k : ℕ) (X : ZMod (F.q ^ k)) (s : ℕ) :
    jp F k X s = jpG F k X s (fun _ => True) := by
  unfold jp jpG
  rw [jointSZ_eq_fwd, PMF.map_apply, ENNReal.tsum_toReal_eq (fun v => by
    split_ifs
    · exact PMF.apply_ne_top _ _
    · exact ENNReal.zero_ne_top)]
  refine tsum_congr fun v => ?_
  by_cases h : ∑ i, (v i).1 = s ∧ F.offsetFwd v = X
  · rw [if_pos (by rw [Prod.ext_iff]; exact ⟨h.2.symm, h.1.symm⟩), if_pos ⟨h.1, h.2, trivial⟩,
      mul_one]
  · rw [if_neg (by
      rw [Prod.ext_iff]
      exact fun h' => h ⟨h'.2.symm, h'.1.symm⟩), if_neg (by
      rintro ⟨h1, h2, -⟩
      exact h ⟨h1, h2⟩), mul_zero, ENNReal.toReal_zero]

open Classical in
/-- The difference after removing the restriction is the complementary event. -/
theorem jpG_true_sub (k : ℕ) (X : ZMod (F.q ^ k)) (s : ℕ) (G : (Fin k → ℕ) → Prop) :
    jpG F k X s (fun _ => True) - jpG F k X s G = jpG F k X s (fun a => ¬ G a) := by
  unfold jpG
  rw [← Summable.tsum_sub (summable_mass_mul F k _ (fun v => by split_ifs <;> norm_num))
    (summable_mass_mul F k _ (fun v => by split_ifs <;> norm_num))]
  refine tsum_congr fun v => ?_
  rw [← mul_sub]
  congr 1
  by_cases hA : ∑ i, (v i).1 = s ∧ F.offsetFwd v = X
  · by_cases hG : G (fun i => (v i).1)
    · simp [hA.1, hA.2, hG]
    · simp [hA.1, hA.2, hG]
  · have h1 : ¬ (∑ i, (v i).1 = s ∧ F.offsetFwd v = X ∧ True) := fun h => hA ⟨h.1, h.2.1⟩
    have h2 : ¬ (∑ i, (v i).1 = s ∧ F.offsetFwd v = X ∧ G (fun i => (v i).1)) :=
      fun h => hA ⟨h.1, h.2.1⟩
    have h3 : ¬ (∑ i, (v i).1 = s ∧ F.offsetFwd v = X ∧ ¬ G (fun i => (v i).1)) :=
      fun h => hA ⟨h.1, h.2.1⟩
    rw [if_neg h1, if_neg h2, if_neg h3, sub_zero]

open Classical in
/-- Summing over residue classes. -/
theorem sum_jpG (k s : ℕ) (G : (Fin k → ℕ) → Prop) :
    ∑ X : ZMod (F.q ^ k), jpG F k X s G = pG F k s G := by
  unfold jpG pG
  rw [← Summable.tsum_finsetSum (fun X _ => summable_mass_mul F k _
    (fun v => by split_ifs <;> norm_num))]
  refine tsum_congr fun v => ?_
  rw [← Finset.mul_sum]
  congr 1
  by_cases hA : ∑ i, (v i).1 = s ∧ G (fun i => (v i).1)
  · rw [if_pos hA]
    have : ∀ X : ZMod (F.q ^ k),
        (if (∑ i, (v i).1 = s ∧ F.offsetFwd v = X ∧ G (fun i => (v i).1)) then (1 : ℝ) else 0)
          = if F.offsetFwd v = X then 1 else 0 := fun X => by
      by_cases hX : F.offsetFwd v = X
      · rw [if_pos ⟨hA.1, hX, hA.2⟩, if_pos hX]
      · rw [if_neg (fun h => hX h.2.1), if_neg hX]
    rw [Finset.sum_congr rfl (fun X _ => this X)]
    simp
  · rw [if_neg hA]
    exact Finset.sum_eq_zero fun X _ => if_neg (fun h => hA ⟨h.1, h.2.2⟩)

open Classical in
/-- The finite sum over `s` is at most `P(G)`. -/
theorem sum_pG_le (k : ℕ) (G : (Fin k → ℕ) → Prop) (S : Finset ℕ) :
    ∑ s ∈ S, pG F k s G ≤ Family.expect ((geomP F.p).iid k) (Set.indicator {a | G a} 1) := by
  unfold pG
  rw [← Summable.tsum_finsetSum (fun s _ => summable_mass_mul F k _
    (fun v => by split_ifs <;> norm_num))]
  have hR : Family.expect ((geomP F.p).iid k) (Set.indicator {a | G a} 1)
      = ∑' v : Fin k → ℕ × ℕ, ((PMF.iid (stepLaw F.p) k) v).toReal *
          (if G (fun i => (v i).1) then 1 else 0) := by
    rw [← iid_stepLaw_map_fst, Family.expect_map_indicator]
    unfold Family.expect
    refine tsum_congr fun v => ?_
    congr 1
  rw [hR]
  refine Summable.tsum_le_tsum (fun v => ?_)
    (summable_sum fun s _ => summable_mass_mul F k _ (fun v => by split_ifs <;> norm_num))
    (summable_mass_mul F k _ (fun v => by split_ifs <;> norm_num))
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  by_cases hG : G (fun i => (v i).1)
  · rw [if_pos hG]
    calc ∑ s ∈ S, (if (∑ i, (v i).1 = s ∧ G (fun i => (v i).1)) then (1 : ℝ) else 0)
        = ∑ s ∈ S, (if ∑ i, (v i).1 = s then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl fun s _ => by
            by_cases h : ∑ i, (v i).1 = s
            · rw [if_pos ⟨h, hG⟩, if_pos h]
            · rw [if_neg (fun h' => h h'.1), if_neg h]
      _ ≤ 1 := by
          rw [Finset.sum_ite_eq]
          split_ifs <;> norm_num
  · rw [if_neg hG]
    exact le_of_eq (Finset.sum_eq_zero fun s _ => if_neg (fun h => hG h.2))

/-- The sum over a finite first component is the marginal law of the second component (copy from `NatDen/SumMixC/Compose.lean`). -/
theorem sum_fst_toReal {A B : Type*} [Fintype A] (μ : PMF (A × B)) (b : B) :
    ∑ a : A, (μ (a, b)).toReal = ((μ.map Prod.snd) b).toReal := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod', tsum_fintype]
  rw [ENNReal.toReal_sum (fun a _ => ?_)]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    rw [tsum_eq_single b]
    · simp
    · intro b' hb'
      rw [if_neg (fun h => hb' h.symm)]
  · exact ENNReal.ne_top_of_tsum_ne_top (by
      rw [← ENNReal.tsum_prod']
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (by
        calc ∑' x : A × B, (if b = x.2 then μ x else 0) ≤ ∑' x, μ x :=
              ENNReal.tsum_le_tsum (fun x => by split_ifs <;> simp)
          _ = 1 := PMF.tsum_coe μ)) a

/-- `Σ_X jp = nb`. -/
theorem sum_jp (k s : ℕ) : ∑ X : ZMod (F.q ^ k), jp F k X s = nb F.p k s := by
  unfold jp
  rw [sum_fst_toReal]
  unfold nb jointSZ iidSum
  congr 2
  rw [PMF.map_comp, ← iid_stepLaw_map_fst, PMF.map_comp]
  rfl

theorem jp_nonneg (k : ℕ) (X : ZMod (F.q ^ k)) (s : ℕ) : 0 ≤ jp F k X s := ENNReal.toReal_nonneg

theorem nb_nonneg (p k s : ℕ) : 0 ≤ nb p k s := ENNReal.toReal_nonneg

/-- **Local bound**: `P(s_k = s) ≤ C (1+k)^{-1/2}`. -/
theorem nb_le_local : ∃ C : ℝ, 0 < C ∧ ∀ k s : ℕ, nb F.p k s ≤ C / Real.sqrt (1 + k) := by
  obtain ⟨c, -, C, hC, h⟩ := geomP_local_bound F.two_le_p
  refine ⟨2 * C, by positivity, fun k s => ?_⟩
  have h1 := h k s
  have hG := Gweight_le_two (1 + (k : ℝ)) (c * ((s : ℝ) - muP F.p * k)) (by positivity)
  have hsq : 0 < Real.sqrt (1 + (k : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  unfold nb
  calc ((iidSum (geomP F.p) k) s).toReal
      ≤ C / Real.sqrt (1 + k) * Gweight (1 + k) (c * ((s : ℝ) - muP F.p * k)) := h1
    _ ≤ C / Real.sqrt (1 + k) * 2 := mul_le_mul_of_nonneg_left hG (by positivity)
    _ = 2 * C / Real.sqrt (1 + k) := by ring

/-- The radius of the central window `R_k = 1600 √(k log k)`. -/
noncomputable def rad (k : ℕ) : ℝ := 1600 * Real.sqrt (k * Real.log k)

/-- For `k ≥ 1`, `exp(-2 log k) = 1/k²`. -/
theorem exp_neg_two_log (k : ℕ) (hk : 1 ≤ k) :
    Real.exp (-(2 * Real.log k)) = 1 / (k : ℝ) ^ 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Real.exp_neg, show (2 : ℝ) * Real.log k = ((2 : ℕ) : ℝ) * Real.log k by norm_num,
    Real.exp_nat_mul, Real.exp_log hk0, one_div]

/-- For `k ≥ 1`, `G_{1+k}(R_k/400) ≤ 2/k²`. -/
theorem Gweight_rad_le (k : ℕ) (hk : 1 ≤ k) :
    Gweight (1 + k) (c_geomTail * rad k) ≤ 2 / (k : ℝ) ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hlog0 : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hlogk : Real.log k ≤ k := (Real.log_le_sub_one_of_pos hk0).trans (by linarith)
  set z := c_geomTail * rad k with hz
  have hz' : z = 4 * Real.sqrt (k * Real.log k) := by
    rw [hz, rad, c_geomTail]; ring
  have hzsq : z ^ 2 = 16 * (k * Real.log k) := by
    rw [hz', mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  have hz0 : 0 ≤ z := by rw [hz']; positivity
  -- `z²/(1+k) ≥ 2 log k`
  have h1 : 2 * Real.log k ≤ z ^ 2 / (1 + k) := by
    rw [le_div_iff₀ (by positivity), hzsq]
    nlinarith
  -- `z ≥ 2 log k`
  have h2 : 2 * Real.log k ≤ z := by
    have hsq : (2 * Real.log k) ^ 2 ≤ z ^ 2 := by
      rw [hzsq]; nlinarith
    exact (sq_le_sq₀ (by positivity) hz0).mp hsq
  have e1 : Real.exp (-(z ^ 2) / (1 + k)) ≤ Real.exp (-(2 * Real.log k)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]; linarith
  have e2 : Real.exp (-|z|) ≤ Real.exp (-(2 * Real.log k)) := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg hz0]; linarith
  unfold Gweight
  rw [exp_neg_two_log k hk] at e1 e2
  calc Real.exp (-(z ^ 2) / (1 + k)) + Real.exp (-|z|) ≤ 1 / (k : ℝ) ^ 2 + 1 / (k : ℝ) ^ 2 :=
        add_le_add e1 e2
    _ = 2 / (k : ℝ) ^ 2 := by ring

open Classical in
/-- **The tail outside the centre**: for `k ≥ 1`, `Σ_{s ∈ S, |s - μk| > R_k} P(s_k = s) ≤ 4/k²`. -/
theorem nb_tail_cen (k : ℕ) (hk : 1 ≤ k) (S : Finset ℕ) :
    ∑ s ∈ S.filter (fun s : ℕ => ¬ |(s : ℝ) - F.mu * k| ≤ rad k), nb F.p k s ≤ 4 / (k : ℝ) ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hrad0 : 0 ≤ rad k := by unfold rad; positivity
  set f : ℕ → ℝ := fun s => if rad k ≤ |(s : ℝ) - muP F.p * k| then
    ((iidSum (geomP F.p) k) s).toReal else 0 with hf
  have hf0 : ∀ s, 0 ≤ f s := fun s => by
    simp only [hf]; split_ifs <;> simp
  have hfs : Summable f := by
    refine Summable.of_nonneg_of_le hf0 (fun s => ?_)
      (ENNReal.summable_toReal (f := fun s => (iidSum (geomP F.p) k) s)
        (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top))
    simp only [hf]; split_ifs <;> simp
  have hsub : ∑ s ∈ S.filter (fun s : ℕ => ¬ |(s : ℝ) - F.mu * k| ≤ rad k), nb F.p k s
      ≤ ∑ s ∈ S, f s := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun s _ => ?_
    simp only [hf]
    rw [show muP F.p = F.mu from rfl]
    by_cases h : |(s : ℝ) - F.mu * k| ≤ rad k
    · rw [if_neg (not_not.mpr h)]; split_ifs <;> simp
    · rw [if_pos h, if_pos (le_of_lt (not_le.mp h))]
      rfl
  have htail := geomP_tail_bound_atC F.two_le_p k (rad k) hrad0
  calc _ ≤ ∑ s ∈ S, f s := hsub
    _ ≤ ∑' s, f s := hfs.sum_le_tsum S (fun s _ => hf0 s)
    _ ≤ C_geomTail * Gweight (1 + k) (c_geomTail * rad k) := htail
    _ ≤ 2 * (2 / (k : ℝ) ^ 2) := by
        rw [C_geomTail]
        exact mul_le_mul_of_nonneg_left (Gweight_rad_le k hk) (by norm_num)
    _ = 4 / (k : ℝ) ^ 2 := by ring

end MasterAux

end ND

end GGMCollatz
