import GGMCollatz.NatDen.Defs

/-!
# The decomposition for (SUMMIX b): the fibre sum mod `q^m` written via the independence of the first `m` entries and the remaining `k` entries

Let `n = m + k`. `𝒮_n mod q^m = 𝒮_m` is determined by the first `m` entries alone (`castHom_offsetIn`, `offsetIn_truncate`),
and the valuation sum is `s_n = σ₁ + σ₂` (`σ₁` over the first `m`, `σ₂` over the remaining `k`), the two blocks being independent. Hence

`P(𝒮_n ≡ Z (q^m), s_n = s) = Σ_σ P(𝒮_m = Z, σ₁ = σ) · P(s_k = s - σ)` (`fiber_joint`).

From this, the left-hand side of (SUMMIX b) is at most `Σ_σ P(s_m = σ) |P(s_k = s - σ) - P(s_n = s)|` (`lhs_le_reduced`),
and the right-hand side is a quantity depending only on `p` (a convolution of negative binomials). Trivial upper bound `≤ 2 P(s_n = s)` (`reduced_le_two`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace SumMixBAux

/-! ### The truncated negative binomial and convolution -/

/-- The truncated negative binomial `P(s_k = s - σ)` (0 for `σ > s`; ℝ≥0∞ form). -/
noncomputable def fcutE (p k s σ : ℕ) : ℝ≥0∞ :=
  if σ ≤ s then iidSum (geomP p) k (s - σ) else 0

/-- The real form of the truncated negative binomial. -/
noncomputable def fcut (p k s σ : ℕ) : ℝ := if σ ≤ s then nb p k (s - σ) else 0

theorem fcut_eq_toReal (p k s σ : ℕ) : fcut p k s σ = (fcutE p k s σ).toReal := by
  unfold fcut fcutE nb
  split_ifs <;> simp

theorem fcutE_ne_top (p k s σ : ℕ) : fcutE p k s σ ≠ ∞ := by
  unfold fcutE
  split_ifs
  · exact PMF.apply_ne_top _ _
  · exact ENNReal.zero_ne_top

theorem nb_nonneg (p n s : ℕ) : 0 ≤ nb p n s := ENNReal.toReal_nonneg

theorem nb_le_one (p n s : ℕ) : nb p n s ≤ 1 := by
  unfold nb
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact PMF.coe_le_one _ _)

theorem fcut_nonneg (p k s σ : ℕ) : 0 ≤ fcut p k s σ := by
  unfold fcut; split_ifs
  · exact nb_nonneg _ _ _
  · exact le_refl 0

theorem fcut_le_one (p k s σ : ℕ) : fcut p k s σ ≤ 1 := by
  unfold fcut; split_ifs
  · exact nb_le_one _ _ _
  · exact zero_le_one

/-- The mass of the push-forward under a translation. -/
theorem map_add_left_apply (ν : PMF ℕ) (c s : ℕ) :
    (ν.map (c + ·)) s = if c ≤ s then ν (s - c) else 0 := by
  rw [PMF.map_apply]
  split_ifs with h
  · rw [tsum_eq_single (s - c)]
    · rw [if_pos (by omega)]
    · intro b hb
      rw [if_neg (by omega)]
  · refine ENNReal.tsum_eq_zero.mpr fun b => ?_
    rw [if_neg (by omega)]

/-- **Convolution**: `P(s_{m+k} = s) = Σ_σ P(s_m = σ) P(s_k = s - σ)`. -/
theorem iidSum_add_apply (p m k s : ℕ) :
    iidSum (geomP p) (m + k) s = ∑' σ, iidSum (geomP p) m σ * fcutE p k s σ := by
  rw [iidSum_add, PMF.bind_apply]
  refine tsum_congr fun σ => ?_
  rw [map_add_left_apply]
  rfl

/-- The real masses of a `PMF` sum to 1. -/
theorem tsum_toReal_pmf {α : Type*} (ν : PMF α) : ∑' a, (ν a).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun a => PMF.apply_ne_top ν a), PMF.tsum_coe, ENNReal.toReal_one]

theorem summable_toReal_pmf {α : Type*} (ν : PMF α) : Summable fun a => (ν a).toReal :=
  ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)

/-- The real convolution. -/
theorem nb_add_eq_tsum (p m k s : ℕ) :
    nb p (m + k) s = ∑' σ, nb p m σ * fcut p k s σ := by
  unfold nb
  rw [iidSum_add_apply, ENNReal.tsum_toReal_eq
    (fun σ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (fcutE_ne_top _ _ _ _))]
  refine tsum_congr fun σ => ?_
  rw [ENNReal.toReal_mul, fcut_eq_toReal]

/-! ### Splitting an i.i.d. vector -/

/-- An i.i.d. vector splits into front and back blocks: `iid (m+k) = iid m ⊗ iid k` (joined by `Fin.append`). -/
theorem iid_add {α : Type*} (μ : PMF α) (m k : ℕ) :
    μ.iid (m + k) = (μ.iid m).bind fun a => (μ.iid k).map (Fin.append a) := by
  ext v
  rw [PMF.bind_apply, tsum_eq_single (fun i => v (Fin.castAdd k i))]
  · rw [PMF.map_apply, tsum_eq_single (fun j => v (Fin.natAdd m j))]
    · rw [if_pos Fin.append_castAdd_natAdd.symm, PMF.iid_apply_eq_prod, PMF.iid_apply_eq_prod,
        PMF.iid_apply_eq_prod, Fin.prod_univ_add]
    · intro b hb
      rw [if_neg]
      intro h
      apply hb
      funext j
      rw [h, Fin.append_right]
  · intro a ha
    rw [PMF.map_apply, ENNReal.tsum_eq_zero.mpr, mul_zero]
    intro b
    rw [if_neg]
    intro h
    apply ha
    funext i
    rw [h, Fin.append_left]

/-- Splitting the valuation sum. -/
theorem sum_fst_append {m k : ℕ} (a : Fin m → ℕ × ℕ) (b : Fin k → ℕ × ℕ) :
    ∑ i, (Fin.append a b i).1 = ∑ i, (a i).1 + ∑ j, (b j).1 := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- The valuation sum of the i.i.d. one-step law is the sum of `n` copies of `G(μ)`. -/
theorem iid_stepLaw_map_sum (p n : ℕ) :
    ((stepLaw p).iid n).map (fun v => ∑ i, (v i).1) = iidSum (geomP p) n := by
  rw [iidSum, ← iid_stepLaw_map_fst, PMF.map_comp]
  rfl

variable (F : Family)

/-- Modulo `q^m`, the back block has no effect. -/
theorem offsetIn_append {m k : ℕ} (a : Fin m → ℕ × ℕ) (b : Fin k → ℕ × ℕ) :
    F.offsetIn (F.q ^ m) (Fin.append a b) = F.offsetIn (F.q ^ m) a := by
  rw [F.offsetIn_truncate (Nat.le_add_right m k)]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rw [show Fin.castLE (Nat.le_add_right m k) i = Fin.castAdd k i from Fin.ext rfl, Fin.append_left]

/-! ### Marginals of the joint law -/

/-- The fibre sum of the law of `(𝒮_n mod q^m, s_n)` (step (i)). -/
theorem sum_filter_jointSZ (m k : ℕ) (h : m ≤ m + k) (Z : ZMod (F.q ^ m)) (s : ℕ) :
    ∑ Y ∈ Finset.univ.filter (fun Y : ZMod (F.q ^ (m + k)) =>
        ZMod.castHom (pow_dvd_pow F.q h) (ZMod (F.q ^ m)) Y = Z), jointSZ F (m + k) (Y, s)
      = (((stepLaw F.p).iid (m + k)).map
          (fun v => (F.offsetIn (F.q ^ m) v, ∑ i, (v i).1))) (Z, s) := by
  classical
  unfold jointSZ
  simp only [PMF.map_apply]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr fun v => ?_
  have hA : ZMod.castHom (pow_dvd_pow F.q h) (ZMod (F.q ^ m)) (F.offsetIn (F.q ^ (m + k)) v)
      = F.offsetIn (F.q ^ m) v := F.castHom_offsetIn h v
  by_cases hZ : F.offsetIn (F.q ^ m) v = Z
  · rw [Finset.sum_eq_single (F.offsetIn (F.q ^ (m + k)) v)]
    · by_cases hs : s = ∑ i, (v i).1
      · rw [if_pos (by rw [hs]), if_pos (by rw [hs, hZ])]
      · rw [if_neg (fun he => hs (Prod.mk.inj he).2), if_neg (fun he => hs (Prod.mk.inj he).2)]
    · intro Y _ hY
      exact if_neg (fun he => hY (Prod.mk.inj he).1)
    · intro hnot
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ (F.offsetIn (F.q ^ (m + k)) v),
        hA.trans hZ⟩) hnot
  · rw [Finset.sum_eq_zero, if_neg (fun he => hZ (Prod.mk.inj he).1.symm)]
    intro Y hY
    rw [if_neg]
    intro he
    rw [Finset.mem_filter] at hY
    exact hZ (by rw [← hA, ← (Prod.mk.inj he).1]; exact hY.2)

/-- Point mass of a push-forward (with the first component fixed). -/
theorem map_prodMk_apply {β : Type*} [DecidableEq β] (ν : PMF ℕ) (c Z : β) (s : ℕ) :
    (ν.map (fun σ => (c, σ))) (Z, s) = if c = Z then ν s else 0 := by
  classical
  rw [PMF.map_apply]
  split_ifs with h
  · subst h
    rw [tsum_eq_single s]
    · rw [if_pos rfl]
    · intro b hb
      rw [if_neg]
      intro he
      exact hb (Prod.mk.inj he).2.symm
  · refine ENNReal.tsum_eq_zero.mpr fun b => ?_
    rw [if_neg]
    intro he
    exact h (Prod.mk.inj he).1.symm

/-- **Decomposition** (steps (i)–(iv)): `P(𝒮_n ≡ Z (q^m), s_n = s) = Σ_σ P(𝒮_m = Z, σ₁ = σ) P(s_k = s - σ)`. -/
theorem fiber_joint (m k : ℕ) (h : m ≤ m + k) (Z : ZMod (F.q ^ m)) (s : ℕ) :
    ∑ Y ∈ Finset.univ.filter (fun Y : ZMod (F.q ^ (m + k)) =>
        ZMod.castHom (pow_dvd_pow F.q h) (ZMod (F.q ^ m)) Y = Z), jointSZ F (m + k) (Y, s)
      = ∑' σ, jointSZ F m (Z, σ) * fcutE F.p k s σ := by
  classical
  rw [sum_filter_jointSZ F m k h Z s, iid_add, PMF.map_bind, PMF.bind_apply]
  -- rewrite the right-hand side as a sum over the first `m` entries
  have hR : ∑' σ, jointSZ F m (Z, σ) * fcutE F.p k s σ
      = ∑' a : Fin m → ℕ × ℕ, ((stepLaw F.p).iid m) a *
          (if F.offsetIn (F.q ^ m) a = Z then fcutE F.p k s (∑ i, (a i).1) else 0) := by
    unfold jointSZ
    rw [← PMF.tsum_map_mul ((stepLaw F.p).iid m) (fun v => (F.offsetIn (F.q ^ m) v, ∑ i, (v i).1))
      (fun x => if x.1 = Z then fcutE F.p k s x.2 else 0), ENNReal.tsum_prod',
      tsum_eq_single Z]
    · refine tsum_congr fun σ => ?_
      rw [if_pos rfl]
    · intro Z' hZ'
      refine ENNReal.tsum_eq_zero.mpr fun σ => ?_
      rw [if_neg hZ', mul_zero]
  rw [hR]
  refine tsum_congr fun a => ?_
  congr 1
  rw [PMF.map_comp]
  have hcomp : ((fun v : Fin (m + k) → ℕ × ℕ => (F.offsetIn (F.q ^ m) v, ∑ i, (v i).1)) ∘
      Fin.append a) = (fun σ => (F.offsetIn (F.q ^ m) a, σ)) ∘ ((∑ i, (a i).1 + ·) ∘
        (fun b : Fin k → ℕ × ℕ => ∑ j, (b j).1)) := by
    funext b
    simp only [Function.comp_apply]
    rw [offsetIn_append, sum_fst_append]
  rw [hcomp, ← PMF.map_comp, ← PMF.map_comp, iid_stepLaw_map_sum, map_prodMk_apply,
    map_add_left_apply]
  rfl

/-- Marginal (A2): `P(𝒮_m = Z) = Σ_σ P(𝒮_m = Z, s_m = σ)`. -/
theorem syracZ_eq_tsum_joint (m : ℕ) (Z : ZMod (F.q ^ m)) :
    F.syracZ m Z = ∑' σ, jointSZ F m (Z, σ) := by
  classical
  have hmap : F.syracZ m = (jointSZ F m).map Prod.fst := by
    unfold Family.syracZ jointSZ
    rw [PMF.map_comp]
    rfl
  rw [hmap, PMF.map_apply, ENNReal.tsum_prod', tsum_eq_single Z]
  · exact tsum_congr fun σ => if_pos rfl
  · intro Z' hZ'
    exact ENNReal.tsum_eq_zero.mpr fun σ => if_neg (Ne.symm hZ')

/-- Marginal (A3): `Σ_Z P(𝒮_m = Z, s_m = σ) = P(s_m = σ)`. -/
theorem sum_joint_eq_iidSum (m σ : ℕ) :
    ∑ Z : ZMod (F.q ^ m), jointSZ F m (Z, σ) = iidSum (geomP F.p) m σ := by
  classical
  have hmap : iidSum (geomP F.p) m = (jointSZ F m).map Prod.snd := by
    unfold jointSZ
    rw [PMF.map_comp, ← iid_stepLaw_map_sum]
    rfl
  rw [hmap, PMF.map_apply, ENNReal.tsum_prod', tsum_fintype]
  refine Finset.sum_congr rfl fun Z _ => ?_
  rw [tsum_eq_single σ]
  · rw [if_pos rfl]
  · intro σ' hσ'
    rw [if_neg (Ne.symm hσ')]

/-! ### Real form and reduction of the left-hand side -/

theorem jp_nonneg (m : ℕ) (Z : ZMod (F.q ^ m)) (σ : ℕ) : 0 ≤ jp F m Z σ := ENNReal.toReal_nonneg

theorem summable_jp (m : ℕ) (Z : ZMod (F.q ^ m)) : Summable fun σ => jp F m Z σ := by
  unfold jp
  refine ENNReal.summable_toReal ?_
  rw [← syracZ_eq_tsum_joint]
  exact PMF.apply_ne_top _ _

theorem tsum_jp (m : ℕ) (Z : ZMod (F.q ^ m)) :
    ∑' σ, jp F m Z σ = (F.syracZ m Z).toReal := by
  unfold jp
  rw [syracZ_eq_tsum_joint, ENNReal.tsum_toReal_eq (fun σ => PMF.apply_ne_top _ _)]

theorem sum_jp (m σ : ℕ) : ∑ Z : ZMod (F.q ^ m), jp F m Z σ = nb F.p m σ := by
  unfold jp nb
  rw [← sum_joint_eq_iidSum, ENNReal.toReal_sum (fun Z _ => PMF.apply_ne_top _ _)]

/-- The real form of the fibre sum. -/
theorem sum_filter_jp (m k : ℕ) (h : m ≤ m + k) (Z : ZMod (F.q ^ m)) (s : ℕ) :
    ∑ Y ∈ Finset.univ.filter (fun Y : ZMod (F.q ^ (m + k)) =>
        ZMod.castHom (pow_dvd_pow F.q h) (ZMod (F.q ^ m)) Y = Z), jp F (m + k) Y s
      = ∑' σ, jp F m Z σ * fcut F.p k s σ := by
  unfold jp
  rw [← ENNReal.toReal_sum (fun Y _ => PMF.apply_ne_top _ _), fiber_joint F m k h Z s,
    ENNReal.tsum_toReal_eq
      (fun σ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (fcutE_ne_top _ _ _ _))]
  refine tsum_congr fun σ => ?_
  rw [ENNReal.toReal_mul, fcut_eq_toReal]

/-- **Reduction of the left-hand side**: the left-hand side of (SUMMIX b) is `≤ Σ_σ P(s_m = σ) |P(s_k = s - σ) - P(s_n = s)|` (`n = m + k`). -/
theorem lhs_le_reduced (m k : ℕ) (h : m ≤ m + k) (s : ℕ) :
    ∑ Z : ZMod (F.q ^ m),
        |(∑ Y ∈ Finset.univ.filter (fun Y : ZMod (F.q ^ (m + k)) =>
            ZMod.castHom (pow_dvd_pow F.q h) (ZMod (F.q ^ m)) Y = Z), jp F (m + k) Y s)
          - nb F.p (m + k) s * ((F.syracZ m) Z).toReal|
      ≤ ∑' σ, nb F.p m σ * |fcut F.p k s σ - nb F.p (m + k) s| := by
  set b := nb F.p (m + k) s with hb
  have hb0 : 0 ≤ b := nb_nonneg _ _ _
  have hb1 : b ≤ 1 := nb_le_one _ _ _
  -- the bound at each `Z`
  have habs : ∀ σ, |fcut F.p k s σ - b| ≤ 1 := by
    intro σ
    rw [abs_le]
    constructor <;> linarith [fcut_nonneg F.p k s σ, fcut_le_one F.p k s σ]
  have hsumZ : ∀ Z : ZMod (F.q ^ m),
      Summable fun σ => jp F m Z σ * |fcut F.p k s σ - b| := fun Z =>
    Summable.of_nonneg_of_le (fun σ => mul_nonneg (jp_nonneg F m Z σ) (abs_nonneg _))
      (fun σ => mul_le_of_le_one_right (jp_nonneg F m Z σ) (habs σ)) (summable_jp F m Z)
  have hZ : ∀ Z : ZMod (F.q ^ m),
      |(∑ Y ∈ Finset.univ.filter (fun Y : ZMod (F.q ^ (m + k)) =>
            ZMod.castHom (pow_dvd_pow F.q h) (ZMod (F.q ^ m)) Y = Z), jp F (m + k) Y s)
          - b * ((F.syracZ m) Z).toReal|
        ≤ ∑' σ, jp F m Z σ * |fcut F.p k s σ - b| := by
    intro Z
    have hs1 : Summable fun σ => jp F m Z σ * fcut F.p k s σ :=
      Summable.of_nonneg_of_le (fun σ => mul_nonneg (jp_nonneg F m Z σ) (fcut_nonneg _ _ _ _))
        (fun σ => mul_le_of_le_one_right (jp_nonneg F m Z σ) (fcut_le_one _ _ _ _))
        (summable_jp F m Z)
    have hs2 : Summable fun σ => b * jp F m Z σ := (summable_jp F m Z).mul_left b
    rw [sum_filter_jp F m k h Z s, ← tsum_jp, ← tsum_mul_left, ← hs1.tsum_sub hs2]
    have heq : (fun σ => jp F m Z σ * fcut F.p k s σ - b * jp F m Z σ)
        = fun σ => jp F m Z σ * (fcut F.p k s σ - b) := by
      funext σ; ring
    rw [heq]
    have hnorm : Summable fun σ => ‖jp F m Z σ * (fcut F.p k s σ - b)‖ := by
      refine (hsumZ Z).congr fun σ => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (jp_nonneg F m Z σ)]
    calc |∑' σ, jp F m Z σ * (fcut F.p k s σ - b)|
        ≤ ∑' σ, ‖jp F m Z σ * (fcut F.p k s σ - b)‖ := by
          rw [← Real.norm_eq_abs]; exact norm_tsum_le_tsum_norm hnorm
      _ = ∑' σ, jp F m Z σ * |fcut F.p k s σ - b| := by
          refine tsum_congr fun σ => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (jp_nonneg F m Z σ)]
  calc _ ≤ ∑ Z : ZMod (F.q ^ m), ∑' σ, jp F m Z σ * |fcut F.p k s σ - b| :=
        Finset.sum_le_sum fun Z _ => hZ Z
    _ = ∑' σ, ∑ Z : ZMod (F.q ^ m), jp F m Z σ * |fcut F.p k s σ - b| :=
        (Summable.tsum_finsetSum fun Z _ => hsumZ Z).symm
    _ = ∑' σ, nb F.p m σ * |fcut F.p k s σ - b| := by
        refine tsum_congr fun σ => ?_
        rw [← Finset.sum_mul, sum_jp]

/-! ### Trivial upper bound -/

theorem summable_nb (p m : ℕ) : Summable fun σ => nb p m σ := summable_toReal_pmf _

theorem tsum_nb (p m : ℕ) : ∑' σ, nb p m σ = 1 := tsum_toReal_pmf _

/-- Summability of a sum of `nb` with bounded weights. -/
theorem summable_nb_mul {p m : ℕ} {g : ℕ → ℝ} {B : ℝ} (hg0 : ∀ σ, 0 ≤ g σ) (hgB : ∀ σ, g σ ≤ B) :
    Summable fun σ => nb p m σ * g σ :=
  Summable.of_nonneg_of_le (fun σ => mul_nonneg (nb_nonneg _ _ _) (hg0 σ))
    (fun σ => by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hgB σ) (nb_nonneg _ _ _))
    ((summable_nb p m).mul_left B)

/-- **Trivial upper bound**: `Σ_σ P(s_m = σ) |P(s_k = s - σ) - P(s_n = s)| ≤ 2 P(s_n = s)` (from the convolution). -/
theorem reduced_le_two (p m k s : ℕ) :
    ∑' σ, nb p m σ * |fcut p k s σ - nb p (m + k) s| ≤ 2 * nb p (m + k) s := by
  set b := nb p (m + k) s with hb
  have hb0 : 0 ≤ b := nb_nonneg _ _ _
  have hf : Summable fun σ => nb p m σ * fcut p k s σ :=
    summable_nb_mul (fun σ => fcut_nonneg _ _ _ _) (fun σ => fcut_le_one _ _ _ _)
  have hg : Summable fun σ => nb p m σ * b := (summable_nb p m).mul_right b
  have hle : ∀ σ, nb p m σ * |fcut p k s σ - b| ≤ nb p m σ * fcut p k s σ + nb p m σ * b := by
    intro σ
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (nb_nonneg _ _ _)
    rw [abs_le]
    constructor <;> linarith [fcut_nonneg p k s σ]
  have hs : Summable fun σ => nb p m σ * |fcut p k s σ - b| :=
    Summable.of_nonneg_of_le (fun σ => mul_nonneg (nb_nonneg _ _ _) (abs_nonneg _)) hle
      (hf.add hg)
  calc ∑' σ, nb p m σ * |fcut p k s σ - b|
      ≤ ∑' σ, (nb p m σ * fcut p k s σ + nb p m σ * b) := hs.tsum_le_tsum hle (hf.add hg)
    _ = b + b := by
        rw [hf.tsum_add hg, ← nb_add_eq_tsum, tsum_mul_right, tsum_nb, one_mul]
    _ = 2 * b := by ring

end SumMixBAux

end ND

end GGMCollatz
