import GGMCollatz.NatDen.UProf.Statements
import GGMCollatz.NatDen.UProf.Master.Core
import GGMCollatz.NatDen.UProf.Master.AsympBound

/-!
# (UM) The master formula (Lemma 7.18 of the paper)

For central `s` (`|s - μk| ≤ C₁√(k log k)`) the good-tuple restriction is removed (divide `P(not good) ≪ e^{-cL^{0.2}}` by `P(s_k = s)`),
and non-central `s` are discarded (Chernoff). The weight `ν_{n,s}(X) = #{M ∈ E' | s ∈ Σ(n,M), M ≡ X}` depends on the residue class,
so it is bounded by `q^{-k} ν̄_{n,s} + x^{1/2}` using the flatness (EP2). By the product formula (Proposition 6.12 (c) of the paper),
`P(Σa = s, F_k ≡ X) ≈ P(s_k = s) q^{-(k - m₁)} ω_{m₁}(X)`, `m₁ = ⌊log^{0.4} x⌋`. Finally the non-central `s` are put back into the kernel
(by (EP1), `q^{m₁} Σ ω_{m₁}(M)/M ≪ 1`). The laws of the forward offset and of `jp` (`offsetIn`) agree after reversing the order of the i.i.d. variables.

**Assembly in the formalization** (`NatDen/UProf/Master/`, auxiliary lemmas in the namespace `GGMCollatz.ND.MasterAux`):

* `Master/Prob.lean`: orientation (`jp = jpG(·, True)`, `offsetFwd v = offsetIn (v ∘ rev)`), sums of `jpG`,
  the local bound `P(s_k = s) ≤ C (1+k)^{-1/2}`, and the tail `≤ 4/k²` outside the centre `|s - μk| ≤ R_k = 1600 √(k log k)`.
* `Master/Count.lean`: the averaged form of (EP1), flattening by (EP2), geometric series, and the upper bound `kernC_le` for the kernel restricted to the centre.
* `Master/Rows.lean`: the pointwise triangle inequality, the cost of the good tuples, the cost of non-central `s`.
* `Master/RowSum.lean`: the bound `row_bound` for each row `k` and sum `s`, re-summation of the central `s` into the kernel, the part (P).
* `Master/Core.lean`: the bound `core` at fixed `x` (sum of four errors × `Y`).
* `Master/Asymp.lean`, `Master/AsympBound.lean`: the applicability conditions (`k^{1/4} ≤ m₁ ≤ k^{1/2}` etc.), `Y ≤ 2pZ`,
  and that the sum of the errors is at most `K' L^{-1/5}`.

Differences from the accompanying paper:

* The cost of removing the good-tuple restriction is not divided by `P(s_k = s)` as in the paper; it is bounded directly by
  `Y K₁ P(not good)` using the weight `p^s ≤ Y q^k/M` and (EP1) (`P(not good) ≤ L^{-4}` is `geom_good_tail`). The lower bound of (LCLT) is not needed.
* For the upper bound of the kernel restricted to the centre, instead of the paper's hockey stick and Lemma 7.21, we use the local bound
  `P(s_k = s) ≪ L^{-1/2}` (`k ≥ m₀ ≫ L`), a count of the central window in `k` (width `≪ R log p/d`, `R = R_{n₀} ≪ L^{0.55}`), and the
  geometric series below it (`kernC_le`). Multiplying by the product-formula error `ε₁ ≪ L^{-1/4}` gives `L^{-1/4} L^{-1/2} L^{0.55} = L^{-1/5}`.
* Hence the hypothesis (LCLT) is not used, and `umaster` does not take it as an argument (the local bound and the tail are the
  unconditional `geomP_local_bound`, `geomP_tail_bound_atC`).
-/

namespace GGMCollatz

namespace ND

variable (F : Family)

open MasterAux in
/-- **(UM)**. The hypothesis (LCLT) is not used (the local bound `geomP_local_bound` and the tail
`geomP_tail_bound_atC` suffice), so it is not taken as an argument (removed after a referee pointed it out). -/
theorem umaster (hC : summixC_statement F)
    (h1 : eprimeC_statement F) (h2 : eprimeFlat_statement F) : umaster_statement F := by
  obtain ⟨a₁, ha₁, h1'⟩ := h1
  obtain ⟨a₂, ha₂, h2'⟩ := h2
  refine ⟨min a₁ a₂, lt_min ha₁ ha₂, fun α hα hαa => ?_⟩
  obtain ⟨K₁, hK₁pos, hK₁ev⟩ := h1' α hα (le_trans hαa (min_le_left _ _))
  have hflat := h2' α hα (le_trans hαa (min_le_right _ _))
  obtain ⟨Kc, hKc, hmixC⟩ := hC 1 1600 one_pos (by norm_num)
  obtain ⟨Cl, hCl, hloc⟩ := nb_le_local F
  obtain ⟨K', hK', hasymp⟩ := asymp F hα hK₁pos.le hKc.le hCl.le
  refine ⟨1 / 5, 2 * F.p * K', by norm_num, by
    have : (0 : ℝ) < F.p := F.p_real_pos
    positivity, ?_⟩
  filter_upwards [hK₁ev, hflat, F.geom_good_tail, hasymp, eventually_side F hα,
    Family.eventually_log_ge 1] with x hK hfl hgood has hside hL1
  intro E
  obtain ⟨hx0, hY, hMlo, hm1, hm0, hkc, hZ⟩ := hside
  set m₀ := F.mZero α x with hm₀def
  set n₀ := F.nZero x with hn₀def
  have hm0r : (1 : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hm0
  -- application of the product formula
  have hmix : ∀ k (hk : m1 x ≤ k), m₀ ≤ k → k ≤ n₀ → ∀ s : ℕ,
      |(s : ℝ) - F.mu * k| ≤ rad k →
      ∑ X : ZMod (F.q ^ k), |jp F k X s - nb F.p k s * (F.q : ℝ) ^ ((m1 x : ℤ) - (k : ℤ)) *
          ((F.syracZ (m1 x)) (ZMod.castHom (pow_dvd_pow F.q hk) (ZMod (F.q ^ m1 x)) X)).toReal|
        ≤ epsX F Kc α x * nb F.p k s := by
    intro k hk hk0 hk1 s hs
    obtain ⟨h2k, h14, h12⟩ := hkc k hk0 hk1
    have := hmixC k (m1 x) hk h2k h14 h12 s (by simpa [rad, muP, Family.mu] using hs)
    refine this.trans ?_
    have h := mix_err_le F hKc.le hm0 hk0 hk1
    calc Kc * nb F.p k s * ((m1 x : ℝ) ^ (-1 : ℝ) + Real.sqrt ((m1 x : ℝ) * Real.log k / k))
        = (Kc * ((m1 x : ℝ) ^ (-1 : ℝ) + Real.sqrt ((m1 x : ℝ) * Real.log k / k))) * nb F.p k s := by
          ring
      _ ≤ epsX F Kc α x * nb F.p k s := mul_le_mul_of_nonneg_right h (nb_nonneg _ _ _)
  have htail : ∀ k, m₀ ≤ k → k ≤ n₀ → ∀ S : Finset ℕ,
      ∑ s ∈ S.filter (fun s : ℕ => ¬ |(s : ℝ) - F.mu * k| ≤ rad k), nb F.p k s
        ≤ 4 / (m₀ : ℝ) ^ 2 := by
    intro k hk0 _ S
    refine (nb_tail_cen F k (le_trans hm0 hk0) S).trans ?_
    have hkr : (m₀ : ℝ) ≤ k := by exact_mod_cast hk0
    gcongr
  have hloc' : ∀ k, m₀ ≤ k → k ≤ n₀ → ∀ s, nb F.p k s ≤ Cl / Real.sqrt (1 + m₀) := by
    intro k hk0 _ s
    refine (hloc k s).trans ?_
    have hkr : (m₀ : ℝ) ≤ k := by exact_mod_cast hk0
    gcongr
  have hR : ∀ k, k ≤ n₀ → rad k ≤ rad n₀ := fun k hk => rad_mono hk
  have hε : 0 ≤ epsX F Kc α x := by
    unfold epsX
    have : (0 : ℝ) ≤ (m1 x : ℝ) ^ (-1 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have := Real.sqrt_nonneg ((m1 x : ℝ) * Real.log n₀ / m₀)
    positivity
  have hcore := core F E hx0.le hY hMlo hK hfl hgood hm1 hmix htail hloc' hR hK₁pos.le hε
    (by positivity) (by positivity) (by
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Real.log x) (-4 : ℝ)
      exact this) (by unfold rad; positivity)
  have hLc : 0 ≤ Real.log x ^ (-(1 / 5 : ℝ)) := Real.rpow_nonneg (by linarith) _
  calc |∑ n ∈ rows F α x, umain F α x E n - kernSum F α x E|
      ≤ (x ^ α) ^ α * _ := hcore
    _ ≤ (x ^ α) ^ α * (K' * Real.log x ^ (-(1 / 5 : ℝ))) :=
        mul_le_mul_of_nonneg_left has hY.le
    _ ≤ (2 * F.p * wCard F α x) * (K' * Real.log x ^ (-(1 / 5 : ℝ))) :=
        mul_le_mul_of_nonneg_right hZ (by positivity)
    _ = 2 * F.p * K' * wCard F α x * Real.log x ^ (-(1 / 5 : ℝ)) := by ring

end ND

end GGMCollatz
