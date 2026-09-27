import GGMCollatz.NatDen.SumMixA.Step
import GGMCollatz.NatDen.SumMixA.Tele
import GGMCollatz.NatDen.SumMixA.Lower

/-!
# Proposition 6.12 (a) of the paper: assembly

The telescoping of `GGMCollatz/Tao/Sec6/FromDecay.lean` (`osc_syracZ_telescope`), derived from
`TaoCollatz/Sec6/MixingFromDecay.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2, adapted to the density conditioned on the sum.

For `n^{1/4} ≤ m ≤ n` and `|s - μn| ≤ C√(n log n)`,
`Osc_{m,n}(P(𝒮_n = ·, s_n = s)) ≤ Σ_{m ≤ k < n} Osc_{k,k+1}(projS_{k+1}(…))` (`osc_le_sum_of_steps`), and
each term is the oscillation of a nonnegative mixture of the `P(𝒮_{k+1} = ·, s_{k+1} = σ)` (total weight at most 1), hence `≤ K (k+1)^{-B}`
(`osc_proj_jp_le`, `step_bound`). The sum is `≤ K ζ(2) m^{-(B-2)}`. Finally, by the lower bound from (LCLT)
`P(s_n = s) ≥ c₀ n^{-E} ≥ c₀ m^{-4E}` (`n ≤ m⁴`), `m^{-(B-2)} = m^{-A} m^{-4E} ≤ m^{-A} P(s_n = s)/c₀`
(`B = A + 4E + 2`). Small `n` are absorbed by the trivial upper bound `Osc ≤ 2 P(s_n = s)`.
-/

open scoped BigOperators ENNReal

namespace GGMCollatz

namespace ND

namespace SumMixAAux

open Family

variable (F : Family)

/-- The bound for one pair of adjacent levels (a mixture of projections). -/
theorem step_proj_le (K B : ℝ) (hK : 0 < K)
    (hstep : ∀ k σ : ℕ, F.osc k (k + 1) (Nat.le_succ k) (fun Y => jp F (k + 1) Y σ)
      ≤ K * ((k + 1 : ℕ) : ℝ) ^ (-B))
    (k n s : ℕ) (hk : k + 1 ≤ n) :
    F.osc k (k + 1) (Nat.le_succ k) (projS F (k + 1) n hk (fun Y => jp F n Y s))
      ≤ K * ((k + 1 : ℕ) : ℝ) ^ (-B) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine le_trans (osc_proj_jp_le F k d s) ?_
  have hK0 : 0 ≤ K * ((k + 1 : ℕ) : ℝ) ^ (-B) := by positivity
  calc ∑ σ ∈ Finset.range (s + 1),
        nb F.p d (s - σ) * F.osc k (k + 1) (Nat.le_succ k) (fun Y => jp F (k + 1) Y σ)
      ≤ ∑ σ ∈ Finset.range (s + 1), nb F.p d (s - σ) * (K * ((k + 1 : ℕ) : ℝ) ^ (-B)) :=
        Finset.sum_le_sum (fun σ _ =>
          mul_le_mul_of_nonneg_left (hstep k σ) (nb_nonneg F d (s - σ)))
    _ = (∑ σ ∈ Finset.range (s + 1), nb F.p d (s - σ)) * (K * ((k + 1 : ℕ) : ℝ) ^ (-B)) := by
        rw [Finset.sum_mul]
    _ ≤ 1 * (K * ((k + 1 : ℕ) : ℝ) ^ (-B)) := by
        refine mul_le_mul_of_nonneg_right ?_ hK0
        have hrefl : ∑ σ ∈ Finset.range (s + 1), nb F.p d (s - σ)
            = ∑ t ∈ Finset.range (s + 1), nb F.p d t := by
          have := Finset.sum_range_reflect (fun t => nb F.p d t) (s + 1)
          simpa using this
        rw [hrefl]
        exact sum_nb_le_one F d _
    _ = K * ((k + 1 : ℕ) : ℝ) ^ (-B) := one_mul _

/-- Bound for the telescoping sum: `Σ_{m ≤ k < n} K (k+1)^{-B} ≤ K ζ(2) m^{-(B-2)}` (`m ≥ 1`, `B ≥ 2`). -/
theorem sum_steps_le (K B : ℝ) (hK : 0 < K) (hB : 2 ≤ B) (m n : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Ico m n, K * ((k + 1 : ℕ) : ℝ) ^ (-B)
      ≤ K * sZeta2 * (m : ℝ) ^ (-(B - 2)) := by
  have hsummable : Summable (fun k : ℕ => (k : ℝ) ^ (-(2 : ℝ))) := by
    rw [Real.summable_nat_rpow]; norm_num
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  calc ∑ k ∈ Finset.Ico m n, K * ((k + 1 : ℕ) : ℝ) ^ (-B)
      ≤ ∑ k ∈ Finset.Ico m n, K * (m : ℝ) ^ (-(B - 2)) * (k : ℝ) ^ (-(2 : ℝ)) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hmk : m ≤ k := (Finset.mem_Ico.mp hk).1
        have hkpos : (0 : ℝ) < k := hmpos.trans_le (by exact_mod_cast hmk)
        have h1 : ((k + 1 : ℕ) : ℝ) ^ (-B) ≤ (k : ℝ) ^ (-B) :=
          Real.rpow_le_rpow_of_nonpos hkpos (by push_cast; linarith) (by linarith)
        have h2 : (k : ℝ) ^ (-B) = (k : ℝ) ^ (-(B - 2)) * (k : ℝ) ^ (-(2 : ℝ)) := by
          rw [← Real.rpow_add hkpos]; ring_nf
        have h3 : (k : ℝ) ^ (-(B - 2)) ≤ (m : ℝ) ^ (-(B - 2)) :=
          Real.rpow_le_rpow_of_nonpos hmpos (by exact_mod_cast hmk) (by linarith)
        have hk2 : 0 ≤ (k : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        calc K * ((k + 1 : ℕ) : ℝ) ^ (-B) ≤ K * (k : ℝ) ^ (-B) :=
              mul_le_mul_of_nonneg_left h1 hK.le
          _ = K * (k : ℝ) ^ (-(B - 2)) * (k : ℝ) ^ (-(2 : ℝ)) := by rw [h2]; ring
          _ ≤ K * (m : ℝ) ^ (-(B - 2)) * (k : ℝ) ^ (-(2 : ℝ)) := by gcongr
    _ = K * (m : ℝ) ^ (-(B - 2)) * ∑ k ∈ Finset.Ico m n, (k : ℝ) ^ (-(2 : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ K * (m : ℝ) ^ (-(B - 2)) * sZeta2 := by
        gcongr
        exact hsummable.sum_le_tsum (Finset.Ico m n)
          (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = K * sZeta2 * (m : ℝ) ^ (-(B - 2)) := by ring

/-- **Proposition 6.12 (a) of the paper**. -/
theorem summixA (hcf : sumcf_statement F) (hL : lclt_statement F.p) : summixA_statement F := by
  intro A C hA hC
  obtain ⟨c₀, E, hc₀, hE, N₀, hlow⟩ := nb_lower F hL C hC
  set B : ℝ := A + 4 * E + 2 with hBdef
  have hB : 0 < B := by positivity
  obtain ⟨Ks, hKs, hstep⟩ := step_bound F hcf B hB
  set K : ℝ := 2 * (N₀ : ℝ) ^ A + Ks * sZeta2 / c₀ + 1 with hKdef
  have hN₀A : 0 ≤ (N₀ : ℝ) ^ A := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hZ : 0 ≤ sZeta2 := sZeta2_nonneg
  have hK : 0 < K := by positivity
  refine ⟨K, hK, fun n m hmn hn hm s hs => ?_⟩
  -- `m ≥ 1`
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h14 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hmR : (1 : ℝ) ≤ m := h14.trans hm
  have hm1 : 1 ≤ m := by exact_mod_cast hmR
  have hmpos : (0 : ℝ) < m := by linarith
  have hmA : 0 ≤ (m : ℝ) ^ (-A) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hnb : 0 ≤ nb F.p n s := nb_nonneg F n s
  have hbase : 0 ≤ (m : ℝ) ^ (-A) * nb F.p n s := mul_nonneg hmA hnb
  by_cases hnN : n < N₀
  · -- small `n`: `Osc ≤ 2 P(s_n = s)`
    have htriv : F.osc m n hmn (fun Y => jp F n Y s) ≤ 2 * nb F.p n s := by
      refine le_trans (F.osc_le_two_mul_l1 m n hmn _) ?_
      rw [← sum_jp F n s]
      exact le_of_eq (by
        congr 1
        exact Finset.sum_congr rfl (fun Y _ => abs_of_nonneg (jp_nonneg F n Y s)))
    have hmN : (m : ℝ) ≤ N₀ := by exact_mod_cast (le_of_lt (lt_of_le_of_lt hmn hnN))
    have hone : 1 ≤ (N₀ : ℝ) ^ A * (m : ℝ) ^ (-A) := by
      have hpow : (m : ℝ) ^ A ≤ (N₀ : ℝ) ^ A := Real.rpow_le_rpow hmpos.le hmN hA.le
      have : (m : ℝ) ^ A * (m : ℝ) ^ (-A) = 1 := by
        rw [← Real.rpow_add hmpos]; simp
      calc (1 : ℝ) = (m : ℝ) ^ A * (m : ℝ) ^ (-A) := this.symm
        _ ≤ (N₀ : ℝ) ^ A * (m : ℝ) ^ (-A) := mul_le_mul_of_nonneg_right hpow hmA
    calc F.osc m n hmn (fun Y => jp F n Y s) ≤ 2 * nb F.p n s := htriv
      _ ≤ 2 * ((N₀ : ℝ) ^ A * (m : ℝ) ^ (-A)) * nb F.p n s := by nlinarith
      _ = 2 * (N₀ : ℝ) ^ A * ((m : ℝ) ^ (-A) * nb F.p n s) := by ring
      _ ≤ K * ((m : ℝ) ^ (-A) * nb F.p n s) := by
          refine mul_le_mul_of_nonneg_right ?_ hbase
          have : 0 ≤ Ks * sZeta2 / c₀ := by positivity
          linarith
      _ = K * (m : ℝ) ^ (-A) * nb F.p n s := by ring
  · -- large `n`: telescoping
    have hNn : N₀ ≤ n := le_of_not_gt hnN
    have hlow' := hlow n hNn s hs
    -- `m^{-4E} ≤ n^{-E}` from `n ≤ m⁴`
    have hn4 : (n : ℝ) ≤ (m : ℝ) ^ (4 : ℝ) := by
      have h1 : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℝ) = (n : ℝ) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
      rw [← h1]
      exact Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) hm (by norm_num)
    have hnpos : (0 : ℝ) < n := by linarith
    have hm4E : (m : ℝ) ^ (-(4 * E)) ≤ (n : ℝ) ^ (-E) := by
      have : (m : ℝ) ^ (-(4 * E)) = ((m : ℝ) ^ (4 : ℝ)) ^ (-E) := by
        rw [← Real.rpow_mul hmpos.le]; ring_nf
      rw [this]
      exact Real.rpow_le_rpow_of_nonpos hnpos hn4 (by linarith)
    -- telescoping
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have htele := osc_le_sum_of_steps F (fun k => Ks * ((k + 1 : ℕ) : ℝ) ^ (-B)) d m
      (fun Y => jp F (m + d) Y s)
      (fun k hk _ => step_proj_le F Ks B hKs hstep k (m + d) s hk)
    have hsum := sum_steps_le Ks B hKs (by linarith) m (m + d) hm1
    have hBm : (m : ℝ) ^ (-(B - 2)) = (m : ℝ) ^ (-A) * (m : ℝ) ^ (-(4 * E)) := by
      rw [← Real.rpow_add hmpos]; congr 1; rw [hBdef]; ring
    calc F.osc m (m + d) hmn (fun Y => jp F (m + d) Y s)
        ≤ Ks * sZeta2 * (m : ℝ) ^ (-(B - 2)) := htele.trans hsum
      _ = Ks * sZeta2 * ((m : ℝ) ^ (-A) * (m : ℝ) ^ (-(4 * E))) := by rw [hBm]
      _ ≤ Ks * sZeta2 * ((m : ℝ) ^ (-A) * (nb F.p (m + d) s / c₀)) := by
          gcongr
          rw [le_div_iff₀ hc₀]
          calc (m : ℝ) ^ (-(4 * E)) * c₀ ≤ (((m + d : ℕ) : ℝ)) ^ (-E) * c₀ :=
                mul_le_mul_of_nonneg_right hm4E hc₀.le
            _ = c₀ * (((m + d : ℕ) : ℝ)) ^ (-E) := by ring
            _ ≤ nb F.p (m + d) s := hlow'
      _ = (Ks * sZeta2 / c₀) * ((m : ℝ) ^ (-A) * nb F.p (m + d) s) := by
          field_simp
      _ ≤ K * ((m : ℝ) ^ (-A) * nb F.p (m + d) s) := by
          refine mul_le_mul_of_nonneg_right ?_ hbase
          linarith
      _ = K * (m : ℝ) ^ (-A) * nb F.p (m + d) s := by ring

end SumMixAAux

end ND

end GGMCollatz
