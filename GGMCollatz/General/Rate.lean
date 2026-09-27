import GGMCollatz.General.Transfer

/-!
# Removing (d), reduction 4: the rate transfer proper (Lemma 3.6 of the paper)

* **`transferA`**: (A) for `G` from (A) for `G* = reduce G d hd` (with the same exponent `c`).
  For `N₀ ≥ d`, `∑_{N ≤ x, bad} 1/N ≤ 2 ∑_{badFree} ≤ 2p((q+R)/d) ∑_{badStar(⌊(q+R)x⌋)} ≤ 2p((q+R)/d) K*
  ⌊N₀/d⌋^{-c} log((q+R)x)`, with `⌊N₀/d⌋^{-c} ≤ (2d)^c N₀^{-c}` and `log((q+R)x) ≤ (1 + log(q+R)) log x`.
* **`transferB`**: (B) for `G` from (B) for `G*` (with the same exponent `c`).
  `#{N ≤ X, bad} ≤ ∑_k #badFree(⌊n/p^k⌋) ≤ ∑_k p K* (q+R)⌊n/p^k⌋ ⌊N₀/d⌋^{-c} ≤ 2p K* (q+R)(2d)^c X N₀^{-c}`.
* Small `N₀ < d` are absorbed by `mainA_of_large`, `mainB_of_large`.
-/

namespace GGMCollatz

namespace Gen

open Finset

variable {G : FamilyGen} {d : ℕ} (hd : CommonDiv G d)

/-- **Lemma 3.6 (i) of the paper**: (A) for `G` from (A) for `G*`. -/
theorem transferA (h : (reduce G d hd).mainA_gen_statement) : G.mainA_gen_statement := by
  obtain ⟨K, c, hK, hc, hG'⟩ := h
  set Q : ℕ := G.q + bigR G with hQdef
  have hQ2 : 2 ≤ Q := by have := G.two_le_q; omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.pos
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
  apply mainA_of_large G d
    (K := 2 * ((G.p : ℝ) * ((Q : ℝ) / d)) * K * (2 * (d : ℝ)) ^ c * (1 + Real.log Q))
    (by have := Real.log_nonneg hQ1; have : (0 : ℝ) < G.p := by exact_mod_cast p_pos G
        positivity) hc
  intro N₀ _ hdN₀ x hx
  have hx0 : 0 < x := by linarith
  set n := ⌊x⌋₊ with hn
  set m := ⌊(Q : ℝ) * x⌋₊ with hm
  have hnm : Q * n ≤ m := by
    apply Nat.le_floor; push_cast
    exact mul_le_mul_of_nonneg_left (Nat.floor_le hx0.le) (by linarith)
  have hN₀d : 1 ≤ N₀ / d := (Nat.one_le_div_iff hd.pos).mpr hdN₀
  have hQx : 3 ≤ (Q : ℝ) * x := by nlinarith
  have h1 := sum_bad_le G N₀ n
  have h2 := sum_badFree_le hd N₀ n m hnm
  have h3 : ∑ M ∈ badStar hd N₀ m, (1 / (M : ℝ)) ≤
      K * ((N₀ / d : ℕ) : ℝ) ^ (-c) * Real.log ((Q : ℝ) * x) := hG' (N₀ / d) hN₀d _ hQx
  have h4 := rpow_div_le hd.pos hdN₀ hc.le
  have h5 := log_mul_le hQ1 hx
  have hlogQx : 0 ≤ Real.log ((Q : ℝ) * x) := Real.log_nonneg (by linarith)
  have hA : ∑ M ∈ badStar hd N₀ m, (1 / (M : ℝ)) ≤
      K * ((2 * (d : ℝ)) ^ c * (N₀ : ℝ) ^ (-c)) * ((1 + Real.log Q) * Real.log x) := by
    calc _ ≤ K * ((N₀ / d : ℕ) : ℝ) ^ (-c) * Real.log ((Q : ℝ) * x) := h3
      _ ≤ K * ((2 * (d : ℝ)) ^ c * (N₀ : ℝ) ^ (-c)) * ((1 + Real.log Q) * Real.log x) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h4 hK.le) h5 hlogQx
            (mul_nonneg hK.le (by positivity))
  calc ∑ N ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun N => N₀ < G.Cmin N), (1 / (N : ℝ))
      ≤ 2 * ∑ N ∈ badFree G N₀ n, (1 / (N : ℝ)) := h1
    _ ≤ 2 * ((G.p : ℝ) * ((Q : ℝ) / d) * ∑ M ∈ badStar hd N₀ m, (1 / (M : ℝ))) := by
        linarith
    _ ≤ 2 * ((G.p : ℝ) * ((Q : ℝ) / d) *
          (K * ((2 * (d : ℝ)) ^ c * (N₀ : ℝ) ^ (-c)) * ((1 + Real.log Q) * Real.log x))) := by
        gcongr
    _ = 2 * ((G.p : ℝ) * ((Q : ℝ) / d)) * K * (2 * (d : ℝ)) ^ c * (1 + Real.log Q) *
          (N₀ : ℝ) ^ (-c) * Real.log x := by ring

/-- `∑_{k ≤ n} ⌊n/p^k⌋ ≤ 2n`. -/
lemma sum_div_pow_le (p : ℕ) (hp : 2 ≤ p) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), ((n / p ^ k : ℕ) : ℝ) ≤ 2 * n := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  calc _ ≤ ∑ k ∈ Finset.range (n + 1), (n : ℝ) * (1 / (p : ℝ)) ^ k := by
        apply sum_le_sum
        intro k _
        calc ((n / p ^ k : ℕ) : ℝ) ≤ (n : ℝ) / ((p ^ k : ℕ) : ℝ) := Nat.cast_div_le
          _ = (n : ℝ) * (1 / (p : ℝ)) ^ k := by
              rw [Nat.cast_pow, one_div_pow, mul_one_div]
    _ = (n : ℝ) * ∑ k ∈ Finset.range (n + 1), (1 / (p : ℝ)) ^ k := by rw [mul_sum]
    _ ≤ (n : ℝ) * 2 := mul_le_mul_of_nonneg_left (geom_le_two hp _) (Nat.cast_nonneg _)
    _ = 2 * n := mul_comm _ _

/-- **Lemma 3.6 (ii) of the paper**: (B) for `G` from (B) for `G*`. -/
theorem transferB (h : (reduce G d hd).mainB_gen_statement) : G.mainB_gen_statement := by
  obtain ⟨K, c, hK, hc, hG'⟩ := h
  set Q : ℕ := G.q + bigR G with hQdef
  have hQ2 : 2 ≤ Q := by have := G.two_le_q; omega
  have hp0 : (0 : ℝ) < G.p := by exact_mod_cast p_pos G
  apply mainB_of_large G d (K := 2 * (G.p : ℝ) * K * Q * (2 * (d : ℝ)) ^ c)
    (by have : (0 : ℝ) < d := by exact_mod_cast hd.pos
        positivity) hc
  intro N₀ _ hdN₀ X hX
  have hX0 : 0 ≤ X := by linarith
  set n := ⌊X⌋₊ with hn
  have hN₀d : 1 ≤ N₀ / d := (Nat.one_le_div_iff hd.pos).mpr hdN₀
  set t : ℝ := ((N₀ / d : ℕ) : ℝ) ^ (-c) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- Each level: `#badFree(n') ≤ p K (Q n') t`
  have hk : ∀ n' : ℕ, ((badFree G N₀ n').card : ℝ) ≤ (G.p : ℝ) * (K * ((Q * n' : ℕ) : ℝ) * t) := by
    intro n'
    rcases Nat.eq_zero_or_pos n' with h0 | hpos
    · subst h0
      have : badFree G N₀ 0 = ∅ := by
        rw [badFree]; simp
      rw [this, card_empty, Nat.cast_zero]
      positivity
    · have hc1 := card_badFree_le hd N₀ n' (Q * n') le_rfl
      have hX' : (1 : ℝ) ≤ ((Q * n' : ℕ) : ℝ) := by
        have : 1 ≤ Q * n' := Nat.one_le_iff_ne_zero.mpr (by positivity)
        exact_mod_cast this
      have h3 := hG' (N₀ / d) hN₀d ((Q * n' : ℕ) : ℝ) hX'
      rw [Nat.floor_natCast] at h3
      calc ((badFree G N₀ n').card : ℝ) ≤ (G.p : ℝ) * ((badStar hd N₀ (Q * n')).card : ℝ) := hc1
        _ ≤ (G.p : ℝ) * (K * ((Q * n' : ℕ) : ℝ) * t) := by
            apply mul_le_mul_of_nonneg_left _ hp0.le
            exact h3
  have hsum := card_bad_le G N₀ n
  have hgeo := sum_div_pow_le G.p G.two_le_p n
  have h4 := rpow_div_le hd.pos hdN₀ hc.le
  have hnX : (n : ℝ) ≤ X := Nat.floor_le hX0
  calc (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => N₀ < G.Cmin N)).card : ℝ)
      ≤ ∑ k ∈ Finset.range (n + 1), ((badFree G N₀ (n / G.p ^ k)).card : ℝ) := by
        exact_mod_cast hsum
    _ ≤ ∑ k ∈ Finset.range (n + 1), (G.p : ℝ) * (K * ((Q * (n / G.p ^ k) : ℕ) : ℝ) * t) :=
        sum_le_sum (fun k _ => hk _)
    _ = (G.p : ℝ) * K * Q * t * ∑ k ∈ Finset.range (n + 1), ((n / G.p ^ k : ℕ) : ℝ) := by
        rw [mul_sum]
        refine sum_congr rfl (fun k _ => ?_)
        push_cast; ring
    _ ≤ (G.p : ℝ) * K * Q * t * (2 * X) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ ≤ (G.p : ℝ) * K * Q * ((2 * (d : ℝ)) ^ c * (N₀ : ℝ) ^ (-c)) * (2 * X) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        apply mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 2 * (G.p : ℝ) * K * Q * (2 * (d : ℝ)) ^ c * X * (N₀ : ℝ) ^ (-c) := by ring

end Gen

end GGMCollatz
