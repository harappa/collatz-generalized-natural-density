import GGMCollatz.General.Reduce
import GGMCollatz.General.Tools

/-!
# Removing (d), reduction 3: rate-preserving transfer (Lemma 3.6 of the paper)

For a family `G` and the family `G* = reduce G d hd` obtained by dividing by a common divisor `d`:

* `sum_bad_le`, `card_bad_le`: write `N = p^k N'` (`p ∤ N'`) and use `C_min(p^k N') ≤ C_min(N')` to move the bad
  points to the bad points `badFree` coprime to `p` (for (A) via `∑_k p^{-k} ≤ 2`, for (B) via `N' ≤ n/p^k`).
* `mapsTo_T`: a bad point `N'` with `p ∤ N'` is mapped to `M = C(N')/d`, which is a bad point of `G*` (with
  threshold `⌊N₀/d⌋`) and satisfies `1 ≤ M ≤ (q + R) N'`.
* `fiber_card_le`: the fibre over a single `M` has at most `p` points (it is determined by the residue `N' mod p`;
  the accompanying paper has `p - 1`).
* `sum_badFree_le`, `card_badFree_le`: `1/N' ≤ ((q+R)/d)/M` and counting the fibres.
* **`transferA`, `transferB`**: (A), (B) for `G` from (A), (B) for `G*`. **The exponent `c` does not change.**

**Deviation from the accompanying paper**: the paper estimates `M ≤ (qY + R)/h` and `1/N' ≤ 2q/(hM)`
(for `M ≥ 2R/h`); here we use `C(N') ≤ (q + R)N'` (from `N' ≥ 1`) to get `M ≤ (q+R)N'/d` and
`1/N' ≤ (q+R)/(dM)` (no case distinction on `M ≥ 2R/h` is needed). The fibre size is bounded by `p` instead of
`p - 1` (this only affects the constant).
-/

namespace GGMCollatz

namespace Gen

open Finset

variable (G : FamilyGen)

/-- The bad points coprime to `p`: `{1 ≤ N ≤ n | p ∤ N, C_min(N) > N₀}`. -/
noncomputable def badFree (N₀ n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun N => N % G.p ≠ 0 ∧ N₀ < G.Cmin N)

lemma mem_badFree {N₀ n N : ℕ} :
    N ∈ badFree G N₀ n ↔ (1 ≤ N ∧ N ≤ n) ∧ N % G.p ≠ 0 ∧ N₀ < G.Cmin N := by
  rw [badFree, mem_filter, mem_Icc]

/-- Write `N ≥ 1` as `p^k N'` (`p ∤ N'`). -/
lemma exists_pow_mul {N : ℕ} (hN : 1 ≤ N) :
    ∃ k N', N' % G.p ≠ 0 ∧ 1 ≤ N' ∧ N = G.p ^ k * N' ∧ k < G.p ^ k ∧ N' * G.p ^ k ≤ N := by
  obtain ⟨k, N', hN'p, rfl⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (n := N) (by omega) G.p (by have := one_lt_p G; omega)
  have hN'0 : N' ≠ 0 := by rintro rfl; simp at hN
  refine ⟨k, N', fun h0 => hN'p (Nat.dvd_of_mod_eq_zero h0), Nat.one_le_iff_ne_zero.mpr hN'0, rfl,
    Nat.lt_pow_self (one_lt_p G), le_of_eq (mul_comm _ _)⟩

/-- **Separating the powers of `p` in (A)**: `∑_{N ≤ n, C_min(N) > N₀} 1/N ≤ 2 ∑_{N' ∈ badFree} 1/N'`. -/
lemma sum_bad_le (N₀ n : ℕ) :
    ∑ N ∈ (Finset.Icc 1 n).filter (fun N => N₀ < G.Cmin N), (1 / (N : ℝ)) ≤
      2 * ∑ N ∈ badFree G N₀ n, (1 / (N : ℝ)) := by
  set S := (Finset.Icc 1 n).filter (fun N => N₀ < G.Cmin N) with hS
  set g : ℕ × ℕ → ℕ := fun kN => G.p ^ kN.1 * kN.2 with hg
  have hsub : S ⊆ (Finset.range (n + 1) ×ˢ badFree G N₀ n).image g := by
    intro N hN
    rw [hS, mem_filter, mem_Icc] at hN
    obtain ⟨⟨hN1, hNn⟩, hbad⟩ := hN
    obtain ⟨k, N', hN'p, hN'1, rfl, hk, hle⟩ := exists_pow_mul G hN1
    rw [mem_image]
    refine ⟨(k, N'), ?_, rfl⟩
    have hpk : 1 ≤ G.p ^ k := Nat.one_le_pow _ _ (p_pos G)
    have h1 : N' ≤ N' * G.p ^ k := Nat.le_mul_of_pos_right _ hpk
    have h2 : G.p ^ k ≤ G.p ^ k * N' := Nat.le_mul_of_pos_right _ hN'1
    rw [mem_product, mem_range, mem_badFree]
    exact ⟨by omega, ⟨hN'1, by omega⟩, hN'p, lt_of_lt_of_le hbad (Cmin_pow_mul_le G k N')⟩
  have hgeom := geom_le_two G.two_le_p (n + 1)
  calc ∑ N ∈ S, (1 / (N : ℝ))
      ≤ ∑ N ∈ (Finset.range (n + 1) ×ˢ badFree G N₀ n).image g, (1 / (N : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ kN ∈ Finset.range (n + 1) ×ˢ badFree G N₀ n, (1 / (g kN : ℝ)) :=
        sum_image_le_of_nonneg (fun _ _ => by positivity)
    _ = ∑ k ∈ Finset.range (n + 1), ∑ N ∈ badFree G N₀ n, ((1 / (G.p : ℝ)) ^ k * (1 / (N : ℝ))) := by
        rw [sum_product]
        refine sum_congr rfl (fun k _ => sum_congr rfl (fun N _ => ?_))
        simp only [hg, Nat.cast_mul, Nat.cast_pow, one_div_pow, one_div_mul_one_div]
    _ = (∑ k ∈ Finset.range (n + 1), (1 / (G.p : ℝ)) ^ k) * ∑ N ∈ badFree G N₀ n, (1 / (N : ℝ)) := by
        rw [sum_mul_sum]
    _ ≤ 2 * ∑ N ∈ badFree G N₀ n, (1 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hgeom (sum_nonneg fun _ _ => by positivity)

/-- **Separating the powers of `p` in (B)**: `#{N ≤ n | C_min(N) > N₀} ≤ ∑_{k ≤ n} #badFree(N₀, ⌊n/p^k⌋)`. -/
lemma card_bad_le (N₀ n : ℕ) :
    ((Finset.Icc 1 n).filter (fun N => N₀ < G.Cmin N)).card ≤
      ∑ k ∈ Finset.range (n + 1), (badFree G N₀ (n / G.p ^ k)).card := by
  have hsub : (Finset.Icc 1 n).filter (fun N => N₀ < G.Cmin N) ⊆
      (Finset.range (n + 1)).biUnion
        (fun k => (badFree G N₀ (n / G.p ^ k)).image (fun N' => G.p ^ k * N')) := by
    intro N hN
    rw [mem_filter, mem_Icc] at hN
    obtain ⟨⟨hN1, hNn⟩, hbad⟩ := hN
    obtain ⟨k, N', hN'p, hN'1, rfl, hk, hle⟩ := exists_pow_mul G hN1
    have h2 : G.p ^ k ≤ G.p ^ k * N' := Nat.le_mul_of_pos_right _ hN'1
    rw [mem_biUnion]
    refine ⟨k, mem_range.mpr (by omega), mem_image.mpr ⟨N', ?_, rfl⟩⟩
    rw [mem_badFree]
    refine ⟨⟨hN'1, (Nat.le_div_iff_mul_le (pow_pos (p_pos G) k)).mpr (by omega)⟩, hN'p,
      lt_of_lt_of_le hbad (Cmin_pow_mul_le G k N')⟩
  calc _ ≤ ((Finset.range (n + 1)).biUnion
        (fun k => (badFree G N₀ (n / G.p ^ k)).image (fun N' => G.p ^ k * N'))).card :=
        card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range (n + 1), ((badFree G N₀ (n / G.p ^ k)).image (fun N' => G.p ^ k * N')).card :=
        card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (n + 1), (badFree G N₀ (n / G.p ^ k)).card :=
        sum_le_sum (fun k _ => card_image_le)

variable {G} {d : ℕ} (hd : CommonDiv G d)

/-- The set of bad points of `G*`: `{1 ≤ M ≤ m | C*_min(M) > ⌊N₀/d⌋}`. -/
noncomputable def badStar (N₀ m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 m).filter (fun M => N₀ / d < (reduce G d hd).Cmin M)

/-- **The map `N' ↦ C(N')/d`** sends `badFree` into `badStar` (Lemma 3.5 (iii) of the paper). -/
lemma mapsTo_badStar {N₀ n m : ℕ} (hm : (G.q + bigR G) * n ≤ m) {N : ℕ}
    (hN : N ∈ badFree G N₀ n) : G.C N / d ∈ badStar hd N₀ m := by
  rw [mem_badFree] at hN
  obtain ⟨⟨hN1, hNn⟩, hNp, hbad⟩ := hN
  have hdC := dvd_C hd hNp
  have hC1 := one_le_C G hNp
  have hCle := C_le G hNp hN1
  have e : G.C N = d * (G.C N / d) := (Nat.mul_div_cancel' hdC).symm
  rw [badStar, mem_filter, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rcases Nat.eq_zero_or_pos (G.C N / d) with h0 | h0
    · rw [h0, mul_zero] at e; omega
    · exact h0
  · calc G.C N / d ≤ G.C N := Nat.div_le_self _ _
      _ ≤ (G.q + bigR G) * N := hCle
      _ ≤ (G.q + bigR G) * n := Nat.mul_le_mul_left _ hNn
      _ ≤ m := hm
  · rw [Nat.div_lt_iff_lt_mul hd.pos]
    calc N₀ < G.Cmin N := hbad
      _ ≤ d * (reduce G d hd).Cmin (G.C N / d) := Cmin_le_mul_Cmin hd hNp
      _ = (reduce G d hd).Cmin (G.C N / d) * d := mul_comm _ _

include hd in
/-- **Fibre size**: at most `p` points of `badFree` are mapped to a single `M` (they are determined by the
residue). -/
lemma fiber_card_le (N₀ n M : ℕ) :
    ((badFree G N₀ n).filter (fun N => G.C N / d = M)).card ≤ G.p := by
  calc _ ≤ (Finset.Ioo 0 G.p).card := by
        apply Finset.card_le_card_of_injOn (fun N => N % G.p)
        · intro N hN
          rw [Finset.mem_coe, mem_filter, mem_badFree] at hN
          rw [Finset.mem_coe, mem_Ioo]
          exact ⟨mod_pos G hN.1.2.1, mod_lt_p G N⟩
        · intro N₁ h₁ N₂ h₂ hmod
          rw [Finset.mem_coe, mem_filter, mem_badFree] at h₁ h₂
          have e₁ : G.C N₁ = d * (G.C N₁ / d) := (Nat.mul_div_cancel' (dvd_C hd h₁.1.2.1)).symm
          have e₂ : G.C N₂ = d * (G.C N₂ / d) := (Nat.mul_div_cancel' (dvd_C hd h₂.1.2.1)).symm
          have hC : G.C N₁ = G.C N₂ := by rw [e₁, e₂, h₁.2, h₂.2]
          exact C_inj_of_mod_eq G h₁.1.2.1 hmod hC
    _ ≤ G.p := by rw [Nat.card_Ioo]; omega

/-- **The core of the transfer for (A)**: `∑_{badFree} 1/N' ≤ p ((q+R)/d) ∑_{badStar} 1/M`. -/
lemma sum_badFree_le (N₀ n m : ℕ) (hm : (G.q + bigR G) * n ≤ m) :
    ∑ N ∈ badFree G N₀ n, (1 / (N : ℝ)) ≤
      (G.p : ℝ) * (((G.q + bigR G : ℕ) : ℝ) / d) * ∑ M ∈ badStar hd N₀ m, (1 / (M : ℝ)) := by
  set Q : ℝ := ((G.q + bigR G : ℕ) : ℝ) / d with hQ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.pos
  have hpt : ∀ N ∈ badFree G N₀ n, 1 / (N : ℝ) ≤ Q * (1 / ((G.C N / d : ℕ) : ℝ)) := by
    intro N hN
    have hM := mapsTo_badStar hd le_rfl hN
    rw [badStar, mem_filter, mem_Icc] at hM
    rw [mem_badFree] at hN
    obtain ⟨⟨hN1, _⟩, hNp, _⟩ := hN
    have hM1 : (1 : ℝ) ≤ ((G.C N / d : ℕ) : ℝ) := by exact_mod_cast hM.1.1
    have e : d * (G.C N / d) = G.C N := Nat.mul_div_cancel' (dvd_C hd hNp)
    have hCle := C_le G hNp hN1
    have key : (d : ℝ) * ((G.C N / d : ℕ) : ℝ) ≤ ((G.q + bigR G : ℕ) : ℝ) * N := by
      have : d * (G.C N / d) ≤ (G.q + bigR G) * N := by rw [e]; exact hCle
      exact_mod_cast this
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [hQ, mul_one_div, div_div, div_le_div_iff₀ hN0 (by positivity)]
    linarith
  calc ∑ N ∈ badFree G N₀ n, (1 / (N : ℝ))
      ≤ ∑ N ∈ badFree G N₀ n, Q * (1 / ((G.C N / d : ℕ) : ℝ)) := sum_le_sum hpt
    _ = Q * ∑ N ∈ badFree G N₀ n, (1 / ((G.C N / d : ℕ) : ℝ)) := by rw [mul_sum]
    _ ≤ Q * ((G.p : ℝ) * ∑ M ∈ badStar hd N₀ m, (1 / (M : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_comp_le (fun N => G.C N / d) (fun M => 1 / (M : ℝ))
          (fun _ _ => by positivity) (fun N hN => mapsTo_badStar hd hm hN) G.p
          (fun M _ => fiber_card_le hd N₀ n M)
    _ = (G.p : ℝ) * Q * ∑ M ∈ badStar hd N₀ m, (1 / (M : ℝ)) := by ring

/-- **The core of the transfer for (B)**: `#badFree ≤ p #badStar`. -/
lemma card_badFree_le (N₀ n m : ℕ) (hm : (G.q + bigR G) * n ≤ m) :
    ((badFree G N₀ n).card : ℝ) ≤ (G.p : ℝ) * ((badStar hd N₀ m).card : ℝ) := by
  have h := sum_comp_le (s := badFree G N₀ n) (t := badStar hd N₀ m) (fun N => G.C N / d)
    (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) (fun N hN => mapsTo_badStar hd hm hN) G.p
    (fun M _ => fiber_card_le hd N₀ n M)
  simpa using h

end Gen

end GGMCollatz
