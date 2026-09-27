import GGMCollatz.MainB

/-!
# Corollaries of (B): restatements in terms of densities (Corollary 8.6 of the accompanying paper)

From `FamilyGen.mainB_gen` (for the whole family of GGM's Theorem 1.3, under `MatveevHyp G.p G.q`,
`#{N ≤ X | C_min(N) > N₀} ≤ K X N₀^{-c}`), with the same `K, c`:

* (i) **Upper density**: for every `N₀ ≥ 1`, the upper natural density of `{N | C_min(N) > N₀}`,
  `limsup_{X → ∞} #{1 ≤ N ≤ X | N₀ < C_min(N)}/X`, is at most `K N₀^{-c}` (the ratio lies in `[0, 1]`, so the
  `limsup` is a genuine limit superior of reals; the boundedness is also part of the statement).
* (ii) **Natural density one** (`density_one`): if `f(N) → ∞`, then `{N | C_min(N) < f(N)}` has natural density 1.
  This is the form that GGM §1.3 describes as "still is out of reach" (the natural-density version of GGM's
  Theorem 1.3).
* (iii) The barrier `X^θ`: for `θ > 0` and real `X ≥ 1`, `#{1 ≤ N ≤ X | X^θ < C_min(N)} ≤ 2^c K X^{1-θc}`.
* (iv) The barrier `N^θ`: for `θ > 0`, `θc < 1` and real `X ≥ 1`,
  `#{1 ≤ N ≤ X | N^θ < C_min(N)} ≤ 2^{c(1+θ)} K X^{1-θc}/(1 - 2^{θc-1})`.

The proofs follow the proof of the corollary in the paper (elementary): (iii) takes `N₀ = ⌊X^θ⌋₊ ≥ X^θ/2`; (iv) splits
into the dyadic shells `(X/2^{j+1}, X/2^j]`, applies the form (iii) on each shell (with the barrier `(X/2^{j+1})^θ`),
and sums a geometric series. An `N` with `N^θ < C_min(N)` satisfies `N ≥ 2` (since `C_min(1) ≤ 1`), so
`X/2^{j+1} ≥ 1` on every nonempty shell.
-/

namespace GGMCollatz

namespace FamilyGen

variable (G : FamilyGen)

namespace Cor

/-- `C_min(N) ≤ N`. -/
theorem cmin_le_self (N : ℕ) : G.Cmin N ≤ N := Nat.sInf_le ⟨0, rfl⟩

/-- If `t ≥ 1`, then `t/2 ≤ ⌊t⌋₊`. -/
theorem half_le_floor {t : ℝ} (ht : 1 ≤ t) : t / 2 ≤ (⌊t⌋₊ : ℝ) := by
  have h1 := Nat.sub_one_lt_floor t
  have h2 : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
  have h2' : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast h2
  linarith

/-- The inequality of the main theorem (the body of `mainB_gen_statement`). -/
def MainIneq (K c : ℝ) : Prop :=
  ∀ N₀ : ℕ, 1 ≤ N₀ → ∀ X : ℝ, 1 ≤ X →
    (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => N₀ < G.Cmin N)).card : ℝ) ≤ K * X * (N₀ : ℝ) ^ (-c)

variable {G}

/-- The main theorem at natural numbers `X ≥ 1`: `#{1 ≤ N ≤ X | N₀ < C_min(N)}/X ≤ K N₀^{-c}`. -/
theorem ratio_le {K c : ℝ} (hmain : MainIneq G K c) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) {X : ℕ} (hX : 1 ≤ X) :
    (((Finset.Icc 1 X).filter (fun N => N₀ < G.Cmin N)).card : ℝ) / X ≤ K * (N₀ : ℝ) ^ (-c) := by
  have hX' : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have h := hmain N₀ hN₀ (X : ℝ) hX'
  rw [Nat.floor_natCast] at h
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- **Counting above a barrier `b ≥ 1`**: `#{1 ≤ N ≤ Y | b < C_min(N)} ≤ 2^c K Y b^{-c}` (with
`N₀ = ⌊b⌋₊ ≥ b/2`). -/
theorem count_barrier {K c : ℝ} (hK : 0 < K) (hc : 0 < c) (hmain : MainIneq G K c)
    {Y b : ℝ} (hY : 1 ≤ Y) (hb : 1 ≤ b) :
    (((Finset.Icc 1 ⌊Y⌋₊).filter (fun N => b < (G.Cmin N : ℝ))).card : ℝ)
      ≤ 2 ^ c * K * Y * b ^ (-c) := by
  set N₀ := ⌊b⌋₊ with hN₀
  have hN₀1 : 1 ≤ N₀ := Nat.le_floor (by exact_mod_cast hb)
  have hN₀b : (N₀ : ℝ) ≤ b := Nat.floor_le (by linarith)
  have hhalf : b / 2 ≤ (N₀ : ℝ) := half_le_floor hb
  have hsub : (Finset.Icc 1 ⌊Y⌋₊).filter (fun N => b < (G.Cmin N : ℝ)) ⊆
      (Finset.Icc 1 ⌊Y⌋₊).filter (fun N => N₀ < G.Cmin N) := by
    intro N hN
    rw [Finset.mem_filter] at hN ⊢
    refine ⟨hN.1, ?_⟩
    have : (N₀ : ℝ) < G.Cmin N := lt_of_le_of_lt hN₀b hN.2
    exact_mod_cast this
  have hcard : (((Finset.Icc 1 ⌊Y⌋₊).filter (fun N => b < (G.Cmin N : ℝ))).card : ℝ) ≤
      (((Finset.Icc 1 ⌊Y⌋₊).filter (fun N => N₀ < G.Cmin N)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have h1 := hmain N₀ hN₀1 Y hY
  have hb2 : 0 < b / 2 := by linarith
  have hpow : (N₀ : ℝ) ^ (-c) ≤ (b / 2) ^ (-c) :=
    Real.rpow_le_rpow_of_nonpos hb2 hhalf (by linarith)
  have hdiv : (b / 2) ^ (-c) = 2 ^ c * b ^ (-c) := by
    rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul]
    ring
  have hKY : 0 ≤ K * Y := by positivity
  calc (((Finset.Icc 1 ⌊Y⌋₊).filter (fun N => b < (G.Cmin N : ℝ))).card : ℝ)
      ≤ K * Y * (N₀ : ℝ) ^ (-c) := hcard.trans h1
    _ ≤ K * Y * (b / 2) ^ (-c) := mul_le_mul_of_nonneg_left hpow hKY
    _ = 2 ^ c * K * Y * b ^ (-c) := by rw [hdiv]; ring

/-- `X * (X^θ)^{-c} = X^{1-θc}` (for `X > 0`). -/
theorem mul_rpow_barrier {X θ c : ℝ} (hX : 0 < X) : X * (X ^ θ) ^ (-c) = X ^ (1 - θ * c) := by
  rw [← Real.rpow_mul hX.le, show (1 : ℝ) - θ * c = 1 + θ * (-c) by ring, Real.rpow_add hX,
    Real.rpow_one]

/-- (iii): `#{1 ≤ N ≤ X | X^θ < C_min(N)} ≤ 2^c K X^{1-θc}`. -/
theorem count_Xpow {K c : ℝ} (hK : 0 < K) (hc : 0 < c) (hmain : MainIneq G K c)
    {θ : ℝ} (hθ : 0 < θ) {X : ℝ} (hX : 1 ≤ X) :
    (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => X ^ θ < (G.Cmin N : ℝ))).card : ℝ)
      ≤ 2 ^ c * K * X ^ (1 - θ * c) := by
  have hb : 1 ≤ X ^ θ := Real.one_le_rpow hX hθ.le
  have h := count_barrier hK hc hmain hX hb
  have hX0 : 0 < X := by linarith
  calc _ ≤ 2 ^ c * K * X * (X ^ θ) ^ (-c) := h
    _ = 2 ^ c * K * (X * (X ^ θ) ^ (-c)) := by ring
    _ = 2 ^ c * K * X ^ (1 - θ * c) := by rw [mul_rpow_barrier hX0]

/-- Dyadic shells: if `1 ≤ t ≤ X`, there is `j ≤ ⌊X⌋₊` with `X/2^{j+1} < t ≤ X/2^j`. -/
theorem exists_dyadic {X t : ℝ} (ht1 : 1 ≤ t) (htX : t ≤ X) :
    ∃ j : ℕ, j ≤ ⌊X⌋₊ ∧ X / 2 ^ (j + 1) < t ∧ t ≤ X / 2 ^ j := by
  classical
  have hfl : X / 2 ^ (⌊X⌋₊ + 1) < t := by
    have h1 : X < ((⌊X⌋₊ + 1 : ℕ) : ℝ) := by push_cast; exact Nat.lt_floor_add_one X
    have h2 : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (⌊X⌋₊ + 1) := by
      exact_mod_cast (Nat.lt_two_pow_self).le
    have hpos : (0 : ℝ) < 2 ^ (⌊X⌋₊ + 1) := by positivity
    rw [div_lt_iff₀ hpos]
    nlinarith
  have hex : ∃ j : ℕ, X / 2 ^ (j + 1) < t := ⟨_, hfl⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hfl, Nat.find_spec hex, ?_⟩
  cases hj : Nat.find hex with
  | zero => simpa using htX
  | succ k =>
    have hk : k < Nat.find hex := by omega
    have := Nat.find_min hex hk
    exact not_lt.mp this

/-- `(X/2^j)^s = X^s (2^{-s})^j` (for `X ≥ 0`). -/
theorem div_two_pow_rpow {X : ℝ} (hX : 0 ≤ X) (s : ℝ) (j : ℕ) :
    (X / 2 ^ j) ^ s = X ^ s * ((2 : ℝ) ^ (-s)) ^ j := by
  rw [Real.div_rpow hX (by positivity), ← Real.rpow_natCast (2 : ℝ) j,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
    div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  congr 2
  ring

/-- (iv): if `θc < 1`, then `#{1 ≤ N ≤ X | N^θ < C_min(N)} ≤ 2^{c(1+θ)} K X^{1-θc}/(1 - 2^{θc-1})`. -/
theorem count_Npow {K c : ℝ} (hK : 0 < K) (hc : 0 < c) (hmain : MainIneq G K c)
    {θ : ℝ} (hθ : 0 < θ) (hθc : θ * c < 1) {X : ℝ} (hX : 1 ≤ X) :
    (((Finset.Icc 1 ⌊X⌋₊).filter (fun N : ℕ => (N : ℝ) ^ θ < (G.Cmin N : ℝ))).card : ℝ)
      ≤ 2 ^ (c * (1 + θ)) * K * X ^ (1 - θ * c) / (1 - 2 ^ (θ * c - 1)) := by
  classical
  have hX0 : 0 < X := by linarith
  set B := (Finset.Icc 1 ⌊X⌋₊).filter (fun N : ℕ => (N : ℝ) ^ θ < (G.Cmin N : ℝ)) with hB
  set s : ℝ := 1 - θ * c with hs
  set r : ℝ := (2 : ℝ) ^ (θ * c - 1) with hr
  set A : ℝ := 2 ^ (c * (1 + θ)) * K * X ^ s with hA
  have hA0 : 0 ≤ A := by positivity
  -- the shells `S j = B ∩ (X/2^{j+1}, X/2^j]`
  set S : ℕ → Finset ℕ := fun j =>
    B.filter (fun N => X / 2 ^ (j + 1) < (N : ℝ) ∧ (N : ℝ) ≤ X / 2 ^ j) with hS
  -- the elements of `B` are at least `2` (`C_min(1) ≤ 1 = 1^θ`)
  have hB2 : ∀ N ∈ B, 2 ≤ N := by
    intro N hN
    rw [hB, Finset.mem_filter, Finset.mem_Icc] at hN
    obtain ⟨⟨h1, -⟩, h2⟩ := hN
    by_contra hlt
    have hN1 : N = 1 := by omega
    subst hN1
    have h3 : (G.Cmin 1 : ℝ) ≤ 1 := by exact_mod_cast cmin_le_self G 1
    rw [Nat.cast_one, Real.one_rpow] at h2
    linarith
  -- cover `B` by the shells
  have hcover : B ⊆ (Finset.range (⌊X⌋₊ + 1)).biUnion S := by
    intro N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (by norm_num) (hB2 N hN)
    have hNX : (N : ℝ) ≤ X := by
      have := hN
      rw [hB, Finset.mem_filter, Finset.mem_Icc] at this
      exact le_trans (by exact_mod_cast this.1.2) (Nat.floor_le hX0.le)
    obtain ⟨j, hjle, hlo, hhi⟩ := exists_dyadic hN1 hNX
    rw [Finset.mem_biUnion]
    refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
    rw [hS, Finset.mem_filter]
    exact ⟨hN, hlo, hhi⟩
  -- the bound on each shell
  have hshell : ∀ j : ℕ, ((S j).card : ℝ) ≤ A * r ^ j := by
    intro j
    have hYpos : 0 < X / 2 ^ j := by positivity
    have hArj : 0 ≤ A * r ^ j := by positivity
    rcases (S j).eq_empty_or_nonempty with he | ⟨N, hN⟩
    · rw [he, Finset.card_empty, Nat.cast_zero]; exact hArj
    · set Y := X / 2 ^ j with hY
      have hN' := hN
      rw [hS, Finset.mem_filter] at hN'
      obtain ⟨hNB, -, hhi⟩ := hN'
      have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hB2 N hNB
      have hY2 : 2 ≤ Y := le_trans h2 hhi
      have hY1 : 1 ≤ Y / 2 := by linarith
      have hhalfY : X / 2 ^ (j + 1) = Y / 2 := by rw [hY, pow_succ]; ring
      have hsub : S j ⊆ (Finset.Icc 1 ⌊Y⌋₊).filter (fun M => (Y / 2) ^ θ < (G.Cmin M : ℝ)) := by
        intro M hM
        rw [hS, Finset.mem_filter] at hM
        obtain ⟨hMB, hMlo, hMhi⟩ := hM
        rw [hB, Finset.mem_filter, Finset.mem_Icc] at hMB
        rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨hMB.1.1, Nat.le_floor hMhi⟩, ?_⟩
        rw [hhalfY] at hMlo
        calc (Y / 2) ^ θ < (M : ℝ) ^ θ := Real.rpow_lt_rpow (by linarith) hMlo hθ
          _ < G.Cmin M := hMB.2
      have hb : 1 ≤ (Y / 2) ^ θ := Real.one_le_rpow hY1 hθ.le
      have hcnt := count_barrier (Y := Y) hK hc hmain (by linarith) hb
      have e1 : ((Y / 2) ^ θ) ^ (-c) = Y ^ (θ * (-c)) * 2 ^ (θ * c) := by
        rw [← Real.rpow_mul (by linarith), Real.div_rpow (by linarith) (by norm_num),
          show θ * -c = -(θ * c) by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
      have e2 : Y * Y ^ (θ * (-c)) = Y ^ s := by
        rw [hs, show (1 : ℝ) - θ * c = 1 + θ * (-c) by ring, Real.rpow_add (by linarith),
          Real.rpow_one]
      have e3 : (2 : ℝ) ^ c * 2 ^ (θ * c) = 2 ^ (c * (1 + θ)) := by
        rw [← Real.rpow_add (by norm_num), show c + θ * c = c * (1 + θ) by ring]
      have e4 : Y ^ s = X ^ s * r ^ j := by
        rw [hY, div_two_pow_rpow hX0.le, hr, hs, show -(1 - θ * c) = θ * c - 1 by ring]
      calc ((S j).card : ℝ)
          ≤ (((Finset.Icc 1 ⌊Y⌋₊).filter (fun M => (Y / 2) ^ θ < (G.Cmin M : ℝ))).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ 2 ^ c * K * Y * ((Y / 2) ^ θ) ^ (-c) := hcnt
        _ = (2 ^ c * 2 ^ (θ * c)) * K * (Y * Y ^ (θ * (-c))) := by rw [e1]; ring
        _ = A * r ^ j := by rw [e2, e3, e4, hA]; ring
  -- sum over the shells
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeom : ∑ j ∈ Finset.range (⌊X⌋₊ + 1), r ^ j ≤ 1 / (1 - r) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := ⌊X⌋₊ + 1) hr0 hr1
    rw [← Finset.range_eq_Ico, pow_zero] at this
    exact this
  have h1r : 0 < 1 - r := by linarith
  calc (B.card : ℝ)
      ≤ (((Finset.range (⌊X⌋₊ + 1)).biUnion S).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ j ∈ Finset.range (⌊X⌋₊ + 1), ((S j).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.range (⌊X⌋₊ + 1), A * r ^ j := Finset.sum_le_sum fun j _ => hshell j
    _ = A * ∑ j ∈ Finset.range (⌊X⌋₊ + 1), r ^ j := by rw [Finset.mul_sum]
    _ ≤ A * (1 / (1 - r)) := mul_le_mul_of_nonneg_left hgeom hA0
    _ = 2 ^ (c * (1 + θ)) * K * X ^ (1 - θ * c) / (1 - 2 ^ (θ * c - 1)) := by
        rw [hA, hs, hr]; ring

end Cor

open Cor

open Classical in
/-- **Corollaries of (B)** ((i), (iii), (iv) of Corollary 8.6 of the paper): for every family of GGM's Theorem 1.3,
under `MatveevHyp G.p G.q`, there are `K, c > 0` such that the inequality of the main theorem holds, and with the
same `K, c`:

* (i) upper natural density: for every `N₀ ≥ 1`, the ratio `#{1 ≤ N ≤ X | N₀ < C_min(N)}/X` (`X ∈ ℕ`) is bounded
  above, and its `limsup_{X → ∞}` is at most `K N₀^{-c}`;
* (iii) for every `θ > 0` and real `X ≥ 1`, `#{1 ≤ N ≤ X | X^θ < C_min(N)} ≤ 2^c K X^{1-θc}`;
* (iv) for `θ > 0`, `θc < 1` and real `X ≥ 1`,
  `#{1 ≤ N ≤ X | N^θ < C_min(N)} ≤ 2^{c(1+θ)} K X^{1-θc}/(1 - 2^{θc-1})`.

(ii) (natural density one) is `FamilyGen.density_one`. -/
theorem corollaries (G : FamilyGen) (hM : MatveevHyp G.p G.q) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
      (∀ N₀ : ℕ, 1 ≤ N₀ → ∀ X : ℝ, 1 ≤ X →
        (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => N₀ < G.Cmin N)).card : ℝ)
          ≤ K * X * (N₀ : ℝ) ^ (-c)) ∧
      (∀ N₀ : ℕ, 1 ≤ N₀ →
        Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
          (fun X : ℕ => (((Finset.Icc 1 X).filter (fun N => N₀ < G.Cmin N)).card : ℝ) / X) ∧
        Filter.limsup
          (fun X : ℕ => (((Finset.Icc 1 X).filter (fun N => N₀ < G.Cmin N)).card : ℝ) / X)
          Filter.atTop ≤ K * (N₀ : ℝ) ^ (-c)) ∧
      (∀ θ : ℝ, 0 < θ → ∀ X : ℝ, 1 ≤ X →
        (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => X ^ θ < (G.Cmin N : ℝ))).card : ℝ)
          ≤ 2 ^ c * K * X ^ (1 - θ * c)) ∧
      (∀ θ : ℝ, 0 < θ → θ * c < 1 → ∀ X : ℝ, 1 ≤ X →
        (((Finset.Icc 1 ⌊X⌋₊).filter (fun N : ℕ => (N : ℝ) ^ θ < (G.Cmin N : ℝ))).card : ℝ)
          ≤ 2 ^ (c * (1 + θ)) * K * X ^ (1 - θ * c) / (1 - 2 ^ (θ * c - 1))) := by
  obtain ⟨K, c, hK, hc, hmain⟩ := G.mainB_gen hM
  refine ⟨K, c, hK, hc, hmain, fun N₀ hN₀ => ?_, fun θ hθ X hX => count_Xpow hK hc hmain hθ hX,
    fun θ hθ hθc X hX => count_Npow hK hc hmain hθ hθc hX⟩
  have hev : ∀ᶠ X : ℕ in Filter.atTop,
      (((Finset.Icc 1 X).filter (fun N => N₀ < G.Cmin N)).card : ℝ) / X ≤ K * (N₀ : ℝ) ^ (-c) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with X hX
    exact ratio_le hmain hN₀ hX
  refine ⟨Filter.isBoundedUnder_of_eventually_le hev, ?_⟩
  exact Filter.limsup_le_of_le
    (Filter.isCoboundedUnder_le_of_le Filter.atTop fun X => by positivity) hev

/-- **Corollary (ii) of (B): natural density one** (Corollary 8.6 (ii) of the paper; the form that GGM §1.3
describes as "still is out of reach"). For every family of GGM's Theorem 1.3, under `MatveevHyp G.p G.q`, if
`f(N) → ∞`, then `#{1 ≤ N ≤ X | C_min(N) < f(N)}/X → 1` (as `X → ∞`, `X ∈ ℕ`). -/
theorem density_one (G : FamilyGen) (hM : MatveevHyp G.p G.q) (f : ℕ → ℝ)
    (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun X : ℕ => (((Finset.Icc 1 X).filter (fun N => (G.Cmin N : ℝ) < f N)).card : ℝ) / X)
      Filter.atTop (nhds 1) := by
  classical
  obtain ⟨K, c, hK, hc, hmain⟩ := G.mainB_gen hM
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- an `N₀ ≥ 1` with `K N₀^{-c} < ε/2`
  have hlim : Filter.Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-c)) Filter.atTop (nhds 0) := by
    have h := ((tendsto_rpow_neg_atTop hc).comp tendsto_natCast_atTop_atTop).const_mul K
    rw [mul_zero] at h
    exact h
  obtain ⟨N₀, hN₀ε, hN₀1⟩ :=
    ((hlim.eventually (Iio_mem_nhds (half_pos hε))).and (Filter.eventually_ge_atTop 1)).exists
  have hN₀ε' : K * (N₀ : ℝ) ^ (-c) < ε / 2 := hN₀ε
  -- `f(N) ≥ N₀ + 1` for `N ≥ N₁`
  obtain ⟨N₁, hN₁⟩ := Filter.tendsto_atTop_atTop.mp hf ((N₀ : ℝ) + 1)
  -- the `X` with `N₁/X < ε/2`
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp
    (((tendsto_const_div_atTop_nhds_zero_nat (N₁ : ℝ)).eventually
      (Iio_mem_nhds (half_pos hε))).and (Filter.eventually_ge_atTop 1))
  refine ⟨X₀, fun X hX => ?_⟩
  obtain ⟨hN₁X, hX1⟩ := hX₀ X hX
  have hN₁X' : (N₁ : ℝ) / X < ε / 2 := hN₁X
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  set T := Finset.Icc 1 X with hT
  set A := T.filter (fun N => (G.Cmin N : ℝ) < f N) with hA
  set Bc := T.filter (fun N => ¬ (G.Cmin N : ℝ) < f N) with hBc
  have hsplit : A.card + Bc.card = X := by
    rw [hA, hBc, Finset.card_filter_add_card_filter_not, hT, Nat.card_Icc]
    omega
  -- the complement lies in `[1, N₁] ∪ {N₀ < C_min}`
  have hsub : Bc ⊆ Finset.Icc 1 N₁ ∪ T.filter (fun N => N₀ < G.Cmin N) := by
    intro N hN
    rw [hBc, Finset.mem_filter] at hN
    obtain ⟨hNT, hNf⟩ := hN
    rw [Finset.mem_union]
    by_cases hNN : N < N₁
    · left
      rw [hT, Finset.mem_Icc] at hNT
      rw [Finset.mem_Icc]
      exact ⟨hNT.1, hNN.le⟩
    · right
      rw [Finset.mem_filter]
      refine ⟨hNT, ?_⟩
      have h1 := hN₁ N (not_lt.mp hNN)
      have h2 : (N₀ : ℝ) < G.Cmin N := by
        have := not_lt.mp hNf
        linarith
      exact_mod_cast h2
  have hBcard : (Bc.card : ℝ) ≤ N₁ + K * X * (N₀ : ℝ) ^ (-c) := by
    have h1 : Bc.card ≤ N₁ + (T.filter (fun N => N₀ < G.Cmin N)).card := by
      calc Bc.card ≤ (Finset.Icc 1 N₁ ∪ T.filter (fun N => N₀ < G.Cmin N)).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.Icc 1 N₁).card + (T.filter (fun N => N₀ < G.Cmin N)).card :=
            Finset.card_union_le _ _
        _ = N₁ + (T.filter (fun N => N₀ < G.Cmin N)).card := by rw [Nat.card_Icc]; omega
    have h2 := hmain N₀ hN₀1 (X : ℝ) (by exact_mod_cast hX1)
    rw [Nat.floor_natCast] at h2
    have h1' : (Bc.card : ℝ) ≤ N₁ + ((T.filter (fun N => N₀ < G.Cmin N)).card : ℝ) := by
      exact_mod_cast h1
    linarith
  -- `|A/X - 1| = Bc/X < ε`
  have hAeq : (A.card : ℝ) = X - Bc.card := by
    have : ((A.card + Bc.card : ℕ) : ℝ) = X := by exact_mod_cast hsplit
    push_cast at this
    linarith
  rw [Real.dist_eq, hAeq, show ((X : ℝ) - Bc.card) / X - 1 = -((Bc.card : ℝ) / X) by
    field_simp; ring, abs_neg, abs_of_nonneg (by positivity)]
  calc (Bc.card : ℝ) / X ≤ (N₁ + K * X * (N₀ : ℝ) ^ (-c)) / X :=
        div_le_div_of_nonneg_right hBcard hXpos.le
    _ = N₁ / X + K * (N₀ : ℝ) ^ (-c) := by field_simp
    _ < ε / 2 + ε / 2 := add_lt_add hN₁X' hN₀ε'
    _ = ε := by ring

end FamilyGen

end GGMCollatz
