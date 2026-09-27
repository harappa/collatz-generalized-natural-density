import GGMCollatz.NatDen.UProf.URD.Count

/-!
# Auxiliary for (URD): the discrepancy of window replacement (row by row)

The row-wise bound of the lemma on the discrepancy of window replacement in the accompanying paper. Notation: `Q = q^k`, `B = rBound`,
`Δ = QB` (since `|fint| ≤ p^{|a|} Q B`, `|F_k(v)| ≤ Δ`), `s = |a|`.

1. **Localization** (`endpoint`, `ind_sub_le`): `1[y ≤ N_{v,M} ≤ Y]` and `1[y < p^s M/Q ≤ Y]` disagree only if
   `|M - eQ/p^s| ≤ Δ` for an endpoint `e ∈ {y, Y}`.
2. **Counting** (`card_near_le`): if `E' ⊂ [Mlo, ∞)` and `2Δ ≤ Mlo`, then
   `#{M ∈ E' | |M - c| ≤ Δ} ≤ (2Δ + 1)·(2c/Mlo)` (if the set is nonempty, then `c ≥ Mlo/2`).
3. **Summing with the model mass** (`row_disc`): since `c = eQ/p^s`, each tuple `v` contributes `≤ (2Δ+1)(2eQ/Mlo) p^{-s}`, and
   from `Σ_{v ∈ box} p^{-s} ≤ 1` (`sum_box_inv_le`) the discrepancy of a row is `≤ 4(2Δ+1) Q Y/Mlo`.

The paper's proof uses (IRR), the local bound and (EP2); none of them is used here: for each `(k, s)` the disagreeing `M` number
`O(Δ)`, and their weight `p^s/Q ≈ Y/M ≤ 2Y/Mlo` is small (`≪ Y x^{-1/2}` with `Δ ≪ x^{1/5}`, `Mlo ≥ x^{9/10}`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace URDAux

variable (F : Family)

/-- **Endpoint lemma**: if the truth values of `b ∈ [y, Y]` and `a ∈ (y, Y]` differ, then one of the endpoints is within
`|a - b|` of `a`. -/
theorem endpoint {a b y Y : ℝ} (h : ¬((y ≤ b ∧ b ≤ Y) ↔ (y < a ∧ a ≤ Y))) :
    |a - y| ≤ |a - b| ∨ |a - Y| ≤ |a - b| := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  apply h
  have k1 := neg_abs_le (a - b)
  have k2 := le_abs_self (a - b)
  rcases le_or_gt a y with hay | hay
  · rw [abs_of_nonpos (by linarith : a - y ≤ 0)] at h1
    constructor
    · rintro ⟨hyb, -⟩; exfalso; linarith
    · rintro ⟨hya, -⟩; exfalso; linarith
  · rw [abs_of_pos (by linarith : 0 < a - y)] at h1
    rcases le_or_gt a Y with haY | haY
    · rw [abs_of_nonpos (by linarith : a - Y ≤ 0)] at h2
      exact ⟨fun _ => ⟨hay, haY⟩, fun _ => ⟨by linarith, by linarith⟩⟩
    · rw [abs_of_pos (by linarith : 0 < a - Y)] at h2
      constructor
      · rintro ⟨-, hbY⟩; exfalso; linarith
      · rintro ⟨-, haY'⟩; exfalso; linarith

open Classical in
/-- **Localization**: for a valid tuple `v`, the difference of the two window indicators is bounded by the sum of the endpoint-proximity indicators. -/
theorem ind_sub_le {k : ℕ} {y Y : ℝ} {v : Fin k → ℕ × ℕ} (hv : F.validVec v) (M : ℕ) (A A' : Prop)
    [Decidable A] [Decidable A'] :
    |(if (A ∧ A' ∧ winN F y Y v M) then (1 : ℝ) else 0)
        - (if (A ∧ A' ∧ inWin F y Y k (sOf v) M) then (1 : ℝ) else 0)|
      ≤ (if |(M : ℝ) - y * (F.q : ℝ) ^ k / (F.p : ℝ) ^ sOf v| ≤ (F.q : ℝ) ^ k * F.rBound
          then (1 : ℝ) else 0)
        + (if |(M : ℝ) - Y * (F.q : ℝ) ^ k / (F.p : ℝ) ^ sOf v| ≤ (F.q : ℝ) ^ k * F.rBound
          then (1 : ℝ) else 0) := by
  have hq : (0 : ℝ) < (F.q : ℝ) ^ k := pow_pos F.q_real_pos k
  have hps : (0 : ℝ) < (F.p : ℝ) ^ sOf v := pow_pos F.p_real_pos _
  have hnn : ∀ P : Prop, (0 : ℝ) ≤ (if P then (1 : ℝ) else 0) := fun P => by
    split_ifs <;> norm_num
  set a : ℝ := (F.p : ℝ) ^ sOf v * M / (F.q : ℝ) ^ k with hadef
  set b : ℝ := ((F.p : ℝ) ^ sOf v * M - (fOf F v : ℝ)) / (F.q : ℝ) ^ k with hbdef
  -- `|a - b| = |f|/Q ≤ p^s B`
  have hab : |a - b| ≤ (F.p : ℝ) ^ sOf v * F.rBound := by
    have : a - b = (fOf F v : ℝ) / (F.q : ℝ) ^ k := by
      rw [hadef, hbdef]; field_simp; ring
    rw [this, abs_div, abs_of_pos hq, div_le_iff₀ hq]
    have := abs_fOf_le F hv
    linarith
  -- if the endpoint `e` is near `a`, then `|M - eQ/p^s| ≤ QB`
  have hnear : ∀ e : ℝ, |a - e| ≤ |a - b| →
      |(M : ℝ) - e * (F.q : ℝ) ^ k / (F.p : ℝ) ^ sOf v| ≤ (F.q : ℝ) ^ k * F.rBound := by
    intro e he
    have hid : (M : ℝ) - e * (F.q : ℝ) ^ k / (F.p : ℝ) ^ sOf v
        = (F.q : ℝ) ^ k / (F.p : ℝ) ^ sOf v * (a - e) := by
      rw [hadef]; field_simp
    rw [hid, abs_mul, abs_of_pos (div_pos hq hps)]
    calc (F.q : ℝ) ^ k / (F.p : ℝ) ^ sOf v * |a - e|
        ≤ (F.q : ℝ) ^ k / (F.p : ℝ) ^ sOf v * ((F.p : ℝ) ^ sOf v * F.rBound) :=
          mul_le_mul_of_nonneg_left (le_trans he hab) (div_pos hq hps).le
      _ = (F.q : ℝ) ^ k * F.rBound := by field_simp
  by_cases hA : A ∧ A'
  · have hw : winN F y Y v M ↔ (y ≤ b ∧ b ≤ Y) := Iff.rfl
    have hi : inWin F y Y k (sOf v) M ↔ (y < a ∧ a ≤ Y) := Iff.rfl
    by_cases heq : (y ≤ b ∧ b ≤ Y) ↔ (y < a ∧ a ≤ Y)
    · have : (A ∧ A' ∧ winN F y Y v M) ↔ (A ∧ A' ∧ inWin F y Y k (sOf v) M) := by
        rw [hw, hi, heq]
      rw [if_congr this rfl rfl, sub_self, abs_zero]
      exact add_nonneg (hnn _) (hnn _)
    · have hdiff : |(if (A ∧ A' ∧ winN F y Y v M) then (1 : ℝ) else 0)
          - (if (A ∧ A' ∧ inWin F y Y k (sOf v) M) then (1 : ℝ) else 0)| ≤ 1 := by
        split_ifs <;> norm_num
      rcases endpoint heq with he | he
      · rw [if_pos (hnear y he)]
        linarith [hnn (|(M : ℝ) - Y * (F.q : ℝ) ^ k / (F.p : ℝ) ^ sOf v|
          ≤ (F.q : ℝ) ^ k * F.rBound)]
      · rw [if_pos (hnear Y he)]
        linarith [hnn (|(M : ℝ) - y * (F.q : ℝ) ^ k / (F.p : ℝ) ^ sOf v|
          ≤ (F.q : ℝ) ^ k * F.rBound)]
  · rw [if_neg (fun h => hA ⟨h.1, h.2.1⟩), if_neg (fun h => hA ⟨h.1, h.2.1⟩), sub_self, abs_zero]
    exact add_nonneg (hnn _) (hnn _)

/-- The number of natural numbers in the real interval `[c - Δ, c + Δ]` is at most `2Δ + 1`. -/
theorem card_near_le_aux (S : Finset ℕ) (c Δ : ℝ) (hΔ : 0 ≤ Δ) :
    ((S.filter (fun M : ℕ => |(M : ℝ) - c| ≤ Δ)).card : ℝ) ≤ 2 * Δ + 1 := by
  rcases lt_or_ge (c + Δ) 0 with hneg | hpos
  · have : S.filter (fun M : ℕ => |(M : ℝ) - c| ≤ Δ) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro M _ hM
      have := (abs_le.mp hM).2
      have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      linarith
    rw [this, Finset.card_empty, Nat.cast_zero]
    linarith
  · have hsub : S.filter (fun M : ℕ => |(M : ℝ) - c| ≤ Δ) ⊆ Finset.Icc ⌈c - Δ⌉₊ ⌊c + Δ⌋₊ := by
      intro M hM
      rw [Finset.mem_filter] at hM
      obtain ⟨h1, h2⟩ := abs_le.mp hM.2
      rw [Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hpos]
      constructor <;> linarith
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have hc1 : (⌊c + Δ⌋₊ : ℝ) ≤ c + Δ := Nat.floor_le hpos
    have hc2 : c - Δ ≤ (⌈c - Δ⌉₊ : ℝ) := Nat.le_ceil _
    calc ((S.filter (fun M : ℕ => |(M : ℝ) - c| ≤ Δ)).card : ℝ)
        ≤ ((⌊c + Δ⌋₊ + 1 - ⌈c - Δ⌉₊ : ℕ) : ℝ) := by exact_mod_cast hcard
      _ ≤ 2 * Δ + 1 := by
          rcases le_or_gt ⌈c - Δ⌉₊ (⌊c + Δ⌋₊ + 1) with hle | hlt
          · rw [Nat.cast_sub hle]; push_cast; linarith
          · rw [Nat.sub_eq_zero_of_le hlt.le, Nat.cast_zero]; linarith

/-- **Counting**: if `E' ⊂ [Mlo, ∞)`, `0 < Mlo`, `2Δ ≤ Mlo`, `0 ≤ c`, then
`#{M ∈ E' | |M - c| ≤ Δ} ≤ (2Δ+1)(2c/Mlo)`. -/
theorem card_near_le (S : Finset ℕ) {Mlo c Δ : ℝ} (hMlo : 0 < Mlo) (hΔ : 0 ≤ Δ)
    (hΔM : 2 * Δ ≤ Mlo) (hc0 : 0 ≤ c) (hS : ∀ M ∈ S, Mlo ≤ M) :
    ((S.filter (fun M : ℕ => |(M : ℝ) - c| ≤ Δ)).card : ℝ) ≤ (2 * Δ + 1) * (2 * c / Mlo) := by
  rcases (S.filter (fun M : ℕ => |(M : ℝ) - c| ≤ Δ)).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.card_empty, Nat.cast_zero]
    positivity
  · obtain ⟨M, hM⟩ := hne
    rw [Finset.mem_filter] at hM
    have hcM := (abs_le.mp hM.2).2
    have hMl := hS M hM.1
    have hc : Mlo / 2 ≤ c := by linarith
    have h1 := card_near_le_aux S c Δ hΔ
    have h2 : (1 : ℝ) ≤ 2 * c / Mlo := by
      rw [le_div_iff₀ hMlo]; linarith
    calc ((S.filter (fun M : ℕ => |(M : ℝ) - c| ≤ Δ)).card : ℝ) ≤ 2 * Δ + 1 := h1
      _ = (2 * Δ + 1) * 1 := by ring
      _ ≤ (2 * Δ + 1) * (2 * c / Mlo) := mul_le_mul_of_nonneg_left h2 (by positivity)

open Classical in
/-- **Row discrepancy** (the row-wise form of the window-replacement lemma): if `E' ⊂ [Mlo, ∞)`, `0 < y ≤ Y`, `2QB ≤ Mlo`, then
`|Σ_{M,v} 1[…, N_{v,M} ∈ [y,Y]] - Σ_{M,v} 1[…, |a| ∈ Σ(n,M)]| ≤ 4(2QB + 1) Q Y/Mlo` (`Q = q^k`). -/
theorem row_disc {k T : ℕ} {y Y Mlo : ℝ} (hy : 0 < y) (hyY : y ≤ Y) (hMlo : 0 < Mlo)
    (E' : Finset ℕ) (G : (Fin k → ℕ) → Prop)
    (hE : ∀ M ∈ E', Mlo ≤ M) (hΔ : 2 * ((F.q : ℝ) ^ k * F.rBound) ≤ Mlo) :
    |(∑ M ∈ E', ∑ v ∈ box F k T,
          if (F.offsetFwd v = (M : ZMod (F.q ^ k)) ∧ G (fun i => (v i).1) ∧ winN F y Y v M)
          then (1 : ℝ) else 0)
        - ∑ M ∈ E', ∑ v ∈ box F k T,
          if (F.offsetFwd v = (M : ZMod (F.q ^ k)) ∧ G (fun i => (v i).1) ∧
              inWin F y Y k (sOf v) M)
          then (1 : ℝ) else 0|
      ≤ 4 * (2 * ((F.q : ℝ) ^ k * F.rBound) + 1) * (F.q : ℝ) ^ k * Y / Mlo := by
  set Q : ℝ := (F.q : ℝ) ^ k with hQdef
  set Δ : ℝ := Q * F.rBound with hΔdef
  have hQ : 0 < Q := pow_pos F.q_real_pos k
  have hB : (0 : ℝ) ≤ F.rBound := by exact_mod_cast F.rBound_nonneg
  have hΔ0 : 0 ≤ Δ := mul_nonneg hQ.le hB
  -- the proximity indicators
  set ind : ℝ → (Fin k → ℕ × ℕ) → ℕ → ℝ := fun e v M =>
    if |(M : ℝ) - e * Q / (F.p : ℝ) ^ sOf v| ≤ Δ then (1 : ℝ) else 0 with hind
  have hind_card : ∀ (e : ℝ) (v : Fin k → ℕ × ℕ), 0 ≤ e →
      ∑ M ∈ E', ind e v M ≤ (2 * Δ + 1) * (2 * (e * Q / (F.p : ℝ) ^ sOf v) / Mlo) := by
    intro e v he
    have hps : (0 : ℝ) < (F.p : ℝ) ^ sOf v := pow_pos F.p_real_pos _
    rw [hind]
    simp only
    rw [Finset.sum_boole]
    exact card_near_le E' hMlo hΔ0 hΔ (by positivity) hE
  rw [← Finset.sum_sub_distrib]
  calc |∑ M ∈ E', ((∑ v ∈ box F k T,
          if (F.offsetFwd v = (M : ZMod (F.q ^ k)) ∧ G (fun i => (v i).1) ∧ winN F y Y v M)
          then (1 : ℝ) else 0)
        - ∑ v ∈ box F k T,
          if (F.offsetFwd v = (M : ZMod (F.q ^ k)) ∧ G (fun i => (v i).1) ∧
              inWin F y Y k (sOf v) M)
          then (1 : ℝ) else 0)|
      ≤ ∑ M ∈ E', ∑ v ∈ box F k T, (ind y v M + ind Y v M) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun M _ => ?_)
        rw [← Finset.sum_sub_distrib]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun v hv => ?_)
        exact ind_sub_le F (valid_of_mem_box F hv) M _ _
    _ = ∑ v ∈ box F k T, (∑ M ∈ E', ind y v M + ∑ M ∈ E', ind Y v M) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_add_distrib]
    _ ≤ ∑ v ∈ box F k T, (2 * Δ + 1) * (2 / Mlo) * (y + Y) * Q * ((F.p : ℝ) ^ sOf v)⁻¹ := by
        refine Finset.sum_le_sum fun v _ => ?_
        have h1 := hind_card y v hy.le
        have h2 := hind_card Y v (le_trans hy.le hyY)
        have hps : (0 : ℝ) < (F.p : ℝ) ^ sOf v := pow_pos F.p_real_pos _
        have heq : (2 * Δ + 1) * (2 * (y * Q / (F.p : ℝ) ^ sOf v) / Mlo)
            + (2 * Δ + 1) * (2 * (Y * Q / (F.p : ℝ) ^ sOf v) / Mlo)
            = (2 * Δ + 1) * (2 / Mlo) * (y + Y) * Q * ((F.p : ℝ) ^ sOf v)⁻¹ := by
          field_simp
        linarith
    _ = (2 * Δ + 1) * (2 / Mlo) * (y + Y) * Q * ∑ v ∈ box F k T, ((F.p : ℝ) ^ sOf v)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (2 * Δ + 1) * (2 / Mlo) * (y + Y) * Q * 1 := by
        apply mul_le_mul_of_nonneg_left (sum_box_inv_le F k T)
        have : 0 ≤ y + Y := by linarith
        positivity
    _ ≤ 4 * (2 * Δ + 1) * Q * Y / Mlo := by
        rw [mul_one]
        have hyY2 : y + Y ≤ 2 * Y := by linarith
        have h0 : 0 ≤ (2 * Δ + 1) * (2 / Mlo) * Q := by positivity
        calc (2 * Δ + 1) * (2 / Mlo) * (y + Y) * Q
            = (2 * Δ + 1) * (2 / Mlo) * Q * (y + Y) := by ring
          _ ≤ (2 * Δ + 1) * (2 / Mlo) * Q * (2 * Y) := mul_le_mul_of_nonneg_left hyY2 h0
          _ = 4 * (2 * Δ + 1) * Q * Y / Mlo := by field_simp; ring

end URDAux

end ND

end GGMCollatz
