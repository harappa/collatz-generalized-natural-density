import GGMCollatz.Tao.Basic.Valuation

/-!
# Sums over the box of keys (the counting in Lemma 7.13 (i)(ii) of the paper)

When the key `κ = (b, j) ∈ ℕ^m × ℕ^{m+1}` ranges over the box `[1, B]^m × (0, p)^{m+1}`, the sum of the weights
`p^{-b_{[1,m-1]}} h(b_m)` is bounded by the product of coordinatewise sums:
`Σ_κ p^{-b_{[1,m-1]}} h(b_m) ≤ (p-1)^{m+1} (Σ_{t≥1} p^{-t})^{m-1} Σ_{t=1}^{B} h(t) = (p-1)^2 Σ_{t=1}^B h(t)`.
With `h = 1` this counts the keys (together with `p^{b_{[1,m-1]}} ≤ W`, `Π_x ≤ W (p-1)^2 B`);
with `h(t) = p^{-t-1}(log 4 + t log p)` it gives the main term of `C_k` (the sum `Σ_b (p-1)^{m₀} p^{-|b|} g(b)` in the accompanying paper).
-/

namespace GGMCollatz

namespace ND

namespace EPrimeAux

/-- **The sum over the box**. -/
theorem box_sum {p : ℕ} (hp : 2 ≤ p) (m : ℕ) (hm : 1 ≤ m) (B : ℕ)
    (K : Finset ((Fin m → ℕ) × (Fin (m + 1) → ℕ)))
    (hK : ∀ κ ∈ K, (∀ i, 1 ≤ κ.1 i ∧ κ.1 i ≤ B) ∧ (∀ i, 0 < κ.2 i ∧ κ.2 i < p))
    (h : ℕ → ℝ) (hh : ∀ t, 0 ≤ h t) :
    ∑ κ ∈ K, ((p : ℝ)⁻¹) ^ pre κ.1 (m - 1) * h (κ.1 ⟨m - 1, by omega⟩)
      ≤ ((p : ℝ) - 1) ^ 2 * ∑ t ∈ Finset.Icc 1 B, h t := by
  classical
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hp0 : (0 : ℝ) < p := by linarith
  have hpinv0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hp0.le
  set g : (Fin (m' + 1) → ℕ) → ℝ := fun b => ((p : ℝ)⁻¹) ^ pre b m' * h (b (Fin.last m'))
    with hg
  have hg0 : ∀ b, 0 ≤ g b := fun b => mul_nonneg (pow_nonneg hpinv0 _) (hh _)
  show ∑ κ ∈ K, g κ.1 ≤ _
  set Bbox := Fintype.piFinset (fun _ : Fin (m' + 1) => Finset.Icc 1 B) with hBbox
  set Jbox := Fintype.piFinset (fun _ : Fin (m' + 1 + 1) => Finset.Ioo 0 p) with hJbox
  -- (1) extend to the box
  have hsub : K ⊆ Bbox ×ˢ Jbox := by
    intro κ hκ
    obtain ⟨h1, h2⟩ := hK κ hκ
    rw [Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset]
    exact ⟨fun i => Finset.mem_Icc.mpr (h1 i), fun i => Finset.mem_Ioo.mpr (h2 i)⟩
  have step1 : ∑ κ ∈ K, g κ.1 ≤ ∑ κ ∈ Bbox ×ˢ Jbox, g κ.1 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun κ _ _ => hg0 κ.1)
  -- (2) the size of the box of digits
  have hJcard : (Jbox.card : ℝ) = ((p : ℝ) - 1) ^ (m' + 2) := by
    rw [hJbox, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Nat.card_Ioo, Nat.sub_zero]
    push_cast [show 1 ≤ p by omega]
    ring
  have step2 : ∑ κ ∈ Bbox ×ˢ Jbox, g κ.1 = (Jbox.card : ℝ) * ∑ b ∈ Bbox, g b := by
    rw [Finset.sum_product, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    show ∑ _y ∈ Jbox, g b = _
    rw [Finset.sum_const, nsmul_eq_mul]
  -- (3) the sum over the box of valuations is a product
  set f : Fin (m' + 1) → ℕ → ℝ := fun i t => if (i : ℕ) < m' then ((p : ℝ)⁻¹) ^ t else h t
    with hf
  have hprod : ∀ b : Fin (m' + 1) → ℕ, g b = ∏ i, f i (b i) := by
    intro b
    rw [Fin.prod_univ_castSucc]
    have e1 : ∀ i : Fin m', f i.castSucc (b i.castSucc) = ((p : ℝ)⁻¹) ^ (b i.castSucc) := by
      intro i
      simp only [hf, Fin.val_castSucc, i.isLt, if_true]
    have e2 : f (Fin.last m') (b (Fin.last m')) = h (b (Fin.last m')) := by
      simp only [hf, Fin.val_last, lt_irrefl, if_false]
    rw [Finset.prod_congr rfl (fun i _ => e1 i), e2, Finset.prod_pow_eq_pow_sum]
    have hpre : pre b m' = ∑ i : Fin m', b i.castSucc := by
      rw [← pre_init b le_rfl, pre_eq_fin_sum]; rfl
    show ((p : ℝ)⁻¹) ^ pre b m' * h (b (Fin.last m')) = _
    rw [hpre]
  have step3 : ∑ b ∈ Bbox, g b
      = (∑ t ∈ Finset.Icc 1 B, ((p : ℝ)⁻¹) ^ t) ^ m' * ∑ t ∈ Finset.Icc 1 B, h t := by
    rw [Finset.sum_congr rfl (fun b _ => hprod b), hBbox, ← Finset.prod_univ_sum,
      Fin.prod_univ_castSucc]
    congr 1
    · rw [← Fin.prod_const]
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro t _
      simp only [hf, Fin.val_castSucc, i.isLt, if_true]
    · apply Finset.sum_congr rfl
      intro t _
      simp only [hf, Fin.val_last, lt_irrefl, if_false]
  -- (4) geometric sum
  have hgeom : ∑ t ∈ Finset.Icc 1 B, ((p : ℝ)⁻¹) ^ t ≤ ((p : ℝ) - 1)⁻¹ := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    have hlt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    refine (geom_sum_Ico_le_of_lt_one hpinv0 hlt).trans (le_of_eq ?_)
    field_simp
  have hS0 : 0 ≤ ∑ t ∈ Finset.Icc 1 B, ((p : ℝ)⁻¹) ^ t :=
    Finset.sum_nonneg fun t _ => pow_nonneg hpinv0 t
  have hH0 : 0 ≤ ∑ t ∈ Finset.Icc 1 B, h t := Finset.sum_nonneg fun t _ => hh t
  have hp10 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hprod1 : ((p : ℝ) - 1) * ∑ t ∈ Finset.Icc 1 B, ((p : ℝ)⁻¹) ^ t ≤ 1 := by
    calc ((p : ℝ) - 1) * ∑ t ∈ Finset.Icc 1 B, ((p : ℝ)⁻¹) ^ t
        ≤ ((p : ℝ) - 1) * ((p : ℝ) - 1)⁻¹ := mul_le_mul_of_nonneg_left hgeom hp10.le
      _ = 1 := mul_inv_cancel₀ hp10.ne'
  have hpow1 : (((p : ℝ) - 1) * ∑ t ∈ Finset.Icc 1 B, ((p : ℝ)⁻¹) ^ t) ^ m' ≤ 1 :=
    pow_le_one₀ (mul_nonneg hp10.le hS0) hprod1
  calc ∑ κ ∈ K, g κ.1 ≤ ∑ κ ∈ Bbox ×ˢ Jbox, g κ.1 := step1
    _ = ((p : ℝ) - 1) ^ (m' + 2) *
          ((∑ t ∈ Finset.Icc 1 B, ((p : ℝ)⁻¹) ^ t) ^ m' * ∑ t ∈ Finset.Icc 1 B, h t) := by
        rw [step2, hJcard, step3]
    _ = ((p : ℝ) - 1) ^ 2 *
          ((((p : ℝ) - 1) * ∑ t ∈ Finset.Icc 1 B, ((p : ℝ)⁻¹) ^ t) ^ m'
            * ∑ t ∈ Finset.Icc 1 B, h t) := by rw [mul_pow]; ring
    _ ≤ ((p : ℝ) - 1) ^ 2 * (1 * ∑ t ∈ Finset.Icc 1 B, h t) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hpow1 hH0
    _ = ((p : ℝ) - 1) ^ 2 * ∑ t ∈ Finset.Icc 1 B, h t := by ring

/-- `Σ_{t<n} t 2^{-t} ≤ 2`. -/
theorem sum_mul_half_pow_le (n : ℕ) : ∑ t ∈ Finset.range n, (t : ℝ) * (1 / 2 : ℝ) ^ t ≤ 2 := by
  have key : ∀ n : ℕ, ∑ t ∈ Finset.range n, (t : ℝ) * (1 / 2 : ℝ) ^ t
      = 2 - 2 * ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast
      ring
  rw [key]
  have : 0 ≤ 2 * ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n := by positivity
  linarith

/-- `Σ_{t=1}^{B} p^{-t-1}(log 4 + t log p) ≤ 2(log 4 + log p)`. -/
theorem sum_hC_le {p : ℕ} (hp : 2 ≤ p) (B : ℕ) :
    ∑ t ∈ Finset.Icc 1 B, ((p : ℝ)⁻¹) ^ (t + 1) * (Real.log 4 + t * Real.log p)
      ≤ 2 * (Real.log 4 + Real.log p) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hpinv0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hp0.le
  have hpinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hp2
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  calc ∑ t ∈ Finset.Icc 1 B, ((p : ℝ)⁻¹) ^ (t + 1) * (Real.log 4 + t * Real.log p)
      ≤ ∑ t ∈ Finset.Icc 1 B, (Real.log 4 + Real.log p) * ((t : ℝ) * (1 / 2 : ℝ) ^ t) := by
        apply Finset.sum_le_sum
        intro t ht
        have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (Finset.mem_Icc.mp ht).1
        have hpow : ((p : ℝ)⁻¹) ^ (t + 1) ≤ (1 / 2 : ℝ) ^ t := by
          calc ((p : ℝ)⁻¹) ^ (t + 1) = ((p : ℝ)⁻¹) ^ t * (p : ℝ)⁻¹ := pow_succ _ _
            _ ≤ ((p : ℝ)⁻¹) ^ t * 1 :=
                mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hpinv0 t)
            _ = ((p : ℝ)⁻¹) ^ t := mul_one _
            _ ≤ (1 / 2 : ℝ) ^ t := pow_le_pow_left₀ hpinv0 hpinv t
        have hlin : Real.log 4 + t * Real.log p ≤ t * (Real.log 4 + Real.log p) := by nlinarith
        calc ((p : ℝ)⁻¹) ^ (t + 1) * (Real.log 4 + t * Real.log p)
            ≤ (1 / 2 : ℝ) ^ t * (t * (Real.log 4 + Real.log p)) :=
              mul_le_mul hpow hlin (by positivity) (by positivity)
          _ = (Real.log 4 + Real.log p) * ((t : ℝ) * (1 / 2 : ℝ) ^ t) := by ring
    _ = (Real.log 4 + Real.log p) * ∑ t ∈ Finset.Icc 1 B, (t : ℝ) * (1 / 2 : ℝ) ^ t := by
        rw [Finset.mul_sum]
    _ ≤ (Real.log 4 + Real.log p) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∑ t ∈ Finset.Icc 1 B, (t : ℝ) * (1 / 2 : ℝ) ^ t
            ≤ ∑ t ∈ Finset.range (B + 1), (t : ℝ) * (1 / 2 : ℝ) ^ t := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro t ht
                rw [Finset.mem_Icc] at ht
                rw [Finset.mem_range]
                omega
              · intro t _ _; positivity
          _ ≤ 2 := sum_mul_half_pow_le _
    _ = 2 * (Real.log 4 + Real.log p) := by ring

end EPrimeAux

end ND

end GGMCollatz
