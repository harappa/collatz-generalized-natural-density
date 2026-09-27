import GGMCollatz.NatDen.UProf.EPrime.Class
import GGMCollatz.NatDen.UProf.EPrime.Box

/-!
# The number `Π_x` of prefix classes and the boundedness of `C_k` (Lemma 7.13 (i)(ii) of the paper)

* `card_keys_le`: `Π_x = #{key(M) | M ∈ E'} ≤ W (p-1)^2 Bmax ≤ x^{1/2}` (under `Good`).
* `class_sum_le`: on one class `κ = (b, j)`, adding `M ≡ X (q^k)` gives one residue class mod `Q_b = p^{|b|+1} q^k`
  ((a) and the Chinese remainder theorem), contained in `[max(L_b, Mlo), 4p^{b_m} max(L_b, Mlo)]`, so
  `q^k Σ 1/M ≤ q^k/Mlo + p^{-|b|-1} log(4 p^{b_m})` (`sum_inv_le_of_modEq`).
* `cE_le_of_good`: summing over classes, `C_k(X) ≤ Π_x q^k/Mlo + (p-1)^2 Σ_t p^{-t-1}(log 4 + t log p)
  ≤ 1 + 2(p-1)^2(log 4 + log p)`.
-/

namespace GGMCollatz

namespace ND

namespace EPrimeAux

open Family

variable (F : Family)

/-- The set `Π_x` of keys (the nonempty prefix classes). -/
noncomputable def keys (α x : ℝ) :
    Finset ((Fin (F.mZero α x) → ℕ) × (Fin (F.mZero α x + 1) → ℕ)) :=
  (F.Eprime α x Set.univ).image (key F (F.mZero α x))

/-- The weight of the main term of `C_k`, `h(t) = p^{-t-1}(log 4 + t log p)`. -/
noncomputable def hC (t : ℕ) : ℝ := ((F.p : ℝ)⁻¹) ^ (t + 1) * (Real.log 4 + t * Real.log F.p)

/-- The constant `1 + 2(p-1)^2(log 4 + log p)` in the upper bound for `C_k`. -/
noncomputable def Kc : ℝ := 1 + ((F.p : ℝ) - 1) ^ 2 * (2 * (Real.log 4 + Real.log F.p))

theorem log_four_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)

theorem Kc_pos : 0 < Kc F := by
  have h4 := log_four_nonneg
  have hp := F.log_p_pos
  have : 0 ≤ ((F.p : ℝ) - 1) ^ 2 * (2 * (Real.log 4 + Real.log F.p)) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  unfold Kc
  linarith

theorem hC_nonneg (t : ℕ) : 0 ≤ hC F t := by
  have h4 := log_four_nonneg
  have hp := F.log_p_pos
  have hpinv : (0 : ℝ) ≤ (F.p : ℝ)⁻¹ := inv_nonneg.mpr F.p_real_pos.le
  unfold hC
  exact mul_nonneg (pow_nonneg hpinv _) (by positivity)

/-- The ranges of the key's components (`key_bounds` on the set of keys). -/
theorem keys_bounds {α x : ℝ} (hG : Good F α x) :
    ∀ κ ∈ keys F α x, (∀ i, 1 ≤ κ.1 i ∧ κ.1 i ≤ Bmax F α x) ∧ (∀ i, 0 < κ.2 i ∧ κ.2 i < F.p) := by
  intro κ hκ
  obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hκ
  exact key_bounds F hG hM

/-- **`Π_x ≤ x^{1/2}`**. -/
theorem card_keys_le {α x : ℝ} (hG : Good F α x) : ((keys F α x).card : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
  have hm := hG.one_le_m
  have hx0 : 0 < x := by linarith [hG.one_le_x]
  have hW0 : 0 ≤ Wb F α x := by unfold Wb Family.Mhi; positivity
  have hbox := box_sum F.two_le_p (F.mZero α x) hm (Bmax F α x) (keys F α x) (keys_bounds F hG)
    (fun _ => (1 : ℝ)) (fun _ => zero_le_one)
  have hone : ∀ κ ∈ keys F α x,
      (1 : ℝ) ≤ Wb F α x * (((F.p : ℝ)⁻¹) ^ pre κ.1 (F.mZero α x - 1) * 1) := by
    intro κ hκ
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hκ
    have h := pow_pre_le_W F hG hM
    have hP : (0 : ℝ) < (F.p : ℝ) ^ pre (key F (F.mZero α x) M).1 (F.mZero α x - 1) := by
      have := F.p_real_pos; positivity
    rw [mul_one, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hP, one_mul]
    exact h
  calc ((keys F α x).card : ℝ) = ∑ _κ ∈ keys F α x, (1 : ℝ) := by simp
    _ ≤ ∑ κ ∈ keys F α x, Wb F α x * (((F.p : ℝ)⁻¹) ^ pre κ.1 (F.mZero α x - 1) * 1) :=
        Finset.sum_le_sum hone
    _ = Wb F α x * ∑ κ ∈ keys F α x, ((F.p : ℝ)⁻¹) ^ pre κ.1 (F.mZero α x - 1) * 1 := by
        rw [Finset.mul_sum]
    _ ≤ Wb F α x * (((F.p : ℝ) - 1) ^ 2 * ∑ _t ∈ Finset.Icc 1 (Bmax F α x), (1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hbox hW0
    _ = Wb F α x * ((F.p : ℝ) - 1) ^ 2 * (Bmax F α x : ℝ) := by simp; ring
    _ ≤ x ^ (1 / 2 : ℝ) := hG.count

/-- If `k ≤ n₀`, then `q^k ≤ x^{1/5}` (`x ≥ 1`). -/
theorem q_pow_le {x : ℝ} (hx : 1 ≤ x) {k : ℕ} (hk : k ≤ F.nZero x) :
    (F.q : ℝ) ^ k ≤ x ^ (1 / 5 : ℝ) := by
  have hq := F.log_q_pos
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hn0 : (F.nZero x : ℝ) ≤ Real.log x / (5 * Real.log F.q) := by
    unfold Family.nZero; exact Nat.floor_le (by positivity)
  have hkR : (k : ℝ) ≤ F.nZero x := by exact_mod_cast hk
  have h1 : (k : ℝ) * Real.log F.q ≤ Real.log x / 5 := by
    calc (k : ℝ) * Real.log F.q ≤ Real.log x / (5 * Real.log F.q) * Real.log F.q :=
          mul_le_mul_of_nonneg_right (le_trans hkR hn0) hq.le
      _ = Real.log x / 5 := by field_simp
  rw [← Real.exp_log F.q_real_pos, ← Real.exp_nat_mul, Real.rpow_def_of_pos (by linarith)]
  apply Real.exp_le_exp.mpr
  linarith

/-- **The harmonic sum over one class**. -/
theorem class_sum_le {α x : ℝ} (hG : Good F α x) {k : ℕ} (X : ZMod (F.q ^ k))
    (κ : (Fin (F.mZero α x) → ℕ) × (Fin (F.mZero α x + 1) → ℕ)) :
    (F.q : ℝ) ^ k * ∑ M ∈ ((F.Eprime α x Set.univ).filter
        (fun M : ℕ => ((M : ℕ) : ZMod (F.q ^ k)) = X)).filter
          (fun M => key F (F.mZero α x) M = κ), (M : ℝ)⁻¹
      ≤ (F.q : ℝ) ^ k / F.Mlo α x + ((F.p : ℝ)⁻¹) ^ pre κ.1 (F.mZero α x - 1) *
          hC F (κ.1 ⟨F.mZero α x - 1, Nat.sub_lt hG.one_le_m Nat.one_pos⟩) := by
  have hm := hG.one_le_m
  have hp0 : (0 : ℝ) < F.p := F.p_real_pos
  have hq0 : (0 : ℝ) < F.q := F.q_real_pos
  set S := ((F.Eprime α x Set.univ).filter
    (fun M : ℕ => ((M : ℕ) : ZMod (F.q ^ k)) = X)).filter
      (fun M => key F (F.mZero α x) M = κ) with hSdef
  set A := pre κ.1 (F.mZero α x - 1) with hA
  set t := κ.1 ⟨F.mZero α x - 1, Nat.sub_lt hG.one_le_m Nat.one_pos⟩ with ht
  have hpre : pre κ.1 (F.mZero α x) = A + t := pre_last hm κ.1
  set Lb : ℝ := x * (F.p : ℝ) ^ A / (2 * (F.q : ℝ) ^ (F.mZero α x - 1)) with hLb
  set a : ℝ := max Lb (F.Mlo α x) with ha_def
  have hMlo0 : 0 < F.Mlo α x := Real.exp_pos _
  have ha : 0 < a := lt_of_lt_of_le hMlo0 (le_max_right _ _)
  have hpt : (1 : ℝ) ≤ (F.p : ℝ) ^ t := one_le_pow₀ (by linarith [F.one_lt_p_real])
  set b : ℝ := a * (4 * (F.p : ℝ) ^ t) with hb
  have hab : a ≤ b := le_mul_of_one_le_right ha.le (by linarith)
  have hmemS : ∀ M ∈ S, M ∈ F.Eprime α x Set.univ ∧ key F (F.mZero α x) M = κ ∧
      ((M : ℕ) : ZMod (F.q ^ k)) = X := by
    intro M hM
    simp only [hSdef, Finset.mem_filter] at hM
    exact ⟨hM.1.1, hM.2, hM.1.2⟩
  -- each element lies in `[a, b]`
  have hbound : ∀ M ∈ S, a ≤ (M : ℝ) ∧ (M : ℝ) ≤ b := by
    intro M hM
    obtain ⟨hME, hkey, -⟩ := hmemS M hM
    obtain ⟨-, -, -, -, hlo⟩ := basic_of_mem F hG hME
    have hl := lower_bound F hG hME
    have hu := upper_bound F hG hME
    rw [hkey] at hl hu
    rw [hpre, pow_add] at hu
    have hq1 : (0 : ℝ) < 2 * (F.q : ℝ) ^ (F.mZero α x - 1) := by positivity
    have hLbM : Lb ≤ M := by rw [hLb, div_le_iff₀ hq1]; linarith
    refine ⟨max_le hLbM hlo, ?_⟩
    have hqm : (0 : ℝ) < (F.q : ℝ) ^ (F.mZero α x - 1) := by positivity
    have h4 : (M : ℝ) ≤ 4 * (F.p : ℝ) ^ t * Lb := by
      have e : 4 * (F.p : ℝ) ^ t * Lb
          = (2 * x * ((F.p : ℝ) ^ A * (F.p : ℝ) ^ t)) / (F.q : ℝ) ^ (F.mZero α x - 1) := by
        rw [hLb]; field_simp; ring
      rw [e, le_div_iff₀ hqm]
      linarith
    calc (M : ℝ) ≤ 4 * (F.p : ℝ) ^ t * Lb := h4
      _ ≤ 4 * (F.p : ℝ) ^ t * a := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      _ = b := by rw [hb]; ring
  -- congruent mod `Q = p^{|b|+1} q^k`
  set Q : ℕ := F.p ^ (pre κ.1 (F.mZero α x) + 1) * F.q ^ k with hQ
  have hQpos : 0 < Q := Nat.mul_pos (pow_pos F.p_pos _) (pow_pos F.q_pos _)
  have hcong : ∀ M ∈ S, ∀ M' ∈ S, M % Q = M' % Q := by
    intro M hM M' hM'
    obtain ⟨hME, hkey, hX⟩ := hmemS M hM
    obtain ⟨hME', hkey', hX'⟩ := hmemS M' hM'
    have hp := (basic_of_mem F hG hME).1
    have hp' := (basic_of_mem F hG hME').1
    have h1 := modEq_of_key_eq F hp hp' (hkey.trans hkey'.symm)
    rw [hkey] at h1
    have h2 : M ≡ M' [MOD F.q ^ k] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp (hX.trans hX'.symm)
    have hcop : Nat.Coprime (F.p ^ (pre κ.1 (F.mZero α x) + 1)) (F.q ^ k) :=
      Nat.Coprime.pow _ _ F.coprime
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩
  have hsum := sum_inv_le_of_modEq hQpos ha S b hab hbound hcong
  -- computation
  have hba : b / a = 4 * (F.p : ℝ) ^ t := by rw [hb]; field_simp
  have hlog : Real.log (b / a) = Real.log 4 + t * Real.log F.p := by
    rw [hba, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have hQR : (Q : ℝ) = (F.p : ℝ) ^ (A + t + 1) * (F.q : ℝ) ^ k := by
    rw [hQ, hpre]; push_cast; ring
  have hqk : (0 : ℝ) < (F.q : ℝ) ^ k := by positivity
  have hmain : (F.q : ℝ) ^ k * (Real.log (b / a) / (Q : ℝ))
      = ((F.p : ℝ)⁻¹) ^ A * hC F t := by
    rw [hlog, hQR]
    unfold hC
    rw [inv_pow, inv_pow, pow_add, pow_add, pow_add]
    field_simp
  calc (F.q : ℝ) ^ k * ∑ M ∈ S, (M : ℝ)⁻¹
      ≤ (F.q : ℝ) ^ k * (a⁻¹ + Real.log (b / a) / (Q : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum hqk.le
    _ = (F.q : ℝ) ^ k / a + (F.q : ℝ) ^ k * (Real.log (b / a) / (Q : ℝ)) := by
        ring
    _ = (F.q : ℝ) ^ k / a + ((F.p : ℝ)⁻¹) ^ A * hC F t := by rw [hmain]
    _ ≤ (F.q : ℝ) ^ k / F.Mlo α x + ((F.p : ℝ)⁻¹) ^ A * hC F t := by
        have := div_le_div_of_nonneg_left hqk.le hMlo0 (le_max_right Lb (F.Mlo α x))
        linarith

/-- **(EP1) `C_k(X) ≤ Kc`** (`Good`, `k ≤ n₀`). -/
theorem cE_le_of_good {α x : ℝ} (hG : Good F α x) {k : ℕ} (hk : k ≤ F.nZero x)
    (X : ZMod (F.q ^ k)) : F.cE α x Set.univ k X ≤ Kc F := by
  have hm := hG.one_le_m
  have hMlo0 : 0 < F.Mlo α x := Real.exp_pos _
  unfold Family.cE
  set E1 := (F.Eprime α x Set.univ).filter (fun M : ℕ => ((M : ℕ) : ZMod (F.q ^ k)) = X)
    with hE1
  have hmaps : ∀ M ∈ E1, key F (F.mZero α x) M ∈ keys F α x := by
    intro M hM
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hM).1
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  have h1 := Finset.sum_le_sum (fun κ (_ : κ ∈ keys F α x) => class_sum_le F hG X κ)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
  -- first term: `Π_x q^k / Mlo ≤ 1`
  have hc := card_keys_le F hG
  have hqk := q_pow_le F hG.one_le_x hk
  have hfirst : ((keys F α x).card : ℝ) * ((F.q : ℝ) ^ k / F.Mlo α x) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hMlo0]
    calc ((keys F α x).card : ℝ) * (F.q : ℝ) ^ k ≤ x ^ (1 / 2 : ℝ) * x ^ (1 / 5 : ℝ) :=
          mul_le_mul hc hqk (by positivity) (Real.rpow_nonneg (by linarith [hG.one_le_x]) _)
      _ ≤ F.Mlo α x := hG.small
  -- second term: the sum over the box
  have hbox := box_sum F.two_le_p (F.mZero α x) hm (Bmax F α x) (keys F α x) (keys_bounds F hG)
    (hC F) (hC_nonneg F)
  have hsumC := sum_hC_le F.two_le_p (Bmax F α x)
  have hsumC' : ∑ t ∈ Finset.Icc 1 (Bmax F α x), hC F t ≤ 2 * (Real.log 4 + Real.log F.p) := hsumC
  have hsecond : ∑ κ ∈ keys F α x, ((F.p : ℝ)⁻¹) ^ pre κ.1 (F.mZero α x - 1) *
      hC F (κ.1 ⟨F.mZero α x - 1, Nat.sub_lt hG.one_le_m Nat.one_pos⟩)
      ≤ ((F.p : ℝ) - 1) ^ 2 * (2 * (Real.log 4 + Real.log F.p)) :=
    le_trans hbox (mul_le_mul_of_nonneg_left hsumC' (sq_nonneg _))
  unfold Kc
  linarith

end EPrimeAux

end ND

end GGMCollatz
