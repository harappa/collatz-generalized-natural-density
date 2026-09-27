import GGMCollatz.NatDen.UProf.Statements

/-!
# Auxiliary for (UC): the number of points of the uniform window and equidistribution of residues (the uniform-window side of the no-hit argument)

Source: the second half of `unif_equidist` (the argument `ℓ¹ = 2 Σ (ν - u)⁺`) is adapted from `window_equidist` in
`Tao/Sec5/FirstPassage.lean` (derived from `TaoCollatz/Sec5/FirstPassage.lean` of gotrevor/tao-collatz (Apache-2.0),
commit 15efca2), with the logarithmic window replaced by the uniform window and the harmonic-sum estimate replaced
by an estimate of class sizes.

For the uniform window `unifWin F lo hi` (the uniform distribution on `W = ℕ_p ∩ [lo, hi]`, `Z = #W`):

* `card_class_bounds`: the number of elements of one residue class mod `m` in the real interval `[lo, hi]` (`m ≤ lo`) is `(hi - lo)/m ± 1`.
* `card_window_ge`: the number of window points `Z ≥ (hi - lo)/p - 1` (`p ≤ lo`).
* `expect_unifWin`: the expectation on the uniform window is `Σ_{N ∈ W} f(N) / Z`.
* `map_unifWin_apply_toReal`: the mass of a pushforward of the uniform window is `#{N ∈ W | g(N) = b} / Z`.
* `unif_equidist`: the `ℓ¹` distance between the distribution mod `p^k` of the uniform window and `unifNpMod k` is at most `4 p^k / Z`
  (`p^k ≤ lo`. The uniform-window version of `window_equidist` (`Tao/Sec5/FirstPassage.lean`) for the logarithmic window.
  Each class of the window has `(hi - lo)/p^k ± 1` elements and `Z = Σ_z (class size)`, so each class has mass `1/#T + O(1/Z)`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace ConcAux

variable (F : Family)

open Family

/-- The number of elements of a residue class in a real interval: if `0 < m`, `v < m`, `m ≤ lo ≤ hi`, then
`(hi - lo)/m - 1 ≤ #{N ∈ [lo, hi] | N % m = v} ≤ (hi - lo)/m + 1`. -/
theorem card_class_bounds {m v : ℕ} (hm : 0 < m) (hv : v < m) {lo hi : ℝ} (hlo : (m : ℝ) ≤ lo)
    (hle : lo ≤ hi) :
    (hi - lo) / m - 1 ≤ (((Finset.range (⌈hi⌉₊ + 1)).filter fun N : ℕ =>
        lo ≤ (N : ℝ) ∧ (N : ℝ) ≤ hi ∧ N % m = v).card : ℝ) ∧
      (((Finset.range (⌈hi⌉₊ + 1)).filter fun N : ℕ =>
        lo ≤ (N : ℝ) ∧ (N : ℝ) ≤ hi ∧ N % m = v).card : ℝ) ≤ (hi - lo) / m + 1 := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hvR : (v : ℝ) < m := by exact_mod_cast hv
  have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg v
  have hhi0 : 0 ≤ hi := by linarith
  set A : ℝ := (lo - v) / m with hA
  set B : ℝ := (hi - v) / m with hB
  have hA0 : 0 ≤ A := div_nonneg (by linarith) hmR.le
  have hAB : A ≤ B := div_le_div_of_nonneg_right (by linarith) hmR.le
  have hBhi : B ≤ hi := by
    rw [hB, div_le_iff₀ hmR]
    nlinarith
  have hBlt : B < (⌈hi⌉₊ : ℝ) + 1 := by linarith [Nat.le_ceil hi]
  have hbd := card_filter_range_bounds (n₀ := ⌈hi⌉₊) hA0 hAB hBlt
  -- the class is the image of `J = {j | A ≤ j ≤ B}` under `j ↦ m j + v`
  have himg : ((Finset.range (⌈hi⌉₊ + 1)).filter fun N : ℕ =>
        lo ≤ (N : ℝ) ∧ (N : ℝ) ≤ hi ∧ N % m = v)
      = ((Finset.range (⌈hi⌉₊ + 1)).filter fun j : ℕ => A ≤ (j : ℝ) ∧ (j : ℝ) ≤ B).image
          (fun j => m * j + v) := by
    ext N
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hN, h1, h2, h3⟩
      have hdec : m * (N / m) + v = N := by
        have := Nat.div_add_mod N m
        rw [h3] at this
        exact this
      have hdecR : (m : ℝ) * ((N / m : ℕ) : ℝ) + v = N := by exact_mod_cast hdec
      refine ⟨N / m, ⟨?_, ?_, ?_⟩, hdec⟩
      · have := Nat.div_le_self N m; omega
      · rw [hA, div_le_iff₀ hmR]; nlinarith
      · rw [hB, le_div_iff₀ hmR]; nlinarith
    · rintro ⟨j, ⟨_, h1, h2⟩, rfl⟩
      have hjR : ((m * j + v : ℕ) : ℝ) = m * (j : ℝ) + v := by push_cast; ring
      rw [hA, div_le_iff₀ hmR] at h1
      rw [hB, le_div_iff₀ hmR] at h2
      have hN1 : lo ≤ ((m * j + v : ℕ) : ℝ) := by rw [hjR]; nlinarith
      have hN2 : ((m * j + v : ℕ) : ℝ) ≤ hi := by rw [hjR]; nlinarith
      refine ⟨?_, hN1, hN2, ?_⟩
      · have : ((m * j + v : ℕ) : ℝ) < (⌈hi⌉₊ : ℝ) + 1 := by linarith [Nat.le_ceil hi]
        have : m * j + v < ⌈hi⌉₊ + 1 := by exact_mod_cast this
        exact this
      · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
  have hinj : Set.InjOn (fun j : ℕ => m * j + v)
      (((Finset.range (⌈hi⌉₊ + 1)).filter fun j : ℕ => A ≤ (j : ℝ) ∧ (j : ℝ) ≤ B) : Set ℕ) := by
    intro j _ j' _ h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_left hm (by omega)
  rw [himg, Finset.card_image_of_injOn hinj]
  have e : B - A = (hi - lo) / m := by rw [hA, hB]; field_simp; ring
  constructor <;> linarith [hbd.1, hbd.2]

/-- `(N : ZMod m) = z ↔ N % m = z.val`. -/
theorem natCast_eq_iff_mod {m : ℕ} [NeZero m] (N : ℕ) (z : ZMod m) :
    (N : ZMod m) = z ↔ N % m = z.val := by
  constructor
  · rintro rfl; rw [ZMod.val_natCast]
  · intro h; rw [← ZMod.natCast_mod, h, ZMod.natCast_zmod_val]

/-- Lower bound on the number of window points: if `p ≤ lo ≤ hi`, then `Z ≥ (hi - lo)/p - 1` (count only the class of 1 mod `p`). -/
theorem card_window_ge {lo hi : ℝ} (hlo : (F.p : ℝ) ≤ lo) (hle : lo ≤ hi) :
    (hi - lo) / F.p - 1 ≤ ((F.logWindow lo hi).card : ℝ) := by
  classical
  have h := (card_class_bounds (m := F.p) (v := 1) F.p_pos F.one_lt_p hlo hle).1
  refine le_trans h ?_
  have hsub : ((Finset.range (⌈hi⌉₊ + 1)).filter fun N : ℕ =>
        lo ≤ (N : ℝ) ∧ (N : ℝ) ≤ hi ∧ N % F.p = 1) ⊆ F.logWindow lo hi := by
    intro N hN
    rw [Finset.mem_filter] at hN
    obtain ⟨hN, h1, h2, h3⟩ := hN
    unfold logWindow
    rw [Finset.mem_filter]
    exact ⟨hN, by omega, h1, h2⟩
  exact_mod_cast Finset.card_le_card hsub

/-- If the window is nonempty, `unifWin` is the uniform distribution on `W`. -/
theorem unifWin_eq {lo hi : ℝ} (h : (F.logWindow lo hi).Nonempty) :
    unifWin F lo hi = PMF.uniformOfFinset _ h := by
  unfold unifWin
  rw [dif_pos h]

/-- The expectation on the uniform window is the finite sum `Σ_{N ∈ W} f(N) / Z`. -/
theorem expect_unifWin {lo hi : ℝ} (h : (F.logWindow lo hi).Nonempty) (f : ℕ → ℝ) :
    Family.expect (unifWin F lo hi) f
      = (∑ N ∈ F.logWindow lo hi, f N) / ((F.logWindow lo hi).card : ℝ) := by
  rw [unifWin_eq F h]
  unfold Family.expect
  rw [tsum_eq_sum (s := F.logWindow lo hi) (fun N hN => by
    rw [PMF.uniformOfFinset_apply_of_notMem h hN]; simp)]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun N hN => ?_
  rw [PMF.uniformOfFinset_apply_of_mem h hN, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  ring

/-- The mass of a pushforward of the uniform window: `#{N ∈ W | g(N) = b} / Z`. -/
theorem map_unifWin_apply_toReal {lo hi : ℝ} (h : (F.logWindow lo hi).Nonempty) {β : Type*}
    [DecidableEq β] (g : ℕ → β) (b : β) :
    ((PMF.map g (unifWin F lo hi)) b).toReal
      = (((F.logWindow lo hi).filter fun N => g N = b).card : ℝ)
          / ((F.logWindow lo hi).card : ℝ) := by
  classical
  rw [unifWin_eq F h, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_uniformOfFinset_apply, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]
  congr 3
  ext N
  simp

/-- **Equidistribution of the uniform window**: if `1 ≤ k` and `p^k ≤ lo ≤ hi`, then
`‖(Ñ mod p^k) - unifNpMod k‖_{ℓ¹} ≤ 4 p^k / Z`. -/
theorem unif_equidist {lo hi : ℝ} (h : (F.logWindow lo hi).Nonempty) (hle : lo ≤ hi) {k : ℕ}
    (hk : 1 ≤ k) (hpk : (F.p : ℝ) ^ k ≤ lo) :
    PMF.dTV ((unifWin F lo hi).map fun N => (N : ZMod (F.p ^ k))) (F.unifNpMod k)
      ≤ 4 * (F.p : ℝ) ^ k / ((F.logWindow lo hi).card : ℝ) := by
  classical
  have hp := F.p_pos
  rw [map_coe_eq]
  set W := F.logWindow lo hi with hW
  set ν := PMF.map (fun N : ℕ => (N : ZMod (F.p ^ k))) (unifWin F lo hi) with hν
  set u := F.unifNpMod k with hu
  set Z : ℝ := (W.card : ℝ) with hZ
  have hZpos : 0 < Z := by rw [hZ]; exact_mod_cast h.card_pos
  set T := Finset.univ.filter fun z : ZMod (F.p ^ k) => z.val % F.p ≠ 0 with hT
  have hpk1 : 1 < F.p ^ k := Nat.one_lt_pow (by omega) (by have := F.two_le_p; omega)
  have hTne : T.Nonempty := ⟨1, by
    rw [hT, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [ZMod.val_one'' (by omega)]
    rw [Nat.mod_eq_of_lt F.one_lt_p]; norm_num⟩
  have huval : ∀ z, (u z).toReal = if z ∈ T then ((T.card : ℝ))⁻¹ else 0 := by
    intro z
    rw [hu]; unfold unifNpMod
    rw [dif_pos hTne, PMF.uniformOfFinset_apply]
    by_cases hz : z ∈ T
    · rw [if_pos hz, if_pos (by simpa [hT] using hz), ENNReal.toReal_inv, ENNReal.toReal_natCast]
    · rw [if_neg hz, if_neg (by simpa [hT] using hz)]
      simp
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast hTne.card_pos
  have hTle : (T.card : ℝ) ≤ (F.p : ℝ) ^ k := by
    have h1 : T.card ≤ F.p ^ k := by
      calc T.card ≤ (Finset.univ : Finset (ZMod (F.p ^ k))).card := Finset.card_filter_le _ _
        _ = F.p ^ k := by rw [Finset.card_univ, ZMod.card]
    exact_mod_cast h1
  set c : ZMod (F.p ^ k) → ℕ := fun z => (W.filter fun N : ℕ => ((N : ℕ) : ZMod (F.p ^ k)) = z).card with hc
  have hνval : ∀ z, (ν z).toReal = (c z : ℝ) / Z := fun z => by
    rw [hν, map_unifWin_apply_toReal F h]
  set D : ℝ := (hi - lo) / ((F.p ^ k : ℕ) : ℝ) with hD
  -- the size of each class
  have hclass : ∀ z ∈ T, D - 1 ≤ (c z : ℝ) ∧ (c z : ℝ) ≤ D + 1 := by
    intro z hz
    have hzv : z.val % F.p ≠ 0 := (Finset.mem_filter.mp hz).2
    have heq : W.filter (fun N : ℕ => ((N : ℕ) : ZMod (F.p ^ k)) = z)
        = (Finset.range (⌈hi⌉₊ + 1)).filter (fun N : ℕ =>
            lo ≤ (N : ℝ) ∧ (N : ℝ) ≤ hi ∧ N % F.p ^ k = z.val) := by
      ext N
      simp only [hW, logWindow, Finset.mem_filter, Finset.mem_range, natCast_eq_iff_mod]
      constructor
      · rintro ⟨⟨hN, _, h1, h2⟩, h3⟩; exact ⟨hN, h1, h2, h3⟩
      · rintro ⟨hN, h1, h2, h3⟩
        refine ⟨⟨hN, ?_, h1, h2⟩, h3⟩
        rw [← Nat.mod_mod_of_dvd N (dvd_pow_self F.p (by omega : k ≠ 0)), h3]
        exact hzv
    have hb := card_class_bounds (m := F.p ^ k) (v := z.val) (by omega) (ZMod.val_lt z)
      (by push_cast; exact hpk) hle
    have hcz : c z = ((Finset.range (⌈hi⌉₊ + 1)).filter (fun N : ℕ =>
            lo ≤ (N : ℝ) ∧ (N : ℝ) ≤ hi ∧ N % F.p ^ k = z.val)).card := by
      rw [hc]; simp only; rw [heq]
    rw [hcz, hD]
    exact hb
  -- `Z = Σ_{z ∈ T} c z`
  have hsumc : Z = ∑ z ∈ T, (c z : ℝ) := by
    have := Finset.card_eq_sum_card_fiberwise (f := fun N : ℕ => (N : ZMod (F.p ^ k)))
      (s := W) (t := T) (fun N hN => by
        simp only [Finset.mem_coe] at hN ⊢
        rw [hT, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [ZMod.val_natCast, Nat.mod_mod_of_dvd _ (dvd_pow_self F.p (by omega))]
        exact ((F.mem_logWindow_iff).mp hN).1)
    rw [hZ, this]
    push_cast
    rfl
  have hZlow : (T.card : ℝ) * (D - 1) ≤ Z := by
    rw [hsumc]
    calc (T.card : ℝ) * (D - 1) = ∑ _z ∈ T, (D - 1) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ T, (c z : ℝ) := Finset.sum_le_sum fun z hz => (hclass z hz).1
  -- the estimate for each class
  have hpt0 : ∀ z, (ν z).toReal - (u z).toReal ≤ if z ∈ T then 2 / Z else 0 := by
    intro z
    rw [hνval, huval]
    by_cases hz : z ∈ T
    · rw [if_pos hz, if_pos hz]
      have h1 := (hclass z hz).2
      rw [div_sub' hZpos.ne', div_le_div_iff_of_pos_right hZpos]
      -- `c z - Z/#T ≤ 2`
      have h2 : Z * (T.card : ℝ)⁻¹ ≥ D - 1 := by
        rw [ge_iff_le, ← div_eq_mul_inv, le_div_iff₀ hTpos]; linarith
      linarith
    · rw [if_neg hz, if_neg hz]
      have : c z = 0 := by
        rw [hc]; simp only
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro N hN hNz
        apply hz
        rw [hT, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hNz, ZMod.val_natCast, Nat.mod_mod_of_dvd _ (dvd_pow_self F.p (by omega))]
        exact ((F.mem_logWindow_iff).mp hN).1
      rw [this]; simp
  -- `ℓ¹ = 2 Σ (ν - u)⁺`
  have hsumν : ∑ z, (ν z).toReal = 1 := by
    have := tsum_toReal_eq_one ν; rwa [tsum_fintype] at this
  have hsumu : ∑ z, (u z).toReal = 1 := by
    have := tsum_toReal_eq_one u; rwa [tsum_fintype] at this
  unfold PMF.dTV
  rw [tsum_fintype]
  have hpt : ∀ z : ZMod (F.p ^ k), |(ν z).toReal - (u z).toReal|
      ≤ 2 * (if z ∈ T then 2 / Z else 0) - ((ν z).toReal - (u z).toReal) := by
    intro z
    have h1 := hpt0 z
    rcases le_or_gt 0 ((ν z).toReal - (u z).toReal) with h0 | h0
    · rw [abs_of_nonneg h0]; linarith
    · rw [abs_of_neg h0]
      have : 0 ≤ (if z ∈ T then 2 / Z else 0 : ℝ) := by
        split_ifs <;> positivity
      linarith
  calc ∑ z, |(ν z).toReal - (u z).toReal|
      ≤ ∑ z, (2 * (if z ∈ T then 2 / Z else 0) - ((ν z).toReal - (u z).toReal)) :=
        Finset.sum_le_sum fun z _ => hpt z
    _ = 2 * (T.card * (2 / Z)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsumν, hsumu, ← Finset.mul_sum,
          Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ 2 * ((F.p : ℝ) ^ k * (2 / Z)) := by gcongr
    _ = 4 * (F.p : ℝ) ^ k / Z := by ring

end ConcAux

end ND

end GGMCollatz
