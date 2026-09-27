import GGMCollatz.NatDen.UProf.URD.Box

/-!
# Auxiliary for (URD): writing the row count and the main term as sums over the same set of tuples

For a row `n` (`k = n - m₀`), both `urow(n)` and `umain(n)` are written in the form
`Σ_{M ∈ E'(E)} Σ_{v ∈ box} 1[F_k(v) ≡ M, a ∈ A^{(k)}, window condition]`. They differ only in the window condition:

* `urow`: the preimage `N_{v,M} = (p^{|a|} M - fint)/q^k` lies in the window `[y, Y]` (`winN`).
  The bijection `N ↦ (S^k N, vecOf N k)` given by Lemma 7.9 of the paper (`exists_preimage`, `vecOf_injective`, `syr_iterate_key`).
* `umain`: `y < p^{|a|} M/q^k ≤ Y` (`inWin`; `s ∈ Σ(n, M)` in the accompanying paper). Identity (K) (`jpG_eq_count`).

The box size `T` suffices if `2 q^k Y ≤ T` (under `M ≥ 2 q^k B`, `B = rBound`, one has `p^{|a|} ≤ 2 q^k Y`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace URDAux

variable (F : Family)

/-- The preimage window condition `y ≤ (p^{|a|} M - fint)/q^k ≤ Y`. -/
def winN (y Y : ℝ) {k : ℕ} (v : Fin k → ℕ × ℕ) (M : ℕ) : Prop :=
  y ≤ ((F.p : ℝ) ^ sOf v * M - (fOf F v : ℝ)) / (F.q : ℝ) ^ k ∧
    ((F.p : ℝ) ^ sOf v * M - (fOf F v : ℝ)) / (F.q : ℝ) ^ k ≤ Y

/-- `|fint(a, r ∘ dig)| ≤ p^{|a|} q^k B` (`B = rBound`, valid tuple). -/
theorem abs_fOf_le {k : ℕ} {v : Fin k → ℕ × ℕ} (hv : F.validVec v) :
    |(fOf F v : ℝ)| ≤ (F.p : ℝ) ^ sOf v * (F.q : ℝ) ^ k * (F.rBound : ℝ) := by
  have h := F.abs_fint_le (fun i => (v i).1) (fun i => F.r (v i).2) F.rBound_nonneg
    (fun m => F.abs_r_le_rBound (hv m).2.2)
  rw [pre_eq_fin_sum] at h
  have h' : ((|fOf F v| : ℤ) : ℝ) ≤ (((F.p : ℤ) ^ sOf v * (F.q : ℤ) ^ k * F.rBound : ℤ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  exact h'

/-- Iteration formula: `p^{|a|} S^k(N) - fint = q^k N` (`p ∤ N`, `v = vecOf N k`). -/
theorem key_vecOf {N : ℕ} (hN : N % F.p ≠ 0) (k : ℕ) :
    (F.p : ℝ) ^ sOf (F.vecOf N k) * (F.S^[k] N : ℕ) - (fOf F (F.vecOf N k) : ℝ)
      = (F.q : ℝ) ^ k * N := by
  have h := F.syr_iterate_key hN k
  rw [pre_eq_fin_sum] at h
  have hs : sOf (F.vecOf N k) = ∑ i, F.valVec N k i := rfl
  have hf : fOf F (F.vecOf N k) = F.fint (F.valVec N k) (F.resVec N k) := rfl
  rw [hs, hf]
  have h' : (((F.p : ℤ) ^ (∑ i, F.valVec N k i) * (F.S^[k] N : ℤ) : ℤ) : ℝ)
      = (((F.q : ℤ) ^ k * N + F.fint (F.valVec N k) (F.resVec N k) : ℤ) : ℝ) := by
    rw [h]
  push_cast at h'
  linarith

/-- `s < p^s` (as reals). -/
theorem nat_lt_pow_real (s : ℕ) : (s : ℝ) < (F.p : ℝ) ^ s := by
  have h : s < F.p ^ s := Nat.lt_pow_self (by have := F.two_le_p; omega)
  exact_mod_cast h

/-- If `p^s ≤ T` (as reals), then `s ≤ T`. -/
theorem le_of_pow_le {s T : ℕ} (h : (F.p : ℝ) ^ s ≤ T) : s ≤ T := by
  have := lt_of_lt_of_le (nat_lt_pow_real F s) h
  exact_mod_cast this.le

open Classical in
/-- **Recounting via preimages** (Lemma 7.9 of the paper): if the elements of `E'` satisfy `p ∤ M`, `M ≥ 2 q^k B`, `M ≥ 1`,
and `2 q^k Y ≤ T`, `y > 0`, then the number of `N` in the window with `G(a^{(k)}(N))` and `S^k(N) ∈ E'` is
`Σ_{M ∈ E'} Σ_{v ∈ box} 1[F_k(v) ≡ M, G(a), N_{v,M} ∈ [y, Y]]`. -/
theorem card_window_eq {k T : ℕ} {y Y : ℝ} (hy : 0 < y) (E' : Finset ℕ)
    (G : (Fin k → ℕ) → Prop)
    (hE : ∀ M ∈ E', M % F.p ≠ 0 ∧ 2 * (F.q : ℝ) ^ k * F.rBound ≤ M ∧ (1 : ℝ) ≤ M)
    (hT : 2 * (F.q : ℝ) ^ k * Y ≤ T) :
    (((F.logWindow y Y).filter (fun N => G (F.valVec N k) ∧ F.S^[k] N ∈ E')).card : ℝ)
      = ∑ M ∈ E', ∑ v ∈ box F k T,
          if (F.offsetFwd v = (M : ZMod (F.q ^ k)) ∧ G (fun i => (v i).1) ∧ winN F y Y v M)
          then (1 : ℝ) else 0 := by
  have hq : (0 : ℝ) < (F.q : ℝ) ^ k := pow_pos F.q_real_pos k
  have hp : (0 : ℝ) < F.p := F.p_real_pos
  -- turn the right-hand side into a count over the product set
  set P : ℕ × (Fin k → ℕ × ℕ) → Prop := fun z =>
    F.offsetFwd z.2 = (z.1 : ZMod (F.q ^ k)) ∧ G (fun i => (z.2 i).1) ∧ winN F y Y z.2 z.1 with hPdef
  have hR : (∑ M ∈ E', ∑ v ∈ box F k T,
      if (F.offsetFwd v = (M : ZMod (F.q ^ k)) ∧ G (fun i => (v i).1) ∧ winN F y Y v M)
      then (1 : ℝ) else 0) = (((E' ×ˢ box F k T).filter P).card : ℝ) := by
    rw [Finset.natCast_card_filter, Finset.sum_product]
  rw [hR]
  congr 1
  refine Finset.card_bij (fun N _ => (F.S^[k] N, F.vecOf N k)) ?_ ?_ ?_
  · -- the map lands in the image
    intro N hN
    rw [Finset.mem_filter] at hN
    obtain ⟨hW, hG, hM⟩ := hN
    unfold Family.logWindow at hW
    rw [Finset.mem_filter] at hW
    obtain ⟨-, hNp, hyN, hNY⟩ := hW
    obtain ⟨hMp, hMB, hM1⟩ := hE _ hM
    have hkey := key_vecOf F hNp k
    have hvalid := F.vecOf_valid hNp k
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hM, mem_box_of_valid F hvalid ?_⟩, ?_, hG, ?_⟩
    · -- `|a| ≤ T`
      apply le_of_pow_le F
      set s := sOf (F.vecOf N k)
      set M := F.S^[k] N
      have hf := abs_fOf_le F hvalid
      have hf' := (abs_le.mp hf).2
      have hps : (0 : ℝ) < (F.p : ℝ) ^ s := pow_pos hp s
      -- `p^s M/2 ≤ q^k N ≤ q^k Y`
      have h1 : (F.p : ℝ) ^ s * M ≤ 2 * ((F.q : ℝ) ^ k * N) := by
        have : (F.p : ℝ) ^ s * (F.q : ℝ) ^ k * F.rBound ≤ (F.p : ℝ) ^ s * M / 2 := by
          have := mul_le_mul_of_nonneg_left hMB hps.le
          linarith
        linarith
      have h2 : (F.q : ℝ) ^ k * N ≤ (F.q : ℝ) ^ k * Y := mul_le_mul_of_nonneg_left hNY hq.le
      have h3 : (F.p : ℝ) ^ s ≤ (F.p : ℝ) ^ s * M := by
        have := mul_le_mul_of_nonneg_left hM1 hps.le
        linarith
      linarith
    · exact F.offsetFwd_vecOf hNp k
    · -- the window condition: `N_{v,M} = N`
      have hNv : ((F.p : ℝ) ^ sOf (F.vecOf N k) * (F.S^[k] N : ℕ)
          - (fOf F (F.vecOf N k) : ℝ)) / (F.q : ℝ) ^ k = N := by
        rw [hkey]; field_simp
      unfold winN
      rw [hNv]
      exact ⟨hyN, hNY⟩
  · -- injective
    intro N₁ h₁ N₂ h₂ he
    have hN₁ : N₁ % F.p ≠ 0 := by
      have := (Finset.mem_filter.mp h₁).1
      unfold Family.logWindow at this
      exact (Finset.mem_filter.mp this).2.1
    have hN₂ : N₂ % F.p ≠ 0 := by
      have := (Finset.mem_filter.mp h₂).1
      unfold Family.logWindow at this
      exact (Finset.mem_filter.mp this).2.1
    simp only [Prod.mk.injEq] at he
    exact F.vecOf_injective hN₁ hN₂ he.2 he.1
  · -- surjective
    rintro ⟨M, v⟩ hz
    rw [Finset.mem_filter, Finset.mem_product] at hz
    obtain ⟨⟨hM, hv⟩, hO, hG, hwin⟩ := hz
    obtain ⟨hMp, -, -⟩ := hE M hM
    have hvalid := valid_of_mem_box F hv
    have hpos : F.fint (fun i => (v i).1) (fun i => F.r (v i).2)
        < (F.p : ℤ) ^ pre (fun i => (v i).1) k * M := by
      rw [pre_eq_fin_sum]
      have h1 := hwin.1
      have h2 : 0 < ((F.p : ℝ) ^ sOf v * M - (fOf F v : ℝ)) / (F.q : ℝ) ^ k := lt_of_lt_of_le hy h1
      have h3 : 0 < (F.p : ℝ) ^ sOf v * M - (fOf F v : ℝ) := by
        rwa [div_pos_iff_of_pos_right hq] at h2
      have h4 : ((F.fint (fun i => (v i).1) (fun i => F.r (v i).2) : ℤ) : ℝ)
          < (((F.p : ℤ) ^ (∑ i, (v i).1) * M : ℤ) : ℝ) := by
        push_cast
        have : (fOf F v : ℝ) = ((F.fint (fun i => (v i).1) (fun i => F.r (v i).2) : ℤ) : ℝ) := rfl
        unfold sOf at h3
        linarith
      exact_mod_cast h4
    obtain ⟨N, hNp, hvec, hS, hqN⟩ := F.exists_preimage hvalid hMp hO.symm hpos
    refine ⟨N, ?_, ?_⟩
    · have hNreal : ((F.p : ℝ) ^ sOf v * M - (fOf F v : ℝ)) / (F.q : ℝ) ^ k = N := by
        rw [pre_eq_fin_sum] at hqN
        have h' : (((F.q : ℤ) ^ k * N : ℤ) : ℝ)
            = (((F.p : ℤ) ^ (∑ i, (v i).1) * M
                - F.fint (fun i => (v i).1) (fun i => F.r (v i).2) : ℤ) : ℝ) := by
          rw [hqN]
        push_cast at h'
        have : (fOf F v : ℝ) = ((F.fint (fun i => (v i).1) (fun i => F.r (v i).2) : ℤ) : ℝ) := rfl
        rw [this, div_eq_iff hq.ne']
        unfold sOf
        linarith
      have hwin' := hwin
      unfold winN at hwin'
      rw [hNreal] at hwin'
      rw [Finset.mem_filter]
      refine ⟨?_, ?_, ?_⟩
      · unfold Family.logWindow
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, hNp, hwin'.1, hwin'.2⟩
        have := Nat.le_ceil Y
        have : (N : ℝ) ≤ (⌈Y⌉₊ : ℝ) := le_trans hwin'.2 this
        have : N ≤ ⌈Y⌉₊ := by exact_mod_cast this
        omega
      · have hval : F.valVec N k = fun i => (v i).1 := by
          funext i
          have := congrFun hvec i
          simp only [Family.vecOf] at this
          rw [← this]
        rw [hval]; exact hG
      · rw [hS]; exact hM
    · simp only [hS, hvec]

open Classical in
/-- **Counting the main term** (identity (K), `jpG_eq_count`): if `M ≥ 1` and `q^k Y ≤ T`, then
`Σ'_s 1[s ∈ Σ(n,M)] p^s jpG(k, M, s, G) = Σ_{v ∈ box} 1[F_k(v) ≡ M, G(a), |a| ∈ Σ(n,M)]`. -/
theorem tsum_inWin_eq {k T : ℕ} {y Y : ℝ} (M : ℕ) (hM1 : (1 : ℝ) ≤ M)
    (G : (Fin k → ℕ) → Prop) (hT : (F.q : ℝ) ^ k * Y ≤ T) :
    (∑' s : ℕ, if inWin F y Y k s M then
        (F.p : ℝ) ^ s * jpG F k (M : ZMod (F.q ^ k)) s G else 0)
      = ∑ v ∈ box F k T,
          if (F.offsetFwd v = (M : ZMod (F.q ^ k)) ∧ G (fun i => (v i).1) ∧ inWin F y Y k (sOf v) M)
          then (1 : ℝ) else 0 := by
  have hq : (0 : ℝ) < (F.q : ℝ) ^ k := pow_pos F.q_real_pos k
  have hp : (0 : ℝ) < F.p := F.p_real_pos
  -- `inWin` implies `s ≤ T`
  have hsT : ∀ s, inWin F y Y k s M → s ≤ T := by
    intro s hs
    apply le_of_pow_le F
    have h1 := hs.2
    rw [div_le_iff₀ hq] at h1
    have hps : (0 : ℝ) < (F.p : ℝ) ^ s := pow_pos hp s
    have h2 : (F.p : ℝ) ^ s ≤ (F.p : ℝ) ^ s * M := by
      have := mul_le_mul_of_nonneg_left hM1 hps.le
      linarith
    nlinarith
  set g : (Fin k → ℕ × ℕ) → ℝ := fun v =>
    if (F.offsetFwd v = (M : ZMod (F.q ^ k)) ∧ G (fun i => (v i).1) ∧ inWin F y Y k (sOf v) M)
    then (1 : ℝ) else 0 with hgdef
  rw [tsum_eq_sum (s := Finset.range (T + 1))]
  · -- turn the term of each `s` into a sum over the box
    have hterm : ∀ s ∈ Finset.range (T + 1),
        (if inWin F y Y k s M then (F.p : ℝ) ^ s * jpG F k (M : ZMod (F.q ^ k)) s G else 0)
          = ∑ v ∈ box F k T, if sOf v = s then g v else 0 := by
      intro s hs
      have hsT' : s ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      by_cases hw : inWin F y Y k s M
      · rw [if_pos hw, jpG_eq_count F hsT' _ G]
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases hsv : sOf v = s
        · rw [if_pos hsv]
          rw [hgdef]
          simp only
          by_cases hc : F.offsetFwd v = (M : ZMod (F.q ^ k)) ∧ G (fun i => (v i).1)
          · rw [if_pos ⟨hsv, hc.1, hc.2⟩, if_pos ⟨hc.1, hc.2, by rw [hsv]; exact hw⟩]
          · rw [if_neg (fun h => hc ⟨h.2.1, h.2.2⟩), if_neg (fun h => hc ⟨h.1, h.2.1⟩)]
        · rw [if_neg hsv, if_neg (fun h => hsv h.1)]
      · rw [if_neg hw]
        symm
        refine Finset.sum_eq_zero fun v _ => ?_
        by_cases hsv : sOf v = s
        · rw [if_pos hsv, hgdef]
          simp only
          rw [if_neg (fun h => hw (hsv ▸ h.2.2))]
        · rw [if_neg hsv]
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_ite_eq]
    by_cases hmem : sOf v ∈ Finset.range (T + 1)
    · rw [if_pos hmem]
    · rw [if_neg hmem, hgdef]
      simp only
      rw [if_neg]
      intro h
      exact hmem (Finset.mem_range.mpr (Nat.lt_succ_of_le (hsT _ h.2.2)))
  · intro s hs
    rw [if_neg]
    intro hw
    exact hs (Finset.mem_range.mpr (Nat.lt_succ_of_le (hsT s hw)))

end URDAux

end ND

end GGMCollatz
