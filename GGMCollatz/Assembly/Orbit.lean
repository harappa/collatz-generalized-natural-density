import GGMCollatz.Seed.Step

/-!
# The assembly of (A), part 2: comparison of orbits

* `Smin` and `Cmin` are attained as minima of the orbits (`lt_Smin_iff`, `lt_Cmin_iff`).
* Decomposition by first passage: if `N₀ ≤ x`, then
  `S_min(N) > N₀ ⟺ T_x(N) = ∞ ∨ S_min(Pass_x(N)) > N₀`, and the two events are disjoint (`1 ∉ A`).
* One block for `p ∤ M`: with `v = (qM + r(j)).toNat` and `ν = ν_p(v) ≥ 1`, `C~^i(M) = v/p^i`
  (`1 ≤ i ≤ ν`), `C^{1+i}(M) = v/p^i` (`i ≤ ν`), `S(M) = v/p^ν`, `p ∤ S(M)`.
* The orbit of the reduced map is bounded below by values of the orbit of `S`
  (`exists_S_iterate_le_Ct_iterate`; `C~_min ≥ S_min` in the accompanying paper).
* The orbit of `S` is a subsequence of the orbit of `C` (`exists_C_iterate_eq_S_iterate`). For
  `N = p^k N'`, `C^k(N) = N'`. In particular `C_min(N) > N₀ ⇒ S_min(N') > N₀` (the direction we use of
  the first item of the reduction in the accompanying paper).
-/

namespace GGMCollatz

namespace Asm

variable (F : Family)

/-! ## Minima -/

theorem Smin_le_iterate (N k : ℕ) : F.Smin N ≤ F.S^[k] N := Nat.sInf_le ⟨k, rfl⟩

theorem Smin_le_self (N : ℕ) : F.Smin N ≤ N := (Smin_le_iterate F) N 0

theorem Smin_mem (N : ℕ) : ∃ k, F.S^[k] N = F.Smin N := Nat.sInf_mem (Set.range_nonempty _)

theorem lt_Smin_iff {N₀ N : ℕ} : N₀ < F.Smin N ↔ ∀ k, N₀ < F.S^[k] N := by
  constructor
  · intro h k; exact lt_of_lt_of_le h ((Smin_le_iterate F) N k)
  · intro h
    obtain ⟨k, hk⟩ := (Smin_mem F) N
    rw [← hk]; exact h k

theorem Cmin_le_iterate (N k : ℕ) : F.Cmin N ≤ F.C^[k] N := Nat.sInf_le ⟨k, rfl⟩

theorem Cmin_mem (N : ℕ) : ∃ k, F.C^[k] N = F.Cmin N := Nat.sInf_mem (Set.range_nonempty _)

theorem lt_Cmin_iff {N₀ N : ℕ} : N₀ < F.Cmin N ↔ ∀ k, N₀ < F.C^[k] N := by
  constructor
  · intro h k; exact lt_of_lt_of_le h ((Cmin_le_iterate F) N k)
  · intro h
    obtain ⟨k, hk⟩ := (Cmin_mem F) N
    rw [← hk]; exact h k

theorem not_lt_Smin_one {N₀ : ℕ} (hN₀ : 1 ≤ N₀) : ¬ N₀ < F.Smin 1 := by
  have := (Smin_le_self F) 1; omega

/-! ## Decomposition by first passage -/

theorem passLoc_of_not_passes {x N : ℕ} (h : ¬ F.passes x N) : F.passLoc x N = 1 := by
  unfold Family.passLoc; rw [if_neg h]

theorem passLoc_of_passes {x N : ℕ} (h : F.passes x N) :
    F.passLoc x N = F.S^[F.passTime x N] N := by
  unfold Family.passLoc; rw [if_pos h]

theorem lt_iterate_of_lt_passTime {x N n : ℕ} (hn : n < F.passTime x N) : x < F.S^[n] N := by
  have := Nat.notMem_of_lt_sInf hn
  simp only [Set.mem_ofPred_eq, not_le] at this
  exact this

/-- `S_min(N) > N₀ ⟺ T_x(N) = ∞ ∨ S_min(Pass_x(N)) > N₀` (`N₀ ≤ x`). -/
theorem lt_Smin_iff_passes {x N₀ : ℕ} (hx : N₀ ≤ x) (N : ℕ) :
    N₀ < F.Smin N ↔ (¬ F.passes x N ∨ N₀ < F.Smin (F.passLoc x N)) := by
  by_cases hp : F.passes x N
  · have hloc := (passLoc_of_passes F) hp
    set T := F.passTime x N
    simp only [hp, not_true_eq_false, false_or, hloc, lt_Smin_iff]
    constructor
    · intro h k
      rw [← Function.iterate_add_apply]; exact h _
    · intro h k
      by_cases hk : k < T
      · exact lt_of_le_of_lt hx ((lt_iterate_of_lt_passTime F) hk)
      · have := h (k - T)
        rw [← Function.iterate_add_apply] at this
        rwa [show k - T + T = k by omega] at this
  · simp only [hp, not_false_eq_true, true_or, iff_true]
    rw [lt_Smin_iff]
    intro k
    have : ¬ F.S^[k] N ≤ x := fun h => hp ⟨k, h⟩
    omega

/-- The two events of the decomposition are disjoint. -/
theorem disjoint_passes {x N₀ : ℕ} (hN₀ : 1 ≤ N₀) :
    Disjoint {N | ¬ F.passes x N} (F.passLoc x ⁻¹' {m | N₀ < F.Smin m}) := by
  rw [Set.disjoint_left]
  intro N hN hN'
  simp only [Set.mem_ofPred_eq] at hN
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, (passLoc_of_not_passes F) hN] at hN'
  exact (not_lt_Smin_one F) hN₀ hN'

theorem bad_eq_union {x N₀ : ℕ} (hx : N₀ ≤ x) :
    {N | N₀ < F.Smin N} = {N | ¬ F.passes x N} ∪ (F.passLoc x ⁻¹' {m | N₀ < F.Smin m}) := by
  ext N
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_preimage]
  exact (lt_Smin_iff_passes F) hx N

/-! ## One block -/

/-- `v(M) = (qM + r(M mod p)).toNat`. -/
def vv (M : ℕ) : ℕ := ((F.q : ℤ) * M + F.r (M % F.p)).toNat

theorem S_eq (M : ℕ) : F.S M = (vv F) M / F.p ^ padicValNat F.p ((vv F) M) := rfl

theorem C_of_mod_ne_zero {M : ℕ} (hM : M % F.p ≠ 0) : F.C M = (vv F) M := by
  simp only [Family.C, vv, if_neg hM]

theorem C_of_mod_eq_zero {M : ℕ} (hM : M % F.p = 0) : F.C M = M / F.p := by
  simp only [Family.C, if_pos hM]

theorem vv_cast {M : ℕ} (hM : M % F.p ≠ 0) : ((vv F) M : ℤ) = (F.q : ℤ) * M + F.r (M % F.p) := by
  unfold vv
  have := F.one_le_q_mul_add_r hM
  rw [Int.toNat_of_nonneg (by omega)]

theorem one_le_vv {M : ℕ} (hM : M % F.p ≠ 0) : 1 ≤ (vv F) M := by
  have h1 := F.one_le_q_mul_add_r hM
  have h2 := (vv_cast F) hM
  omega

theorem p_dvd_vv {M : ℕ} (hM : M % F.p ≠ 0) : F.p ∣ (vv F) M := by
  have h := F.dvd_q_mul_add_r hM
  rw [← (vv_cast F) hM] at h
  exact_mod_cast h

theorem p_ne_one : F.p ≠ 1 := by have := F.two_le_p; omega

theorem one_le_val {M : ℕ} (hM : M % F.p ≠ 0) : 1 ≤ padicValNat F.p ((vv F) M) := by
  have h := (p_dvd_vv F) hM
  rw [← pow_one F.p, padicValNat_dvd_iff_le_of_ne_one (p_ne_one F)
    (by have := (one_le_vv F) hM; omega)] at h
  exact h

/-- If `i < ν` then `p ∣ v/p^i`. -/
theorem p_dvd_div_pow {v i : ℕ} (hv : v ≠ 0) (hi : i < padicValNat F.p v) : F.p ∣ v / F.p ^ i := by
  apply Nat.dvd_div_of_mul_dvd
  rw [← pow_succ, padicValNat_dvd_iff_le_of_ne_one (p_ne_one F) hv]
  omega

/-- `p ∤ v/p^ν`. -/
theorem not_p_dvd_div_pow_val {v : ℕ} (hv : v ≠ 0) : ¬ F.p ∣ v / F.p ^ padicValNat F.p v := by
  intro h
  have h1 : F.p ^ padicValNat F.p v ∣ v :=
    (padicValNat_dvd_iff_le_of_ne_one (p_ne_one F) hv).mpr le_rfl
  have h2 := Nat.mul_dvd_of_dvd_div h1 h
  rw [← pow_succ, padicValNat_dvd_iff_le_of_ne_one (p_ne_one F) hv] at h2
  omega

theorem S_mod_ne_zero {M : ℕ} (hM : M % F.p ≠ 0) : F.S M % F.p ≠ 0 := by
  rw [(S_eq F)]
  intro h
  exact (not_p_dvd_div_pow_val F) (by have := (one_le_vv F) hM; omega) (Nat.dvd_of_mod_eq_zero h)

theorem S_iterate_mod_ne_zero {M : ℕ} (hM : M % F.p ≠ 0) (n : ℕ) : F.S^[n] M % F.p ≠ 0 := by
  induction n with
  | zero => exact hM
  | succ n ih => rw [Function.iterate_succ_apply']; exact (S_mod_ne_zero F) ih

/-- A block of the reduced map: `C~^{j+1}(M) = v/p^{j+1}` (`j + 1 ≤ ν`). -/
theorem Ct_iterate_block {M : ℕ} (hM : M % F.p ≠ 0) :
    ∀ j, j + 1 ≤ padicValNat F.p ((vv F) M) → F.Ct^[j + 1] M = (vv F) M / F.p ^ (j + 1) := by
  have hv0 : (vv F) M ≠ 0 := by have := (one_le_vv F) hM; omega
  intro j
  induction j with
  | zero =>
    intro _
    have h1 := F.p_mul_Ct_of_mod_ne_zero hM
    rw [← (vv_cast F) hM] at h1
    have h2 : F.p * F.Ct M = (vv F) M := by exact_mod_cast h1
    simp only [zero_add, Function.iterate_one, pow_one]
    rw [← h2, Nat.mul_div_cancel_left _ F.p_pos]
  | succ j ih =>
    intro hj
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hd := (p_dvd_div_pow F) hv0 (show j + 1 < padicValNat F.p ((vv F) M) by omega)
    rw [F.Ct_of_mod_eq_zero (Nat.mod_eq_zero_of_dvd hd), Nat.div_div_eq_div_mul, ← pow_succ]

/-- A block of the Collatz map: `C^{1+i}(M) = v/p^i` (`i ≤ ν`). -/
theorem C_iterate_block {M : ℕ} (hM : M % F.p ≠ 0) :
    ∀ i, i ≤ padicValNat F.p ((vv F) M) → F.C^[i + 1] M = (vv F) M / F.p ^ i := by
  have hv0 : (vv F) M ≠ 0 := by have := (one_le_vv F) hM; omega
  intro i
  induction i with
  | zero =>
    intro _
    simp only [zero_add, Function.iterate_one, pow_zero, Nat.div_one]
    exact (C_of_mod_ne_zero F) hM
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hd := (p_dvd_div_pow F) hv0 (show i < padicValNat F.p ((vv F) M) by omega)
    rw [(C_of_mod_eq_zero F) (Nat.mod_eq_zero_of_dvd hd), Nat.div_div_eq_div_mul, ← pow_succ]

theorem C_iterate_eq_S {M : ℕ} (hM : M % F.p ≠ 0) :
    F.C^[padicValNat F.p ((vv F) M) + 1] M = F.S M := by
  rw [(C_iterate_block F) hM _ le_rfl, (S_eq F)]

theorem Ct_iterate_eq_S {M : ℕ} (hM : M % F.p ≠ 0) :
    F.Ct^[padicValNat F.p ((vv F) M)] M = F.S M := by
  obtain ⟨j, hj⟩ : ∃ j, padicValNat F.p ((vv F) M) = j + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
    ((one_le_val F) hM)).symm⟩
  rw [hj, (Ct_iterate_block F) hM j (by omega), ← hj, (S_eq F)]

theorem S_le_Ct_iterate {M : ℕ} (hM : M % F.p ≠ 0) {i : ℕ} (hi1 : 1 ≤ i)
    (hi : i ≤ padicValNat F.p ((vv F) M)) : F.S M ≤ F.Ct^[i] M := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [(Ct_iterate_block F) hM j hi, (S_eq F)]
  exact Nat.div_le_div_left (Nat.pow_le_pow_right F.p_pos hi) (pow_pos F.p_pos _)

/-! ## Comparison of orbits -/

/-- Each value of the orbit of the reduced map is at least some value of the orbit of `S`. -/
theorem exists_S_iterate_le_Ct_iterate :
    ∀ k M, M % F.p ≠ 0 → ∃ n, F.S^[n] M ≤ F.Ct^[k] M := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro M hM
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨0, le_rfl⟩
  set ν := padicValNat F.p ((vv F) M) with hν
  by_cases hkν : k ≤ ν
  · exact ⟨1, by simpa using (S_le_Ct_iterate F) hM hk hkν⟩
  · have hν1 := (one_le_val F) hM
    obtain ⟨n, hn⟩ := ih (k - ν) (by omega) (F.S M) ((S_mod_ne_zero F) hM)
    refine ⟨n + 1, ?_⟩
    rw [Function.iterate_succ_apply]
    have e : F.Ct^[k] M = F.Ct^[k - ν] (F.Ct^[ν] M) := by
      rw [← Function.iterate_add_apply]; congr 1; omega
    rw [e, (Ct_iterate_eq_S F) hM]
    exact hn

/-- If `p ∤ N` and `S_min(N) > N₀ ≥ p^L`, then the orbit of the reduced map stays `≥ p^L` forever. -/
theorem Ct_iterate_ge_of_lt_Smin {N N₀ L : ℕ} (hN : N % F.p ≠ 0) (hL : F.p ^ L ≤ N₀)
    (h : N₀ < F.Smin N) (k : ℕ) : F.p ^ L ≤ F.Ct^[k] N := by
  obtain ⟨n, hn⟩ := (exists_S_iterate_le_Ct_iterate F) k N hN
  have := ((lt_Smin_iff F).mp h) n
  omega

/-- The orbit of `S` is a subsequence of the orbit of `C`. -/
theorem exists_C_iterate_eq_S_iterate :
    ∀ n M, M % F.p ≠ 0 → ∃ t, F.C^[t] M = F.S^[n] M := by
  intro n
  induction n with
  | zero => intro M _; exact ⟨0, rfl⟩
  | succ n ih =>
    intro M hM
    obtain ⟨t, ht⟩ := ih (F.S M) ((S_mod_ne_zero F) hM)
    refine ⟨t + (padicValNat F.p ((vv F) M) + 1), ?_⟩
    rw [Function.iterate_add_apply, (C_iterate_eq_S F) hM, ht, Function.iterate_succ_apply]

theorem C_pow_mul (k m : ℕ) : F.C^[k] (F.p ^ k * m) = m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have h : F.p ^ (k + 1) * m = F.p * (F.p ^ k * m) := by ring
    rw [h, (C_of_mod_eq_zero F) (Nat.mul_mod_right _ _), Nat.mul_div_cancel_left _ F.p_pos, ih]

/-- The part `N' = N / p^{ν_p(N)}` with the power of `p` removed. -/
theorem pow_val_mul_div (N : ℕ) : F.p ^ padicValNat F.p N * (N / F.p ^ padicValNat F.p N) = N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · exact Nat.mul_div_cancel' ((padicValNat_dvd_iff_le_of_ne_one (p_ne_one F) hN.ne').mpr le_rfl)

theorem div_pow_val_mod_ne_zero {N : ℕ} (hN : N ≠ 0) :
    (N / F.p ^ padicValNat F.p N) % F.p ≠ 0 := by
  intro h
  exact (not_p_dvd_div_pow_val F) hN (Nat.dvd_of_mod_eq_zero h)

/-- `C_min(N) > N₀ ⇒ S_min(N') > N₀`, where `N' = N/p^{ν_p(N)}`. -/
theorem lt_Smin_of_lt_Cmin {N₀ N : ℕ} (hN : N ≠ 0) (h : N₀ < F.Cmin N) :
    N₀ < F.Smin (N / F.p ^ padicValNat F.p N) := by
  set k := padicValNat F.p N
  set N' := N / F.p ^ k
  have hN' : N' % F.p ≠ 0 := (div_pow_val_mod_ne_zero F) hN
  have hk : F.C^[k] N = N' := by
    conv_lhs => rw [← (pow_val_mul_div F) N]
    exact (C_pow_mul F) k N'
  rw [lt_Smin_iff]
  intro n
  obtain ⟨t, ht⟩ := (exists_C_iterate_eq_S_iterate F) n N' hN'
  rw [← ht, ← hk, ← Function.iterate_add_apply]
  exact ((lt_Cmin_iff F).mp h) _

end Asm

end GGMCollatz
