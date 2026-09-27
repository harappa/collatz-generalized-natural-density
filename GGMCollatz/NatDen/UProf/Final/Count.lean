import GGMCollatz.NatDen.UProf.Statements

/-!
# Auxiliary for (UF): the number of points of the window `Z = #(ℕ_p ∩ [lo, hi])` (the `Z_y = Y/μ (1 + O(y/Y))` of the accompanying paper)

`card_logWindow_approx`: if `1 ≤ lo ≤ hi` then `|#(ℕ_p ∩ [lo, hi]) - (hi - lo)/μ| ≤ 3`.
`ℕ_p` is periodic with period `p` and has density `(p-1)/p = 1/μ`. There are `⌊n/p⌋` multiples of `p` in `(0, n]` (Mathlib's
`Nat.Ioc_filter_dvd_card_eq_div`), so there are `n - ⌊n/p⌋` numbers not divisible by `p`.
-/

namespace GGMCollatz

namespace ND

namespace FinalAux

variable (F : Family)

/-- The number of integers in `(0, n]` not divisible by `p`, as a real number: `n - ⌊n/p⌋`. -/
theorem card_Ioc_not_dvd (n : ℕ) :
    (((Finset.Ioc 0 n).filter (fun N => N % F.p ≠ 0)).card : ℝ) = (n : ℝ) - ((n / F.p : ℕ) : ℝ) := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.Ioc 0 n)
    (fun N => F.p ∣ N)
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.card_Ioc, Nat.sub_zero] at h1
  have h2 : (Finset.Ioc 0 n).filter (fun N => ¬ F.p ∣ N)
      = (Finset.Ioc 0 n).filter (fun N => N % F.p ≠ 0) := by
    refine Finset.filter_congr (fun N _ => ?_)
    rw [Nat.dvd_iff_mod_eq_zero]
  rw [h2] at h1
  have h3 : ((n / F.p : ℕ) : ℝ) + (((Finset.Ioc 0 n).filter (fun N => N % F.p ≠ 0)).card : ℝ)
      = (n : ℝ) := by exact_mod_cast h1
  linarith

/-- `n/p - 1 < ⌊n/p⌋ ≤ n/p` (in the reals). -/
theorem div_bounds (n : ℕ) :
    (n : ℝ) / F.p - 1 < ((n / F.p : ℕ) : ℝ) ∧ ((n / F.p : ℕ) : ℝ) ≤ (n : ℝ) / F.p := by
  have hp : (0 : ℝ) < F.p := F.p_real_pos
  refine ⟨?_, Nat.cast_div_le⟩
  have hdm := Nat.div_add_mod n F.p
  have hml : n % F.p < F.p := Nat.mod_lt _ F.p_pos
  have h1 : (n : ℝ) = F.p * ((n / F.p : ℕ) : ℝ) + ((n % F.p : ℕ) : ℝ) := by exact_mod_cast hdm.symm
  have h2 : ((n % F.p : ℕ) : ℝ) < F.p := by exact_mod_cast hml
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hp]
  linarith

/-- `n/μ = n - n/p`. -/
theorem div_mu (t : ℝ) : t / F.mu = t - t / F.p := by
  have hp : (1 : ℝ) < F.p := F.one_lt_p_real
  unfold Family.mu
  field_simp

/-- The number of integers in `(0, n]` not divisible by `p` is within `1` of `n/μ`. -/
theorem card_Ioc_not_dvd_approx (n : ℕ) :
    |(((Finset.Ioc 0 n).filter (fun N => N % F.p ≠ 0)).card : ℝ) - (n : ℝ) / F.mu| ≤ 1 := by
  rw [card_Ioc_not_dvd F n, div_mu F]
  obtain ⟨h1, h2⟩ := div_bounds F n
  rw [abs_le]
  constructor <;> linarith

/-- **The number of points of the window**: if `1 ≤ lo ≤ hi` then `|#(ℕ_p ∩ [lo, hi]) - (hi - lo)/μ| ≤ 3`. -/
theorem card_logWindow_approx {lo hi : ℝ} (hlo : 1 ≤ lo) (hle : lo ≤ hi) :
    |((F.logWindow lo hi).card : ℝ) - (hi - lo) / F.mu| ≤ 3 := by
  classical
  have hlo0 : 0 < lo := by linarith
  have hhi0 : 0 < hi := by linarith
  set A := ⌈lo⌉₊ with hA
  set B := ⌊hi⌋₊ with hB
  have hA1 : 1 ≤ A := Nat.one_le_iff_ne_zero.mpr (by
    intro h0; have := Nat.le_ceil lo; rw [← hA, h0] at this; simp at this; linarith)
  have hAr1 : (A : ℝ) < lo + 1 := Nat.ceil_lt_add_one hlo0.le
  have hAr2 : lo ≤ (A : ℝ) := Nat.le_ceil lo
  have hBr1 : (B : ℝ) ≤ hi := Nat.floor_le hhi0.le
  have hBr2 : hi < (B : ℝ) + 1 := Nat.lt_floor_add_one hi
  have hAB : A ≤ B + 1 := by
    have : (A : ℝ) < (B : ℝ) + 2 := by linarith
    have : A < B + 2 := by exact_mod_cast this
    omega
  have hWeq : F.logWindow lo hi = (Finset.Icc A B).filter (fun N => N % F.p ≠ 0) := by
    ext N
    rw [F.mem_logWindow_iff, Finset.mem_filter, Finset.mem_Icc, hA, hB, Nat.ceil_le,
      Nat.le_floor_iff hhi0.le]
    tauto
  -- `(0, B] = (0, A-1] ⊔ [A, B]`
  have hsplit : (Finset.Ioc 0 B).filter (fun N => N % F.p ≠ 0)
      = (Finset.Ioc 0 (A - 1)).filter (fun N => N % F.p ≠ 0)
        ∪ (Finset.Icc A B).filter (fun N => N % F.p ≠ 0) := by
    rw [← Finset.filter_union]
    congr 1
    ext N
    simp only [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hdisj : Disjoint ((Finset.Ioc 0 (A - 1)).filter (fun N => N % F.p ≠ 0))
      ((Finset.Icc A B).filter (fun N => N % F.p ≠ 0)) := by
    rw [Finset.disjoint_left]
    intro N h1 h2
    have h1' := (Finset.mem_Ioc.mp (Finset.mem_filter.mp h1).1)
    have h2' := (Finset.mem_Icc.mp (Finset.mem_filter.mp h2).1)
    omega
  have hcard : (((Finset.Ioc 0 B).filter (fun N => N % F.p ≠ 0)).card : ℝ)
      = (((Finset.Ioc 0 (A - 1)).filter (fun N => N % F.p ≠ 0)).card : ℝ)
        + (((Finset.Icc A B).filter (fun N => N % F.p ≠ 0)).card : ℝ) := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
    push_cast; ring
  have eB := card_Ioc_not_dvd_approx F B
  have eA := card_Ioc_not_dvd_approx F (A - 1)
  have hA1r : ((A - 1 : ℕ) : ℝ) = (A : ℝ) - 1 := by
    rw [Nat.cast_sub hA1]; simp
  rw [hA1r] at eA
  rw [hWeq]
  have hμ := F.one_lt_mu
  have hμ0 : 0 < F.mu := F.mu_pos
  -- `|(B - (A-1)) - (hi - lo)| ≤ 1`, `1/μ ≤ 1`
  have hdiff : |((B : ℝ) - ((A : ℝ) - 1)) / F.mu - (hi - lo) / F.mu| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hμ0, div_le_one hμ0]
    rw [abs_le]; constructor <;> linarith
  have e3 : ((B : ℝ) - ((A : ℝ) - 1)) / F.mu = (B : ℝ) / F.mu - ((A : ℝ) - 1) / F.mu := sub_div _ _ _
  rw [abs_le] at eA eB hdiff ⊢
  constructor <;> linarith

end FinalAux

end ND

end GGMCollatz
