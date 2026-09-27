import GGMCollatz.NatDen.UProf.Statements
import GGMCollatz.NatDen.UProf.URD.Asymp

/-!
# (URD) Recounting via preimages and window replacement

`urow(n) = Σ_{M ∈ E'(E)} #{v valid | a ∈ A^{(k)}, F_k(v) ≡ M, N_{v,M} ∈ W}` (Lemma 7.9 of the paper: `exists_preimage`, `vecOf_injective` in
`Tao/Sec5/Reindex.lean`); a valid tuple has mass `p^{-Σa}`, so the count is `Σ_s p^s P(Σa = s, …)` (identity (K)).
The cost of replacing the window indicator `1[y ≤ N_{v,M} ≤ Y]` (`N_{v,M} = (p^s M - fint)/q^k`) by `1[s ∈ Σ(n,M)]`
(`Disc` in the accompanying paper) is `≪ Z L^{-1/2}`: counting the `M` near the endpoints in residue classes ((EP2)); at the upper end,
at most one per `n'` by (IRR); the local bound `max_s P(s_k = s) ≪ k^{-1/2}`; at the lower end, `y^{1-α}`.

**The proof in the formalization** (stronger than the paper, and using none of the hypotheses): for each pair `(k, s)`, the `M` where the two
disagree are near an endpoint, `|M - e q^k/p^s| ≤ q^k B` (`B = rBound`, `e ∈ {y, Y}`), so there are only `O(q^k B)` of them, and since
`E' ⊂ [Mlo, ∞)`, `p^s ≤ 2Y q^k/Mlo`. Summing with the model mass `Σ_v p^{-|a|} ≤ 1`, the discrepancy per row is
`≤ 4(2 q^k B + 1) q^k Y/Mlo ≤ 4(2B + 1) Y x^{-1/2}` (`q^k ≤ x^{1/5}`, `Mlo ≥ x^{9/10}`).
There are `≤ log x` rows and `Y ≤ 2p Z`, so the error is `≤ Z (log x)^{-1}` (for large `x`).
(IRR), (LCLT), (EP1), (EP2) are not used (so `urd` takes no hypotheses). The parts are under `URD/`
(`Box`, `Count`, `Disc`, `Asymp`).
-/

namespace GGMCollatz

namespace ND

namespace URDAux

variable (F : Family)

open Classical in
/-- **Row-wise bound**: if `x ≥ 1`, `1 ≤ y ≤ Y`, `Mlo ≥ x^{9/10}`, `2B x^{1/5} ≤ x^{9/10}`, then for a row `n ∈ [2m₀, n₀]`,
`|urow(n) - umain(n)| ≤ 4(2B + 1) Y x^{-1/2}`. -/
theorem row_bound {α x : ℝ} (E : Set ℕ) {n : ℕ} (hn : n ∈ rows F α x)
    (hx0 : 0 < x) (hx1 : 1 ≤ x) (hy1 : 1 ≤ x ^ α) (hyY : x ^ α ≤ (x ^ α) ^ α)
    (hMlo : x ^ (9 / 10 : ℝ) ≤ F.Mlo α x)
    (hB : 2 * (F.rBound : ℝ) * x ^ (1 / 5 : ℝ) ≤ x ^ (9 / 10 : ℝ)) :
    |(urow F α x E n : ℝ) - umain F α x E n|
      ≤ 4 * (2 * (F.rBound : ℝ) + 1) * (x ^ α) ^ α * x ^ (-(1 / 2 : ℝ)) := by
  set k := n - F.mZero α x with hkdef
  set y := x ^ α with hydef
  set Y := (x ^ α) ^ α with hYdef
  set Q : ℝ := (F.q : ℝ) ^ k with hQdef
  set Mlo := F.Mlo α x with hMlodef
  have hB0 : (0 : ℝ) ≤ F.rBound := by exact_mod_cast F.rBound_nonneg
  have hk : k ≤ F.nZero x := le_trans (Nat.sub_le _ _) (Finset.mem_Icc.mp hn).2
  have hQx : Q ≤ x ^ (1 / 5 : ℝ) := q_pow_le F hx0 hx1 hk
  have hQ0 : 0 < Q := pow_pos F.q_real_pos k
  have hx15 : 1 ≤ x ^ (1 / 5 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hx910 : 1 ≤ x ^ (9 / 10 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hMlo0 : 0 < Mlo := by linarith
  have hy0 : 0 < y := by linarith
  -- `2QB ≤ Mlo`
  have hQB : 2 * (Q * F.rBound) ≤ Mlo := by
    have : Q * F.rBound ≤ x ^ (1 / 5 : ℝ) * F.rBound := mul_le_mul_of_nonneg_right hQx hB0
    linarith
  -- properties of the elements of `E'`
  have hE : ∀ M ∈ F.Eprime α x E,
      M % F.p ≠ 0 ∧ 2 * Q * F.rBound ≤ M ∧ (1 : ℝ) ≤ M ∧ Mlo ≤ M := by
    intro M hM
    unfold Family.Eprime at hM
    rw [Finset.mem_filter] at hM
    obtain ⟨-, hMp, hMl, -⟩ := hM
    refine ⟨hMp, by linarith, by linarith, hMl⟩
  set T : ℕ := ⌈2 * Q * Y⌉₊ with hTdef
  have hT : 2 * Q * Y ≤ T := Nat.le_ceil _
  have hT' : Q * Y ≤ T := by
    have : 0 ≤ Q * Y := by positivity
    linarith
  -- turn the row count into a sum over pairs (recounting via preimages)
  have hurow := card_window_eq F (k := k) (T := T) hy0 (F.Eprime α x E) (fun a => F.goodVec x a)
    (fun M hM => ⟨(hE M hM).1, (hE M hM).2.1, (hE M hM).2.2.1⟩) hT
  have hu : (urow F α x E n : ℝ) = _ := hurow
  -- turn the main term into a sum over pairs (identity (K))
  have hm : umain F α x E n = ∑ M ∈ F.Eprime α x E, ∑ v ∈ box F k T,
      if (F.offsetFwd v = (M : ZMod (F.q ^ k)) ∧ F.goodVec x (fun i => (v i).1) ∧
          inWin F y Y k (sOf v) M)
      then (1 : ℝ) else 0 := by
    unfold umain
    refine Finset.sum_congr rfl fun M hM => ?_
    exact tsum_inWin_eq F M (hE M hM).2.2.1 (fun a => F.goodVec x a) hT'
  rw [hu, hm]
  have hd := row_disc F (k := k) (T := T) hy0 hyY hMlo0 (F.Eprime α x E) (fun a => F.goodVec x a)
    (fun M hM => (hE M hM).2.2.2) hQB
  refine le_trans hd ?_
  -- `4(2QB + 1) Q Y/Mlo ≤ 4(2B + 1) Y x^{-1/2}`
  have h1 : 2 * (Q * F.rBound) + 1 ≤ (2 * F.rBound + 1) * x ^ (1 / 5 : ℝ) := by
    have : Q * F.rBound ≤ x ^ (1 / 5 : ℝ) * F.rBound := mul_le_mul_of_nonneg_right hQx hB0
    nlinarith
  have hpow : x ^ (1 / 5 : ℝ) * x ^ (1 / 5 : ℝ) = x ^ (-(1 / 2 : ℝ)) * x ^ (9 / 10 : ℝ) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; norm_num
  have hY0 : 0 ≤ Y := by linarith
  have hxm : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  rw [div_le_iff₀ hMlo0]
  calc 4 * (2 * (Q * F.rBound) + 1) * Q * Y
      ≤ 4 * ((2 * F.rBound + 1) * x ^ (1 / 5 : ℝ)) * x ^ (1 / 5 : ℝ) * Y := by
        gcongr
    _ = 4 * (2 * F.rBound + 1) * Y * (x ^ (-(1 / 2 : ℝ)) * x ^ (9 / 10 : ℝ)) := by
        rw [← hpow]; ring
    _ ≤ 4 * (2 * F.rBound + 1) * Y * (x ^ (-(1 / 2 : ℝ)) * Mlo) := by
        gcongr
    _ = 4 * (2 * (F.rBound : ℝ) + 1) * Y * x ^ (-(1 / 2 : ℝ)) * Mlo := by ring

end URDAux

variable (F : Family)

/-- **(URD)**. No hypotheses (the bound `URDAux.row_bound` is unconditional). Since (IRR), (LCLT), (EP1), (EP2)
are not used, they are not taken as arguments (removed after a referee pointed them out; an earlier version accepted
and discarded them for compatibility of the statement). -/
theorem urd : urd_statement F := by
  refine ⟨2, by norm_num, fun α hα _ => ⟨1, 1, one_pos, one_pos, ?_⟩⟩
  have hB0 : (0 : ℝ) ≤ F.rBound := by exact_mod_cast F.rBound_nonneg
  have hp0 : (0 : ℝ) < F.p := F.p_real_pos
  filter_upwards [URDAux.eventually_wCard_ge F hα, URDAux.eventually_Mlo_ge F α,
    Family.eventually_mul_rpow_neg_le_log (c := 1 / 2) (by norm_num) 2
      (8 * (F.p : ℝ) * (2 * F.rBound + 1)),
    Family.eventually_mul_rpow_neg_le_log (c := 7 / 10) (by norm_num) 0 (2 * (F.rBound : ℝ)),
    Family.eventually_log_ge 2, Filter.eventually_ge_atTop (1 : ℝ)] with
    x hW hMlo hfin hB7 hL2 hx1
  obtain ⟨hy1, hyY, hZ⟩ := hW
  intro E
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hLdef
  set Y := (x ^ α) ^ α with hYdef
  set Z := wCard F α x with hZdef
  have hL0 : 0 < L := by linarith
  -- `2B x^{1/5} ≤ x^{9/10}`
  have hB : 2 * (F.rBound : ℝ) * x ^ (1 / 5 : ℝ) ≤ x ^ (9 / 10 : ℝ) := by
    rw [neg_zero, Real.rpow_zero] at hB7
    have hsplit : x ^ (1 / 5 : ℝ) = x ^ (-(7 / 10 : ℝ)) * x ^ (9 / 10 : ℝ) := by
      rw [← Real.rpow_add hx0]; norm_num
    rw [hsplit, ← mul_assoc]
    have hx9 : 0 ≤ x ^ (9 / 10 : ℝ) := Real.rpow_nonneg hx0.le _
    calc 2 * (F.rBound : ℝ) * x ^ (-(7 / 10 : ℝ)) * x ^ (9 / 10 : ℝ)
        ≤ 1 * x ^ (9 / 10 : ℝ) := mul_le_mul_of_nonneg_right hB7 hx9
      _ = x ^ (9 / 10 : ℝ) := one_mul _
  -- row-wise bound
  have hrow : ∀ n ∈ rows F α x, |(urow F α x E n : ℝ) - umain F α x E n|
      ≤ 4 * (2 * (F.rBound : ℝ) + 1) * Y * x ^ (-(1 / 2 : ℝ)) := fun n hn =>
    URDAux.row_bound F E hn hx0 hx1 hy1 hyY hMlo hB
  -- the number of rows is `≤ log x`
  have hrows : ((rows F α x).card : ℝ) ≤ L := by
    unfold rows
    rw [Nat.card_Icc]
    have h3 := F.nZero_le hx1
    have : ((F.nZero x + 1 - 2 * F.mZero α x : ℕ) : ℝ) ≤ (F.nZero x : ℝ) + 1 := by
      have : F.nZero x + 1 - 2 * F.mZero α x ≤ F.nZero x + 1 := Nat.sub_le _ _
      exact_mod_cast this
    linarith
  have hYZ : Y ≤ 2 * F.p * Z := by
    rw [div_le_iff₀ (by positivity)] at hZ
    linarith
  have hxm : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hZ0 : 0 ≤ Z := by unfold Z wCard; positivity
  have hLL : L * L ^ (-(2 : ℝ)) = L ^ (-(1 : ℝ)) := by
    rw [show (-(1 : ℝ)) = 1 + -(2 : ℝ) by norm_num, Real.rpow_add hL0, Real.rpow_one]
  rw [← Finset.sum_sub_distrib]
  calc |∑ n ∈ rows F α x, ((urow F α x E n : ℝ) - umain F α x E n)|
      ≤ ∑ n ∈ rows F α x, |(urow F α x E n : ℝ) - umain F α x E n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ rows F α x, 4 * (2 * (F.rBound : ℝ) + 1) * Y * x ^ (-(1 / 2 : ℝ)) :=
        Finset.sum_le_sum hrow
    _ = ((rows F α x).card : ℝ) * (4 * (2 * (F.rBound : ℝ) + 1) * Y * x ^ (-(1 / 2 : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ L * (4 * (2 * (F.rBound : ℝ) + 1) * (2 * F.p * Z) * x ^ (-(1 / 2 : ℝ))) := by
        gcongr
    _ = L * Z * (8 * (F.p : ℝ) * (2 * F.rBound + 1) * x ^ (-(1 / 2 : ℝ))) := by ring
    _ ≤ L * Z * L ^ (-(2 : ℝ)) := by gcongr
    _ = 1 * Z * L ^ (-(1 : ℝ)) := by rw [← hLL]; ring

end ND

end GGMCollatz
