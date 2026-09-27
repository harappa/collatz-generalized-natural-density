import GGMCollatz.Tao.Sec7.Monotone

/-!
# GGM §7: unrolling the recursion for `Q` up to the first passage ((7.45) of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/Unroll.lean` (first half);
generalized to the GGM family (p, q, r). Modified.

* `hold_support_snd_ge`: the second coordinate of `ℋ` is `≥ 3` (`3 + Σ`).
* `fpDist s`: the law of the first-passage endpoint (the displacement until the height budget `s` is first exceeded; tao-collatz's finitization D6).
* `fpDist_support_fst_pos`, `fpDist_support_snd_gt`: the endpoint satisfies `e₁ ≥ 1`, `e₂ > s`.
* `Q_le_fpDist_expect`: `Q(j,l) ≤ E[Q((j,l) + endpoint)]` ((7.45) with the decay discarded, in `ℝ≥0∞`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- The second coordinate of an atom of `hold` is `≥ 3`. -/
theorem hold_support_snd_ge (d : ℕ × ℤ) (hd : d ∈ F.hold.support) : 3 ≤ d.2 := by
  rw [hold, PMF.mem_support_bind_iff] at hd
  obtain ⟨k, hk, hkd⟩ := hd
  rw [PMF.mem_support_map_iff] at hkd
  obtain ⟨v, _, hv⟩ := hkd
  rw [← hv]
  have h0 : (0 : ℤ) ≤ ∑ i, ((v i : ℕ) : ℤ) := Finset.sum_nonneg fun i _ => Int.natCast_nonneg _
  show (3 : ℤ) ≤ 3 + ∑ i, ((v i : ℕ) : ℤ)
  linarith

/-- Points whose second coordinate is `< 3` have mass `0`. -/
theorem hold_zero_of_snd_lt {d : ℕ × ℤ} (h2 : d.2 < 3) : F.hold d = 0 := by
  rw [PMF.apply_eq_zero_iff]
  intro hd
  exact absurd (F.hold_support_snd_ge d hd) (by omega)

/-- **Law of the first-passage endpoint** (`fpDist` of tao-collatz, (7.44)): draw `d ~ ℋ`; if it exceeds the budget
(`d₂ > s`), the endpoint is `d`; otherwise recurse with budget `s - d₂` and translate. -/
noncomputable def fpDist : ℕ → PMF (ℕ × ℤ)
  | s =>
    F.hold.bind fun d =>
      if _h : d.2 ≤ 0 ∨ (s : ℤ) < d.2 then PMF.pure d
      else (fpDist (s - d.2.toNat)).map fun e => (d.1 + e.1, d.2 + e.2)
  termination_by s => s
  decreasing_by
    push Not at _h
    omega

/-- The first coordinate of the endpoint is positive. -/
theorem fpDist_support_fst_pos :
    ∀ s, ∀ e ∈ (F.fpDist s).support, 1 ≤ e.1 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro e he
    rw [fpDist, PMF.mem_support_bind_iff] at he
    obtain ⟨d, hd, hde⟩ := he
    have hd1 := F.hold_support_fst_pos d hd
    split_ifs at hde with hcond
    · rw [PMF.support_pure, Set.mem_singleton_iff] at hde
      subst hde
      exact hd1
    · rw [PMF.mem_support_map_iff] at hde
      obtain ⟨e', _, he'⟩ := hde
      rw [← he']
      show 1 ≤ d.1 + e'.1
      omega

/-- The endpoint exceeds the budget: `s < e₂`. -/
theorem fpDist_support_snd_gt :
    ∀ s, ∀ e ∈ (F.fpDist s).support, (s : ℤ) < e.2 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro e he
    rw [fpDist, PMF.mem_support_bind_iff] at he
    obtain ⟨d, hd, hde⟩ := he
    have hd2 := F.hold_support_snd_ge d hd
    split_ifs at hde with hcond
    · rw [PMF.support_pure, Set.mem_singleton_iff] at hde
      subst hde
      rcases hcond with h | h
      · omega
      · exact h
    · push Not at hcond
      rw [PMF.mem_support_map_iff] at hde
      obtain ⟨e', he's, he'⟩ := hde
      have hrec := IH (s - d.2.toNat) (by omega) e' he's
      rw [← he']
      show (s : ℤ) < d.2 + e'.2
      have : ((s - d.2.toNat : ℕ) : ℤ) = (s : ℤ) - d.2 := by omega
      omega

/-- **First-passage inequality** (`Q_le_fpDist_expect` of tao-collatz, the form of (7.45) with the decay discarded). -/
theorem Q_le_fpDist_expect (half : ℕ) (W : Set (ℕ × ℤ)) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∀ (s : ℕ) (j : ℕ) (l : ℤ),
      ENNReal.ofReal (F.Q half W κ j l)
        ≤ ∑' e : ℕ × ℤ, F.fpDist s e * ENNReal.ofReal (F.Q half W κ (j + e.1) (l + e.2)) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro j l
    rcases Nat.lt_or_ge half j with hj | hj
    · rw [F.Q_boundary _ _ _ _ _ hj]
      have hRHS : ∑' e : ℕ × ℤ,
          F.fpDist s e * ENNReal.ofReal (F.Q half W κ (j + e.1) (l + e.2)) = 1 := by
        rw [← (F.fpDist s).tsum_coe]
        refine tsum_congr fun e => ?_
        by_cases h0 : F.fpDist s e = 0
        · rw [h0, zero_mul]
        · have h1 := F.fpDist_support_fst_pos s e (by rwa [PMF.mem_support_iff])
          rw [F.Q_boundary _ _ _ _ _ (by omega), ENNReal.ofReal_one, mul_one]
      rw [hRHS, ENNReal.ofReal_one]
    · rw [F.Q_rec _ _ _ _ _ hj]
      have hexp1 : Real.exp (-κ * Set.indicator W 1 (j, l)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
        exact mul_nonneg hκ (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      have hS0 : 0 ≤ ∑' d : ℕ × ℤ, (F.hold d).toReal * F.Q half W κ (j + d.1) (l + d.2) :=
        tsum_nonneg fun d => mul_nonneg ENNReal.toReal_nonneg (F.Q_nonneg _ _ _ _ _)
      have hdrop : ENNReal.ofReal (Real.exp (-κ * Set.indicator W 1 (j, l)) *
            ∑' d : ℕ × ℤ, (F.hold d).toReal * F.Q half W κ (j + d.1) (l + d.2))
          ≤ ENNReal.ofReal
            (∑' d : ℕ × ℤ, (F.hold d).toReal * F.Q half W κ (j + d.1) (l + d.2)) :=
        ENNReal.ofReal_le_ofReal (by
          calc Real.exp (-κ * Set.indicator W 1 (j, l)) * _
              ≤ 1 * (∑' d : ℕ × ℤ, (F.hold d).toReal * F.Q half W κ (j + d.1) (l + d.2)) :=
                mul_le_mul_of_nonneg_right hexp1 hS0
            _ = _ := one_mul _)
      refine le_trans hdrop ?_
      have hlift : ENNReal.ofReal
            (∑' d : ℕ × ℤ, (F.hold d).toReal * F.Q half W κ (j + d.1) (l + d.2))
          = ∑' d : ℕ × ℤ, F.hold d * ENNReal.ofReal (F.Q half W κ (j + d.1) (l + d.2)) := by
        rw [← PMF.toReal_tsum_mul_ofReal F.hold _ (fun d => F.Q_nonneg _ _ _ _ _),
          ENNReal.ofReal_toReal]
        exact ne_top_of_le_ne_top (by simp)
          (PMF.tsum_mul_ofReal_le_one F.hold _ (fun d => F.Q_le_one _ _ _ hκ _ _))
      rw [hlift, fpDist, PMF.tsum_bind_mul]
      refine ENNReal.tsum_le_tsum fun d => ?_
      by_cases h0 : F.hold d = 0
      · rw [h0, zero_mul, zero_mul]
      · have hd2 := F.hold_support_snd_ge d (by rwa [PMF.mem_support_iff])
        refine mul_le_mul_right ?_ _
        split_ifs with hcond
        · refine le_of_eq ?_
          rw [tsum_eq_single d (fun e he => by
            rw [PMF.pure_apply, if_neg he, zero_mul])]
          rw [PMF.pure_apply, if_pos rfl, one_mul]
        · push Not at hcond
          rw [PMF.tsum_map_mul]
          have hIH := IH (s - d.2.toNat) (by omega) (j + d.1) (l + d.2)
          refine le_trans hIH (le_of_eq (tsum_congr fun e => ?_))
          rw [show (j + d.1) + e.1 = j + (d.1 + e.1) from by omega,
            show (l + d.2) + e.2 = l + (d.2 + e.2) from by ring]

end Family

end GGMCollatz
